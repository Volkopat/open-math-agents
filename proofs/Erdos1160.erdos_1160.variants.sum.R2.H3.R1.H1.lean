import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R1
-- Credit: @Thomassien
/-!
Reuses the Higman and off-strip enumeration proofs from open-math-agents PR 7063,
commit 6c096a4ccb84dfd27917c03c8f414dfe4c49324a (Apache-2.0).
That submission inlines proofs from PRs 393, 2283, 2310, 2379, and 2452.
The final LargeSquareIndex namespace adapts the off-strip bound to this exact step.
-/
namespace InlinedL
open Filter Erdos1160
def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop, 2^(2*m^3) ≤ g (2^m)^27 * 2^(13*m^2)
end InlinedL
section PartL
namespace Erdos1160.Tables
open CategoryTheory
def orderClasses (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n}
def GroupTable (n : ℕ) :=
  { t : Fin n → Fin n → Fin n // ∃ s : Group (Fin n), s.mul = t }
instance {n : ℕ} : Finite (GroupTable n) := by
  unfold GroupTable
  infer_instance
noncomputable abbrev model {n : ℕ} (t : GroupTable n) : FiniteGrp.{0} :=
  @FiniteGrp.of (Fin n) t.property.choose inferInstance
def product (G : FiniteGrp) (a b : G) : G := a * b
theorem model_mul {n : ℕ} (t : GroupTable n) (a b : Fin n) :
    product (model t) a b = t.val a b :=
  congrFun (congrFun t.property.choose_spec a) b
noncomputable def groupClass {n : ℕ} (t : GroupTable n) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (model t)
theorem iso_of_mul_equiv {G H : FiniteGrp} (e : G ≃ H)
    (h : ∀ a b, e (product G a b) = product H (e a) (e b)) : Nonempty (G ≅ H) := by
  let f : G ≃* H := { e with map_mul' := h }
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩
theorem range_groupClass (n : ℕ) : Set.range (@groupClass n) = orderClasses n := by
  ext c
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨model t, Nat.card_fin n, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    let e : Fin n ≃ G := ((Nat.equivFinOfCardPos (α := G) Nat.card_pos.ne').trans
      (finCongr hG)).symm
    let law : Group (Fin n) := e.group
    let t : GroupTable n := ⟨law.mul, law, rfl⟩
    refine ⟨t, Quotient.sound ?_⟩
    apply iso_of_mul_equiv e
    intro a b
    exact (congrArg (fun z => e z) (model_mul t a b)).trans (e.apply_symm_apply (e a * e b))
theorem orderClasses_finite (n : ℕ) : (orderClasses n).Finite := by
  rw [← range_groupClass]
  exact Set.finite_range _
end Erdos1160.Tables
namespace Erdos1160.PresentationCount
open CategoryTheory
theorem card_le_of_fiber_bound {A B : Type*} [Finite A] [Finite B] (f : A → B)
    (M : ℕ) (h : ∀ b : B, Nat.card {a : A // f a = b} ≤ M) :
    Nat.card A ≤ Nat.card B * M := by
  classical
  let : Fintype B := Fintype.ofFinite B
  calc
    Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
      rw [← Nat.card_sigma]
      exact (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ ≤ ∑ _b : B, M := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * M := by simp [Nat.card_eq_fintype_card]
end Erdos1160.PresentationCount
namespace Erdos1160.PresentationCount
open CategoryTheory
theorem card_le_of_relative_codes {A C : Type*} [Finite A] [Finite C] {n : ℕ}
    (X : A → FiniteGrp.{0}) (hN : ∀ a, Nat.card (X a) = n)
    (code : ∀ a b : A, (X a ≃* X b) → C)
    (sep : ∀ (a b r : A) (e : X a ≃* X r) (f : X b ≃* X r),
      code a r e = code b r f → a = b) :
    Nat.card A ≤ Erdos1160.g n * Nat.card C := by
  classical
  let classOf (a : A) : Tables.orderClasses n := ⟨Quotient.mk _ (X a), X a, hN a, rfl⟩
  let : Finite (Tables.orderClasses n) := (Tables.orderClasses_finite n).to_subtype
  apply card_le_of_fiber_bound classOf (Nat.card C)
  intro c
  let F := {a : A // classOf a = c}
  by_cases hn : Nonempty F
  · let r := Classical.choice hn
    have sameClass (a : F) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (X a.val)
        = Quotient.mk _ (X r.val) :=
      congrArg Subtype.val (a.property.trans r.property.symm)
    let transport (a : F) : X a.val ≃* X r.val :=
      ((inducedFunctor FiniteGrp.toGrp).mapIso
        (Classical.choice (Quotient.exact (sameClass a)))).groupIsoToMulEquiv
    let encode (a : F) : C := code a.val r.val (transport a)
    exact Nat.card_le_card_of_injective encode (fun {a b} h =>
      Subtype.ext (sep a.val b.val r.val (transport a) (transport b) h))
  · have empty : IsEmpty F := not_nonempty_iff.mp hn
    change Nat.card F ≤ Nat.card C
    simp
end Erdos1160.PresentationCount
namespace Erdos1160Growth
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
structure BilinearExtension (B : V →+ V →+ W) where
  base : V
  fiber : W
namespace BilinearExtension
variable {B : V →+ V →+ W}
theorem ext {x y : BilinearExtension B} (hb : x.base = y.base) (hf : x.fiber = y.fiber) : x = y := by
  cases x
  cases y
  simp_all
instance : Mul (BilinearExtension B) :=
  ⟨fun x y => ⟨x.base + y.base, x.fiber + y.fiber + B x.base y.base⟩⟩
instance : One (BilinearExtension B) := ⟨⟨0,0⟩⟩
instance : Inv (BilinearExtension B) :=
  ⟨fun x => ⟨-x.base, -x.fiber + B x.base x.base⟩⟩
@[simp] theorem mul_base (x y : BilinearExtension B) :
    (x*y).base = x.base + y.base := rfl
@[simp] theorem mul_fiber (x y : BilinearExtension B) :
    (x*y).fiber = x.fiber + y.fiber + B x.base y.base := rfl
@[simp] theorem inv_base (x : BilinearExtension B) : (x⁻¹).base = -x.base := rfl
@[simp] theorem inv_fiber (x : BilinearExtension B) :
    (x⁻¹).fiber = -x.fiber + B x.base x.base := rfl
@[simp] theorem one_base : (1 : BilinearExtension B).base = 0 := rfl
@[simp] theorem one_fiber : (1 : BilinearExtension B).fiber = 0 := rfl
instance : Group (BilinearExtension B) where
  mul_assoc x y z := by
    apply BilinearExtension.ext <;> simp [map_add] <;> abel
  one_mul x := by
    apply BilinearExtension.ext <;> simp
  mul_one x := by
    apply BilinearExtension.ext <;> simp
  inv_mul_cancel x := by
    apply BilinearExtension.ext <;> simp
def coordinateEquiv (B : V →+ V →+ W) : BilinearExtension B ≃ V × W where
  toFun x := (x.base, x.fiber)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem card (B : V →+ V →+ W) :
    Nat.card (BilinearExtension B) = Nat.card V * Nat.card W := by
  rw [Nat.card_congr (coordinateEquiv B), Nat.card_prod]
open scoped commutatorElement
theorem commutator_formula (x y : BilinearExtension B) :
    ⁅x, y⁆ = ⟨0, B x.base y.base - B y.base x.base⟩ := by
  rw [commutatorElement_def]
  apply BilinearExtension.ext <;> simp [map_add, map_neg]
  abel
end BilinearExtension
end Erdos1160Growth
namespace Erdos1160Growth.BilinearExtension
open scoped commutatorElement
private theorem double_zero {s : ℕ} (w : Fin s → ZMod 2) : w+w = 0 := by
  funext i
  have h : ∀ z : ZMod 2, z+z = 0 := by decide
  exact h (w i)
theorem lift_square_eq_of_base_eq {V : Type*} [AddCommGroup V] {s : ℕ}
    {B : V →+ V →+ (Fin s → ZMod 2)} {a b : BilinearExtension B} (h : a.base = b.base) :
    a * a = b * b := by
  apply BilinearExtension.ext
  · simp only [mul_base, h]
  · simp only [mul_fiber, double_zero, zero_add, h]
theorem lift_commutator_eq_of_base_eq {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    {B : V →+ V →+ W} {a b c d : BilinearExtension B}
    (hac : a.base = c.base) (hbd : b.base = d.base) :
    ⁅a,b⁆ = ⁅c,d⁆ := by
  rw [commutator_formula, commutator_formula, hac, hbd]
end Erdos1160Growth.BilinearExtension
open scoped BigOperators commutatorElement
namespace Erdos1160Growth.SharpFamily
abbrev V (d : ℕ) := Fin d → ZMod 2
abbrev Slot (d s : ℕ) := (Σ i : Fin d, Fin i.val) ⊕ Fin (d-s)
abbrev Param (d s : ℕ) := Slot d s → V s
variable {d s : ℕ}
def basis {k : ℕ} (i : Fin k) : V k := Pi.single i 1
def entry (t : Param d s) (i j : Fin d) : V s :=
  if h : j < i then t (.inl ⟨i, ⟨j.val,h⟩⟩)
  else if i = j then
    if hl : i.val < s then basis ⟨i.val, hl⟩
    else t (.inr ⟨i.val - s, by have := i.isLt; omega⟩)
  else 0
theorem entry_fixed {t : Param d s} (i : Fin s) (hs : s ≤ d) :
    entry t (Fin.castLE hs i) (Fin.castLE hs i) = basis i := by
  simp [entry, i.isLt]
theorem entry_upper {t : Param d s} {i j : Fin d} (h : i < j) : entry t i j = 0 := by
  simp [entry, not_lt_of_ge (le_of_lt h), ne_of_lt h]
theorem entry_injective {t u : Param d s} (h : ∀ i j, entry t i j = entry u i j) : t = u := by
  funext k
  rcases k with ⟨i,j⟩ | k
  · let j' : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩
    have hj : j' < i := j.isLt
    simpa [entry,hj,j'] using h i j'
  · have hk : s + k.val < d := by have := k.isLt; omega
    let i : Fin d := ⟨s + k.val, hk⟩
    have hi : ¬ i.val < s := by simp [i]
    simpa [entry,hi,i] using h i i
def form (t : Param d s) : V d →+ V d →+ V s where
  toFun a :=
    { toFun := fun b k => ∑ i, ∑ j, a i * b j * entry t i j k
      map_zero' := by funext k; simp
      map_add' := by
        intro b c
        funext k
        simp [mul_add, add_mul, Finset.sum_add_distrib] }
  map_zero' := by ext b k; simp
  map_add' := by
    intro a b
    ext c k
    simp [add_mul, Finset.sum_add_distrib]
abbrev G (t : Param d s) := BilinearExtension (form t)
def gen (t : Param d s) (i : Fin d) : G t := ⟨basis i, 0⟩
def Z (t : Param d s) (z : V s) : G t := ⟨0, z⟩
lemma eval_basis (t : Param d s) (i j : Fin d) :
    form t (basis i) (basis j) = entry t i j := by
  funext k
  change (∑ a, ∑ b, basis i a * basis j b * entry t a b k) = _
  simp [basis, Pi.single_apply, ite_mul, mul_ite, Finset.sum_ite_eq']
theorem double_zero {k : ℕ} (v : V k) : v + v = 0 := by
  funext j
  exact (show ∀ x : ZMod 2, x + x = 0 by decide) (v j)
theorem gen_sq (t : Param d s) (i : Fin d) : gen t i * gen t i = Z t (entry t i i) := by
  apply BilinearExtension.ext
  · exact double_zero (basis i)
  · change 0 + 0 + form t (basis i) (basis i) = entry t i i
    rw [zero_add, zero_add, eval_basis]
theorem gen_comm (t : Param d s) (i j : Fin d) (h : j < i) :
    ⁅gen t i, gen t j⁆ = Z t (entry t i j) := by
  rw [BilinearExtension.commutator_formula]
  apply BilinearExtension.ext
  · rfl
  · change form t (basis i) (basis j) - form t (basis j) (basis i) = _
    rw [eval_basis, eval_basis, entry_upper h, sub_zero]
    rfl
theorem Z_injective (t : Param d s) : Function.Injective (Z t) :=
  fun _ _ h => congrArg BilinearExtension.fiber h
theorem Z_add (t : Param d s) (u v : V s) : Z t (u + v) = Z t u * Z t v := by
  apply BilinearExtension.ext <;> simp [Z]
end Erdos1160Growth.SharpFamily
namespace Erdos1160Growth.SharpFamily
open scoped commutatorElement
variable {d s : ℕ}
theorem map_Z_agree {R : Type*} [Group R] {t u : Param d s}
    (e : G t →* R) (f : G u →* R)
    (h : ∀ i : Fin s, e (Z t (basis i)) = f (Z u (basis i))) (w : V s) :
    e (Z t w) = f (Z u w) := by
  have hz : e (Z t 0) = f (Z u 0) := e.map_one.trans f.map_one.symm
  induction w using Pi.single_induction with
  | zero => exact hz
  | add a b ha hb => rw [Z_add, Z_add, map_mul, map_mul, ha, hb]
  | single i x =>
    have bit : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases bit x with rfl | rfl
    · simpa only [Pi.single_zero] using hz
    · exact h i
theorem recover_of_equal_base (hs : s ≤ d) (t u r : Param d s)
    (e : G t ≃* G r) (f : G u ≃* G r)
    (h : ∀ i : Fin d, (e (gen t i)).base = (f (gen u i)).base) : t = u := by
  have hsquare (i : Fin d) : e (Z t (entry t i i)) = f (Z u (entry u i i)) := by
    rw [← gen_sq, ← gen_sq, map_mul, map_mul]
    exact BilinearExtension.lift_square_eq_of_base_eq (h i)
  have hfix (i : Fin s) : e (Z t (basis i)) = f (Z u (basis i)) := by
    simpa only [entry_fixed i hs] using hsquare (Fin.castLE hs i)
  have recover {v w : V s} (hv : e (Z t v) = f (Z u w)) : v = w := by
    have hsame := map_Z_agree e.toMonoidHom f.toMonoidHom hfix v
    exact Z_injective u (f.injective (hsame.symm.trans hv))
  apply entry_injective
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [entry_upper hij, entry_upper hij]
  · exact recover (hsquare i)
  · apply recover
    rw [← gen_comm t i j hji, ← gen_comm u i j hji, map_commutatorElement, map_commutatorElement]
    exact BilinearExtension.lift_commutator_eq_of_base_eq (h i) (h j)
end Erdos1160Growth.SharpFamily
namespace Erdos1160Growth.SharpFamily
theorem triangular_card (d : ℕ) :
    Nat.card ((i : Fin d) × Fin i.val) = d * (d - 1) / 2 := by
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)
end Erdos1160Growth.SharpFamily
namespace Erdos1160Growth.SharpFamily
private instance {d s : ℕ} (t : Param d s) : Finite (G t) :=
  Finite.of_equiv _ (BilinearExtension.coordinateEquiv (form t)).symm
private def bundled {d s : ℕ} (t : Param d s) : FiniteGrp.{0} := FiniteGrp.of (G t)
private theorem bundled_order {d s : ℕ} (t : Param d s) : Nat.card (bundled t) = 2 ^ (d+s) := by
  change Nat.card (BilinearExtension (form t)) = _
  rw [BilinearExtension.card]
  simp only [V, Nat.card_fun, Nat.card_zmod, Nat.card_fin, pow_add]
theorem parameter_card {d s : ℕ} (hs : s ≤ d) :
    Nat.card (Param d s) = 2 ^ (s * (d * (d - 1) / 2 + d - s)) := by
  change Nat.card (Slot d s → Fin s → ZMod 2) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul]
  unfold Slot
  rw [Nat.card_sum, triangular_card, Nat.card_fin]
  have h : d * (d - 1) / 2 + (d - s) = d * (d - 1) / 2 + d - s := by omega
  rw [h]
theorem sharp_parameter_lower {d s : ℕ} (hs : s ≤ d) :
    2 ^ (s * (d * (d - 1) / 2 + d - s)) ≤
      Erdos1160.g (2 ^ (d+s)) * 2 ^ (d*d) := by
  let code (a r : Param d s) (e : bundled a ≃* bundled r) (i : Fin d) : V d :=
    (e (gen a i) : G r).base
  have sep (a b r : Param d s) (e : bundled a ≃* bundled r) (f : bundled b ≃* bundled r)
      (h : code a r e = code b r f) : a = b :=
    recover_of_equal_base hs a b r e f (congrFun h)
  have h := Erdos1160.PresentationCount.card_le_of_relative_codes bundled bundled_order code sep
  rw [parameter_card hs] at h
  change _ ≤ _ * Nat.card (Fin d → Fin d → ZMod 2) at h
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, ← pow_mul] using h
end Erdos1160Growth.SharpFamily
namespace Erdos1160Growth.SharpFamily
private theorem converted_bound (m d s : ℕ) (hs : s ≤ d) (horder : d+s=m)
    (hexp : 2*m^3 + (d*d)*27 ≤ (s*(d*(d-1)/2+d-s))*27 + 12*m^2) :
    2^(2*m^3) ≤ Erdos1160.g (2^m)^27 * 2^(12*m^2) := by
  have count := Nat.pow_le_pow_left (sharp_parameter_lower hs) 27
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, horder] at count
  apply Nat.le_of_mul_le_mul_right (c := 2^((d*d)*27)) _ (Nat.pow_pos (by decide))
  calc
    2^(2*m^3) * 2^((d*d)*27) = 2^(2*m^3+(d*d)*27) := (pow_add _ _ _).symm
    _ ≤ 2^((s*(d*(d-1)/2+d-s))*27+12*m^2) := Nat.pow_le_pow_right (by decide) hexp
    _ = _ := pow_add _ _ _
    _ ≤ (Erdos1160.g (2^m)^27 * 2^((d*d)*27)) * 2^(12*m^2) :=
      Nat.mul_le_mul_right _ count
    _ = _ := Nat.mul_right_comm _ _ _
private theorem triangle_even (u : ℕ) :
    (2*u)*(2*u-1)/2 = u*(2*u-1) := by
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
private theorem triangle_odd (u : ℕ) :
    (2*u+1)*(2*u+1-1)/2 = (2*u+1)*u := by
  have h : 2*u+1-1 = 2*u := by omega
  rw [h, show (2*u+1)*(2*u) = (2*u+1)*u*2 by ring, Nat.mul_div_cancel _ (by decide)]
theorem higman_lower_all (m : ℕ) (hm : 3 ≤ m) :
    2^(2*m^3) ≤ Erdos1160.g (2^m)^27 * 2^(12*m^2) := by
  let k := m/3-1
  have cases_m : m=3*(k+1) ∨ m=3*(k+1)+1 ∨ m=3*(k+1)+2 := by
    dsimp [k]
    omega
  have even_pred : 2*(k+1)-1 = 2*k+1 := by omega
  rcases cases_m with h | h | h
  · apply converted_bound m (2*(k+1)) (k+1) (by omega) (by omega)
    rw [h, triangle_even, even_pred]
    have sub_id : (k+1)*(2*k+1)+2*(k+1)-(k+1) = (k+1)*(2*k+1)+(k+1) := by omega
    rw [sub_id]
    exact le_of_eq (by ring)
  · apply converted_bound m (2*(k+1)) (k+2) (by omega) (by omega)
    rw [h, triangle_even, even_pred]
    have sub_id : (k+1)*(2*k+1)+2*(k+1)-(k+2) = (k+1)*(2*k+1)+k := by omega
    rw [sub_id]
    apply Nat.le.intro (k := 27*k+10)
    ring
  · apply converted_bound m (2*(k+1)+1) (k+2) (by omega) (by omega)
    rw [h, triangle_odd]
    have sub_id : (2*(k+1)+1)*(k+1)+(2*(k+1)+1)-(k+2) =
        (2*(k+1)+1)*(k+1)+(k+1) := by omega
    rw [sub_id]
    apply Nat.le.intro (k := 18*k+23)
    ring
end Erdos1160Growth.SharpFamily
namespace Erdos1160.Growth
open Filter
end Erdos1160.Growth
namespace Erdos1160.Growth
open Filter
theorem adjacent_growth_lower : ∀ᶠ m : ℕ in atTop,
    2^(2*m^3) ≤ g (2^m)^27 * 2^(13*m^2) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨3, fun m hm => ?_⟩
  apply (Erdos1160Growth.SharpFamily.higman_lower_all m hm).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
end Erdos1160.Growth
theorem InlinedL.lower : InlinedL.H1 := by
  exact Erdos1160.Growth.adjacent_growth_lower
end PartL
section PartUH1
section
namespace OrbitUp
open scoped BigOperators Matrix
abbrev K := ZMod 2
abbrev V (d : ℕ) := Fin d → K
abbrev Q (d s : ℕ) := QuadraticMap K (V d) (V s)
abbrev L (d : ℕ) := V d ≃ₗ[K] V d
def basis {d : ℕ} (i : Fin d) : V d := Pi.single i 1
private theorem twozero {d : ℕ} (w : V d) : w+w = 0 := by
  funext i
  have h : ∀ z : K, z+z = 0 := by decide
  exact h (w i)
private theorem maps_eq_on_basis {d s : ℕ} {f g : V d → V s} (hz : f 0 = g 0)
    (hadd : ∀ x y, f x = g x → f y = g y → f (x+y) = g (x+y))
    (hb : ∀ i, f (basis i) = g (basis i)) (x : V d) : f x = g x := by
  induction x using Pi.single_induction with
  | zero => exact hz
  | add a b ha hb' => exact hadd a b ha hb'
  | single i x =>
    have h : ∀ b : K, b=0 ∨ b=1 := by decide
    rcases h x with rfl | rfl
    · simpa only [Pi.single_zero] using hz
    · exact hb i
abbrev Slots (d : ℕ) := Fin d ⊕ ((i : Fin d) × Fin i.val)
def coefficients {d s : ℕ} (q : Q d s) : Slots d → V s :=
  Sum.elim (fun i => q (basis i))
    (fun z => QuadraticMap.polar q (basis z.1) (basis ⟨z.2.val, z.2.isLt.trans z.1.isLt⟩))
theorem coefficients_injective {d s : ℕ} : Function.Injective (@coefficients d s) := by
  intro q r he
  have hd (i : Fin d) : q (basis i) = r (basis i) := congrFun he (.inl i)
  have lower (i j : Fin d) (h : j < i) : QuadraticMap.polar q (basis i) (basis j) =
      QuadraticMap.polar r (basis i) (basis j) := congrFun he (.inr ⟨i,⟨j.val,h⟩⟩)
  have entries (i j : Fin d) : QuadraticMap.polar q (basis i) (basis j) =
      QuadraticMap.polar r (basis i) (basis j) := by
    rcases lt_trichotomy i j with h | rfl | h
    · rw [QuadraticMap.polar_comm q, QuadraticMap.polar_comm r]
      exact lower j i h
    · simp only [QuadraticMap.polar_self, two_nsmul, twozero]
    · exact lower i j h
  have eq2 (x y : V d) : QuadraticMap.polar q x y = QuadraticMap.polar r x y := by
    apply maps_eq_on_basis _ _ _ x
    · simp
    · intro u v hu hv
      simp only [QuadraticMap.polar_add_left,hu,hv]
    · intro i
      apply maps_eq_on_basis _ _ (entries i) y
      · simp
      · intro u v hu hv
        simp only [QuadraticMap.polar_add_right, hu,hv]
  apply QuadraticMap.ext
  intro x
  apply maps_eq_on_basis _ _ hd x
  · simp
  · intro u v hu hv
    rw [QuadraticMap.map_add q, QuadraticMap.map_add r, hu, hv, eq2]
theorem count_forms (d s : ℕ) :
    Nat.card (Q d s) ≤ 2^(s*(d+d*(d-1)/2)) := by
  have h := Nat.card_le_card_of_injective (@coefficients d s) coefficients_injective
  have slots : Nat.card (Slots d) = d + d*(d-1)/2 := by
    rw [Slots, Nat.card_sum, Nat.card_fin, Nat.card_sigma]
    simp only [Nat.card_fin]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)
  simpa only [Nat.card_fun, slots, V, Nat.card_fin, Nat.card_zmod, ← pow_mul] using h
theorem gl_lower (d : ℕ) : 2^(d*(d-1)) ≤ Nat.card (L d) := by
  let e : GL (Fin d) K ≃* L d := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (V d))
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field (𝔽 := K) d, ZMod.card]
  cases d with
  | zero => simp
  | succ n =>
    have hfactor (i : Fin (n+1)) : 2^n ≤ 2^(n+1)-2^i.val := by
      have hi : 2^i.val ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ]
      omega
    calc
      2^((n+1)*(n+1-1)) = ∏ _i : Fin (n+1), 2^n := by simp [← pow_mul, Nat.mul_comm]
      _ ≤ _ := Finset.prod_le_prod' (fun i _ => hfactor i)
end OrbitUp
end
section
namespace OrbitUp
abbrev Change (d s : ℕ) := L d × L s
noncomputable def change {d s : ℕ} (g : Change d s) (q : Q d s) : Q d s :=
  g.2.toLinearMap.compQuadraticMap (q.comp g.1.symm.toLinearMap)
noncomputable instance {d s : ℕ} : MulAction (Change d s) (Q d s) where
  smul := change
  one_smul q := by ext x; rfl
  mul_smul g h q := by ext x; rfl
private instance forms_finite (d s : ℕ) : Finite (Q d s) :=
  Finite.of_injective (@coefficients d s) coefficients_injective
private instance linear_finite (d : ℕ) : Finite (L d) :=
  Finite.of_injective (fun e : L d => (e : V d → V d)) (by intro f g h; exact LinearEquiv.ext (fun v => congrFun h v))
abbrev Classes (d s : ℕ) := MulAction.orbitRel.Quotient (Change d s) (Q d s)
end OrbitUp
end
section
namespace OrbitUp
private theorem rank_polynomial (d s : ℝ) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    27*(s*(d*(d+1)/2)-d*(d-1)-s*(s-1)) + 12*(d+s)^2 ≤
      2*(d+s)^3+60*(d+s) := by
  let m := d+s
  let x := d-2*m/3
  have hm : 0 ≤ m := add_nonneg hd hs
  have hdx : 0 ≤ m+x-m/3 := by dsimp [m,x]; linarith
  have cubic := mul_nonneg hdx (sq_nonneg x)
  have square := mul_nonneg hm (sq_nonneg (x+5/2))
  have xx := sq_nonneg x
  dsimp [m,x] at cubic square xx hm
  nlinarith only [cubic, square, xx, hm]
theorem rank_powers (d s : ℕ) :
    27*(s*(d+d*(d-1)/2)) + 12*(d+s)^2 ≤
      2*(d+s)^3+60*(d+s)+27*(d*(d-1)+s*(s-1)) := by
  have tri_even : 2*(d*(d-1)/2) = d*(d-1) := by
    rcases Nat.even_or_odd d with ⟨k,hk⟩ | ⟨k,hk⟩
    · have hv : d*(d-1)=2*(k*(d-1)) := by rw [hk]; ring
      rw [hv, Nat.mul_div_cancel_left _ (by decide)]
    · have hp : d-1=2*k := by omega
      have hv : d*(d-1)=2*(d*k) := by rw [hp]; ring
      rw [hv, Nat.mul_div_cancel_left _ (by decide)]
  have input (j : ℕ) : ((j*(j-1):ℕ):ℝ) = (j:ℝ)*((j:ℝ)-1) := by
    cases j with
    | zero => simp
    | succ n => simp
  have rad := rank_polynomial (d:ℝ) (s:ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have tri : 2*((d*(d-1)/2 : ℕ):ℝ) = (d:ℝ)*((d:ℝ)-1) := by
    rw [← input]
    exact_mod_cast tri_even
  have tris := congrArg (fun r : ℝ => r*(s:ℝ)) tri
  change (2*((d*(d-1)/2:ℕ):ℝ))*(s:ℝ) = ((d:ℝ)*((d:ℝ)-1))*(s:ℝ) at tris
  have goal : 27*((s:ℝ)*((d:ℝ)+((d*(d-1)/2:ℕ):ℝ)))+12*((d:ℝ)+(s:ℝ))^2 ≤
      2*((d:ℝ)+(s:ℝ))^3+60*((d:ℝ)+(s:ℝ))+27*(((d*(d-1):ℕ):ℝ)+((s*(s-1):ℕ):ℝ)) := by
    rw [input d, input s]
    linarith only [rad,tris]
  exact_mod_cast goal
end OrbitUp
end
section
namespace OrbitUp
private def shearMap {d : ℕ} (i j : Fin d) : V d →ₗ[K] V d where
  toFun v := v + (v i) • basis j
  map_add' x y := by simp [add_smul, add_add_add_comm]
  map_smul' a x := by simp [smul_add, smul_smul]
def shear {d : ℕ} (i j : Fin d) (h : i ≠ j) : L d :=
  let t := shearMap i j
  { t with
    invFun := t
    left_inv := by
      intro v
      funext k
      have zero : basis j i = 0 := by simp [basis,Ne.symm h]
      change (v k + v i * basis j k) + (v i + v i * basis j i)*basis j k = v k
      rw [zero,mul_zero, add_zero]
      have dbl : ∀ z : K, z+z=0 := by decide
      rw [add_assoc,dbl,add_zero]
    right_inv := by
      intro v
      funext k
      have zero : basis j i = 0 := by simp [basis,Ne.symm h]
      change (v k + v i * basis j k) + (v i + v i * basis j i)*basis j k = v k
      rw [zero,mul_zero, add_zero]
      have dbl : ∀ z : K, z+z=0 := by decide
      rw [add_assoc,dbl,add_zero] }
end OrbitUp
end
section
namespace OrbitUp
end OrbitUp
end
section
namespace OrbitUp
def fixedSubspace {s : ℕ} (b : L s) : Submodule K (V s) :=
  LinearMap.ker (b.toLinearMap - LinearMap.id)
theorem mem_fixedSubspace {s : ℕ} (b : L s) (w : V s) :
    w ∈ fixedSubspace b ↔ b w = w := by
  change b w - w = 0 ↔ b w = w
  exact sub_eq_zero
abbrev mixedFix {d s : ℕ} (a : L d) (b : L s) := {q : Q d s // ∀ x, b (q x) = q (a x)}
end OrbitUp
end
section
namespace OrbitUp
abbrev ShearClass {d : ℕ} (i j : Fin d) (h : i ≠ j) :=
  {a : L d // ∃ u : L d, ∀ x, a x = u (shear i j h (u.symm x))}
private noncomputable def conjCode {d : ℕ} {i j : Fin d} {h : i ≠ j}
    (a : ShearClass i j h) : (V d →ₗ[K] K) × V d :=
  let u := a.property.choose
  ⟨(LinearMap.proj i).comp u.symm.toLinearMap, u (basis j)⟩
theorem gl_upper (d : ℕ) : Nat.card (L d) ≤ 2^(d*d) := by
  have inj : Function.Injective (fun a : L d => a.toLinearMap) := by
    intro a b hb
    exact LinearEquiv.ext (fun x => LinearMap.congr_fun hb x)
  letI : Finite (V d →ₗ[K] V d) := Finite.of_injective (fun f => (f : V d → V d)) DFunLike.coe_injective
  have bd := Nat.card_le_card_of_injective _ inj
  rw [Module.natCard_eq_pow_finrank (K := K) (V := V d →ₗ[K] V d),Module.finrank_linearMap] at bd
  simpa [V,K] using bd
end OrbitUp
end
section
namespace OrbitUp
private def entry {k s : ℕ} (t : Slots k → V s) (i j : Fin k) : V s :=
  if h : j < i then t (.inr ⟨i,⟨j.val,h⟩⟩)
  else if i=j then t (.inl i) else 0
private def bilin {k s : ℕ} (t : Slots k → V s) : V k →ₗ[K] V k →ₗ[K] V s :=
  LinearMap.mk₂ K (fun a b c => ∑ i, ∑ j, a i * b j * entry t i j c)
    (by intro a b y; funext c; simp [add_mul,Finset.sum_add_distrib])
    (by intro x a b; funext c; simp [Finset.mul_sum,mul_assoc])
    (by intro a b y; funext c; simp [mul_add,add_mul,Finset.sum_add_distrib])
    (by intro x a b; funext c; simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring)
private theorem bilin_basis {k s : ℕ} (t : Slots k → V s) (i j : Fin k) :
    bilin t (basis i) (basis j) = entry t i j := by
  funext c
  change (∑ a, ∑ b, basis i a * basis j b * entry t a b c) = _
  simp [basis, Pi.single_apply, ite_mul, mul_ite, Finset.sum_ite_eq']
private theorem build_injective {k s : ℕ} :
    Function.Injective (fun t : Slots k → V s => LinearMap.BilinMap.toQuadraticMap (bilin t)) := by
  intro t u he
  funext z
  rcases z with i | ⟨i,j⟩
  · have eq := congrArg (fun f : Q k s => f (basis i)) he
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply,bilin_basis,entry,lt_self_iff_false,
      dite_false,ite_true] using eq
  · let l : Fin k := ⟨j.val,j.isLt.trans i.isLt⟩
    have hl : l < i := j.isLt
    have eq := congrArg (fun f : Q k s => QuadraticMap.polar f (basis i) (basis l)) he
    simpa [LinearMap.BilinMap.polar_toQuadraticMap,bilin_basis,entry,hl,
      not_lt_of_ge (le_of_lt hl),ne_of_lt hl,l] using eq
theorem card_forms_exact (k s : ℕ) : Nat.card (Q k s) = 2^(s*(k+k*(k-1)/2)) := by
  apply Nat.le_antisymm (count_forms k s)
  have bd := Nat.card_le_card_of_injective _ (@build_injective k s)
  have slots : Nat.card (Slots k) = k + k*(k-1)/2 := by
    rw [Slots, Nat.card_sum, Nat.card_fin, Nat.card_sigma]
    simp only [Nat.card_fin]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) k).trans (Finset.sum_range_id k)
  simpa only [Nat.card_fun,slots,V,Nat.card_fin,Nat.card_zmod,←pow_mul] using bd
def Moves {d : ℕ} (a : L d) (k : ℕ) : Prop :=
  ∃ (u : V k →ₗ[K] V d) (c : V d →ₗ[K] V k), (∀ x, c (u x) = 0) ∧ (∀ x, c (a (u x)) = x)
theorem moved_fixed_card {d s k : ℕ} {a : L d} (b : L s) (ha : Moves a k) :
    Nat.card (mixedFix a b) * 2^(s*(k+k*(k-1)/2)) ≤ 2^(s*(d+d*(d-1)/2)) := by
  obtain ⟨u,c,zero,decode⟩ := ha
  let enc (p : mixedFix a b × Q k s) : Q d s := p.1.val + p.2.comp c
  have inj : Function.Injective enc := by
    rintro ⟨q,t⟩ ⟨r,v⟩ he
    have hv (x : V d) : q.val x + t (c x) = r.val x + v (c x) :=
      congrArg (fun f : Q d s => f x) he
    have hu (x : V k) : q.val (u x) = r.val (u x) := by simpa [zero] using hv (u x)
    have ht : t = v := by
      apply QuadraticMap.ext
      intro x
      have := hv (a (u x))
      rw [decode,←q.property,←r.property,hu] at this
      exact add_left_cancel this
    subst v
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    apply QuadraticMap.ext
    intro x
    exact add_right_cancel (hv x)
  have bd := Nat.card_le_card_of_injective enc inj
  rw [Nat.card_prod,card_forms_exact,card_forms_exact] at bd
  exact bd
end OrbitUp
end
section
namespace OrbitUp
abbrev Incidence (d s : ℕ) := (a : L d) × (b : L s) × mixedFix a b
private noncomputable def mixedFixEquiv {d s : ℕ} (a : L d) (b : L s) :
    mixedFix a b ≃ MulAction.fixedBy (Q d s) (a,b) where
  toFun := fun ⟨q,hq⟩ => ⟨q, by
    apply QuadraticMap.ext
    intro x
    change b (q (a.symm x)) = q x
    simpa only [a.apply_symm_apply] using hq (a.symm x)⟩
  invFun := fun ⟨q,hq⟩ => ⟨q, fun x => by
    have h := congrArg (fun z : Q d s => z (a x)) hq
    change b (q (a.symm (a x))) = q (a x) at h
    simpa only [a.symm_apply_apply] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem incidence_eq_orbits_mul_group (d s : ℕ) :
    Nat.card (Incidence d s) = Nat.card (Classes d s) * Nat.card (Change d s) := by
  let e : Incidence d s ≃ (Σ g : Change d s, MulAction.fixedBy (Q d s) g) := {
    toFun := fun ⟨a,b,q⟩ => ⟨(a,b),mixedFixEquiv a b q⟩
    invFun := fun ⟨⟨a,b⟩,q⟩ => ⟨a,b,(mixedFixEquiv a b).symm q⟩
    left_inv := by rintro ⟨a,b,q⟩; rfl
    right_inv := by rintro ⟨⟨a,b⟩,q⟩; rfl }
  exact (Nat.card_congr (e.trans (MulAction.sigmaFixedByEquivOrbitsProdGroup (Change d s) (Q d s)))).trans (Nat.card_prod _ _)
theorem count_all_of_incidence {d s R : ℕ}
    (h : Nat.card (Incidence d s) ≤ (2^(2*d*R) + 2)*2^(s*(d+d*(d-1)/2))) :
    Nat.card (Classes d s) * 2^(d*(d-1)+s*(s-1)) ≤
      2^(s*(d+d*(d-1)/2)+(2*d*R+2)) := by
  rw [incidence_eq_orbits_mul_group] at h
  have hg : 2^(d*(d-1)+s*(s-1)) ≤ Nat.card (Change d s) := by
    rw [Nat.pow_add,Nat.card_prod]
    exact Nat.mul_le_mul (gl_lower d) (gl_lower s)
  have hf : 2^(2*d*R)+2 ≤ 2^(2*d*R+2) := by
    rw [Nat.pow_add]
    have hp : 0 < 2^(2*d*R) := Nat.two_pow_pos _
    omega
  calc
    _ ≤ Nat.card (Classes d s) * Nat.card (Change d s) := Nat.mul_le_mul_left _ hg
    _ ≤ _ := h
    _ ≤ 2^(2*d*R+2) * 2^(s*(d+d*(d-1)/2)) := Nat.mul_le_mul_right _ hf
    _ = _ := by rw [Nat.mul_comm, ← Nat.pow_add]
end OrbitUp
end
section
namespace OrbitUp
abbrev slotsN (d : ℕ) := d + d*(d-1)/2
theorem twice_slots (d : ℕ) : 2*slotsN d = d^2+d := by
  cases d with
  | zero => decide
  | succ n =>
    have he : 2*((n+1)*n/2)=(n+1)*n := by
      rcases Nat.even_or_odd n with ⟨k,h⟩ | ⟨k,h⟩
      · have h' : (n+1)*n=2*((n+1)*k) := by rw [h];ring
        rw [h',Nat.mul_div_cancel_left _ (by decide)]
      · have h' : (n+1)*n=2*((k+1)*n) := by rw [h];ring
        rw [h',Nat.mul_div_cancel_left _ (by decide)]
    dsimp only [slotsN]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at *
    nlinarith only [he]
theorem far_move_pays {d s r k : ℕ} (hm : 10000000 ≤ d+s) (hlo : d≤3*s)
    (hhi : 3*s≤2*d) (hr : d/128<r) (hmoves : r ≤ 2*k+2) :
    d*d+s*s ≤ s*slotsN k := by
  have hd : d≤300*k := by omega
  have hs : 360000 ≤ s := by omega
  have hsd : s ≤ d := by omega
  have h1 := Nat.mul_le_mul hd hd
  have h2 := Nat.mul_le_mul hsd hsd
  have hk := twice_slots k
  have h3 := Nat.mul_le_mul_right (slotsN k) hs
  nlinarith only [h1,h2,hk,h3]
theorem low_move_pays {d s r f : ℕ} (hhi : 3*s≤2*d)
    (hr : r≤d/128) (hf : r+f=d) :
    2*d*(d/128)+s*s ≤ slotsN f := by
  let R := d/128
  have hR : 128*R ≤ d := by dsimp [R];omega
  have hf' : 127*d ≤ 128*f := by omega
  have h1 := Nat.mul_le_mul hhi hhi
  have h2 := Nat.mul_le_mul hf' hf'
  have h3 := Nat.mul_le_mul_left d hR
  have h4 := twice_slots f
  change 2*d*R+s*s ≤ slotsN f
  nlinarith only [h1,h2,h3,h4]
theorem low_input_slack {d s : ℕ} (hm : 10000000 ≤ d+s) :
    27*(2*d*(d/128)+2) + 60*(d+s) ≤ 2*(d+s)^2 := by
  have h1 : 128*(d/128) ≤ d := by omega
  have h2 := Nat.mul_le_mul_left d h1
  have h3 := Nat.mul_le_mul_left (d+s) hm
  nlinarith only [h2,h3,hm,sq_nonneg (d:ℤ)]
theorem far_rank_slots {d s : ℕ} (hm : 10000000 ≤ d+s) (hfar : 3*s ≤ d ∨ 2*d ≤ 3*s) :
    27*(s*slotsN d)+10*(d+s)^2 ≤ 2*(d+s)^3 := by
  let m := d+s
  have slots := Nat.mul_le_mul_left s (le_of_eq (twice_slots d))
  have hmp := Nat.mul_le_mul_left (m^2) hm
  change 10000000 ≤ m at hm
  have gap : m^3 + 25*(27*s*d^2) ≤ 25*(4*m^3) := by
    rcases hfar with h | h
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le h
      dsimp [m]
      apply Nat.le.intro (k := 261*s^3+702*s^2*u+513*s*u^2+99*u^3)
      ring
    · have h' : 2*s ≥ d := by omega
      obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le h'
      have hh : d+s ≤ 5*u := by omega
      have hg₁ := Nat.mul_le_mul hh hh
      have hg₂ := Nat.mul_le_mul hg₁ (show d+s ≤ 4*d+s by omega)
      dsimp [m]
      nlinarith only [hg₂, congrArg (fun x : ℕ => (4*d+s)*x^2) hu,
          congrArg (fun x : ℕ => (4*d+s)*d*x) hu]
  dsimp [m] at hmp gap
  nlinarith only [slots,hmp,gap]
end OrbitUp
end
section
namespace OrbitUp
theorem orbit_rank_near {d s : ℕ} (hm : 10000000 ≤ d+s)
    (h : Nat.card (Incidence d s) ≤ (2^(2*d*(d/128))+2)*2^(s*slotsN d)) :
    Nat.card (Classes d s)^27 * 2^(10*(d+s)^2) ≤ 2^(2*(d+s)^3) := by
  let m := d+s
  let A := d*(d-1)+s*(s-1)
  let P := s*slotsN d
  let E := 2*d*(d/128)+2
  have hc := Nat.pow_le_pow_left (count_all_of_incidence h) 27
  change (Nat.card (Classes d s)*2^A)^27 ≤ (2^(P+E))^27 at hc
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hc
  have he : (P+E)*27+10*m^2 ≤ 2*m^3 + A*27 := by
    have hpoly := rank_powers d s
    have hslack := low_input_slack hm
    change 27*P + 12*m^2 ≤ 2*m^3+60*m+27*A at hpoly
    change 27*E + 60*m ≤ 2*m^2 at hslack
    omega
  apply Nat.le_of_mul_le_mul_right (c := 2^(A*27)) _ (Nat.two_pow_pos _)
  calc
    _ = (Nat.card (Classes d s)^27 * 2^(A*27)) * 2^(10*m^2) := Nat.mul_right_comm _ _ _
    _ ≤ 2^((P+E)*27) * 2^(10*m^2) := Nat.mul_le_mul_right _ hc
    _ = 2^((P+E)*27+10*m^2) := (Nat.pow_add _ _ _).symm
    _ ≤ 2^(2*m^3+A*27) := Nat.pow_le_pow_right (by decide) he
    _ = _ := Nat.pow_add _ _ _
theorem orbit_rank_far {d s : ℕ} (hm : 10000000 ≤ d+s) (hfar : 3*s≤d ∨ 2*d≤3*s) :
    Nat.card (Classes d s)^27 * 2^(10*(d+s)^2) ≤ 2^(2*(d+s)^3) := by
  letI : Finite (Q d s) := Finite.of_injective _ (@coefficients_injective d s)
  have hc : Nat.card (Classes d s) ≤ Nat.card (Q d s) :=
    Nat.card_le_card_of_surjective Quotient.mk'' Quotient.mk''_surjective
  have h := Nat.pow_le_pow_left (hc.trans (count_forms d s)) 27
  rw [← Nat.pow_mul] at h
  calc
    _ ≤ 2^((s*slotsN d)*27)*2^(10*(d+s)^2) := Nat.mul_le_mul_right _ h
    _ = 2^((s*slotsN d)*27+10*(d+s)^2) := (Nat.pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      rw [Nat.mul_comm (s*slotsN d) 27];exact far_rank_slots hm hfar)
end OrbitUp
end
section
namespace OrbitUp
theorem fixed_input_card {d s : ℕ} (a : L d) (b : L s) (hb : b ≠ 1) :
    let f := Module.finrank K (fixedSubspace a)
    Nat.card (mixedFix a b) * 2^(f+f*(f-1)/2) ≤ 2^(s*(d+d*(d-1)/2)) := by
  classical
  let f := Module.finrank K (fixedSubspace a)
  let e : fixedSubspace a ≃ₗ[K] V f := (Module.finBasis K _).equivFun
  let u : V f →ₗ[K] V d := (fixedSubspace a).subtype.comp e.symm.toLinearMap
  have au (x : V f) : a (u x) = u x := (mem_fixedSubspace a _).mp (e.symm x).property
  have injU : Function.Injective u := (fixedSubspace a).subtype_injective.comp e.symm.injective
  obtain ⟨c,cinv⟩ := u.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr injU)
  have cu (x : V f) : c (u x) = x := LinearMap.congr_fun cinv x
  obtain ⟨w,hw⟩ : ∃ w : V s, b w ≠ w := by
    by_contra! h
    exact hb (LinearEquiv.ext h)
  let line : V 1 →ₗ[K] V s := (LinearMap.id.smulRight w).comp (LinearMap.proj 0)
  let enc (p : mixedFix a b × Q f 1) : Q d s := p.1.val +
    line.compQuadraticMap (p.2.comp c)
  have delta (q : mixedFix a b) (t : Q f 1) (x : V f) :
      b (enc (q,t) (u x)) - enc (q,t) (u x) = t x 0 • (b w-w) := by
    change b (q.val (u x) + t (c (u x)) 0 • w) - (q.val (u x) + t (c (u x)) 0 • w) = _
    rw [cu,map_add,map_smul,q.property,au,smul_sub]
    abel
  have inj : Function.Injective enc := by
    rintro ⟨q,t⟩ ⟨r,v⟩ he
    have ht : t = v := by
      apply QuadraticMap.ext
      intro x
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      apply smul_left_injective K (sub_ne_zero.mpr hw)
      change (t x 0) • (b w - w) = (v x 0) • (b w - w)
      rw [←delta q t x,he,delta r v x]
    subst v
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    apply QuadraticMap.ext
    intro x
    apply add_right_cancel (b := line (t (c x)))
    exact congrArg (fun z : Q d s => z x) he
  have bd := Nat.card_le_card_of_injective enc inj
  rw [Nat.card_prod,card_forms_exact,card_forms_exact,one_mul] at bd
  exact bd
theorem rank_add_fixed {d : ℕ} (a : L d) :
    Module.finrank K (LinearMap.range (a.toLinearMap - LinearMap.id)) +
      Module.finrank K (fixedSubspace a) = d := by
  exact (a.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker.trans (by simp [V])
end OrbitUp
end
section
namespace OrbitUp
private theorem low_rank_factor {d r : ℕ} (f : V d →ₗ[K] V d)
    (h : Module.finrank K (LinearMap.range f) ≤ r) :
    ∃ t : (V d →ₗ[K] V r) × (V r →ₗ[K] V d), t.2.comp t.1 = f := by
  have hdim : Module.finrank K (LinearMap.range f) ≤ Module.finrank K (V r) := by
    simpa only [Module.finrank_fin_fun] using h
  obtain ⟨i, hi⟩ := finrank_le_iff_exists_linearMap.mp hdim
  obtain ⟨p, hp⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨⟨i.comp f.rangeRestrict, (LinearMap.range f).subtype.comp p⟩, ?_⟩
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (DFunLike.congr_fun hp (f.rangeRestrict x))
private lemma card_rectangular (d r : ℕ) :
    Nat.card (V d →ₗ[K] V r) = 2^(d*r) := by
  rw [Nat.card_congr (LinearMap.toMatrix' : (V d →ₗ[K] V r) ≃ₗ[K] Matrix (Fin r) (Fin d) K).toEquiv]
  change Nat.card (Fin r → Fin d → ZMod 2) = _
  simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, pow_mul]
theorem count_small_rank_changes (d r : ℕ) :
    Nat.card {a : L d // Module.finrank K (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ r}
      ≤ 2^(2*d*r) := by
  classical
  let _ (p q : ℕ) : Finite (V p →ₗ[K] V q) :=
    Finite.of_equiv (Matrix (Fin q) (Fin p) K) LinearMap.toMatrix'.symm.toEquiv
  let A := {a : L d // Module.finrank K (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ r}
  let f (a : A) := a.val.toLinearMap - LinearMap.id
  have fac (a : A) := low_rank_factor (r := r) (f a) a.property
  let code (a : A) := (fac a).choose
  have hi : Function.Injective code := by
    intro a b hab
    have he : f a = f b := (fac a).choose_spec.symm.trans
      ((congrArg (fun z : (V d →ₗ[K] V r) × (V r →ₗ[K] V d) => z.2.comp z.1) hab).trans (fac b).choose_spec)
    change a.val.toLinearMap - LinearMap.id = b.val.toLinearMap - LinearMap.id at he
    exact Subtype.ext (LinearEquiv.toLinearMap_injective (sub_left_inj.mp he))
  calc
    _ ≤ Nat.card ((V d →ₗ[K] V r) × (V r →ₗ[K] V d)) := Nat.card_le_card_of_injective code hi
    _ = _ := by
      rw [Nat.card_prod, card_rectangular, card_rectangular, ← pow_add]
      congr 1
      ring
end OrbitUp
end
section
namespace OrbitUp
noncomputable abbrev rankChange {d : ℕ} (a : L d) := Module.finrank K (LinearMap.range (a.toLinearMap - LinearMap.id))
abbrev Incidences (d s : ℕ) := (a : L d) × (b : L s) × mixedFix a b
private theorem sum_bound {A : Type*} [Fintype A] (f : A → ℕ) {c z : ℕ}
    (hA : Nat.card A ≤ c) (h : ∀ a, f a ≤ z) : ∑ a, f a ≤ c * z := by
  calc
    _ ≤ ∑ _a : A, z := Finset.sum_le_sum (fun a _ => h a)
    _ = Nat.card A * z := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := Nat.mul_le_mul_right _ hA
theorem incidence_stratified (d s R : ℕ)
    (hi : ∀ a : L d, R < rankChange a → ∃ k, Moves a k ∧ d*d+s*s ≤ s*(k+k*(k-1)/2))
    (lo : ∀ a : L d, rankChange a ≤ R →
      let f := Module.finrank K (fixedSubspace a)
      2*d*R+s*s ≤ f+f*(f-1)/2) :
    Nat.card (Incidences d s) ≤ (2^(2*d*R)+2)*2^(s*(d+d*(d-1)/2)) := by
  classical
  let _ := Fintype.ofFinite (L d)
  let _ := Fintype.ofFinite (L s)
  let N := 2^(s*(d+d*(d-1)/2))
  let F (a : L d) (b : L s) := Nat.card (mixedFix a b)
  let P (a : L d) := rankChange a ≤ R
  have small (a : {a // P a}) (b : {b : L s // b ≠ 1}) :
      F a.val b.val ≤ N / (2^(2*d*R+s*s)) := by
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).2
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (lo a.val a.property))).trans
      (fixed_input_card a.val b.val b.property)
  have large (a : {a // ¬P a}) (b : L s) :
      F a.val b ≤ N / (2^(d*d+s*s)) := by
    obtain ⟨k,hm,hk⟩ := hi a.val (Nat.lt_of_not_ge a.property)
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).2
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)).trans (moved_fixed_card b hm)
  have all_low : Nat.card {a // P a} ≤ 2^(2*d*R) := count_small_rank_changes d R
  have all_high : Nat.card {a // ¬P a} ≤ 2^(d*d) :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (gl_upper d)
  have outputs : Nat.card {b : L s // b ≠ 1} ≤ 2^(s*s) :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (gl_upper s)
  have smallrow (a : {a // P a}) :
      ∑ b : L s, F a.val b ≤ N+2^(s*s)*(N / 2^(2*d*R+s*s)) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 1]
    apply Nat.add_le_add _ (sum_bound _ outputs (small a))
    exact (Nat.card_le_card_of_injective Subtype.val (@Subtype.val_injective _ _)).trans_eq
      (card_forms_exact d s)
  have biggerow (a : {a // ¬P a}) :
      ∑ b : L s, F a.val b ≤ 2^(s*s)*(N / 2^(d*d+s*s)) :=
    sum_bound _ (gl_upper s) (large a)
  have lowtotal : (∑ a : {a // P a}, ∑ b : L s, F a.val b) ≤ 2^(2*d*R)*N + N := by
    apply (sum_bound _ all_low smallrow).trans
    rw [Nat.mul_add,← Nat.mul_assoc,←pow_add 2 (2*d*R) (s*s)]
    exact Nat.add_le_add_left (Nat.mul_div_le _ _) _
  have hightotal : (∑ a : {a // ¬P a}, ∑ b : L s, F a.val b) ≤ N := by
    apply (sum_bound _ all_high biggerow).trans
    rw [← Nat.mul_assoc,←pow_add]
    exact Nat.mul_div_le _ _
  calc
    _ = ∑ a : L d, ∑ b : L s, F a b := by
      rw [Incidences,Nat.card_sigma]
      exact Finset.sum_congr rfl (fun a _ => Nat.card_sigma)
    _ = _ := (Fintype.sum_subtype_add_sum_subtype P (fun a : L d => ∑ b : L s, F a b)).symm
    _ ≤ (2^(2*d*R)*N+N)+N := Nat.add_le_add lowtotal hightotal
    _ = _ := by dsimp [N]; ring
end OrbitUp
end
section
namespace OrbitUp
private theorem dimV (d : ℕ) : Module.finrank K (V d) = d := by
  simp [V]
private theorem cardW {d : ℕ} (W : Submodule K (V d)) :
    (W : Set (V d)).ncard = 2^Module.finrank K W := by
  classical
  let _ := Fintype.ofFinite W
  change Nat.card W = _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), ZMod.card]
private theorem find_extra {d k : ℕ} (a : L d) (W : Submodule K (V d))
    (hW : Module.finrank K W ≤ 2*k)
    (high : 2*k+2 < Module.finrank K (LinearMap.range (a.toLinearMap-LinearMap.id))) :
    ∃ v : V d, v ∉ W ∧ a v ∉ W ∧ a v-v ∉ W := by
  classical
  let f := a.toLinearMap - LinearMap.id
  let T := W.comap f
  let U := W.comap a.toLinearMap
  have hr : Module.finrank K f.range ≤ d := f.range.finrank_le.trans_eq (dimV _)
  have hT : T ≠ ⊤ := by
    intro he
    have hle : f.range ≤ W := by
      rintro _ ⟨x,rfl⟩
      exact (show x ∈ T by rw [he]; trivial)
    have := Submodule.finrank_mono hle
    change 2*k+2 < Module.finrank K f.range at high
    omega
  have hTd := (Submodule.finrank_lt hT).trans_eq (dimV d)
  have hUd : Module.finrank K U ≤ 2*k := by
    let g : U →ₗ[K] W := (a.toLinearMap.comp U.subtype).codRestrict W (fun x => x.property)
    have hi : Function.Injective g := fun x y h => Subtype.ext (a.injective (congrArg Subtype.val h))
    exact (LinearMap.finrank_le_finrank_of_injective hi).trans hW
  change 2*k+2 < Module.finrank K f.range at high
  let n := d-3
  have hd : d = n+3 := by dsimp [n]; omega
  have hUW : 2*k ≤ n := by omega
  have hTn : Module.finrank K T ≤ n+2 := by omega
  by_contra! hen
  have hall : (Set.univ : Set (V d)) ⊆ (W : Set (V d)) ∪ U ∪ T := by
    intro v _
    by_cases h : v ∈ W
    · exact Or.inl (Or.inl h)
    by_cases h' : a v ∈ W
    · exact Or.inl (Or.inr h')
    exact Or.inr (hen v h h')
  have hu := Set.ncard_le_ncard hall
  have h1 := Set.ncard_union_le (W : Set (V d)) U
  have h2 := Set.ncard_union_le ((W : Set (V d)) ∪ U) T
  simp only [Set.ncard_univ, V,Nat.card_fun,Nat.card_fin,Nat.card_zmod] at hu
  rw [cardW,cardW] at h1
  rw [cardW] at h2
  have p1 := Nat.pow_le_pow_right (n := 2) (by decide) (hW.trans hUW)
  have p2 := Nat.pow_le_pow_right (n := 2) (by decide) (hUd.trans hUW)
  have p3 := Nat.pow_le_pow_right (n := 2) (by decide) hTn
  have hpow : 2^d = 2^n*8 := by rw [hd,Nat.pow_add]
  rw [hpow] at hu
  rw [Nat.pow_add] at p3
  have hp := Nat.two_pow_pos n
  omega
private def pairMap {k d : ℕ} (a : L d) (u : V k →ₗ[K] V d) :=
  u.coprod (a.toLinearMap.comp u)
private def prepend {k d : ℕ} (u : V k →ₗ[K] V d) (b : V d) : V (k+1) →ₗ[K] V d where
  toFun x := x 0 • b + u (Fin.tail x)
  map_add' x y := by
    change (x 0+y 0) • b + u (Fin.tail x + Fin.tail y) = _
    rw [add_smul,map_add]
    abel
  map_smul' z x := by
    change (z * x 0) • b + u (z • Fin.tail x) = z • (x 0 • b + u (Fin.tail x))
    rw [mul_smul,map_smul,smul_add]
private theorem extend_pair {k d : ℕ} (a : L d) (u : V k →ₗ[K] V d)
    (hu : (pairMap a u).ker = ⊥)
    (high : 2*k+2 < Module.finrank K (LinearMap.range (a.toLinearMap-LinearMap.id))) :
    ∃ u' : V (k+1) →ₗ[K] V d, (pairMap a u').ker = ⊥ := by
  let W := (pairMap a u).range
  have hd : Module.finrank K W ≤ 2*k := by
    simpa only [Module.finrank_prod,dimV,two_mul] using (pairMap a u).finrank_range_le
  obtain ⟨b,hb,ha,hab⟩ := find_extra a W hd high
  refine ⟨prepend u b,LinearMap.ker_eq_bot'.mpr ?_⟩
  rintro ⟨x,y⟩ h
  change (x 0 • b + u (Fin.tail x)) + a (y 0 • b + u (Fin.tail y)) = 0 at h
  rw [map_add,map_smul] at h
  have hout : x 0 • b + y 0 • a b ∈ W := by
    have he : x 0 • b + y 0 • a b = -((pairMap a u) (Fin.tail x, Fin.tail y)) := by
      change _ = -(u (Fin.tail x) + a (u (Fin.tail y)))
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_assoc,add_left_comm,add_comm] using h
    rw [he]
    exact W.neg_mem ⟨_,rfl⟩
  have bits (z : K) : z=0 ∨ z=1 := (show ∀ w : K, w=0 ∨ w=1 by decide) z
  have hx : x 0 = 0 ∧ y 0 = 0 := by
    rcases bits (x 0) with hx|hx <;> rcases bits (y 0) with hy|hy
    · exact ⟨hx,hy⟩
    · exact False.elim (ha (by simpa [hx,hy] using hout))
    · exact False.elim (hb (by simpa [hx,hy] using hout))
    · apply False.elim (hab ?_)
      have hneg : -b=b := by
        funext i
        exact (show ∀ w : K, -w=w by decide) (b i)
      simpa [hx,hy,sub_eq_add_neg,hneg,add_comm] using hout
  simp [hx.1,hx.2] at h
  have ht : (Fin.tail x,Fin.tail y) = (0 : V k × V k) :=
    (LinearMap.ker_eq_bot'.mp hu) _ h
  apply Prod.ext
  · funext i
    exact Fin.cases hx.1 (congrFun (congrArg Prod.fst ht)) i
  · funext i
    exact Fin.cases hx.2 (congrFun (congrArg Prod.snd ht)) i
theorem exists_moves_rank {d : ℕ} (a : L d) : ∃ k,
    Module.finrank K (LinearMap.range (a.toLinearMap-LinearMap.id)) ≤ 2*k+2 ∧ Moves a k := by
  classical
  let P (k : ℕ) := ∃ u : V k →ₗ[K] V d, (pairMap a u).ker = ⊥
  have base : P 0 := ⟨0,LinearMap.ker_eq_bot'.mpr (fun x _ => Subsingleton.elim _ _)⟩
  let k := Nat.findGreatest P d
  obtain ⟨u,hu⟩ := Nat.findGreatest_spec (Nat.zero_le d) base
  refine ⟨k,?_,?_⟩
  · by_contra! h
    have hr := (LinearMap.range (a.toLinearMap-LinearMap.id)).finrank_le.trans_eq (dimV d)
    have hmax := Nat.findGreatest_is_greatest (P := P) (n := d) (k := k+1) (Nat.lt_succ_self _) (by omega)
    exact hmax (extend_pair a u hu h)
  · obtain ⟨g,hg⟩ := (pairMap a u).exists_leftInverse_of_injective hu
    refine ⟨u,(LinearMap.snd K (V k) (V k)).comp g,?_,?_⟩
    · intro x
      have h := congrArg Prod.snd (LinearMap.congr_fun hg (x,0))
      simpa [pairMap] using h
    · intro x
      have h := congrArg Prod.snd (LinearMap.congr_fun hg (0,x))
      simpa [pairMap] using h
end OrbitUp
end
section
namespace OrbitUp
theorem all_quadratic_orbits_upper (d s : ℕ) (hm : 10000000 ≤ d+s) :
    Nat.card (Classes d s)^27 * 2^(10*(d+s)^2) ≤ 2^(2*(d+s)^3) := by
  by_cases hnear : d ≤ 3*s ∧ 3*s ≤ 2*d
  · apply orbit_rank_near hm
    apply incidence_stratified d s (d/128)
    · intro a ha
      obtain ⟨k,hk,hmove⟩ := exists_moves_rank a
      exact ⟨k,hmove,far_move_pays hm hnear.1 hnear.2 ha hk⟩
    · intro a ha
      exact low_move_pays hnear.2 ha (rank_add_fixed a)
  · exact orbit_rank_far hm (by omega)
end OrbitUp
end
section
namespace OrbitUp
end OrbitUp
end
section
open CategoryTheory
namespace Erdos1160
end Erdos1160
end
section
namespace Erdos1160Growth
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
namespace BilinearExtension
variable {B : V →+ V →+ W}
open scoped commutatorElement
variable {V' W' : Type*} [AddCommGroup V'] [AddCommGroup W'] {C : V' →+ V' →+ W'}
end BilinearExtension
end Erdos1160Growth
end
section
namespace Erdos1160Growth.SharpFamily
end Erdos1160Growth.SharpFamily
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
abbrev V (d : ℕ) := Fin d → ZMod 2
abbrev Slot (d : ℕ) := (Σ i : Fin d, Fin i.val) ⊕ Fin d
abbrev P (d s : ℕ) := Slot d → V s
variable {d s : ℕ}
def row : Slot d → Fin d := Sum.elim Sigma.fst id
def col : Slot d → Fin d :=
  Sum.elim (fun h => ⟨h.2.val, h.2.isLt.trans h.1.isLt⟩) id
def form (a : P d s) : V d →+ V d →+ V s where
  toFun x :=
    { toFun := fun y => ∑ l, (x (row l) * y (col l)) • a l
      map_zero' := by simp
      map_add' := by
        intro y z
        simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib] }
  map_zero' := by ext y; simp
  map_add' := by
    intro x y
    ext z
    simp [add_mul, add_smul, Finset.sum_add_distrib]
abbrev G (a : P d s) := BilinearExtension (form a)
instance (a : P d s) : Finite (G a) := Finite.of_equiv _ (BilinearExtension.coordinateEquiv _).symm
def bundle (a : P d s) : FiniteGrp := FiniteGrp.of (G a)
def classOf (a : P d s) : Quotient (isIsomorphicSetoid FiniteGrp) := Quotient.mk _ (bundle a)
def Full (a : P d s) : Prop := Submodule.span (ZMod 2) (Set.range a) = ⊤
def classes (d s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp)) :=
  classOf '' {a : P d s | Full a}
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
variable {d s : ℕ}
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
variable {d s : ℕ}
lemma form_add (a b : P d s) : form (a+b) = form a + form b := by
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro y
  change (∑ l, (x (row l) * y (col l)) • (a l+b l)) =
    (∑ l, (x (row l) * y (col l)) • a l) + ∑ l, (x (row l) * y (col l)) • b l
  simp only [smul_add,Finset.sum_add_distrib]
lemma two_copies_zero (v : V s) : v+v = 0 := by
  ext i
  exact (show ∀ z : ZMod 2, z+z = 0 by decide) (v i)
def normalizedIso (A B : V d →+ V d →+ V s) :
    BilinearExtension (A + B.flip) ≃* BilinearExtension (A + B) where
  toFun x := ⟨x.base, x.fiber + B x.base x.base⟩
  invFun x := ⟨x.base, x.fiber - B x.base x.base⟩
  left_inv x := by apply BilinearExtension.ext; · rfl
                   exact add_sub_cancel_right _ _
  right_inv x := by apply BilinearExtension.ext; · rfl
                    exact sub_add_cancel _ _
  map_mul' x y := by
    apply BilinearExtension.ext
    · rfl
    · change (x.fiber + y.fiber + (A x.base y.base + B y.base x.base)) +
        B (x.base+y.base) (x.base+y.base) =
        (x.fiber+B x.base x.base) + (y.fiber+B y.base y.base) +
          (A x.base y.base + B x.base y.base)
      simp only [map_add,AddMonoidHom.add_apply]
      nth_rewrite 2 [← add_zero (B x.base y.base)]
      rw [← two_copies_zero (B y.base x.base)]
      abel
noncomputable def normalize_arrays (a b : P d s) :
    BilinearExtension (form a + (form b).flip) ≃* G (a+b) := by
  unfold G
  rw [form_add]
  exact normalizedIso (form a) (form b)
end Erdos1160Growth.LowerTriangularUpper
end
section
open scoped BigOperators commutatorElement
namespace Erdos1160Growth.TensorFamily
variable {d : ℕ}
end Erdos1160Growth.TensorFamily
end
section
namespace Erdos1160Growth.LowerTriangularUpper
variable {d s : ℕ}
def bit (i : Fin d) : V d := Pi.single i 1
lemma col_le_row (l : Slot d) : col l ≤ row l := by
  rcases l with ⟨i,j⟩|i
  · exact j.isLt.le
  · exact le_rfl
lemma slot_inj : Function.Injective (fun l : Slot d => (row l,col l)) := by
  rintro (⟨i,j⟩|i) (⟨k,n⟩|k) h
  · obtain rfl : i = k := congrArg Prod.fst h
    have hval : j.val = n.val := congrArg (fun p => (p.2 : Fin d).val) h
    obtain rfl : j = n := Fin.ext hval
    rfl
  · have h1 : i = k := congrArg Prod.fst h
    have h2 : j.val = k.val := congrArg (fun p => (p.2 : Fin d).val) h
    have hj := j.isLt
    subst k
    omega
  · have h1 : i = k := congrArg Prod.fst h
    have h2 : i.val = n.val := congrArg (fun p => (p.2 : Fin d).val) h
    have hn := n.isLt
    subst i
    omega
  · obtain rfl : i = k := congrArg Prod.fst h
    rfl
lemma form_at_slot (a : P d s) (l : Slot d) :
    form a (bit (row l)) (bit (col l)) = a l := by
  change (∑ k, (bit (row l) (row k) * bit (col l) (col k)) • a k) = a l
  rw [Fintype.sum_eq_single l]
  · simp [bit]
  · intro k hk
    by_cases hr : row k = row l
    · have hc : col k ≠ col l := fun hc => hk (slot_inj <| Prod.ext hr hc)
      simp [bit,Pi.single_apply,hc]
    · simp [bit,Pi.single_apply,hr]
lemma form_above (a : P d s) (i j : Fin d) (h : i < j) :
    form a (bit i) (bit j) = 0 := by
  change (∑ l, (bit i (row l) * bit j (col l)) • a l) = 0
  apply Finset.sum_eq_zero
  intro l _
  by_cases hr : row l = i
  · have hc : col l ≠ j := by
      intro hc
      have hrc := col_le_row l
      rw [hr,hc] at hrc
      exact h.not_ge hrc
    simp [bit,Pi.single_apply,hc]
  · simp [bit,Pi.single_apply,hr]
lemma addhom_eq_bits {W : Type*} [AddCommGroup W] (b c : V d →+ W)
    (h : ∀ i, b (bit i) = c (bit i)) : b = c := by
  apply AddMonoidHom.ext
  intro x
  induction x using Pi.single_induction with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | single i a =>
    have hbit : ∀ b : ZMod 2, b=0 ∨ b=1 := by decide
    rcases hbit a with rfl|rfl
    · simp
    · exact h i
def lowerArray (B : V d →+ V d →+ V s) : P d s := fun l => B (bit (row l)) (bit (col l))
def upperArray (B : V d →+ V d →+ V s) : P d s := fun l =>
  if row l = col l then 0 else B (bit (col l)) (bit (row l))
lemma split_matrix (B : V d →+ V d →+ V s) :
    B = form (lowerArray B) + (form (upperArray B)).flip := by
  apply addhom_eq_bits
  intro i
  apply addhom_eq_bits
  intro j
  change B (bit i) (bit j) = form (lowerArray B) (bit i) (bit j) +
    form (upperArray B) (bit j) (bit i)
  rcases lt_trichotomy i j with hij | rfl | hji
  · let l : Slot d := .inl ⟨j,⟨i.val,hij⟩⟩
    rw [form_above _ _ _ hij,zero_add]
    change _ = form (upperArray B) (bit (row l)) (bit (col l))
    rw [form_at_slot]
    simp [upperArray,l,row,col,ne_of_gt hij]
  · let l : Slot d := .inr i
    change _ = form (lowerArray B) (bit (row l)) (bit (col l)) +
      form (upperArray B) (bit (row l)) (bit (col l))
    rw [form_at_slot,form_at_slot]
    simp [l,row,col,lowerArray,upperArray]
  · let l : Slot d := .inl ⟨i,⟨j.val,hji⟩⟩
    rw [form_above _ _ _ hji,add_zero]
    change _ = form (lowerArray B) (bit (row l)) (bit (col l))
    rw [form_at_slot]
    rfl
noncomputable def allBilinear_normal (B : V d →+ V d →+ V s) :
    BilinearExtension B ≃* G (lowerArray B + upperArray B) := by
  let castLaw {b c : V d →+ V d →+ V s} (h : b = c) : BilinearExtension b ≃* BilinearExtension c := h ▸ MulEquiv.refl _
  apply (castLaw (split_matrix B)).trans
  exact normalize_arrays _ _
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
variable {d s : ℕ}
lemma square_span_eq (B : V d →+ V d →+ V s) :
    Submodule.span (ZMod 2) (Set.range (fun x => B x x)) =
      Submodule.span (ZMod 2) (Set.range (lowerArray B + upperArray B)) := by
  let C := lowerArray B + upperArray B
  let K := Submodule.span (ZMod 2) (Set.range (fun x => B x x))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have hsplit := congrArg (fun L : V d →+ V d →+ V s => L x x) (split_matrix B)
    change B x x = form (lowerArray B) x x + form (upperArray B) x x at hsplit
    have hsum := congrArg (fun L : V d →+ V d →+ V s => L x x) (form_add (lowerArray B) (upperArray B))
    change form C x x = form (lowerArray B) x x + form (upperArray B) x x at hsum
    change B x x ∈ Submodule.span (ZMod 2) (Set.range C)
    rw [hsplit,←hsum]
    apply Submodule.sum_mem
    intro l _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨l,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,rfl⟩
    have diagonal (x : V d) : B x x ∈ K := Submodule.subset_span ⟨x,rfl⟩
    rcases l with ⟨i,j⟩ | i
    · let k : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩
      have hk : k < i := j.isLt
      change B (bit i) (bit k) + (if i = k then 0 else B (bit k) (bit i)) ∈ K
      rw [if_neg (ne_of_gt hk)]
      have h := K.sub_mem (K.sub_mem (diagonal (bit i + bit k)) (diagonal (bit i))) (diagonal (bit k))
      simp only [map_add,AddMonoidHom.add_apply] at h
      convert h using 1 <;> abel
    · change B (bit i) (bit i) + (if i=i then 0 else _) ∈ K
      simpa using diagonal (bit i)
private def bundleB (B : V d →+ V d →+ V s) : FiniteGrp :=
  have : Finite (BilinearExtension B) := Finite.of_equiv _ (BilinearExtension.coordinateEquiv _).symm
  FiniteGrp.of (BilinearExtension B)
def bilinearClasses (d s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp)) :=
  (fun B : V d →+ V d →+ V s => Quotient.mk _ (bundleB B)) ''
    {B | Submodule.span (ZMod 2) (Set.range (fun x => B x x)) = ⊤}
lemma classes_finite (d s : ℕ) : (classes d s).Finite :=
  (Set.toFinite {a : P d s | Full a}).image _
lemma bilinearClasses_subset (d s : ℕ) : bilinearClasses d s ⊆ classes d s := by
  rintro _ ⟨B,hB,rfl⟩
  refine ⟨lowerArray B+upperArray B, ?_, ?_⟩
  · change Submodule.span (ZMod 2) (Set.range _) = ⊤
    rw [←square_span_eq]
    exact hB
  · symm
    apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (bundleB B).toGrp)
        (Y := (bundle (lowerArray B+upperArray B)).toGrp) (allBilinear_normal B))⟩
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
structure CentralData (E : Type*) [Group E] (d s : ℕ) where
  incl : Multiplicative (V s) →* E
  proj : E →* Multiplicative (V d)
  incl_inj : Function.Injective incl
  proj_onto : Function.Surjective proj
  exact_ker : proj.ker = incl.range
  central : ∀ v : Multiplicative (V s), ∀ x : E, Commute (incl v) x
namespace CentralData
variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)
def liftK (w : V s) : E := S.incl (Multiplicative.ofAdd w)
def base (x : E) : V d := (S.proj x).toAdd
@[simp] lemma liftK_zero : S.liftK 0 = 1 := S.incl.map_one
@[simp] lemma liftK_add (a b : V s) : S.liftK (a+b) = S.liftK a * S.liftK b := S.incl.map_mul ..
@[simp] lemma base_one : S.base 1 = 0 := congrArg Multiplicative.toAdd S.proj.map_one
@[simp] lemma base_mul (x y : E) : S.base (x*y) = S.base x + S.base y :=
  congrArg Multiplicative.toAdd (S.proj.map_mul ..)
lemma liftK_comm (v : V s) (x : E) : Commute (S.liftK v) x := S.central _ _
lemma liftK_inj : Function.Injective S.liftK := fun _ _ h => congrArg Multiplicative.toAdd (S.incl_inj h)
lemma liftK_mem (v : V s) : S.base (S.liftK v) = 0 := by
  change S.liftK v ∈ S.proj.ker
  rw [S.exact_ker]
  exact ⟨_,rfl⟩
lemma exists_lift {x : E} (hx : S.base x = 0) : ∃ w : V s, S.liftK w = x := by
  change x ∈ S.proj.ker at hx
  rw [S.exact_ker] at hx
  exact hx
lemma base_onto : Function.Surjective S.base := fun w => S.proj_onto (Multiplicative.ofAdd w)
lemma exists_square (x : E) : ∃ w, S.liftK w = x*x := by
  apply S.exists_lift
  rw [base_mul,two_copies_zero]
end CentralData
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
lemma exist_elementary_coords {G : Type*} [Group G] [Finite G] {d : ℕ}
    (h : ∀ x : G, x*x=1) (hcard : Nat.card G = 2^d) :
    Nonempty (G ≃* Multiplicative (V d)) := by
  classical
  have hinv (x : G) : x⁻¹=x := inv_eq_of_mul_eq_one_left (h x)
  let _ : CommGroup G := { ‹Group G› with
    mul_comm := fun x y => by
      calc x*y = (x*y)⁻¹ := (hinv _).symm
           _ = y*x := by rw [mul_inv_rev,hinv,hinv] }
  let _ : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    exact h x.toMul)
  let _ : Fintype (Additive G) := Fintype.ofFinite _
  have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive G)
  rw [← Nat.card_eq_fintype_card, ZMod.card] at hc
  change Nat.card G = 2^Module.finrank (ZMod 2) (Additive G) at hc
  rw [hcard] at hc
  have hd : Module.finrank (ZMod 2) (Additive G) = d :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm
  let e := (Module.finBasisOfFinrankEq (ZMod 2) (Additive G) hd).equivFun
  exact ⟨e.toAddEquiv.toMultiplicativeRight⟩
noncomputable def dataOfSubgroup {G : Type*} [Group G] (H : Subgroup G) [H.Normal] {d s : ℕ}
    (hc : H ≤ Subgroup.center G) (h : H ≃* Multiplicative (V s))
    (q : G ⧸ H ≃* Multiplicative (V d)) : CentralData G d s where
  incl := H.subtype.comp h.symm.toMonoidHom
  proj := q.toMonoidHom.comp (QuotientGroup.mk' H)
  incl_inj := Subtype.val_injective.comp h.symm.injective
  proj_onto := q.surjective.comp (QuotientGroup.mk'_surjective H)
  exact_ker := by
    ext x
    constructor
    · intro hx
      change q ((QuotientGroup.mk' H) x) = 1 at hx
      have hh : x ∈ H := (QuotientGroup.eq_one_iff x).mp (q.injective (hx.trans q.map_one.symm))
      exact ⟨h ⟨x,hh⟩,by simp⟩
    · rintro ⟨w,rfl⟩
      change q ((QuotientGroup.mk' H) ((h.symm w : H) : G)) = 1
      simp
  central v x := by
    have hcomm := Subgroup.mem_center_iff.mp (hc (h.symm v).property) x
    exact hcomm.symm
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper.CentralData
open CategoryTheory
variable {E : Type*} [Group E] {d s : ℕ}
variable (S : CentralData E d s) (σ : V d → E) (B : V d →+ V d →+ V s)
variable (hπ : ∀ x, S.base (σ x) = x)
variable (hmul : ∀ x y, σ x * σ y = S.liftK (B x y) * σ (x+y))
include hmul in
theorem section_zero : σ 0 = 1 := by
  have he := hmul 0 0
  simp only [map_zero,S.liftK_zero,one_mul,zero_add] at he
  exact mul_right_cancel (b := σ 0) (he.trans (one_mul _).symm)
include hπ in
theorem section_decomp (z : E) : ∃ w, S.liftK w * σ (S.base z) = z := by
  have hb : S.base (z * (σ (S.base z))⁻¹) = 0 := by
    change (S.proj (z * (σ (S.base z))⁻¹)).toAdd = 0
    rw [map_mul, map_inv]
    change S.base z + -S.base (σ (S.base z)) = 0
    rw [hπ,add_neg_cancel]
  obtain ⟨w,hw⟩ := S.exists_lift hb
  exact ⟨w, by rw [hw, mul_assoc, inv_mul_cancel, mul_one]⟩
def sectionHom : BilinearExtension B →* E where
  toFun z := S.liftK z.fiber * σ z.base
  map_one' := by simp [section_zero S σ B hmul]
  map_mul' x y := by
    change S.liftK (x.fiber+y.fiber+B x.base y.base)*σ (x.base+y.base) = _
    rw [S.liftK_add, S.liftK_add, mul_assoc, mul_assoc, ← hmul]
    rw [mul_assoc, (S.liftK_comm y.fiber (σ x.base)).symm.left_comm]
noncomputable def sectionEquiv : BilinearExtension B ≃* E := by
  apply MulEquiv.ofBijective (sectionHom S σ B hmul)
  constructor
  · rintro ⟨u,w⟩ ⟨v,t⟩ h
    change S.liftK w * σ u = S.liftK t * σ v at h
    have hb := congrArg S.base h
    simp only [S.base_mul, S.liftK_mem, zero_add, hπ] at hb
    subst v
    obtain rfl := S.liftK_inj (mul_right_cancel h)
    rfl
  · intro z
    obtain ⟨w,hw⟩ := S.section_decomp σ hπ z
    exact ⟨⟨S.base z,w⟩,hw⟩
include hπ hmul in
theorem squares_eq_diagonal :
    {w : V s | ∃ z : E, S.liftK w = z*z} = Set.range (fun u => B u u) := by
  ext w
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨t,ht⟩ := S.section_decomp σ hπ z
    refine ⟨S.base z, S.liftK_inj ?_⟩
    have h_square : (S.liftK t * σ (S.base z))*(S.liftK t * σ (S.base z)) =
        S.liftK (B (S.base z) (S.base z)) := by
      rw [mul_assoc, (S.liftK_comm t (σ (S.base z))).symm.left_comm, ← mul_assoc]
      rw [← S.liftK_add, two_copies_zero, S.liftK_zero, one_mul,hmul,
        two_copies_zero,section_zero S σ B hmul,mul_one]
    rw [ht] at h_square
    exact h_square.symm.trans hz.symm
  · rintro ⟨u,rfl⟩
    refine ⟨σ u, ?_⟩
    rw [hmul, two_copies_zero,section_zero S σ B hmul,mul_one]
end Erdos1160Growth.LowerTriangularUpper.CentralData
end
section
namespace Erdos1160Growth.LowerTriangularUpper.CentralData
open scoped commutatorElement
theorem exists_commCode {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s) (g : E) :
    ∃ h : E →* Multiplicative (V s), (∀ x, g * x = S.liftK (h x).toAdd * x * g) ∧
      (∀ w, h (S.liftK w) = 1) := by
  classical
  have hc (x : E) : ⁅g, x⁆ ∈ S.incl.range := by
    rw [← S.exact_ker]
    change S.proj ⁅g, x⁆ = 1
    simpa only [map_commutatorElement] using
      (commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (S.proj g) (S.proj x)))
  choose c he using hc
  have central (x y : E) : Commute ⁅g, x⁆ y := he x ▸ S.central (c x) y
  let h : E →* Multiplicative (V s) := {
    toFun := c
    map_one' := S.incl_inj (by rw [he, commutatorElement_one_right, S.incl.map_one])
    map_mul' := fun x y => S.incl_inj (by
      rw [he, S.incl.map_mul, he, he, commutatorElement_mul_right_eq_mul_conj]
      rw [mul_assoc ⁅g, x⁆ x, (central y x).symm.eq, ← mul_assoc, mul_inv_cancel_right]) }
  refine ⟨h, ?_, ?_⟩
  · intro x
    change g * x = S.incl (c x) * x * g
    rw [he, commutatorElement_def]
    group
  · intro w
    apply S.incl_inj
    change S.incl (c (S.liftK w)) = S.incl 1
    rw [he, S.incl.map_one]
    exact (S.liftK_comm w g).symm.commutator_eq
end Erdos1160Growth.LowerTriangularUpper.CentralData
end
section
namespace Erdos1160Growth.LowerTriangularUpper.CentralData
variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)
structure Collected where
  sec : V d → E
  bil : V d →+ V d →+ V s
  sec_zero : sec 0 = 1
  sec_mul : ∀ x y, sec x * sec y = S.liftK (bil x y) * sec (x+y)
private lemma two_bits (b : ZMod 2) : b = 0 ∨ b = 1 :=
  (show ∀ b : ZMod 2, b=0 ∨ b=1 by decide) b
def useBit (g : E) (b : ZMod 2) : E := if b=1 then g else 1
lemma bit_product (g : E) (z : V s) (hz : S.liftK z = g*g) (a b : ZMod 2) :
    useBit g a * useBit g b = S.liftK ((a*b) • z) * useBit g (a+b) := by
  rcases two_bits a with rfl|rfl <;> rcases two_bits b with rfl|rfl <;>
    simp [useBit,show (1+1 : ZMod 2) = 0 by decide,hz]
lemma bit_cross (g y : E) (v : V s) (h : g*y = S.liftK v * y * g) (u : ZMod 2) :
    useBit g u * y = S.liftK (u • v) * y * useBit g u := by
  rcases two_bits u with rfl|rfl <;> simp [useBit,h]
lemma product_collect (x b y b' X B : E) (a c z : V s)
    (hbase : x*y = S.liftK a * X)
    (hcross : b*y = S.liftK c * y * b)
    (hbit : b*b' = S.liftK z * B) :
    (x*b)*(y*b') = S.liftK (a+c+z) * (X*B) := by
  calc
    _ = x*(b*y)*b' := by group
    _ = (x*S.liftK c)*(y*(b*b')) := by rw [hcross]; group
    _ = S.liftK c*((x*y)*(b*b')) := by rw [←(S.liftK_comm c x).eq]; group
    _ = S.liftK c*((S.liftK a*X)*(S.liftK z*B)) := by rw [hbase,hbit]
    _ = S.liftK c*(S.liftK a*(X*S.liftK z)*B) := by group
    _ = S.liftK (c+a+z)*(X*B) := by rw [←(S.liftK_comm z X).eq]; simp [mul_assoc]
    _ = _ := by rw [add_comm c a]
def crossBilinear (i : Fin d) (L : V d →+ V s) (z : V s) : V d →+ V d →+ V s where
  toFun x :=
    { toFun := fun y => x i • L y + (x i * y i) • z
      map_zero' := by simp
      map_add' := by intro a b; simp [map_add,smul_add,mul_add,add_smul]; abel }
  map_zero' := by apply AddMonoidHom.ext; intro x; simp
  map_add' := by
    intro x y
    apply AddMonoidHom.ext
    intro v
    simp [add_mul, add_smul]
    abel
noncomputable def codeLinear (C : Collected S) (h : E →* Multiplicative (V s))
    (hc : ∀ w, h (S.liftK w) = 1) : V d →+ V s where
  toFun x := (h (C.sec x)).toAdd
  map_zero' := by rw [C.sec_zero,map_one]; rfl
  map_add' x y := by
    have hm := congrArg h (C.sec_mul x y)
    rw [map_mul, map_mul, hc, one_mul] at hm
    exact congrArg Multiplicative.toAdd hm.symm
noncomputable def adjoin (C : Collected S) (g : E) (i : Fin d) : Collected S := by
  let z := Classical.choose (S.exists_square g)
  have hz : S.liftK z = g*g := Classical.choose_spec (S.exists_square g)
  let h := Classical.choose (S.exists_commCode g)
  have hh := Classical.choose_spec (S.exists_commCode g)
  let L := S.codeLinear C h hh.2
  exact
    { sec := fun x => C.sec x * useBit g (x i)
      bil := C.bil + crossBilinear i L z
      sec_zero := by simp [C.sec_zero,useBit]
      sec_mul := by
        intro x y
        exact S.product_collect _ _ _ _ _ _ (C.bil x y) (x i • L y) ((x i*y i) • z)
          (C.sec_mul x y) (S.bit_cross g (C.sec y) (L y) (hh.1 _) (x i))
          (S.bit_product g z hz (x i) (y i)) |>.trans (by
            congr 2
            exact add_assoc _ _ _) }
end Erdos1160Growth.LowerTriangularUpper.CentralData
end
section
namespace Erdos1160Growth.LowerTriangularUpper.CentralData
variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)
def emptyCollected : Collected S where
  sec _ := 1
  bil := 0
  sec_zero := rfl
  sec_mul x y := by change 1*1 = S.liftK 0 * 1; simp
lemma base_useBit (g : E) (i : Fin d) (hg : S.base g = bit i) (b : ZMod 2) :
    S.base (useBit g b) = Pi.single i b := by
  rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) b with rfl|rfl <;>
    simp [useBit,bit,hg]
theorem collected_on (I : Finset (Fin d)) :
    ∃ C : Collected S, ∀ x, S.base (C.sec x) = ∑ i ∈ I, Pi.single i (x i) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨S.emptyCollected, fun x => by simp [emptyCollected]⟩
  | insert i I hi ih =>
    obtain ⟨C,hC⟩ := ih
    obtain ⟨g,hg⟩ := S.base_onto (bit i)
    refine ⟨S.adjoin C g i, ?_⟩
    intro x
    change S.base (C.sec x * useBit g (x i)) = _
    rw [S.base_mul, hC, S.base_useBit g i hg, Finset.sum_insert hi, add_comm]
theorem exists_bilinear_section :
    ∃ (σ : V d → E) (B : V d →+ V d →+ V s),
      (∀ x, S.base (σ x) = x) ∧ (∀ x y, σ x * σ y = S.liftK (B x y) * σ (x+y)) := by
  obtain ⟨C,hC⟩ := S.collected_on Finset.univ
  refine ⟨C.sec,C.bil,?_,C.sec_mul⟩
  intro x
  exact (hC x).trans (Finset.univ_sum_single x)
end Erdos1160Growth.LowerTriangularUpper.CentralData
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
namespace CentralData
variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)
def SquaresGenerate : Prop :=
  S.incl.range ≤ Subgroup.closure (Set.range (fun z : E => z*z))
theorem square_span_top (h : S.SquaresGenerate) :
    Submodule.span (ZMod 2) {w : V s | ∃ z : E, S.liftK w = z*z} = ⊤ := by
  let K := Submodule.span (ZMod 2) {w : V s | ∃ z : E, S.liftK w = z*z}
  let H := (AddSubgroup.toSubgroup K.toAddSubgroup).map S.incl
  have hsq : Subgroup.closure (Set.range (fun z : E => z*z)) ≤ H := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨z,rfl⟩
    obtain ⟨w,hw⟩ := S.exists_square z
    refine ⟨Multiplicative.ofAdd w, ?_,hw⟩
    change w ∈ K
    exact Submodule.subset_span ⟨z,hw⟩
  apply top_unique
  intro w _
  have hw : S.liftK w ∈ H := hsq (h ⟨Multiplicative.ofAdd w,rfl⟩)
  obtain ⟨v,hv,he⟩ := hw
  have he' : v.toAdd = w := congrArg Multiplicative.toAdd (S.incl_inj he)
  exact he' ▸ hv
variable {E : FiniteGrp.{0}}
theorem class_mem_of_section (S : CentralData E d s) (σ : V d → E)
    (B : V d →+ V d →+ V s) (hπ : ∀ x, S.base (σ x) = x)
    (hmul : ∀ x y, σ x * σ y = S.liftK (B x y) * σ (x+y))
    (h : Submodule.span (ZMod 2) {w : V s | ∃ z : E, S.liftK w = z*z} = ⊤) :
    Quotient.mk _ E ∈ bilinearClasses d s := by
  refine ⟨B,?_,?_⟩
  · change Submodule.span (ZMod 2) (Set.range (fun u => B u u)) = ⊤
    rwa [← S.squares_eq_diagonal σ B hπ hmul]
  · apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := GrpCat.of (BilinearExtension B)) (Y := E.toGrp)
        (S.sectionEquiv σ B hπ hmul))⟩
theorem class_mem (S : CentralData E d s) (h : S.SquaresGenerate) :
    Quotient.mk _ E ∈ bilinearClasses d s := by
  obtain ⟨σ,B,hπ,hmul⟩ := S.exists_bilinear_section
  exact S.class_mem_of_section σ B hπ hmul (S.square_span_top h)
end CentralData
def intrinsicClasses (d s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | ∃ S : CentralData E d s, S.SquaresGenerate}
theorem intrinsicClasses_subset (d s : ℕ) : intrinsicClasses d s ⊆ bilinearClasses d s := by
  rintro _ ⟨E,⟨S,hS⟩,rfl⟩
  exact S.class_mem hS
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
def squareCore (E : Type*) [Group E] : Subgroup E :=
  Subgroup.closure (Set.range fun x : E => x*x)
def squareCoreClasses (d s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | squareCore E ≤ Subgroup.center E ∧
    (∀ x : squareCore E, x*x = 1) ∧ Nat.card (squareCore E) = 2^s ∧
    (squareCore E).index = 2^d}
lemma squareCoreClasses_subset (d s : ℕ) : squareCoreClasses d s ⊆ intrinsicClasses d s := by
  rintro _ ⟨E, ⟨hc,he,hw,hv⟩,rfl⟩
  let K := squareCore E
  let _ : K.Normal :=
    { conj_mem := fun n hn g => by
        have hh := Subgroup.mem_center_iff.mp (hc hn) g
        rwa [hh,mul_inv_cancel_right] }
  have hxq (x : E ⧸ K) : x*x = 1 := by
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_closure ⟨a,rfl⟩
  obtain ⟨h⟩ := exist_elementary_coords he hw
  have hv' : Nat.card (E ⧸ K) = 2^d := by rwa [← Subgroup.index_eq_card]
  obtain ⟨q⟩ := exist_elementary_coords hxq hv'
  let S := dataOfSubgroup K hc h q
  refine ⟨E,⟨S,?_⟩,rfl⟩
  rintro x ⟨w,rfl⟩
  exact (h.symm w).property
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
private lemma frattini_f2 : frattini (Multiplicative (ZMod 2)) = ⊥ := by
  let _ : Fact (Nat.card (Multiplicative (ZMod 2))).Prime := ⟨by
    change (Nat.card (ZMod 2)).Prime
    rw [Nat.card_zmod]
    decide⟩
  apply le_antisymm _ bot_le
  apply frattini_le_coatom
  refine ⟨bot_ne_top, ?_⟩
  intro H h
  exact H.eq_bot_or_eq_top_of_prime_card.resolve_left (ne_of_gt h)
instance squareCore_normal {E : Type*} [Group E] : (squareCore E).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_closure_iff.mpr
  rintro h _ _ ⟨g,rfl⟩
  apply Subgroup.subset_closure
  exact ⟨h*g*h⁻¹, by group⟩
theorem frattini_le_squareCore {E : Type*} [Group E] [Finite E] : frattini E ≤ squareCore E := by
  let K := squareCore E
  let π := QuotientGroup.mk' K
  have hq (x : E ⧸ K) : x*x=1 := by
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨y,rfl⟩)
  have htwo : IsPGroup 2 (E ⧸ K) := fun x => ⟨1, by rw [pow_one,pow_two]; exact hq x⟩
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  obtain ⟨e⟩ := exist_elementary_coords hq hn
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply e.injective
  rw [map_one]
  have heval (i : Fin n) :
      ((e (π x)).toAdd i) = 0 := by
    let f : Multiplicative (V n) →* Multiplicative (ZMod 2) :=
      { toFun := fun v => Multiplicative.ofAdd (v.toAdd i)
        map_mul' := fun _ _ => rfl
        map_one' := rfl }
    have onto_f : Function.Surjective f := fun v => ⟨Multiplicative.ofAdd (fun _ => v.toAdd),rfl⟩
    let ψ := f.comp (e.toMonoidHom.comp π)
    have hφ : Function.Surjective ψ := onto_f.comp (e.surjective.comp (QuotientGroup.mk'_surjective K))
    have hmem := (frattini_le_comap_frattini_of_surjective hφ) hx
    change ψ x ∈ frattini (Multiplicative (ZMod 2)) at hmem
    rw [frattini_f2] at hmem
    exact congrArg Multiplicative.toAdd (Subgroup.mem_bot.mp hmem)
  exact congrArg Multiplicative.ofAdd (funext heval)
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
theorem coatom_index_prime_pow {G : Type*} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (hc : Nat.card G = p^m) (H : Subgroup G) (hH : IsCoatom H) : H.index = p := by
  let hp := (Fact.out : p.Prime)
  have hg : IsPGroup p G := IsPGroup.of_card hc
  obtain ⟨h,hh⟩ := (hg.to_subgroup H).exists_card_eq
  have hlt : h < m := by
    have ht : Nat.card H < Nat.card G := lt_of_le_of_ne (H.card_le_card_group) (fun he => hH.1 (H.eq_top_of_card_eq he))
    rw [hh,hc] at ht
    exact lt_of_not_ge (fun hi => ht.not_ge (Nat.pow_le_pow_right hp.pos hi))
  obtain ⟨J,hJ,hle⟩ := Sylow.exists_subgroup_card_pow_succ (G := G)
    (hc ▸ pow_dvd_pow p (show h+1 ≤ m by omega)) hh
  have hne : H ≠ J := by
    intro he
    rw [← he,hh] at hJ
    exact (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self h)).ne hJ
  have htop := hH.2 J (lt_of_le_of_ne hle hne)
  have heq := H.index_mul_card
  rw [htop,Subgroup.card_top] at hJ
  rw [hJ,hh,pow_succ,Nat.mul_comm (p^h) p] at heq
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hp.pos) heq
theorem squares_le_frattini {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hc : Nat.card G = 2^m) :
    Subgroup.closure (Set.range (fun z : G => z*z)) ≤ frattini G := by
  simp only [frattini,Order.radical,le_iInf_iff]
  intro H hH
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨z,rfl⟩
  exact H.mul_self_mem_of_index_two (coatom_index_prime_pow hc H hH) z
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
theorem frattini_eq_squareCore {G : Type*} [Group G] [Finite G] {m : ℕ}
    (h : Nat.card G = 2^m) : frattini G = squareCore G :=
  le_antisymm frattini_le_squareCore (squares_le_frattini h)
def frattiniClasses (d s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | frattini E ≤ Subgroup.center E ∧
    (∀ x : frattini E, x*x = 1) ∧ Nat.card (frattini E) = 2^s ∧ (frattini E).index = 2^d}
theorem frattiniClasses_subset (d s : ℕ) : frattiniClasses d s ⊆ squareCoreClasses d s := by
  rintro _ ⟨E, h,rfl⟩
  change frattini E ≤ Subgroup.center E ∧ _ at h
  have hcard := (frattini E).index_mul_card
  rw [h.2.2.1, h.2.2.2, ←pow_add] at hcard
  refine ⟨E,?_,rfl⟩
  change squareCore E ≤ Subgroup.center E ∧ _
  rwa [←frattini_eq_squareCore hcard.symm]
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
variable {d s : ℕ}
def diagonalQ (B : V d →+ V d →+ V s) : OrbitUp.Q d s :=
  LinearMap.BilinMap.toQuadraticMap
    (((AddMonoidHom.toZModLinearMapEquiv 2).toAddMonoidHom.comp B).toZModLinearMap 2)
def pushB (g : OrbitUp.Change d s) (B : V d →+ V d →+ V s) : V d →+ V d →+ V s where
  toFun x := g.2.toAddMonoidHom.comp ((B (g.1.symm x)).comp g.1.symm.toAddMonoidHom)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
def pushIso (g : OrbitUp.Change d s) (B : V d →+ V d →+ V s) :
    BilinearExtension B ≃* BilinearExtension (pushB g B) where
  toFun x := ⟨g.1 x.base, g.2 x.fiber⟩
  invFun x := ⟨g.1.symm x.base, g.2.symm x.fiber⟩
  left_inv _ := by apply BilinearExtension.ext <;> simp
  right_inv _ := by apply BilinearExtension.ext <;> simp
  map_mul' x y := by
    apply BilinearExtension.ext
    · exact map_add _ _ _
    · change g.2 (x.fiber+y.fiber+B x.base y.base) =
        g.2 x.fiber + g.2 y.fiber + g.2 (B (g.1.symm (g.1 x.base)) (g.1.symm (g.1 y.base)))
      simp
lemma normalizedArray_eq {B C : V d →+ V d →+ V s} (h : ∀ x, B x x = C x x) :
    lowerArray B + upperArray B = lowerArray C + upperArray C := by
  funext l
  rcases l with ⟨i,j⟩ | i
  · let k : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩
    have hk : k < i := j.isLt
    change B (bit i) (bit k) + (if i = k then 0 else B (bit k) (bit i)) =
      C (bit i) (bit k) + (if i = k then 0 else C (bit k) (bit i))
    simp only [if_neg (ne_of_gt hk)]
    have H := h (bit i + bit k)
    simp only [map_add,AddMonoidHom.add_apply] at H
    rw [h (bit i),h (bit k)] at H
    apply add_left_cancel (a := C (bit i) (bit i) + C (bit k) (bit k))
    convert H using 1 <;> abel
  · change B (bit i) (bit i) + (if i=i then 0 else _) =
      C (bit i) (bit i) + (if i=i then 0 else _)
    simpa using h (bit i)
noncomputable def diagonalIso {B C : V d →+ V d →+ V s} (h : ∀ x, B x x = C x x) :
    BilinearExtension B ≃* BilinearExtension C := by
  have he := normalizedArray_eq h
  let e := allBilinear_normal B
  rw [he] at e
  exact e.trans (allBilinear_normal C).symm
lemma classOf_eq_of_orbit {a b : P d s}
    (h : (Quotient.mk'' (diagonalQ (form a)) : OrbitUp.Classes d s) =
      Quotient.mk'' (diagonalQ (form b))) : classOf a = classOf b := by
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  have hdiag (x : V d) : pushB g (form b) x x = form a x x :=
    congrArg (fun q : OrbitUp.Q d s => q x) hg
  let e := (pushIso g (form b)).trans (diagonalIso hdiag)
  symm
  apply Quotient.sound
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X := (bundle b).toGrp) (Y := (bundle a).toGrp) e)⟩
theorem classes_le_quadraticOrbits (d s : ℕ) :
    (classes d s).ncard ≤ Nat.card (OrbitUp.Classes d s) := by
  classical
  let rep (c : classes d s) : P d s := c.property.choose
  have hr (c : classes d s) : classOf (rep c) = c.val := c.property.choose_spec.2
  let f (c : classes d s) : OrbitUp.Classes d s := Quotient.mk'' (diagonalQ (form (rep c)))
  have hf : Function.Injective f := by
    intro c e he
    apply Subtype.ext
    rw [←hr c,←hr e]
    exact classOf_eq_of_orbit he
  exact Nat.card_le_card_of_injective f hf
theorem frattini_le_quadraticOrbits (d s : ℕ) :
    (frattiniClasses d s).ncard ≤ Nat.card (OrbitUp.Classes d s) := by
  have h := (((frattiniClasses_subset d s).trans (squareCoreClasses_subset d s)).trans
    (intrinsicClasses_subset d s)).trans (bilinearClasses_subset d s)
  exact (Set.ncard_le_ncard h (classes_finite d s)).trans (classes_le_quadraticOrbits d s)
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
def frattiniOrderClasses (m : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m ∧
    frattini G ≤ Subgroup.center G ∧ ∀ x : frattini G, x*x=1}
theorem frattiniClasses_finite (d s : ℕ) : (frattiniClasses d s).Finite :=
  (classes_finite d s).subset ((((frattiniClasses_subset d s).trans (squareCoreClasses_subset d s)).trans
    (intrinsicClasses_subset d s)).trans (bilinearClasses_subset d s))
theorem frattiniOrderClasses_le_sum (m : ℕ) :
    (frattiniOrderClasses m).ncard ≤ ∑ d ∈ Finset.range (m+1), (frattiniClasses d (m-d)).ncard := by
  let F := fun d => frattiniClasses d (m-d)
  let U := ⋃ d ∈ Finset.range (m+1), F d
  have hs : frattiniOrderClasses m ⊆ U := by
    rintro _ ⟨G, ⟨hcard, hc, he⟩, rfl⟩
    have hi := (frattini G).index_mul_card
    rw [hcard] at hi
    obtain ⟨d,hd,hd'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show (frattini G).index ∣ 2^m from ⟨_,hi.symm⟩)
    obtain ⟨s,_,hs'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (frattini G) ∣ 2^m from (dvd_mul_left _ _).trans (dvd_of_eq hi))
    rw [hd',hs',←pow_add] at hi
    have hds : d+s=m := Nat.pow_right_injective (by decide : 1<2) hi
    have hsd : m-d=s := by omega
    apply Set.mem_iUnion_of_mem d
    apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr (by omega : d < m + 1))
    change Quotient.mk _ G ∈ frattiniClasses d (m-d)
    exact ⟨G, ⟨hc, he, hsd ▸ hs', hd'⟩,rfl⟩
  have hfin : U.Finite := (Finset.range (m+1)).finite_toSet.biUnion (fun i _ => frattiniClasses_finite i _)
  exact (Set.ncard_le_ncard hs hfin).trans ((Finset.range (m+1)).set_ncard_biUnion_le F)
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
end Erdos1160Growth.LowerTriangularUpper
end
namespace OrbitUp
theorem sum_four_over_ranks (m A : ℕ) (hm : 10000000 ≤ m) (f : ℕ → ℕ)
    (hA : A ≤ ∑ k ∈ Finset.range (m+1), f k)
    (h : ∀ k ≤ m, (f k)^27 * 2^(10*m^2) ≤ 2^(2*m^3)) :
    (4*A)^27 * 2^(9*m^2) ≤ 2^(2*m^3) := by
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image (Finset.range (m+1)) f (by simp)
  have hs : A ≤ (m+1)*f k := hA.trans (calc
    _ ≤ ∑ _i ∈ Finset.range (m+1), f k := Finset.sum_le_sum hmax
    _ = _ := by simp)
  have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hfactor : 4*A ≤ 2^(m+2)*f k := calc
    _ ≤ 4*((m+1)*f k) := Nat.mul_le_mul_left _ hs
    _ = (4*(m+1))*f k := (Nat.mul_assoc _ _ _).symm
    _ ≤ (4*2^m)*f k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (show m < 2^m from Nat.lt_two_pow_self))
    _ = _ := by rw [pow_add]; ring
  have he : (m+2)*27+9*m^2 ≤ 10*m^2 := by
    have hbig := Nat.mul_le_mul_left m hm
    nlinarith only [hbig,hm]
  calc
    _ ≤ (2^(m+2)*f k)^27 * 2^(9*m^2) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hfactor 27)
    _ = (f k)^27 * 2^((m+2)*27+9*m^2) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_add, Nat.mul_comm (2^((m+2)*27)),Nat.mul_assoc]
    _ ≤ (f k)^27 * 2^(10*m^2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) he)
    _ ≤ _ := h k hk'
end OrbitUp
namespace Erdos1160Growth.LowerTriangularUpper
theorem finite_frattiniOrderClasses (m : ℕ) : (frattiniOrderClasses m).Finite := by
  let F := fun d => frattiniClasses d (m-d)
  let U := ⋃ d ∈ Finset.range (m+1), F d
  have hs : frattiniOrderClasses m ⊆ U := by
    rintro _ ⟨G, ⟨hcard, hc, he⟩, rfl⟩
    have hi := (frattini G).index_mul_card
    rw [hcard] at hi
    obtain ⟨d,hd,hd'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show (frattini G).index ∣ 2^m from ⟨_,hi.symm⟩)
    obtain ⟨s,_,hs'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (frattini G) ∣ 2^m from (dvd_mul_left _ _).trans (dvd_of_eq hi))
    rw [hd',hs',←pow_add] at hi
    have hds : d+s=m := Nat.pow_right_injective (by decide : 1<2) hi
    have hsd : m-d=s := by omega
    apply Set.mem_iUnion_of_mem d
    apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr (by omega : d < m + 1))
    change Quotient.mk _ G ∈ frattiniClasses d (m-d)
    exact ⟨G, ⟨hc, he, hsd ▸ hs', hd'⟩,rfl⟩
  have hfin : U.Finite := (Finset.range (m+1)).finite_toSet.biUnion (fun i _ => frattiniClasses_finite i _)
  exact hfin.subset hs
theorem root_population_upper (m : ℕ) (hm : 10000000 ≤ m) :
    (4*(frattiniOrderClasses m).ncard)^27 * 2^(9*m^2) ≤ 2^(2*m^3) := by
  apply OrbitUp.sum_four_over_ranks m _ hm _ (frattiniOrderClasses_le_sum m)
  intro d hd
  have he : d+(m-d)=m := by omega
  have h := OrbitUp.all_quadratic_orbits_upper d (m-d) (by omega)
  rw [he] at h
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (frattini_le_quadraticOrbits d (m-d)) 27)).trans h
end Erdos1160Growth.LowerTriangularUpper
open Erdos1160Growth.LowerTriangularUpper CategoryTheory
open scoped commutatorElement
end PartUH1
section PartUH2
namespace Erdos1160.CentralLifts
end Erdos1160.CentralLifts
namespace Erdos1160.SylowActions
end Erdos1160.SylowActions
section
namespace BinaryFactor
abbrev Bit := ZMod 2
lemma add_self (a : Bit) : a+a=0 := (show ∀ a : Bit,a+a=0 by decide) a
lemma bit_cases (a : Bit) : a=0 ∨ a=1 := (show ∀ a : Bit,a=0 ∨ a=1 by decide) a
variable {G : Type*} [Group G]
abbrev C₁ (G : Type*) := G → Bit
abbrev C₂ (G : Type*) := G → G → Bit
abbrev C₃ (G : Type*) := G → G → G → Bit
def d₂ (F : C₂ G) (x y z : G) : Bit := F y z + F (x*y) z + F x (y*z) + F x y
structure Cocycle (G : Type*) [Group G] where
  val : C₂ G
  norm_left : ∀ x,val 1 x=0
  norm_right : ∀ x,val x 1=0
  condition : ∀ x y z,d₂ val x y z=0
namespace Cocycle
variable (c : Cocycle G)
def prod (v w : G × Bit) : G × Bit := (v.1*w.1,v.2+w.2+c.val v.1 w.1)
lemma prod_assoc (u v w : G×Bit) : c.prod (c.prod u v) w = c.prod u (c.prod v w) := by
  apply Prod.ext (mul_assoc ..)
  change _+_+c.val (u.1*v.1) w.1 = _+_+c.val u.1 (v.1*w.1)
  have h := c.condition u.1 v.1 w.1
  dsimp [d₂] at h
  change u.2+v.2+c.val u.1 v.1+w.2+c.val (u.1*v.1) w.1 =
    u.2+(v.2+w.2+c.val v.1 w.1)+c.val u.1 (v.1*w.1)
  linear_combination h - (add_self (c.val v.1 w.1)) - (add_self (c.val u.1 (v.1*w.1)))
def base (x : G) : G×Bit := (x,0)
def zbit : G×Bit := (1,1)
def unit : G×Bit := (1,0)
def de₁ (t : C₁ (G×Bit)) (x y : G×Bit) : Bit := t x + t y + t (c.prod x y)
def de₂ (F : C₂ (G×Bit)) (x y z : G×Bit) : Bit :=
  F y z + F (c.prod x y) z + F x (c.prod y z) + F x y
def bock (x y z : G) : Bit :=
  c.val x y*c.val (x*y) z + c.val y z*c.val x (y*z)
def form (u : C₂ G) (chi : C₁ G) (eps : Bit) (x y : G×Bit) : Bit :=
  u x.1 y.1 + chi x.1*y.2 + eps*(x.2*y.2+(x.2+y.2)*c.val x.1 y.1)
theorem form_boundary (u : C₂ G) (chi : C₁ G) (eps : Bit) (x y z : G×Bit) :
    c.de₂ (c.form u chi eps) x y z =
      d₂ u x.1 y.1 z.1 + chi x.1*c.val y.1 z.1 + eps*c.bock x.1 y.1 z.1 +
      (chi x.1+chi y.1+chi (x.1*y.1))*z.2 := by
  have h := c.condition x.1 y.1 z.1
  dsimp only [d₂] at h
  dsimp only [de₂,form,prod,d₂,bock]
  linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) (eps*(x.2+y.2+z.2))*h
def normalized (F : C₂ (G×Bit)) : Prop :=
  (∀x,F unit x=0) ∧ (∀x,F x unit=0)
def relative (F : C₂ (G×Bit)) : Prop :=
  ∀ x y z, x.1=1 ∨ y.1=1 ∨ z.1=1 → c.de₂ F x y z=0
def correction (F : C₂ (G×Bit)) (x : G×Bit) : Bit := x.2*F zbit (base x.1)
def clean (F : C₂ (G×Bit)) (x y : G×Bit) : Bit := F x y + c.de₁ (correction F) x y
private lemma prod_unit_left (v : G×Bit) : c.prod unit v=v := by
  cases v; simp [prod,unit,c.norm_left]
private lemma prod_unit_right (v : G×Bit) : c.prod v unit=v := by
  cases v; simp [prod,unit,c.norm_right]
lemma clean_normal {F : C₂ (G×Bit)} (hn : normalized F) : normalized (c.clean F) := by
  constructor
  · intro x
    rw [clean,de₁,c.prod_unit_left,hn.1]
    simp [correction,unit,add_self]
  · intro x
    rw [clean,de₁,c.prod_unit_right,hn.2]
    simp [correction,unit,add_self]
lemma clean_boundary (F : C₂ (G×Bit)) (x y z : G×Bit) :
    c.de₂ (c.clean F) x y z = c.de₂ F x y z := by
  simp only [de₂,clean,de₁,c.prod_assoc]
  ring_nf <;> simp [show (2:Bit)=0 by decide]
lemma clean_normalizes {F : C₂ (G×Bit)} (hn : normalized F) (x : G) : c.clean F zbit (base x)=0 := by
  simp [clean,correction,de₁,zbit,base,prod,c.norm_left,show F (1,1) (1,0)=0 from hn.2 _,add_self]
end Cocycle
end BinaryFactor
end
section
namespace BinaryFactor.Cocycle
open BinaryFactor
variable {G : Type*} [Group G] (c : Cocycle G)
private theorem bit_base (x : G) : c.prod zbit (base x)=(x,1) := by simp [zbit,base,prod,c.norm_left]
private theorem base_bit (x : G) : c.prod (base x) zbit=(x,1) := by simp [zbit,base,prod,c.norm_right]
private theorem bit_bit : c.prod (zbit (G:=G)) zbit=unit := by simp [zbit,unit,prod,c.norm_left,add_self]
private theorem base_pair (x y : G) (j : Bit) : c.prod (base x) (y,j)=(x*y,j+c.val x y) := by simp [base,prod]
private theorem bit_eq_of_add {x y : Bit} (h : x+y=0) : x=y := by
  linear_combination h-(add_self y)
theorem relative_normal_form (F : C₂ (G×Bit)) (hn : normalized F) (hr : c.relative F)
    (hg : ∀x,F zbit (base x)=0) :
    ∃ (u : C₂ G) (chi : C₁ G) (eps : Bit), F=c.form u chi eps ∧ (∀x,u 1 x=0) ∧ (∀x,u x 1=0) ∧ (∀x y,chi (x*y)=chi x+chi y) := by
  let eps := F zbit zbit
  let chi (x : G) := F (base x) zbit
  let u (x y : G) := F (base x) (base y)
  have hze (x : G) (i : Bit) : F zbit (x,i) = eps*i := by
    rcases bit_cases i with rfl|rfl
    · simpa only [mul_zero,base] using hg x
    · rw [mul_one]
      have h := hr zbit zbit (base x) (Or.inl rfl)
      simp only [de₂,c.bit_bit,c.bit_base,hn.1,hg,zero_add,add_zero] at h
      exact bit_eq_of_add h
  have hshift (x y : G) (j : Bit) :
      F (x,1) (y,j) = F (base x) (y,j) + eps*(j+c.val x y) := by
    have h := hr zbit (base x) (y,j) (Or.inl rfl)
    simp only [de₂,c.bit_base,c.base_pair,hg,add_zero,hze] at h
    linear_combination h-(add_self (F (base x) (y,j)))-(add_self (eps*(j+c.val x y)))
  have hrow (x y : G) : F (base x) (y,1)=u x y + chi x + eps*c.val x y := by
    have h := hr (base x) zbit (base y) (Or.inr (Or.inl rfl))
    simp only [de₂,c.base_bit,c.bit_base,hg,zero_add] at h
    have hs := hshift x y 0
    simp only [zero_add] at hs
    change F (x,1) (base y)=u x y + eps*c.val x y at hs
    rw [hs] at h
    dsimp only [chi]
    linear_combination h-(add_self (u x y))-(add_self (F (base x) zbit))-(add_self (eps*c.val x y))
  have he : F=c.form u chi eps := by
    funext x y
    obtain ⟨x,i⟩ := x
    obtain ⟨y,j⟩ := y
    rcases bit_cases i with rfl|rfl <;> rcases bit_cases j with rfl|rfl
    · simp only [form,zero_mul,mul_zero,add_zero];rfl
    · simpa [form,base,add_assoc,add_comm,add_left_comm] using hrow x y
    · simpa [form,u,base] using hshift x y 0
    · rw [hshift,hrow]
      dsimp only [form]
      ring_nf <;> simp [show (2:Bit)=0 by decide]
  refine ⟨u,chi,eps,he,fun x=>hn.1 _,fun x=>hn.2 _,?_⟩
  intro x y
  have h := hr (base x) (base y) zbit (Or.inr (Or.inr rfl))
  rw [he,c.form_boundary] at h
  have hz (x : G) : u x 1=0 := hn.2 _
  simp only [base,zbit,d₂,bock,hz,c.norm_right,mul_one,zero_mul,mul_zero,add_zero,zero_add] at h
  linear_combination h-(add_self (chi x))-(add_self (chi y))-(add_self (u x y))
end BinaryFactor.Cocycle
end
section
namespace BinaryFactor.Cocycle
open BinaryFactor
variable {G : Type*} [Group G] (c : Cocycle G)
def norm₂ (u : C₂ G) : Prop := (∀x,u 1 x=0) ∧ (∀x,u x 1=0)
def norm₃ (z : C₃ G) : Prop := (∀x y,z 1 x y=0) ∧ (∀x y,z x 1 y=0) ∧ (∀x y,z x y 1=0)
def character (a : C₁ G) : Prop := ∀ x y,a (x*y)=a x+a y
def inflBoundary (z : C₃ G) : Prop :=
  ∃ F : C₂ (G×Bit),normalized F ∧ ∀ x y w,c.de₂ F x y w=z x.1 y.1 w.1
theorem inflation_iff (z : C₃ G) (hn : norm₃ z) :
    c.inflBoundary z ↔ ∃ (u : C₂ G) (chi : C₁ G) (eps : Bit), norm₂ u ∧ character chi ∧
      ∀ x y w,z x y w=d₂ u x y w + chi x*c.val y w + eps*c.bock x y w := by
  constructor
  · rintro ⟨F,hF,hz⟩
    have hrel : c.relative F := by
      intro x y w h
      rw [hz]
      rcases h with h|h|h
      · rw [h,hn.1]
      · rw [h,hn.2.1]
      · rw [h,hn.2.2]
    have hrel' : c.relative (c.clean F) := fun x y w h => (c.clean_boundary F x y w).trans (hrel _ _ _ h)
    obtain ⟨u,chi,eps,eqn,h₁,h₂,hchi⟩ := c.relative_normal_form (c.clean F) (c.clean_normal hF) hrel' (c.clean_normalizes hF)
    refine ⟨u,chi,eps,⟨h₁,h₂⟩,hchi,fun x y w=>?_⟩
    have h := (hz (base x) (base y) (base w)).symm
    rw [←c.clean_boundary F,eqn,c.form_boundary] at h
    simpa [base] using h
  · rintro ⟨u,chi,eps,hu,hchi,hz⟩
    have h1 : chi 1=0 := by simpa using hchi 1 1
    refine ⟨c.form u chi eps,⟨?_,?_⟩,?_⟩
    · intro x; simp [form,unit,hu.1,h1,c.norm_left]
    · intro x; simp [form,unit,hu.2,c.norm_right]
    · intro x y w
      rw [c.form_boundary,hz,hchi]
      simp [add_self]
end BinaryFactor.Cocycle
end
section
namespace BinaryFactor
open Cocycle
variable (G : Type*) [Group G]
def normalOne : Submodule Bit (C₁ G) where
  carrier := {u | u 1=0}
  zero_mem' := rfl
  add_mem' := by intro x y hx hy; change x 1+y 1=0; rw [show x 1=0 from hx,show y 1=0 from hy,add_zero]
  smul_mem' := by intro k x hx; change k*x 1=0; rw [show x 1=0 from hx,mul_zero]
def normalTwo : Submodule Bit (C₂ G) where
  carrier := {u | norm₂ u}
  zero_mem' := ⟨fun _=>rfl,fun _=>rfl⟩
  add_mem' := by
    rintro x y ⟨hx,hx'⟩ ⟨hy,hy'⟩
    exact ⟨fun i=>(congrArg₂ (·+·) (hx i) (hy i)).trans (zero_add _),fun i=>(congrArg₂ (·+·) (hx' i) (hy' i)).trans (zero_add _)⟩
  smul_mem' := by
    rintro k x ⟨hx,hx'⟩
    exact ⟨fun i=>(congrArg (k*·) (hx i)).trans (mul_zero _),fun i=>(congrArg (k*·) (hx' i)).trans (mul_zero _)⟩
def characters : Submodule Bit (C₁ G) where
  carrier := {u | character u}
  zero_mem' := fun _ _ => by change (0:Bit)=0+0;simp
  add_mem' := by
    intro a b ha hb x y
    change a (x*y)+b (x*y)=(a x+b x)+(a y+b y)
    rw [ha x y,hb x y];abel
  smul_mem' := by
    intro k a ha x y
    change k*a (x*y)=k*a x+k*a y
    rw [ha x y,mul_add]
def d₁Linear : (normalOne G) →ₗ[Bit] (normalTwo G) where
  toFun g := ⟨fun x y => g.val y+g.val (x*y)+g.val x,by
    have hz : g.val 1=0 := g.property
    exact ⟨fun y=>by simp [one_mul,hz,add_self],fun x=>by simp [mul_one,hz,add_self]⟩⟩
  map_add' u v := by apply Subtype.ext;funext x y;change (u.val y+v.val y)+(u.val (x*y)+v.val (x*y))+(u.val x+v.val x)=_;dsimp;abel
  map_smul' k u := by apply Subtype.ext;funext x y;change k*_+k*_+k*_=k*(_+_+_);ring
def d₂Linear : (normalTwo G) →ₗ[Bit] C₃ G where
  toFun := fun u => d₂ u.val
  map_add' u v := by funext x y z;dsimp [d₂];abel
  map_smul' k u := by funext x y z;dsimp [d₂];simp [mul_add]
abbrev boundaries₃ := LinearMap.range (d₂Linear G)
abbrev cycles₂ := LinearMap.ker (d₂Linear G)
variable {G} (c : Cocycle G)
def rawObstruction : (characters G × Bit) →ₗ[Bit] C₃ G where
  toFun := fun a x y w => a.1.val x*c.val y w+a.2*c.bock x y w
  map_add' a b := by funext x y w;dsimp;ring
  map_smul' k a := by funext x y w;dsimp;ring
def obstructionLinear : (characters G × Bit) →ₗ[Bit] ((C₃ G) ⧸ boundaries₃ G) :=
  (boundaries₃ G).mkQ.comp (rawObstruction c)
theorem inflation_range {z : C₃ G} (hn : norm₃ z) :
    c.inflBoundary z ↔ (boundaries₃ G).mkQ z ∈ LinearMap.range (obstructionLinear c) := by
  rw [c.inflation_iff z hn]
  constructor
  · rintro ⟨u,a,e,hu,ha,h⟩
    refine ⟨(⟨a,ha⟩,e),?_⟩
    change Submodule.Quotient.mk (p := boundaries₃ G) (fun x y w=>a x*c.val y w+e*c.bock x y w)=Submodule.Quotient.mk z
    apply (Submodule.Quotient.eq (boundaries₃ G)).mpr
    refine ⟨⟨u,hu⟩,?_⟩
    funext x y w
    change d₂ u x y w = (a x*c.val y w+e*c.bock x y w)-z x y w
    rw [h]
    linear_combination add_self (d₂ u x y w)
  · rintro ⟨⟨a,e⟩,he⟩
    change Submodule.Quotient.mk (p := boundaries₃ G) (fun x y w=>a.val x*c.val y w+e*c.bock x y w)=Submodule.Quotient.mk z at he
    obtain ⟨u,hu⟩ := (Submodule.Quotient.eq (boundaries₃ G)).mp he
    refine ⟨u.val,a.val,e,u.property,a.property,fun x y w=>?_⟩
    have hh := congrFun (congrFun (congrFun hu x) y) w
    change d₂ u.val x y w=(a.val x*c.val y w+e*c.bock x y w)-z x y w at hh
    linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) hh
theorem inflation_rank_kernel [Finite G] :
    Module.finrank Bit (LinearMap.range (obstructionLinear c)) +
      Module.finrank Bit (LinearMap.ker (obstructionLinear c)) =
      Module.finrank Bit (characters G)+1 := by
  have H := LinearMap.finrank_range_add_finrank_ker (obstructionLinear c)
  rw [Module.finrank_prod,Module.finrank_self] at H
  exact H
end BinaryFactor
end
section
namespace BinaryFactor.Cocycle
open BinaryFactor
variable {G : Type*} [Group G] (c : Cocycle G)
def Twist (_ : Cocycle G) := G × Bit
instance : Group c.Twist where
  one := unit
  mul := c.prod
  mul_assoc := c.prod_assoc
  one_mul x := by
    obtain ⟨x,j⟩ := x
    change c.prod unit (x,j)=(x,j)
    simp [prod,unit,c.norm_left]
  mul_one x := by
    obtain ⟨x,j⟩ := x
    change c.prod (x,j) unit=(x,j)
    simp [prod,unit,c.norm_right]
  inv x := (x.1⁻¹,x.2+c.val x.1⁻¹ x.1)
  inv_mul_cancel x := by
    obtain ⟨x,j⟩ := x
    change (x⁻¹*x,j+c.val x⁻¹ x+j+c.val x⁻¹ x)=unit
    rw [inv_mul_cancel]
    apply congrArg (fun b:Bit => ((1:G),b))
    change j+c.val x⁻¹ x+j+c.val x⁻¹ x=0
    ring_nf
    simp [show (2:Bit)=0 by decide]
instance [Finite G] : Finite c.Twist := inferInstanceAs (Finite (G×Bit))
def projTwist : c.Twist →* G where
  toFun := Prod.fst
  map_one' := rfl
  map_mul' _ _ := rfl
theorem projTwist_onto : Function.Surjective c.projTwist := fun x => ⟨base x,rfl⟩
theorem projTwist_central : c.projTwist.ker ≤ Subgroup.center c.Twist := by
  rintro ⟨x,j⟩ (hx : x=1)
  subst x
  apply Subgroup.mem_center_iff.mpr
  rintro ⟨y,k⟩
  change c.prod (y,k) (1,j) = c.prod (1,j) (y,k)
  simp [prod,c.norm_left,c.norm_right,add_comm]
theorem card_twist [Finite G] : Nat.card c.Twist=2*Nat.card G := by
  change Nat.card (G×Bit)=_
  rw [Nat.card_prod,Nat.card_zmod,Nat.mul_comm]
end BinaryFactor.Cocycle
end
section
namespace BinaryFactor.Cocycle
open BinaryFactor
variable {G : Type*} [Group G] (c : Cocycle G)
def readCharacter (F : C₂ (G×Bit)) (x : G) : Bit := F (base x) zbit+F zbit (base x)
def readSquare (F : C₂ (G×Bit)) : Bit := F zbit zbit
def readBase (F : C₂ (G×Bit)) (x y : G) : Bit := c.clean F (base x) (base y)
lemma read_spec {F : C₂ (G×Bit)} (hn : normalized F) (hr : c.relative F) :
    character (readCharacter F) ∧ norm₂ (c.readBase F) ∧
      c.clean F=c.form (c.readBase F) (readCharacter F) (readSquare F) := by
  have hrel : c.relative (c.clean F) := fun x y z h=> (c.clean_boundary F x y z).trans (hr _ _ _ h)
  obtain ⟨u,chi,ep,he,h₁,h₂,hchi⟩ := c.relative_normal_form (c.clean F)
    (c.clean_normal hn) hrel (c.clean_normalizes hn)
  have hc1 : chi 1=0 := by simpa using hchi 1 1
  have eu : c.readBase F=u := by
    funext x y
    change c.clean F (base x) (base y)=u x y
    rw [he]
    simp [form,base]
  have em : readCharacter F=chi := by
    funext x
    have h := congrFun (congrFun he (base x)) zbit
    have h0 : F ((1,1) : G×Bit) (1,0)=0 := hn.2 _
    simpa [clean,correction,de₁,zbit,base,prod,form,readCharacter,h0,c.norm_right,h₂] using h
  have es : readSquare F=ep := by
    have h := congrFun (congrFun he zbit) zbit
    have h0 : F ((1,1) : G×Bit) (1,0)=0 := hn.2 _
    simpa [clean,correction,de₁,zbit,base,prod,form,readSquare,h0,c.norm_left,h₁,hc1,add_self] using h
  rw [eu,em,es]
  exact ⟨hchi,⟨h₁,h₂⟩,he⟩
theorem twist_relative (v : cycles₂ c.Twist) : c.relative v.val.val := by
  intro x y z _
  exact congrFun (congrFun (congrFun v.property x) y) z
theorem twist_normalized (v : cycles₂ c.Twist) : normalized v.val.val := v.val.property
def readLinear : (cycles₂ c.Twist) →ₗ[Bit] (characters G × Bit) where
  toFun v := (⟨readCharacter v.val.val,(c.read_spec (c.twist_normalized v) (c.twist_relative v)).1⟩,readSquare v.val.val)
  map_add' v w := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      change (v.val.val (base x) zbit+w.val.val (base x) zbit)+(v.val.val zbit (base x)+w.val.val zbit (base x)) = _
      dsimp [readCharacter];abel
    · rfl
  map_smul' k v := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      change k*v.val.val (base x) zbit+k*v.val.val zbit (base x)=k*(v.val.val (base x) zbit+v.val.val zbit (base x))
      ring
    · rfl
theorem read_range : LinearMap.range (c.readLinear)=LinearMap.ker (obstructionLinear c) := by
  ext p
  constructor
  · rintro ⟨v,rfl⟩
    obtain ⟨hchi,hu,he⟩ := c.read_spec (c.twist_normalized v) (c.twist_relative v)
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨⟨c.readBase v.val.val,hu⟩,?_⟩
    funext x y z
    have h : c.de₂ v.val.val (base x) (base y) (base z)=0 :=
      congrFun (congrFun (congrFun v.property (base x)) (base y)) (base z)
    rw [←c.clean_boundary v.val.val,he,c.form_boundary] at h
    simp only [base,mul_zero,add_zero] at h
    change d₂ _ x y z=readCharacter v.val.val x*c.val y z+readSquare v.val.val*c.bock x y z
    linear_combination h-(add_self (readCharacter v.val.val x*c.val y z))-(add_self (readSquare v.val.val*c.bock x y z))
  · intro hp
    have hz := (Submodule.Quotient.mk_eq_zero (boundaries₃ G)).mp (show (Submodule.Quotient.mk (p:=boundaries₃ G) (rawObstruction c p))=0 from hp)
    obtain ⟨u,hu⟩ := hz
    have hc1 : p.1.val 1=0 := by simpa using p.1.property 1 1
    have hn : normalized (c.form u.val p.1.val p.2) := by
      exact ⟨fun x=>by simp [form,unit,u.property.1,hc1,c.norm_left],
             fun x=>by simp [form,unit,u.property.2,c.norm_right]⟩
    let lifted : cycles₂ c.Twist := ⟨⟨c.form u.val p.1.val p.2,hn⟩,by
      funext x y z
      change G×Bit at x y z
      change c.de₂ (c.form u.val p.1.val p.2) x y z=0
      rw [c.form_boundary,p.1.property]
      have h := congrFun (congrFun (congrFun hu x.1) y.1) z.1
      change d₂ u.val x.1 y.1 z.1=p.1.val x.1*c.val y.1 z.1+p.2*c.bock x.1 y.1 z.1 at h
      rw [h]
      ring_nf <;> simp [show (2:Bit)=0 by decide]⟩
    refine ⟨lifted,?_⟩
    apply Prod.ext
    · apply Subtype.ext
      funext x
      change readCharacter (c.form u.val p.1.val p.2) x=p.1.val x
      simp [readCharacter,form,base,zbit,u.property.1,u.property.2,c.norm_left,c.norm_right,hc1]
    · change readSquare (c.form u.val p.1.val p.2)=p.2
      simp [readSquare,form,zbit,u.property.1,c.norm_left,hc1,add_self]
end BinaryFactor.Cocycle
end
section
namespace BinaryFactor.Cocycle
open BinaryFactor
variable {G : Type*} [Group G] (c : Cocycle G)
def gaugeParam (g : normalOne G) (x : G×Bit) := x.2*g.val x.1
def assemble (u : cycles₂ G) (g : normalOne G) (x y : G×Bit) : Bit :=
  u.val.val x.1 y.1+c.de₁ (gaugeParam g) x y
lemma assemble_norm (u : cycles₂ G) (g : normalOne G) : normalized (c.assemble u g) := by
  have h0 : g.val 1=0 := g.property
  exact ⟨fun x=>by simp [assemble,de₁,unit,prod,gaugeParam,c.norm_left,u.val.property.1,h0,add_self],
    fun x=>by simp [assemble,de₁,unit,prod,gaugeParam,c.norm_right,u.val.property.2,h0,add_self]⟩
lemma assemble_closed (u : cycles₂ G) (g : normalOne G) :
    ∀ x y z,c.de₂ (c.assemble u g) x y z=0 := by
  intro x y z
  have h := congrFun (congrFun (congrFun u.property x.1) y.1) z.1
  change d₂ u.val.val x.1 y.1 z.1=0 at h
  simp only [de₂,assemble,de₁,c.prod_assoc]
  dsimp only [prod] at *
  dsimp only [d₂] at h
  linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) h
def assembleLinear : (cycles₂ G × normalOne G) →ₗ[Bit] cycles₂ c.Twist where
  toFun a := ⟨⟨c.assemble a.1 a.2,c.assemble_norm ..⟩,by
    funext x y z;exact c.assemble_closed a.1 a.2 x y z⟩
  map_add' a b := by
    apply Subtype.ext;apply Subtype.ext
    funext x y
    change c.assemble (a.1+b.1) (a.2+b.2) x y=c.assemble a.1 a.2 x y+c.assemble b.1 b.2 x y
    dsimp [assemble,de₁,gaugeParam];ring
  map_smul' k a := by
    apply Subtype.ext;apply Subtype.ext
    funext x y
    change c.assemble (k•a.1) (k•a.2) x y=k*c.assemble a.1 a.2 x y
    dsimp [assemble,de₁,gaugeParam];ring
lemma assemble_bit_base (u : cycles₂ G) (g : normalOne G) (x : G) :
    c.assemble u g zbit (base x)=g.val x := by
  simp [assemble,de₁,zbit,base,prod,gaugeParam,u.val.property.1,show g.val 1=0 from g.property,c.norm_left]
lemma assemble_base_bit (u : cycles₂ G) (g : normalOne G) (x : G) :
    c.assemble u g (base x) zbit=g.val x := by
  simp [assemble,de₁,zbit,base,prod,gaugeParam,u.val.property.2,show g.val 1=0 from g.property,c.norm_right]
lemma assemble_base_base (u : cycles₂ G) (g : normalOne G) (x y : G) :
    c.assemble u g (base x) (base y)=u.val.val x y+c.val x y*g.val (x*y) := by
  simp [assemble,de₁,base,prod,gaugeParam]
theorem assemble_injective : Function.Injective (c.assembleLinear) := by
  rintro ⟨u,g⟩ ⟨v,h⟩ he
  have hx (x y : G×Bit) : c.assemble u g x y=c.assemble v h x y :=
    congrArg (fun a : cycles₂ c.Twist => a.val.val x y) he
  have hh : g=h := by
    apply Subtype.ext
    funext x
    exact (c.assemble_bit_base u g x).symm.trans ((hx zbit (base x)).trans (c.assemble_bit_base v h x))
  subst h
  apply congrArg (fun a : cycles₂ G=>(a,g))
  apply Subtype.ext;apply Subtype.ext
  funext x y
  have e := hx (base x) (base y)
  rwa [c.assemble_base_base,c.assemble_base_base,add_left_inj] at e
theorem assemble_range : LinearMap.range (c.assembleLinear)=LinearMap.ker (c.readLinear) := by
  ext v
  constructor
  · rintro ⟨⟨u,g⟩,rfl⟩
    apply Prod.ext
    · apply Subtype.ext;funext x
      change c.assemble u g (base x) zbit+c.assemble u g zbit (base x)=0
      rw [c.assemble_base_bit,c.assemble_bit_base,add_self]
    · change c.assemble u g zbit zbit=0
      simp [assemble,de₁,zbit,prod,gaugeParam,c.norm_left,show g.val 1=0 from g.property,u.val.property.1]
  · intro h
    have hx : readCharacter v.val.val=0 := congrArg (fun a : characters G × Bit=>a.1.val) h
    have hz : readSquare v.val.val=0 := congrArg Prod.snd (show c.readLinear v=0 from h)
    obtain ⟨_,hu,he⟩ := c.read_spec (c.twist_normalized v) (c.twist_relative v)
    rw [hx,hz] at he
    have heb (x y : G×Bit) : c.clean v.val.val x y=c.readBase v.val.val x.1 y.1 := by
      simpa [form] using congrFun (congrFun he x) y
    let g : normalOne G := ⟨fun x=>v.val.val zbit (base x),v.val.property.2 _⟩
    let u : cycles₂ G := ⟨⟨c.readBase v.val.val,hu⟩,by
      funext x y z
      have h := (c.clean_boundary v.val.val (base x) (base y) (base z)).trans (congrFun (congrFun (congrFun v.property (base x)) (base y)) (base z))
      change c.de₂ (c.clean v.val.val) (base x) (base y) (base z)=0 at h
      change d₂ (c.readBase v.val.val) x y z=0
      simpa only [de₂,heb,base,prod,d₂] using h⟩
    refine ⟨(u,g),?_⟩
    apply Subtype.ext;apply Subtype.ext;funext x y
    change c.readBase v.val.val x.1 y.1 + c.de₁ (correction v.val.val) x y = v.val.val x y
    have hh := heb x y
    dsimp only [clean] at hh
    linear_combination (add_self (c.de₁ (correction v.val.val) x y))-hh
theorem cycles_twist_finrank [Finite G] :
    Module.finrank Bit (cycles₂ c.Twist) = Module.finrank Bit (cycles₂ G) +
      Module.finrank Bit (normalOne G) + Module.finrank Bit (LinearMap.ker (obstructionLinear c)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (c.readLinear)
  rw [c.read_range,←c.assemble_range,LinearMap.finrank_range_of_inj c.assemble_injective,Module.finrank_prod] at h
  omega
end BinaryFactor.Cocycle
end
section
namespace BinaryFactor
open Cocycle
variable (G : Type*) [Group G]
def boundaryLinear : normalOne G →ₗ[Bit] cycles₂ G :=
  (d₁Linear G).codRestrict _ (fun g=>by
    funext x y z
    change (g.val z+g.val (y*z)+g.val y)+(g.val z+g.val ((x*y)*z)+g.val (x*y))+
      (g.val (y*z)+g.val (x*(y*z))+g.val x)+(g.val y+g.val (x*y)+g.val x)=0
    rw [mul_assoc]
    ring_nf <;> simp [show (2:Bit)=0 by decide])
abbrev H₂ := (cycles₂ G) ⧸ LinearMap.range (boundaryLinear G)
noncomputable abbrev r₂ := Module.finrank Bit (H₂ G)
noncomputable abbrev r₁ := Module.finrank Bit (characters G)
def characterKerEquiv : (LinearMap.ker (boundaryLinear G)) ≃ₗ[Bit] (characters G) where
  toFun g := ⟨g.val.val,fun x y=>by
    have h := congrArg (fun a : cycles₂ G=>a.val.val x y) g.property
    change g.val.val y+g.val.val (x*y)+g.val.val x=0 at h
    linear_combination h-(add_self (g.val.val y))-(add_self (g.val.val x))⟩
  invFun a := ⟨⟨a.val,by change a.val 1=0; simpa using a.property 1 1⟩,by
    apply Subtype.ext;apply Subtype.ext;funext x y
    change a.val y+a.val (x*y)+a.val x=0
    rw [a.property];ring_nf <;> simp [show (2:Bit)=0 by decide]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem betti_formula [Finite G] :
    r₂ G + Module.finrank Bit (normalOne G) = Module.finrank Bit (cycles₂ G)+r₁ G := by
  have hr := (LinearMap.range (boundaryLinear G)).finrank_quotient_add_finrank
  have hb := LinearMap.finrank_range_add_finrank_ker (boundaryLinear G)
  rw [(characterKerEquiv G).finrank_eq] at hb
  change Module.finrank Bit (H₂ G) + Module.finrank Bit (LinearMap.range (boundaryLinear G)) = Module.finrank Bit (cycles₂ G) at hr
  change Module.finrank Bit (H₂ G)+_=_+Module.finrank Bit (characters G)
  omega
theorem normalOne_finrank [Finite G] : Module.finrank Bit (normalOne G)+1=Nat.card G := by
  classical
  let _ := Fintype.ofFinite G
  let f : (G→Bit) →ₗ[Bit] Bit := LinearMap.proj (1:G)
  have hf : Function.Surjective f := fun x=>⟨fun _=>x,rfl⟩
  have hk : f.ker=normalOne G := rfl
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hk,LinearMap.range_eq_top.mpr hf,finrank_top,Module.finrank_self,Module.finrank_fintype_fun_eq_card] at h
  rw [Nat.card_eq_fintype_card]
  exact (Nat.add_comm ..).trans h
variable {G} (c : Cocycle G)
def pullCharacters : characters G →ₗ[Bit] characters c.Twist where
  toFun a := ⟨fun x=>a.val x.1,fun x y=>a.property x.1 y.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma pullCharacters_inj : Function.Injective (pullCharacters c) := by
  intro a b h;apply Subtype.ext;funext x
  exact congrArg (fun f : characters c.Twist=>f.val (base x)) h
def invisible : Prop := ∀a : characters c.Twist,a.val zbit=0
lemma pullCharacters_surj (hi : invisible c) : Function.Surjective (pullCharacters c) := by
  intro a
  have ha (x : G) (j : Bit) : a.val ((x,j) : G×Bit)=a.val (base x) := by
    rcases bit_cases j with rfl|rfl
    · rfl
    · have h := a.property (zbit : c.Twist) (base x)
      have hp : c.prod zbit (base x)=(x,1) := by simp [prod,zbit,base,c.norm_left]
      change a.val (c.prod zbit (base x))=_ at h
      rwa [hp,hi,zero_add] at h
  have hab (x y : G) : a.val (base (x*y))=a.val (base x)+a.val (base y) := by
    have h := a.property (base x) (base y)
    change a.val (c.prod (base x) (base y))=_ at h
    simpa only [base,prod,zero_add,ha] using h
  refine ⟨⟨fun x=>a.val (base x),hab⟩,?_⟩
  apply Subtype.ext;funext x
  exact (ha x.1 x.2).symm
theorem r₁_twist (hi : invisible c) : r₁ c.Twist=r₁ G :=
  (LinearEquiv.ofBijective (pullCharacters c) ⟨pullCharacters_inj c,pullCharacters_surj c hi⟩).finrank_eq.symm
end BinaryFactor
end
section
namespace Erdos1160Growth
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
namespace BilinearExtension
variable {B : V →+ V →+ W}
open scoped commutatorElement
variable {V' W' : Type*} [AddCommGroup V'] [AddCommGroup W'] {C : V' →+ V' →+ W'}
end BilinearExtension
end Erdos1160Growth
end
section
namespace Erdos1160Growth.SharpFamily
end Erdos1160Growth.SharpFamily
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
variable {d s : ℕ}
abbrev Change (s : ℕ) := V s ≃ₗ[ZMod 2] V s
def change (u : Change s) (a : P d s) : P d s := fun l => u (a l)
lemma form_change (u : Change s) (a : P d s) (x y : V d) :
    form (change u a) x y = u (form a x y) := by
  change (∑ l, (x (row l) * y (col l)) • u (a l)) =
    u (∑ l, (x (row l) * y (col l)) • a l)
  simp
def changeIso (u : Change s) (a : P d s) : G a ≃* G (change u a) where
  toFun x := ⟨x.base, u x.fiber⟩
  invFun x := ⟨x.base, u.symm x.fiber⟩
  left_inv x := by apply BilinearExtension.ext; · rfl
                   exact u.symm_apply_apply _
  right_inv x := by apply BilinearExtension.ext; · rfl
                    exact u.apply_symm_apply _
  map_mul' x y := by
    apply BilinearExtension.ext
    · rfl
    · change u (x.fiber + y.fiber + form a x.base y.base) =
        u x.fiber + u y.fiber + form (change u a) x.base y.base
      rw [form_change,map_add,map_add]
theorem classOf_change (u : Change s) (a : P d s) :
    classOf (change u a) = classOf a := by
  symm
  apply Quotient.sound
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X := (bundle a).toGrp) (Y := (bundle (change u a)).toGrp)
      (changeIso u a))⟩
theorem classes_card_fiber (d s : ℕ) :
    (classes d s).ncard * Nat.card (Change s) ≤
      2 ^ (s * (d*(d-1)/2+d)) := by
  classical
  let C := ↥(classes d s)
  have witness (c : C) : ∃ a : P d s, Full a ∧ classOf a = c.val := c.property
  let rep (c : C) := Classical.choose (witness c)
  have repFull (c : C) : Full (rep c) := (Classical.choose_spec (witness c)).1
  have repClass (c : C) : classOf (rep c) = c.val := (Classical.choose_spec (witness c)).2
  let encode (cu : C × Change s) := change cu.2 (rep cu.1)
  have encInj : Function.Injective encode := by
    rintro ⟨c,u⟩ ⟨e,v⟩ heq
    change change u (rep c) = change v (rep e) at heq
    have hclass := congrArg classOf heq
    rw [classOf_change,classOf_change,repClass,repClass] at hclass
    obtain rfl : c = e := Subtype.ext hclass
    have hu : u.toLinearMap = v.toLinearMap :=
      LinearMap.ext_on_range (repFull c) (congrFun heq)
    exact Prod.ext rfl (LinearEquiv.toLinearMap_injective hu)
  calc
    _ = Nat.card (C × Change s) := by rw [Nat.card_prod]; rfl
    _ ≤ Nat.card (P d s) := Nat.card_le_card_of_injective encode encInj
    _ = _ := by
      simp only [P, V, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul, Slot,
        Nat.card_sum, SharpFamily.triangular_card]
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
lemma card_change (s : ℕ) :
    Nat.card (Change s) = ∏ i : Fin s, (2^s-2^i.val) := by
  let e : Matrix.GeneralLinearGroup (Fin s) (ZMod 2) ≃* Change s :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (V s))
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp
theorem triangular_class_upper (d s : ℕ) :
    (classes d s).ncard * (∏ i : Fin s, (2^s-2^i.val)) ≤
      2^(s * (d*(d-1)/2+d)) := by
  rw [← card_change]
  exact classes_card_fiber d s
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
variable {d s : ℕ}
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
variable {d s : ℕ}
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
variable {d s : ℕ}
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
namespace CentralData
variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)
end CentralData
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper.CentralData
open CategoryTheory
variable {E : Type*} [Group E] {d s : ℕ}
variable (S : CentralData E d s) (σ : V d → E) (B : V d →+ V d →+ V s)
variable (hπ : ∀ x, S.base (σ x) = x)
variable (hmul : ∀ x y, σ x * σ y = S.liftK (B x y) * σ (x+y))
end Erdos1160Growth.LowerTriangularUpper.CentralData
end
section
namespace Erdos1160Growth.LowerTriangularUpper.CentralData
open scoped commutatorElement
end Erdos1160Growth.LowerTriangularUpper.CentralData
end
section
namespace Erdos1160Growth.LowerTriangularUpper.CentralData
variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)
end Erdos1160Growth.LowerTriangularUpper.CentralData
end
section
namespace Erdos1160Growth.LowerTriangularUpper.CentralData
variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)
end Erdos1160Growth.LowerTriangularUpper.CentralData
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
namespace CentralData
variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)
variable {E : FiniteGrp.{0}}
end CentralData
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace BinaryFactor
open Cocycle
variable {G : Type*} [Group G] (c : Cocycle G)
def cupObstruction : (characters G) →ₗ[Bit] (C₃ G ⧸ boundaries₃ G) :=
  (obstructionLinear c).comp (LinearMap.inl Bit _ _)
abbrev cupAnn := LinearMap.ker (cupObstruction c)
def epsilonMap : LinearMap.ker (obstructionLinear c) →ₗ[Bit] Bit :=
  (LinearMap.snd Bit _ _).comp (LinearMap.ker (obstructionLinear c)).subtype
noncomputable def epsilon := Module.finrank Bit (LinearMap.range (epsilonMap c))
theorem epsilon_le_one : epsilon c ≤ 1 :=
  (Submodule.finrank_le (LinearMap.range (epsilonMap c))).trans_eq (Module.finrank_self ..)
def annEquiv : cupAnn c ≃ₗ[Bit] (LinearMap.ker (epsilonMap c)) where
  toFun a := ⟨⟨(a.val,0),a.property⟩,rfl⟩
  invFun p := ⟨p.val.val.1,by
    have hz : p.val.val.2=0 := p.property
    change obstructionLinear c (p.val.val.1,0)=0
    rw [←hz];exact p.val.property⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext;apply Subtype.ext
    exact Prod.ext rfl (show p.val.val.2=0 from p.property).symm
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
theorem ker_obstruction_dim [Finite G] :
    Module.finrank Bit (LinearMap.ker (obstructionLinear c)) =
      Module.finrank Bit (cupAnn c)+epsilon c := by
  have h := LinearMap.finrank_range_add_finrank_ker (epsilonMap c)
  rw [←(annEquiv c).finrank_eq] at h
  exact h.symm.trans (Nat.add_comm ..)
theorem betti_step [Finite G] (hi : invisible c) :
    r₂ c.Twist+1 = r₂ G + Module.finrank Bit (LinearMap.ker (obstructionLinear c)) := by
  have h₁ := betti_formula c.Twist
  have h₂ := betti_formula G
  have h₃ := c.cycles_twist_finrank
  have h₄ := normalOne_finrank c.Twist
  have h₅ := normalOne_finrank G
  rw [c.card_twist] at h₄
  rw [r₁_twist c hi] at h₁
  omega
theorem scalar_recurrences [Finite G] (hi : invisible c) :
    r₂ c.Twist+1=r₂ G+Module.finrank Bit (cupAnn c)+epsilon c ∧
      Module.finrank Bit (LinearMap.range (obstructionLinear c))+r₂ c.Twist=r₁ G+r₂ G := by
  have h := betti_step c hi
  have h' := inflation_rank_kernel c
  refine ⟨by rw [h,ker_obstruction_dim,Nat.add_assoc],?_⟩
  change _=Module.finrank Bit (characters G)+r₂ G
  omega
theorem invisible_of_frattini [Finite G] (h : (zbit : c.Twist) ∈ frattini c.Twist) : invisible c := by
  intro a
  let f : c.Twist →* Multiplicative Bit := {
    toFun := fun x=>Multiplicative.ofAdd (a.val x)
    map_one' := by change a.val 1=0; simpa using a.property 1 1
    map_mul' := fun x y=>a.property x y }
  have hle : Erdos1160Growth.LowerTriangularUpper.squareCore c.Twist ≤ f.ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    change a.val (x*x)=0
    rw [a.property,add_self]
  exact hle (Erdos1160Growth.LowerTriangularUpper.frattini_le_squareCore h)
end BinaryFactor
end
section
namespace BinaryFactor
open Cocycle
variable {G H J : Type*} [Group G] [Group H] [Group J]
def pull₃Raw (f : H→*G) : C₃ G →ₗ[Bit] C₃ H where
  toFun θ x y z := θ (f x) (f y) (f z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def pull₂Normal (f : H→*G) : normalTwo G →ₗ[Bit] normalTwo H where
  toFun u := ⟨fun x y=>u.val (f x) (f y),⟨fun x=>by change u.val (f 1) (f x)=0;rw [map_one]; exact u.property.1 _, fun y=>by change u.val (f y) (f 1)=0;rw [map_one];exact u.property.2 _⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def inflate₃ (f : H→*G) : (C₃ G ⧸ boundaries₃ G) →ₗ[Bit] (C₃ H ⧸ boundaries₃ H) :=
  (boundaries₃ G).mapQ (boundaries₃ H) (pull₃Raw f) (by
    rintro _ ⟨u,rfl⟩
    refine ⟨pull₂Normal f u,?_⟩
    funext x y z
    change u.val (f y) (f z) + u.val (f (x*y)) (f z)+u.val (f x) (f (y*z))+u.val (f x) (f y)=_
    simp only [map_mul];rfl)
lemma inflate₃_comp (f : H→*G) (g : J→*H) : inflate₃ (f.comp g)=(inflate₃ g).comp (inflate₃ f) := by
  apply LinearMap.ext
  intro θ
  induction θ using Submodule.Quotient.induction_on with
  | _ θ => rfl
theorem obstruction_range_eq_inflation_ker (c : Cocycle G) :
    LinearMap.range (obstructionLinear c) = LinearMap.ker (inflate₃ c.projTwist) := by
  ext v
  induction v using Submodule.Quotient.induction_on with
  | _ θ =>
    have iff₁ : Submodule.Quotient.mk (p:=boundaries₃ G) θ ∈ LinearMap.ker (inflate₃ c.projTwist) ↔ c.inflBoundary θ := by
      change Submodule.Quotient.mk (p:=boundaries₃ c.Twist) (pull₃Raw c.projTwist θ)=0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · rintro ⟨F,h⟩
        exact ⟨F.val,F.property,fun x y z => congrFun (congrFun (congrFun h x) y) z⟩
      · rintro ⟨F,hF,h⟩
        exact ⟨⟨F,hF⟩,funext (fun x=>funext (fun y=>funext (fun z=>h x y z)))⟩
    rw [iff₁]
    apply Iff.symm
    by_cases hn : norm₃ θ
    · exact inflation_range c hn
    · apply iff_of_false
      · rintro ⟨F,hF,he⟩
        have hF₁ (g:G×Bit) : F (1,0) g=0 := hF.1 _
        have hF₂ (g:G×Bit) : F g (1,0)=0 := hF.2 _
        apply hn
        refine ⟨fun x y=>?_,fun x y=>?_,fun x y=>?_⟩
        · have h := (he unit (base x) (base y)).symm
          change θ 1 x y=c.de₂ F unit (base x) (base y) at h
          simpa [de₂,prod,unit,base,c.norm_left,hF₁,add_self] using h
        · have h := (he (base x) unit (base y)).symm
          change θ x 1 y=c.de₂ F (base x) unit (base y) at h
          simpa [de₂,prod,unit,base,c.norm_left,c.norm_right,hF₁,hF₂,add_self] using h
        · have h := (he (base x) (base y) unit).symm
          change θ x y 1=c.de₂ F (base x) (base y) unit at h
          simpa [de₂,prod,unit,base,c.norm_right,hF₂,add_self] using h
      · rintro ⟨p,hp⟩
        change Submodule.Quotient.mk (p:=boundaries₃ G) (rawObstruction c p)=Submodule.Quotient.mk θ at hp
        obtain ⟨u,hu⟩ := (Submodule.Quotient.eq (boundaries₃ G)).mp hp
        have htheta (x y z : G) : θ x y z = d₂ u.val x y z+p.1.val x*c.val y z+p.2*c.bock x y z := by
          have h := congrFun (congrFun (congrFun hu x) y) z
          change d₂ u.val x y z=p.1.val x*c.val y z+p.2*c.bock x y z-θ x y z at h
          linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) h
        have h1 : p.1.val 1=0 := by simpa using p.1.property 1 1
        apply hn
        refine ⟨fun x y=>?_,fun x y=>?_,fun x y=>?_⟩ <;>
          rw [htheta] <;> simp [d₂,bock,c.norm_right,c.norm_left,h1,u.property.1,u.property.2,add_self]
theorem inflation_dimension [Finite G] (c : Cocycle G) (hi : invisible c) :
    Module.finrank Bit (LinearMap.ker (inflate₃ c.projTwist)) + r₂ c.Twist = r₁ G+r₂ G := by
  rw [←obstruction_range_eq_inflation_ker c]
  exact (scalar_recurrences c hi).2
end BinaryFactor
end
section
namespace BinaryFactor
open Cocycle
variable {A : Type*} [CommGroup A]
def antisym₃ (θ : C₃ A) (x y z : A) : Bit :=
  θ x y z+θ x z y+θ y x z+θ y z x+θ z x y+θ z y x
theorem antisym₃_boundary (u : C₂ A) (x y z : A) : antisym₃ (d₂ u) x y z=0 := by
  simp only [antisym₃,d₂,mul_comm y x,mul_comm z x,mul_comm z y]
  ring_nf <;> simp [show (2:Bit)=0 by decide]
def cupRaw {X : Type*} (chi : C₁ X) (u : C₂ X) (x y z : X) : Bit := chi x*u y z
variable {Y : Type*} [Group Y]
end BinaryFactor
end
section
namespace BinaryFactor
variable {E G : Type*} [Group E] [Group G]
theorem exists_twist_over (F : E →* G) (onto : Function.Surjective F)
    (central : F.ker ≤ Subgroup.center E) (hcard : Nat.card F.ker=2) :
    ∃ c : Cocycle G, ∃ e : E ≃* c.Twist, ∀ x, c.projTwist (e x)=F x := by
  classical
  let i : Multiplicative Bit ≃* F.ker := mulEquivOfPrimeCardEq
    (by change Nat.card (ZMod 2) = 2; simp) hcard
  let k (b : Bit) : E := i (.ofAdd b)
  have k0 : k 0=1 := congrArg Subtype.val i.map_one
  have kadd (b d : Bit) : k (b+d)=k b*k d := congrArg Subtype.val (i.map_mul (.ofAdd b) (.ofAdd d))
  have ki : Function.Injective k := fun _ _ e => congrArg Multiplicative.toAdd (i.injective (Subtype.ext e))
  have kc (x : E) (b : Bit) : x*k b=k b*x := Subgroup.mem_center_iff.mp (central (i (.ofAdd b)).property) x
  let s (x : G) : E := if x=1 then 1 else (onto x).choose
  have h1 : s 1=1 := if_pos rfl
  have hs (x : G) : F (s x)=x := by
    by_cases hx : x=1
    · subst x; rw [h1,F.map_one]
    · simpa [s,hx] using (onto x).choose_spec
  let X (x : G) (b : Bit) := k b * s x
  have xp (x : G) (b : Bit) : F (X x b)=x := by
    change F (k b * s x)=x
    rw [F.map_mul,(show F (k b)=1 from (i (.ofAdd b)).property),hs,one_mul]
  have xi (x : G) : Function.Injective (X x) := fun _ _ e => ki (mul_right_cancel e)
  have xs (u : E) : ∃ b, X (F u) b=u := by
    let n : F.ker := ⟨u*(s (F u))⁻¹,by change F (_*_)=1; rw [F.map_mul,F.map_inv,hs,mul_inv_cancel]⟩
    refine ⟨(i.symm n).toAdd,?_⟩
    change (i (i.symm n) : E)*s (F u)=u
    rw [i.apply_symm_apply]
    exact inv_mul_cancel_right u _
  have prod (x y : G) : ∃ b, X (x*y) b=s x*s y := by
    obtain ⟨b,hb⟩ := xs (s x*s y)
    rw [F.map_mul,hs,hs] at hb
    exact ⟨b,hb⟩
  let f (x y : G) := (prod x y).choose
  have spec (x y : G) : X (x*y) (f x y)=s x*s y := (prod x y).choose_spec
  have xl (x y : G) (b d : Bit) : X x b * X y d=X (x*y) (b+d+f x y) := by
    change (k b*s x)*(k d*s y)=k (b+d+f x y)*s (x*y)
    rw [kadd,kadd,mul_assoc (k b*k d) (k (f x y)),← show X (x*y) (f x y)=k (f x y)*s (x*y) from rfl,spec]
    rw [mul_assoc (k b) (s x),←mul_assoc (s x),kc,mul_assoc,mul_assoc]
  have xzero (x : G) : X x 0=s x := by change k 0*s x=_;rw [k0,one_mul]
  let c : Cocycle G := {
    val := f
    norm_left := fun x => xi x (by simpa only [one_mul,h1,xzero] using (spec 1 x))
    norm_right := fun x => xi x (by simpa only [mul_one,h1,xzero] using (spec x 1))
    condition := fun x y z => by
      have eq := mul_assoc (X x 0) (X y 0) (X z 0)
      simp only [xl,zero_add,add_zero,mul_assoc] at eq
      have hf := xi _ eq
      dsimp only [d₂]
      linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) hf
  }
  let phi : c.Twist →* E := {
    toFun := fun z => X z.1 z.2
    map_one' := (xzero 1).trans h1
    map_mul' := fun x y => (xl _ _ _ _).symm
  }
  have hphi : Function.Bijective phi := by
    constructor
    · rintro ⟨x,b⟩ ⟨y,d⟩ h
      change X x b=X y d at h
      have he := (xp x b).symm.trans ((congrArg F h).trans (xp y d))
      subst y
      exact Prod.ext rfl (xi x h)
    · intro u
      obtain ⟨b,hb⟩ := xs u
      exact ⟨((F u,b) : G×Bit),hb⟩
  let e := MulEquiv.ofBijective phi hphi
  refine ⟨c,e.symm,fun x => ?_⟩
  obtain ⟨u,rfl⟩ := e.surjective x
  rw [e.symm_apply_apply]
  exact (xp u.1 u.2).symm
end BinaryFactor
end
section
namespace BinaryFactor
open Cocycle
variable {E G H : Type*} [Group E] [Group G] [Group H]
def characterPull (f : E→*G) : characters G →ₗ[Bit] characters E where
  toFun a := ⟨fun x=>a.val (f x),fun x y=>by
    change a.val (f (x*y))=a.val (f x)+a.val (f y)
    rw [map_mul,a.property]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def cyclePull (f : E→*G) : cycles₂ G →ₗ[Bit] cycles₂ E where
  toFun u := ⟨pull₂Normal f u.val,by
    funext x y z
    have h := congrFun (congrFun (congrFun u.property (f x)) (f y)) (f z)
    change d₂ u.val.val (f x) (f y) (f z)=0 at h
    change u.val.val (f y) (f z)+u.val.val (f (x*y)) (f z)+u.val.val (f x) (f (y*z))+u.val.val (f x) (f y)=0
    simpa only [map_mul,d₂] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def characterCongr (i : E≃*G) : characters G ≃ₗ[Bit] characters E :=
  LinearEquiv.ofLinear (characterPull i.toMonoidHom) (characterPull i.symm.toMonoidHom)
    (by ext a x;change a.val (i.symm (i x))=a.val x;rw [i.symm_apply_apply])
    (by ext a x;change a.val (i (i.symm x))=a.val x;rw [i.apply_symm_apply])
def cycleCongr (i : E≃*G) : cycles₂ G ≃ₗ[Bit] cycles₂ E :=
  LinearEquiv.ofLinear (cyclePull i.toMonoidHom) (cyclePull i.symm.toMonoidHom)
    (by apply LinearMap.ext; intro a;apply Subtype.ext;apply Subtype.ext;funext x y
        change a.val.val (i.symm (i x)) (i.symm (i y))=a.val.val x y
        rw [i.symm_apply_apply,i.symm_apply_apply])
    (by apply LinearMap.ext; intro a;apply Subtype.ext;apply Subtype.ext;funext x y
        change a.val.val (i (i.symm x)) (i (i.symm y))=a.val.val x y
        rw [i.apply_symm_apply,i.apply_symm_apply])
theorem r₁_equiv (i : E≃*G) : r₁ E=r₁ G := (characterCongr i).finrank_eq.symm
theorem r₂_equiv [Finite E] [Finite G] (i : E≃*G) : r₂ E=r₂ G := by
  have h₁ := betti_formula E
  have h₂ := betti_formula G
  have h₃ := normalOne_finrank E
  have h₄ := normalOne_finrank G
  rw [Nat.card_congr i.toEquiv] at h₃
  rw [r₁_equiv i,←(cycleCongr i).finrank_eq] at h₁
  omega
theorem inflate₃_iso_inj (i : E≃*G) : Function.Injective (inflate₃ i.toMonoidHom) := by
  have inv : Function.LeftInverse (inflate₃ i.symm.toMonoidHom) (inflate₃ i.toMonoidHom) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      apply congrArg (Submodule.Quotient.mk (p:=boundaries₃ G))
      funext a b c
      change x (i (i.symm a)) (i (i.symm b)) (i (i.symm c))=x a b c
      rw [i.apply_symm_apply,i.apply_symm_apply,i.apply_symm_apply]
  exact inv.injective
theorem scalar_inflation [Finite E] [Finite G] (f : E→*G) (hf : Function.Surjective f)
    (central : f.ker ≤ Subgroup.center E) (hc : Nat.card f.ker=2) (hΦ : f.ker ≤ frattini E) :
    Module.finrank Bit (LinearMap.ker (inflate₃ f)) + r₂ E = r₁ G+r₂ G ∧ r₁ E=r₁ G := by
  obtain ⟨c,⟨i,hi⟩⟩ := exists_twist_over f hf central hc
  have heq : c.projTwist.comp i.toMonoidHom=f := MonoidHom.ext hi
  have hbit : (zbit:c.Twist) ∈ frattini c.Twist := by
    obtain ⟨u,hu⟩ := i.surjective (zbit:c.Twist)
    have hker : u ∈ f.ker := by
      rw [MonoidHom.mem_ker,←hi u,hu];rfl
    have hmem : i u∈frattini c.Twist := frattini_le_comap_frattini_of_surjective (φ:=i.toMonoidHom) i.surjective (hΦ hker)
    rwa [hu] at hmem
  have hz := invisible_of_frattini c hbit
  refine ⟨?_,(r₁_equiv i).trans (r₁_twist c hz)⟩
  rw [r₂_equiv i,←heq,inflate₃_comp,LinearMap.ker_comp,LinearMap.ker_eq_bot.mpr (inflate₃_iso_inj i),Submodule.comap_bot]
  exact inflation_dimension c hz
end BinaryFactor
end
section
namespace BinaryFactor
open Cocycle
variable {E G : Type*} [Group E] [Group G]
def inflate₂ (f : E→*G) : H₂ G →ₗ[Bit] H₂ E :=
  (LinearMap.range (boundaryLinear G)).mapQ (LinearMap.range (boundaryLinear E)) (cyclePull f) (by
    rintro _ ⟨u,rfl⟩
    refine ⟨⟨fun x=>u.val (f x),by change u.val (f 1)=0;rw [map_one];exact u.property⟩,?_⟩
    apply Subtype.ext;apply Subtype.ext
    funext x y
    change u.val (f y)+u.val (f (x*y))+u.val (f x)=u.val (f y)+u.val (f x*f y)+u.val (f x)
    rw [map_mul])
def cupCycle (a : characters G) : cycles₂ G →ₗ[Bit] C₃ G where
  toFun u := cupRaw a.val u.val.val
  map_add' u v := by funext x y z;change a.val x*(u.val.val y z+v.val.val y z)=_;rw [mul_add];rfl
  map_smul' k u := by funext x y z;change a.val x*(k*u.val.val y z)=k*(a.val x*u.val.val y z);ring
def cupClass (a : characters G) : H₂ G →ₗ[Bit] (C₃ G ⧸ boundaries₃ G) :=
  (LinearMap.range (boundaryLinear G)).mapQ (boundaries₃ G) (cupCycle a) (by
    rintro _ ⟨t,rfl⟩
    have ha : a.val 1=0 := by simpa using a.property 1 1
    have ht : t.val 1=0 := t.property
    let u (x y : G) : Bit := a.val x*t.val y
    refine ⟨⟨u,⟨fun x=>by simp [u,ha],fun x=>by simp [u,ht]⟩⟩,?_⟩
    funext x y z
    change d₂ u x y z=a.val x*(t.val z+t.val (y*z)+t.val y)
    dsimp [d₂,u]
    rw [a.property]
    ring_nf <;> simp [show (2:Bit)=0 by decide])
theorem cup_natural (f : E→*G) (a : characters G) (v : H₂ G) :
    inflate₃ f (cupClass a v) = cupClass (characterPull f a) (inflate₂ f v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ u => rfl
theorem cupClass_eq_obstruction (c : Cocycle G) (a : characters G) :
    cupClass a (Submodule.Quotient.mk (⟨⟨c.val,⟨c.norm_left,c.norm_right⟩⟩,
      funext fun x=>funext fun y=>funext fun z=>c.condition x y z⟩ : cycles₂ G)) = cupObstruction c a := by
  apply congrArg (Submodule.Quotient.mk (p:=boundaries₃ G))
  funext x y z
  change a.val x*c.val y z = a.val x*c.val y z+0*_
  simp
end BinaryFactor
end
section
namespace BinaryFactor
open Cocycle
variable {G : Type*} [Group G] (c : Cocycle G)
def cohomClass : H₂ G := Submodule.Quotient.mk (⟨⟨c.val,⟨c.norm_left,c.norm_right⟩⟩,
      funext fun x=>funext fun y=>funext fun z=>c.condition x y z⟩ : cycles₂ G)
theorem invisible_of_nonsplit (h : cohomClass c≠0) : invisible c := by
  intro a
  by_contra hn
  have ha : a.val zbit=1 := (bit_cases _).resolve_left hn
  have hh (x : G) (i : Bit) : a.val ((x,i) : G×Bit)=a.val (base x)+i := by
    rcases bit_cases i with rfl|rfl
    · simp [base]
    · have hp : c.prod (base x) zbit=(x,1) := by simp [prod,zbit,base,c.norm_right]
      have hh := a.property (base x) zbit
      change a.val (c.prod (base x) zbit)=_ at hh
      rwa [hp,ha] at hh
  apply h
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  let t : normalOne G := ⟨fun x=>a.val (base x),by
    change a.val (1:c.Twist)=0
    simpa using a.property 1 1⟩
  refine ⟨t,?_⟩
  apply Subtype.ext;apply Subtype.ext;funext x y
  have he := a.property (base x) (base y)
  change a.val (c.prod (base x) (base y))=a.val (base x)+a.val (base y) at he
  change a.val ((x*y,0+0+c.val x y) : G×Bit)=a.val (base x)+a.val (base y) at he
  rw [zero_add,zero_add,hh] at he
  change a.val (base y)+a.val (base (x*y))+a.val (base x)=c.val x y
  linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) he
def bockClass : C₃ G ⧸ boundaries₃ G := (boundaries₃ G).mkQ c.bock
lemma obstruction_decomp (a : characters G) (e : Bit) :
    obstructionLinear c (a,e)=cupObstruction c a+e • bockClass c := by
  change (boundaries₃ G).mkQ _ = (boundaries₃ G).mkQ _+e • (boundaries₃ G).mkQ _
  rw [←map_smul,←map_add]
  congr 1
  funext x y z
  change a.val x*c.val y z+e*c.bock x y z=(a.val x*c.val y z+0*c.bock x y z)+e*c.bock x y z
  simp
theorem epsilon_iff_bock :
    epsilon c=1 ↔ bockClass c ∈ LinearMap.range (cupObstruction c) := by
  have htop : LinearMap.range (epsilonMap c)=⊤ ↔ (1:Bit) ∈ LinearMap.range (epsilonMap c) := by
    constructor
    · intro h;rw [h];trivial
    · intro h;apply top_unique;intro x _
      rcases bit_cases x with rfl|rfl
      · exact Submodule.zero_mem _
      · exact h
  have heps : epsilon c=1 ↔ LinearMap.range (epsilonMap c)=⊤ := by
    constructor
    · intro h;exact Submodule.eq_top_of_finrank_eq (h.trans (Module.finrank_self ..).symm)
    · intro h;rw [epsilon,h,finrank_top,Module.finrank_self]
  rw [heps,htop]
  constructor
  · rintro ⟨p,hp⟩
    have he : p.val.2=1 := hp
    refine ⟨p.val.1,?_⟩
    have hz : obstructionLinear c (p.val.1,p.val.2)=0 := p.property
    rw [obstruction_decomp,he,one_smul] at hz
    have hs : bockClass c+bockClass c=0 := by rw [←two_smul Bit,show (2:Bit)=0 by decide,zero_smul]
    exact add_right_cancel (hz.trans hs.symm)
  · rintro ⟨a,ha⟩
    refine ⟨⟨(a,1),?_⟩,rfl⟩
    change obstructionLinear c (a,1)=0
    rw [obstruction_decomp,one_smul,ha,←two_smul Bit,show (2:Bit)=0 by decide,zero_smul]
end BinaryFactor
end
section
namespace BinaryFactor
open Cocycle
variable {G : Type*} [Group G]
def Cocycle.asCycle (c : Cocycle G) : cycles₂ G :=
  ⟨⟨c.val,c.norm_left,c.norm_right⟩,by funext x y z; exact c.condition x y z⟩
def ofCycle (z : cycles₂ G) : Cocycle G :=
  ⟨z.val.val,z.val.property.1,z.val.property.2,
    fun x y w => congrFun (congrFun (congrFun z.property x) y) w⟩
def gaugeEquiv (c h : Cocycle G) (t : G → Bit)
    (eq : ∀ x y, t y + t (x*y) + t x = c.val x y - h.val x y) : c.Twist ≃* h.Twist where
  toFun x := (x.1,x.2+t x.1)
  invFun x := (x.1,x.2+t x.1)
  left_inv x := Prod.ext rfl (by change x.2+t x.1+t x.1=x.2; rw [add_assoc,add_self,add_zero])
  right_inv x := Prod.ext rfl (by change x.2+t x.1+t x.1=x.2; rw [add_assoc,add_self,add_zero])
  map_mul' x y := by
    change ((x.1*y.1,x.2+y.2+c.val x.1 y.1+t (x.1*y.1)) : G × Bit) =
      (x.1*y.1,(x.2+t x.1)+(y.2+t y.1)+h.val x.1 y.1)
    congr 1
    linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) -(eq x.1 y.1)
noncomputable def classCocycle (x : H₂ G) : Cocycle G :=
  ofCycle ((Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear G))) x).choose
theorem exists_class_equiv (c : Cocycle G) :
    ∃ x : H₂ G, ∃ e : c.Twist ≃* (classCocycle x).Twist,
      ∀ g : c.Twist, (classCocycle x).projTwist (e g)=c.projTwist g := by
  let x : H₂ G := Submodule.Quotient.mk c.asCycle
  let a := ((Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear G))) x).choose
  have h : (Submodule.Quotient.mk c.asCycle : H₂ G) = Submodule.Quotient.mk a :=
    ((Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear G))) x).choose_spec.symm
  obtain ⟨t,ht⟩ := (Submodule.Quotient.eq _).mp h
  have eq (y z : G) : t.val z + t.val (y*z) + t.val y = c.val y z - (classCocycle x).val y z :=
    congrArg (fun j : cycles₂ G => j.val.val y z) ht
  exact ⟨x,gaugeEquiv c (classCocycle x) t.val eq,fun _ => rfl⟩
end BinaryFactor
end
section
namespace BinaryFactor
open Cocycle
variable {G E : Type*} [Group G] [Group E]
private theorem add_identity :
    ∀ a b c d A B C D : Bit, a+b+c+d=0 → A+B+C+D=0 →
    a*A+b*B+c*C+d*D =
      (d+D)*(b+B)+(a+A)*(c+C)-(d*b+a*c + (D*B+A*C)) := by decide
private def gaugeBit (u v w : Bit) := w+u*v+u*w+v*w
private theorem gauge_identity :
    ∀ x y z xy yz xyz : Bit,
      gaugeBit y z yz + gaugeBit xy z xyz + gaugeBit x yz xyz + gaugeBit x y xy =
      (y+xy+x)*(z+xyz+xy)+(z+yz+y)*(yz+xyz+x) := by decide
private theorem scalar_zero (u : Bit) : gaugeBit 0 u u=0 ∧ gaugeBit u 0 u=0 :=
  (show ∀u : Bit,gaugeBit 0 u u=0 ∧ gaugeBit u 0 u=0 by decide) u
private def bockCycles (G : Type*) [Group G] : cycles₂ G →ₗ[Bit] (C₃ G ⧸ boundaries₃ G) where
  toFun u := bockClass (ofCycle u)
  map_add' u v := by
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
    rw [←Submodule.Quotient.mk_add]
    apply (Submodule.Quotient.eq _).mpr
    let F (x y : G) := u.val.val x y * v.val.val x y
    refine ⟨⟨F,⟨fun y => by simp [F,u.val.property.1],fun x => by simp [F,u.val.property.2]⟩⟩,?_⟩
    funext x y z
    have hu := (ofCycle u).condition x y z
    have hv := (ofCycle v).condition x y z
    exact add_identity _ _ _ _ _ _ _ _ hu hv
  map_smul' k u := by
    change bockClass (ofCycle (k • u)) = k • bockClass (ofCycle u)
    rcases bit_cases k with rfl|rfl
    · rw [zero_smul,zero_smul]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨0,by funext x y z; change (0:Bit)=0*0+0*0;simp⟩
    · rw [one_smul,one_smul]
def bockH (G : Type*) [Group G] : H₂ G →ₗ[Bit] (C₃ G ⧸ boundaries₃ G) :=
  (LinearMap.range (boundaryLinear G)).liftQ (bockCycles G) (by
    rintro _ ⟨t,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    let F (x y : G) := gaugeBit (t.val x) (t.val y) (t.val (x*y))
    have h0 : t.val 1=0 := t.property
    refine ⟨⟨F,⟨fun y => by simpa only [F,h0,one_mul] using (scalar_zero (t.val y)).1,
      fun x=>by simpa only [F,h0,mul_one] using (scalar_zero (t.val x)).2⟩⟩,?_⟩
    funext x y z
    change gaugeBit _ _ _ + gaugeBit _ _ (t.val ((x*y)*z)) +
      gaugeBit _ _ _ +gaugeBit _ _ _ =
      (t.val y+t.val (x*y)+t.val x)*(t.val z+t.val ((x*y)*z)+t.val (x*y))+
      (t.val z+t.val (y*z)+t.val y)*(t.val (y*z)+t.val (x*(y*z))+t.val x)
    rw [mul_assoc]
    exact gauge_identity ..)
theorem bockH_cohomClass (c : Cocycle G) : bockH G (cohomClass c)=bockClass c := rfl
theorem bock_natural (f : E →* G) (u : H₂ G) :
    inflate₃ f (bockH G u)=bockH E (inflate₂ f u) := by
  induction u using Submodule.Quotient.induction_on with
  | _ v =>
    apply congrArg (Submodule.Quotient.mk (p:=boundaries₃ E))
    funext x y z
    change v.val.val (f x) (f y)*v.val.val (f x*f y) (f z)+
      v.val.val (f y) (f z)*v.val.val (f x) (f y*f z)=
      v.val.val (f x) (f y)*v.val.val (f (x*y)) (f z)+
      v.val.val (f y) (f z)*v.val.val (f x) (f (y*z))
    rw [map_mul,map_mul]
end BinaryFactor
end
section
namespace BinaryFactor.Elementary
open Erdos1160Growth.LowerTriangularUpper
open BinaryFactor
abbrev Vectors (d : ℕ) := Multiplicative (Fin d → Bit)
abbrev Coeffs (d : ℕ) := Slot d → Bit
def expand {d : ℕ} (u : Coeffs d) : P d 1 := fun l _ => u l
def bilCycle {d : ℕ} (B : V d →+ V d →+ V 1) : cycles₂ (Vectors d) :=
  ⟨⟨fun x y => B x.toAdd y.toAdd 0,
    fun y => by change B 0 y.toAdd 0=0; simp,
    fun x => by change B x.toAdd 0 0=0; simp⟩,by
    funext x y z
    change B y.toAdd z.toAdd 0+B (x.toAdd+y.toAdd) z.toAdd 0+
      B x.toAdd (y.toAdd+z.toAdd) 0+B x.toAdd y.toAdd 0=0
    simp only [map_add,AddMonoidHom.add_apply,Pi.add_apply]
    ring_nf <;> simp [show (2:Bit)=0 by decide]⟩
def coeffCycles (d : ℕ) : Coeffs d →ₗ[Bit] cycles₂ (Vectors d) where
  toFun u := bilCycle (form (expand u))
  map_add' u v := by
    apply Subtype.ext;apply Subtype.ext;funext x y
    change form (expand u+expand v) x.toAdd y.toAdd 0=_
    rw [form_add];rfl
  map_smul' a u := by
    rcases bit_cases a with rfl|rfl
    · simp only [zero_smul,map_zero]
      apply Subtype.ext; apply Subtype.ext; funext x y
      change form (0: P d 1) x.toAdd y.toAdd 0=0
      simp [form]
    · simp
def coeffMap (d : ℕ) : Coeffs d →ₗ[Bit] H₂ (Vectors d) :=
  (LinearMap.range (boundaryLinear (Vectors d))).mkQ.comp (coeffCycles d)
theorem coeffMap_inj (d : ℕ) : Function.Injective (coeffMap d) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro u hu
  obtain ⟨g,hg⟩ := (Submodule.Quotient.mk_eq_zero _).mp (show coeffMap d u=0 from hu)
  let C (x y : V d) : Bit := form (expand u) x y 0
  have eq (x y : V d) : g.val (.ofAdd y) + g.val (.ofAdd (x+y)) + g.val (.ofAdd x)=C x y :=
    congrArg (fun z : cycles₂ (Vectors d) => z.val.val (.ofAdd x) (.ofAdd y)) hg
  have sym (x y : V d) : C x y=C y x := by
    rw [←eq,←eq y x,add_comm y x]
    abel
  have diag (x : V d) : C x x=0 := by
    rw [←eq,two_copies_zero]
    rw [show g.val (.ofAdd 0)=0 from g.property,add_zero,add_self]
  change u=0
  funext l
  rcases l with p | i
  · let k := (Sum.inl p : Slot d)
    have hlt : col k < row k := p.2.isLt
    calc
      u (.inl p) = C (bit (row k)) (bit (col k)) := (congrFun (form_at_slot (expand u) k) 0).symm
      _ = C (bit (col k)) (bit (row k)) := sym _ _
      _ = 0 := congrFun (form_above (expand u) _ _ hlt) 0
  · exact (congrFun (form_at_slot (expand u) (.inr i)) 0).symm.trans (diag (bit i))
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open Erdos1160Growth.LowerTriangularUpper
open BinaryFactor Cocycle
private def kernelMap {d : ℕ} (c : Cocycle (Vectors d)) : Multiplicative (V 1) →* c.Twist where
  toFun w := (1,w.toAdd 0)
  map_one' := rfl
  map_mul' u v := by
    change ((1 : Vectors d),u.toAdd 0+v.toAdd 0) = c.prod (1,u.toAdd 0) (1,v.toAdd 0)
    simp [prod,c.norm_left]
private def data {d : ℕ} (c : Cocycle (Vectors d)) : CentralData c.Twist d 1 where
  incl := kernelMap c
  proj := c.projTwist
  incl_inj := by
    intro w z h
    have eq : w.toAdd 0=z.toAdd 0 := congrArg Prod.snd h
    apply Multiplicative.toAdd.injective; funext j
    exact (Subsingleton.elim j (0:Fin 1)) ▸ eq
  proj_onto := c.projTwist_onto
  exact_ker := by
    ext z
    constructor
    · intro h
      refine ⟨.ofAdd (fun _=>z.2),?_⟩
      exact Prod.ext (show 1=z.1 from h.symm) rfl
    · rintro ⟨w,rfl⟩; rfl
  central w x := (Subgroup.mem_center_iff.mp (c.projTwist_central (show kernelMap c w ∈ c.projTwist.ker from rfl)) x).symm
private theorem factor_equation {d : ℕ} (c : Cocycle (Vectors d)) :
    ∃ (B : V d →+ V d →+ V 1) (u : C₁ (Vectors d)), u 1=0 ∧
      ∀ x y : Vectors d, u x + u y + c.val x y = B x.toAdd y.toAdd 0 + u (x*y) := by
  obtain ⟨σ,B,hπ,hm⟩ := (data c).exists_bilinear_section
  refine ⟨B,fun x => (σ x.toAdd).2,congrArg Prod.snd (CentralData.section_zero (data c) σ B hm),?_⟩
  intro x y
  have h := congrArg Prod.snd (hm x.toAdd y.toAdd)
  have hx (a : Vectors d) : (σ a.toAdd).1=a := congrArg Multiplicative.ofAdd (hπ a.toAdd)
  change (σ x.toAdd).2+(σ y.toAdd).2+c.val (σ x.toAdd).1 (σ y.toAdd).1 =
    B x.toAdd y.toAdd 0+(σ (x.toAdd+y.toAdd)).2+c.val 1 (σ (x.toAdd+y.toAdd)).1 at h
  rw [hx,hx,c.norm_left,add_zero] at h
  exact h
theorem coeffMap_surj (d : ℕ) : Function.Surjective (coeffMap d) := by
  intro z
  obtain ⟨b,rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear (Vectors d))) z
  let c := ofCycle b
  obtain ⟨B,u,hu,he⟩ := factor_equation c
  let U := form (upperArray B)
  let T := lowerArray B+upperArray B
  let t : Coeffs d := fun l => T l 0
  have het : expand t=T := by
    funext l i
    exact congrArg (T l) (Subsingleton.elim (0:Fin 1) i)
  refine ⟨t,(Submodule.Quotient.eq _).mpr ?_⟩
  let f : normalOne (Vectors d) := ⟨fun x => u x+U x.toAdd x.toAdd 0,by
    change u 1+U 0 0 0=0; rw [hu,U.map_zero];rfl⟩
  refine ⟨f,Subtype.ext (Subtype.ext (funext (fun x => funext (fun y => ?_))))⟩
  have split := congrArg (fun Z : V d →+ V d →+ V 1 => Z x.toAdd y.toAdd 0) (split_matrix B)
  change B x.toAdd y.toAdd 0=form (lowerArray B) x.toAdd y.toAdd 0+U y.toAdd x.toAdd 0 at split
  have h := he x y
  change (u y+U y.toAdd y.toAdd 0)+(u (x*y)+U (x.toAdd+y.toAdd) (x.toAdd+y.toAdd) 0)+
    (u x+U x.toAdd x.toAdd 0)=form (expand t) x.toAdd y.toAdd 0 - c.val x y
  rw [het,show form T=form (lowerArray B)+U from form_add ..]
  simp only [map_add,AddMonoidHom.add_apply,Pi.add_apply]
  linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) h + split
noncomputable def coordinateEquiv (d : ℕ) : Coeffs d ≃ₗ[Bit] H₂ (Vectors d) :=
  LinearEquiv.ofBijective (coeffMap d) ⟨coeffMap_inj d,coeffMap_surj d⟩
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open Erdos1160Growth.LowerTriangularUpper
theorem elementary_r₂ (d : ℕ) : r₂ (Vectors d)=d*(d-1)/2+d := by
  classical
  change Module.finrank Bit (H₂ (Vectors d))=_
  rw [←(coordinateEquiv d).finrank_eq]
  change Module.finrank Bit (Slot d → Bit)=_
  rw [Module.finrank_fintype_fun_eq_card,←Nat.card_eq_fintype_card]
  simp only [Slot,Nat.card_sum,Erdos1160Growth.SharpFamily.triangular_card,Nat.card_fin]
theorem coefficients_of_representative {d : ℕ} (u : Coeffs d) (z : cycles₂ (Vectors d))
    (hz : Submodule.Quotient.mk z = coordinateEquiv d u) :
    (∀ i, z.val.val (.ofAdd (bit i)) (.ofAdd (bit i))=u (.inr i)) ∧
    (∀ p : (i : Fin d) × Fin i.val, let l : Slot d := .inl p
      let x : Vectors d := .ofAdd (bit (row l))
      let y : Vectors d := .ofAdd (bit (col l))
      z.val.val x y + z.val.val y x=u l) := by
  obtain ⟨g,hg⟩ := (Submodule.Quotient.eq _).mp (show Submodule.Quotient.mk z = coeffMap d u from hz)
  let C (x y : V d) := form (expand u) x y 0
  have eq (x y : V d) : g.val (.ofAdd y) + g.val (.ofAdd (x+y)) + g.val (.ofAdd x)=
      z.val.val (.ofAdd x) (.ofAdd y) - C x y :=
    congrArg (fun t : cycles₂ (Vectors d) => t.val.val (.ofAdd x) (.ofAdd y)) hg
  constructor
  · intro i
    have h := eq (bit i) (bit i)
    rw [two_copies_zero,show g.val (.ofAdd 0)=0 from g.property,add_zero,add_self] at h
    exact (sub_eq_zero.mp h.symm).trans (congrFun (form_at_slot (expand u) (.inr i)) 0)
  · intro p
    let l : Slot d := .inl p
    let x := bit (row l)
    let y := bit (col l)
    have h := eq x y
    have h' := eq y x
    rw [add_comm y x] at h'
    have hl : C x y=u l := congrFun (form_at_slot (expand u) l) 0
    have hl' : C y x=0 := congrFun (form_above (expand u) _ _ p.2.isLt) 0
    change z.val.val (.ofAdd x) (.ofAdd y)+z.val.val (.ofAdd y) (.ofAdd x)=u l
    rw [←hl]
    rw [hl'] at h'
    linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) -h+h'
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open Erdos1160Growth.LowerTriangularUpper
def characterDual (d : ℕ) : characters (Vectors d) ≃ₗ[Bit] Module.Dual Bit (V d) where
  toFun a :=
    let h : V d →+ Bit := {
      toFun := fun x => a.val (.ofAdd x)
      map_zero' := by have h := a.property 1 1; change a.val 1=0; simpa using h
      map_add' x y := a.property (.ofAdd x) (.ofAdd y)
    }
    h.toZModLinearMap 2
  invFun f := ⟨fun x=>f x.toAdd,fun x y=>f.map_add x.toAdd y.toAdd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem adapted_characters {d r : ℕ} (a : Fin r → characters (Vectors d)) (h : LinearIndependent Bit a) :
    ∃ (χ : Module.Basis (Fin d) Bit (characters (Vectors d))) (e : Fin d → Vectors d)
      (idx : Fin r ↪ Fin d), (∀ i, χ (idx i) = a i) ∧
        ∀ i j, (χ i).val (e j)=if i=j then 1 else 0 := by
  classical
  let J := h.linearIndepOn_id.extend (Set.subset_univ (Set.range a))
  let B : Module.Basis J Bit (characters (Vectors d)) := Module.Basis.extend h.linearIndepOn_id
  let _ : Fintype J := Fintype.ofFinite _
  let H := characterDual d
  have hd : Fintype.card J=d := by
    rw [← Module.finrank_eq_card_basis B,H.finrank_eq,Subspace.dual_finrank_eq,Module.finrank_fin_fun]
  let j := Fintype.equivFinOfCardEq hd
  let χ := B.reindex j
  let D := χ.map H
  let e (i : Fin d) : Vectors d := .ofAdd ((Module.evalEquiv Bit (V d)).symm (D.dualBasis i))
  let old (i : Fin r) : J := ⟨a i,h.linearIndepOn_id.subset_extend _ ⟨i,rfl⟩⟩
  let embed : Fin r ↪ Fin d := ⟨j ∘ old,j.injective.comp (fun _ _ h' => h.injective (congrArg Subtype.val h'))⟩
  refine ⟨χ,e,embed,fun i=>?_,fun i k=>?_⟩
  · change B.reindex j (j (old i))=a i
    rw [Module.Basis.reindex_apply,j.symm_apply_apply]
    exact Module.Basis.extend_apply_self h.linearIndepOn_id _
  · change D i ((Module.evalEquiv Bit (V d)).symm (D.dualBasis k))=_
    rw [Module.apply_evalEquiv_symm_apply,D.dualBasis_apply_self]
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open Erdos1160Growth.LowerTriangularUpper
theorem adapted_coordinate_iso {d r : ℕ} (a : Fin r → characters (Vectors d))
    (h : LinearIndependent Bit a) :
    ∃ (φ : Vectors d ≃* Vectors d) (idx : Fin r ↪ Fin d),
      ∀ i (x : Vectors d), (a i).val (φ x)=x.toAdd (idx i) := by
  classical
  obtain ⟨χ,_,idx,ha,_⟩ := adapted_characters a h
  let D := χ.map (characterDual d)
  let L := (Module.evalEquiv Bit (V d)).trans D.dualBasis.equivFun
  let φ := L.symm.toAddEquiv.toMultiplicative
  refine ⟨φ,idx,fun i x=>?_⟩
  rw [←ha i]
  change D (idx i) (L.symm x.toAdd)=_
  have he := congrFun (L.apply_symm_apply x.toAdd) (idx i)
  simpa only [L,LinearEquiv.trans_apply,Module.Basis.dualBasis_equivFun,
    Module.evalEquiv_apply,Module.Dual.eval_apply] using he
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open BinaryFactor Cocycle Erdos1160Growth.LowerTriangularUpper
def shuffle {G : Type*} (v : C₃ G) (x y : G) := v x x y+v x y x+v y x x
theorem shuffle_boundary {G : Type*} [CommGroup G] (u : normalTwo G) (x y : G)
    (hx : x*x=1) : shuffle (d₂ u.val) x y=0 := by
  simp only [shuffle,d₂,hx,mul_comm y x,u.property.1,u.property.2]
  ring_nf <;> simp [show (2:Bit)=0 by decide]
theorem shuffle_bock {G : Type*} [CommGroup G] (c : Cocycle G) (x y : G)
    (hx : x*x=1) : shuffle c.bock x y=c.val x y+c.val y x := by
  have hc := c.condition x y x
  simp only [d₂,mul_comm y x] at hc
  simp only [shuffle,bock,hx,mul_comm y x,c.norm_left,c.norm_right,mul_zero,zero_add,add_zero]
  have h : ∀ p q r s : Bit, q+s+r+p=0 → p*r+(p*s+q*r)+q*s=p+q := by decide
  exact h _ _ _ _ hc
def shuffleMap {d : ℕ} (x y : Vectors d) :
    (C₃ (Vectors d) ⧸ boundaries₃ (Vectors d)) →ₗ[Bit] Bit :=
  (boundaries₃ (Vectors d)).liftQ ({
    toFun := fun v=>shuffle v x y
    map_add' := by intro a b;dsimp [shuffle];abel
    map_smul' := by intro r v; change r*_+r*_+r*_ = r*(_+_+_);ring
  } : C₃ (Vectors d) →ₗ[Bit] Bit) (by
    rintro _ ⟨u,rfl⟩
    exact shuffle_boundary u x y (congrArg Multiplicative.ofAdd (two_copies_zero x.toAdd)))
theorem shuffle_difference {d : ℕ} (x y : Vectors d) (c : Cocycle (Vectors d))
    (a : characters (Vectors d)) (hx : a.val x=0) (hy : a.val y=0) :
    shuffleMap x y (bockClass c - cupClass a (cohomClass c)) = c.val x y+c.val y x := by
  rw [map_sub]
  change shuffle c.bock x y-shuffle (cupRaw a.val c.val) x y=_
  rw [shuffle_bock c x y (congrArg Multiplicative.ofAdd (two_copies_zero x.toAdd))]
  simp [shuffle,cupRaw,hx,hy]
private def deleteCoordinate {n : ℕ} (p : Fin (n+1)) : Vectors (n+1) →* Vectors n where
  toFun x := .ofAdd (fun i=>x.toAdd (p.succAbove i))
  map_one' := rfl
  map_mul' _ _ := rfl
abbrev Off (n : ℕ) := (i : Fin n) × Fin i.val
private def offCoeffs (n : ℕ) : (Off n → Bit) →ₗ[Bit] Coeffs n where
  toFun u := Sum.elim u (fun _=>0)
  map_add' a b := by funext i;cases i <;> simp
  map_smul' a b := by funext i;cases i <;> simp
private theorem split_nonzero {n : ℕ} (a : characters (Vectors (n+1))) (ha : a ≠ 0) :
    ∃ (R : Vectors (n+1) →* Vectors n) (x : Fin n → Vectors (n+1)) (e : Vectors (n+1)),
      (∀i,R (x i)=.ofAdd (bit i)) ∧ (∀i,a.val (x i)=0) ∧ R e=1 ∧ a.val e=1 := by
  classical
  obtain ⟨φ,idx,he⟩ := adapted_coordinate_iso (fun _ : Fin 1=>a) (linearIndependent_unique_iff.mpr ha)
  let p := idx 0
  let y (i : Fin n) : Vectors (n+1) := .ofAdd (p.insertNth 0 (bit i))
  let v : Vectors (n+1) := .ofAdd (p.insertNth 1 (fun _=>0))
  let R := (deleteCoordinate p).comp φ.symm.toMonoidHom
  have drop (w : Vectors (n+1)) : R (φ w)=deleteCoordinate p w :=
    congrArg (deleteCoordinate p) (φ.symm_apply_apply w)
  refine ⟨R,fun i=>φ (y i),φ v,?_,?_,?_,?_⟩
  · intro i; rw [drop]
    apply Multiplicative.toAdd.injective
    funext j
    exact Fin.insertNth_apply_succAbove (α:=fun _=>Bit) p 0 (bit i) j
  · intro i; rw [he 0]
    exact Fin.insertNth_apply_same (α:=fun _=>Bit) p 0 (bit i)
  · rw [drop]
    apply Multiplicative.toAdd.injective
    funext j
    exact Fin.insertNth_apply_succAbove (α:=fun _=>Bit) p 1 (fun _=>0) j
  · rw [he 0]
    exact Fin.insertNth_apply_same (α:=fun _=>Bit) p 1 (fun _=>0)
private theorem full_rank_zero (d : ℕ) :
    d*(d-1)/2 ≤ Module.finrank Bit (LinearMap.range (bockH (Vectors d)-cupClass 0)) := by
  classical
  let T := (coeffMap d).comp (offCoeffs d)
  let F := (bockH (Vectors d)-cupClass 0).comp T
  have hF : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro u hu
    funext p
    let l : Slot d := .inl p
    let z := coeffCycles d (offCoeffs d u)
    let c := ofCycle z
    let x : Vectors d := .ofAdd (bit (row l))
    let y : Vectors d := .ofAdd (bit (col l))
    have zero : bockClass c-cupClass 0 (cohomClass c)=0 := hu
    have obs := shuffle_difference x y c 0 rfl rfl
    rw [zero,map_zero] at obs
    exact ((coefficients_of_representative (offCoeffs d u) z rfl).2 p).symm.trans obs.symm
  have hs := Submodule.finrank_mono (LinearMap.range_comp_le_range T (bockH (Vectors d)-cupClass 0))
  change Module.finrank Bit (LinearMap.range F) ≤ _ at hs
  rw [LinearMap.finrank_range_of_inj hF,
    Module.finrank_fintype_fun_eq_card,←Nat.card_eq_fintype_card,
    Erdos1160Growth.SharpFamily.triangular_card] at hs
  exact hs
private theorem full_rank_nonzero {n : ℕ} (a : characters (Vectors (n+1))) (ha : a ≠ 0) :
    r₂ (Vectors n) ≤ Module.finrank Bit (LinearMap.range (bockH (Vectors (n+1))-cupClass a)) := by
  classical
  obtain ⟨R,x,e,hR,hx,hRe,he⟩ := split_nonzero a ha
  let T := (inflate₂ R).comp (coeffMap n)
  let F := (bockH (Vectors (n+1))-cupClass a).comp T
  have hF : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro u hu
    let z := coeffCycles n u
    let c := ofCycle (cyclePull R z)
    have zero : bockClass c-cupClass a (cohomClass c)=0 := hu
    funext l
    rcases l with p | i
    · let l : Slot n := .inl p
      let r := row l
      let s := col l
      have obs := shuffle_difference (x r) (x s) c a (hx r) (hx s)
      rw [zero,map_zero] at obs
      change 0=z.val.val (R (x r)) (R (x s))+z.val.val (R (x s)) (R (x r)) at obs
      rw [hR,hR] at obs
      exact ((coefficients_of_representative u z rfl).2 p).symm.trans obs.symm
    · have obs := congrArg (shuffleMap (x i) e) zero
      rw [map_sub,map_zero] at obs
      change shuffle c.bock (x i) e-shuffle (cupRaw a.val c.val) (x i) e=0 at obs
      rw [shuffle_bock c (x i) e (congrArg Multiplicative.ofAdd (two_copies_zero (x i).toAdd))] at obs
      simp only [shuffle,cupRaw,hx,he,zero_mul,zero_add,one_mul] at obs
      change z.val.val (R (x i)) (R e)+z.val.val (R e) (R (x i))-z.val.val (R (x i)) (R (x i))=0 at obs
      rw [hR,hRe,z.val.property.1,z.val.property.2,zero_add,zero_sub,neg_eq_zero] at obs
      exact ((coefficients_of_representative u z rfl).1 i).symm.trans obs
  have hs := Submodule.finrank_mono (LinearMap.range_comp_le_range T (bockH (Vectors (n+1))-cupClass a))
  rw [show ((bockH (Vectors (n+1))-cupClass a).comp T)=F from rfl,LinearMap.finrank_range_of_inj hF,
    (coordinateEquiv n).finrank_eq] at hs
  exact hs
theorem bock_cup_rank {d : ℕ} (a : characters (Vectors d)) :
    d*(d-1)/2 ≤ Module.finrank Bit (LinearMap.range (bockH (Vectors d)-cupClass a)) := by
  by_cases ha : a=0
  · subst a; exact full_rank_zero d
  cases d with
  | zero => simp
  | succ n =>
    have h := full_rank_nonzero a ha
    rw [elementary_r₂] at h
    have hh : (n+1)*((n+1)-1)/2=n*(n-1)/2+n := by
      cases n with
      | zero => decide
      | succ j =>
        simp only [Nat.add_sub_cancel]
        rw [show (j+1+1)*(j+1)=(j+1)*j+2*(j+1) by ring]
        omega
    rwa [hh]
end BinaryFactor.Elementary
end
section
namespace OrbitUp
open scoped BigOperators Matrix
end OrbitUp
end
section
namespace OrbitUp
end OrbitUp
end
section
namespace BinaryFactor.Elementary
open OrbitUp Cocycle Erdos1160Growth.LowerTriangularUpper
def unitVec {d : ℕ} (i : Fin d) : Vectors d := Multiplicative.ofAdd (bit i)
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open Cocycle Erdos1160Growth.LowerTriangularUpper
def repeatShuffle {G : Type*} (θ : C₃ G) (x y : G) : Bit := θ x x y+θ x y x+θ y x x
theorem repeatShuffle_boundary {G : Type*} [CommGroup G] (g : normalTwo G) (x y : G) (hx : x*x=1) :
    repeatShuffle (d₂ g.val) x y=0 := by
  dsimp [repeatShuffle,d₂]
  rw [hx,g.property.1,g.property.2,mul_comm y x]
  ring_nf <;> simp [show (2:Bit)=0 by decide]
theorem diagonal_boundary {G : Type*} [Group G] (g : normalTwo G) (x : G) (hx : x*x=1) :
    d₂ g.val x x x=0 := by simp [d₂,hx,g.property.1,g.property.2,add_self]
private theorem unitSq {d : ℕ} (i : Fin d) : unitVec i*unitVec i=1 :=
  congrArg Multiplicative.ofAdd (two_copies_zero (bit i))
theorem coordinate_cup_injective {d : ℕ} (a : characters (Vectors d)) (k : Fin d)
    (ha : ∀i,(a.val (unitVec i))=if i=k then 1 else 0) : Function.Injective (cupClass a) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro v hv
  obtain ⟨w,rfl⟩ := coeffMap_surj d v
  let z := coeffCycles d w
  let u (i j : Fin d) := z.val.val (unitVec i) (unitVec j)
  let θ := cupRaw a.val z.val.val
  obtain ⟨g,hg⟩ := (Submodule.Quotient.mk_eq_zero (boundaries₃ (Vectors d))).mp
    (show (boundaries₃ (Vectors d)).mkQ θ=0 from hv)
  have eq : d₂ g.val=θ := hg
  have mix (i j : Fin d) : a.val (unitVec i)*u i j + a.val (unitVec i)*u j i + a.val (unitVec j)*u i i=0 := by
    change repeatShuffle θ (unitVec i) (unitVec j)=0
    rw [←eq]
    exact repeatShuffle_boundary _ _ _ (unitSq i)
  have tri (i j l : Fin d) : a.val (unitVec i)*(u j l+u l j)+a.val (unitVec j)*(u i l+u l i)+
      a.val (unitVec l)*(u i j+u j i)=0 := by
    have h := antisym₃_boundary g.val (unitVec i) (unitVec j) (unitVec l)
    rw [eq] at h
    dsimp [antisym₃,θ,cupRaw] at h
    simpa only [u,mul_add,add_assoc] using h
  have ak : a.val (unitVec k)=1 := by simp [ha]
  have diag (i : Fin d) : u i i=0 := by
    by_cases h : i=k
    · subst i
      have h := diagonal_boundary g (unitVec k) (unitSq k)
      rw [eq] at h
      change a.val (unitVec k)*u k k=0 at h
      simpa only [ak,one_mul] using h
    · simpa [ha,h] using mix i k
  have pairZero (i j : Fin d) (ne : i≠j) : u i j+u j i=0 := by
    by_cases hi : i=k
    · subst i
      simpa [ak,diag] using mix k j
    by_cases hj : j=k
    · subst j
      simpa [ak,diag,add_comm] using mix k i
    simpa [ha,hi,hj] using tri k i j
  have uZero : w=0 := by
    funext slot
    rcases slot with p|i
    · let l : Slot d := .inl p
      have hlt : col l < row l := p.2.isLt
      have h := pairZero (row l) (col l) hlt.ne'
      have h₁ : u (row l) (col l)=w l := congrFun (form_at_slot (expand w) l) 0
      have h₂ : u (col l) (row l)=0 := congrFun (form_above (expand w) _ _ hlt) 0
      simpa [h₁,h₂,l] using h
    · exact (congrFun (form_at_slot (expand w) (.inr i)) 0).symm.trans (diag i)
  change coeffMap d w=0
  rw [uZero,map_zero]
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open Cocycle
theorem admissible_density_of_affine {S : Type*} [AddCommGroup S] [Module Bit S] [Finite S]
    (L : Submodule Bit S) (P : S→Prop) (m n : ℕ)
    (each : ∀s : S,Nat.card {x : L // P (s+x.val)}*m ≤ Nat.card L*n) :
    Nat.card {x : S // x∉L ∧ P x}*m ≤ Nat.card {x : S // x∉L}*n := by
  classical
  let X := {s : S // s∉L}
  let G := {s : S // s∉L ∧ P s}
  let W := (s : X) × {x : L // P (s.val+x.val)}
  letI := Fintype.ofFinite X
  letI := Fintype.ofFinite L
  let e : W ≃ G×L := {
    toFun z := (⟨z.1.val+z.2.val.val,fun h=>z.1.property ((L.add_mem_iff_left z.2.val.property).mp h),z.2.property⟩,z.2.val)
    invFun z := ⟨⟨z.1.val-z.2.val,fun h=>z.1.property.1 (by simpa only [sub_add_cancel] using L.add_mem h z.2.property)⟩,
      ⟨z.2,by simpa only [sub_add_cancel] using z.1.property.2⟩⟩
    left_inv := by
      rintro ⟨⟨x,h⟩,⟨l,hl⟩⟩
      apply Sigma.ext (Subtype.ext (add_sub_cancel_right x l.val))
      apply (Subtype.heq_iff_coe_eq (by intro u;change P (x+l.val-l.val+u.val) ↔ _;rw [add_sub_cancel_right])).2
      rfl
    right_inv := by rintro ⟨⟨x,h⟩,⟨l,hl⟩⟩;simp only [sub_add_cancel] }
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun x (_ : x∈Finset.univ) => each (x : X).val)
  rw [←Finset.sum_mul] at h
  have hc : (∑x:X,Nat.card {l : L // P (x.val+l.val)})=Nat.card G*Nat.card L := by
    rw [←Nat.card_prod,←Nat.card_congr e]
    change _=Nat.card ((x : X) × {l : L // P (x.val+l.val)})
    rw [Nat.card_sigma]
  rw [hc,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,smul_eq_mul] at h
  have bound : (Nat.card G*m)*Nat.card L≤(Nat.card X*n)*Nat.card L := by
    convert h using 1 <;> ac_rfl
  exact Nat.le_of_mul_le_mul_right bound Nat.card_pos
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open Cocycle
theorem cup_injective {d : ℕ} (a : characters (Vectors d)) (ha : a≠0) : Function.Injective (cupClass a) := by
  obtain ⟨φ,i,hi⟩ := adapted_coordinate_iso (fun _ : Fin 1=>a) (linearIndependent_unique_iff.mpr ha)
  let b := characterPull φ.toMonoidHom a
  have hcoord (j : Fin d) : b.val (unitVec j)=if j=i 0 then 1 else 0 := by
    change a.val (φ (unitVec j))=_
    rw [hi (0:Fin 1)]
    simp [unitVec,Erdos1160Growth.LowerTriangularUpper.bit,Pi.single_apply,eq_comm]
  have inj := coordinate_cup_injective b (i 0) hcoord
  intro x y h
  have eq := congrArg (inflate₃ φ.toMonoidHom) h
  rw [cup_natural,cup_natural] at eq
  have hz := congrArg (inflate₂ φ.symm.toMonoidHom) (inj eq)
  have cancel (z : H₂ (Vectors d)) : inflate₂ φ.symm.toMonoidHom (inflate₂ φ.toMonoidHom z)=z := by
    induction z using Submodule.Quotient.induction_on with
    | _ u =>
      apply congrArg (Submodule.Quotient.mk (p:=LinearMap.range (boundaryLinear (Vectors d))))
      apply Subtype.ext;apply Subtype.ext;funext x y
      change u.val.val (φ (φ.symm x)) (φ (φ.symm y))=_
      rw [φ.apply_symm_apply,φ.apply_symm_apply]
  exact (cancel x).symm.trans (hz.trans (cancel y))
theorem affine_zero_count {S T : Type*} [AddCommGroup S] [Module Bit S] [Finite S]
    [AddCommGroup T] [Module Bit T] (f : S→ₗ[Bit] T) (c : T) :
    Nat.card {x : S // c+f x=0}≤Nat.card (LinearMap.ker f) := by
  classical
  let P := {x : S // c+f x=0}
  by_cases h : Nonempty P
  · let b := Classical.choice h
    let m (x : P) : LinearMap.ker f := ⟨x.val-b.val,by
      rw [LinearMap.mem_ker,map_sub,sub_eq_zero]
      exact add_left_cancel (x.property.trans b.property.symm)⟩
    exact Nat.card_le_card_of_injective m (fun x y h=>Subtype.ext (sub_left_inj.mp (congrArg Subtype.val h)))
  · haveI : IsEmpty P := not_nonempty_iff.mp h
    change Nat.card P≤_
    simp
theorem single_cup_density {Y : Type} [Group Y] [Finite Y] {d : ℕ} (f : Y→*Vectors d)
    (a : characters (Vectors d)) (ha : a≠0) (baseClass : H₂ Y) (K₀ : ℕ)
    (hK : Module.finrank Bit (LinearMap.ker (inflate₃ f)) ≤ K₀) :
    Nat.card {x : LinearMap.range (inflate₂ f) // cupClass (characterPull f a) (baseClass+x.val)=0} *
      2^(r₂ (Vectors d)) ≤ Nat.card (LinearMap.range (inflate₂ f))*2^K₀ := by
  classical
  letI : Finite (H₂ Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  letI : Finite (H₂ (Vectors d)) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  let S := LinearMap.range (inflate₂ f)
  let T := (cupClass (characterPull f a)).comp S.subtype
  let W := T.comp (inflate₂ f).rangeRestrict
  let ev : LinearMap.ker W →ₗ[Bit] LinearMap.ker (inflate₃ f) :=
    ((cupClass a).comp (LinearMap.ker W).subtype).codRestrict _ (fun x=>by
      change inflate₃ f (cupClass a x.val)=0
      rw [cup_natural]
      exact x.property)
  have h : Module.finrank Bit (LinearMap.ker W) ≤ K₀ :=
    (LinearMap.finrank_le_finrank_of_injective (f:=ev) (fun x y eq=>Subtype.ext (cup_injective a ha (congrArg (fun t:LinearMap.ker (inflate₃ f)=>t.val) eq)))).trans hK
  have h₁ := LinearMap.finrank_range_add_finrank_ker W
  have h₂ := LinearMap.finrank_range_add_finrank_ker T
  have h₃ : Module.finrank Bit (LinearMap.range W) ≤ Module.finrank Bit (LinearMap.range T) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have e : Module.finrank Bit (LinearMap.ker T)+r₂ (Vectors d) ≤ Module.finrank Bit S+K₀ := by
    unfold r₂;omega
  simp only [map_add]
  apply (Nat.mul_le_mul_right _ (affine_zero_count T (cupClass (characterPull f a) baseClass))).trans
  change Nat.card (LinearMap.ker T)*_ ≤ Nat.card S*_
  rw [Module.natCard_eq_pow_finrank (K:=Bit) (V:=S),Module.natCard_eq_pow_finrank (K:=Bit) (V:=LinearMap.ker T),Nat.card_zmod,←pow_add,←pow_add]
  exact Nat.pow_le_pow_right (by decide) e
end BinaryFactor.Elementary
end
section
namespace Erdos1160.Tables
open CategoryTheory
end Erdos1160.Tables
end
section
namespace Erdos1160.CentralLifts
open scoped commutatorElement
variable {I J : Type} {p : ℕ}
theorem normal_zpowers_of_central {G : Type} [Group G] (u : G) (hz : u ∈ Subgroup.center G) :
    (Subgroup.zpowers u).Normal where
  conj_mem n hn g := by
    have hc := Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hz) hn) g
    rwa [hc,mul_inv_cancel_right]
theorem card_quotient_prime {G : Type} [Group G] {u : G}
    [_n : (Subgroup.zpowers u).Normal] {p k : ℕ} (hp : 0 < p)
    (ho : orderOf u = p) (h : Nat.card G = p^(k+1)) :
    Nat.card (G ⧸ Subgroup.zpowers u) = p^k := by
  apply Nat.mul_left_cancel hp
  calc
    p * Nat.card (G ⧸ Subgroup.zpowers u) = Nat.card (Subgroup.zpowers u) * (Subgroup.zpowers u).index := by
      rw [Nat.card_zpowers, ho, Subgroup.index_eq_card]
    _ = Nat.card G := Subgroup.card_mul_index _
    _ = p*p^k := by rw [h, pow_succ, mul_comm]
end Erdos1160.CentralLifts
end
section
namespace Erdos1160.CentralLifts
open CategoryTheory
variable {p m : ℕ} {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q]
theorem central_prime_in_normal (hp : p.Prime) (hG : IsPGroup p G)
    (N : Subgroup G) [N.Normal] (hd : p ∣ Nat.card N) :
    ∃ u : G, u ∈ N ∧ u ∈ Subgroup.center G ∧ orderOf u = p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp' := hG.of_equiv ConjAct.toConjAct
  have hone : (1 : N) ∈ MulAction.fixedPoints (ConjAct G) N := fun _ => smul_one _
  obtain ⟨b,hb,hb1⟩ := hp'.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hd hone
  let C := N ⊓ Subgroup.center G
  have hc : (b : G) ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    have h := congrArg ((↑) : N → G) (hb (ConjAct.toConjAct g))
    change g * (b:G) * g⁻¹ = b at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hn : Nontrivial C := (Subgroup.nontrivial_iff_exists_ne_one C).mpr
    ⟨b,⟨b.property,hc⟩,fun e => hb1 (Subtype.ext e.symm)⟩
  obtain ⟨k,hk,hC⟩ := (hG.to_subgroup C).nontrivial_iff_card.mp hn
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := C) p (hC ▸ dvd_pow_self _ (Nat.ne_of_gt hk))
  exact ⟨u,u.property.1,u.property.2,(Subgroup.orderOf_coe u).trans hu⟩
omit [Finite G] [Finite Q] in
theorem ker_card_of_epi (hp : p.Prime) {e : ℕ} (hG : Nat.card G = p^(m+e))
    (hQ : Nat.card Q = p^m) (f : G →* Q) (hf : Function.Surjective f) :
    Nat.card f.ker = p^e := by
  apply Nat.mul_left_cancel (n := p^m) (pow_pos hp.pos _)
  calc
    p^m * Nat.card f.ker = f.ker.index * Nat.card f.ker := by
      rw [Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective f hf]
      simp [hQ]
    _ = Nat.card G := f.ker.index_mul_card
    _ = p^m * p^e := hG.trans (pow_add _ _ _)
end Erdos1160.CentralLifts
end
section
namespace BinaryFactor
open Erdos1160.CentralLifts
theorem ker_comp_bound {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module Bit U] [Module Bit V] [Module Bit W] [Finite U] [Finite V]
    (f : U →ₗ[Bit] V) (g : V →ₗ[Bit] W) :
    Module.finrank Bit (LinearMap.ker (g.comp f)) ≤
      Module.finrank Bit (LinearMap.ker g)+Module.finrank Bit (LinearMap.ker f) := by
  let h : (LinearMap.ker (g.comp f)) →ₗ[Bit] (LinearMap.ker g) :=
    (f.comp (LinearMap.ker (g.comp f)).subtype).codRestrict _ (fun u=>u.property)
  let k : (LinearMap.ker h) →ₗ[Bit] (LinearMap.ker f) := {
    toFun := fun x=>⟨x.val.val,congrArg Subtype.val x.property⟩
    map_add' := fun _ _=>rfl
    map_smul' := fun _ _=>rfl }
  have h₁ := LinearMap.finrank_range_add_finrank_ker h
  have h₂ := Submodule.finrank_le (LinearMap.range h)
  have h₃ := LinearMap.finrank_le_finrank_of_injective (f := k)
    (show Function.Injective k from fun _ _ h=>Subtype.ext (Subtype.ext (congrArg (fun z : LinearMap.ker f=>z.val) h)))
  omega
theorem inflation_tower {Q Y : Type} [Group Q] [Finite Q] [Group Y] [Finite Y] {m : ℕ}
    (hQ : Nat.card Q=2^m) (j : ℕ) (hY : Nat.card Y=2^(m+j))
    (f : Y→*Q) (hf : Function.Surjective f) (hΦ : f.ker ≤ frattini Y) :
    Module.finrank Bit (LinearMap.ker (inflate₃ f)) + r₂ Y ≤ j*r₁ Q+r₂ Q ∧ r₁ Y=r₁ Q := by
  induction j generalizing Y with
  | zero =>
    let i := MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).2 ⟨hf,hY.trans hQ.symm⟩)
    have hker : LinearMap.ker (inflate₃ i.toMonoidHom)=⊥ := LinearMap.ker_eq_bot.mpr (inflate₃_iso_inj i)
    change Module.finrank Bit (LinearMap.ker (inflate₃ i.toMonoidHom))+_≤_ ∧ _
    have hr : Module.finrank Bit (LinearMap.ker (inflate₃ i.toMonoidHom))=0 := by rw [hker];exact finrank_bot ..
    exact ⟨by rw [hr,zero_add,zero_mul,zero_add];exact (r₂_equiv i).le,r₁_equiv i⟩
  | succ j ih =>
    have hsize := ker_card_of_epi Nat.prime_two hY hQ f hf
    obtain ⟨u,hu,hz,ho⟩ := central_prime_in_normal Nat.prime_two (IsPGroup.of_card hY) f.ker
      (hsize ▸ dvd_pow_self 2 (Nat.succ_ne_zero j))
    let N := Subgroup.zpowers u
    let _ : N.Normal := normal_zpowers_of_central u hz
    let q := QuotientGroup.mk' N
    have hq := QuotientGroup.mk'_surjective N
    have hN : N ≤ f.ker := Subgroup.zpowers_le.mpr hu
    let F := QuotientGroup.lift N f hN
    have hF : Function.Surjective F := fun x=>by obtain ⟨a,rfl⟩ := hf x;exact ⟨q a,rfl⟩
    have frF : F.ker ≤ frattini (Y ⧸ N) := by
      intro w hw
      obtain ⟨a,rfl⟩ := hq w
      exact frattini_le_comap_frattini_of_surjective hq (hΦ (show a∈f.ker from hw))
    have hmiddle := card_quotient_prime (by decide : 0 < 2) ho (k:=m+j) hY
    obtain ⟨upper,rank⟩ := ih hmiddle F hF frF
    have hk : q.ker=N := QuotientGroup.ker_mk' _
    have hc : Nat.card q.ker=2 := by rw [hk];exact (Nat.card_zpowers u).trans ho
    have hcent : q.ker ≤ Subgroup.center Y := hk.le.trans (Subgroup.zpowers_le.mpr hz)
    obtain ⟨one,rank'⟩ := scalar_inflation q hq hcent hc (hk.le.trans (hN.trans hΦ))
    have hcomp : F.comp q=f := rfl
    let _ : Finite (C₃ Q ⧸ boundaries₃ Q) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective (boundaries₃ Q))
    let _ : Finite (C₃ (Y ⧸ N) ⧸ boundaries₃ (Y ⧸ N)) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective (boundaries₃ (Y ⧸ N)))
    have lower := ker_comp_bound (inflate₃ F) (inflate₃ q)
    rw [←inflate₃_comp,hcomp] at lower
    change Module.finrank Bit (LinearMap.ker (inflate₃ F))+r₂ (Y ⧸ N) ≤ j*r₁ Q+r₂ Q at upper
    change r₁ (Y ⧸ N)=r₁ Q at rank
    rw [rank] at one
    rw [Nat.succ_mul]
    exact ⟨by omega,rank'.trans rank⟩
end BinaryFactor
end
section
namespace BinaryFactor.Elementary
open Cocycle
theorem vectors_card (d : ℕ) : Nat.card (Vectors d)=2^d := by
  change Nat.card (Fin d→Bit)=_
  rw [Nat.card_fun,Nat.card_zmod,Nat.card_fin]
theorem vectors_char_rank (d : ℕ) : r₁ (Vectors d)=d := by
  change Module.finrank Bit (characters (Vectors d))=_
  rw [(characterDual d).finrank_eq,Subspace.dual_finrank_eq,Module.finrank_fin_fun]
end BinaryFactor.Elementary
end
section
namespace BinaryFactor
open Finset
abbrev numFrames (k r : ℕ) := ∏i : Fin r,(2^k-2^i.val)
theorem frame_incidence {X T : Type*} [Finite X] [AddCommGroup T] [Module Bit T] [Finite T]
    (S : X→Submodule Bit T) {r a M B : ℕ} (hr : r ≤ a) (had : a ≤ Module.finrank Bit T)
    (test : ∀v : Fin r→T,LinearIndependent Bit v →
      Nat.card {x : X // ∀i,v i ∈ S x} * M ≤ B) :
    Nat.card {x : X // a ≤ Module.finrank Bit (S x)} * numFrames a r * M ≤
      numFrames (Module.finrank Bit T) r * B := by
  classical
  let Good := {x : X // a ≤ Module.finrank Bit (S x)}
  let Frames := {v : Fin r→T // LinearIndependent Bit v}
  let _ := Fintype.ofFinite Good
  let _ := Fintype.ofFinite Frames
  let R (x : Good) (v : Frames) := ∀i,v.val i∈S x.val
  let left (x : Good) := (univ : Finset Frames).bipartiteAbove R x
  let right (v : Frames) := (univ : Finset Good).bipartiteBelow R v
  have lower (x : Good) : numFrames a r ≤ (left x).card := by
    let U := S x.val
    let f (v : {u : Fin r→U // LinearIndependent Bit u}) : left x :=
      ⟨⟨fun i=>(v.val i).val,v.property.map' _ U.ker_subtype⟩,mem_filter.mpr ⟨mem_univ _,fun i=>(v.val i).property⟩⟩
    have hi : Function.Injective f := by
      intro u v h
      apply Subtype.ext
      funext i
      exact Subtype.ext (congrArg (fun z : left x=>z.val.val i) h)
    have le := Nat.card_le_card_of_injective f hi
    rw [card_linearIndependent (hr.trans x.property),ZMod.card,Nat.card_eq_finsetCard] at le
    exact (prod_le_prod' (fun (i : Fin r) _=> Nat.sub_le_sub_right (Nat.pow_le_pow_right (n:=2) (by decide) x.property) (2^i.val))).trans le
  have upper (v : Frames) : (right v).card*M ≤ B := by
    let f (x : right v) : {z : X // ∀i,v.val i∈S z} :=
      ⟨x.val.val,(mem_filter.mp x.property).2⟩
    have hi : Function.Injective f := fun _ _ h=>Subtype.ext (Subtype.ext (congrArg (fun t : {z : X // ∀i,v.val i∈S z}=>t.val) h))
    have le := Nat.card_le_card_of_injective f hi
    rw [Nat.card_eq_finsetCard] at le
    exact (Nat.mul_le_mul_right _ le).trans (test v.val v.property)
  have left_sum := (Finset.univ : Finset Good).card_nsmul_le_sum _ _ (fun x _=> lower x)
  have right_sum := (Finset.univ : Finset Frames).sum_le_card_nsmul _ _ (fun v _=>upper v)
  have lenses : (∑x : Good,(left x).card)=(∑v : Frames,(right v).card) :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
  simp only [nsmul_eq_mul,card_univ] at left_sum right_sum
  rw [←sum_mul,←lenses] at right_sum
  have goal := (Nat.mul_le_mul_right M left_sum).trans right_sum
  rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card] at goal
  simpa only [Nat.cast_id,Frames,Good,card_linearIndependent (hr.trans had),ZMod.card,numFrames] using goal
end BinaryFactor
end
section
namespace BinaryFactor
open Cocycle
variable {G : Type*} [Group G]
def cupWith (v : H₂ G) : characters G →ₗ[Bit] (C₃ G ⧸ boundaries₃ G) where
  toFun a := cupClass a v
  map_add' a b := by
    induction v using Submodule.Quotient.induction_on with
    | _ u =>
      change (boundaries₃ G).mkQ _ = (boundaries₃ G).mkQ _+(boundaries₃ G).mkQ _
      rw [←map_add];congr 1;funext x y z
      change (a.val x+b.val x)*u.val.val y z=a.val x*u.val.val y z+b.val x*u.val.val y z
      rw [add_mul]
  map_smul' k a := by
    induction v using Submodule.Quotient.induction_on with
    | _ u =>
      change (boundaries₃ G).mkQ _ = k • (boundaries₃ G).mkQ _
      rw [←map_smul];congr 1;funext x y z
      change (k*a.val x)*u.val.val y z=k*(a.val x*u.val.val y z)
      rw [mul_assoc]
noncomputable def annRank (v : H₂ G) := Module.finrank Bit (LinearMap.ker (cupWith v))
theorem annRank_cohomClass (c : Cocycle G) : annRank (cohomClass c)=Module.finrank Bit (cupAnn c) := by
  have eq : cupWith (cohomClass c)=cupObstruction c := LinearMap.ext (cupClass_eq_obstruction c)
  rw [annRank,eq]
end BinaryFactor
end
section
namespace BinaryFactor.Elementary
open Cocycle
theorem cup_union_density {Y : Type} [Group Y] [Finite Y] {d n : ℕ}
    (hY : Nat.card Y=2^(d+n)) (f : Y→*Vectors d) (hf : Function.Surjective f)
    (hΦ : f.ker ≤ frattini Y) (hd : 1 ≤ d) (baseClass : H₂ Y) :
    Nat.card {x : LinearMap.range (inflate₂ f) // 0 < annRank (baseClass+x.val)} * 2^(d*(d-1)/2+d) ≤
      (2^d-1) * (Nat.card (LinearMap.range (inflate₂ f))*2^(d*n+(d*(d-1)/2+d)-r₂ Y)) := by
  classical
  letI : Finite (H₂ Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  obtain ⟨bound,rank⟩ := inflation_tower (vectors_card d) n hY f hf hΦ
  rw [vectors_char_rank,elementary_r₂,Nat.mul_comm n d] at bound
  have dY : Module.finrank Bit (characters Y)=d := rank.trans (vectors_char_rank d)
  let K₀ := d*n+(d*(d-1)/2+d)-r₂ Y
  have kBd : Module.finrank Bit (LinearMap.ker (inflate₃ f)) ≤ K₀ := by dsimp [K₀];omega
  have inj : Function.Injective (characterPull f) := by
    intro a b eq;apply Subtype.ext;funext x;obtain ⟨y,rfl⟩ := hf x
    exact congrArg (fun h : characters Y=>h.val y) eq
  have sur := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rank.symm).1 inj
  let L := LinearMap.range (inflate₂ f)
  let S (x : L) := LinearMap.ker (cupWith (baseClass+x.val))
  have h := frame_incidence S (r:=1) (a:=1) le_rfl (dY ▸ hd)
    (M:=2^(r₂ (Vectors d))) (B:=Nat.card L*2^K₀) (by
      intro v hv
      obtain ⟨a,ha⟩ := sur (v 0)
      have an : a≠0 := fun eq=>hv.ne_zero 0 (ha.symm.trans (eq ▸ map_zero _))
      let I := {x : L // ∀i,v i∈S x}
      let T := {x : L // cupClass (characterPull f a) (baseClass+x.val)=0}
      let m (x : I) : T := ⟨x.val,by rw [ha];exact x.property 0⟩
      have lower := Nat.card_le_card_of_injective m (fun x y eq=>Subtype.ext (congrArg (fun z:T=>z.val) eq))
      exact (Nat.mul_le_mul_right _ lower).trans (single_cup_density f a an baseClass _ kBd))
  simpa only [S,annRank,Nat.succ_le_iff,numFrames,Fin.prod_univ_one,Fin.val_zero,pow_zero,
    dY,elementary_r₂,one_pow,show 2^1-1=1 by decide,mul_one] using h
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open Cocycle
theorem fixed_bock_density {Y : Type} [Group Y] [Finite Y] {d : ℕ} (f : Y→*Vectors d)
    (a : characters (Vectors d)) (z : H₂ Y) {K : ℕ}
    (hK : Module.finrank Bit (LinearMap.ker (inflate₃ f)) ≤ K) :
    Nat.card {x : LinearMap.range (inflate₂ f) //
      (bockH Y-cupClass (characterPull f a)) (z+x.val)=0} * 2^(d*(d-1)/2) ≤
        Nat.card (LinearMap.range (inflate₂ f))*2^K := by
  classical
  letI : Finite (H₂ Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  letI : Finite (H₂ (Vectors d)) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  let L := LinearMap.range (inflate₂ f)
  let B := bockH (Vectors d)-cupClass a
  let C := bockH Y-cupClass (characterPull f a)
  let T := C.comp L.subtype
  let W := (inflate₃ f).comp (LinearMap.range B).subtype
  let embed : LinearMap.ker W →ₗ[Bit] LinearMap.ker (inflate₃ f) :=
    (((LinearMap.range B).subtype).comp (LinearMap.ker W).subtype).codRestrict _ (fun x=>x.property)
  have hker : Module.finrank Bit (LinearMap.ker W) ≤ K :=
    (LinearMap.finrank_le_finrank_of_injective (f:=embed) (fun _ _ he=>Subtype.ext (Subtype.ext
      (congrArg (fun t : LinearMap.ker (inflate₃ f)=>t.val) he)))).trans hK
  have inc : LinearMap.range W ≤ LinearMap.range T := by
    rintro _ ⟨⟨_,v,rfl⟩,rfl⟩
    refine ⟨(inflate₂ f).rangeRestrict v,?_⟩
    change bockH Y (inflate₂ f v)-cupClass (characterPull f a) (inflate₂ f v)=inflate₃ f _
    change _=inflate₃ f (bockH _ v-cupClass a v)
    rw [map_sub,bock_natural,cup_natural]
  have h₁ := LinearMap.finrank_range_add_finrank_ker W
  have h₂ := LinearMap.finrank_range_add_finrank_ker T
  have h₃ := Submodule.finrank_mono inc
  have h₄ : d*(d-1)/2 ≤ Module.finrank Bit (LinearMap.range B) := bock_cup_rank a
  have exp : Module.finrank Bit (LinearMap.ker T)+d*(d-1)/2 ≤ Module.finrank Bit L+K := by omega
  change Nat.card {x : L // C (z+x.val)=0}*_≤_
  simp only [map_add]
  apply (Nat.mul_le_mul_right _ (affine_zero_count T (C z))).trans
  change Nat.card (LinearMap.ker T)*_ ≤ Nat.card L*_
  rw [Module.natCard_eq_pow_finrank (K:=Bit) (V:=LinearMap.ker T),
    Module.natCard_eq_pow_finrank (K:=Bit) (V:=L),Nat.card_zmod,←pow_add,←pow_add]
  exact Nat.pow_le_pow_right (by decide) exp
def bockHit {Y : Type*} [Group Y] (v : H₂ Y) := ∃a : characters Y,(bockH Y-cupClass a) v=0
def exceptional {Y : Type*} [Group Y] (v : H₂ Y) := 0 < annRank v ∨ bockHit v
theorem bockHit_iff {Y : Type*} [Group Y] (c : Cocycle Y) :
    bockHit (cohomClass c) ↔ epsilon c=1 := by
  rw [epsilon_iff_bock]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    exact (sub_eq_zero.mp (show bockClass c-cupObstruction c a=0 from by
      rw [←bockH_cohomClass,←cupClass_eq_obstruction];exact ha)).symm
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    change bockH Y (cohomClass c)-cupClass a (cohomClass c)=0
    rw [sub_eq_zero,bockH_cohomClass]
    exact ha.symm.trans (cupClass_eq_obstruction c a).symm
theorem exceptional_iff {Y : Type*} [Group Y] (c : Cocycle Y) :
    exceptional (cohomClass c) ↔ 0 < Module.finrank Bit (cupAnn c) ∨ epsilon c=1 := by
  rw [exceptional,annRank_cohomClass,bockHit_iff]
private theorem union_count {A X : Type*} [Finite A] [Finite X] (P : A→X→Prop) {q N : ℕ}
    (h : ∀a,Nat.card {x : X // P a x}*q ≤ N) :
    Nat.card {x : X // ∃a,P a x}*q ≤ Nat.card A*N := by
  classical
  letI := Fintype.ofFinite A
  let S := {x : X // ∃a,P a x}
  let T := (a : A) × {x : X // P a x}
  let emb (x : S) : T := ⟨x.property.choose,⟨x.val,x.property.choose_spec⟩⟩
  have hi : Function.Injective emb := fun _ _ he=>Subtype.ext (congrArg (fun t : T=>t.2.val) he)
  have hb := Nat.mul_le_mul_right q (Nat.card_le_card_of_injective emb hi)
  change Nat.card S*q ≤ Nat.card T*q at hb
  apply hb.trans
  dsimp only [T]
  rw [Nat.card_sigma,Finset.sum_mul]
  simpa [←Nat.card_eq_fintype_card] using Finset.sum_le_sum (s:=Finset.univ) (fun (a : A) _=>h a)
private theorem card_union {X : Type*} [Finite X] (P Q : X→Prop) :
    Nat.card {x : X // P x ∨ Q x}≤Nat.card {x : X // P x}+Nat.card {x : X // Q x} := by
  classical
  let T := {x : X // P x} ⊕ {x : X // Q x}
  let m (x : {x : X // P x ∨ Q x}) : T :=
    if h : P x.val then .inl ⟨x.val,h⟩ else .inr ⟨x.val,x.property.resolve_left h⟩
  let g := Sum.elim (Subtype.val : {x : X // P x}→X) (Subtype.val : {x : X // Q x}→X)
  have id (x : {x : X // P x ∨ Q x}) : g (m x)=x.val := by dsimp [m];split <;> rfl
  rw [←Nat.card_sum]
  exact Nat.card_le_card_of_injective m (fun x y he=>Subtype.ext ((id x).symm.trans ((congrArg g he).trans (id y))))
theorem su_xia_5_5_affine {Y : Type} [Group Y] [Finite Y] {d n : ℕ}
    (hY : Nat.card Y=2^(d+n)) (f : Y→*Vectors d) (hf : Function.Surjective f)
    (hΦ : f.ker ≤ frattini Y) (hd : 1 ≤ d) (z : H₂ Y) :
    Nat.card {x : LinearMap.range (inflate₂ f) // exceptional (z+x.val)}*2^(d*(d-1)/2) ≤
      Nat.card (LinearMap.range (inflate₂ f))*2^(d+1+(d*n+(d*(d-1)/2+d)-r₂ Y)) := by
  classical
  letI : Finite (H₂ Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  obtain ⟨bound,rank⟩ := inflation_tower (vectors_card d) n hY f hf hΦ
  rw [vectors_char_rank,elementary_r₂,Nat.mul_comm n d] at bound
  let L := LinearMap.range (inflate₂ f)
  let K := d*n+(d*(d-1)/2+d)-r₂ Y
  let D := d*(d-1)/2
  have hk : Module.finrank Bit (LinearMap.ker (inflate₃ f)) ≤ K := by dsimp [K];omega
  have inj : Function.Injective (characterPull f) := by
    intro a b he; apply Subtype.ext;funext x;obtain ⟨y,rfl⟩ := hf x
    exact congrArg (fun c : characters Y=>c.val y) he
  have sur := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rank.symm).1 inj
  let B (x : L) := bockHit (z+x.val)
  let A (x : L) := 0 < annRank (z+x.val)
  let P (a : characters Y) (x : L) := (bockH Y-cupClass a) (z+x.val)=0
  have HB := union_count P (q:=2^D) (N:=Nat.card L*2^K) (fun a=>by
    obtain ⟨b,rfl⟩ := sur a
    exact fixed_bock_density f b z hk)
  have cardCh : Nat.card (characters Y)=2^d := by
    rw [Module.natCard_eq_pow_finrank (K:=Bit),Nat.card_zmod,←vectors_char_rank d,←rank]
  rw [cardCh] at HB
  change Nat.card {x : L // B x}*2^D ≤ 2^d*(Nat.card L*2^K) at HB
  have HA := cup_union_density hY f hf hΦ hd z
  change Nat.card {x : L // A x}*2^(D+d) ≤ (2^d-1)*(Nat.card L*2^K) at HA
  have cup : Nat.card {x : L // A x}*2^D ≤ 2^d*(Nat.card L*2^K) :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right D d))).trans
      (HA.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)))
  have hu := Nat.mul_le_mul_right (2^D) (card_union A B)
  calc
    _ ≤ _ := hu
    _ = _ := Nat.add_mul ..
    _ ≤ _ := Nat.add_le_add cup HB
    _ = Nat.card L*2^(d+1+K) := by rw [pow_add,pow_succ];ring
theorem su_xia_5_5_allowable {Y : Type} [Group Y] [Finite Y] {d n : ℕ}
    (hY : Nat.card Y=2^(d+n)) (f : Y→*Vectors d) (hf : Function.Surjective f)
    (hΦ : f.ker ≤ frattini Y) (hd : 1 ≤ d) :
    Nat.card {x : H₂ Y // x∉LinearMap.range (inflate₂ f) ∧ exceptional x}*2^(d*(d-1)/2) ≤
      Nat.card {x : H₂ Y // x∉LinearMap.range (inflate₂ f)}*2^(d+1+(d*n+(d*(d-1)/2+d)-r₂ Y)) := by
  letI : Finite (H₂ Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  exact admissible_density_of_affine _ exceptional _ _ (su_xia_5_5_affine hY f hf hΦ hd)
end BinaryFactor.Elementary
end
section
namespace Erdos1160.DeepJacobi
abbrev Bit := ZMod 2
variable {q n s : ℕ}
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {G : Type*} [Group G]
abbrev Second (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries 1
def secondBracket (x y : G) : Second G :=
  ⟨⁅x,y⁆,Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
abbrev C₂ := Multiplicative Bit
variable {E Q : Type*} [Group E] [Group Q]
end Erdos1160.DeepJacobi
end
section
namespace ThirdLowerCentral
theorem order_two_central {G : Type*} [Group G] (K : Subgroup G) [hn : K.Normal]
    (hc : Nat.card K = 2) : K ≤ Subgroup.center G := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  by_cases h : x=1
  · simp [h]
  let a : K := ⟨x,hx⟩
  let b : K := ⟨y*x*y⁻¹,hn.conj_mem _ hx y⟩
  have ha : a ≠ 1 := fun e => h (congrArg Subtype.val e)
  have hb : b ≠ 1 := by
    intro h'
    have he : y*x*y⁻¹=1 := congrArg Subtype.val h'
    have he' : (y*x*y⁻¹)*y = y := by rw [he, one_mul]
    exact h (by simpa using he')
  have hab := (Nat.card_eq_two_iff' (1 : K)).mp hc
  have eq : b=a := hab.unique hb ha
  have hh : y*x*y⁻¹=x := congrArg Subtype.val eq
  simpa using congrArg (· * y) hh
end ThirdLowerCentral
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace CentralKernelCount
open CategoryTheory Erdos1160Growth.LowerTriangularUpper
theorem squareCore_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
    (squareCore G).map f = squareCore H := by
  rw [squareCore,squareCore,MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_,⟨g,rfl⟩,rfl⟩
    exact ⟨f g,(f.map_mul ..).symm⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨x,rfl⟩ := hf g
    exact ⟨x*x,⟨x,rfl⟩,f.map_mul ..⟩
end CentralKernelCount
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
open Erdos1160Growth.LowerTriangularUpper CentralLifts
def binaryThird (G : Type*) [Group G] : Subgroup G :=
  Subgroup.closure (Set.range (fun x : squareCore G => x.val*x.val) ∪
    Set.range (fun z : squareCore G × G => ⁅z.1.val,z.2⁆))
lemma binaryThird_map {G H : Type*} [Group G] [Group H] (q : G →* H) (hq : Function.Surjective q) :
    (binaryThird G).map q ≤ binaryThird H := by
  rw [binaryThird,MonoidHom.map_closure,Subgroup.closure_le]
  have h (u : squareCore G) : q u.val ∈ squareCore H :=
    (CentralKernelCount.squareCore_map q hq).le (show q u.val ∈ (squareCore G).map q from ⟨_,u.property,rfl⟩)
  rintro _ ⟨_,(⟨u,rfl⟩|⟨⟨u,x⟩,rfl⟩),rfl⟩
  · rw [map_mul]
    exact Subgroup.subset_closure (.inl ⟨⟨q u.val,h u⟩,rfl⟩)
  · rw [map_commutatorElement]
    exact Subgroup.subset_closure (.inr ⟨(⟨q u.val,h u⟩,q x),rfl⟩)
instance {G : Type*} [Group G] : (binaryThird G).Characteristic :=
  Subgroup.characteristic_iff_map_le.mpr fun e => binaryThird_map e.toMonoidHom e.surjective
lemma binaryThird_eq_bot {G : Type*} [Group G] [Finite G] {m : ℕ} (hG : Nat.card G=2^m)
    (hc : frattini G ≤ Subgroup.center G) (hs : ∀u:frattini G,u*u=1) : binaryThird G=⊥ := by
  apply eq_bot_iff.mpr
  rw [binaryThird,Subgroup.closure_le]
  have hΦ := frattini_eq_squareCore hG
  rintro _ (⟨v,rfl⟩|⟨⟨v,x⟩,rfl⟩)
  · let w : frattini G := ⟨v.val,hΦ.ge v.property⟩
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hs w))
  · exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hc (hΦ.ge v.property)) x).symm)
variable {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q] {m : ℕ}
omit [Finite Q] in
theorem one_step_factor (hQ : Nat.card Q=2^m) (j : ℕ) (hG : Nat.card G=2^(m+(j+1)))
    (f : G →* Q) (hf : Function.Surjective f) :
    ∃ (Y : FiniteGrp.{0}) (q : G →* Y) (k : Y →* Q), Function.Surjective q ∧
      Function.Surjective k ∧ k.comp q=f ∧ Nat.card Y=2^(m+1) := by
  induction j generalizing G with
  | zero => exact ⟨FiniteGrp.of G,MonoidHom.id G,f,Function.surjective_id,hf,rfl,hG⟩
  | succ j ih =>
    have hcard := ker_card_of_epi Nat.prime_two hG hQ f hf
    obtain ⟨u,hu,hz,ho⟩ := central_prime_in_normal Nat.prime_two (IsPGroup.of_card hG) f.ker
      (hcard ▸ dvd_pow_self 2 (Nat.succ_ne_zero _))
    let N := Subgroup.zpowers u
    let _ : N.Normal := normal_zpowers_of_central u hz
    let π := QuotientGroup.mk' N
    let F := QuotientGroup.lift N f (Subgroup.zpowers_le.mpr hu)
    have ontoF : Function.Surjective F := fun y => by
      obtain ⟨x,rfl⟩ := hf y
      exact ⟨π x,rfl⟩
    obtain ⟨Y,q,k,hq,hk,he,hY⟩ := ih (card_quotient_prime (by decide : 0 < 2) ho (k := m+(j+1)) hG) F ontoF
    exact ⟨Y,q.comp π,k,hq.comp (QuotientGroup.mk'_surjective N),hk,
      by rw [←MonoidHom.comp_assoc,he];rfl,hY⟩
omit [Finite G] [Finite Q] in
lemma kernel_image {Y : Type*} [Group Y] (q : G →* Y) (hq : Function.Surjective q)
    (k : Y →* Q) (f : G →* Q) (he : k.comp q=f) : k.ker ≤ f.ker.map q := by
  intro y hy
  obtain ⟨x,rfl⟩ := hq y
  exact ⟨x,he ▸ hy,rfl⟩
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi (C₂ one_step_factor)
variable {F Q : Type} [Group F] [Group Q]
def conjugateRelation (π : F →* Q) (g : F) (r : π.ker) : π.ker :=
  ⟨g*r.val*g⁻¹,(inferInstance : π.ker.Normal).conj_mem _ r.property _⟩
def RelCharacters (π : F →* Q) : Subgroup (π.ker →* C₂) where
  carrier := {chi | ∀g r,chi (conjugateRelation π g r)=chi r}
  one_mem' := fun _ _ => rfl
  mul_mem' := by intro a b ha hb g r; change a _ * b _ = a r * b r; rw [ha g r,hb g r]
  inv_mem' := by intro a ha g r; change (a _)⁻¹ = (a r)⁻¹; rw [ha g r]
instance {π : F →* Q} [Group.FG F] [Finite Q] : Finite (RelCharacters π) := by
  have hf : Group.FG π.ker := inferInstance
  obtain ⟨ι,_,f,hf⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp hf
  let C (a : RelCharacters π) (i : ι) : C₂ := a.val (f (FreeGroup.of i))
  apply Finite.of_injective C
  intro a b he
  apply Subtype.ext
  have h : a.val.comp f=b.val.comp f := FreeGroup.ext_hom _ _ (fun i => congrFun he i)
  apply MonoidHom.ext
  intro r
  obtain ⟨v,rfl⟩ := hf r
  exact DFunLike.congr_fun h v
instance (π : F →* Q) : Module (ZMod 2) (Additive (RelCharacters π)) :=
  AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    apply Subtype.ext
    apply MonoidHom.ext
    intro r
    change x.toMul.val r * x.toMul.val r=1
    exact (show ∀v : C₂,v*v=1 by decide) _)
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
variable {d : ℕ} {Q : Type} [Group Q]
lemma derived_le_squares (U : Type*) [Group U] : Second U ≤ squareCore U := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  have sq (z : U) : z*z∈squareCore U := Subgroup.subset_closure ⟨z,rfl⟩
  have he : ⁅x,y⁆=((x*x)*((x⁻¹*y)*(x⁻¹*y)))*(y⁻¹*y⁻¹) := by rw [commutatorElement_def];group
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (sq x) (sq (x⁻¹*y))) (sq y⁻¹)
lemma third_quot_squares (U : Type*) [Group U] :
    let Y := U ⧸ binaryThird U
    squareCore Y ≤ Subgroup.center Y ∧ ∀v:squareCore Y,v*v=1 := by
  dsimp only
  let π := QuotientGroup.mk' (binaryThird U)
  have hπ := QuotientGroup.mk'_surjective (binaryThird U)
  have lift (v : squareCore (U ⧸ binaryThird U)) : ∃u:squareCore U, π u.val=v.val := by
    have h : v.val ∈ (squareCore U).map π := (CentralKernelCount.squareCore_map π hπ).ge v.property
    obtain ⟨y,hy,he⟩ := h
    exact ⟨⟨y,hy⟩,he⟩
  constructor
  · intro v hv
    obtain ⟨u,hu⟩ := lift ⟨v,hv⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨w,rfl⟩ := hπ y
    change π w * v = v * π w
    rw [←show π u.val=v from hu]
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure (.inr ⟨(u,w),rfl⟩))
  · intro v
    obtain ⟨u,hu⟩ := lift v
    apply Subtype.ext
    change v.val*v.val=1
    rw [←hu,←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure (.inl ⟨u,rfl⟩))
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
variable {d m : ℕ} {Q : Type} [Group Q] [Finite Q]
lemma binaryThird_map_eq {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
    (binaryThird G).map f=binaryThird H := by
  apply le_antisymm (binaryThird_map f hf)
  have lift (w : squareCore H) : ∃u:squareCore G,f u.val=w.val := by
    obtain ⟨x,hx,e⟩ := (CentralKernelCount.squareCore_map f hf).ge w.property
    exact ⟨⟨x,hx⟩,e⟩
  apply (Subgroup.closure_le _).mpr
  rintro _ (⟨u,rfl⟩|⟨⟨u,x⟩,rfl⟩)
  · obtain ⟨w,hw⟩ := lift u
    exact ⟨w.val*w.val,Subgroup.subset_closure (.inl ⟨w,rfl⟩),by rw [map_mul,hw]⟩
  · obtain ⟨v,rfl⟩ := hf x
    obtain ⟨w,hw⟩ := lift u
    exact ⟨⁅w.val,v⁆,Subgroup.subset_closure (.inr ⟨(w,v),rfl⟩),by rw [map_commutatorElement,hw]⟩
lemma binaryThird_le_squares (Y : Type*) [Group Y] : binaryThird Y ≤ squareCore Y := by
  apply (Subgroup.closure_le _).mpr
  rintro _ (⟨u,rfl⟩|⟨⟨u,x⟩,rfl⟩)
  · exact (squareCore Y).mul_mem u.property u.property
  · exact derived_le_squares Y (secondBracket u.val x).property
end Erdos1160.CentralLifts.Survival
end
section
namespace BinaryFactor
open CategoryTheory
theorem twist_classifies {E G : Type*} [Group E] [Group G] (F : E →* G) (onto : Function.Surjective F)
    (hc : F.ker ≤ Subgroup.center E) (ho : Nat.card F.ker=2) :
    ∃ x : H₂ G, ∃ e : E ≃* (classCocycle x).Twist, ∀ g, (classCocycle x).projTwist (e g)=F g := by
  obtain ⟨c,i,hi⟩ := exists_twist_over F onto hc ho
  obtain ⟨x,j,hj⟩ := exists_class_equiv c
  exact ⟨x,i.trans j,fun g => (hj (i g)).trans (hi g)⟩
end BinaryFactor
end
section
namespace Erdos1160.DescendantTree
def leaves {X : Type*} (ch : ℕ → X → Finset X) : ℕ → ℕ → X → ℕ
  | 0, _, _ => 1
  | k+1, i, x => ∑ y ∈ ch i x, leaves ch k (i+1) y
end Erdos1160.DescendantTree
end
section
namespace Erdos1160.DescendantTree.Actual
open CategoryTheory BinaryFactor BinaryFactor.Cocycle BinaryFactor.Elementary
open Erdos1160.DeepJacobi Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival
structure Vertex (Q : Type) [Group Q] (m : ℕ) where
  group : FiniteGrp.{0}
  overData : group →* Q
  onto : Function.Surjective overData
  deep : overData.ker ≤ binaryThird group
  depth : ℕ
  size : Nat.card group=2^(m+depth)
  gain : ℕ
  exceptional : Bool
variable {Q : Type} [Group Q] {m : ℕ}
def initial [Finite Q] (hQ : Nat.card Q=2^m) : Vertex Q m :=
  ⟨FiniteGrp.of Q,MonoidHom.id Q,Function.surjective_id,by
    intro g hg; exact (show g=1 from hg) ▸ (binaryThird Q).one_mem,0,hQ,0,false⟩
private theorem deep_comp {A B : Type} [Group A] [Group B] (g : A→*B) (hg : Function.Surjective g)
    (hk : g.ker ≤ binaryThird A) (k : B→*Q) (hk' : k.ker ≤ binaryThird B) :
    (k.comp g).ker ≤ binaryThird A := by
  have eq := Subgroup.comap_map_eq_self hk
  rw [binaryThird_map_eq g hg] at eq
  exact (Subgroup.comap_mono (f:=g) hk').trans eq.le
abbrev Allowed (x : Vertex Q m) :=
  {z : H₂ x.group // (classCocycle z).projTwist.ker ≤ binaryThird (classCocycle z).Twist}
noncomputable def next (x : Vertex Q m) (a : Allowed x) : Vertex Q m := by
  classical
  let c := classCocycle a.val
  refine ⟨FiniteGrp.of c.Twist,x.overData.comp c.projTwist,x.onto.comp c.projTwist_onto,
    deep_comp c.projTwist c.projTwist_onto a.property x.overData x.deep,x.depth+1,?_,
    annRank a.val,decide (Elementary.exceptional a.val)⟩
  rw [show Nat.card (FiniteGrp.of c.Twist)=Nat.card c.Twist from rfl,c.card_twist,x.size,
    ←Nat.add_assoc,pow_succ,Nat.mul_comm]
noncomputable def children (i : ℕ) (x : Vertex Q m) : Finset (Vertex Q m) := by
  classical
  letI : Finite (H₂ x.group) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  letI := Fintype.ofFinite (Allowed x)
  exact if i=x.depth then Finset.univ.image (next x) else ∅
theorem mem_children {i : ℕ} {x y : Vertex Q m} : y∈children i x ↔ i=x.depth ∧ ∃a,y=next x a := by
  classical
  letI : Finite (H₂ x.group) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  letI := Fintype.ofFinite (Allowed x)
  by_cases h : i=x.depth
  · simp [children,h,eq_comm]
  · simp [children,h]
noncomputable def terminals {X T : Type*} [DecidableEq T] (labels : X→T) (ch : ℕ→X→Finset X) :
    ℕ→ℕ→X→Finset T
  | 0,_,x => {labels x}
  | k+1,i,x => (ch i x).biUnion (fun y=>terminals labels ch k (i+1) y)
theorem card_terminals {X T : Type*} [DecidableEq T] (labels : X→T) (ch : ℕ→X→Finset X)
    (t i : ℕ) (x : X) : (terminals labels ch t i x).card ≤ leaves ch t i x := by
  induction t generalizing i x with
  | zero => simp [terminals,leaves]
  | succ t ih =>
    exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun y _=>ih (i+1) y))
abbrev IsoClass := Quotient (isIsomorphicSetoid FiniteGrp.{0})
def label (x : Vertex Q m) : IsoClass := Quotient.mk _ x.group
theorem covered [DecidableEq IsoClass] {G : Type} [Group G] [Finite G] (t : ℕ) (x : Vertex Q m)
    (hG : Nat.card G=2^(m+x.depth+t)) (f : G→*x.group) (hf : Function.Surjective f)
    (hk : f.ker ≤ binaryThird G) :
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (FiniteGrp.of G) ∈ terminals label children t x.depth x := by
  induction t generalizing G x with
  | zero =>
    let e := MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).2 ⟨hf,hG.trans x.size.symm⟩)
    apply Finset.mem_singleton.mpr
    exact Quotient.sound ⟨InducedCategory.isoMk (F:=FiniteGrp.toGrp) e.toGrpIso⟩
  | succ j ih =>
    obtain ⟨Y,q,k,hq,hk',he,hY⟩ := one_step_factor x.size j hG f hf
    have hc : Nat.card k.ker=2 := by simpa using ker_card_of_epi Nat.prime_two hY x.size k hk'
    have hdeep : k.ker ≤ binaryThird Y :=
      (kernel_image q hq k f he).trans ((Subgroup.map_mono (f:=q) hk).trans (binaryThird_map q hq))
    obtain ⟨z,e,hev⟩ := twist_classifies k hk' (ThirdLowerCentral.order_two_central _ hc) hc
    let c := classCocycle z
    have deep : c.projTwist.ker ≤ binaryThird c.Twist := by
      intro a ha
      obtain ⟨b,rfl⟩ := e.surjective a
      have hb : k b=1 := (hev b).symm.trans ha
      exact binaryThird_map e.toMonoidHom e.surjective ⟨b,hdeep hb,rfl⟩
    let a : Allowed x := ⟨z,deep⟩
    let y := next x a
    let g := e.toMonoidHom.comp q
    have hg : g.ker ≤ binaryThird G := by
      intro b hb;apply hk
      change f b=1
      rw [←he,MonoidHom.comp_apply]
      have hz : q b=1 := e.injective ((show e (q b)=1 from hb).trans e.map_one.symm)
      rw [hz,map_one]
    have hgcard : Nat.card G=2^(m+y.depth+j) := by
      change Nat.card G=2^(m+(x.depth+1)+j)
      convert hG using 2 <;> omega
    have hnext := ih y hgcard g (e.surjective.comp hq) hg
    exact Finset.mem_biUnion.mpr ⟨y,mem_children.mpr ⟨rfl,⟨a,rfl⟩⟩,hnext⟩
def descendants (Q : Type) [Group Q] (m t : ℕ) : Set IsoClass :=
  {v | ∃G : FiniteGrp.{0}, Nat.card G=2^(m+t) ∧
    (∃ f : G→*Q,Function.Surjective f ∧ f.ker ≤ binaryThird G) ∧ Quotient.mk _ G=v}
theorem count_le_leaves [Finite Q] (hQ : Nat.card Q=2^m) (t : ℕ) :
    (descendants Q m t).ncard ≤ leaves children t 0 (initial hQ) := by
  classical
  let v := initial hQ
  have sub : descendants Q m t ⊆ ↑(terminals label children t 0 v) := by
    rintro _ ⟨G,hG,⟨f,hf,hk⟩,rfl⟩
    exact covered t v hG f hf hk
  exact ((Set.ncard_le_ncard sub (Finset.finite_toSet _)).trans_eq (Set.ncard_coe_finset _)).trans
    (card_terminals label children t 0 v)
end Erdos1160.DescendantTree.Actual
end
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi (C₂ binaryThird)
open Erdos1160Growth.LowerTriangularUpper
open BinaryFactor
open scoped commutatorElement
variable {Y V : Type} [Group Y] [Group V] (p : Y →* V) (hk : p.ker = squareCore Y)
include hk in
lemma binaryThird_killed_by_invariant (a : RelCharacters p) :
    binaryThird Y ≤ a.val.ker.map p.ker.subtype := by
  apply (Subgroup.closure_le _).mpr
  rintro _ (⟨u,rfl⟩|⟨⟨u,x⟩,rfl⟩)
  · let w : p.ker := ⟨u.val,by rw [hk];exact u.property⟩
    refine ⟨w*w,?_,rfl⟩
    change a.val (w*w)=1
    rw [map_mul]
    exact (show ∀ t : Erdos1160.DeepJacobi.C₂,t*t=1 by decide) _
  · let w : p.ker := ⟨u.val,by rw [hk];exact u.property⟩
    refine ⟨w*conjugateRelation p x w⁻¹,?_,?_⟩
    · change a.val (_*_)=1
      rw [map_mul,a.property,map_inv,mul_inv_cancel]
    · change u.val*(x*u.val⁻¹*x⁻¹)=⁅u.val,x⁆
      rw [commutatorElement_def];group
noncomputable def rootKernelRestriction :
    (squareCore (Y ⧸ binaryThird Y) →* Erdos1160.DeepJacobi.C₂) ≃ RelCharacters p := by
  let q := QuotientGroup.mk' (binaryThird Y)
  let W := squareCore (Y ⧸ binaryThird Y)
  have hq := QuotientGroup.mk'_surjective (binaryThird Y)
  have hW : (squareCore Y).map q=W := CentralKernelCount.squareCore_map q hq
  let f := (q.comp p.ker.subtype).codRestrict W (fun w => hW ▸ (show q w.val ∈ (squareCore Y).map q from ⟨w.val,hk ▸ w.property,rfl⟩))
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨w,hw,h⟩ := hW.ge z.property
    exact ⟨⟨w,hk ▸ hw⟩,Subtype.ext h⟩
  let g (c : W →* Erdos1160.DeepJacobi.C₂) : RelCharacters p := ⟨c.comp f,fun x w => by
    apply congrArg c
    apply Subtype.ext
    change q (x*w.val*x⁻¹)=q w.val
    have he : q x*q w.val=q w.val*q x := Subgroup.mem_center_iff.mp ((third_quot_squares Y).1 (f w).property) (q x)
    rw [map_mul,map_mul,map_inv,he,mul_inv_cancel_right]⟩
  apply Equiv.ofBijective g
  constructor
  · intro u v he
    apply MonoidHom.ext
    intro x
    obtain ⟨y,rfl⟩ := hf x
    exact congrArg (fun a : RelCharacters p => a.val y) he
  · intro a
    have hN : f.ker ≤ a.val.ker := by
      intro w hw
      have h : q w.val=1 := congrArg Subtype.val (show f w=1 from hw)
      obtain ⟨v,hv,e⟩ := binaryThird_killed_by_invariant p hk a ((QuotientGroup.eq_one_iff _).mp h)
      exact (show v=w from Subtype.ext e) ▸ hv
    exact ⟨f.liftOfSurjective hf ⟨a.val,hN⟩,Subtype.ext (f.liftOfRightInverse_comp _ _ _)⟩
lemma elementary_character_card {A : Type} [Group A] [Finite A] {s : ℕ}
    (ha : ∀x:A,x*x=1) (hs : Nat.card A=2^s) :
    Nat.card (A →* Erdos1160.DeepJacobi.C₂)=2^s := by
  classical
  obtain ⟨e⟩ := exist_elementary_coords ha hs
  let h : (Elementary.Vectors s →* Erdos1160.DeepJacobi.C₂) ≃ characters (Elementary.Vectors s) := {
    toFun f := ⟨fun x=>(f x).toAdd,fun x y=>f.map_mul x y⟩
    invFun a := { toFun := fun x=>.ofAdd (a.val x)
                  map_one' := by change a.val 1=0;simpa using a.property 1 1
                  map_mul' := a.property }
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr ((e.monoidHomCongrLeftEquiv.trans h).trans (Elementary.characterDual s).toEquiv)]
  let _ : Finite (Module.Dual Bit (Erdos1160Growth.LowerTriangularUpper.V s)) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let _ := Fintype.ofFinite (Module.Dual Bit (Erdos1160Growth.LowerTriangularUpper.V s))
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=Bit),Subspace.dual_finrank_eq,Module.finrank_fin_fun,ZMod.card]
include hk in
theorem frattini_relchar_rank {s : ℕ} [Finite Y] [Finite V]
    (hs : Nat.card (squareCore (Y ⧸ binaryThird Y))=2^s) :
    Module.finrank Bit (Additive (RelCharacters p))=s := by
  classical
  let _ := Fintype.ofFinite (Additive (RelCharacters p))
  have h : Nat.card (Additive (RelCharacters p))=2^s :=
    (Nat.card_congr (rootKernelRestriction p hk).symm).trans
      (elementary_character_card (third_quot_squares Y).2 hs)
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=Bit),ZMod.card] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) h
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.CentralLifts.Survival
open BinaryFactor
open Erdos1160.DeepJacobi (C₂)
variable {Y V : Type} [Group Y] [Group V] (p : Y →* V)
structure NormSection where
  s : V → Y
  one : s 1=1
  right : ∀x,p (s x)=x
noncomputable def normSection (hp : Function.Surjective p) : NormSection p := by
  classical
  let s (x : V) : Y := if x=1 then 1 else (hp x).choose
  refine ⟨s,if_pos rfl,fun x => ?_⟩
  dsimp only [s]
  split
  · rename_i hx;rw [hx,map_one]
  · exact (hp x).choose_spec
variable {p} (S : NormSection p)
def residual (y : Y) : p.ker :=
  ⟨y*(S.s (p y))⁻¹,by change p (_*_)=1;rw [map_mul,map_inv,S.right,mul_inv_cancel]⟩
def defect (x y : V) : p.ker :=
  ⟨S.s x*S.s y*(S.s (x*y))⁻¹,by change p (_*_)=1;rw [map_mul,map_mul,map_inv,S.right,S.right,S.right,mul_inv_cancel]⟩
variable (a : Additive (RelCharacters p))
def splitFunction (y : Y) : Bit := (a.toMul.val (residual S y)).toAdd
def splitFactor (x y : V) : Bit := (a.toMul.val (defect S x y)).toAdd
lemma split_function_one : splitFunction S a 1=0 := by
  have h : residual S 1=1 := Subtype.ext (by simp [residual,S.one])
  simp [splitFunction,h]
lemma split_function_kernel (w : p.ker) : splitFunction S a w.val=(a.toMul.val w).toAdd := by
  have h : residual S w.val=w := Subtype.ext (by simp [residual,show p w.val=1 from w.property,S.one])
  simp [splitFunction,h]
lemma split_product (x y : Y) :
    splitFunction S a (x*y)=splitFunction S a x+splitFunction S a y+splitFactor S a (p x) (p y) := by
  have eq : residual S (x*y)=residual S x * conjugateRelation p (S.s (p x)) (residual S y) *
      defect S (p x) (p y) := by
    apply Subtype.ext
    change x*y*(S.s (p (x*y)))⁻¹=(x*(S.s (p x))⁻¹*(S.s (p x)*(y*(S.s (p y))⁻¹)*(S.s (p x))⁻¹))*
      (S.s (p x)*S.s (p y)*(S.s (p x*p y))⁻¹)
    rw [map_mul];group
  rw [splitFunction,eq,a.toMul.val.map_mul,a.toMul.val.map_mul,a.toMul.property]
  rfl
def transgressCycle : cycles₂ V :=
  ⟨⟨splitFactor S a,fun x => by
      have e : defect S 1 x=1 := Subtype.ext (by simp [defect,S.one])
      simp [splitFactor,e],
    fun x => by
      have e : defect S x 1=1 := Subtype.ext (by simp [defect,S.one])
      simp [splitFactor,e]⟩,by
    funext x y z
    change d₂ (splitFactor S a) x y z=0
    have h := congrArg (splitFunction S a) (mul_assoc (S.s x) (S.s y) (S.s z))
    simp only [split_product,map_mul,S.right] at h
    dsimp only [d₂]
    linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) h⟩
noncomputable def transgression : Additive (RelCharacters p) →+ H₂ V where
  toFun a := Submodule.Quotient.mk (transgressCycle S a)
  map_zero' := congrArg (Submodule.Quotient.mk (p:=LinearMap.range (boundaryLinear V))) (show transgressCycle S 0=0 by rfl)
  map_add' a b := congrArg (Submodule.Quotient.mk (p:=LinearMap.range (boundaryLinear V))) (show transgressCycle S (a+b)=transgressCycle S a+transgressCycle S b by rfl)
lemma transgression_in_kernel (a : Additive (RelCharacters p)) : transgression S a ∈ LinearMap.ker (inflate₂ p) := by
  change (Submodule.Quotient.mk (cyclePull p (transgressCycle S a)) : H₂ Y)=0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨⟨splitFunction S a,split_function_one S a⟩,?_⟩
  apply Subtype.ext;apply Subtype.ext;funext x y
  change splitFunction S a y+splitFunction S a (x*y)+splitFunction S a x=splitFactor S a (p x) (p y)
  rw [split_product]
  ring_nf <;> simp [show (2:Bit)=0 by decide]
lemma transgression_injective
    (hmin : ∀ χ : Y→*Erdos1160.DeepJacobi.C₂,p.ker ≤ χ.ker) : Function.Injective (transgression S) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨t,ht⟩ := (Submodule.Quotient.mk_eq_zero _).mp (show (Submodule.Quotient.mk (transgressCycle S a) : H₂ V)=0 from ha)
  have ht' (x y : V) : t.val y+t.val (x*y)+t.val x=splitFactor S a x y :=
    congrArg (fun z : cycles₂ V => z.val.val x y) ht
  let χ : Y →* Erdos1160.DeepJacobi.C₂ := {
    toFun y := .ofAdd (splitFunction S a y+t.val (p y))
    map_one' := by change splitFunction S a 1+t.val (p 1)=0;rw [map_one,split_function_one,zero_add];exact t.property
    map_mul' x y := by
      change splitFunction S a (x*y)+t.val (p (x*y))=(splitFunction S a x+t.val (p x))+(splitFunction S a y+t.val (p y))
      rw [split_product,map_mul,←ht']
      ring_nf <;> simp [show (2:Bit)=0 by decide] }
  apply Subtype.ext;apply MonoidHom.ext;intro w
  have hk := hmin χ w.property
  change splitFunction S a w.val+t.val (p w.val)=0 at hk
  rw [split_function_kernel,show p w.val=1 from w.property,show t.val 1=0 from t.property,add_zero] at hk
  exact hk
lemma transgression_range (x : H₂ V) (hx : x ∈ LinearMap.ker (inflate₂ p)) :
    ∃ a : Additive (RelCharacters p),transgression S a=x := by
  obtain ⟨z,rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear V)) x
  obtain ⟨t,ht⟩ := (Submodule.Quotient.mk_eq_zero _).mp (show (Submodule.Quotient.mk (cyclePull p z) : H₂ Y)=0 from hx)
  let c := ofCycle z
  have dt (u v : Y) : t.val v+t.val (u*v)+t.val u=c.val (p u) (p v) :=
    congrArg (fun z : cycles₂ Y => z.val.val u v) ht
  have left (v : Y) (w : p.ker) : t.val (w.val*v)=t.val w.val+t.val v := by
    have h := dt w.val v
    rw [show p w.val=1 from w.property,c.norm_left] at h
    linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) h
  have right (v : Y) (w : p.ker) : t.val (v*w.val)=t.val v+t.val w.val := by
    have h := dt v w.val
    rw [show p w.val=1 from w.property,c.norm_right] at h
    linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) h
  let χ : p.ker →* Erdos1160.DeepJacobi.C₂ := {
    toFun w := .ofAdd (t.val w.val)
    map_one' := t.property
    map_mul' w v := left v.val w }
  have ih (g : Y) (w : p.ker) : χ (conjugateRelation p g w)=χ w := by
    have h := left g (conjugateRelation p g w)
    change t.val (g*w.val*g⁻¹*g)=t.val (g*w.val*g⁻¹)+t.val g at h
    rw [inv_mul_cancel_right,right g w] at h
    change t.val (g*w.val*g⁻¹)=t.val w.val
    linear_combination -h
  let a := Additive.ofMul (⟨χ,ih⟩ : RelCharacters p)
  refine ⟨a,(Submodule.Quotient.eq _).mpr ?_⟩
  refine ⟨⟨fun v=>t.val (S.s v),by change t.val (S.s 1)=0;rw [S.one];exact t.property⟩,?_⟩
  apply Subtype.ext;apply Subtype.ext;funext u v
  have h := dt (S.s u) (S.s v)
  rw [S.right,S.right] at h
  have l := left (S.s (u*v)) (defect S u v)
  change t.val (S.s u*S.s v*(S.s (u*v))⁻¹*S.s (u*v))=t.val (defect S u v).val+t.val (S.s (u*v)) at l
  rw [inv_mul_cancel_right] at l
  change t.val (S.s v)+t.val (S.s (u*v))+t.val (S.s u)=t.val (defect S u v).val-c.val u v
  linear_combination (norm := (ring_nf <;> simp [show (2:Bit)=0 by decide])) h-l
noncomputable def inflationKernelEquiv (hp : Function.Surjective p)
    (hmin : ∀ χ : Y→*Erdos1160.DeepJacobi.C₂,p.ker ≤ χ.ker) :
    Additive (RelCharacters p) ≃ₗ[Bit] LinearMap.ker (inflate₂ p) := by
  let S := normSection p hp
  let f := ((transgression S).toZModLinearMap 2).codRestrict _ (transgression_in_kernel S)
  exact LinearEquiv.ofBijective f ⟨fun _ _ e => transgression_injective S hmin (congrArg Subtype.val e),
    fun y => by obtain ⟨a,ha⟩ := transgression_range S y.val y.property;exact ⟨a,Subtype.ext ha⟩⟩
end Erdos1160.CentralLifts.Survival
end
section
namespace OrbitUp
end OrbitUp
end
section
namespace Erdos1160.CentralLifts.Survival
open BinaryFactor Erdos1160Growth.LowerTriangularUpper
open Erdos1160.DeepJacobi (binaryThird)
lemma squareCore_in_char_kernel {Y : Type} [Group Y] (χ : Y→* Erdos1160.DeepJacobi.C₂) :
    squareCore Y≤χ.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨u,rfl⟩
  change χ (u*u)=1
  rw [map_mul]
  exact (show ∀v : Erdos1160.DeepJacobi.C₂,v*v=1 by decide) _
theorem allowable_dimension_general {Y V : Type} [Group Y] [Group V] [Finite Y] [Finite V]
    (p : Y→*V) (hp : Function.Surjective p) (hk : p.ker=squareCore Y) {s : ℕ}
    (hs : Nat.card (squareCore (Y ⧸ binaryThird Y))=2^s) :
    Module.finrank Bit (LinearMap.range (inflate₂ p))+s=r₂ V := by
  let e := inflationKernelEquiv hp (fun χ => hk ▸ squareCore_in_char_kernel χ)
  have h := e.finrank_eq
  rw [frattini_relchar_rank p hk hs] at h
  have hr := LinearMap.finrank_range_add_finrank_ker (inflate₂ p)
  rw [←h] at hr
  exact hr
theorem allowable_dimension {Y : Type} [Group Y] [Finite Y] {d s : ℕ}
    (p : Y→*Elementary.Vectors d) (hp : Function.Surjective p) (hk : p.ker=squareCore Y)
    (hs : Nat.card (squareCore (Y ⧸ binaryThird Y))=2^s) :
    Module.finrank Bit (LinearMap.range (inflate₂ p))+s=d*(d+1)/2 := by
  rw [allowable_dimension_general p hp hk hs,Elementary.elementary_r₂]
  have h := OrbitUp.twice_slots d
  dsimp only [OrbitUp.slotsN] at h
  have eq : d*(d+1)=d^2+d := by ring
  rw [eq,←h]
  omega
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.DescendantTree.Actual
open CategoryTheory BinaryFactor BinaryFactor.Cocycle BinaryFactor.Elementary
open Erdos1160.DeepJacobi (binaryThird binaryThird_map)
open Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival
open Erdos1160Growth.LowerTriangularUpper
variable {Q : Type} [Group Q] {m d s : ℕ}
theorem quotient_root (x : Vertex Q m) (hQ : binaryThird Q=⊥) :
    Nonempty ((x.group ⧸ binaryThird x.group) ≃* Q) := by
  have hb : binaryThird x.group ≤ x.overData.ker := by
    intro u hu
    have h : x.overData u∈binaryThird Q := binaryThird_map x.overData x.onto ⟨u,hu,rfl⟩
    rw [hQ] at h; exact h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm hb x.deep)).trans
    (QuotientGroup.quotientKerEquivOfSurjective x.overData x.onto)⟩
theorem root_width (x : Vertex Q m) (hQ : binaryThird Q=⊥) (hs : Nat.card (squareCore Q)=2^s) :
    Nat.card (squareCore (x.group ⧸ binaryThird x.group))=2^s := by
  obtain ⟨e⟩ := quotient_root x hQ
  have b := Nat.card_congr (e.subgroupMap (squareCore _)).toEquiv
  change Nat.card (squareCore _) = Nat.card ((squareCore _).map e.toMonoidHom) at b
  rw [CentralKernelCount.squareCore_map e.toMonoidHom e.surjective] at b
  exact b.trans hs
def toVectors (p : Q →* Vectors d) (x : Vertex Q m) := p.comp x.overData
theorem toVectors_ker (p : Q →* Vectors d) (hp : p.ker=squareCore Q) (x : Vertex Q m) :
    (toVectors p x).ker=squareCore x.group := by
  have eq := Subgroup.comap_map_eq_self (x.deep.trans (binaryThird_le_squares x.group))
  rwa [CentralKernelCount.squareCore_map x.overData x.onto,←hp] at eq
theorem actual_image_dimension (p : Q→*Vectors d) (hf : Function.Surjective p) (hp : p.ker=squareCore Q)
    (hQ : binaryThird Q=⊥) (hs : Nat.card (squareCore Q)=2^s) (x : Vertex Q m) :
    Module.finrank Bit (LinearMap.range (inflate₂ (toVectors p x)))+s=d*(d+1)/2 :=
  allowable_dimension (toVectors p x) (hf.comp x.onto) (toVectors_ker p hp x) (root_width x hQ hs)
instance finite_h₂ (G : Type*) [Group G] [Finite G] : Finite (H₂ G) :=
  Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
theorem filtered_card (i : ℕ) (x : Vertex Q m) (P : H₂ x.group→Prop) (test : Vertex Q m→Prop)
    [DecidablePred test] (h : ∀z : Allowed x,test (next x z)→P z.val) :
    ((children i x).filter test).card ≤ Nat.card {z : H₂ x.group // P z} := by
  classical
  let S := (children i x).filter test
  have witness (y : S) : ∃ a : Allowed x, y.val=next x a :=
    (mem_children.mp (Finset.mem_filter.mp y.property).1).2
  let a (y : S) := (witness y).choose
  have ha (y : S) : y.val=next x (a y) := (witness y).choose_spec
  let emb (y : S) : {z : H₂ x.group // P z} :=
    ⟨(a y).val,h _ ((ha y) ▸ (Finset.mem_filter.mp y.property).2)⟩
  have inj : Function.Injective emb := by
    intro y w eq
    have eq' : a y=a w := Subtype.ext (congrArg (fun z : {z : H₂ x.group // P z}=>z.val) eq)
    exact Subtype.ext ((ha y).trans ((congrArg (next x) eq').trans (ha w).symm))
  simpa only [Nat.card_eq_finsetCard,S] using Nat.card_le_card_of_injective emb inj
theorem child_card (i : ℕ) (x : Vertex Q m) : (children i x).card ≤ 2^(r₂ x.group) := by
  classical
  have h := filtered_card i x (fun _=>True) (fun _=>True) (fun _ _=>trivial)
  simpa [
    Module.natCard_eq_pow_finrank (K:=Bit) (V:=H₂ x.group),Nat.card_zmod,r₂] using h
theorem classCocycle_repr {G : Type*} [Group G] (z : H₂ G) : cohomClass (classCocycle z)=z :=
  (Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear G)) z).choose_spec
noncomputable def height (b i : ℕ) (x : Vertex Q m) := if i=x.depth then r₂ x.group-b else 0
theorem actual_step {b i : ℕ} {x y : Vertex Q m} (hy : y∈children i x) (hb : b < r₂ x.group)
    (hν : ∀a : Allowed x, a.val≠0) :
    height b (i+1) y ≤ height b i x+y.gain ∧
      (y.exceptional=false → height b (i+1) y+1 ≤ height b i x) := by
  classical
  obtain ⟨rfl,z,rfl⟩ := mem_children.mp hy
  let c := classCocycle z.val
  have hc := scalar_recurrences c (invisible_of_nonsplit _ ((classCocycle_repr z.val) ▸ hν z))
  have recu := hc.1
  rw [←annRank_cohomClass,classCocycle_repr] at recu
  have eb := epsilon_le_one c
  have hd : (next x z).depth=x.depth+1 := rfl
  simp only [height,hd,if_true]
  constructor
  · change r₂ c.Twist-b ≤ r₂ x.group-b+annRank z.val
    omega
  · intro hn
    have hnot : ¬Elementary.exceptional z.val := of_decide_eq_false hn
    rw [←classCocycle_repr z.val,exceptional_iff] at hnot
    change ¬(0 < Module.finrank Bit (cupAnn c) ∨ epsilon c=1) at hnot
    have hε : epsilon c=0 := by omega
    have hâ : Module.finrank Bit (cupAnn c)=0 := by omega
    have en := annRank_cohomClass c
    rw [classCocycle_repr] at en
    change r₂ c.Twist-b+1 ≤ r₂ x.group-b
    omega
end Erdos1160.DescendantTree.Actual
end
section
namespace Erdos1160.CentralLifts.Survival
open BinaryFactor BinaryFactor.Cocycle
open Erdos1160Growth.LowerTriangularUpper
open Erdos1160.DeepJacobi (binaryThird)
variable {Y V : Type} [Group Y] [Group V] (p : Y→*V) (c : Cocycle Y)
theorem range_iff_bit_lift : cohomClass c ∈ LinearMap.range (inflate₂ p) ↔
    ∃ b : Cocycle V, ∃ f : c.Twist →* b.Twist, b.projTwist.comp f=p.comp c.projTwist ∧
      f zbit=zbit := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨z,rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear V)) x
    let b := ofCycle z
    obtain ⟨t,ht⟩ := (Submodule.Quotient.eq _).mp (show (Submodule.Quotient.mk (cyclePull p z) : H₂ Y)=Submodule.Quotient.mk c.asCycle from hx)
    have dt (x y : Y) : t.val y+t.val (x*y)+t.val x=b.val (p x) (p y)-c.val x y :=
      congrArg (fun a : cycles₂ Y => a.val.val x y) ht
    let f : c.Twist →* b.Twist := {
      toFun v := (p v.1,v.2+t.val v.1)
      map_one' := Prod.ext p.map_one (by change 0+t.val 1=0;rw [zero_add];exact t.property)
      map_mul' x y := Prod.ext (p.map_mul x.1 y.1) (by
        change x.2+y.2+c.val x.1 y.1+t.val (x.1*y.1)=(x.2+t.val x.1)+(y.2+t.val y.1)+b.val (p x.1) (p y.1)
        linear_combination (norm := (ring_nf; simp [show (2:Bit)=0 by decide])) dt x.1 y.1) }
    exact ⟨b,f,rfl,Prod.ext p.map_one (by change 1+t.val 1=1;rw [show t.val 1=0 from t.property,add_zero])⟩
  · rintro ⟨b,f,hf,hb⟩
    have base_eq (v : c.Twist) : (f v).1=p v.1 := DFunLike.congr_fun hf v
    let mark (x : Y) : c.Twist := (x,0)
    let kernelBit : c.Twist := zbit
    let t (x : Y) := (f (mark x)).2
    have t0 : t 1=0 := congrArg (fun z : b.Twist => z.2) f.map_one
    have atBit (v : Y) (i : Bit) : (f ((v,i) : c.Twist)).2=t v+i := by
      rcases bit_cases i with rfl|rfl
      · exact (add_zero _).symm
      · have hz : ((v,1) : c.Twist)=mark v*kernelBit := by
          change (v,1)=c.prod (v,0) (1,1)
          simp [prod,c.norm_right]
        rw [hz,f.map_mul,show f kernelBit=zbit from hb]
        change (f (mark v)).2+1+b.val (f (mark v)).1 1=t v+1
        rw [b.norm_right,add_zero]
    refine ⟨cohomClass b,(Submodule.Quotient.eq _).mpr ?_⟩
    refine ⟨⟨t,t0⟩,?_⟩
    apply Subtype.ext;apply Subtype.ext;funext u v
    have h := congrArg (fun z : b.Twist=>z.2) (f.map_mul (mark u) (mark v))
    change (f ((u*v,0+0+c.val u v):c.Twist)).2=(f (mark u)).2+(f (mark v)).2+b.val (f (mark u)).1 (f (mark v)).1 at h
    rw [zero_add,zero_add,atBit,base_eq (mark u),base_eq (mark v)] at h
    change t (u*v)+c.val u v=t u+t v+b.val (p u) (p v) at h
    change t v+t (u*v)+t u=b.val (p u) (p v)-c.val u v
    linear_combination (norm := (ring_nf; simp [show (2:Bit)=0 by decide])) h
theorem binaryTwist_ker_square {X : Type} [Group X] (b : Cocycle X) (k : b.projTwist.ker) :
    k.val*k.val=1 := by
  rcases k with ⟨⟨x,i⟩,h⟩
  change x=1 at h
  subst x
  change b.prod (1,i) (1,i)=(1,0)
  simp [prod,b.norm_left,add_self]
theorem binaryTwist_ker_bit {X : Type} [Group X] (b : Cocycle X) :
    (zbit : b.Twist) ∈ b.projTwist.ker := rfl
open scoped commutatorElement in
lemma bit_lift_kills_third {X E : Type} [Group X] [Group E]
    (b : Cocycle X) (f : E →* b.Twist) (hs : ∀x:X,x*x=1) :
    binaryThird E ≤ f.ker := by
  have sq : squareCore E ≤ (b.projTwist.comp f).ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨y,rfl⟩
    change (b.projTwist.comp f) (y*y)=1
    rw [map_mul];exact hs _
  apply (Subgroup.closure_le _).mpr
  rintro _ (⟨w,rfl⟩|⟨⟨w,x⟩,rfl⟩)
  · change f (w.val*w.val)=1
    rw [f.map_mul]
    exact binaryTwist_ker_square b ⟨f w.val,sq w.property⟩
  · change f ⁅w.val,x⁆=1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (b.projTwist_central (sq w.property)) (f x)).symm
lemma detected_bit_yields_lift (hp : Function.Surjective p)
    (a : RelCharacters (p.comp c.projTwist))
    (ha : (a.val ⟨zbit,show p 1=1 from map_one p⟩).toAdd=1) :
    cohomClass c ∈ LinearMap.range (inflate₂ p) := by
  let g := p.comp c.projTwist
  let S := normSection g (hp.comp c.projTwist_onto)
  let A := Additive.ofMul a
  let b := ofCycle (transgressCycle S A)
  let f : c.Twist →* b.Twist := {
    toFun x := (g x,splitFunction S A x)
    map_one' := Prod.ext g.map_one (split_function_one S A)
    map_mul' x y := Prod.ext (g.map_mul x y) (split_product S A x y) }
  apply (range_iff_bit_lift p c).mpr
  refine ⟨b,f,rfl,Prod.ext (map_one p) ?_⟩
  exact (split_function_kernel S A ⟨zbit,show p 1=1 from map_one p⟩).trans ha
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.CentralLifts.Survival
open BinaryFactor Erdos1160Growth.LowerTriangularUpper
open Erdos1160.DeepJacobi (binaryThird)
lemma elementary_separates {A : Type} [Group A] [Finite A]
    (hs : ∀x:A,x*x=1) (w : A) (hw : w≠1) :
    ∃ χ : A →* Erdos1160.DeepJacobi.C₂,(χ w).toAdd=1 := by
  have hp : IsPGroup 2 A := fun u => ⟨1,by simpa only [pow_one,pow_two] using hs u⟩
  obtain ⟨s,hsize⟩ := hp.exists_card_eq
  obtain ⟨i⟩ := exist_elementary_coords hs hsize
  have he : ∃ j, (i w).toAdd j≠0 := by
    by_contra! h
    apply hw
    exact i.injective ((show i w=1 from funext h).trans i.map_one.symm)
  obtain ⟨j,hj⟩ := he
  let χ : A →* Erdos1160.DeepJacobi.C₂ :=
    (show Multiplicative (Erdos1160Growth.LowerTriangularUpper.V s) →* Erdos1160.DeepJacobi.C₂ from
      { toFun := fun x=>.ofAdd (x.toAdd j)
        map_one' := rfl
        map_mul' _ _ := rfl }).comp i.toMonoidHom
  exact ⟨χ,(bit_cases _).resolve_left hj⟩
variable {E Y V : Type} [Group E] [Group Y] [Group V]
lemma preimage_binary_third (f : E→*Y) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center E) (hb : ∀x:f.ker,x.val*x.val=1)
    (w : E) (hw : f w∈squareCore Y) :
    let q := QuotientGroup.mk' (binaryThird E)
    q w∈Subgroup.center (E ⧸ binaryThird E) ∧ q w*q w=1 := by
  let q := QuotientGroup.mk' (binaryThird E)
  have hq := QuotientGroup.mk'_surjective (binaryThird E)
  obtain ⟨v,hv,e⟩ := (CentralKernelCount.squareCore_map f hf).ge hw
  let k : f.ker := ⟨v⁻¹*w,by change f (_*_)=1;rw [map_mul,map_inv,e,inv_mul_cancel]⟩
  have eq : w=v*k.val := by simp [k]
  have hvc : q v∈Subgroup.center (E ⧸ binaryThird E) := (third_quot_squares E).1
    ((CentralKernelCount.squareCore_map q hq).le ⟨v,hv,rfl⟩)
  have hvb : q v*q v=1 := congrArg Subtype.val ((third_quot_squares E).2
    ⟨q v,(CentralKernelCount.squareCore_map q hq).le ⟨v,hv,rfl⟩⟩)
  have hkc : q k.val∈Subgroup.center (E ⧸ binaryThird E) := by
    apply Subgroup.mem_center_iff.mpr
    intro z
    obtain ⟨x,rfl⟩ := hq z
    rw [←map_mul,←map_mul,Subgroup.mem_center_iff.mp (hc k.property) x]
  have hkb : q k.val*q k.val=1 := (q.map_mul ..).symm.trans (by rw [hb k,map_one])
  change q w∈_ ∧ q w*q w=1
  rw [eq,q.map_mul]
  refine ⟨(Subgroup.center _).mul_mem hvc hkc,?_⟩
  have hcomm : Commute (q v) (q k.val) := (Subgroup.mem_center_iff.mp hvc _).symm
  calc
    q v * q k.val * (q v * q k.val) = (q v*q k.val)^2 := (pow_two _).symm
    _ = q v ^ 2*q k.val^2 := hcomm.mul_pow 2
    _ = 1 := by rw [pow_two,pow_two,hvb,hkb,one_mul]
theorem scalar_bit_detected [Finite E] (p : Y→*V) (hk : p.ker=squareCore Y)
    (f : E→*Y) (hf : Function.Surjective f) (hc : f.ker ≤ Subgroup.center E)
    (hb : ∀x:f.ker,x.val*x.val=1) (z : f.ker) (hz : z.val∉binaryThird E) :
    ∃ a : RelCharacters (p.comp f),(a.val ⟨z.val,by change p (f z.val)=1;rw [show f z.val=1 from z.property,map_one]⟩).toAdd=1 := by
  let q := QuotientGroup.mk' (binaryThird E)
  let g := p.comp f
  let W := g.ker.map q
  let h := (q.comp g.ker.subtype).codRestrict W (fun x=>⟨x.val,x.property,rfl⟩)
  have spec (w : g.ker) := preimage_binary_third f hf hc hb w.val (hk ▸ (show f w.val∈p.ker from w.property))
  have sq (v : W) : v*v=1 := by
    obtain ⟨w,hw,e⟩ := v.property
    apply Subtype.ext
    change v.val*v.val=1
    rw [←e]
    exact (spec ⟨w,hw⟩).2
  let marker : g.ker := ⟨z.val,by change p (f z.val)=1;rw [show f z.val=1 from z.property,map_one]⟩
  have hn : h marker≠1 := by
    intro he;apply hz
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val he)
  obtain ⟨χ,hχ⟩ := elementary_separates sq (h marker) hn
  let a := χ.comp h
  refine ⟨⟨a,?_⟩,hχ⟩
  intro x w
  apply congrArg χ
  apply Subtype.ext
  change q (x*w.val*x⁻¹)=q w.val
  rw [map_mul,map_mul,map_inv,Subgroup.mem_center_iff.mp (spec w).1 (q x),mul_inv_cancel_right]
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.CentralLifts.Survival
open BinaryFactor BinaryFactor.Cocycle
open Erdos1160Growth.LowerTriangularUpper
open Erdos1160.DeepJacobi (binaryThird)
variable {Y V : Type} [Group Y] [Group V] [Finite Y]
theorem allowable_bit_general (p : Y→*V) (hp : Function.Surjective p) (hk : p.ker=squareCore Y)
    (hV : ∀x:V,x*x=1) (c : Cocycle Y) :
    (zbit : c.Twist) ∈ binaryThird c.Twist ↔ cohomClass c ∉ LinearMap.range (inflate₂ p) := by
  constructor
  · intro hz h
    obtain ⟨b,f,_,hbit⟩ := (range_iff_bit_lift p c).mp h
    have e : f (zbit : c.Twist)=1 := bit_lift_kills_third b f hV hz
    rw [hbit] at e
    exact (by decide : (1:Bit)≠0) (congrArg (fun w : b.Twist => w.2) e)
  · intro h
    by_contra hz
    obtain ⟨a,ha⟩ := scalar_bit_detected p hk c.projTwist c.projTwist_onto c.projTwist_central
      (binaryTwist_ker_square c) ⟨zbit,binaryTwist_ker_bit c⟩ hz
    exact h (detected_bit_yields_lift p c hp a ha)
theorem allowable_bit_iff {d : ℕ} (p : Y→*Elementary.Vectors d)
    (hp : Function.Surjective p) (hk : p.ker=squareCore Y) (c : Cocycle Y) :
    (zbit : c.Twist) ∈ binaryThird c.Twist ↔ cohomClass c ∉ LinearMap.range (inflate₂ p) :=
  allowable_bit_general p hp hk (fun x => show x.toAdd+x.toAdd=0 from two_copies_zero _) c
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.DescendantTree
theorem exceptional_fraction {count exceptional d s i K : ℕ} (hd : 64 ≤ d)
    (hs : 16*s ≤ d) (hi : 8*i ≤ d) (hK : K ≤ d*(s+i)+s)
    (hcover : exceptional*2^(d*(d-1)/2) ≤ count*2^(d+1+K)) :
    exceptional*2^(d^2/4) ≤ count := by
  have hd₁ := Nat.mul_le_mul_left d hs
  have hd₂ := Nat.mul_le_mul_left d hi
  have hd₃ := Nat.div_mul_le_self (d^2) 4
  have hd₄ := congrArg (d*·) (show d-1+1=d by omega)
  have hd₅ := Nat.mul_le_mul_left d hd
  have hnum : d^2/4+(d+1+K) ≤ d*(d-1)/2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    nlinarith only [hd₁,hd₂,hd₃,hd₄,hd₅,hK,hs,hd]
  apply Nat.le_of_mul_le_mul_right (c := 2^(d+1+K)) _ (by positivity)
  rw [Nat.mul_assoc,←pow_add]
  exact (Nat.mul_le_mul_left exceptional (Nat.pow_le_pow_right (by decide) hnum)).trans hcover
end Erdos1160.DescendantTree
end
section
namespace Erdos1160.DescendantTree.Actual
open BinaryFactor BinaryFactor.Cocycle BinaryFactor.Elementary CategoryTheory
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival Erdos1160Growth.LowerTriangularUpper
structure Root (d s : ℕ) where
  group : FiniteGrp.{0}
  size : Nat.card group=2^(d+s)
  elementary : group →* Vectors d
  onto : Function.Surjective elementary
  ker_eq : elementary.ker=squareCore group
  deep_trivial : binaryThird group=⊥
  width : Nat.card (squareCore group)=2^s
variable {d s : ℕ} (R : Root d s)
abbrev Layer := Vertex R.group (d+s)
abbrev b₀ (d s : ℕ) := d*(d+1)/2-s
theorem coeff_identity (d : ℕ) : d*(d-1)/2+d=d*(d+1)/2 := by
  have h := OrbitUp.twice_slots d
  dsimp only [OrbitUp.slotsN] at h
  rw [show d*(d+1)=d^2+d by ring,←h]
  omega
theorem local_dimension (x : Layer R) :
    Module.finrank Bit (LinearMap.range (inflate₂ (toVectors R.elementary x)))=b₀ d s := by
  have h := actual_image_dimension R.elementary R.onto R.ker_eq R.deep_trivial R.width x
  dsimp only [b₀];omega
theorem height_floor (x : Layer R) : b₀ d s ≤ r₂ x.group := by
  rw [←local_dimension R x]
  exact Submodule.finrank_le _
theorem forest_ambient (x : Layer R) : b₀ d s+height (b₀ d s) x.depth x=r₂ x.group := by
  simp only [height,if_true]
  have h := height_floor R x
  omega
theorem allowed_outside (x : Layer R) (a : Allowed x) :
    a.val∉LinearMap.range (inflate₂ (toVectors R.elementary x)) := by
  rw [←classCocycle_repr a.val]
  exact (allowable_bit_iff (toVectors R.elementary x) (R.onto.comp x.onto) (toVectors_ker _ R.ker_eq x) _).mp (a.property rfl)
theorem active_floor (x : Layer R) (a : Allowed x) : b₀ d s < r₂ x.group := by
  let S := LinearMap.range (inflate₂ (toVectors R.elementary x))
  have hs : S<⊤ := lt_top_iff_ne_top.mpr (fun hh=>allowed_outside R x a (show a.val∈S from hh.symm ▸ Submodule.mem_top))
  have h := Submodule.finrank_lt_finrank_of_lt hs
  rw [finrank_top,local_dimension] at h
  exact h
noncomputable def loss (i : ℕ) (x : Layer R) := if i=x.depth then d*(s+i)+(d*(d-1)/2+d)-r₂ x.group else 0
theorem loss_bound (i : ℕ) (x : Layer R) : loss R i x ≤ d*(s+i)+s := by
  by_cases h : i=x.depth
  · rw [loss,if_pos h,coeff_identity]
    have h₁ := height_floor R x
    dsimp only [b₀] at h₁
    omega
  · simp [loss,h]
private theorem normalize {i : ℕ} (x : Layer R) (P : H₂ x.group→Prop)
    (test : Layer R→Prop) [DecidablePred test]
    (good : ∀a : Allowed x,test (next x a)→P a.val) {n k : ℕ}
    (cc : Nat.card {z:H₂ x.group // z∉LinearMap.range (inflate₂ (toVectors R.elementary x)) ∧ P z}*n ≤
      Nat.card {z:H₂ x.group // z∉LinearMap.range (inflate₂ (toVectors R.elementary x))}*k) :
    ((children i x).filter test).card*n ≤ 2^(r₂ x.group)*k := by
  have h := filtered_card i x (fun z=>z∉LinearMap.range (inflate₂ (toVectors R.elementary x)) ∧ P z) test (fun a h=>And.intro (allowed_outside R x a) (good a h))
  apply ((Nat.mul_le_mul_right n h).trans cc).trans
  apply Nat.mul_le_mul_right k
  have hc := Nat.card_le_card_of_injective
    (Subtype.val : {z:H₂ x.group // z∉LinearMap.range (inflate₂ (toVectors R.elementary x))}→H₂ x.group)
    Subtype.val_injective
  rwa [Module.natCard_eq_pow_finrank (K:=Bit) (V:=H₂ x.group),Nat.card_zmod] at hc
private theorem order_at (x : Layer R) : Nat.card x.group=2^(d+(s+x.depth)) := by
  rw [x.size,Nat.add_assoc]
private theorem frattini_at (x : Layer R) : (toVectors R.elementary x).ker ≤ frattini x.group :=
  (toVectors_ker _ R.ker_eq x).le.trans (squares_le_frattini (order_at R x))
theorem local_rare {i : ℕ} (x : Layer R) (hd : 64 ≤ d) (hs : 16*s ≤ d) (hi : 8*i ≤ d) :
    ((children i x).filter (fun y=>y.exceptional)).card*2^(d^2/4) ≤ 2^(b₀ d s+height (b₀ d s) i x) := by
  classical
  by_cases hx : i=x.depth
  · subst i
    have cc := su_xia_5_5_allowable (order_at R x) (toVectors R.elementary x) (R.onto.comp x.onto) (frattini_at R x)
      (by omega : 1 ≤ d)
    have h := normalize R (i:=x.depth) x Elementary.exceptional (fun v=>v.exceptional) (fun a h=>of_decide_eq_true h) cc
    rw [forest_ambient]
    apply exceptional_fraction hd hs hi (loss_bound R x.depth x)
    simpa only [loss,if_true] using h
  · simp [children,hx]
end Erdos1160.DescendantTree.Actual
end
section
namespace BinaryCapacity
open Erdos1160.DeepJacobi Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival
open Erdos1160Growth.LowerTriangularUpper CentralKernelCount
open scoped commutatorElement
theorem sqmap_le {G H : Type*} [Group G] [Group H] (f : G→*H) :
    (squareCore G).map f ≤ squareCore H := by
  rw [squareCore,MonoidHom.map_closure,Subgroup.closure_le]
  rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
  exact (map_mul f x x).symm ▸ Subgroup.subset_closure ⟨f x,rfl⟩
theorem thirdmap_le {G H : Type*} [Group G] [Group H] (f : G→*H) :
    (binaryThird G).map f ≤ binaryThird H := by
  rw [binaryThird,MonoidHom.map_closure,Subgroup.closure_le]
  have lift (x : squareCore G) : f x.val∈squareCore H := sqmap_le f ⟨x.val,x.property,rfl⟩
  rintro _ ⟨_,(⟨x,rfl⟩|⟨⟨x,y⟩,rfl⟩),rfl⟩
  · rw [map_mul];exact Subgroup.subset_closure (.inl ⟨⟨_,lift x⟩,rfl⟩)
  · rw [map_commutatorElement];exact Subgroup.subset_closure (.inr ⟨(⟨_,lift x⟩,f y),rfl⟩)
lemma square_characteristic (G : Type*) [Group G] : (squareCore G).Characteristic :=
  Subgroup.characteristic_iff_map_le.mpr (fun e=>sqmap_le e.toMonoidHom)
lemma normal_contains_squares {G : Type*} [Group G] (H : Subgroup G) (h : squareCore G ≤ H) :
    H.Normal := by
  constructor
  intro x hx g
  have w : ⁅g,x⁆∈H := h (derived_le_squares G (secondBracket g x).property)
  have e : g*x*g⁻¹=⁅g,x⁆*x := by rw [commutatorElement_def];group
  exact e ▸ H.mul_mem w hx
theorem square_eq_bot {G : Type} [Group G] [Finite G] {m : ℕ}
    (hc : Nat.card G=2^m) (h : squareCore G ≤ binaryThird G) : squareCore G=⊥ := by
  induction m generalizing G with
  | zero =>
    have hx : Nat.card G=1 := hc
    have hsub : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hx).1
    exact eq_bot_iff.mpr (fun x _=>Subgroup.mem_bot.mpr (hsub.elim x 1))
  | succ m ih =>
    obtain ⟨u,_,hz,ho⟩ := central_prime_in_normal Nat.prime_two (IsPGroup.of_card hc) ⊤
      (by rw [Subgroup.card_top,hc];exact dvd_pow_self _ (Nat.succ_ne_zero _))
    let N := Subgroup.zpowers u
    let _ : N.Normal := normal_zpowers_of_central u hz
    let q := QuotientGroup.mk' N
    have sq := QuotientGroup.mk'_surjective N
    have hle : squareCore (G ⧸ N) ≤ binaryThird (G ⧸ N) := by
      rw [←squareCore_map q sq,←binaryThird_map_eq q sq]
      exact Subgroup.map_mono h
    have hi := ih (card_quotient_prime (by decide : 0 < 2) ho hc) hle
    have hk : squareCore G ≤ N := (QuotientGroup.ker_mk' N) ▸
      (Subgroup.map_eq_bot_iff _).mp ((squareCore_map q sq).trans hi)
    have hcard : Nat.card N=2 := (Nat.card_zpowers u).trans ho
    have hcent : N ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hz
    have bit (x : N) : x*x=1 := by
      simpa only [hcard,pow_two] using (pow_card_eq_one' (x:=x))
    have z := binaryThird_eq_bot hc (by rw [frattini_eq_squareCore hc];exact hk.trans hcent)
      (fun x=>by
        have hx := hk ((frattini_eq_squareCore hc).le x.property)
        exact Subtype.ext (congrArg (fun z : N=>z.val) (bit ⟨x.val,hx⟩)))
    exact eq_bot_iff.mpr (h.trans z.le)
theorem same_squares {G : Type} [Group G] [Finite G] {m : ℕ} (hc : Nat.card G=2^m)
    (H : Subgroup G) (hH : squareCore G ≤ H)
    (hspan : squareCore G≤(squareCore H).map H.subtype ⊔ binaryThird G) :
    (squareCore H).map H.subtype=squareCore G := by
  letI := normal_contains_squares H hH
  letI := square_characteristic H
  let K := (squareCore H).map H.subtype
  let q := QuotientGroup.mk' K
  have sq := QuotientGroup.mk'_surjective K
  have vanish : K.map q=⊥ := (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' K).ge
  have le := Subgroup.map_mono (f:=q) hspan
  change (squareCore G).map q ≤ (K ⊔ binaryThird G).map q at le
  rw [squareCore_map q sq,Subgroup.map_sup,vanish,bot_sup_eq,binaryThird_map_eq q sq] at le
  obtain ⟨n,hn⟩ := ((IsPGroup.of_card hc).to_quotient K).exists_card_eq
  have hbot := square_eq_bot hn le
  have hk : squareCore G ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp ((squareCore_map q sq).trans hbot)
  exact le_antisymm (sqmap_le H.subtype) (hk.trans (QuotientGroup.ker_mk' K).le)
end BinaryCapacity
end
section
namespace BinaryCapacity
open Erdos1160.DeepJacobi Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival
open Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
theorem same_third {G : Type*} [Group G] (H : Subgroup G) (hH : squareCore G ≤ H)
    (hΦ : (squareCore H).map H.subtype=squareCore G) :
    (binaryThird H).map H.subtype=binaryThird G := by
  letI := normal_contains_squares H hH
  let K := (binaryThird H).map H.subtype
  let q := QuotientGroup.mk' K
  let h := q.comp H.subtype
  have kill (x : H) (hx : x∈binaryThird H) : h x=1 := (QuotientGroup.eq_one_iff _).mpr ⟨x,hx,rfl⟩
  have square (x : squareCore H) : h x.val*h x.val=1 := by
    rw [←map_mul]
    exact kill _ (Subgroup.subset_closure (.inl ⟨x,rfl⟩))
  have central (x : squareCore H) (y : H) : h x.val*h y=h y*h x.val := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact kill _ (Subgroup.subset_closure (.inr ⟨(x,y),rfl⟩))
  have fix (g : G) (x : H) (hx : x∈squareCore H) :
      q (g*x.val*g⁻¹)=h x := by
    let h' := q.comp ((MulAut.conj g).toMonoidHom.comp H.subtype)
    apply MonoidHom.eqOn_closure (f:=h') (g:=h) (s:=Set.range (fun y : H=>y*y)) _ hx
    rintro _ ⟨y,rfl⟩
    let n := ⁅g,y.val⁆
    have hn : n∈(squareCore H).map H.subtype := hΦ.ge (derived_le_squares G (secondBracket g y.val).property)
    obtain ⟨w,hw,he⟩ := hn
    have wh : g*y.val*g⁻¹=w.val*y.val := by rw [←show n=w.val from he.symm];dsimp [n,commutatorElement_def];group
    have eq : h' y =h w*h y := by change q (g*y.val*g⁻¹)=q w.val*q y.val;rw [wh,map_mul]
    rw [map_mul,map_mul,eq]
    have comm := central ⟨w,hw⟩ y
    calc
      h w*h y*(h w*h y) = (h w*(h y*h w))*h y := by group
      _ = (h w*h w)*(h y*h y) := by rw [←comm];group
      _ = h y*h y := by rw [square ⟨w,hw⟩,one_mul]
  refine le_antisymm (thirdmap_le H.subtype) ?_
  change binaryThird G ≤ K
  rw [←QuotientGroup.ker_mk' K,binaryThird,Subgroup.closure_le]
  rintro _ (⟨x,rfl⟩|⟨⟨x,g⟩,rfl⟩)
  · obtain ⟨v,hv,e⟩ := hΦ.ge x.property
    change q (x.val*x.val)=1
    rw [←e,map_mul]
    exact square ⟨v,hv⟩
  · obtain ⟨v,hv,e⟩ := hΦ.ge x.property
    have hg := fix g v hv
    change q (g*v.val*g⁻¹)=q v.val at hg
    rw [map_mul,map_mul,map_inv] at hg
    have comm := mul_inv_eq_iff_eq_mul.mp hg
    change q ⁅x.val,g⁆=1
    rw [←e,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr comm.symm
theorem subgroup_criterion {G : Type} [Group G] [Finite G] {m : ℕ} (hc : Nat.card G=2^m)
    (H : Subgroup G) (hH : squareCore G ≤ H)
    (hspan : squareCore G≤(squareCore H).map H.subtype ⊔ binaryThird G) :
    (squareCore H).map H.subtype=squareCore G ∧
      (binaryThird H).map H.subtype=binaryThird G := by
  let h := same_squares hc H hH hspan
  exact ⟨h,same_third H hH h⟩
end BinaryCapacity
end
section
namespace BinaryCapacity
open Erdos1160.DeepJacobi Erdos1160.CentralLifts.Survival Erdos1160Growth.LowerTriangularUpper CentralKernelCount
def preimageHom {E G : Type*} [Group E] [Group G] (f : E→*G) (H : Subgroup G) :
    H.comap f →* H := (f.comp (H.comap f).subtype).codRestrict H (fun x=>x.property)
theorem preimageHom_surjective {E G : Type*} [Group E] [Group G]
    (f : E→*G) (hf : Function.Surjective f) (H : Subgroup G) :
    Function.Surjective (preimageHom f H) := by
  intro x
  obtain ⟨y,hy⟩ := hf x.val
  exact ⟨⟨y,show f y∈H from hy ▸ x.property⟩,Subtype.ext hy⟩
theorem lifted_criterion {E G : Type} [Group E] [Finite E] [Group G] {m : ℕ}
    (hc : Nat.card E=2^m) (f : E→*G) (hf : Function.Surjective f)
    (hk : f.ker ≤ binaryThird E) (H : Subgroup G) (hH : squareCore G ≤ H)
    (hΦ : (squareCore H).map H.subtype=squareCore G) :
    (binaryThird (H.comap f)).map (H.comap f).subtype=binaryThird E := by
  let M := H.comap f
  let p := preimageHom f H
  have sp := preimageHom_surjective f hf H
  have sq : squareCore E ≤ M :=
    fun x hx=>hH ((sqmap_le f) (show f x ∈ (squareCore E).map f from ⟨x,hx,rfl⟩))
  apply (subgroup_criterion hc M sq _).2
  intro x hx
  obtain ⟨v,hv,he⟩ := hΦ.ge ((sqmap_le f) (show f x∈(squareCore E).map f from ⟨x,hx,rfl⟩))
  obtain ⟨w,hw,ew⟩ := (squareCore_map p sp).ge hv
  have ew' : f w.val=f x := (congrArg Subtype.val ew).trans he
  have z : x*w.val⁻¹∈f.ker := by rw [MonoidHom.mem_ker,map_mul,map_inv,ew',mul_inv_cancel]
  have m₁ : x*w.val⁻¹∈(squareCore M).map M.subtype ⊔ binaryThird E := (show binaryThird E ≤ (squareCore M).map M.subtype ⊔ binaryThird E from le_sup_right) (hk z)
  have m₂ : w.val∈(squareCore M).map M.subtype ⊔ binaryThird E := (show (squareCore M).map M.subtype ≤ (squareCore M).map M.subtype ⊔ binaryThird E from le_sup_left) (show w.val∈(squareCore M).map M.subtype from ⟨w,hw,rfl⟩)
  simpa only [inv_mul_cancel_right] using Subgroup.mul_mem _ m₁ m₂
open BinaryFactor BinaryFactor.Cocycle
def restrictCycle {G : Type*} [Group G] (c : Cocycle G) (H : Subgroup G) : Cocycle H :=
  ofCycle (cyclePull H.subtype c.asCycle)
def restrictTwistEquiv {G : Type*} [Group G] (c : Cocycle G) (H : Subgroup G) :
    (restrictCycle c H).Twist ≃* H.comap c.projTwist where
  toFun z := ⟨(z.1.val,z.2),z.1.property⟩
  invFun z := (⟨z.val.1,z.property⟩,z.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
theorem ker_bit_le {G : Type*} [Group G] (c : Cocycle G) (S : Subgroup c.Twist)
    (h : zbit∈S) : c.projTwist.ker ≤ S := by
  rintro ⟨x,t⟩ (hx : x=1)
  subst x
  rcases bit_cases t with rfl|rfl
  · exact S.one_mem
  · exact h
theorem restriction_third_iff {G : Type} [Group G] [Finite G] {m : ℕ}
    (hc : Nat.card G=2^m) (H : Subgroup G) (hH : squareCore G ≤ H)
    (hΦ : (squareCore H).map H.subtype=squareCore G) (c : Cocycle G) :
    zbit∈binaryThird (restrictCycle c H).Twist ↔ zbit∈binaryThird c.Twist := by
  let e := restrictTwistEquiv c H
  let M := H.comap c.projTwist
  have hcE : Nat.card c.Twist=2^(m+1) := by rw [c.card_twist,hc,pow_succ,Nat.mul_comm]
  constructor
  · intro hx
    have h₁ : e (zbit:(restrictCycle c H).Twist)∈binaryThird M :=
      thirdmap_le e.toMonoidHom ⟨_,hx,rfl⟩
    exact thirdmap_le M.subtype ⟨_,h₁,rfl⟩
  · intro h
    have eq := lifted_criterion hcE c.projTwist c.projTwist_onto (ker_bit_le c _ h) H hH hΦ
    obtain ⟨x,hx,he⟩ := eq.ge h
    have eq' : x=e (zbit:(restrictCycle c H).Twist) := Subtype.ext he
    rw [eq'] at hx
    obtain ⟨y,hy,ey⟩ := (binaryThird_map_eq e.toMonoidHom e.surjective).ge hx
    exact e.injective ey ▸ hy
end BinaryCapacity
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
theorem short_generator_subset {I G : Type} [Fintype I] [Group G] [Finite G] (f : I→G)
    (gen : Subgroup.closure (Set.range f)=⊤) :
    ∃S : Finset I, Subgroup.closure (f '' (S : Set I))=⊤ ∧ 2^S.card ≤ Nat.card G := by
  classical
  let H (S : Finset I) := Subgroup.closure (f '' (S : Set I))
  let C := Finset.univ.filter (fun S : Finset I=>2^S.card ≤ Nat.card (H S))
  have ne : C.Nonempty := ⟨∅,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [H]⟩⟩
  obtain ⟨S,hs,maxH⟩ := C.exists_max_image (fun S=>Nat.card (H S)) ne
  have bound := (Finset.mem_filter.mp hs).2
  have top : H S=⊤ := by
    by_contra h
    have missing : ∃i,f i∉H S := by
      by_contra! hall
      exact h (top_unique (gen ▸ (Subgroup.closure_le (H S)).mpr (by rintro _ ⟨i,rfl⟩;exact hall i)))
    obtain ⟨i,hi⟩ := missing
    let T := insert i S
    have ni : i∉S := fun mem=>hi (Subgroup.subset_closure ⟨i,mem,rfl⟩)
    have sub : H S ≤ H T := Subgroup.closure_mono (Set.image_mono (by intro x hx;exact Finset.mem_insert_of_mem hx))
    have nle : ¬H T ≤ H S := fun h'=>hi (h' (Subgroup.subset_closure ⟨i,Finset.mem_insert_self ..,rfl⟩))
    let j := (H S).relIndex (H T)
    have jpos : 0 < j := Nat.card_pos
    have jn : j≠1 := fun h'=> nle (Subgroup.relIndex_eq_one.mp h')
    have eq : j*Nat.card (H S)=Nat.card (H T) := by
      rw [←Nat.card_congr (Subgroup.subgroupOfEquivOfLe sub).toEquiv]
      exact ((H S).subgroupOf (H T)).index_mul_card
    have big : 2*Nat.card (H S) ≤ Nat.card (H T) := eq ▸ Nat.mul_le_mul_right _ (show 2 ≤ j by omega)
    have tc : T∈C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      rw [show T.card=S.card+1 from Finset.card_insert_of_notMem ni,pow_succ',Nat.mul_comm 2]
      exact (Nat.mul_le_mul_right 2 bound).trans ((Nat.mul_comm ..).le.trans big)⟩
    have hg := maxH T tc
    have positive := Nat.card_pos (α:=H S)
    omega
  refine ⟨S,top,bound.trans (H S).card_le_card_group⟩
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.ChiefFactors
theorem commuting_generated_bound {d p : ℕ} (hp : 0 < p) {G : Type*} [Group G] (z : Fin d → G)
    (hz : ∀ i, z i^p=1) (hc : Pairwise fun i j => Commute (z i) (z j)) :
    Finite (Subgroup.closure (Set.range z)) ∧ Nat.card (Subgroup.closure (Set.range z)) ≤ p^d := by
  let S (i : Fin d) := Subgroup.zpowers (z i)
  have hco : Pairwise (fun i j : Fin d => ∀ (x:S i) (y:S j), Commute ((S i).subtype x) ((S j).subtype y)) := by
    change Pairwise (fun i j : Fin d => ∀ (x:S i) (y:S j), Commute (x:G) (y:G))
    intro i j h x y
    obtain ⟨u,hu⟩ := x.property
    obtain ⟨v,hv⟩ := y.property
    rw [←hu,←hv]
    exact ((hc h).zpow_left _).zpow_right _
  let f := MonoidHom.noncommPiCoprod (fun i => (S i).subtype) hco
  let _ (i : Fin d) : Finite (S i) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨p,hp,hz i⟩).orderOf_pos.ne')
  have hsize (i : Fin d) : Nat.card (S i) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one (hz i))
  have sub : Subgroup.closure (Set.range z) ≤ f.range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    change z i ∈ (MonoidHom.noncommPiCoprod (fun i => (S i).subtype) hco).range
    rw [MonoidHom.noncommPiCoprod_range (fun i => (S i).subtype) (hcomm := hco)]
    apply (le_iSup (fun i : Fin d => (S i).subtype.range) i)
    exact ⟨⟨z i,Subgroup.mem_zpowers _⟩,rfl⟩
  let _ : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfin : Finite (Subgroup.closure (Set.range z)) := Finite.of_injective
    (Subgroup.inclusion sub) (Subgroup.inclusion_injective sub)
  refine ⟨hfin, ?_⟩
  calc
    _ ≤ Nat.card f.range := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective sub)
    _ ≤ Nat.card ((i:Fin d) → S i) := Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective
    _ = ∏ i : Fin d, Nat.card (S i) := Nat.card_pi
    _ ≤ ∏ _ : Fin d, p := Finset.prod_le_prod' (fun i _ => hsize i)
    _ = _ := by simp
end Erdos1160.ChiefFactors
end
section
namespace Erdos1160.CohomCapacity
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
private theorem quotient_commute {Y : Type} [Group Y] (x y : Y ⧸ squareCore Y) : Commute x y := by
  have h (a : Y ⧸ squareCore Y) : a*a=1 := by
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (squareCore Y) a
    rw [←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨w,rfl⟩)
  have hi (a : Y ⧸ squareCore Y) : a⁻¹=a := inv_eq_of_mul_eq_one_left (h a)
  exact calc x*y = (x*y)⁻¹ := (hi _).symm
             _ = y*x := by rw [mul_inv_rev,hi,hi]
theorem small_square_subgroup (Y : Type) [Group Y] [Finite Y] {s : ℕ}
    (hs : Nat.card (squareCore (Y ⧸ binaryThird Y))=2^s) :
    ∃ H : Subgroup Y, squareCore Y ≤ H ∧
      squareCore Y ≤ (squareCore H).map H.subtype ⊔ binaryThird Y ∧
      (squareCore Y).relIndex H ≤ 2^s := by
  classical
  let _ := Fintype.ofFinite Y
  let Q := Y ⧸ binaryThird Y
  let π := QuotientGroup.mk' (binaryThird Y)
  let sq (y:Y) : squareCore Q := ⟨π y*π y,Subgroup.subset_closure ⟨π y,rfl⟩⟩
  have gen : Subgroup.closure (Set.range sq)=⊤ := by
    let D := Subgroup.closure (Set.range sq)
    have all : squareCore Q ≤ D.map (squareCore Q).subtype := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨w,rfl⟩
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (binaryThird Y) w
      exact ⟨sq y,Subgroup.subset_closure ⟨y,rfl⟩,rfl⟩
    apply top_unique
    intro z _
    obtain ⟨v,hv,h⟩ := all z.property
    exact (Subtype.ext h : v=z) ▸ hv
  obtain ⟨T,hgen,hnum⟩ := short_generator_subset sq gen
  let p := QuotientGroup.mk' (squareCore Y)
  let e := (Fintype.equivFin T).symm
  let z (i : Fin (Fintype.card T)) := p (e i).val
  let R := Subgroup.closure (Set.range z)
  let H := R.comap p
  have chosen (y:Y) (hy:y∈T) : y∈H := by
    apply Subgroup.subset_closure
    exact ⟨e.symm ⟨y,hy⟩,by simp [z]⟩
  have h0 : p.ker=squareCore Y := QuotientGroup.ker_mk' _
  refine ⟨H,h0 ▸ Subgroup.ker_le_comap _ _,?_,?_⟩
  · let D := (squareCore H).map H.subtype
    let L := D.map π
    have all : (squareCore Q) ≤ L := by
      have sub : Subgroup.closure (sq '' (T:Set Y)) ≤ L.comap (squareCore Q).subtype := by
        apply (Subgroup.closure_le _).mpr
        rintro _ ⟨y,hy,rfl⟩
        let w : H := ⟨y,chosen y hy⟩
        exact ⟨y*y,⟨w*w,Subgroup.subset_closure ⟨w,rfl⟩,rfl⟩,map_mul π y y⟩
      rw [hgen] at sub
      exact fun x hx=>sub (Subgroup.mem_top (⟨x,hx⟩:squareCore Q))
    have hmap : (squareCore Y).map π ≤ D.map π := (CentralKernelCount.squareCore_map π (QuotientGroup.mk'_surjective _)).le.trans all
    have h := (Subgroup.map_le_iff_le_comap).mp hmap
    rwa [Subgroup.comap_map_eq,QuotientGroup.ker_mk'] at h
  · have order (i) : (z i)^2=1 := by
      rw [pow_two,←show p ((e i).val*(e i).val)=z i*z i from map_mul ..]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨(e i).val,rfl⟩)
    have hc := (ChiefFactors.commuting_generated_bound (by decide : 0 < 2) z order
      (fun i j _=>quotient_commute ..)).2
    rw [←h0,Subgroup.relIndex_ker,Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _]
    exact hc.trans ((Fintype.card_coe T) ▸ hs ▸ hnum)
end Erdos1160.CohomCapacity
end
section
namespace BinaryCapacity
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160.CentralLifts.Survival Erdos1160Growth.LowerTriangularUpper
open BinaryFactor BinaryFactor.Cocycle BinaryFactor.Elementary
open CentralKernelCount
lemma quotient_codim_le {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module Bit X] [Module Bit Y] [Finite X] [Finite Y]
    (L : Submodule Bit X) (M : Submodule Bit Y) (f : X→ₗ[Bit]Y)
    (hf : M.comap f=L) : Module.finrank Bit (X ⧸ L) ≤ Module.finrank Bit (Y ⧸ M) := by
  let g := L.mapQ M f hf.ge
  have hker : LinearMap.ker g=⊥ := by
    apply eq_bot_iff.mpr
    intro t
    induction t using Submodule.Quotient.induction_on with
    | _ t =>
      intro ht
      change Submodule.Quotient.mk (p:=M) (f t)=0 at ht
      apply (Submodule.Quotient.mk_eq_zero L).mpr
      exact hf.le ((Submodule.Quotient.mk_eq_zero M).mp ht)
  exact LinearMap.finrank_le_finrank_of_injective (f:=g) (LinearMap.ker_eq_bot.mp hker)
def Detect {G : Type} [Group G] {d : ℕ} (f : G→*Vectors d) :=
  ∀c : Cocycle G,zbit∈binaryThird c.Twist ↔ cohomClass c∉LinearMap.range (inflate₂ f)
lemma restriction_codim {G : Type} [Group G] [Finite G] {m d k : ℕ} (hc : Nat.card G=2^m)
    (H : Subgroup G) (hH : squareCore G ≤ H) (hΦ : (squareCore H).map H.subtype=squareCore G)
    (f : G→*Vectors d) (p : H→*Vectors k) (detG : Detect f) (detH : Detect p) :
    Module.finrank Bit (H₂ G ⧸ LinearMap.range (inflate₂ f)) ≤
      Module.finrank Bit (H₂ H ⧸ LinearMap.range (inflate₂ p)) := by
  letI : Finite (H₂ G) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  letI : Finite (H₂ H) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  apply quotient_codim_le _ _ (inflate₂ H.subtype)
  ext x
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
    let c := ofCycle u
    change cohomClass (restrictCycle c H)∈LinearMap.range (inflate₂ p) ↔
      cohomClass c∈LinearMap.range (inflate₂ f)
    exact not_iff_not.mp (((detH _).symm.trans (restriction_third_iff hc H hH hΦ c)).trans (detG c))
lemma root_square_size (G : Type) [Group G] :
    Nat.card (squareCore (G ⧸ binaryThird G))=(binaryThird G).relIndex (squareCore G) := by
  let q := QuotientGroup.mk' (binaryThird G)
  rw [←squareCore_map q (QuotientGroup.mk'_surjective _),←Subgroup.relIndex_ker,QuotientGroup.ker_mk']
lemma square_quotient_chart {G : Type} [Group G] [Finite G] {k : ℕ}
    (hc : (squareCore G).index=2^k) : ∃p : G→*Vectors k,Function.Surjective p ∧ p.ker=squareCore G := by
  let q := QuotientGroup.mk' (squareCore G)
  have hq := QuotientGroup.mk'_surjective (squareCore G)
  have sq (z : G ⧸ squareCore G) : z*z=1 := by
    obtain ⟨x,rfl⟩ := hq z
    rw [←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨x,rfl⟩)
  obtain ⟨i⟩ := exist_elementary_coords sq hc
  refine ⟨i.toMonoidHom.comp q,i.surjective.comp hq,?_⟩
  rw [←MonoidHom.comap_ker,MonoidHom.ker_eq_bot _ i.injective,MonoidHom.comap_bot,QuotientGroup.ker_mk']
theorem small_rank_comparison {G : Type} [Group G] [Finite G] {m d s j : ℕ}
    (hc : Nat.card G=2^m) (hs : Nat.card (squareCore (G ⧸ binaryThird G))=2^s)
    (hj : Nat.card (binaryThird G)=2^j) (f : G→*Vectors d) (hf : Function.Surjective f)
    (hker : f.ker=squareCore G)
    (detect : ∀ {A : Type} [Group A] [Finite A] {v : ℕ} (p : A→*Vectors v),
      Function.Surjective p → p.ker=squareCore A → Detect p) :
    r₂ G+s ≤ d*(d+1)/2+(s*(s+1)+s*j) := by
  classical
  obtain ⟨H,hH,hspan,hsmall⟩ := Erdos1160.CohomCapacity.small_square_subgroup G hs
  obtain ⟨sq,th⟩ := subgroup_criterion hc H hH hspan
  have hsH : Nat.card (squareCore (H ⧸ binaryThird H))=2^s := by
    rw [root_square_size,←Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective,th,sq,←root_square_size,hs]
  have cardΦ : Nat.card (squareCore G)=2^(s+j) := by
    rw [root_square_size] at hs
    have eq : (binaryThird G).relIndex (squareCore G)*Nat.card (binaryThird G)=Nat.card (squareCore G) := by
      rw [←Nat.card_congr (Subgroup.subgroupOfEquivOfLe (binaryThird_le_squares G)).toEquiv]
      exact ((binaryThird G).subgroupOf (squareCore G)).index_mul_card
    rw [←eq,hs,hj,pow_add]
  have hΦH : Nat.card (squareCore H)=2^(s+j) := by
    rw [←Subgroup.card_map_of_injective H.subtype_injective,sq,cardΦ]
  have hix : (squareCore H).index ≤ 2^s := by
    have e := Subgroup.relIndex_map_map_of_injective (squareCore H) ⊤ H.subtype_injective
    rw [sq,←MonoidHom.range_eq_map,H.range_subtype,Subgroup.relIndex_top_right] at e
    exact e.ge.trans hsmall
  obtain ⟨k,hk⟩ := (((IsPGroup.of_card hc).to_subgroup H).to_quotient (squareCore H)).exists_card_eq
  change (squareCore H).index=2^k at hk
  have hks : k ≤ s := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hk ▸ hix)
  obtain ⟨p,hp,hpk⟩ := square_quotient_chart hk
  have horder : Nat.card H=2^(k+(s+j)) := by rw [←(squareCore H).index_mul_card,hk,hΦH,←pow_add]
  have rel := restriction_codim hc H hH sq f p (detect f hf hker) (detect p hp hpk)
  letI : Finite (H₂ G) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  letI : Finite (H₂ H) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have rankG := Submodule.finrank_quotient_add_finrank (LinearMap.range (inflate₂ f))
  have rankH := Submodule.finrank_quotient_add_finrank (LinearMap.range (inflate₂ p))
  have dG := allowable_dimension f hf hker hs
  have dH := allowable_dimension p hp hpk hsH
  have hfr : p.ker ≤ frattini H := hpk.le.trans (squares_le_frattini horder)
  have growth := (inflation_tower (vectors_card k) (s+j) horder p hp hfr).1
  rw [vectors_char_rank,elementary_r₂] at growth
  have eq : k*(k-1)/2+k=k*(k+1)/2 := by
    have h := OrbitUp.twice_slots k
    dsimp only [OrbitUp.slotsN] at h
    have eq : k*(k+1)=k^2+k := by ring
    rw [eq,←h];omega
  rw [eq] at growth
  change _=r₂ G at rankG
  change _=r₂ H at rankH
  have hl := Nat.mul_le_mul_left (s+j) hks
  nlinarith only [rel,rankG,rankH,dG,dH,growth,hl]
end BinaryCapacity
end
section
namespace BinaryCapacity
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160.CentralLifts.Survival Erdos1160Growth.LowerTriangularUpper
open BinaryFactor BinaryFactor.Elementary
theorem descendant_height {G : Type} [Group G] [Finite G] {m d s j : ℕ}
    (hc : Nat.card G=2^m) (hs : Nat.card (squareCore (G ⧸ binaryThird G))=2^s)
    (hj : Nat.card (binaryThird G)=2^j) (f : G→*Vectors d) (hf : Function.Surjective f)
    (hk : f.ker=squareCore G) :
    r₂ G+s ≤ d*(d+1)/2+(s*(s+1)+s*j) :=
  small_rank_comparison hc hs hj f hf hk (fun p hp hk=>allowable_bit_iff p hp hk)
theorem descendant_tree_cap {G : Type} [Group G] [Finite G] {m d s j : ℕ}
    (hc : Nat.card G=2^m) (hs : Nat.card (squareCore (G ⧸ binaryThird G))=2^s)
    (hj : Nat.card (binaryThird G)=2^j) (f : G→*Vectors d) (hf : Function.Surjective f)
    (hk : f.ker=squareCore G) :
    r₂ G - (d*(d+1)/2-s) ≤ (2*s+1)*s+2*s*j := by
  have h := descendant_height hc hs hj f hf hk
  have g := allowable_dimension f hf hk hs
  have h₁ : s ≤ d*(d+1)/2 := by omega
  have hl : s*(s+1)+s*j≤(2*s+1)*s+2*s*j := by nlinarith only [Nat.zero_le (s*s),Nat.zero_le (s*j)]
  omega
end BinaryCapacity
end
section
namespace Erdos1160.DescendantTree.Actual
open BinaryFactor BinaryFactor.Cocycle BinaryFactor.Elementary CategoryTheory
open Erdos1160.DeepJacobi (binaryThird binaryThird_map)
open Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival Erdos1160Growth.LowerTriangularUpper
variable {d s : ℕ} (R : Root d s)
theorem node_capacity (i : ℕ) (x : Layer R) : height (b₀ d s) i x ≤ (2*s+1)*s+2*s*i := by
  by_cases hi : i=x.depth
  · subst i
    have hb : binaryThird x.group ≤ x.overData.ker := by
      intro u hu
      have h : x.overData u∈binaryThird R.group := binaryThird_map x.overData x.onto ⟨u,hu,rfl⟩
      rwa [R.deep_trivial] at h
    have he : x.overData.ker=binaryThird x.group := le_antisymm x.deep hb
    have hcard := ker_card_of_epi Nat.prime_two x.size R.size x.overData x.onto
    rw [he] at hcard
    simpa only [height,if_true] using BinaryCapacity.descendant_tree_cap x.size (root_width x R.deep_trivial R.width)
      hcard (toVectors R.elementary x) (R.onto.comp x.onto) (toVectors_ker R.elementary R.ker_eq x)
  · simp [height,hi]
theorem node_branch (i : ℕ) (x : Layer R) : (children i x).card ≤ 2^(b₀ d s+height (b₀ d s) i x) := by
  by_cases hi : i=x.depth
  · subst i;rw [forest_ambient];exact child_card _ _
  · classical
    simp [children,hi]
theorem node_step (i : ℕ) {x y : Layer R} (hy : y∈children i x) :
    height (b₀ d s) (i+1) y ≤ height (b₀ d s) i x+y.gain ∧
    (y.exceptional=false → height (b₀ d s) (i+1) y+1 ≤ height (b₀ d s) i x) ∧
    0 < height (b₀ d s) i x := by
  obtain ⟨hi,z,hz⟩ := mem_children.mp hy
  have hb := active_floor R x z
  have h := actual_step hy hb (fun a he=>allowed_outside R x a (he ▸ Submodule.zero_mem _))
  exact ⟨h.1,h.2,by simpa [height,hi] using Nat.sub_pos_of_lt hb⟩
end Erdos1160.DescendantTree.Actual
end
section
namespace Erdos1160.DescendantTree
def capacityUpdate (B A x : ℕ) := (A+1)*x+B
private theorem update_mono (B A : ℕ) : Monotone (capacityUpdate B A) :=
  fun _ _ h => Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _
def rough (b B A : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 1
  | k+1,i => 2^(b+B+A*i)*rough b B A k (i+1)
theorem rough_formula (b B A k i : ℕ) :
    rough b B A k i=2^(k*(b+B+A*i)+A*∑ j ∈ Finset.range k,j) := by
  induction k generalizing i with
  | zero => simp [rough]
  | succ k ih =>
    rw [rough,ih,←pow_add,Finset.sum_range_succ]
    congr 1
    ring
theorem sparse_leaf_bound {X : Type*} (ch : ℕ → X → Finset X) (height : ℕ → X → ℕ)
    (bad : ℕ → X → X → Bool) {t J L b B A K : ℕ} (hJ : J ≤ t)
    (hc : ∀ i < t, ∀x, (ch i x).card ≤ 2^(b+B+A*i))
    (hpos : ∀ i < t, ∀x, ∀y∈ch i x, 0 < height i x)
    (hgood : ∀ i < J, ∀x, ∀y∈ch i x, bad i x y=false → height (i+1) y + 1 ≤ height i x)
    (hcap : ∀ i ≤ t, ∀x,height i x ≤ B+A*i)
    (hbad : ∀ i < J, ∀x, ((ch i x).filter (fun y => bad i x y)).card * 2^L ≤ 2^(b+B+A*i))
    (hK : ∀ j < K, ((capacityUpdate B A)^[j]) B < J) (root : X) :
    2^(K*L)*leaves ch t 0 root ≤ 2^(J+t*(b+B)+A*∑ j ∈ Finset.range t,j) := by
  classical
  let f := capacityUpdate B A
  have hm : Monotone f := update_mono B A
  have aux (k i : ℕ) (hit : i+k=t) (x : X) (c : ℕ)
      (hneed : ∀ j < c,(f^[j]) (i+height i x) < J) :
      2^(c*L)*leaves ch k i x ≤ 2^(J-i)*rough b B A k i := by
    induction k generalizing i x c with
    | zero =>
      have h0 : c=0 := by
        by_contra! h
        have he := hneed 0 (by omega)
        simp only [Function.iterate_zero_apply] at he
        omega
      simp [h0,leaves,rough]; exact Nat.two_pow_pos _
    | succ k ih =>
      have hi : i < t := by omega
      let R := 2^(J-(i+1))*rough b B A k (i+1)
      let M := 2^(b+B+A*i)
      let S := ch i x
      by_cases hearly : i < J
      · have point (y : X) (hy : y∈S) : 2^(c*L)*leaves ch k (i+1) y ≤
            (if bad i x y then 2^L else 1)*R := by
          cases hflag : bad i x y with
          | false =>
            simp only [Bool.false_eq_true,if_false,one_mul]
            apply ih (i+1) (by omega) y c
            intro j hj
            have hz := hgood i hearly x y hy hflag
            exact ((hm.iterate j) (by omega : i+1+height (i+1) y ≤ i+height i x)).trans_lt (hneed j hj)
          | true =>
            simp only [if_true]
            have hx := hpos i hi x y hy
            have hz := hcap (i+1) (by omega) y
            have hh : i+1+height (i+1) y ≤ f (i+height i x) := by
              have h₁ : i+1 ≤ i+height i x := by omega
              have h₂ := Nat.mul_le_mul_left (A+1) h₁
              change _ ≤ (A+1)*(i+height i x)+B
              nlinarith only [h₂,hz]
            cases c with
            | zero =>
              have hh' := ih (i+1) (by omega) y 0 (by simp)
              exact hh'.trans (Nat.le_mul_of_pos_left _ (by positivity))
            | succ c =>
              have hh' := ih (i+1) (by omega) y c (fun j hj => by
                apply ((hm.iterate j) hh).trans_lt
                simpa only [Function.iterate_succ_apply] using hneed (j+1) (by omega))
              rw [Nat.succ_mul,pow_add,Nat.mul_comm _ (2^L),Nat.mul_assoc]
              exact Nat.mul_le_mul_left _ hh'
        have hweight : (∑ y∈S, (if bad i x y then 2^L else 1)) ≤ 2*M := by
          have heq := Finset.sum_filter_add_sum_filter_not S (fun y => bad i x y=true)
            (fun y => if bad i x y then 2^L else 1)
          have h₁ : (∑ y ∈ S.filter (fun y => bad i x y=true), (if bad i x y then 2^L else 1)) =
              (S.filter (fun y => bad i x y)).card * 2^L := by
            calc
              _ = ∑ _y ∈ S.filter (fun y => bad i x y=true), 2^L := Finset.sum_congr rfl
                (fun y hy => if_pos (Finset.mem_filter.mp hy).2)
              _ = _ := by simp
          have h₂ : (∑ y ∈ S.filter (fun y => ¬bad i x y=true), (if bad i x y then 2^L else 1)) ≤ S.card := by
            calc
              _ = ∑ _y ∈ S.filter (fun y => ¬bad i x y=true), 1 := Finset.sum_congr rfl
                (fun y hy => if_neg (Finset.mem_filter.mp hy).2)
              _ ≤ _ := by simpa using Finset.card_filter_le S (fun y => ¬bad i x y=true)
          have hm₁ : (S.filter (fun y => bad i x y)).card*2^L ≤ M := hbad i hearly x
          have hm₂ : S.card ≤ M := hc i hi x
          omega
        calc
          _ = ∑ y∈S, 2^(c*L)*leaves ch k (i+1) y := Finset.mul_sum ..
          _ ≤ ∑ y∈S, (if bad i x y then 2^L else 1)*R := Finset.sum_le_sum point
          _ = (∑ y∈S, (if bad i x y then 2^L else 1))*R := (Finset.sum_mul ..).symm
          _ ≤ (2*M)*R := Nat.mul_le_mul_right _ hweight
          _ = _ := by
            dsimp only [M,R,rough]
            rw [show J-i=(J-(i+1))+1 by omega,pow_succ]
            ring
      · have h0 : c=0 := by
          by_contra! h
          have := hneed 0 (by omega)
          simp only [Function.iterate_zero_apply] at this
          omega
        have point (y : X) (_ : y∈S) : leaves ch k (i+1) y ≤ rough b B A k (i+1) := by
          have hh := ih (i+1) (by omega) y 0 (by simp)
          simpa [Nat.sub_eq_zero_of_le (show J ≤ i+1 by omega)] using hh
        rw [h0,zero_mul,pow_zero,one_mul,Nat.sub_eq_zero_of_le (by omega : J ≤ i),pow_zero,one_mul]
        calc
          _ ≤ ∑ _y∈S, rough b B A k (i+1) := Finset.sum_le_sum point
          _ = S.card*rough b B A k (i+1) := by simp
          _ ≤ _ := Nat.mul_le_mul_right _ (hc i hi x)
  have h₀ : height 0 root ≤ B := by simpa using hcap 0 (Nat.zero_le _) root
  have hroot := aux t 0 (by simp) root K (fun j hj => by
    simpa using ((hm.iterate j) h₀).trans_lt (hK j hj))
  simpa [rough_formula,←pow_add,Nat.add_assoc] using hroot
end Erdos1160.DescendantTree
end
section
namespace Erdos1160.DescendantTree
def profilePrice (J d s t B A : ℕ) := J+(s+t)*(d*(d+1)/2)+t*B+A*∑ j∈Finset.range t,j
private theorem price_split {J m d s t B A : ℕ} (h : d+s+t=m) (hJ : J ≤ m) (hm : 1 ≤ m) :
    2*profilePrice J d s t B A ≤ (s+t)*d^2 + (2*B+2*A+4)*m^2 := by
  have hd : d ≤ m := by omega
  have hst : s+t ≤ m := by omega
  have ht : t ≤ m := by omega
  have hsq : m ≤ m^2 := by simpa [pow_two] using Nat.mul_le_mul_left m hm
  have hp := Nat.mul_le_mul_left (s+t) (Nat.div_mul_le_self (d*(d+1)) 2)
  have hp₁ := Nat.mul_le_mul hst hd
  have hp₂ := Nat.mul_le_mul_right B (ht.trans hsq)
  have hsum : (∑ j∈Finset.range t,j) ≤ m^2 := by
    calc
      _ ≤ ∑ _j∈Finset.range t,m := Finset.sum_le_sum fun i hi => (Finset.mem_range.mp hi).le.trans ht
      _ = t*m := by simp
      _ ≤ _ := by simpa [pow_two] using Nat.mul_le_mul_right m ht
  have hp₃ := Nat.mul_le_mul_left A hsum
  unfold profilePrice
  nlinarith only [hp,hp₁,hp₂,hp₃,hJ,hsq]
private theorem cubic_term (d v : ℕ) : 27*v*d^2 ≤ 4*(d+v)^3 := by
  zify
  nlinarith only [mul_nonneg (sq_nonneg ((d:ℤ)-2*v)) (show 0 ≤ 4*(d:ℤ)+v by positivity)]
private theorem small_degree_cubic {m d v : ℕ} (he : d+v=m) (hd : 2*d ≤ m) :
    8*v*d^2 ≤ m^3 := by
  have hdv : d ≤ v := by omega
  obtain ⟨w,hw⟩ := Nat.exists_eq_add_of_le hdv
  rw [←he,hw]
  nlinarith only [Nat.zero_le (w^3),Nat.zero_le (w^2*d),Nat.zero_le (w*d^2)]
private theorem small_depth_cubic {m d v : ℕ} (hd : d ≤ m) (hv : 8*v ≤ m) :
    8*v*d^2 ≤ m^3 := by
  have h := Nat.mul_le_mul hv (Nat.pow_le_pow_left hd 2)
  nlinarith only [h]
theorem sparse_margin_outside {S C m d s t : ℕ} (hsize : d+s+t=m) (hs : s ≤ S)
    (hm : 200*((2*S+1)*S+2*S+C+4) ≤ m) (hfar : 2*d ≤ m ∨ 100*t ≤ m) :
    27*(profilePrice 0 d s t ((2*S+1)*S) (2*S)+C*m^2) ≤ 2*m^3 := by
  let B := (2*S+1)*S
  let A := 2*S
  change 200*(B+A+C+4) ≤ m at hm
  have hlarge : 1 ≤ m := by omega
  have hbase := price_split (B:=B) (A:=A) hsize (Nat.zero_le _) hlarge
  have hc : 8*(s+t)*d^2 ≤ m^3 := by
    rcases hfar with h|h
    · exact small_degree_cubic (by omega) h
    · exact small_depth_cubic (by omega) (by dsimp [A] at hm; omega)
  have hgap := Nat.mul_le_mul_right (m^2) hm
  change 27*(profilePrice 0 d s t B A+C*m^2) ≤ _
  nlinarith only [hbase,hc,hgap,Nat.zero_le (m^2)]
private theorem floor_penalty {d m : ℕ} (hm : m ≤ 2*d) (hd : 4 ≤ d) : m^2 ≤ 32*(d^2/4) := by
  have h := Nat.mul_le_mul hm hm
  have hdiv : d^2 ≤ 4*(d^2/4)+3 := by omega
  have hs := Nat.mul_le_mul hd hd
  nlinarith only [h,hdiv,hs]
theorem sparse_margin_central (S C : ℕ) :
    ∃ M K : ℕ, ∀ {m d s t : ℕ}, M ≤ m → d+s+t=m → s ≤ S → m ≤ 2*d → m ≤ 100*t →
      let B := (2*S+1)*S
      let A := 2*S
      let J := m/100
      J ≤ t ∧ 8*J ≤ d ∧ (∀ j < K,((capacityUpdate B A)^[j]) B < J) ∧
        27*(profilePrice J d s t B A+C*m^2) ≤ 2*m^3+27*(K*(d^2/4)) := by
  let B := (2*S+1)*S
  let A := 2*S
  let K := 32*(B+A+C+2)
  let f := capacityUpdate B A
  let M := 100*((f^[K]) B + 1)+1000
  refine ⟨M,K,?_⟩
  intro m d s t hm he _ hd ht
  dsimp only
  have hM : 100*((f^[K]) B+1)+1000 ≤ m := hm
  have hmpos : 1 ≤ m := by omega
  refine ⟨by omega,by omega,?_,?_⟩
  · intro j hj
    have hf : id ≤ f := fun x => by change x≤(A+1)*x+B; nlinarith only [Nat.zero_le (A*x),Nat.zero_le B]
    have hmono : (f^[j]) B ≤ (f^[K]) B := Function.monotone_iterate_of_id_le hf hj.le B
    change (f^[j]) B < m/100
    exact hmono.trans_lt (by omega)
  · have hp := price_split (B:=B) (A:=A) he (show m/100 ≤ m by omega) hmpos
    have hc := cubic_term d (s+t)
    rw [←Nat.add_assoc,he] at hc
    have hq := floor_penalty hd (by omega)
    have hg := Nat.mul_le_mul_left (B+A+C+2) hq
    change 27*(profilePrice (m/100) d s t B A+C*m^2) ≤ 2*m^3+27*(K*(d^2/4))
    dsimp only [K]
    nlinarith only [hp,hc,hg]
end Erdos1160.DescendantTree
end
section
namespace Erdos1160.DescendantTree
private theorem unweighted {X : Type*} (ch : ℕ→X→Finset X) {m b B A : ℕ}
    (hb : ∀ i < m, ∀x, (ch i x).card ≤ 2^(b+B+A*i)) (k i : ℕ) (hi : i+k=m) (x : X) :
    leaves ch k i x ≤ rough b B A k i := by
  induction k generalizing i x with
  | zero => simp [leaves,rough]
  | succ k ih =>
    calc
      _ ≤ ∑ _y ∈ ch i x, rough b B A k (i+1) := Finset.sum_le_sum (fun y _ => ih (i+1) (by omega) y)
      _ = (ch i x).card*rough b B A k (i+1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (hb i (by omega) x)
private theorem sum_root_price {X : Type*} (roots : Finset X) (f : X→ℕ) {q D s J t B A : ℕ}
    (hR : roots.card ≤ 2^(s*D)) (hf : ∀x∈roots, 2^q*f x ≤ 2^(J+t*(D+B)+A*∑ j∈Finset.range t,j)) :
    2^q*(∑ x∈roots,f x) ≤ 2^(J+(s+t)*D+t*B+A*∑ j∈Finset.range t,j) := by
  let L := J+t*(D+B)+A*∑ j∈Finset.range t,j
  calc
    _ = ∑ x ∈ roots, 2^q*f x := Finset.mul_sum ..
    _ ≤ ∑ _x ∈ roots, 2^L := Finset.sum_le_sum hf
    _ = roots.card*2^L := by simp
    _ ≤ 2^(s*D)*2^L := Nat.mul_le_mul_right _ hR
    _ = _ := by rw [←pow_add]; dsimp only [L]; congr 1; ring
private theorem absorb_price {q Y P C m : ℕ} (hp : 2^q*Y ≤ 2^P)
    (ha : 27*(P+C*m^2) ≤ 2*m^3+27*q) : Y^27*2^(27*C*m^2) ≤ 2^(2*m^3) := by
  apply Nat.le_of_mul_le_mul_right (c:=2^(q*27)) _ (by positivity)
  calc
    _ = (2^q*Y)^27*2^(27*C*m^2) := by rw [mul_pow,←pow_mul]; ring
    _ ≤ (2^P)^27*2^(27*C*m^2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hp 27)
    _ = 2^(P*27+27*C*m^2) := by rw [←pow_mul,←pow_add]
    _ ≤ 2^(2*m^3+q*27) := Nat.pow_le_pow_right (by decide) (by linarith only [ha])
    _ = _ := pow_add _ _ _
theorem bounded_root_profiles (S C : ℕ) : ∃ M : ℕ, ∀ (m d s t : ℕ), M ≤ m → d+s+t=m → s ≤ S →
    ∀ {X : Type*} (roots : Finset X) (ch : ℕ→X→Finset X) (height : ℕ→X→ℕ) (bad : ℕ→X→X→Bool),
    let D := d*(d+1)/2
    let B := (2*S+1)*S
    let A := 2*S
    roots.card ≤ 2^(s*D) →
    (∀ i < t, ∀x, (ch i x).card ≤ 2^(D+B+A*i)) →
    (∀ i < t, ∀x, ∀y∈ch i x, 0 < height i x) →
    (∀ i < t, 8*i ≤ d → ∀x, ∀y∈ch i x, bad i x y=false → height (i+1) y+1 ≤ height i x) →
    (∀ i ≤ t, ∀x, height i x ≤ B+A*i) →
    (64 ≤ d → 16*s ≤ d → ∀ i < t, 8*i ≤ d → ∀x, ((ch i x).filter (fun y => bad i x y)).card *
      2^(d^2/4) ≤ 2^(D+B+A*i)) →
      (∑ x∈roots, leaves ch t 0 x)^27 * 2^(27*C*m^2) ≤ 2^(2*m^3) := by
  obtain ⟨M,K,hmar⟩ := sparse_margin_central S C
  let B := (2*S+1)*S
  let A := 2*S
  refine ⟨max M (200*(B+A+C+4)),?_⟩
  intro m d s t hsz he hs X roots ch height bad
  dsimp only
  intro hR htree hpos hord hcap hbad
  let D := d*(d+1)/2
  have hM : M ≤ m := (le_max_left ..).trans hsz
  have hlarge : 200*(B+A+C+4) ≤ m := (le_max_right ..).trans hsz
  by_cases hfar : 2*d ≤ m ∨ 100*t ≤ m
  · have ha := sparse_margin_outside he hs hlarge hfar
    apply absorb_price (q:=0) (P:=profilePrice 0 d s t B A) _ (by simpa using ha)
    apply sum_root_price (q:=0) roots _ hR
    intro x _
    have hh := unweighted (b:=D) (B:=B) (A:=A) ch htree t 0 (by omega) x
    simpa [rough_formula] using hh
  · have hdeg : m ≤ 2*d := by omega
    have hdepth : m ≤ 100*t := by omega
    obtain ⟨hJ,hJd,hK,ha⟩ := hmar hM he hs hdeg hdepth
    let J := m/100
    have gg : 64 ≤ d ∧ 16*s ≤ d := by dsimp [A] at hlarge; omega
    apply absorb_price (q:=K*(d^2/4)) (P:=profilePrice J d s t B A) _ ha
    apply sum_root_price roots _ hR
    intro x _
    apply sparse_leaf_bound ch height bad hJ htree hpos _ hcap _ hK x
    · intro i hi
      exact hord i (hi.trans_le hJ) (by omega)
    · intro i hi
      exact hbad gg.1 gg.2 i (hi.trans_le hJ) (by omega)
end Erdos1160.DescendantTree
end
section
namespace Erdos1160.DescendantTree.Actual
open BinaryFactor BinaryFactor.Cocycle BinaryFactor.Elementary CategoryTheory
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
theorem rare_root (S C : ℕ) : ∃M : ℕ,∀m d s t : ℕ, M ≤ m → d+s+t=m → s ≤ S → ∀R : Root d s,
    (descendants R.group (d+s) t).ncard^27*2^(27*C*m^2) ≤ 2^(2*m^3) := by
  obtain ⟨M,all⟩ := bounded_root_profiles S C
  refine ⟨M,?_⟩
  intro m d s t hm he hs R
  classical
  let D := d*(d+1)/2
  let B := (2*S+1)*S
  let A := 2*S
  let root := initial R.size
  have hb : b₀ d s ≤ D := Nat.sub_le ..
  have cap (i : ℕ) (x : Layer R) : height (b₀ d s) i x ≤ B+A*i := by
    have h₁ := Nat.mul_le_mul (show 2*s+1 ≤ 2*S+1 by omega) hs
    have h₂ := Nat.mul_le_mul_right i (show 2*s ≤ 2*S by omega)
    exact (node_capacity R i x).trans (Nat.add_le_add h₁ h₂)
  have price (i : ℕ) (x : Layer R) : b₀ d s+height (b₀ d s) i x ≤ D+B+A*i := by
    have := cap i x;omega
  have b := all m d s t hm he hs ({root} : Finset (Layer R)) children (height (b₀ d s)) (fun _ _ y=>y.exceptional)
    (by simp only [Finset.card_singleton];exact Nat.two_pow_pos _) (fun i hi x=>(node_branch R i x).trans (Nat.pow_le_pow_right (by decide) (price i x)))
    (fun i _ x y hy=>(node_step R i hy).2.2)
    (fun i _ _ x y hy=>(node_step R i hy).2.1) (fun i _ x=>cap i x)
    (fun hd hs i _ hi x=>(local_rare R x hd hs hi).trans (Nat.pow_le_pow_right (by decide) (price i x)))
  simp only [Finset.sum_singleton] at b
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (count_le_leaves R.size t) 27)).trans b
def rootLabels (d s : ℕ) : Set IsoClass := Set.range (fun R : Root d s=>Quotient.mk _ R.group)
theorem rootLabels_subset (d s : ℕ) : rootLabels d s ⊆ Erdos1160Growth.LowerTriangularUpper.frattiniClasses d s := by
  rintro _ ⟨R,rfl⟩
  refine ⟨R.group,?_,rfl⟩
  change frattini R.group ≤ Subgroup.center R.group ∧ _
  rw [frattini_eq_squareCore R.size]
  have ofThird (x : R.group) (h : x∈binaryThird R.group) : x=1 := by rwa [R.deep_trivial] at h
  refine ⟨?_,?_,R.width,?_⟩
  · intro u hu
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact (commutatorElement_eq_one_iff_mul_comm.mp (ofThird _ (Subgroup.subset_closure
      (Or.inr ⟨(⟨u,hu⟩,y),rfl⟩)))).symm
  · intro u;apply Subtype.ext
    exact ofThird _ (Subgroup.subset_closure (Or.inl ⟨u,rfl⟩))
  · have h := (squareCore R.group).index_mul_card
    rw [R.width,R.size,pow_add] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h
theorem count_rootLabels (d s : ℕ) : (rootLabels d s).ncard ≤ 2^(s*(d*(d+1)/2)) := by
  have sub := ((((rootLabels_subset d s).trans (frattiniClasses_subset d s)).trans (squareCoreClasses_subset d s)).trans
    (intrinsicClasses_subset d s)).trans (bilinearClasses_subset d s)
  have h := triangular_class_upper d s
  rw [←card_change] at h
  rw [←coeff_identity]
  exact (Set.ncard_le_ncard sub (classes_finite d s)).trans
    ((Nat.le_mul_of_pos_right _ (Nat.card_pos (α:=Change s))).trans h)
theorem rootLabels_finite (d s : ℕ) : (rootLabels d s).Finite :=
  (frattiniClasses_finite d s).subset (rootLabels_subset d s)
theorem descendants_finite (Q : Type) [Group Q] [Finite Q] {m : ℕ} (hQ : Nat.card Q=2^m) (t : ℕ) :
    (descendants Q m t).Finite := by
  classical
  let v := initial hQ
  apply (terminals label children t 0 v).finite_toSet.subset
  rintro _ ⟨G,hG,⟨f,hf,hk⟩,rfl⟩
  exact covered t v hG f hf hk
theorem transfer {Q Q' : FiniteGrp.{0}} (h : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) Q=Quotient.mk _ Q')
    (m t : ℕ) : descendants Q m t ⊆ descendants Q' m t := by
  obtain ⟨e⟩ := Quotient.exact h
  let i := ((inducedFunctor FiniteGrp.toGrp).mapIso e).groupIsoToMulEquiv
  rintro _ ⟨G,hG,⟨f,hf,hk⟩,rfl⟩
  refine ⟨G,hG,⟨i.toMonoidHom.comp f,i.surjective.comp hf,?_⟩,rfl⟩
  intro x hx
  exact hk (i.injective ((show i (f x)=1 from hx).trans i.map_one.symm))
noncomputable def reprRoot {d s : ℕ} (z : rootLabels d s) : Root d s := z.property.choose
def profile (d s t : ℕ) : Set IsoClass := ⋃ z : rootLabels d s,descendants (reprRoot z).group (d+s) t
theorem mem_profile (d s t : ℕ) (R : Root d s) : descendants R.group (d+s) t ⊆ profile d s t := by
  let z : rootLabels d s := ⟨Quotient.mk _ R.group,⟨R,rfl⟩⟩
  let h := transfer z.property.choose_spec.symm (d+s) t
  intro u hu
  exact Set.mem_iUnion.mpr ⟨z,h hu⟩
theorem profile_finite (d s t : ℕ) : (profile d s t).Finite := by
  letI := (rootLabels_finite d s).to_subtype
  exact Set.finite_iUnion (fun z=>descendants_finite _ (reprRoot z).size t)
theorem rare_profile (S C : ℕ) : ∃M : ℕ,∀m d s t : ℕ,M ≤ m → d+s+t=m → s ≤ S →
    (profile d s t).ncard^27*2^(27*C*m^2) ≤ 2^(2*m^3) := by
  obtain ⟨M,per⟩ := rare_root S (C+S)
  refine ⟨max M 1,?_⟩
  intro m d s t hm he hs
  have hM := (le_max_left ..).trans hm
  have hm' : 1 ≤ m := (le_max_right ..).trans hm
  classical
  letI := (rootLabels_finite d s).fintype
  let size (z : rootLabels d s) := (descendants (reprRoot z).group (d+s) t).ncard
  by_cases hn : Nonempty (rootLabels d s)
  · obtain ⟨z,_,hz⟩ := Finset.exists_max_image (Finset.univ : Finset (rootLabels d s)) size
      ⟨hn.some,Finset.mem_univ _⟩
    have le := Set.ncard_iUnion_le_of_fintype (fun z : rootLabels d s=>descendants (reprRoot z).group (d+s) t)
    have sum := Finset.sum_le_card_nsmul (Finset.univ : Finset (rootLabels d s)) size (size z) (fun w hw=>hz w hw)
    rw [Finset.card_univ,Set.fintypeCard_eq_ncard,smul_eq_mul] at sum
    have hb : (profile d s t).ncard ≤ 2^(S*m^2)*size z := by
      have hd : d ≤ m := by omega
      have h₁ := Nat.mul_le_mul hd (Nat.succ_le_succ hd)
      change d*(d+1) ≤ m*(m+1) at h₁
      have h₂ : m*(m+1) ≤ 2*m^2 := by nlinarith only [Nat.mul_le_mul_left m hm']
      have hD : d*(d+1)/2 ≤ m^2 := by omega
      exact (le.trans sum).trans (Nat.mul_le_mul_right _ ((count_rootLabels d s).trans
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hs hD))))
    apply (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hb 27)).trans
    have hp := per m d s t hM he hs (reprRoot z)
    change size z^27*2^(27*(C+S)*m^2) ≤ 2^(2*m^3) at hp
    calc
      _ = size z^27*2^(27*(C+S)*m^2) := by
        rw [mul_pow,←pow_mul,Nat.mul_comm (2^_) (size z^27),Nat.mul_assoc,←pow_add]
        congr 2 <;> ring
      _ ≤ _ := hp
  · letI : IsEmpty (rootLabels d s) := not_nonempty_iff.mp hn
    simp [profile]
end Erdos1160.DescendantTree.Actual
end
section
namespace Erdos1160.DescendantTree.Actual
open BinaryFactor BinaryFactor.Elementary CategoryTheory
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival Erdos1160Growth.LowerTriangularUpper
def boundedWidth (m S : ℕ) : Set IsoClass :=
  {z | ∃G : FiniteGrp.{0},Nat.card G=2^m ∧ Nat.card (squareCore (G ⧸ binaryThird G)) ≤ 2^S ∧ Quotient.mk _ G=z}
theorem decompose {m S : ℕ} (z : IsoClass) (hz : z∈boundedWidth m S) :
    ∃ d s t, d+s+t=m ∧ s ≤ S ∧ z∈profile d s t := by
  obtain ⟨G,hG,hS,rfl⟩ := hz
  let K := binaryThird G
  let Q := G ⧸ K
  let q := QuotientGroup.mk' K
  let π := QuotientGroup.mk' (squareCore Q)
  have sq := QuotientGroup.mk'_surjective K
  have sπ := QuotientGroup.mk'_surjective (squareCore Q)
  have h₂ := IsPGroup.of_card hG
  obtain ⟨t,ht⟩ := (h₂.to_subgroup K).exists_card_eq
  have hQ := h₂.to_quotient K
  obtain ⟨s,hs⟩ := (hQ.to_subgroup (squareCore Q)).exists_card_eq
  obtain ⟨d,hd⟩ := (hQ.to_quotient (squareCore Q)).exists_card_eq
  have sizeQ : Nat.card Q=2^(d+s) := by
    have h := (squareCore Q).card_eq_card_quotient_mul_card_subgroup
    rw [hd,hs,←pow_add] at h;exact h
  have sum : d+s+t=m := by
    have h := K.card_eq_card_quotient_mul_card_subgroup
    change Nat.card G=Nat.card Q*Nat.card K at h
    rw [hG,sizeQ,ht,←pow_add] at h
    exact (Nat.pow_right_injective (by decide : 1 < 2) h).symm
  have sq₂ (u : Q ⧸ squareCore Q) : u*u=1 := by
    obtain ⟨v,rfl⟩ := sπ u
    change π v*π v=1
    rw [←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨v,rfl⟩)
  obtain ⟨e⟩ := exist_elementary_coords sq₂ hd
  let p := e.toMonoidHom.comp π
  have hp : p.ker=squareCore Q := by
    rw [←QuotientGroup.ker_mk' (squareCore Q)]
    ext x
    change e (π x)=1 ↔ π x=1
    rw [←e.map_one,e.injective.eq_iff]
  have bot : binaryThird Q=⊥ :=
    (binaryThird_map_eq q sq).symm.trans ((Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' _).ge)
  let R : Root d s := ⟨FiniteGrp.of Q,sizeQ,p,e.surjective.comp sπ,hp,bot,hs⟩
  have le : 2^s ≤ 2^S := hs ▸ hS
  refine ⟨d,s,t,sum,(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp le,mem_profile d s t R ?_⟩
  exact ⟨G,sum ▸ hG,⟨q,sq,(QuotientGroup.ker_mk' _).le⟩,rfl⟩
abbrev ProfileKey (m S : ℕ) := {z : Fin (m+1) × Fin (m+1) // z.1.val+z.2.val ≤ m ∧ z.2.val ≤ S}
def selected {m S : ℕ} (key : ProfileKey m S) :=
  profile key.val.1.val key.val.2.val (m-(key.val.1.val+key.val.2.val))
theorem profile_cover (m S : ℕ) : boundedWidth m S ⊆ ⋃ k : ProfileKey m S, selected k := by
  intro z hz
  obtain ⟨d,s,t,h,hs,hm⟩ := decompose z hz
  let k : ProfileKey m S := ⟨(⟨d,by omega⟩,⟨s,by omega⟩),by dsimp;omega,hs⟩
  apply Set.mem_iUnion.mpr
  refine ⟨k,?_⟩
  change z∈profile d s (m-(d+s))
  rwa [show m-(d+s)=t by omega]
theorem su_xia_5_7_quadratic (S C : ℕ) : ∃M : ℕ,∀m ≥ M,
    (boundedWidth m S).ncard^27*2^(27*C*m^2) ≤ 2^(2*m^3) := by
  obtain ⟨M,hM⟩ := rare_profile S (C+1)
  refine ⟨max M 2,?_⟩
  intro m hm
  classical
  have h₂ : 2 ≤ m := (le_max_right ..).trans hm
  have hM' : M ≤ m := (le_max_left ..).trans hm
  let I := ProfileKey m S
  let k0 : I := ⟨(0,0),by simp⟩
  let price (k : I) := (selected k).ncard
  obtain ⟨k,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset I) price ⟨k0,Finset.mem_univ _⟩
  have hcount : (boundedWidth m S).ncard ≤ 2^(m^2)*price k := by
    have sum := Finset.sum_le_card_nsmul (Finset.univ : Finset I) price _ (fun w hw=>hmax w hw)
    rw [Finset.card_univ,←Nat.card_eq_fintype_card,smul_eq_mul] at sum
    have card := Nat.card_le_card_of_injective (Subtype.val : I→Fin (m+1)×Fin (m+1)) Subtype.val_injective
    rw [Nat.card_prod,Nat.card_fin] at card
    have rank : m+1 ≤ 2^m := by exact (Nat.lt_two_pow_self (n:=m))
    have keycard : Nat.card I ≤ 2^(m^2) := by
      have h := Nat.mul_le_mul rank rank
      rw [←pow_add] at h
      exact (card.trans h).trans (Nat.pow_le_pow_right (by decide) (by
        nlinarith only [Nat.mul_le_mul_right m h₂]))
    have finite (k : I) : (selected k).Finite := profile_finite ..
    exact (((Set.ncard_le_ncard (profile_cover m S) (Set.finite_iUnion finite)).trans
      (Set.ncard_iUnion_le_of_fintype selected)).trans sum).trans
        (Nat.mul_le_mul_right _ keycard)
  have localBd := hM' |> hM m k.val.1.val k.val.2.val (m-(k.val.1.val+k.val.2.val))
  have hp := localBd (by have := k.property.1;omega) k.property.2
  change price k^27 *2^(27*(C+1)*m^2)≤_ at hp
  apply (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcount 27)).trans
  calc
    _ = price k^27*2^(27*(C+1)*m^2) := by
      rw [mul_pow,←pow_mul,Nat.mul_comm (2^_) (price k^27),Nat.mul_assoc,←pow_add]
      congr 2 <;> ring
    _ ≤ _ := hp
end Erdos1160.DescendantTree.Actual
end
section
namespace Erdos1160.DescendantTree.Actual
open CategoryTheory
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160Growth.LowerTriangularUpper (squareCore)
open Erdos1160.CentralLifts.Survival (binaryThird_le_squares)
theorem squareCore_card_product (G : Type) [Group G] :
    Nat.card (squareCore G)=Nat.card (squareCore (G ⧸ binaryThird G))*Nat.card (binaryThird G) := by
  let q := QuotientGroup.mk' (binaryThird G)
  rw [←CentralKernelCount.squareCore_map q (QuotientGroup.mk'_surjective _),←Subgroup.relIndex_ker,
    QuotientGroup.ker_mk']
  rw [←Nat.card_congr (Subgroup.subgroupOfEquivOfLe (binaryThird_le_squares G)).toEquiv]
  exact ((binaryThird G).subgroupOf (squareCore G)).index_mul_card.symm
def population (m S : ℕ) :=
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) := Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G=2^m}
  {c : A | let G := c.property.choose
           Nat.card (squareCore G) ≤ 2^S*Nat.card (binaryThird G)}
theorem population_bound (S : ℕ) : ∀ᶠ m : ℕ in Filter.atTop,
    (4*(population m S).ncard)^27*2^(9*m^2) ≤ 2^(2*m^3) := by
  obtain ⟨M,hM⟩ := su_xia_5_7_quadratic S 1
  apply Filter.eventually_atTop.mpr
  refine ⟨max M 2,fun m hm=>?_⟩
  have finite : (boundedWidth m S).Finite := by
    apply (Erdos1160.Tables.orderClasses_finite (2^m)).subset
    rintro c ⟨G,hG,_,he⟩
    exact ⟨G,hG,he⟩
  letI := finite.to_subtype
  let inj (c : population m S) : boundedWidth m S := by
    let G := c.val.property.choose
    have spec := c.val.property.choose_spec
    have h : Nat.card (squareCore G) ≤ 2^S*Nat.card (binaryThird G) := c.property
    rw [squareCore_card_product] at h
    exact ⟨c.val.val,G,spec.1,Nat.le_of_mul_le_mul_right h Nat.card_pos,spec.2⟩
  have hi : Function.Injective inj := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun w : boundedWidth m S=>w.val) he))
  have le := Nat.card_le_card_of_injective inj hi
  rw [Nat.card_coe_set_eq,Nat.card_coe_set_eq] at le
  have m2 : 2 ≤ m := (le_max_right ..).trans hm
  have power : 54+9*m^2 ≤ 27*1*m^2 := by nlinarith only [Nat.mul_le_mul m2 m2]
  have hm' := hM m ((le_max_left ..).trans hm)
  apply (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left 4 le) 27)).trans
  rw [mul_pow,Nat.mul_comm (4^27),Nat.mul_assoc,show 4^27=2^54 by decide,←pow_add]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) power)).trans hm'
end Erdos1160.DescendantTree.Actual
end
end PartUH2
section PartUH4
section
namespace Erdos1160.Tables
open CategoryTheory
end Erdos1160.Tables
end
section
namespace Erdos1160.CentralLifts
open scoped commutatorElement
variable {I J : Type} {p : ℕ}
abbrev Grp (R : J → FreeGroup I) := PresentedGroup (Set.range R)
def newRel (R : J → FreeGroup I) (c : J → Fin p) : Unit ⊕ (I ⊕ J) → FreeGroup (Option I)
  | .inl _ => FreeGroup.of none ^ p
  | .inr (.inl i) => ⁅FreeGroup.of (none : Option I), FreeGroup.of (some i)⁆
  | .inr (.inr j) => FreeGroup.map some (R j) * (FreeGroup.of none ^ (c j).val)⁻¹
abbrev Lift (R : J → FreeGroup I) (c : J → Fin p) := Grp (newRel R c)
def z (R : J → FreeGroup I) (c : J → Fin p) : Lift R c := PresentedGroup.of none
def old (R : J → FreeGroup I) (c : J → Fin p) (i : I) : Lift R c := PresentedGroup.of (some i)
theorem relation {A B : Type} (S : B → FreeGroup A) (j : B) :
    PresentedGroup.mk (Set.range S) (S j) = 1 :=
  PresentedGroup.one_of_mem ⟨j,rfl⟩
theorem z_pow (R : J → FreeGroup I) (c : J → Fin p) : z R c ^ p = 1 := by
  simpa only [newRel, map_pow, z, PresentedGroup.of] using relation (newRel R c) (.inl ())
theorem z_commutes_old (R : J → FreeGroup I) (c : J → Fin p) (i : I) :
    Commute (z R c) (old R c i) := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa only [newRel, map_commutatorElement, z, old, PresentedGroup.of] using
    relation (newRel R c) (.inr (.inl i))
theorem z_central (R : J → FreeGroup I) (c : J → Fin p) :
    z R c ∈ Subgroup.center (Lift R c) := by
  rw [Subgroup.center_eq_iInf (PresentedGroup.closure_range_of (Set.range (newRel R c)))]
  simp only [Subgroup.mem_iInf, Subgroup.mem_centralizer_singleton_iff]
  rintro _ ⟨_ | i,rfl⟩
  · rfl
  · exact (z_commutes_old R c i).eq
instance z_normal (R : J → FreeGroup I) (c : J → Fin p) :
    (Subgroup.zpowers (z R c)).Normal where
  conj_mem n hn g := by
    have hcenter : n ∈ Subgroup.center (Lift R c) := (Subgroup.zpowers_le.mpr (z_central R c)) hn
    have hc := Subgroup.mem_center_iff.mp hcenter g
    rwa [hc, mul_inv_cancel_right]
def inc (R : J → FreeGroup I) (c : J → Fin p) : FreeGroup I →* Lift R c :=
  (PresentedGroup.mk (Set.range (newRel R c))).comp (FreeGroup.map some)
theorem inc_rel (R : J → FreeGroup I) (c : J → Fin p) (j : J) :
    inc R c (R j) = z R c ^ (c j).val := by
  apply eq_of_mul_inv_eq_one
  simpa only [newRel, map_mul, map_inv, map_pow, inc, MonoidHom.comp_apply, z, PresentedGroup.of]
    using relation (newRel R c) (.inr (.inr j))
def quotientMap (R : J → FreeGroup I) (c : J → Fin p) :
    Grp R →* (Lift R c ⧸ Subgroup.zpowers (z R c)) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp (inc R c)) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j,rfl⟩
    change (QuotientGroup.mk' _) (inc R c (R j)) = 1
    rw [inc_rel, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
theorem quotientMap_old (R : J → FreeGroup I) (c : J → Fin p) (i : I) :
    quotientMap R c (PresentedGroup.of i) = (QuotientGroup.mk' _) (old R c i) := by rfl
theorem quotientMap_surjective (R : J → FreeGroup I) (c : J → Fin p) :
    Function.Surjective (quotientMap R c) := by
  intro y
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers (z R c)) y
  change (QuotientGroup.mk' _) x ∈ (quotientMap R c).range
  have h : (quotientMap R c).range.comap (QuotientGroup.mk' (Subgroup.zpowers (z R c))) = ⊤ := by
    apply top_unique
    rw [← PresentedGroup.closure_range_of (Set.range (newRel R c))]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨_ | i,rfl⟩
    · change (QuotientGroup.mk' (Subgroup.zpowers (z R c))) (z R c) ∈ (quotientMap R c).range
      have hz : (QuotientGroup.mk' (Subgroup.zpowers (z R c))) (z R c) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
      rw [hz]
      exact Subgroup.one_mem _
    · exact ⟨PresentedGroup.of i,quotientMap_old R c i⟩
  exact (show x ∈ (quotientMap R c).range.comap (QuotientGroup.mk' _) by rw [h]; trivial)
end Erdos1160.CentralLifts
end
section
namespace Erdos1160.CentralLifts
open scoped commutatorElement
variable {I J : Type} {p : ℕ}
end Erdos1160.CentralLifts
end
section
namespace Erdos1160.CentralLifts
open CategoryTheory
variable {p m : ℕ} {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q]
end Erdos1160.CentralLifts
end
section
namespace Erdos1160.CentralLifts
variable {I J : Type} {p : ℕ}
def substitute (w : FreeGroup I) : FreeGroup (Option I) →* FreeGroup I :=
  FreeGroup.lift (fun o => o.elim w FreeGroup.of)
def reducedRel (R : J → FreeGroup I) (c : J → Fin p) (w : FreeGroup I) :
    Unit ⊕ (I ⊕ J) → FreeGroup I := fun r => substitute w (newRel R c r)
def contract (R : J → FreeGroup I) (c : J → Fin p) (w : FreeGroup I) :
    Lift R c →* Grp (reducedRel R c w) :=
  PresentedGroup.map (substitute w) (by rintro _ ⟨r,rfl⟩; exact ⟨r,rfl⟩)
lemma contract_mk (R : J → FreeGroup I) (c : J → Fin p) (w : FreeGroup I) (a : FreeGroup (Option I)) :
    contract R c w (PresentedGroup.mk _ a) = PresentedGroup.mk _ (substitute w a) := rfl
lemma contract_surj (R : J → FreeGroup I) (c : J → Fin p) (w : FreeGroup I) :
    Function.Surjective (contract R c w) := by
  have hinv : (substitute w).comp (FreeGroup.map some) = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ (fun i => by simp [substitute])
  intro x
  obtain ⟨a,rfl⟩ := PresentedGroup.mk_surjective _ x
  refine ⟨PresentedGroup.mk _ (FreeGroup.map some a),?_⟩
  rw [contract_mk]
  exact congrArg (PresentedGroup.mk _) (DFunLike.congr_fun hinv a)
end Erdos1160.CentralLifts
end
section
namespace Erdos1160.CentralLifts.Survival
abbrev Twist (r : ℕ) := {c : Fin r → Fin 2 // c ≠ 0}
theorem card_twist (r : ℕ) : Nat.card (Twist r) = 2^r-1 := by
  classical
  change Nat.card {c : Fin r → Fin 2 // ¬ c=0} = _
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp
theorem exists_one {r : ℕ} (c : Twist r) : ∃ j, (c.val j).val=1 := by
  by_contra! h
  apply c.property
  funext j
  apply Fin.ext
  change (c.val j).val=0
  have := h j
  have := (c.val j).isLt
  omega
noncomputable def pivot {r : ℕ} (c : Twist r) : Fin r := (exists_one c).choose
theorem pivot_eq {r : ℕ} (c : Twist r) : (c.val (pivot c)).val = 1 := (exists_one c).choose_spec
abbrev Kept (d : ℕ) {r : ℕ} (c : Twist r) := Unit ⊕ (Fin d ⊕ {j : Fin r // j ≠ pivot c})
theorem kept_card (d : ℕ) {r : ℕ} (c : Twist r) : Fintype.card (Kept d c) = r+d := by
  classical
  have h := (pivot c).isLt
  change Fintype.card (Unit ⊕ (Fin d ⊕ {j : Fin r // ¬j=pivot c}))=_
  rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_subtype_compl]
  simp only [Fintype.card_unit,Fintype.card_fin,Fintype.card_subtype_eq]
  omega
def intoFull {d r : ℕ} (c : Twist r) : Kept d c → Unit ⊕ (Fin d ⊕ Fin r)
  | .inl u => .inl u
  | .inr (.inl i) => .inr (.inl i)
  | .inr (.inr j) => .inr (.inr j.val)
noncomputable def shortRel {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    Fin (r+d) → FreeGroup (Fin d) := fun j =>
  reducedRel R c.val (R (pivot c)) (intoFull c ((Fintype.equivFinOfCardEq (kept_card d c)).symm j))
theorem pivot_relation {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    reducedRel R c.val (R (pivot c)) (.inr (.inr (pivot c))) = 1 := by
  have h : (substitute (R (pivot c))).comp (FreeGroup.map some) = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ (fun i => by simp [substitute])
  have inc (w : FreeGroup (Fin d)) : substitute (R (pivot c)) (FreeGroup.map some w)=w :=
    DFunLike.congr_fun h w
  simp only [reducedRel,newRel,pivot_eq,pow_one,map_mul,map_inv,inc]
  simp [substitute]
theorem closure_short {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    Subgroup.normalClosure (Set.range (reducedRel R c.val (R (pivot c)))) =
      Subgroup.normalClosure (Set.range (shortRel R c)) := by
  let e := Fintype.equivFinOfCardEq (kept_card d c)
  have mem (j : Kept d c) : reducedRel R c.val (R (pivot c)) (intoFull c j) ∈
      Subgroup.normalClosure (Set.range (shortRel R c)) := by
    apply Subgroup.subset_normalClosure
    exact ⟨e j,by simp [shortRel,e]⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j,rfl⟩
    rcases j with u | (i | j)
    · exact mem (.inl u)
    · exact mem (.inr (.inl i))
    · by_cases he : j=pivot c
      · subst j; rw [pivot_relation]; exact Subgroup.one_mem _
      · exact mem (.inr (.inr ⟨j,he⟩))
  · apply Subgroup.normalClosure_mono
    rintro _ ⟨j,rfl⟩
    exact ⟨_,rfl⟩
noncomputable def shortIso {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    Grp (reducedRel R c.val (R (pivot c))) ≃* Grp (shortRel R c) :=
  QuotientGroup.quotientMulEquivOfEq (closure_short R c)
noncomputable def contractShort {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    Lift R c.val →* Grp (shortRel R c) := (shortIso R c).toMonoidHom.comp (contract R c.val (R (pivot c)))
theorem contractShort_surj {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    Function.Surjective (contractShort R c) := (shortIso R c).surjective.comp (contract_surj R c.val (R (pivot c)))
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.CentralLifts.Survival
open scoped commutatorElement
variable {G H : Type} [Group G] [Group H] [Finite G] [Finite H] {d r : ℕ}
omit [Finite H] in
theorem onto_lifts {F : Type} [Group F] (q : G →* H) (hΦ : q.ker ≤ frattini G)
    (x : F →* G) (h : Function.Surjective (q.comp x)) : Function.Surjective x := by
  apply MonoidHom.range_eq_top.mp
  apply frattini_nongenerating
  apply top_unique
  intro g _
  obtain ⟨w,hw⟩ := h (q g)
  have hd : g*(x w)⁻¹ ∈ q.ker := by
    change q (g*(x w)⁻¹)=1
    rw [map_mul,map_inv,←show q (x w) = q g from hw,mul_inv_cancel]
  have h' := (x.range ⊔ frattini G).mul_mem (show g*(x w)⁻¹ ∈ x.range ⊔ frattini G from (show frattini G ≤ x.range ⊔ frattini G from le_sup_right) (hΦ hd))
    (show x w ∈ x.range ⊔ frattini G from (show x.range ≤ x.range ⊔ frattini G from le_sup_left) ⟨w,rfl⟩)
  simpa using h'
omit [Finite H] in
theorem child_cover_of_no_epi (R : Fin r → FreeGroup (Fin d)) (g : Grp R →* H)
    (hg : Function.Surjective g) (no_epi : ∀v : Grp R →* G,¬Function.Surjective v)
    (q : G →* H) (hq : Function.Surjective q) (hΦ : q.ker ≤ frattini G)
    (u : G) (ho : orderOf u=2) (hz : u ∈ Subgroup.center G) (hker : q.ker = Subgroup.zpowers u) :
    ∃ c : Twist r, ∃ v : Grp (shortRel R c) →* G, Function.Surjective v := by
  classical
  choose x hx using (fun i : Fin d => hq (g (PresentedGroup.of i)))
  let X := FreeGroup.lift x
  have hcomp : q.comp X = g.comp (PresentedGroup.mk (Set.range R)) :=
    FreeGroup.ext_hom _ _ (fun i => by simpa [X,PresentedGroup.of] using hx i)
  have hX : Function.Surjective X := onto_lifts q hΦ X (hcomp ▸ hg.comp (PresentedGroup.mk_surjective _))
  have hmem (j : Fin r) : X (R j) ∈ Subgroup.zpowers u := by
    rw [←hker,MonoidHom.mem_ker]
    change (q.comp X) (R j)=1
    rw [hcomp,MonoidHom.comp_apply,relation,map_one]
  have twist (j : Fin r) : ∃ a : Fin 2, X (R j)=u^a.val := by
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp ((isOfFinOrder_of_finite u).mem_zpowers_iff_mem_range_orderOf.mp (hmem j))
    exact ⟨⟨v,ho ▸ Finset.mem_range.mp hv⟩,he.symm⟩
  choose c hc using twist
  have hne : c≠0 := by
    intro h
    have hrels : ∀ w ∈ Set.range R, X w = 1 := by
      rintro w ⟨j,rfl⟩
      rw [hc,h]; exact pow_zero _
    let v : Grp R →* G := QuotientGroup.lift _ X (Subgroup.normalClosure_le_normal hrels)
    have hv : Function.Surjective v := by
      intro a
      obtain ⟨w,rfl⟩ := hX a
      exact ⟨PresentedGroup.mk _ w,rfl⟩
    exact no_epi v hv
  let t : Twist r := ⟨c,hne⟩
  have hw : X (R (pivot t)) = u := by rw [hc,show (c (pivot t)).val=1 from pivot_eq t,pow_one]
  let Y := X.comp (substitute (R (pivot t)))
  have hy : Y.comp (FreeGroup.map some) = X := FreeGroup.ext_hom _ _ (fun i => by simp [Y,X,substitute])
  have hy0 : Y (FreeGroup.of none)=u := by simpa [Y,substitute] using hw
  have hrels (j : Unit ⊕ (Fin d ⊕ Fin r)) : Y (newRel R c j)=1 := by
    rcases j with _ | (i | j)
    · simpa only [newRel,map_pow,hy0,←ho] using pow_orderOf_eq_one u
    · rw [newRel,map_commutatorElement,hy0,commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hz _).symm
    · have hY : Y (FreeGroup.map some (R j)) = X (R j) := DFunLike.congr_fun hy (R j)
      rw [newRel,map_mul,map_inv,map_pow,hy0,hY,hc,mul_inv_cancel]
  have hrels' : ∀ w ∈ Set.range (shortRel R t), X w=1 := by
    rintro _ ⟨j,rfl⟩
    exact hrels _
  let v : Grp (shortRel R t) →* G := QuotientGroup.lift _ X (Subgroup.normalClosure_le_normal hrels')
  refine ⟨t,v,?_⟩
  intro a
  obtain ⟨w,rfl⟩ := hX a
  exact ⟨PresentedGroup.mk _ w,rfl⟩
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.CentralLifts.Survival
open CategoryTheory
def RelDim (d r : ℕ) : ℕ → ℕ
  | 0 => r
  | j+1 => RelDim d r j+d
def ChildCodes (d r : ℕ) : ℕ → Type
  | 0 => Unit
  | j+1 => ChildCodes d r j × Twist (RelDim d r j)
instance (d r j : ℕ) : Finite (ChildCodes d r j) := by
  induction j with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ j ih => exact inferInstanceAs (Finite (ChildCodes d r j × Twist (RelDim d r j)))
theorem rel_dim (d r j : ℕ) : RelDim d r j=r+j*d := by
  induction j with
  | zero => simp [RelDim]
  | succ j ih => simp [RelDim,ih,Nat.succ_mul,Nat.add_assoc]
theorem exact_code_card (d r j : ℕ) :
    Nat.card (ChildCodes d r j) = ∏ i ∈ Finset.range j, (2^(r+i*d)-1) := by
  induction j with
  | zero => simp [ChildCodes]
  | succ j ih =>
    change Nat.card (ChildCodes d r j × Twist (RelDim d r j)) = _
    rw [Nat.card_prod,ih,card_twist,rel_dim,Finset.prod_range_succ]
noncomputable def run {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) :
    {j : ℕ} → ChildCodes d r j → Fin (RelDim d r j) → FreeGroup (Fin d)
  | 0, _ => R
  | _+1,c => shortRel (run R c.1) c.2
variable {d r m : ℕ} {Q G : Type} [Group Q] [Group G] [Finite Q] [Finite G]
def frattiniClasses (m j : ℕ) (Q : Type) [Group Q] : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  {x | ∃ G : FiniteGrp.{0}, Nat.card G=2^(m+j) ∧
    (∃ f : G →* Q, Function.Surjective f ∧ f.ker ≤ frattini G) ∧ Quotient.mk _ G=x}
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160Growth.SharpFamily
end Erdos1160Growth.SharpFamily
end
section
namespace Erdos1160.DeepJacobi
variable {q n s : ℕ}
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {G : Type*} [Group G]
def TripleCentral (G : Type*) [Group G] : Prop :=
  ∀ a b c : G, ⁅⁅a,b⁆,c⁆ ∈ Subgroup.center G
private lemma conj_center (a : G) {v : G} (hv : v ∈ Subgroup.center G) : a*v*a⁻¹=v := by
  rw [Subgroup.mem_center_iff.mp hv a, mul_inv_cancel_right]
private lemma discard_center_factor {v : G} (hv : v ∈ Subgroup.center G) (b c : G) :
    ⁅v*b,c⁆ = ⁅b,c⁆ := by
  have h₁ := (Subgroup.mem_center_iff.mp hv ⁅b,c⁆).symm
  have h₂ : Commute v c := (Subgroup.mem_center_iff.mp hv c).symm
  rw [commutatorElement_mul_left_eq_conj_mul, h₁, mul_inv_cancel_right, h₂.commutator_eq, mul_one]
private lemma corrected_inner (H : TripleCentral G) (a b c : G) :
    ⁅⁅a⁻¹,b⁆,c⁆ = ⁅⁅b,a⁆,c⁆ := by
  have h : ⁅a⁻¹,⁅b,a⁆⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center G).inv_mem (H b a a⁻¹)
  have he : a⁻¹*⁅b,a⁆*a = ⁅a⁻¹,⁅b,a⁆⁆ * ⁅b,a⁆ := by
    rw [commutatorElement_def (a⁻¹) ⁅b,a⁆]
    group
  rw [commutatorElement_inv_left,he,discard_center_factor h]
theorem triple_cycle (H : TripleCentral G) (x y z : G) :
    ⁅⁅x,y⁆,z⁆ * ⁅⁅z,x⁆,y⁆ * ⁅⁅y,z⁆,x⁆ = 1 := by
  have h := conj_commutatorElement_left_commutatorElement_mul y x z
  rw [corrected_inner H y x z, corrected_inner H z y x, corrected_inner H x z y] at h
  have hg : y*⁅⁅x,y⁆,z⁆*y⁻¹ * (z*⁅⁅y,z⁆,x⁆*z⁻¹) * (x*⁅⁅z,x⁆,y⁆*x⁻¹) = 1 := by
    simpa only [mul_assoc] using h
  rw [conj_center y (H x y z),conj_center z (H y z x),conj_center x (H z x y)] at hg
  have hc := Subgroup.mem_center_iff.mp (H y z x) ⁅⁅z,x⁆,y⁆
  simpa only [mul_assoc, hc] using hg
private theorem flip_triple (H : TripleCentral G) (a b c : G) :
    ⁅⁅b,a⁆,c⁆ = ⁅⁅a,b⁆,c⁆⁻¹ := by
  rw [← commutatorElement_inv a b, commutatorElement_inv_left]
  rw [← commutatorElement_inv ⁅a,b⁆ c]
  have h := (Subgroup.center G).inv_mem (H a b c)
  simpa using conj_center (⁅a,b⁆⁻¹) h
theorem triple_rearranged (H : TripleCentral G) (x y z : G) :
    ⁅⁅y,z⁆,x⁆ = ⁅⁅x,z⁆,y⁆ * ⁅⁅x,y⁆,z⁆⁻¹ := by
  have hc := triple_cycle H x y z
  rw [flip_triple H x z y] at hc
  exact (eq_inv_of_mul_eq_one_right hc).trans (by simp)
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {q n s : ℕ} {G : Type*} [Group G]
abbrev Third (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries 2
def triple (x y z : G) : Third G :=
  ⟨⁅⁅x,y⁆,z⁆,Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)) (Subgroup.mem_top z)⟩
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {G : Type*} [Group G]
lemma lower_map_top {K : Type*} [Group K] (f : G →* K) (hf : Function.Surjective f) (n : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries n).map f = (⊤ : Subgroup K).lowerCentralSeries n := by
  rw [Subgroup.map_lowerCentralSeries,← MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective f hf]
theorem third_le_of_triples (N : Subgroup G) [N.Normal] (h : ∀ x y z : G, ⁅⁅x,y⁆,z⁆ ∈ N) :
    Third G ≤ N := by
  let f := QuotientGroup.mk' N
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hd : ⁅(⊤ : Subgroup (G ⧸ N)),⊤⁆ ≤ Subgroup.center (G ⧸ N) := by
    refine Subgroup.commutator_le.mpr ?_
    intro x _ y _
    obtain ⟨a,rfl⟩ := hf x
    obtain ⟨b,rfl⟩ := hf y
    apply Subgroup.mem_center_iff.mpr
    intro z
    obtain ⟨c,rfl⟩ := hf z
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement f,← map_commutatorElement f]
    exact (QuotientGroup.eq_one_iff _).mpr (h _ _ _)
  have hz : Third (G ⧸ N) = ⊥ := Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hd
  have hm : (Third G).map f = ⊥ := (lower_map_top f hf 2).trans hz
  exact (Subgroup.map_eq_bot_iff (Third G)).mp hm |>.trans (by rw [QuotientGroup.ker_mk'])
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {G : Type*} [Group G]
def thirdBracket (w : Second G) (x : G) : Third G :=
  ⟨⁅(w:G),x⁆,Subgroup.commutator_mem_commutator w.property (Subgroup.mem_top x)⟩
private theorem conjugate_center {w : G} (h : w ∈ Subgroup.center G) (x : G) :
    x*w*x⁻¹ = w := by rw [Subgroup.mem_center_iff.mp h x,mul_inv_cancel_right]
lemma thirdBracket_left (hc : Third G ≤ Subgroup.center G) (a b : Second G) (x : G) :
    thirdBracket (a*b) x = thirdBracket a x * thirdBracket b x := by
  apply Subtype.ext
  change ⁅(a:G)*b,x⁆ = ⁅(a:G),x⁆ * ⁅(b:G),x⁆
  have hb : ⁅(b:G),x⁆ ∈ Subgroup.center G := hc (thirdBracket b x).property
  rw [commutatorElement_mul_left_eq_conj_mul,conjugate_center hb]
  exact Subgroup.mem_center_iff.mp (hc (thirdBracket a x).property) _
lemma thirdBracket_right (hc : Third G ≤ Subgroup.center G) (a : Second G) (x y : G) :
    thirdBracket a (x*y) = thirdBracket a x * thirdBracket a y := by
  apply Subtype.ext
  change ⁅(a:G),x*y⁆ = ⁅(a:G),x⁆ * ⁅(a:G),y⁆
  have hy : ⁅(a:G),y⁆ ∈ Subgroup.center G := hc (thirdBracket a y).property
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅(a:G),x⁆ x, mul_assoc ⁅(a:G),x⁆, conjugate_center hy]
def groupTensor (hc : Third G ≤ Subgroup.center G) (measure : Third G →* Multiplicative Bit) :
    Second G →* (G →* Multiplicative Bit) where
  toFun a :=
    { toFun x := measure (thirdBracket a x)
      map_one' := by rw [show thirdBracket a 1 = 1 by apply Subtype.ext; exact commutatorElement_one_right _]; exact measure.map_one
      map_mul' x y := by rw [thirdBracket_right hc,map_mul] }
  map_one' := by
    apply MonoidHom.ext
    intro x
    change measure (thirdBracket 1 x) = 1
    rw [show thirdBracket 1 x = 1 by apply Subtype.ext; exact commutatorElement_one_left _,map_one]
  map_mul' a b := by
    apply MonoidHom.ext
    intro x
    change measure (thirdBracket (a*b) x) = measure (thirdBracket a x)*measure (thirdBracket b x)
    rw [thirdBracket_left hc,map_mul]
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160Growth.LowerTriangularUpper
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
private noncomputable def descent {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (hf : Function.Surjective f) (g : X →* Z) (hk : f.ker ≤ g.ker) : Y →* Z :=
  f.liftOfSurjective hf ⟨g,hk⟩
private lemma descent_apply {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (hf : Function.Surjective f) (g : X →* Z) (hk : f.ker ≤ g.ker) (x : X) :
    descent f hf g hk (f x)= g x := by
  have h := (f.liftOfSurjective hf).left_inv (⟨g,hk⟩ : {g : X →* Z // f.ker ≤ g.ker})
  exact congrArg (fun u : {g : X →* Z // f.ker ≤ g.ker} => u.val x) h
theorem descend_pair {U V Q R B : Type*} [Group U] [Group V] [Group Q] [Group R] [CommGroup B]
    (f : U →* Q) (hf : Function.Surjective f) (g : V →* R) (hg : Function.Surjective g)
    (a : U →* (V →* B)) (hk₁ : f.ker ≤ a.ker) (hk₂ : ∀u,g.ker ≤ (a u).ker) :
    ∃ t : Q →* (R →* B), ∀u v, t (f u) (g v) = a u v := by
  let row (u : U) := descent g hg (a u) (hk₂ u)
  have he (u : U) (v : V) : row u (g v)=a u v := descent_apply ..
  let t : U →* (R →* B) := {
    toFun := row
    map_one' := by
      apply MonoidHom.ext
      intro r
      obtain ⟨v,rfl⟩ := hg r
      rw [he,a.map_one]; rfl
    map_mul' u w := by
      apply MonoidHom.ext
      intro r
      obtain ⟨v,rfl⟩ := hg r
      change row (u*w) (g v) = row u (g v) * row w (g v)
      rw [he,he,he,a.map_mul]; rfl }
  have hk : f.ker ≤ t.ker := by
    intro u hu
    apply MonoidHom.ext
    intro r
    obtain ⟨v,rfl⟩ := hg r
    change row u (g v)=1
    rw [he,show a u=1 from hk₁ hu]; rfl
  refine ⟨descent f hf t hk,fun u v => ?_⟩
  rw [descent_apply]; exact he u v
variable {E Q : Type*} [Group E] [Group Q]
def secondMap (f : E →* Q) (hf : Function.Surjective f) : Second E →* Second Q :=
  (f.comp (Second E).subtype).codRestrict _ (fun w => (lower_map_top f hf 1).le (show f w.val ∈ (Second E).map f from ⟨w.val,w.property,rfl⟩))
lemma secondMap_surj (f : E →* Q) (hf : Function.Surjective f) :
    Function.Surjective (secondMap f hf) := by
  intro w
  have h : w.val ∈ (Second E).map f := (lower_map_top f hf 1).symm ▸ w.property
  obtain ⟨v,hv,he⟩ := h
  exact ⟨⟨v,hv⟩,Subtype.ext he⟩
lemma secondMap_bracket (f : E →* Q) (hf : Function.Surjective f) (x y : E) :
    secondMap f hf (secondBracket x y) = secondBracket (f x) (f y) :=
  Subtype.ext (map_commutatorElement f x y)
end Erdos1160.DeepJacobi
end
section
namespace ThirdLowerCentral
abbrev third (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries 2
theorem trivial_iff {G : Type*} [Group G] :
    third G = ⊥ ↔ commutator G ≤ Subgroup.center G := by
  change ⁅commutator G,(⊤ : Subgroup G)⁆ = ⊥ ↔ _
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  simp [Subgroup.centralizer_univ]
theorem quotient_has_class_two (G : Type*) [Group G] :
    commutator (G ⧸ third G) ≤ Subgroup.center (G ⧸ third G) := by
  apply trivial_iff.mp
  let q := QuotientGroup.mk' (third G)
  have onto : (⊤ : Subgroup G).map q = ⊤ := by
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have he := (⊤ : Subgroup G).map_lowerCentralSeries q 2
  rw [onto] at he
  change (⊤ : Subgroup (G ⧸ third G)).lowerCentralSeries 2 = ⊥
  rw [← he]
  exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
end ThirdLowerCentral
end
section
namespace CentralKernelCount
open scoped commutatorElement
def adjoin {G : Type*} [Group G] {d : ℕ} (N : Subgroup G) (x : Fin d → G) : Subgroup G :=
  N ⊔ Subgroup.closure (Set.range x)
theorem card_adjoin_orders {G : Type*} [Group G] [Finite G] {d : ℕ} (N : Subgroup G) [N.Normal]
    (x : Fin d → G) (n : Fin d → ℕ) (hn : ∀ i, 0 < n i) (hsq : ∀ i, x i ^ n i ∈ N) (hcomm : ∀ i j, ⁅x i,x j⁆ ∈ N) :
    Nat.card (adjoin N x) ≤ (∏ i, n i) * Nat.card N := by
  classical
  let π := QuotientGroup.mk' N
  let S := adjoin N x
  let f := π.comp S.subtype
  let H (i : Fin d) := Subgroup.zpowers (π (x i))
  have van {g : G} (h : g ∈ N) : π g = 1 := (QuotientGroup.eq_one_iff _).mpr h
  have commute : Pairwise fun i j => ∀ z w : G ⧸ N, z ∈ H i → w ∈ H j → Commute z w := by
    intro i j _ z w hz hw
    obtain ⟨m,rfl⟩ := hz
    obtain ⟨n,rfl⟩ := hw
    have hc : Commute (π (x i)) (π (x j)) :=
      commutatorElement_eq_one_iff_mul_comm.mp <| (map_commutatorElement π _ _).symm.trans (van (hcomm i j))
    exact hc.zpow_zpow _ _
  let p := Subgroup.noncommPiCoprod commute
  have hSP : S ≤ p.range.comap π := by
    apply sup_le
    · intro z hz
      change π z ∈ p.range
      rw [van hz]
      exact p.range.one_mem
    · rw [Subgroup.closure_le]
      rintro _ ⟨i,rfl⟩
      change π (x i) ∈ p.range
      rw [show p.range = ⨆ i, H i from Subgroup.noncommPiCoprod_range]
      exact (le_iSup H i) (Subgroup.mem_zpowers _)
  have hrange : f.range ≤ p.range := by
    rintro z ⟨w,rfl⟩
    exact hSP w.property
  have hp : Nat.card p.range ≤ ∏ i, n i := by
    apply (Nat.card_le_card_of_surjective _ p.rangeRestrict_surjective).trans
    rw [Nat.card_pi]
    apply Finset.prod_le_prod'
    intro i _
    change Nat.card (Subgroup.zpowers (π (x i))) ≤ n i
    rw [Nat.card_zpowers]
    apply Nat.le_of_dvd (hn i)
    exact orderOf_dvd_of_pow_eq_one <| (map_pow π _ _).symm.trans (van (hsq i))
  have hk : Nat.card f.ker ≤ Nat.card N := by
    let m (z : f.ker) : N := ⟨z.val.val,(QuotientGroup.eq_one_iff _).mp z.property⟩
    apply Nat.card_le_card_of_injective m
    intro z w hw
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun q : N => q.val) hw)
  change Nat.card S ≤ _
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  apply Nat.mul_le_mul _ hk
  exact (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hrange)).trans hp
end CentralKernelCount
end
section
namespace CentralKernelCount
open scoped commutatorElement
theorem map_adjoin {G J : Type*} [Group G] [Group J] {d : ℕ}
    (N : Subgroup G) (x : Fin d → G) (f : G →* J) :
    (adjoin N x).map f = adjoin (N.map f) (fun i => f (x i)) := by
  rw [adjoin,adjoin,Subgroup.map_sup,MonoidHom.map_closure,← Set.range_comp]
  rfl
end CentralKernelCount
end
section
namespace CentralKernelCount
open scoped commutatorElement
abbrev PairSlot (d : ℕ) := (i : Fin d) × Fin i.val
def second {d : ℕ} (p : PairSlot d) : Fin d := ⟨p.2.val,p.2.isLt.trans p.1.isLt⟩
def word {G : Type*} [Group G] {t : ℕ} (y : Fin t → G) (w : List (Fin t)) := (w.map y).prod
end CentralKernelCount
end
section
namespace CentralKernelCount
open scoped commutatorElement
abbrev BitGroup (d : ℕ) := Multiplicative (Fin d → ZMod 2)
def bit {d : ℕ} (i : Fin d) : BitGroup d := Multiplicative.ofAdd (Pi.single i 1)
theorem word_mem {G : Type*} [Group G] {t : ℕ}
    (S : Subgroup G) (y : Fin t → G) (hy : ∀ i, y i ∈ S) (l : List (Fin t)) : word y l ∈ S := by
  induction l with
  | nil => exact S.one_mem
  | cons i l h => exact S.mul_mem (hy i) h
theorem bits_word (d : ℕ) (w : BitGroup d) : ∃ l, word bit l = w := by
  change ∃ l, word bit l = Multiplicative.ofAdd w.toAdd
  induction w.toAdd using Pi.single_induction with
  | zero => exact ⟨[],rfl⟩
  | add x y hx hy =>
    obtain ⟨l,hl⟩ := hx
    obtain ⟨r,hr⟩ := hy
    use l++r
    simpa only [word,List.map_append,List.prod_append,ofAdd_add] using congrArg₂ (·*·) hl hr
  | single i c =>
    rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) c with rfl|rfl
    · exact ⟨[],by simp [word]⟩
    · exact ⟨[i],by simp [word,bit]⟩
end CentralKernelCount
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
variable {d s : ℕ}
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
end Erdos1160Growth.LowerTriangularUpper
end
section
namespace Erdos1160.PresentationCount
open CategoryTheory
end Erdos1160.PresentationCount
end
section
namespace CentralKernelCount
open CategoryTheory Erdos1160Growth.LowerTriangularUpper
end CentralKernelCount
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
open Erdos1160Growth.LowerTriangularUpper CentralLifts
variable {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q] {m : ℕ}
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.CentralLifts.Survival
def QuotientCap (P : Type) [Group P] (N : ℕ) := ∀ (Y : Type) [Group Y] [Finite Y],
  IsPGroup 2 Y → ∀ f : P →* Y, Function.Surjective f → Nat.card Y ≤ N
variable {d r m N : ℕ} {P : Type} [Group P]
theorem cap_after_short (R : Fin r → FreeGroup (Fin d)) (hR : QuotientCap (Grp R) N) (c : Twist r) :
    QuotientCap (Grp (shortRel R c)) (N*2) := by
  intro Y _ _ hY h hh
  let f := h.comp (contractShort R c)
  have hf : Function.Surjective f := hh.comp (contractShort_surj R c)
  let u := f (z R c.val)
  have hu : u ∈ Subgroup.center Y := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨w,rfl⟩ := hf y
    exact (map_mul f _ _).symm.trans ((congrArg f (Subgroup.mem_center_iff.mp (z_central R c.val) w)).trans (map_mul f _ _))
  let Z := Subgroup.zpowers u
  let _ : Z.Normal := normal_zpowers_of_central u hu
  have hz : Nat.card Z ≤ 2 := by
    rw [show Nat.card Z=orderOf u by exact Nat.card_zpowers _]
    apply orderOf_le_of_pow_eq_one (by decide)
    exact (map_pow f _ _).symm.trans ((congrArg f (z_pow R c.val)).trans f.map_one)
  let L := Subgroup.zpowers (z R c.val)
  have hl : L ≤ Z.comap f := Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers _)
  let ψ := QuotientGroup.map L Z f hl
  have hp : Function.Surjective ψ := by
    intro w
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective Z w
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨QuotientGroup.mk' L x,rfl⟩
  let π := ψ.comp (quotientMap R c.val)
  have hπ := hp.comp (quotientMap_surjective R c.val)
  have hQ := hR (Y ⧸ Z) (hY.to_quotient Z) π hπ
  rw [Z.card_eq_card_quotient_mul_card_subgroup]
  exact Nat.mul_le_mul hQ hz
theorem cap_run (R : Fin r → FreeGroup (Fin d)) (hR : QuotientCap (Grp R) N)
    (j : ℕ) (c : ChildCodes d r j) : QuotientCap (Grp (run R c)) (N*2^j) := by
  induction j with
  | zero => change QuotientCap (Grp R) (N*2^0); rw [pow_zero,mul_one];exact hR
  | succ j ih =>
    rw [pow_succ,←Nat.mul_assoc]
    exact cap_after_short _ (ih c.1) c.2
theorem max_quotients_iso {E F : Type} [Group E] [Group F] [Finite E] [Finite F]
    (cap : QuotientCap P (2^m)) (hE : Nat.card E=2^m) (hF : Nat.card F=2^m)
    (f : P →* E) (g : P →* F) (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Nonempty (E ≃* F) := by
  let D := (f.prod g).range
  have hp : IsPGroup 2 (E × F) := IsPGroup.of_card (show Nat.card (E × F)=2^(m+m) by
    rw [Nat.card_prod,hE,hF,pow_add])
  have hc : Nat.card D ≤ 2^m := cap D (hp.to_subgroup _) _ (f.prod g).rangeRestrict_surjective
  let fst := (MonoidHom.fst E F).comp D.subtype
  let snd := (MonoidHom.snd E F).comp D.subtype
  have hfst : Function.Surjective fst := by
    intro y;obtain ⟨x,rfl⟩ := hf y;exact ⟨(f.prod g).rangeRestrict x,rfl⟩
  have hsnd : Function.Surjective snd := by
    intro y;obtain ⟨x,rfl⟩ := hg y;exact ⟨(f.prod g).rangeRestrict x,rfl⟩
  have h1 : Nat.card D=Nat.card E := le_antisymm (hc.trans_eq hE.symm) (Nat.card_le_card_of_surjective fst hfst)
  have h2 : Nat.card D=Nat.card F := h1.trans (hE.trans hF.symm)
  let a := MulEquiv.ofBijective fst ((Nat.bijective_iff_surjective_and_card fst).2 ⟨hfst,h1⟩)
  let b := MulEquiv.ofBijective snd ((Nat.bijective_iff_surjective_and_card snd).2 ⟨hsnd,h2⟩)
  exact ⟨a.symm.trans b⟩
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi (C₂ one_step_factor)
variable {F Q : Type} [Group F] [Group Q]
def relEval (π : F →* Q) (r : π.ker) : Additive (RelCharacters π) →ₗ[ZMod 2] ZMod 2 :=
  (show Additive (RelCharacters π) →+ ZMod 2 from
    { toFun := fun a => (a.toMul.val r).toAdd
      map_zero' := rfl
      map_add' := fun _ _ => rfl }).toZModLinearMap 2
theorem relEval_separates (π : F →* Q) (a : Additive (RelCharacters π)) (h : ∀r,relEval π r a = 0) : a=0 := by
  change a.toMul=1
  apply Subtype.ext
  apply MonoidHom.ext
  intro r
  exact (show (a.toMul.val r).toAdd=0 from h r)
private theorem normal_image_character {Y : Type} [Group Y] [Finite Y] (hp : IsPGroup 2 Y)
    (N : Subgroup Y) [N.Normal] (hn : N≠⊥) : ∃ (B : N →* C₂),
      Function.Surjective B ∧ ∀ (g : Y) (r : N),B ⟨g*r.val*g⁻¹,(inferInstance : N.Normal).conj_mem _ r.property _⟩=B r := by
  classical
  obtain ⟨m,hm⟩ := hp.exists_card_eq
  obtain ⟨k,hk⟩ := (hp.to_quotient N).exists_card_eq
  have hlt : k < m := by
    have hq := N.card_eq_card_quotient_mul_card_subgroup
    rw [hm,hk] at hq
    have hcard : 1 < Nat.card N := by
      have : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hn
      exact Finite.one_lt_card
    exact lt_of_not_ge (fun hle => by
      have H := (Nat.pow_le_pow_right (by decide : 0 < 2) hle).trans_lt
        (show 2^k < 2^k*Nat.card N by simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hcard (Nat.two_pow_pos k))
      exact H.ne hq)
  let j := m-(k+1)
  have he : m=k+(j+1) := by dsimp [j];omega
  obtain ⟨U,q,b,hq,hb,eq,hU⟩ := one_step_factor hk j (hm.trans (congrArg (2^·) he))
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hbc : Nat.card b.ker=2 := by simpa using ker_card_of_epi Nat.prime_two hU hk b hb
  have hz := ThirdLowerCentral.order_two_central b.ker hbc
  have hker (r : N) : q r.val ∈ b.ker := by
    change (b.comp q) r.val=1
    rw [eq]
    exact (QuotientGroup.eq_one_iff _).mpr r.property
  let f := (q.comp N.subtype).codRestrict b.ker hker
  have onto : Function.Surjective f := by
    intro r
    obtain ⟨g,hg⟩ := hq r.val
    have hg' : g ∈ N := (QuotientGroup.eq_one_iff _).mp (by
      change QuotientGroup.mk' N g=1;rw [←eq,MonoidHom.comp_apply,hg];exact r.property)
    exact ⟨⟨g,hg'⟩,Subtype.ext hg⟩
  let c : b.ker ≃* C₂ := mulEquivOfPrimeCardEq hbc (Nat.card_zmod 2)
  refine ⟨c.toMonoidHom.comp f,c.surjective.comp onto,?_⟩
  intro g r
  apply congrArg c
  apply Subtype.ext
  change q (g*r.val*g⁻¹)=q r.val
  rw [map_mul,map_mul,map_inv,Subgroup.mem_center_iff.mp (hz (hker r)) (q g),mul_inv_cancel_right]
theorem detecting_character (π : F →* Q) {Y : Type} [Group Y] [Finite Y] (hp : IsPGroup 2 Y)
    (f : F →* Y) (hf : Function.Surjective f) (bad : ¬π.ker ≤ f.ker) :
    ∃ a : RelCharacters π,a≠1 ∧ ∀r : π.ker, f r.val=1 → a.val r=1 := by
  let N := π.ker.map f
  let _ : N.Normal := Subgroup.Normal.map (inferInstance : π.ker.Normal) f hf
  have hn : N≠⊥ := by
    intro he
    apply bad
    intro x hx
    exact Subgroup.mem_bot.mp (he ▸ (show f x∈N from ⟨x,hx,rfl⟩))
  obtain ⟨χ,hχ,invχ⟩ := normal_image_character hp N hn
  let F₀ := (f.comp π.ker.subtype).codRestrict N (fun r => ⟨r.val,r.property,rfl⟩)
  have hF₀ : Function.Surjective F₀ := by
    rintro ⟨_,r,hr,rfl⟩
    exact ⟨⟨r,hr⟩,rfl⟩
  let a := χ.comp F₀
  have inv (g : F) (r : π.ker) : a (conjugateRelation π g r)=a r := by
    apply Eq.trans _ (invχ (f g) (F₀ r))
    apply congrArg χ
    apply Subtype.ext
    change f (g*r.val*g⁻¹)=f g*f r.val*(f g)⁻¹
    simp
  refine ⟨⟨a,inv⟩,?_,?_⟩
  · intro he
    obtain ⟨r,hr⟩ := (hχ.comp hF₀) (Multiplicative.ofAdd 1)
    have hz := congrArg (fun u : RelCharacters π => (u.val r).toAdd) he
    change (a r).toAdd=0 at hz
    change a r=Multiplicative.ofAdd 1 at hr
    rw [hr] at hz
    exact (by decide : (1 : ZMod 2) ≠0) hz
  · intro r hr
    have h : F₀ r=1 := Subtype.ext hr
    change χ (F₀ r)=1
    rw [h,χ.map_one]
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.CentralLifts.Survival
open CategoryTheory
variable {d r m : ℕ} {Q G : Type} [Group Q] [Group G] [Finite Q] [Finite G]
omit [Finite Q] in
theorem virtual_cover (R : Fin r → FreeGroup (Fin d)) (hR : QuotientCap (Grp R) (2^m))
    (q0 : Grp R →* Q) (hq0 : Function.Surjective q0) (hQ : Nat.card Q=2^m)
    (j : ℕ) (hG : Nat.card G=2^(m+j)) (f : G →* Q) (hf : Function.Surjective f)
    (hΦ : f.ker ≤ frattini G) :
    ∃ c : ChildCodes d r j, ∃ v : Grp (run R c) →* G, Function.Surjective v := by
  induction j generalizing G with
  | zero =>
    let e := MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).2 ⟨hf,hG.trans hQ.symm⟩)
    exact ⟨(),e.symm.toMonoidHom.comp q0,e.symm.surjective.comp hq0⟩
  | succ j ih =>
    have hsize := ker_card_of_epi Nat.prime_two hG hQ f hf
    obtain ⟨u,hu,hz,ho⟩ := central_prime_in_normal Nat.prime_two (IsPGroup.of_card hG) f.ker
      (hsize ▸ dvd_pow_self 2 (Nat.succ_ne_zero j))
    let N := Subgroup.zpowers u
    let _ : N.Normal := normal_zpowers_of_central u hz
    let π := QuotientGroup.mk' N
    have hπ := QuotientGroup.mk'_surjective N
    have hN : N ≤ f.ker := Subgroup.zpowers_le.mpr hu
    let F := QuotientGroup.lift N f hN
    have ontoF : Function.Surjective F := fun x => by
      obtain ⟨a,rfl⟩ := hf x
      exact ⟨π a,rfl⟩
    have frF : F.ker ≤ frattini (G ⧸ N) := by
      intro w hw
      obtain ⟨a,rfl⟩ := hπ w
      exact (frattini_le_comap_frattini_of_surjective hπ) (hΦ (show a∈f.ker from hw))
    have cardQ := card_quotient_prime (by decide : 0 < 2) ho (k := m+j) hG
    obtain ⟨c,g,hg⟩ := ih cardQ F ontoF frF
    have noepi (v : Grp (run R c) →* G) (hv : Function.Surjective v) : False := by
      have h := cap_run R hR j c G (IsPGroup.of_card hG) v hv
      rw [←pow_add,hG] at h
      exact (Nat.pow_lt_pow_right (by decide : 1 < 2) (show m+j < m+(j+1) by omega)).not_ge h
    have hk : π.ker ≤ frattini G := (QuotientGroup.ker_mk' N).le.trans (hN.trans hΦ)
    obtain ⟨t,w,hw⟩ := child_cover_of_no_epi (run R c) g hg noepi π hπ hk u ho hz (QuotientGroup.ker_mk' N)
    exact ⟨(c,t),w,hw⟩
omit [Finite Q] in
theorem virtual_frattini_count (R : Fin r → FreeGroup (Fin d)) (cap : QuotientCap (Grp R) (2^m))
    (q : Grp R →* Q) (hq : Function.Surjective q) (hQ : Nat.card Q=2^m) (j : ℕ) :
    (frattiniClasses m j Q).ncard ≤ ∏ i ∈ Finset.range j,(2^(r+i*d)-1) := by
  classical
  let S := frattiniClasses m j Q
  have reps (x : S) : ∃ (Y : FiniteGrp.{0}) (c : ChildCodes d r j) (v : Grp (run R c) →* Y),
      Quotient.mk _ Y=x.val ∧ Nat.card Y=2^(m+j) ∧ Function.Surjective v := by
    obtain ⟨Y,hY,⟨f,hf,hk⟩,eq⟩ := x.property
    obtain ⟨c,v,hv⟩ := virtual_cover R cap q hq hQ j hY f hf hk
    exact ⟨Y,c,v,eq,hY,hv⟩
  choose Y c v eq hc hv using reps
  have hinj : Function.Injective c := by
    intro x y he
    have hy : ∃ f : Grp (run R (c x)) →* Y y, Function.Surjective f := he ▸ ⟨v y,hv y⟩
    obtain ⟨f,hf⟩ := hy
    have b := cap_run R cap j (c x)
    rw [←pow_add] at b
    obtain ⟨e⟩ := max_quotients_iso b (hc x) (hc y) (v x) f (hv x) hf
    apply Subtype.ext
    rw [←eq x,←eq y]
    apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.toGrpIso⟩
  exact (Nat.card_le_card_of_injective c hinj).trans (exact_code_card d r j).le
end Erdos1160.CentralLifts.Survival
end
section
namespace OrbitUp
theorem exists_injective_evaluations {K A I : Type*} [Field K] [AddCommGroup A] [Module K A]
    [FiniteDimensional K A] (ev : I → Module.Dual K A)
    (separates : ∀ x : A, (∀ i, ev i x = 0) → x=0) :
    ∃ select : Fin (Module.finrank K A) → I,
      Function.Injective (fun x : A => fun j => ev (select j) x) := by
  classical
  let W := Submodule.span K (Set.range ev)
  have hz : W.dualCoannihilator = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply separates
    intro i
    exact (Submodule.mem_dualCoannihilator x).mp hx _ (Submodule.subset_span ⟨i,rfl⟩)
  have hr : Module.finrank K W = Module.finrank K A := by
    have eq := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    rw [hz] at eq
    simpa using eq
  obtain ⟨f,hf,hs,_⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range ev)
  choose j hj using hf
  let cast := finCongr hr
  refine ⟨fun k => j (cast.symm k), fun x y he => ?_⟩
  have hk : Submodule.span K (Set.range f) ≤ (Module.Dual.eval K A (x-y)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    change f k (x-y) = 0
    rw [← hj k,map_sub,sub_eq_zero]
    have h := congrFun he (cast k)
    simpa only [cast.symm_apply_apply] using h
  apply sub_eq_zero.mp
  apply separates
  intro i
  apply hk
  rw [hs]
  exact Submodule.subset_span ⟨i,rfl⟩
end OrbitUp
end
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi (C₂)
variable {d m : ℕ} {Q : Type} [Group Q] [Finite Q]
noncomputable def relRank (π : FreeGroup (Fin d) →* Q) :=
  Module.finrank (ZMod 2) (Additive (RelCharacters π))
theorem multiplicator_presentation (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π) :
    ∃ R : Fin (relRank π) → FreeGroup (Fin d), QuotientCap (Grp R) (Nat.card Q) ∧
      ∃ q : Grp R →* Q, Function.Surjective q := by
  classical
  obtain ⟨S,hS⟩ := OrbitUp.exists_injective_evaluations (relEval π) (relEval_separates π)
  let R : Fin (relRank π) → FreeGroup (Fin d) := fun j => (S j).val
  have hR : Subgroup.normalClosure (Set.range R) ≤ π.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j,rfl⟩
    exact (S j).property
  let q : Grp R →* Q := QuotientGroup.lift _ π hR
  have hq : Function.Surjective q := fun y => by
    obtain ⟨x,rfl⟩ := hπ y
    exact ⟨PresentedGroup.mk _ x,rfl⟩
  refine ⟨R,?_,q,hq⟩
  intro Y _ _ hp f hf
  let F := f.comp (PresentedGroup.mk (Set.range R))
  have hF : Function.Surjective F := hf.comp (PresentedGroup.mk_surjective _)
  have hker : π.ker ≤ F.ker := by
    by_contra bad
    obtain ⟨a,ha,hkill⟩ := detecting_character π hp F hF bad
    apply ha
    have H : (fun j => relEval π (S j) (Additive.ofMul a))=(fun j => relEval π (S j) 0) := by
      funext j
      apply congrArg Multiplicative.toAdd
      apply hkill
      change f (PresentedGroup.mk (Set.range R) (R j))=1
      exact (congrArg f (relation R j)).trans f.map_one
    exact hS H
  let ψ := π.liftOfSurjective hπ ⟨F,hker⟩
  have he := (π.liftOfSurjective hπ).left_inv (⟨F,hker⟩ : {u : FreeGroup (Fin d) →* Y // π.ker ≤ u.ker})
  have hy : Function.Surjective ψ := by
    intro y
    obtain ⟨x,rfl⟩ := hF y
    exact ⟨π x,congrArg (fun u : {u : FreeGroup (Fin d) →* Y // π.ker ≤ u.ker} => u.val x) he⟩
  exact Nat.card_le_card_of_surjective ψ hy
theorem multiplicator_fiber_product (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (j : ℕ) :
    (frattiniClasses m j Q).ncard ≤ ∏ i ∈ Finset.range j,(2^(relRank π+i*d)-1) := by
  obtain ⟨R,cap,q,hq⟩ := multiplicator_presentation π hπ
  exact virtual_frattini_count R (hQ ▸ cap) q hq hQ j
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
def JacobiDual (Q : Type*) [Group Q] : Subgroup (Second Q →* (Q →* C₂)) where
  carrier := {t | ∀ x y z : Q, t (secondBracket y z) x =
    t (secondBracket x z) y * (t (secondBracket x y) z)⁻¹}
  one_mem' := by intros _ _ _; change (1:C₂)=1*1⁻¹; simp
  mul_mem' := by
    intro a b ha hb x y z
    change a _ _*b _ _ = (a _ _*b _ _)*(a _ _*b _ _)⁻¹
    rw [ha x y z,hb x y z]
    simp only [mul_inv_rev,inv_inv]
    ac_rfl
  inv_mem' := by
    intro a ha x y z
    change (a _ _)⁻¹ = (a _ _)⁻¹*((a _ _)⁻¹)⁻¹
    rw [ha x y z]
    simp only [mul_inv_rev,inv_inv]
    ac_rfl
instance jacobiDualFinite (Q : Type*) [Group Q] [Finite Q] : Finite (JacobiDual Q) :=
  Finite.of_injective (fun t : JacobiDual Q => fun (w : Second Q) (x : Q) => t.val w x)
    (fun _ _ h => Subtype.ext (MonoidHom.ext fun w=>MonoidHom.ext fun x=>congrFun (congrFun h w) x))
variable {E Q : Type*} [Group E] [Group Q]
private theorem descent_character (f : E →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hc : Third E ≤ Subgroup.center E)
    (mu : Third E →* C₂) :
    ∃ t : JacobiDual Q, ∀u v, t.val (secondMap f hf u) (f v) = mu (thirdBracket u v) := by
  let a := groupTensor hc mu
  have hzRight (w : Second E) : f.ker ≤ (a w).ker := by
    intro x hx
    change mu (thirdBracket w x)=1
    rw [show thirdBracket w x=1 from Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hker hx) _)),map_one]
  have hzLeft : (secondMap f hf).ker ≤ a.ker := by
    intro w hw
    have hz : w.val ∈ Subgroup.center E := hker (show w.val ∈ f.ker from congrArg Subtype.val hw)
    apply MonoidHom.ext
    intro x
    change mu (thirdBracket w x)=1
    rw [show thirdBracket w x=1 from Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz x).symm),map_one]
  obtain ⟨t,ht⟩ := descend_pair (secondMap f hf) (secondMap_surj f hf) f hf a hzLeft hzRight
  have hval (x y z : E) : t (secondBracket (f x) (f y)) (f z)=mu (triple x y z) := by
    rw [←secondMap_bracket f hf,ht];rfl
  refine ⟨⟨t,?_⟩,ht⟩
  intro x y z
  obtain ⟨x,rfl⟩ := hf x
  obtain ⟨y,rfl⟩ := hf y
  obtain ⟨z,rfl⟩ := hf z
  rw [hval,hval,hval,←map_inv,←map_mul]
  exact congrArg mu (Subtype.ext (triple_rearranged (fun a b c=>hc (triple a b c).property) x y z))
private theorem dual_ext {t u : JacobiDual Q} (f : E→*Q) (hf : Function.Surjective f)
    (h : ∀w x,t.val (secondMap f hf w) (f x)=u.val (secondMap f hf w) (f x)) : t=u := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro w
  apply MonoidHom.ext
  intro x
  obtain ⟨w,rfl⟩ := secondMap_surj f hf w
  obtain ⟨x,rfl⟩ := hf x
  exact h w x
noncomputable def characterDual (f : E→*Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hc : Third E ≤ Subgroup.center E) :
    (Third E →* C₂) →* JacobiDual Q where
  toFun mu := (descent_character f hf hker hc mu).choose
  map_one' := by
    apply dual_ext f hf
    intro w x
    exact (descent_character f hf hker hc 1).choose_spec w x
  map_mul' a b := by
    apply dual_ext f hf
    intro w x
    exact ((descent_character f hf hker hc (a*b)).choose_spec w x).trans (congrArg₂ (·*·)
      ((descent_character f hf hker hc a).choose_spec w x).symm
      ((descent_character f hf hker hc b).choose_spec w x).symm)
theorem characterDual_apply (f : E→*Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hc : Third E ≤ Subgroup.center E)
    (mu : Third E →* C₂) (w : Second E) (x : E) :
    (characterDual f hf hker hc mu).val (secondMap f hf w) (f x) = mu (thirdBracket w x) :=
  (descent_character f hf hker hc mu).choose_spec _ _
theorem characterDual_injective (f : E→*Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hc : Third E ≤ Subgroup.center E) :
    Function.Injective (characterDual f hf hker hc) := by
  intro a b h
  let K := a.eqLocus b
  let N := K.map (Third E).subtype
  have hcent : N ≤ Subgroup.center E := by rintro _ ⟨w,_,rfl⟩;exact hc w.property
  let _ : N.Normal := ⟨fun x hx y => by simpa [Subgroup.mem_center_iff.mp (hcent hx) y] using hx⟩
  have hg : Third E ≤ N := third_le_of_triples N (fun x y z=>by
    refine ⟨triple x y z,?_,rfl⟩
    change a (thirdBracket (secondBracket x y) z)=b (thirdBracket (secondBracket x y) z)
    rw [←characterDual_apply f hf hker hc,←characterDual_apply f hf hker hc,h])
  apply MonoidHom.ext
  intro w
  obtain ⟨u,hu,he⟩ := hg w.property
  have huw : u=w := Subtype.ext he
  exact huw ▸ (show a u=b u from hu)
theorem character_dual_card [Finite Q] (f : E→*Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hc : Third E ≤ Subgroup.center E) :
    Nat.card (Third E→* C₂) ≤ Nat.card (JacobiDual Q) :=
  Nat.card_le_card_of_injective _ (characterDual_injective f hf hker hc)
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.DeepJacobi
private theorem bit_mul_self (x : C₂) : x*x=1 := by
  change x.toAdd+x.toAdd=0
  exact (show ∀x : ZMod 2,x+x=0 by decide) _
instance jacobiDualModule (Q : Type*) [Group Q] : Module (ZMod 2) (Additive (JacobiDual Q)) :=
  AddCommGroup.zmodModule (fun u => by
    rw [two_nsmul]
    apply Subtype.ext
    apply MonoidHom.ext
    intro w
    apply MonoidHom.ext
    intro x
    apply bit_mul_self)
variable {E Q : Type*} [Group E] [Group Q]
theorem elementary_third_dimension [Finite E] [Finite Q]
    (f : E→*Q) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center E)
    (hc : Third E ≤ Subgroup.center E) {k : ℕ}
    (hs : ∀ w : Third E, w*w=1) (hsize : Nat.card (Third E)=2^k) :
    k ≤ Module.finrank (ZMod 2) (Additive (JacobiDual Q)) := by
  obtain ⟨i⟩ := Erdos1160Growth.LowerTriangularUpper.exist_elementary_coords hs hsize
  let dot (v : Fin k → ZMod 2) : Multiplicative (Fin k → ZMod 2) →* C₂ := {
    toFun := fun x => Multiplicative.ofAdd (∑j,v j*x.toAdd j)
    map_one' := by change (∑j,v j*0)=0; simp
    map_mul' := fun x y=>by
      change (∑j,v j*(x.toAdd j+y.toAdd j))=(∑j,v j*x.toAdd j)+(∑j,v j*y.toAdd j)
      simp [mul_add,Finset.sum_add_distrib] }
  let embed (v : Fin k → ZMod 2) : Third E →* C₂ := (dot v).comp i.toMonoidHom
  have ev (v : Fin k→ZMod 2) (j : Fin k) : embed v (i.symm (Multiplicative.ofAdd (Pi.single j 1))) =
      Multiplicative.ofAdd (v j) := by
    change (∑l : Fin k,v l * ((i (i.symm (Multiplicative.ofAdd (Pi.single j 1)))).toAdd l)) = _
    rw [i.apply_symm_apply]
    simp [Pi.single_apply, mul_ite]
    rfl
  have inj : Function.Injective embed := by
    intro v w h
    funext j
    have h' := congrArg (fun g : Third E →* C₂ => g (i.symm (Multiplicative.ofAdd (Pi.single j 1)))) h
    exact (ev v j).symm.trans (h'.trans (ev w j))
  let _ : Finite (Third E→*C₂) := Finite.of_injective (fun g : Third E→*C₂ => (g : Third E → C₂)) DFunLike.coe_injective
  have hcard : Nat.card (Fin k→ZMod 2) ≤ Nat.card (JacobiDual Q) := (Nat.card_le_card_of_injective _ inj).trans (character_dual_card f hf hker hc)
  let _ : Fintype (Additive (JacobiDual Q)) := Fintype.ofFinite _
  have hd := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive (JacobiDual Q))
  rw [←Nat.card_eq_fintype_card,ZMod.card] at hd
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [←hd]
  change 2^k ≤ Nat.card (JacobiDual Q)
  simpa only [Nat.card_fun,Nat.card_zmod,Nat.card_fin] using hcard
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.CentralLifts.Survival
variable {d : ℕ} {Q : Type} [Group Q] [Finite Q]
abbrev Adual (π : FreeGroup (Fin d) →* Q) := Module.Dual (ZMod 2) (Additive (RelCharacters π))
def evalHom (π : FreeGroup (Fin d) →* Q) : π.ker →* Multiplicative (Adual π) where
  toFun r := .ofAdd (relEval π r)
  map_one' := by
    apply Multiplicative.ofAdd.injective
    apply LinearMap.ext
    intro a
    exact congrArg Multiplicative.toAdd (a.toMul.val.map_one)
  map_mul' r s := by
    apply Multiplicative.ofAdd.injective
    apply LinearMap.ext
    intro a
    exact congrArg Multiplicative.toAdd (a.toMul.val.map_mul r s)
theorem eval_onto (π : FreeGroup (Fin d) →* Q) : Function.Surjective (evalHom π) := by
  let W : Submodule (ZMod 2) (Adual π) := {
    carrier := Set.range (relEval π)
    zero_mem' := ⟨1,congrArg Multiplicative.toAdd (evalHom π).map_one⟩
    add_mem' := by rintro _ _ ⟨r,rfl⟩ ⟨s,rfl⟩;exact ⟨r*s,congrArg Multiplicative.toAdd ((evalHom π).map_mul r s)⟩
    smul_mem' := by
      rintro k _ ⟨r,rfl⟩
      rcases (show ∀k:ZMod 2,k=0 ∨ k=1 by decide) k with rfl|rfl
      · rw [zero_smul];exact ⟨1,congrArg Multiplicative.toAdd (evalHom π).map_one⟩
      · rw [one_smul];exact ⟨r,rfl⟩ }
  have hz : W.dualCoannihilator=⊥ := by
    apply le_bot_iff.mp
    intro a ha
    apply relEval_separates π
    intro r
    exact (Submodule.mem_dualCoannihilator a).mp ha _ (show relEval π r∈W from ⟨r,rfl⟩)
  have htop : W=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    rw [hz] at h
    simpa using h
  intro b
  have hb : b.toAdd ∈ W := htop.ge Submodule.mem_top
  obtain ⟨r,hr⟩ := hb
  exact ⟨r,congrArg Multiplicative.ofAdd hr⟩
def universalKernel (π : FreeGroup (Fin d) →* Q) := (evalHom π).ker.map π.ker.subtype
instance (π : FreeGroup (Fin d) →* Q) : (universalKernel π).Normal where
  conj_mem := by
    rintro _ ⟨w,hw,rfl⟩ g
    refine ⟨conjugateRelation π g w,?_,rfl⟩
    change Multiplicative.ofAdd (relEval π (conjugateRelation π g w))=1
    apply Multiplicative.ofAdd.injective
    apply LinearMap.ext
    intro a
    have h := congrArg (fun v : Multiplicative (Adual π) => v.toAdd a)
      (show evalHom π w=1 from hw)
    exact (congrArg Multiplicative.toAdd (a.toMul.property g w)).trans h
abbrev Cover (π : FreeGroup (Fin d) →*Q) := FreeGroup (Fin d) ⧸ universalKernel π
def coverProjection (π : FreeGroup (Fin d) →*Q) : Cover π →*Q :=
  QuotientGroup.lift _ π (fun _ ⟨w,_,eq⟩ => eq ▸ w.property)
omit [Finite Q] in
lemma cover_onto (π : FreeGroup (Fin d) →*Q) (hπ : Function.Surjective π) :
    Function.Surjective (coverProjection π) := fun z => by
  obtain ⟨x,rfl⟩ := hπ z
  exact ⟨QuotientGroup.mk' _ x,rfl⟩
theorem cover_card (π : FreeGroup (Fin d) →*Q) (hπ : Function.Surjective π) :
    Nat.card (Cover π)=2^(relRank π)*Nat.card Q := by
  change Nat.card (FreeGroup (Fin d) ⧸ universalKernel π)=_
  rw [←Subgroup.index_eq_card,universalKernel,Subgroup.index_map_subtype,Subgroup.index_ker,Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (eval_onto π),MonoidHom.range_eq_top.mpr hπ,Subgroup.card_top,Subgroup.card_top]
  congr 1
  change Nat.card (Adual π)=_
  let _ : Finite (Adual π) := Finite.of_injective (fun f : Adual π => (f : _ → ZMod 2)) DFunLike.coe_injective
  let _ := Fintype.ofFinite (Adual π)
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Adual π)
  rw [←Nat.card_eq_fintype_card,ZMod.card] at h
  simpa only [Adual,Subspace.dual_finrank_eq,relRank] using h
omit [Finite Q] in
theorem cover_central (π : FreeGroup (Fin d) →*Q) : (coverProjection π).ker ≤ Subgroup.center (Cover π) := by
  intro z hz
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (universalKernel π) z
  let w : π.ker := ⟨u,hz⟩
  apply Subgroup.mem_center_iff.mpr
  intro a
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (universalKernel π) a
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [←map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  let g := conjugateRelation π v w * w⁻¹
  refine ⟨g,?_,rfl⟩
  change evalHom π g=1
  have h : evalHom π (conjugateRelation π v w)=evalHom π w := by
    apply Multiplicative.ofAdd.injective
    apply LinearMap.ext
    intro b
    exact congrArg Multiplicative.toAdd (b.toMul.property v w)
  rw [show g=conjugateRelation π v w*w⁻¹ from rfl,map_mul,map_inv,h,mul_inv_cancel]
omit [Finite Q] in
theorem cover_binary (π : FreeGroup (Fin d) →*Q) (v : (coverProjection π).ker) : v*v=1 := by
  apply Subtype.ext
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (universalKernel π) v.val
  have hz : π u=1 := by change coverProjection π (QuotientGroup.mk' (universalKernel π) u)=1;rw [hu];exact v.property
  change v.val*v.val=1
  rw [←hu,←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  let w : π.ker := ⟨u,hz⟩
  refine ⟨w*w,?_,rfl⟩
  change evalHom π (w*w)=1
  rw [map_mul]
  apply Multiplicative.ofAdd.injective
  apply LinearMap.ext
  intro a
  exact (show ∀x : ZMod 2,x+x=0 by decide) (relEval π w a)
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
variable {d : ℕ} {Q : Type} [Group Q]
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival
open Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
variable {G Q : Type*} [Group G] [Group Q]
private def sq (D : Subgroup G) : Subgroup G :=
  Subgroup.closure (Set.range (fun x : D=>x.val*x.val))
private theorem sq_map (D : Subgroup G) (f : G→*Q) : (sq D).map f=sq (D.map f) := by
  rw [sq,MonoidHom.map_closure,sq]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨⟨f v.val,⟨v.val,v.property,rfl⟩⟩,(f.map_mul ..).symm⟩
  · rintro ⟨v,rfl⟩
    obtain ⟨y,hy,he⟩ := v.property
    exact ⟨y*y,⟨⟨y,hy⟩,rfl⟩,by rw [map_mul,he]⟩
private theorem sq_eq (D : Subgroup G) : (squareCore D).map D.subtype=sq D := by
  rw [squareCore,MonoidHom.map_closure,sq,←Set.range_comp]
  rfl
private theorem comm_mul_z {x z y : G} (hz : z∈Subgroup.center G) : ⁅x*z,y⁆=⁅x,y⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz _).symm]
  simp
private theorem comm_z_mul {x z y : G} (hz : z∈Subgroup.center G) : ⁅x,y*z⁆=⁅x,y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz _)]
  simp
private theorem join_central (H N : Subgroup G) [N.Normal] (hz : N ≤ Subgroup.center G) :
    ⁅H⊔N,H⊔N⁆=⁅H,H⁆ := by
  refine le_antisymm (Subgroup.commutator_le.mpr ?_) (Subgroup.commutator_mono le_sup_left le_sup_left)
  intro x hx y hy
  obtain ⟨u,hu,v,hv,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨c,hc,b,hb,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  rw [comm_mul_z (hz hv),comm_z_mul (hz hb)]
  exact Subgroup.commutator_mem_commutator hu hc
private theorem central_step (H N : Subgroup G) [N.Normal] (hz : N ≤ Subgroup.center G)
    (htwo : ∀v∈N,v*v=1) (hD : commutator G≤ ⁅H,H⁆⊔N)
    (hgen : commutator G ≤ ⁅H,H⁆⊔ (⁅commutator G,⊤⁆ ⊔ sq (commutator G))) :
    commutator G≤⁅H,H⁆ := by
  let L := H⊔N
  letI : L.Normal := Subgroup.Normal.of_commutator_le G
    (hD.trans (sup_le_sup_right H.commutator_le_self N))
  letI : (⁅H,H⁆ : Subgroup G).Normal := (join_central H N hz) ▸ (inferInstance : (⁅L,L⁆ : Subgroup G).Normal)
  have hthird : ⁅commutator G,(⊤ : Subgroup G)⁆ ≤ ⁅H,H⁆ := by
    apply Subgroup.commutator_le.mpr
    intro x hx y _
    obtain ⟨u,hu,v,hv,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hD hx)
    rw [comm_mul_z (hz hv)]
    exact Subgroup.commutator_top_right_le_iff.mpr inferInstance
      (Subgroup.commutator_mem_commutator hu (Subgroup.mem_top y))
  have hsquare : sq (commutator G)≤⁅H,H⁆ := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    obtain ⟨u,hu,v,hv,he⟩ := Subgroup.mem_sup_of_normal_right.mp (hD x.property)
    change x.val*x.val∈⁅H,H⁆
    rw [←he,←pow_two, (show Commute u v from Subgroup.mem_center_iff.mp (hz hv) _).mul_pow,
      pow_two v,htwo v hv,mul_one]
    exact Subgroup.pow_mem _ hu _
  exact hgen.trans (sup_le le_rfl (sup_le hthird hsquare))
private theorem derived_raw {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hc : Nat.card G=2^m) (H : Subgroup G)
    (hgen : commutator G ≤ ⁅H,H⁆⊔(⁅commutator G,⊤⁆⊔sq (commutator G))) :
    ⁅H,H⁆=commutator G := by
  induction m generalizing G with
  | zero =>
    let _ := (Nat.card_eq_one_iff_unique.mp (show Nat.card G=1 from hc)).1
    exact Subsingleton.elim _ _
  | succ m ih =>
    obtain ⟨j,hj,hcZ⟩ := IsPGroup.card_center_eq_prime_pow hc (Nat.succ_pos m)
    obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G:=Subgroup.center G) 2
      (hcZ ▸ dvd_pow_self _ (Nat.ne_of_gt hj))
    let u : G := t.val
    have hz : u ∈ Subgroup.center G := t.property
    have ho : orderOf u=2 := (Subgroup.orderOf_coe t).trans ht
    let N := Subgroup.zpowers u
    let _ : N.Normal := ⟨fun n hn g => by
      have h := Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hz) hn) g
      rwa [h,mul_inv_cancel_right]⟩
    let q := QuotientGroup.mk' N
    have top : (⊤ : Subgroup G).map q=⊤ := by
      rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top];exact QuotientGroup.mk'_surjective _
    have der : (commutator G).map q=commutator (G⧸N) := by
      rw [commutator_def,Subgroup.map_commutator,top];rfl
    have lift := Subgroup.map_mono (f:=q) hgen
    simp only [Subgroup.map_sup,Subgroup.map_commutator,sq_map,der,top] at lift
    have hquot : Nat.card (G ⧸ N)=2^m := by
      have h := N.card_mul_index
      rw [Subgroup.index_eq_card,show Nat.card N=2 from (Nat.card_zpowers u).trans ho,
        hc,pow_succ'] at h
      omega
    have eq := ih hquot (H.map q) lift
    have le : (commutator G).map q ≤ (⁅H,H⁆ : Subgroup G).map q := by rw [der,Subgroup.map_commutator,eq]
    have hD := Subgroup.map_le_iff_le_comap.mp le
    rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk'] at hD
    apply le_antisymm (Subgroup.commutator_mono le_top le_top)
    refine central_step H N (Subgroup.zpowers_le.mpr hz) ?_ hD hgen
    intro v hv
    let a : N := ⟨v,hv⟩
    have hcard : Nat.card N=2 := (Nat.card_zpowers u).trans ho
    have hh := pow_card_eq_one' (x:=a)
    rw [hcard,pow_two] at hh
    exact congrArg (fun w:N=>w.val) hh
theorem structural_derived {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (H : Subgroup G) (hgen : commutator G ≤ (commutator H).map H.subtype ⊔
      (Third G ⊔ (squareCore (commutator G)).map (commutator G).subtype)) :
    (commutator H).map H.subtype=commutator G := by
  obtain ⟨m,hm⟩ := hG.exists_card_eq
  rw [Subgroup.map_subtype_commutator,sq_eq] at *
  exact derived_raw hm H hgen
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi
theorem structural_third {G : Type*} [Group G] (H : Subgroup G)
    (hh : (commutator H).map H.subtype=commutator G) :
    (Third H).map H.subtype=Third G := by
  rw [Subgroup.map_subtype_commutator] at hh
  letI : H.Normal := Subgroup.Normal.of_commutator_le G (hh ▸ H.commutator_le_self)
  let K : Subgroup G := ⁅⁅H,H⁆,H⁆
  change ((⊤ : Subgroup H).lowerCentralSeries 2).map H.subtype=_
  rw [Subgroup.map_lowerCentralSeries,←MonoidHom.range_eq_map,H.range_subtype]
  change K=⁅commutator G,⊤⁆
  refine le_antisymm (Subgroup.commutator_mono hh.le le_top) ?_
  let q := QuotientGroup.mk' K
  let U := H.map q
  have qt : (⊤ : Subgroup G).map q=⊤ := by
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have nil : ⁅⁅U,U⁆,U⁆=⊥ := by
    change ⁅⁅H.map q,H.map q⁆,H.map q⁆=⊥
    rw [←Subgroup.map_commutator,←Subgroup.map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    exact (QuotientGroup.ker_mk' K).ge
  have der : commutator (G⧸K)=⁅U,U⁆ := by
    have h := congrArg (Subgroup.map q) hh
    rwa [commutator_def,Subgroup.map_commutator,Subgroup.map_commutator,qt,eq_comm] at h
  have left : ⁅U,⊤⁆ ≤ ⁅U,U⁆ := (Subgroup.commutator_mono le_top le_rfl :
    ⁅U,⊤⁆ ≤ commutator (G⧸K)).trans der.le
  have right : ⁅⊤,U⁆≤⁅U,U⁆ := (Subgroup.commutator_comm ..).le.trans left
  have z : ⁅⁅U,U⁆,(⊤ : Subgroup (G⧸K))⁆=⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate
    (eq_bot_iff.mpr ((Subgroup.commutator_mono left le_rfl).trans nil.le))
    (eq_bot_iff.mpr ((Subgroup.commutator_mono right le_rfl).trans nil.le))
  apply (show ⁅commutator G,⊤⁆≤q.ker → ⁅commutator G,⊤⁆≤K from fun h=>h.trans (QuotientGroup.ker_mk' K).le)
  apply (Subgroup.map_eq_bot_iff _).mp
  rw [←hh,Subgroup.map_commutator,Subgroup.map_commutator,qt]
  exact z
end Erdos1160.Sims
end
section
namespace OrbitUp
open scoped BigOperators Matrix
end OrbitUp
end
section
namespace OrbitUp
theorem count_small_rank_matrices (d t r : ℕ) :
    Nat.card {A : Matrix (Fin d) (Fin t) K // A.rank ≤ r} ≤ 2^(r*(d+t)) := by
  classical
  let _ (p q : ℕ) : Finite (V p →ₗ[K] V q) :=
    Finite.of_equiv (Matrix (Fin q) (Fin p) K) LinearMap.toMatrix'.symm.toEquiv
  have card (p q : ℕ) : Nat.card (V p →ₗ[K] V q) = 2^(p*q) := by
    rw [Nat.card_congr (LinearMap.toMatrix' : (V p →ₗ[K] V q) ≃ₗ[K] Matrix (Fin q) (Fin p) K).toEquiv]
    change Nat.card (Fin q → Fin p → ZMod 2) = _
    simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, pow_mul]
  let S := {A : Matrix (Fin d) (Fin t) K // A.rank ≤ r}
  let f (A : S) := A.val.mulVecLin
  have fac (A : S) : ∃ z : (V t →ₗ[K] V r) × (V r →ₗ[K] V d), z.2.comp z.1 = f A := by
    have hdim : Module.finrank K (LinearMap.range (f A)) ≤ Module.finrank K (V r) := by
      rw [Module.finrank_fin_fun]; exact A.property
    obtain ⟨i, hi⟩ := finrank_le_iff_exists_linearMap.mp hdim
    obtain ⟨p, hp⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
    refine ⟨⟨i.comp (f A).rangeRestrict, (f A).range.subtype.comp p⟩, ?_⟩
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (DFunLike.congr_fun hp ((f A).rangeRestrict x))
  let code (A : S) := (fac A).choose
  have hi : Function.Injective code := by
    intro A B h
    have he : f A = f B := (fac A).choose_spec.symm.trans
      ((congrArg (fun z : (V t →ₗ[K] V r) × (V r →ₗ[K] V d) => z.2.comp z.1) h).trans (fac B).choose_spec)
    apply Subtype.ext
    exact Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply'] using he)
  calc
    _ ≤ Nat.card ((V t →ₗ[K] V r) × (V r →ₗ[K] V d)) := Nat.card_le_card_of_injective code hi
    _ = _ := by rw [Nat.card_prod,card,card,←pow_add]; congr 1; ring
end OrbitUp
end
section
namespace OrbitUp.BoundedMatrices
variable {U W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
private lemma binary_sum (x : K) : x+x=0 := (show ∀x:K,x+x=0 by decide) x
private lemma scalar_sym (A : U→ₗ[K] U→ₗ[K] K) (alt : ∀u,A u u=0) (x y : U) : A y x=A x y := by
  have eq := alt (x+y)
  simp only [map_add,LinearMap.add_apply,alt,zero_add,add_zero] at eq
  have check : ∀u v:K,u+v=0→u=v := by decide
  exact check _ _ eq
theorem hyperplane_formula (A : U→ₗ[K] U→ₗ[K] K) (alt : ∀u,A u u=0) (l : U→ₗ[K] K) (hl : l≠0)
    (null : ∀x y : U,l x=0→l y=0→A x y=0) (u v : U) (huv : A u v=1) (x : U) :
    l x=l u*A x v+l v*A u x := by
  have ex : ∃w,l w≠0 := by simpa only [ne_eq,LinearMap.ext_iff,LinearMap.zero_apply,not_forall] using hl
  obtain ⟨w,hw⟩ := ex
  have lw : l w=1 := by rcases (show ∀a:K,a=0 ∨ a=1 by decide) (l w) with h|h <;> tauto
  have kills (y : U) : l (y+l y • w)=0 := by simp [map_add,map_smul,lw,binary_sum]
  have det (x y : U) : A x y=l x*A w y+l y*A x w := by
    have h := null _ _ (kills x) (kills y)
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,alt w,mul_zero,add_zero] at h
    have e : ∀a b c:K,a+b+c=0→a=b+c := by decide
    exact e _ _ _ h
  calc l x = l x * A u v := (mul_one _).symm.trans (congrArg (l x * ·) huv.symm)
       _ = l u*A x v+l v*A u x := by
         rw [det u v,det x v,det u x,scalar_sym A alt w x]
         ring_nf <;> simp [show (2:K)=0 by decide]
theorem alternating_hyperplanes (A : U→ₗ[K] U→ₗ[K] K) (alt : ∀u,A u u=0)
    (u v : U) (huv : A u v=1) :
    Nat.card {l : U→ₗ[K] K // l≠0 ∧ ∀x y,l x=0→l y=0→A x y=0}≤3 := by
  classical
  let T := {l : U→ₗ[K] K // l≠0 ∧ ∀x y,l x=0→l y=0→A x y=0}
  let P := {p : K×K // p≠0}
  let c (l:T) : P := ⟨(l.val u,l.val v),fun zero=>by
    have h := l.property.2 _ _ (congrArg Prod.fst zero) (congrArg Prod.snd zero)
    exact one_ne_zero (huv.symm.trans h)⟩
  have inj : Function.Injective c := by
    intro a b eq
    apply Subtype.ext;apply LinearMap.ext;intro x
    rw [hyperplane_formula A alt _ a.property.1 a.property.2 u v huv x,
        hyperplane_formula A alt _ b.property.1 b.property.2 u v huv x]
    rw [show a.val u=b.val u from congrArg (fun p:P=>p.val.1) eq,
        show a.val v=b.val v from congrArg (fun p:P=>p.val.2) eq]
  have h := Nat.card_le_card_of_injective c inj
  exact h.trans (by rw [Nat.card_eq_fintype_card]; decide)
end OrbitUp.BoundedMatrices
end
section
namespace OrbitUp.BoundedMatrices
variable {U W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
def valuesOn (β : U→ₗ[K] U→ₗ[K] W) (S : Submodule K U) : Submodule K W :=
  Submodule.span K (Set.range (fun z : S×S=>β z.1.val z.2.val))
private def tested (β : U→ₗ[K] U→ₗ[K] W) (S : Submodule K U) (z : W→ₗ[K] K) : S→ₗ[K] S→ₗ[K] K where
  toFun x := z.comp ((β x.val).comp S.subtype)
  map_add' a b := by ext y;change z (β (a.val+b.val) y.val)=_;simp
  map_smul' a b := by ext y;change z (β (a • b.val) y.val)=_;simp
private theorem dual_card_ne (W : Type) [AddCommGroup W] [Module K W] [Finite W] :
    Nat.card {z : W→ₗ[K] K // z≠0}=2^Module.finrank K W-1 := by
  classical
  letI : Finite (W→ₗ[K] K) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI := Fintype.ofFinite (W→ₗ[K] K)
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    ←Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K:=K),Nat.card_zmod,Subspace.dual_finrank_eq]
  simp
theorem minimal_commutator_span [Finite U] [Finite W] (β : U→ₗ[K] U→ₗ[K] W)
    (alt : ∀u,β u u=0) (spans : valuesOn β ⊤=⊤) :
    ∃S : Submodule K U,valuesOn β S=⊤ ∧ Module.finrank K S ≤ Module.finrank K W+1 := by
  classical
  let P (n : ℕ) := ∃ S : Submodule K U, valuesOn β S=⊤ ∧ Module.finrank K S=n
  have ex : ∃n,P n := ⟨_,⊤,spans,rfl⟩
  obtain ⟨S,hS,rank⟩ := Nat.find_spec ex
  refine ⟨S,hS,?_⟩
  letI : Finite (S→ₗ[K] K) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI : Finite (W→ₗ[K] K) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let A := {a : S→ₗ[K] K // a≠0}
  let B := {b : W→ₗ[K] K // b≠0}
  have pick (l : A) : ∃z:B, ∀x y:S,l.val x=0→l.val y=0→tested β S z.val x y=0 := by
    let H := l.val.ker
    let D := H.map S.subtype
    have sm : Module.finrank K D < Module.finrank K S := by
      rw [←(Submodule.equivMapOfInjective S.subtype S.subtype_injective H).finrank_eq]
      have proper : H<⊤ := lt_top_iff_ne_top.mpr (fun h=>l.property (LinearMap.ker_eq_top.mp h))
      exact (Submodule.finrank_lt_finrank_of_lt proper).trans_eq (finrank_top K S)
    have miss : valuesOn β D ≠ ⊤ := fun e=>by
      have low := Nat.find_min' ex (show P (Module.finrank K D) from ⟨D,e,rfl⟩)
      omega
    obtain ⟨z,hz,hker⟩ := (valuesOn β D).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr miss)
    refine ⟨⟨z,hz⟩,fun x y hx hy=>?_⟩
    exact hker (Submodule.subset_span ⟨(⟨x.val,⟨x,hx,rfl⟩⟩,⟨y.val,⟨y,hy,rfl⟩⟩),rfl⟩)
  choose select hselect using pick
  have pairs (z : B) : ∃u v:S,tested β S z.val u v=1 := by
    by_contra! hn
    have hv : ∀u v:S,z.val (β u.val v.val)=0 := fun u v=>by
      rcases (show ∀a:K,a=0 ∨ a=1 by decide) (z.val (β u.val v.val)) with h|h
      · exact h
      · exact False.elim (hn u v h)
    have hz : valuesOn β S ≤ z.val.ker := Submodule.span_le.mpr (by rintro _ ⟨⟨x,y⟩,rfl⟩;exact hv x y)
    rw [hS] at hz
    exact z.property (LinearMap.ker_eq_top.mp (top_le_iff.mp hz))
  have count := Erdos1160.PresentationCount.card_le_of_fiber_bound select 3 (by
    intro z
    obtain ⟨u,v,huv⟩ := pairs z
    let T := {l : S→ₗ[K] K // l≠0 ∧ ∀x y,l x=0→l y=0→tested β S z.val x y=0}
    let m (x : {l : A // select l=z}) : T := ⟨x.val.val,x.val.property,by have h := hselect x.val;rw [x.property] at h;exact h⟩
    have low := Nat.card_le_card_of_injective m (fun x y eq=>Subtype.ext (Subtype.ext (congrArg (fun a:T=>a.val) eq)))
    exact low.trans (alternating_hyperplanes (tested β S z.val) (fun x=>by change z.val (β x.val x.val)=0;rw [alt,map_zero]) u v huv))
  change Nat.card {l : S→ₗ[K] K // l≠0}≤Nat.card {z : W→ₗ[K] K // z≠0}*3 at count
  rw [dual_card_ne,dual_card_ne] at count
  by_contra! g
  have cmp := Nat.pow_le_pow_right (n:=2) (by decide) (show Module.finrank K W+2 ≤ Module.finrank K S by omega)
  rw [pow_add] at cmp
  have := Nat.two_pow_pos (Module.finrank K W)
  omega
end OrbitUp.BoundedMatrices
end
section
namespace OrbitUp.MinSpan
variable {d h k : ℕ}
abbrev Sample (d h : ℕ) := Fin h→V d
noncomputable def sampleRows (A : V d→ₗ[K] Module.Dual K (V d)) (x : Sample d h) : Submodule K (Module.Dual K (V d)) :=
  Submodule.span K (Set.range (fun i=>A (x i)))
theorem sample_card (d h : ℕ) : Nat.card (Sample d h)=2^(d*h) := by
  simp only [Sample,V,Nat.card_fun,Nat.card_fin,Nat.card_zmod,pow_mul]
private theorem rank_span_in_image (A : V d→ₗ[K] Module.Dual K (V d)) (x : Sample d h) :
    Module.finrank K (Submodule.span K (Set.range (fun i=>A.rangeRestrict (x i))))=Module.finrank K (sampleRows A x) := by
  let T := Submodule.span K (Set.range (fun i=>A.rangeRestrict (x i)))
  have eq : T.map A.range.subtype=sampleRows A x := by
    simp only [T,Submodule.map_span,←Set.range_comp]
    rfl
  exact (Submodule.equivMapOfInjective A.range.subtype A.range.subtype_injective T).finrank_eq.trans (congrArg (fun S : Submodule K (Module.Dual K (V d))=>Module.finrank K S) eq)
theorem low_samples (A : V d→ₗ[K] Module.Dual K (V d)) (h k : ℕ) :
    let r:=Module.finrank K A.range
    Nat.card {x : Sample d h // Module.finrank K (sampleRows A x) ≤ k} ≤
      2^(k*(r+h)+(Module.finrank K A.ker)*h) := by
  classical
  let R := A.range
  let X := {x : Sample d h // Module.finrank K (sampleRows A x) ≤ k}
  let C := (V k→ₗ[K] R) × Sample k h × (Fin h→A.ker)
  let lift : R→V d := Function.surjInv A.surjective_rangeRestrict
  have liftOk (w : R) : A (lift w)=w.val := congrArg Subtype.val (Function.rightInverse_surjInv A.surjective_rangeRestrict w)
  have fac (x : X) : ∃p:C,∀i,x.val i=lift (p.1 (p.2.1 i))+(p.2.2 i).val := by
    let T := Submodule.span K (Set.range (fun i=>A.rangeRestrict (x.val i)))
    have dim : Module.finrank K T ≤ Module.finrank K (V k) := by
      rw [Module.finrank_fin_fun];exact (rank_span_in_image A x.val).le.trans x.property
    obtain ⟨f,hf⟩ := finrank_le_iff_exists_linearMap.mp dim
    obtain ⟨g,hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
    let xi (i : Fin h) : T := ⟨A.rangeRestrict (x.val i),Submodule.subset_span ⟨i,rfl⟩⟩
    have ok (i) : T.subtype (g (f (xi i))) = A.rangeRestrict (x.val i) := congrArg Subtype.val (DFunLike.congr_fun hg (xi i))
    let z (i) : A.ker := ⟨x.val i-lift (A.rangeRestrict (x.val i)),by rw [LinearMap.mem_ker,map_sub,liftOk,sub_eq_zero];rfl⟩
    exact ⟨(T.subtype.comp g,fun i=>f (xi i),z),fun i=>by simp only [LinearMap.comp_apply,ok,z];abel⟩
  choose c hc using fac
  have inj : Function.Injective c := by
    intro x y e
    exact Subtype.ext (funext fun i=>(hc x i).trans ((congrArg (fun p:C=>lift (p.1 (p.2.1 i))+(p.2.2 i).val) e).trans (hc y i).symm))
  letI : Finite (Module.Dual K (V d)) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI : Finite (V k→ₗ[K] R) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have bd := Nat.card_le_card_of_injective c inj
  have cover : Nat.card C=2^(k*(Module.finrank K R+h)+Module.finrank K A.ker*h) := by
    simp only [C,Nat.card_prod,sample_card,Nat.card_fun,Nat.card_fin,Module.natCard_eq_pow_finrank (K:=K) (V:=A.ker),Module.natCard_eq_pow_finrank (K:=K) (V:=V k→ₗ[K] R),Nat.card_zmod,
      Module.finrank_linearMap,Module.finrank_fin_fun,←pow_mul,←pow_add]
    congr 1;ring
  exact bd.trans cover.le
theorem high_fiber (A : V d→ₗ[K] Module.Dual K (V d)) (x : Sample d h) (high : k ≤ Module.finrank K (sampleRows A x)) :
    Nat.card {y:Sample d h // ∀i j,A (x i) (y j)=0}≤2^((d-k)*h) := by
  classical
  let T := sampleRows A x
  let C := T.dualCoannihilator
  let X := {y:Sample d h // ∀i j,A (x i) (y j)=0}
  let into (y:X) (j : Fin h) : C := ⟨y.val j,by
    rw [Submodule.mem_dualCoannihilator]
    intro l hl
    let g := Module.Dual.eval K (V d) (y.val j)
    have le : T ≤ g.ker := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩;exact y.property i j)
    exact le hl⟩
  have inj : Function.Injective into := fun x y e=>Subtype.ext (funext (fun j=>congrArg Subtype.val (congrFun e j)))
  have cap := Subspace.finrank_add_finrank_dualCoannihilator_eq T
  rw [Module.finrank_fin_fun] at cap
  change Module.finrank K T+Module.finrank K C=d at cap
  change k ≤ Module.finrank K T at high
  have bd := Nat.card_le_card_of_injective into inj
  rw [Nat.card_fun,Nat.card_fin,Module.natCard_eq_pow_finrank (K:=K) (V:=C),Nat.card_zmod,←pow_mul] at bd
  exact bd.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h (by omega)))
end OrbitUp.MinSpan
end
section
namespace OrbitUp.MinSpan
open scoped BigOperators
abbrev SamplePair (d k : ℕ) := Sample d (2*k) × Sample d (2*k)
def vanishes {d k : ℕ} (A : V d→ₗ[K] Module.Dual K (V d)) (z : SamplePair d k) : Prop := ∀i j,A (z.1 i) (z.2 j)=0
private theorem finiteUnion {X I : Type} [Finite X] [Fintype I] (p : I→X→Prop) :
    Nat.card {x:X // ∃i,p i x}≤∑i : I,Nat.card {x:X // p i x} := by
  classical
  choose f hf using fun x:{x:X // ∃i,p i x}=>x.property
  let g (x : {x:X // ∃i,p i x}) : (i : I) × {x:X // p i x} := ⟨f x,x.val,hf x⟩
  have inj : Function.Injective g := fun x y e=>Subtype.ext (congrArg (fun z : (i : I) × {x:X // p i x}=>z.2.val) e)
  exact (Nat.card_le_card_of_injective g inj).trans_eq Nat.card_sigma
theorem pair_sample_bound {d k : ℕ} (A : V d→ₗ[K] Module.Dual K (V d))
    (big : 4*k ≤ Module.finrank K A.range) :
    Nat.card {z:SamplePair d k // vanishes A z}*2^(2*k*k) ≤ 2*Nat.card (SamplePair d k) := by
  classical
  let h := 2*k
  let r := Module.finrank K A.range
  let n := Module.finrank K A.ker
  have size : r+n=d := (LinearMap.finrank_range_add_finrank_ker A).trans (Module.finrank_fin_fun K)
  let low (x : Sample d h) := Module.finrank K (sampleRows A x) ≤ k
  let L := {x : Sample d h // low x}
  let H := {x : Sample d h // ¬low x}
  let Z := {z : SamplePair d k // vanishes A z}
  let Y (x : H) := {y : Sample d h // ∀i j,A (x.val i) (y j)=0}
  let C := (L × Sample d h) ⊕ ((x : H) × Y x)
  let enc (z:Z) : C := if m:low z.val.1 then .inl (⟨z.val.1,m⟩,z.val.2)
    else .inr ⟨⟨z.val.1,m⟩,⟨z.val.2,z.property⟩⟩
  let dec : C→SamplePair d k := Sum.elim (fun x=>(x.1.val,x.2)) (fun x=>(x.1.val,x.2.val))
  have left (z : Z) : dec (enc z)=z.val := by by_cases m:low z.val.1 <;> simp [enc,dec,m]
  have cut := Nat.card_le_card_of_injective enc (fun x y e=>Subtype.ext ((left x).symm.trans ((congrArg dec e).trans (left y))))
  have hlow : Nat.card L ≤ 2^(k*(r+h)+n*h) := low_samples A h k
  letI := Fintype.ofFinite H
  have hi : Nat.card ((x : H) × Y x) ≤ 2^(d*h)*2^((d-k)*h) := by
    rw [Nat.card_sigma]
    calc _ ≤ ∑_x : H,2^((d-k)*h) := Finset.sum_le_sum (fun x _=>high_fiber A x.val (by have := x.property;unfold low at this;omega))
         _ = Nat.card H*2^((d-k)*h) := by simp [←Nat.card_eq_fintype_card]
         _ ≤ _ := Nat.mul_le_mul_right _ ((Nat.card_le_card_of_injective (fun x:H=>x.val) Subtype.val_injective).trans_eq (sample_card d h))
  change Nat.card Z*_≤_
  apply (Nat.mul_le_mul_right _ cut).trans
  change (Nat.card ((L × Sample d h) ⊕ ((x:H)×Y x)))*_≤_
  rw [Nat.card_sum,Nat.card_prod,sample_card,Nat.add_mul]
  change _ ≤ 2*(Nat.card (Sample d h × Sample d h))
  rw [Nat.card_prod,sample_card]
  conv_rhs => rw [two_mul]
  apply Nat.add_le_add
  · grw [hlow]
    rw [←pow_add,←pow_add,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    change 4*k ≤ r at big
    dsimp [h];nlinarith only [Nat.mul_le_mul_right k big,congrArg (·*(2*k)) size]
  · grw [hi]
    rw [←pow_add,←pow_add,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have kLe : k ≤ d := by change 4*k ≤ r at big;omega
    have e := Nat.sub_add_cancel kLe
    dsimp [h];nlinarith only [congrArg (·*(2*k)) e]
theorem simultaneous_nonvanish {d k b : ℕ} {I : Type} [Fintype I]
    (A : I→V d→ₗ[K] Module.Dual K (V d)) (hI : Nat.card I ≤ 2^b) (budget : b+1 < 2*k*k) :
    ∃z : SamplePair d k,∀i,4*k ≤ Module.finrank K (A i).range→¬vanishes (A i) z := by
  classical
  let H := {i : I // 4*k ≤ Module.finrank K (A i).range}
  let X := SamplePair d k
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>pair_sample_bound (A (i:H).val) i.property)
  rw [←Finset.sum_mul] at sum
  simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,smul_eq_mul] at sum
  by_contra! fail
  have hit (x:X) : ∃i:H,vanishes (A i.val) x := by obtain ⟨i,hi,h⟩ := fail x;exact ⟨⟨i,hi⟩,h⟩
  have card := finiteUnion (X:=X) (fun i:H=>vanishes (k:=k) (A i.val))
  have all : Nat.card X ≤ Nat.card {x:X // ∃i:H,vanishes (A i.val) x} :=
    Nat.card_le_card_of_injective (fun x:X=>⟨x,hit x⟩) (fun _ _ e=>congrArg Subtype.val e)
  have lim := (Nat.mul_le_mul_right _ (all.trans card)).trans sum
  change Nat.card X*2^(2*k*k) ≤ Nat.card H*(2*Nat.card X) at lim
  have hc : Nat.card H ≤ 2^b := (Nat.card_le_card_of_injective (fun x:H=>x.val) Subtype.val_injective).trans hI
  have avoid : 2^b*2 < 2^(2*k*k) := by rw [←pow_succ];exact Nat.pow_lt_pow_right (by decide) budget
  have := Nat.mul_lt_mul_of_pos_right ((Nat.mul_le_mul_right _ hc).trans_lt avoid) (Nat.card_pos (α:=X))
  nlinarith only [lim,this]
end OrbitUp.MinSpan
end
section
namespace OrbitUp.MinSpan
open BoundedMatrices
abbrev Tensor (d b : ℕ) := V d→ₗ[K] V d→ₗ[K] V b
def minimalAlternating (d b σ : ℕ) := {β : Tensor d b //
    (∀x,β x x=0) ∧ valuesOn β ⊤=⊤ ∧ (∃S,valuesOn β S=⊤ ∧ Module.finrank K S=σ) ∧
    ∀S,valuesOn β S=⊤→σ ≤ Module.finrank K S}
def push {U W Z : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z] (f : W→ₗ[K] Z) (β : U→ₗ[K] U→ₗ[K] W) : U→ₗ[K] U→ₗ[K] Z where
  toFun x := f.comp (β x)
  map_add' x y := LinearMap.ext (fun z=>by change f (β (x+y) z)=_;rw [map_add,LinearMap.add_apply,map_add];rfl)
  map_smul' c x := LinearMap.ext (fun z=>by change f (β (c • x) z)=_;rw [map_smul,LinearMap.smul_apply,map_smul];rfl)
theorem push_values {U W Z : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z] (f : W→ₗ[K] Z) (β : U→ₗ[K] U→ₗ[K] W) (S : Submodule K U) :
    valuesOn (push f β) S=(valuesOn β S).map f := by
  simp only [valuesOn,Submodule.map_span,←Set.range_comp];rfl
theorem values_mono {U W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    (β : U→ₗ[K] U→ₗ[K] W) {S T : Submodule K U} (h : S ≤ T) : valuesOn β S ≤ valuesOn β T := by
  apply Submodule.span_mono
  rintro _ ⟨⟨x,y⟩,rfl⟩
  exact ⟨(⟨x.val,h x.property⟩,⟨y.val,h y.property⟩),rfl⟩
theorem complete_sample {d b σ : ℕ} (β : minimalAlternating d b σ) (S : Submodule K (V d)) :
    σ ≤ Module.finrank K S+Module.finrank K (valuesOn β.val S).dualAnnihilator+1 := by
  classical
  let T := valuesOn β.val S
  let q := T.mkQ
  let A := push q β.val
  have ha (x) : A x x=0 := by change q (β.val x x)=0;rw [β.property.1,map_zero]
  have full : valuesOn A ⊤=⊤ := by
    rw [push_values,β.property.2.1,Submodule.map_top,LinearMap.range_eq_top]
    exact T.mkQ_surjective
  letI : Finite (V b ⧸ T) := Finite.of_surjective _ T.mkQ_surjective
  obtain ⟨U,hu,dim⟩ := minimal_commutator_span A ha full
  let P := valuesOn β.val (S⊔U)
  have whole : P=⊤ := by
    have incl : T ≤ P := values_mono _ le_sup_left
    have un : (valuesOn β.val U).map q=⊤ := (push_values q β.val U).symm.trans hu
    have im : P.map q=⊤ := top_unique (un.ge.trans (Submodule.map_mono (values_mono _ le_sup_right)))
    have pre := congrArg (Submodule.comap q) im
    rwa [Submodule.comap_map_eq,Submodule.ker_mkQ,sup_eq_left.mpr incl,Submodule.comap_top] at pre
  have min := β.property.2.2.2 _ whole
  have plus := Submodule.finrank_sup_add_finrank_inf_eq S U
  have quo : Module.finrank K (V b ⧸ T)=Module.finrank K T.dualAnnihilator := (Subspace.quotEquivAnnihilator T).finrank_eq
  change Module.finrank K U ≤ Module.finrank K (V b ⧸ T)+1 at dim
  rw [quo] at dim
  change σ ≤ Module.finrank K S+Module.finrank K T.dualAnnihilator+1
  omega
theorem many_low_rank_components {d b σ k : ℕ} (β : minimalAlternating d b σ)
    (budget : b+1 < 2*k*k) :
    ∃ T : Submodule K (Module.Dual K (V b)),
      σ ≤ 4*k+Module.finrank K T+1 ∧ ∀f∈T,Module.finrank K (push f β.val).range < 4*k := by
  classical
  letI : Finite (Module.Dual K (V b)) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI := Fintype.ofFinite (Module.Dual K (V b))
  have card : Nat.card (Module.Dual K (V b))=2^b := by rw [Module.natCard_eq_pow_finrank (K:=K),Subspace.dual_finrank_eq,Module.finrank_fin_fun,Nat.card_zmod]
  obtain ⟨z,hz⟩ := simultaneous_nonvanish (d:=d) (fun f:Module.Dual K (V b)=>push f β.val) card.le budget
  let S₁ := Submodule.span K (Set.range z.1)
  let S₂ := Submodule.span K (Set.range z.2)
  let S := S₁⊔S₂
  let T := valuesOn β.val S
  have h₁ : Module.finrank K S₁ ≤ 2*k := (finrank_range_le_card _).trans_eq (Fintype.card_fin _)
  have h₂ : Module.finrank K S₂ ≤ 2*k := (finrank_range_le_card _).trans_eq (Fintype.card_fin _)
  have hS : Module.finrank K S ≤ 4*k := by have h := Submodule.finrank_sup_add_finrank_inf_eq S₁ S₂;change Module.finrank K (S₁⊔S₂ : Submodule K (V d)) ≤ 4*k;omega
  have complete := complete_sample β S
  change σ ≤ Module.finrank K S+Module.finrank K T.dualAnnihilator+1 at complete
  refine ⟨T.dualAnnihilator,by change σ ≤ 4*k+Module.finrank K T.dualAnnihilator+1;omega,fun f hf=>?_⟩
  by_contra! big
  apply hz f big
  intro i j
  change f (β.val (z.1 i) (z.2 j))=0
  apply (T.mem_dualAnnihilator f).mp hf
  exact Submodule.subset_span ⟨(⟨z.1 i,(show S₁ ≤ S from le_sup_left) (Submodule.subset_span ⟨i,rfl⟩)⟩,
    ⟨z.2 j,(show S₂ ≤ S from le_sup_right) (Submodule.subset_span ⟨j,rfl⟩)⟩),rfl⟩
end OrbitUp.MinSpan
end
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
def commutatorTail (G : Type*) [Group G] : Subgroup G :=
  Third G ⊔ (squareCore (commutator G)).map (commutator G).subtype
variable {G J : Type*} [Group G] [Group J]
theorem commutatorTail_le_derived (G : Type*) [Group G] : commutatorTail G ≤ commutator G := by
  refine sup_le ?_ ?_
  · exact Subgroup.commutator_le_left (commutator G) ⊤
  · rintro _ ⟨w,_,rfl⟩;exact w.property
theorem commutatorTail_map_of_parts (f : G→*J) (h₂ : (commutator G).map f=commutator J)
    (h₃ : (Third G).map f=Third J) : (commutatorTail G).map f=commutatorTail J := by
  let a := (f.comp (commutator G).subtype).codRestrict (commutator J) (fun w=>h₂ ▸
    (show f w.val∈(commutator G).map f from ⟨w.val,w.property,rfl⟩))
  have onto : Function.Surjective a := by
    intro w
    obtain ⟨v,hv,he⟩ := h₂.ge w.property
    exact ⟨⟨v,hv⟩,Subtype.ext he⟩
  rw [commutatorTail,commutatorTail,Subgroup.map_sup,h₃,Subgroup.map_map,←CentralKernelCount.squareCore_map a onto,Subgroup.map_map]
  rfl
theorem commutatorTail_map (f : G→*J) (hf : Function.Surjective f) :
    (commutatorTail G).map f=commutatorTail J :=
  commutatorTail_map_of_parts f (lower_map_top f hf 1) (lower_map_top f hf 2)
instance (G : Type*) [Group G] : (commutatorTail G).Characteristic :=
  Subgroup.characteristic_iff_map_le.mpr fun e=>(commutatorTail_map e.toMonoidHom e.surjective).le
theorem subgroup_tail_eq (H : Subgroup G) (hh : (commutator H).map H.subtype=commutator G) :
    (commutatorTail H).map H.subtype=commutatorTail G :=
  commutatorTail_map_of_parts _ hh (structural_third H hh)
theorem head_conditions (G : Type*) [Group G] :
    let Q := G ⧸ commutatorTail G
    Second Q ≤ Subgroup.center Q ∧ ∀w:Second Q,w*w=1 := by
  let q := QuotientGroup.mk' (commutatorTail G)
  have sq := QuotientGroup.mk'_surjective (commutatorTail G)
  have van : (commutatorTail G).map q=⊥ := (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' _).ge
  rw [commutatorTail_map q sq] at van
  refine ⟨?_,?_⟩
  · intro w hw
    apply Subgroup.mem_center_iff.mpr
    intro x
    exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (van ▸
      ((show Third _ ≤ commutatorTail (G⧸commutatorTail G) from le_sup_left) (show ⁅w,x⁆∈Third (G⧸commutatorTail G) from Subgroup.commutator_mem_commutator hw (Subgroup.mem_top x)) :
        ⁅w,x⁆∈commutatorTail (G⧸commutatorTail G))))).symm
  · intro w
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [←van]
    apply (show (squareCore (Second (G⧸commutatorTail G))).map (Second _).subtype ≤ commutatorTail _ from le_sup_right)
    exact ⟨w*w,Subgroup.subset_closure ⟨w,rfl⟩,rfl⟩
end Erdos1160.Sims
end
section
namespace CentralKernelCount
open scoped commutatorElement
theorem paired_of_order {E F : Type*} [Group E] [Group F] [Finite E] [Finite F] {d : ℕ}
    (T : Subgroup (E×F)) (x : Fin d → E×F)
    (genE : adjoin (T.map (MonoidHom.fst E F)) (fun i => (x i).1)=⊤)
    (genF : adjoin (T.map (MonoidHom.snd E F)) (fun i => (x i).2)=⊤)
    (ce : Nat.card (adjoin T x) ≤ Nat.card E) (cf : Nat.card (adjoin T x) ≤ Nat.card F) :
    Nonempty (E ≃* F) := by
  let S := adjoin T x
  let a := (MonoidHom.fst E F).comp S.subtype
  let b := (MonoidHom.snd E F).comp S.subtype
  have sa : Function.Surjective a := by
    intro y
    change y∈a.range
    rw [MonoidHom.range_comp,Subgroup.range_subtype,map_adjoin]
    exact genE ▸ (show y∈(⊤ : Subgroup E) from trivial)
  have sb : Function.Surjective b := by
    intro y
    change y∈b.range
    rw [MonoidHom.range_comp,Subgroup.range_subtype,map_adjoin]
    exact genF ▸ (show y∈(⊤ : Subgroup F) from trivial)
  exact ⟨(MulEquiv.ofBijective a (sa.bijective_of_nat_card_le ce)).symm.trans
    (MulEquiv.ofBijective b (sb.bijective_of_nat_card_le cf))⟩
end CentralKernelCount
end
section
namespace CentralKernelCount
open scoped commutatorElement
theorem card_adjoin_normalized_orders {G : Type*} [Group G] [Finite G] {d : ℕ} (T : Subgroup G)
    (x : Fin d → G) (ord : Fin d→ℕ) (ho : ∀ i,0 < ord i) (hn : ∀ i,x i ∈ Subgroup.normalizer T)
    (hs : ∀ i,x i ^ ord i ∈ T) (hc : ∀ i j, ⁅x i,x j⁆ ∈ T) :
    Nat.card (adjoin T x) ≤ (∏ i,ord i) * Nat.card T := by
  let N := Subgroup.normalizer (T : Set G)
  let U := T.subgroupOf N
  let y (i : Fin d) : N := ⟨x i,hn i⟩
  have su (i : Fin d) : y i ^ ord i ∈ U := hs i
  have cu (i j : Fin d) : ⁅y i,y j⁆ ∈ U := hc i j
  have count := card_adjoin_orders U y ord ho su cu
  have lower : U.map N.subtype=T := Subgroup.map_subgroupOf_eq_of_le T.le_normalizer
  have map_eq : (adjoin U y).map N.subtype = adjoin T x := (map_adjoin ..).trans (by rw [lower];rfl)
  calc
    _ = Nat.card (adjoin U y) := map_eq ▸ Subgroup.card_map_of_injective N.subtype_injective
    _ ≤ (∏ i,ord i) * Nat.card U := count
    _ = _ := congrArg ((∏ i,ord i) * ·) (Nat.card_congr (Subgroup.subgroupOfEquivOfLe T.le_normalizer).toEquiv)
end CentralKernelCount
end
section
namespace Erdos1160.Sims
open CentralKernelCount
open scoped commutatorElement
abbrev ExtraSlot (n t : ℕ) := (Fin n × Fin t) ⊕ PairSlot n
structure ExtensionMark (H E : Type*) [Group H] [Group E] (n : ℕ) where
  incl : H →* E
  x : Fin n→E
  generate : adjoin incl.range x=⊤
def ExtensionFits {H E : Type*} [Group H] [Group E] {n t : ℕ} (m : ExtensionMark H E n)
    (base : Fin t→H) (ord : Fin n→ℕ) (power : Fin n→H) (comm : ExtraSlot n t→H) : Prop :=
  (∀i,m.x i^ord i=m.incl (power i)) ∧
  (∀i j,⁅m.x i,m.incl (base j)⁆=m.incl (comm (.inl (i,j)))) ∧
  (∀z : PairSlot n,⁅m.x z.1,m.x (second z)⁆=m.incl (comm (.inr z)))
theorem restricted_extension_separation {H E J : Type*} [Group H] [Group E] [Group J]
    [Finite H] [Finite E] [Finite J] {n t : ℕ} (m : ExtensionMark H E n) (m' : ExtensionMark H J n)
    (base : Fin t→H) (hbase : Subgroup.closure (Set.range base)=⊤)
    (ord : Fin n→ℕ) (ho : ∀i,0 < ord i) (power : Fin n→H) (comm : ExtraSlot n t→H)
    (he : ExtensionFits m base ord power comm) (hj : ExtensionFits m' base ord power comm)
    (ce : (∏i,ord i)*Nat.card H ≤ Nat.card E) (cj : (∏i,ord i)*Nat.card H ≤ Nat.card J) :
    Nonempty (E≃*J) := by
  let f := m.incl.prod m'.incl
  let T := f.range
  let x (i : Fin n) := (m.x i,m'.x i)
  have tgen : Subgroup.closure (Set.range (f ∘ base))=T := by
    rw [Set.range_comp,←MonoidHom.map_closure,hbase,←f.range_eq_map]
  have normal (i : Fin n) : x i∈Subgroup.normalizer T := by
    let c := (MulAut.conj (x i)).toMonoidHom
    have le : T.map c ≤ T := by
      calc
        T.map c = Subgroup.closure (c '' Set.range (f ∘ base)) := by rw [←MonoidHom.map_closure,tgen]
        _ ≤ T := ?_
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨_,⟨j,rfl⟩,rfl⟩
      change x i*f (base j)*(x i)⁻¹∈T
      have eq : x i*f (base j)*(x i)⁻¹=⁅x i,f (base j)⁆*f (base j) := by rw [commutatorElement_def];group
      rw [eq]
      exact T.mul_mem ⟨comm (.inl (i,j)),Prod.ext (he.2.1 i j).symm (hj.2.1 i j).symm⟩ ⟨base j,rfl⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge le
      (Subgroup.card_map_of_injective (MulAut.conj (x i)).injective).ge)
  have pw (i : Fin n) : x i^ord i∈T := ⟨power i,Prod.ext (he.1 i).symm (hj.1 i).symm⟩
  have half (z : PairSlot n) : ⁅x z.1,x (second z)⁆∈T :=
    ⟨comm (.inr z),Prod.ext (he.2.2 z).symm (hj.2.2 z).symm⟩
  have cross (i j : Fin n) : ⁅x i,x j⁆∈T := by
    rcases lt_trichotomy i j with h|rfl|h
    · rw [←commutatorElement_inv];exact T.inv_mem (half ⟨j,⟨i.val,h⟩⟩)
    · simpa using T.one_mem
    · exact half ⟨i,⟨j.val,h⟩⟩
  have bound := (card_adjoin_normalized_orders T x ord ho normal pw cross).trans
    (Nat.mul_le_mul_left _ (Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective))
  apply paired_of_order T x _ _ (bound.trans ce) (bound.trans cj)
  · change adjoin (f.range.map _) m.x=⊤
    rw [←MonoidHom.range_comp];exact m.generate
  · change adjoin (f.range.map _) m'.x=⊤
    rw [←MonoidHom.range_comp];exact m'.generate
theorem extraSlot_card (n t : ℕ) : Nat.card (ExtraSlot n t)=n*t+n*(n-1)/2 := by
  rw [ExtraSlot,Nat.card_sum,Nat.card_prod,Nat.card_fin,Nat.card_fin]
  congr 1
  rw [PairSlot,Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ=>i) n).trans (Finset.sum_range_id n)
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open CentralKernelCount
private lemma coset_card_le {H V : Type*} [Group H] [Group V] [Finite H] (π : H→*V) (v : V) :
    Nat.card {w : H // π w=v}≤Nat.card π.ker := by
  classical
  by_cases h : Nonempty {w : H // π w=v}
  · let z := h.some
    let T (w : {w : H // π w=v}) : π.ker := ⟨w.val*z.val⁻¹,by
      change π (_*_)=1;rw [map_mul,map_inv,w.property,z.property,mul_inv_cancel]⟩
    exact Nat.card_le_card_of_injective T (fun a b e=>Subtype.ext (mul_right_cancel (congrArg (fun k : π.ker=>k.val) e)))
  · let _ : IsEmpty {w : H // π w=v} := not_nonempty_iff.mp h
    simp
theorem restricted_extension_count {I H V : Type} [Group H] [Finite H] [Group V] {n t : ℕ}
    (E : I→Type) [∀i,Group (E i)] [∀i,Finite (E i)] (mark : ∀i,ExtensionMark H (E i) n)
    (base : Fin t→H) (hbase : Subgroup.closure (Set.range base)=⊤)
    (ord : Fin n→ℕ) (ho : ∀i,0 < ord i) (π : H→*V) (pattern : ExtraSlot n t→V)
    (w : I→Fin n→H) (c : I→ExtraSlot n t→H) (hc : ∀i z,π (c i z)=pattern z)
    (fits : ∀i,ExtensionFits (mark i) base ord (w i) (c i))
    (size : ∀i,(∏j,ord j)*Nat.card H ≤ Nat.card (E i))
    (sep : ∀i j,Nonempty (E i≃*E j)→i=j) :
    Nat.card I ≤ Nat.card H^n*Nat.card π.ker^(n*t+n*(n-1)/2) := by
  classical
  let C (z : ExtraSlot n t) := {v : H // π v=pattern z}
  let enc (i : I) : (Fin n→H) × ((z : ExtraSlot n t)→C z) :=
    (w i,fun z=>⟨c i z,hc i z⟩)
  have hi : Function.Injective enc := by
    intro i j h
    have e₁ : w i=w j := congrArg Prod.fst h
    have e₂ : c i=c j := funext (fun z=>congrArg (fun a : (Fin n→H) × ((z : ExtraSlot n t)→C z)=>(a.2 z).val) h)
    apply sep i j
    exact restricted_extension_separation (mark i) (mark j) base hbase ord ho (w i) (c i) (fits i)
      (e₁ ▸ e₂ ▸ fits j) (size i) (size j)
  calc
    _ ≤ Nat.card ((Fin n→H) × ((z : ExtraSlot n t)→C z)) := Nat.card_le_card_of_injective _ hi
    _ = Nat.card H^n*∏ z,Nat.card (C z) := by rw [Nat.card_prod,Nat.card_fun,Nat.card_fin,Nat.card_pi]
    _ ≤ Nat.card H^n*∏ _z : ExtraSlot n t,Nat.card π.ker :=
      Nat.mul_le_mul_left _ (Finset.prod_le_prod' (fun z _=>coset_card_le π (pattern z)))
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,←Nat.card_eq_fintype_card,extraSlot_card]
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi (Second secondBracket lower_map_top)
open Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] (H : Subgroup G)
abbrev headQuot (G : Type) [Group G] := G ⧸ commutatorTail G
abbrev headMap (G : Type) [Group G] : G→*headQuot G := QuotientGroup.mk' (commutatorTail G)
abbrev headSub := (H.map (headMap G))
def toHeadSub : H→*headSub H := ((headMap G).comp H.subtype).codRestrict _ (fun x=>⟨x.val,x.property,rfl⟩)
theorem toHeadSub_surj : Function.Surjective (toHeadSub H) := by
  rintro ⟨_,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩
theorem toHeadSub_kernel (hh : (commutator H).map H.subtype=commutator G) :
    (toHeadSub H).ker=commutatorTail H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [subgroup_tail_eq H hh]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp (congrArg (fun v:headSub H=>v.val) hy)
  · intro hx
    have incl : commutatorTail G ≤ H := (commutatorTail_le_derived G).trans
      (hh ▸ (Subgroup.map_subtype_le _))
    refine ⟨⟨x,incl hx⟩,?_,rfl⟩
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
theorem head_derived_image (hh : (commutator H).map H.subtype=commutator G) :
    (Second (headSub H)).map (headSub H).subtype=Second (headQuot G) := by
  have part : (Second H).map (toHeadSub H)=Second (headSub H) := lower_map_top _ (toHeadSub_surj H) 1
  rw [←part,Subgroup.map_map,
    show (headSub H).subtype.comp (toHeadSub H)=(headMap G).comp H.subtype from rfl,←Subgroup.map_map]
  change ((commutator H).map H.subtype).map _=_
  rw [hh];exact lower_map_top _ (QuotientGroup.mk'_surjective _) 1
noncomputable def derivedHeadEquiv (hh : (commutator H).map H.subtype=commutator G) :
    Second (headSub H)≃*Second (headQuot G) :=
  ((Second (headSub H)).equivMapOfInjective (headSub H).subtype (headSub H).subtype_injective).trans
    (MulEquiv.subgroupCongr (head_derived_image H hh))
theorem headSub_class_two : Second (headSub H) ≤ Subgroup.center (headSub H) := by
  intro x hx
  have le : (commutator (headSub H)).map (headSub H).subtype ≤ commutator (headQuot G) := by
    rw [Subgroup.map_subtype_commutator];exact Subgroup.commutator_mono le_top le_top
  have mem : (x:headQuot G)∈Second (headQuot G) := le ⟨x,hx,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.mp ((head_conditions G).1 mem) y.val)
theorem headSub_derived_binary (hh : (commutator H).map H.subtype=commutator G) :
    ∀w:Second (headSub H),w*w=1 := by
  intro w
  apply (derivedHeadEquiv H hh).injective
  rw [map_mul,map_one]
  exact (head_conditions G).2 _
theorem headSub_kernel_frattini {m : ℕ} (hH : Nat.card H=2^m)
    (hh : (commutator H).map H.subtype=commutator G) : (toHeadSub H).ker ≤ frattini H := by
  rw [toHeadSub_kernel H hh,frattini_eq_squareCore hH]
  exact (commutatorTail_le_derived H).trans (Erdos1160.CentralLifts.Survival.derived_le_squares H)
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
open OrbitUp OrbitUp.MinSpan
open scoped commutatorElement
variable {G J W : Type*} [Group G] [Group J] [CommGroup W]
private theorem central_bracket_left (hc : Second J ≤ Subgroup.center J) (x y z : J) :
    secondBracket (x*y) z=secondBracket x z*secondBracket y z := by
  apply Subtype.ext
  change ⁅x*y,z⁆=⁅x,z⁆*⁅y,z⁆
  have a := Subgroup.mem_center_iff.mp (hc (secondBracket y z).property) x
  have b := Subgroup.mem_center_iff.mp (hc (secondBracket x z).property) ⁅y,z⁆
  change x*⁅y,z⁆=⁅y,z⁆*x at a
  change ⁅y,z⁆*⁅x,z⁆=⁅x,z⁆*⁅y,z⁆ at b
  rw [commutatorElement_mul_left_eq_conj_mul,a,mul_inv_cancel_right,b]
private theorem central_bracket_right (hc : Second J ≤ Subgroup.center J) (x y z : J) :
    secondBracket x (y*z)=secondBracket x y*secondBracket x z := by
  apply Subtype.ext
  change ⁅x,y*z⁆=⁅x,y⁆*⁅x,z⁆
  have a := Subgroup.mem_center_iff.mp (hc (secondBracket x z).property) y
  change y*⁅x,z⁆=⁅x,z⁆*y at a
  rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc ⁅x,y⁆ y,mul_assoc ⁅x,y⁆,a,mul_inv_cancel_right]
def headBiHom (q : G→*J) (hc : Second J ≤ Subgroup.center J) (a : Second J→*W) :
    G→*(G→*W) where
  toFun x := {
    toFun y := a (secondBracket (q x) (q y))
    map_one' := by rw [q.map_one,show secondBracket (q x) 1=1 from Subtype.ext (commutatorElement_one_right _),a.map_one]
    map_mul' y z := by rw [q.map_mul,central_bracket_right hc,a.map_mul] }
  map_one' := by
    apply MonoidHom.ext;intro y
    change a (secondBracket (q 1) (q y))=1
    rw [q.map_one,show secondBracket 1 (q y)=1 from Subtype.ext (commutatorElement_one_left _),a.map_one]
  map_mul' x y := by
    apply MonoidHom.ext;intro z
    change a (secondBracket (q (x*y)) (q z))=a (secondBracket (q x) (q z))*a (secondBracket (q y) (q z))
    rw [q.map_mul,central_bracket_left hc,a.map_mul]
theorem squareCore_killed {E K : Type*} [Group E] [Group K] (v : E→*K) (hb : ∀x:K,x*x=1) :
    squareCore E ≤ v.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨x,rfl⟩
  change v (x*x)=1
  rw [v.map_mul,hb]
theorem exists_head_tensor {d b : ℕ} (p : G→*Multiplicative (OrbitUp.V d)) (sp : Function.Surjective p)
    (kp : p.ker=squareCore G) (q : G→*J) (sq : Function.Surjective q) (hc : Second J ≤ Subgroup.center J)
    (a : Second J≃*Multiplicative (OrbitUp.V b)) :
    ∃ β : Tensor d b, (∀x,β x x=0) ∧ BoundedMatrices.valuesOn β ⊤=⊤ ∧
      ∀x y,β (p x).toAdd (p y).toAdd=(a (secondBracket (q x) (q y))).toAdd := by
  let A := headBiHom q hc a.toMonoidHom
  have bin (w : Multiplicative (OrbitUp.V b)) : w*w=1 := by
    apply Multiplicative.toAdd.injective
    funext i
    exact (show ∀z:OrbitUp.K,z+z=0 by decide) _
  obtain ⟨B,hB⟩ := descend_pair p sp p sp A (kp ▸ squareCore_killed A (fun v=>MonoidHom.ext fun _=>bin _))
    (fun x=>kp ▸ squareCore_killed (A x) bin)
  let B' : OrbitUp.V d→+OrbitUp.V d→+OrbitUp.V b := {
    toFun x := (B (.ofAdd x)).toAdditive
    map_zero' := by rw [show Multiplicative.ofAdd (0:OrbitUp.V d)=1 from rfl,B.map_one];rfl
    map_add' x y := by rw [show Multiplicative.ofAdd (x+y)=Multiplicative.ofAdd x*Multiplicative.ofAdd y from rfl,B.map_mul];rfl }
  let β : Tensor d b := (((AddMonoidHom.toZModLinearMapEquiv 2).toAddMonoidHom.comp B').toZModLinearMap 2)
  have spec (x y : G) : β (p x).toAdd (p y).toAdd=(a (secondBracket (q x) (q y))).toAdd :=
    congrArg Multiplicative.toAdd (hB x y)
  refine ⟨β,?_,?_,spec⟩
  · intro x
    obtain ⟨u,hu⟩ := sp (.ofAdd x)
    have e : (p u).toAdd=x := congrArg Multiplicative.toAdd hu
    rw [←e,spec,show secondBracket (q u) (q u)=1 from Subtype.ext (commutatorElement_self _),a.map_one]
    rfl
  · let L := BoundedMatrices.valuesOn β ⊤
    let T : Subgroup (Second J) := { carrier := {w | (a w).toAdd∈L}
                                     one_mem' := by change (a 1).toAdd∈L; rw [a.map_one]; exact L.zero_mem
                                     mul_mem' := fun {x y} hx hy=>by change (a (x*y)).toAdd∈L;rw [map_mul];exact L.add_mem hx hy
                                     inv_mem' := fun {x} hx=>by change (a x⁻¹).toAdd∈L;rw [map_inv];exact L.neg_mem hx }
    have all : commutator J ≤ T.map (Second J).subtype := by
      rw [commutator_eq_closure,Subgroup.closure_le]
      rintro _ ⟨u,v,rfl⟩
      obtain ⟨x,rfl⟩ := sq u
      obtain ⟨y,rfl⟩ := sq v
      refine ⟨secondBracket _ _,?_,rfl⟩
      change (a (secondBracket (q x) (q y))).toAdd∈L
      rw [←spec]
      exact Submodule.subset_span ⟨(⟨_,Submodule.mem_top⟩,⟨_,Submodule.mem_top⟩),rfl⟩
    apply top_unique
    intro u _
    let w := a.symm (.ofAdd u)
    obtain ⟨v,hv,e⟩ := all w.property
    have h : v=w := Subtype.ext e
    change (a v).toAdd∈L at hv
    rw [h,show a w=.ofAdd u from a.apply_symm_apply _] at hv
    exact hv
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi (Second secondMap secondBracket)
open OrbitUp OrbitUp.MinSpan
open OrbitUp.BoundedMatrices
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {d b : ℕ}
def vectorSub {d : ℕ} (H : Subgroup (Multiplicative (V d))) : Submodule K (V d) where
  carrier := {x | Multiplicative.ofAdd x∈H}
  zero_mem' := H.one_mem
  add_mem' := H.mul_mem
  smul_mem' k x hx := by
    rcases (show ∀k:K,k=0 ∨ k=1 by decide) k with rfl|rfl
    · rw [zero_smul];exact H.one_mem
    · rwa [one_smul]
theorem subgroup_of_spanning (hG : IsPGroup 2 G) (p : G→*Multiplicative (V d))
    (a : Second (G⧸commutatorTail G)≃*Multiplicative (V b)) (β : Tensor d b)
    (spec : ∀x y,β (p x).toAdd (p y).toAdd=(a (secondBracket
      ((QuotientGroup.mk' (commutatorTail G)) x) ((QuotientGroup.mk' (commutatorTail G)) y))).toAdd)
    (H : Subgroup G) (S : Submodule K (V d)) (hS : valuesOn β S=⊤)
    (covers : ∀u:S,∃x:H,(p x.val).toAdd=u.val) :
    (commutator H).map H.subtype=commutator G := by
  let q := QuotientGroup.mk' (commutatorTail G)
  have sq := QuotientGroup.mk'_surjective (commutatorTail G)
  let D := (commutator H).map H.subtype
  have hD : D ≤ commutator G := by
    rw [show D=⁅H,H⁆ from Subgroup.map_subtype_commutator H]
    exact Subgroup.commutator_mono le_top le_top
  let z := (D.map q).comap (Second (G⧸commutatorTail G)).subtype
  let W := vectorSub (z.map a.toMonoidHom)
  have incl : valuesOn β S ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u,v⟩,rfl⟩
    obtain ⟨x,ex⟩ := covers u
    obtain ⟨y,ey⟩ := covers v
    change β u.val v.val∈W
    rw [←ex,←ey,spec]
    refine ⟨secondBracket (q x.val) (q y.val),?_,rfl⟩
    exact ⟨⁅x.val,y.val⁆,⟨(secondBracket x y).val,(secondBracket x y).property,rfl⟩,map_commutatorElement q _ _⟩
  rw [hS] at incl
  have all : (commutator G).map q ≤ D.map q := by
    rintro _ ⟨u,hu,rfl⟩
    let w := secondMap q sq ⟨u,hu⟩
    have mem := incl (Submodule.mem_top : (a w).toAdd∈⊤)
    obtain ⟨v,hv,ev⟩ := mem
    change v.val∈D.map q at hv
    rw [a.injective ev] at hv
    exact hv
  apply structural_derived hG H
  have hh := Subgroup.map_le_iff_le_comap.mp all
  rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk'] at hh
  exact hh
omit [Finite G] in
theorem lift_subspace (p : G→*Multiplicative (V d)) (sp : Function.Surjective p)
    (S : Submodule K (V d)) :
    ∃ (H : Subgroup G) (x : Fin (Module.finrank K S)→H),
      Subgroup.closure (Set.range x)=⊤ ∧ vectorSub (H.map p)=S := by
  classical
  let B := Module.finBasis K S
  choose y hy using fun i=>sp (Multiplicative.ofAdd (B i).val)
  let H := Subgroup.closure (Set.range y)
  let x (i) : H := ⟨y i,Subgroup.subset_closure ⟨i,rfl⟩⟩
  have hx : Subgroup.closure (Set.range x)=⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [MonoidHom.map_closure,←Set.range_comp,←MonoidHom.range_eq_map,H.range_subtype]
    rfl
  refine ⟨H,x,hx,le_antisymm ?_ ?_⟩
  · let T := S.toAddSubgroup.toSubgroup
    have le : H.map p ≤ T := by
      rw [show H=Subgroup.closure (Set.range y) from rfl,MonoidHom.map_closure,Subgroup.closure_le]
      rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
      rw [hy]
      exact (B i).property
    exact le
  · have bc : Submodule.span K (Set.range (fun i=>(B i).val))=S := by
      rw [show (fun i=>(B i).val)=S.subtype ∘ B from rfl,Set.range_comp,←Submodule.map_span,B.span_eq,Submodule.map_top,Submodule.range_subtype]
    rw [←bc]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨y i,(x i).property,hy i⟩
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi (Second)
open Erdos1160Growth.LowerTriangularUpper (squareCore)
open Erdos1160.CentralLifts.Survival (derived_le_squares)
open OrbitUp
variable {G : Type} [Group G] [Finite G] {m d b : ℕ}
theorem head_size_budget (hG : Nat.card G=2^m) (p : G→*Multiplicative (V d)) (sp : Function.Surjective p)
    (kp : p.ker=squareCore G) (der : Nat.card (Second (headQuot G))=2^b) {t : ℕ}
    (tail : Nat.card (commutatorTail G)=2^t) : d+b+t ≤ m := by
  have van : commutatorTail G ≤ p.ker := kp ▸ (commutatorTail_le_derived G).trans (derived_le_squares G)
  let f := QuotientGroup.lift (commutatorTail G) p van
  have sf : Function.Surjective f := by
    intro w
    obtain ⟨u,rfl⟩ := sp w
    exact ⟨(headMap G) u,rfl⟩
  have incl : Second (headQuot G) ≤ f.ker := Abelianization.commutator_subset_ker f
  have large : 2^b ≤ Nat.card f.ker := der ▸ Nat.card_le_card_of_injective (Subgroup.inclusion incl) (Subgroup.inclusion_injective incl)
  have ix : f.ker.index=2^d := by
    rw [Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective f sf,Subgroup.card_top]
    change Nat.card (Fin d→ZMod 2)=_
    rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  have hhead := f.ker.index_mul_card
  rw [ix] at hhead
  have ch : 2^d*2^b ≤ Nat.card (headQuot G) := (Nat.mul_le_mul_left _ large).trans_eq hhead
  have eq := (commutatorTail G).card_eq_card_quotient_mul_card_subgroup
  rw [hG,tail] at eq
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [pow_add,pow_add]
  exact (Nat.mul_le_mul_right _ ch).trans_eq eq.symm
theorem inside_tail_card (H : Subgroup G) (hh : (commutator H).map H.subtype=commutator G) :
    Nat.card (toHeadSub H).ker=Nat.card (commutatorTail G) := by
  rw [toHeadSub_kernel H hh,←subgroup_tail_eq H hh,Subgroup.card_map_of_injective H.subtype_injective]
theorem card_of_onto {A B : Type*} [Group A] [Group B] (f : A→*B) (sf : Function.Surjective f) :
    Nat.card A=Nat.card B*Nat.card f.ker := by
  rw [←f.ker.index_mul_card,Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective f sf,Subgroup.card_top]
end Erdos1160.Sims
end
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi
open scoped commutatorElement
variable {d m : ℕ} {Q : Type} [Group Q] [Finite Q]
noncomputable def jacobiRank (Q : Type) [Group Q] := Module.finrank (ZMod 2) (Additive (JacobiDual Q))
theorem cover_class_two_decomposition (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (hclass : Second Q ≤ Subgroup.center Q) :
    ∃ (Y : FiniteGrp.{0}) (j : ℕ) (f : Y →* Q) (g : FreeGroup (Fin d) →* Y),
      Function.Surjective f ∧ Function.Surjective g ∧ IsPGroup 2 Y ∧ Second Y ≤ Subgroup.center Y ∧
      f.ker ≤ Subgroup.center Y ∧ (∀x:f.ker,x*x=1) ∧ j ≤ jacobiRank Q ∧
      Nat.card (Cover π)=Nat.card Y * 2^j := by
  let φ := coverProjection π
  have hφ := cover_onto π hπ
  have hc := cover_card π hπ
  rw [hQ,←pow_add] at hc
  let _ : Finite (Cover π) := Nat.finite_of_card_ne_zero (hc ▸ Nat.ne_of_gt (Nat.two_pow_pos _))
  have hp := IsPGroup.of_card hc
  let N := Third (Cover π)
  have hN : N≤φ.ker := by
    apply Subgroup.commutator_le.mpr
    intro w hw x _
    rw [MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hclass (secondMap φ hφ ⟨w,hw⟩).property) _).symm
  let Y := Cover π ⧸ N
  let h := QuotientGroup.mk' N
  have sh := QuotientGroup.mk'_surjective N
  let f := QuotientGroup.lift N φ hN
  have sf : Function.Surjective f := fun z => by obtain ⟨u,rfl⟩ := hφ z;exact ⟨h u,rfl⟩
  let g := h.comp (QuotientGroup.mk' (universalKernel π))
  have sg := sh.comp (QuotientGroup.mk'_surjective _)
  have hfc : f.ker ≤ Subgroup.center Y := by
    intro u hu
    obtain ⟨w,rfl⟩ := sh u
    have hw : w∈φ.ker := hu
    apply Subgroup.mem_center_iff.mpr
    intro z
    obtain ⟨v,rfl⟩ := sh z
    exact (map_mul h _ _).symm.trans ((congrArg h (Subgroup.mem_center_iff.mp (cover_central π hw) v)).trans (map_mul h _ _))
  have hfs (u : f.ker) : u*u=1 := by
    apply Subtype.ext
    obtain ⟨w,hw⟩ := sh u.val
    have hφw : w∈φ.ker := by change f (h w)=1;rw [hw];exact u.property
    change u.val*u.val=1
    rw [←hw,←map_mul,show w*w=1 from congrArg Subtype.val (cover_binary π ⟨w,hφw⟩),map_one]
  obtain ⟨j,hj⟩ := (hp.to_subgroup N).exists_card_eq
  have hns (u : N) : u*u=1 := Subtype.ext (congrArg (fun v : (coverProjection π).ker => v.val) (cover_binary π ⟨u.val,hN u.property⟩))
  have rank := elementary_third_dimension φ hφ (cover_central π) (hN.trans (cover_central π)) hns hj
  exact ⟨FiniteGrp.of Y,j,f,g,sf,sg,hp.to_quotient N,ThirdLowerCentral.quotient_has_class_two _,hfc,hfs,rank,
    N.card_eq_card_quotient_mul_card_subgroup.trans (congrArg (Nat.card Y * ·) hj)⟩
theorem multiplicator_rank_of_class_bound (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (hclass : Second Q ≤ Subgroup.center Q) {D : ℕ}
    (h : ∀ (Y : FiniteGrp.{0}) (f : Y →* Q) (g : FreeGroup (Fin d) →* Y),
      Function.Surjective f → Function.Surjective g → IsPGroup 2 Y → Second Y ≤ Subgroup.center Y →
      f.ker ≤ Subgroup.center Y → (∀x:f.ker,x*x=1) → Nat.card Y ≤ Nat.card Q*2^D) :
    relRank π ≤ D+jacobiRank Q := by
  obtain ⟨Y,j,f,g,hf,hg,hp,hc,hk,hb,hj,hcard⟩ := cover_class_two_decomposition π hπ hQ hclass
  have a := Nat.mul_le_mul (h Y f g hf hg hp hc hk hb) (Nat.pow_le_pow_right (by decide : 0 < 2) hj)
  rw [←hcard,cover_card π hπ,Nat.mul_assoc,←pow_add,Nat.mul_comm (2^(relRank π)),hQ,←pow_add,←pow_add] at a
  have n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp a
  omega
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
private theorem generated_map {G J ι : Type} [Group G] [Group J] (v : ι → G)
    (hgen : Subgroup.closure (Set.range v)=⊤) (π : G →* J) (hπ : Function.Surjective π) :
    Subgroup.closure (Set.range (π ∘ v))=⊤ := by
  rw [Set.range_comp,←MonoidHom.map_closure,hgen,Subgroup.map_top_of_surjective π hπ]
private theorem abelian_binary_torsion {A ι : Type} [CommGroup A] [Finite A] [Fintype ι]
    (v : ι → A) (hgen : Subgroup.closure (Set.range v)=⊤) :
    Nat.card (powMonoidHom (α := A) 2).ker ≤ 2^(Fintype.card ι) := by
  classical
  let s := powMonoidHom (α := A) 2
  let R := s.range
  let π := QuotientGroup.mk' R
  have heq : Nat.card s.ker=Nat.card (A ⧸ R) := by
    have h1 := s.ker.index_mul_card
    rw [Subgroup.index_ker] at h1
    have h2 := R.card_mul_index
    exact Nat.eq_of_mul_eq_mul_left (by exact Nat.card_pos : 0 < Nat.card R) (h1.trans h2.symm)
  let T := Finset.univ.image (π ∘ v)
  have hc : Subgroup.closure (T:Set (A ⧸ R))=⊤ := by
    have eqs : (T : Set (A ⧸ R)) = Set.range (π ∘ v) := by ext x; simp [T,Function.comp_def]
    rw [eqs]; exact generated_map v hgen π (QuotientGroup.mk'_surjective R)
  have hsize : Group.rank (A ⧸ R) ≤ Fintype.card ι :=
    (Group.rank_le hc).trans (Finset.card_image_le.trans_eq (Finset.card_univ : (Finset.univ : Finset ι).card=_))
  have exp (x : A ⧸ R) : x^2=1 := by
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective R x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨q,rfl⟩
  exact heq.le.trans ((Nat.le_of_dvd (Nat.two_pow_pos _) (card_dvd_exponent_pow_rank' _ exp)).trans
    (Nat.pow_le_pow_right (by decide) hsize))
theorem generated_class_two_cover_bound {d : ℕ} {Y Q : Type} [Group Y] [Group Q] [Finite Y] [Finite Q]
    (f : Y →* Q) (hf : Function.Surjective f) (hker2 : ∀ x : f.ker, x*x=1)
    (hY : Second Y ≤ Subgroup.center Y) (g : FreeGroup (Fin d) →* Y) (hg : Function.Surjective g) :
    Nat.card Y ≤ Nat.card Q*2^(d*(d+1)/2) := by
  classical
  let u (i : Fin d) := g (FreeGroup.of i)
  have hgen : Subgroup.closure (Set.range u)=⊤ := generated_map _ (FreeGroup.closure_range_of _) g hg
  let T := (i : Fin d) × Fin i.val
  let bracket (i : T) := ⁅u i.1,u (⟨i.2.val,i.2.isLt.trans i.1.isLt⟩ : Fin d)⁆
  let C := Subgroup.closure (Set.range bracket)
  have hc : C ≤ Subgroup.center Y := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact hY (secondBracket (u i.1) (u (⟨i.2.val,i.2.isLt.trans i.1.isLt⟩ : Fin d))).property
  letI : C.Normal := ⟨fun x hx y => by
    rw [Subgroup.mem_center_iff.mp (hc hx) y,mul_inv_cancel_right]; exact hx⟩
  let groupC : Group C := inferInstance
  letI : CommGroup C := { groupC with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hc b.property) a) }
  let w (i : T) : C := ⟨bracket i,Subgroup.subset_closure ⟨i,rfl⟩⟩
  have hCgen : Subgroup.closure (Set.range w)=⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [MonoidHom.map_closure,←Set.range_comp,←MonoidHom.range_eq_map,C.range_subtype]
    rfl
  let π := QuotientGroup.mk' C
  let q := π ∘ u
  have hq := generated_map u hgen π (QuotientGroup.mk'_surjective C)
  have hpairs (i j : Fin d) (h : j < i) : q i*q j=q j*q i := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅π (u i),π (u j)⁆=1
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨⟨i,⟨j.val,h⟩⟩,rfl⟩)
  have hcomm : IsMulCommutative (Subgroup.closure (Set.range q)) := by
    apply Subgroup.isMulCommutative_closure
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    rcases lt_trichotomy i j with h|h|h
    · exact (hpairs _ _ h).symm
    · rw [h]
    · exact hpairs _ _ h
  change Subgroup.closure (Set.range q)=⊤ at hq
  rw [hq] at hcomm
  let groupQ : Group (Y ⧸ C) := inferInstance
  letI : CommGroup (Y ⧸ C) := { groupQ with
    mul_comm := fun a b => congrArg Subtype.val (hcomm.is_comm.comm (⟨a,trivial⟩ : (⊤ : Subgroup (Y ⧸ C))) ⟨b,trivial⟩) }
  let ψ := π.comp f.ker.subtype
  let qsq := powMonoidHom (α := Y ⧸ C) 2
  let csq := powMonoidHom (α := C) 2
  have him : ψ.range ≤ qsq.ker := by
    rintro _ ⟨x,rfl⟩
    change (ψ x)^2=1
    rw [←map_pow,pow_two,hker2,map_one]
  let lift (x : ψ.ker) : C := ⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩
  let κ (x : ψ.ker) : csq.ker := ⟨lift x,by
    apply Subtype.ext
    change x.val.val^2=1
    rw [pow_two]
    exact congrArg Subtype.val (hker2 x.val)⟩
  have inj : Function.Injective κ := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : csq.ker => z.val.val) h))
  have hk := (Nat.card_le_card_of_injective κ inj).trans (abelian_binary_torsion w hCgen)
  have hi := (Nat.card_le_card_of_injective (Subgroup.inclusion him) (Subgroup.inclusion_injective him)).trans
    (abelian_binary_torsion q hq)
  have he : Nat.card f.ker = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [←Subgroup.index_ker,Subgroup.index_mul_card]
  have hcT : d+Fintype.card T=d*(d+1)/2 := by
    change d+Fintype.card (Σ i : Fin d,Fin i.val)=_
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun i => i),Nat.add_comm,←Finset.sum_range_succ,Finset.sum_range_id]
    simp only [Nat.add_sub_cancel,Nat.mul_comm]
  calc
    _ = Nat.card Q * Nat.card f.ker := by
      rw [←f.ker.index_mul_card,Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective f hf,Subgroup.card_top]
    _ ≤ Nat.card Q*(2^Fintype.card (Fin d)*2^Fintype.card T) := Nat.mul_le_mul_left _ (he.le.trans (Nat.mul_le_mul hi hk))
    _ = _ := by rw [←pow_add,Fintype.card_fin,hcT]
end Erdos1160.DeepJacobi
end
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi
variable {d t m : ℕ} {Q : Type} [Group Q] [Finite Q]
theorem class_two_multiplicator_bound (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (hclass : Second Q ≤ Subgroup.center Q) :
    relRank π ≤ d*(d+1)/2+jacobiRank Q :=
  multiplicator_rank_of_class_bound π hπ hQ hclass
    (fun _ f g hf hg _ hc _ hb => generated_class_two_cover_bound f hf hb hc g hg)
theorem marked_jacobi_fiber_product (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (hclass : Second Q ≤ Subgroup.center Q) (j : ℕ) :
    (frattiniClasses m j Q).ncard ≤ ∏ i ∈ Finset.range j,(2^(d*(d+1)/2+jacobiRank Q+i*d)-1) := by
  apply (multiplicator_fiber_product π hπ hQ j).trans
  apply Finset.prod_le_prod'
  intro i _
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right (class_two_multiplicator_bound π hπ hQ hclass) _)
end Erdos1160.CentralLifts.Survival
end
section
namespace Erdos1160.Sims
open CentralKernelCount
open scoped commutatorElement
theorem root_pattern_count {I W : Type} [Group W] [Finite W] {r b : ℕ}
    (E : I→Type) [∀i,Group (E i)] [∀i,Finite (E i)] (mark : ∀i,ExtensionMark W (E i) r)
    (base : Fin b→W) (hbase : Subgroup.closure (Set.range base)=⊤)
    (central : ∀i,(mark i).incl.range ≤ Subgroup.center (E i))
    (ord : Fin r→ℕ) (ho : ∀i,0 < ord i) (pattern : PairSlot r→W)
    (pows : ∀i j,∃v,(mark i).x j^ord j=(mark i).incl v)
    (comm : ∀i (z : PairSlot r),⁅(mark i).x z.1,(mark i).x (second z)⁆=(mark i).incl (pattern z))
    (size : ∀i,(∏j,ord j)*Nat.card W ≤ Nat.card (E i))
    (sep : ∀i j,Nonempty (E i≃*E j)→i=j) : Nat.card I ≤ Nat.card W^r := by
  classical
  choose w hw using pows
  let c : ExtraSlot r b→W := Sum.elim (fun _=>1) pattern
  have fits (i : I) : ExtensionFits (mark i) base ord (w i) c := by
    refine ⟨hw i,?_,comm i⟩
    intro j k
    have h := (Subgroup.mem_center_iff.mp (central i (show (mark i).incl (base k)∈(mark i).incl.range from ⟨_,rfl⟩))) ((mark i).x j)
    change ⁅_,_⁆=(mark i).incl 1
    rw [map_one,commutatorElement_eq_one_iff_mul_comm]
    exact h
  have h := restricted_extension_count E mark base hbase ord ho (MonoidHom.id W) c w (fun _=>c)
    (fun _ _=>rfl) fits size sep
  simpa using h
end Erdos1160.Sims
end
section
namespace OrbitUp.MinSpan
open BoundedMatrices
variable {d b : ℕ}
abbrev AForm (d : ℕ) := V d→ₗ[K] Module.Dual K (V d)
abbrev Edge (d : ℕ) := (i : Fin d) × Fin i.val
private noncomputable def coord (d : ℕ) := (Pi.basisFun K (Fin d)).dualBasis.equivFun
noncomputable def scalarMatrix (A : AForm d) : Matrix (Fin d) (Fin d) K :=
  LinearMap.toMatrix' ((coord d).toLinearMap.comp A)
theorem scalarMatrix_rank (A : AForm d) : (scalarMatrix A).rank=Module.finrank K A.range := by
  have e : (scalarMatrix A).mulVecLin=(coord d).toLinearMap.comp A := by
    apply LinearMap.ext;intro x;exact LinearMap.toMatrix'_mulVec ((coord d).toLinearMap.comp A) x
  rw [Matrix.rank,e,LinearMap.range_comp]
  exact ((coord d).submoduleMap A.range).finrank_eq.symm
theorem scalarMatrix_inj : Function.Injective (@scalarMatrix d) := by
  intro x y e
  have eq := LinearMap.toMatrix'.injective e
  exact LinearMap.ext (fun i=>(coord d).injective (DFunLike.congr_fun eq i))
def edge (A : AForm d) (i : Edge d) := A (basis i.1) (basis ⟨i.2.val,lt_trans i.2.isLt i.1.isLt⟩)
private theorem alt_sym (A : AForm d) (alt : ∀x,A x x=0) (u v : V d) : A u v=A v u := by
  have e := alt (u+v)
  simp only [map_add,LinearMap.add_apply,alt,zero_add,add_zero] at e
  exact (show ∀x y:K,x+y=0→y=x by decide) _ _ e
theorem edge_sep (A B : AForm d) (ha : ∀x,A x x=0) (hb : ∀x,B x x=0) (eq : edge A=edge B) : A=B := by
  apply (Pi.basisFun K (Fin d)).ext;intro i;rw [Pi.basisFun_apply]
  apply (Pi.basisFun K (Fin d)).ext;intro j;rw [Pi.basisFun_apply]
  change A (basis i) (basis j)=B (basis i) (basis j)
  rcases lt_trichotomy j i with h|rfl|h
  · exact congrFun eq ⟨i,⟨j.val,h⟩⟩
  · rw [ha,hb]
  · rw [alt_sym A ha,alt_sym B hb];exact congrFun eq ⟨j,⟨i.val,h⟩⟩
structure SplitDual (b p : ℕ) where
  low : Fin p→Module.Dual K (V b)
  high : Fin (b-p)→Module.Dual K (V b)
  sep : ∀x y:V b,(∀i,low i x=low i y)→(∀i,high i x=high i y)→x=y
theorem split_under {p : ℕ} (T : Submodule K (Module.Dual K (V b))) (hp : p ≤ Module.finrank K T) :
    ∃a : SplitDual b p,∀i,a.low i∈T := by
  classical
  obtain ⟨i,hi⟩ := finrank_le_iff_exists_linearMap.mp (show Module.finrank K (V p) ≤ Module.finrank K T from (Module.finrank_fin_fun _).le.trans hp)
  let f := T.subtype.comp i
  have hfi : Function.Injective f := T.subtype_injective.comp hi
  let L := f.range
  have rank : Module.finrank K L=p := (LinearMap.finrank_range_of_inj hfi).trans (Module.finrank_fin_fun K)
  obtain ⟨H,hH⟩ := Submodule.exists_isCompl L
  have dims := Submodule.finrank_add_eq_of_isCompl hH
  rw [Subspace.dual_finrank_eq,Module.finrank_fin_fun,rank] at dims
  let A := (Module.finBasis K L).reindex (finCongr rank)
  let B := (Module.finBasis K H).reindex (finCongr (show Module.finrank K H=b-p by omega))
  refine ⟨⟨fun j=>(A j).val,fun j=>(B j).val,?_⟩,fun j=>?_⟩
  · intro x y lo hi
    let g := Module.Dual.eval K (V b) x - Module.Dual.eval K (V b) y
    have van {U : Submodule K (Module.Dual K (V b))} {ι : Type} (C : Module.Basis ι K U)
        (hz : ∀j,(C j).val x=(C j).val y) : U ≤ g.ker := by
      have zg : g.comp U.subtype=0 := C.ext (fun j=>sub_eq_zero.mpr (hz j))
      intro jj h
      exact (show g jj=0 from DFunLike.congr_fun zg (⟨jj,h⟩ : U))
    have all : L⊔H ≤ g.ker := sup_le (van A lo) (van B hi)
    rw [hH.sup_eq_top] at all
    funext j
    exact sub_eq_zero.mp (all (x:=LinearMap.proj j) Submodule.mem_top)
  · obtain ⟨x,h⟩ := (A j).property
    change (A j).val∈T
    rw [←h]
    exact (i x).property
end OrbitUp.MinSpan
end
section
namespace OrbitUp.MinSpan
open BoundedMatrices
theorem minspan_packing {d b σ k : ℕ} (budget : b+1 < 2*k*k) :
    let p := σ-1-4*k
    Nat.card (minimalAlternating d b σ) ≤
      2^(b*b + 8*k*d*p + (b-p)*d.choose 2) := by
  classical
  let p := σ-1-4*k
  let X := minimalAlternating d b σ
  let L := {M : Matrix (Fin d) (Fin d) K // M.rank ≤ 4*k}
  let D := Module.Dual K (V b)
  letI : Finite D := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  by_cases existsX : Nonempty X
  swap
  · haveI : IsEmpty X := not_nonempty_iff.mp existsX
    change Nat.card X ≤ _
    simp
  have frames (x:X) : ∃ a : SplitDual b p,
      ∀j,(scalarMatrix (push (a.low j) x.val)).rank ≤ 4*k := by
    obtain ⟨T,hσ,low⟩ := many_low_rank_components x budget
    obtain ⟨a,good⟩ := split_under T (show p ≤ Module.finrank K T by dsimp [p];omega)
    exact ⟨a,fun j=>by rw [scalarMatrix_rank];exact (low _ (good j)).le⟩
  choose a hlow using frames
  let C := (Fin p→D) × (Fin (b-p)→D) × (Fin p→L) × (Fin (b-p)→Edge d→K)
  let code (x:X) : C :=
    ((a x).low,(a x).high,fun j=>⟨scalarMatrix (push ((a x).low j) x.val),hlow x j⟩,
      fun j=>edge (push ((a x).high j) x.val))
  have inject : Function.Injective code := by
    intro x y h
    have l := congrArg (fun c:C=>c.1) h
    have h' := congrArg (fun c:C=>c.2.1) h
    have ml := congrArg (fun c:C=>c.2.2.1) h
    have mh := congrArg (fun c:C=>c.2.2.2) h
    change (a x).low=(a y).low at l
    change (a x).high=(a y).high at h'
    apply Subtype.ext
    apply LinearMap.ext; intro u
    apply LinearMap.ext; intro v
    apply (a x).sep
    · intro j
      have E := congrArg Subtype.val (congrFun ml j)
      change scalarMatrix (push ((a x).low j) x.val)=scalarMatrix (push ((a y).low j) y.val) at E
      rw [←l] at E
      exact DFunLike.congr_fun (DFunLike.congr_fun (scalarMatrix_inj E) u) v
    · intro j
      have E := congrFun mh j
      change edge (push ((a x).high j) x.val)=edge (push ((a y).high j) y.val) at E
      rw [←h'] at E
      have alt (z:X) (w:V d) : push ((a x).high j) z.val w w=0 := by
        change (a x).high j (z.val w w)=0
        rw [z.property.1 w,map_zero]
      exact DFunLike.congr_fun (DFunLike.congr_fun (edge_sep _ _ (alt x) (alt y) E) u) v
  have hcard := Nat.card_le_card_of_injective code inject
  have Dcard : Nat.card D=2^b := by
    rw [Module.natCard_eq_pow_finrank (K:=K),Subspace.dual_finrank_eq,Module.finrank_fin_fun,Nat.card_zmod]
  have Ecard : Nat.card (Edge d)=d.choose 2 := by
    rw [Nat.choose_two_right];exact Erdos1160Growth.SharpFamily.triangular_card d
  have cardL : Nat.card L ≤ 2^(8*k*d) := by
    convert count_small_rank_matrices d d (4*k) using 2 <;> ring
  have pb : p ≤ b := by
    obtain ⟨x⟩ := existsX
    obtain ⟨T,h,_⟩ := many_low_rank_components x budget
    have hb := Submodule.finrank_le T
    rw [Subspace.dual_finrank_eq,Module.finrank_fin_fun] at hb
    dsimp [p];omega
  change Nat.card X ≤ _
  refine hcard.trans ?_
  change Nat.card ((Fin p→D) × (Fin (b-p)→D) × (Fin p→L) × (Fin (b-p)→Edge d→K))≤_
  simp only [Nat.card_prod,Nat.card_fun,Nat.card_fin,Dcard,Ecard,Nat.card_zmod]
  refine (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left cardL p)))).trans ?_
  simp only [←pow_mul,←pow_add]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have ep : b*p + b*(b-p)=b*b := by rw [←Nat.mul_add,Nat.add_sub_of_le pb]
  nlinarith only [ep]
end OrbitUp.MinSpan
end
section
namespace OrbitUp.MinSpan
theorem minspan_entropy {d b σ m : ℕ} (hd : d ≤ m) (hb : b ≤ m) :
    Nat.card (minimalAlternating d b σ) ≤
      2^((b-(σ-1))*d.choose 2 + 13*(m.sqrt+1)*m^2) := by
  classical
  by_cases hx : Nonempty (minimalAlternating d b σ)
  swap
  · haveI : IsEmpty (minimalAlternating d b σ) := not_nonempty_iff.mp hx
    simp
  let k := m.sqrt+1
  let p := σ-1-4*k
  have hk : 1 ≤ k := by dsimp [k];omega
  have budget : b+1 < 2*k*k := by
    have H : m < k*k := Nat.lt_succ_sqrt m
    have h : 0 < k*k := Nat.mul_pos hk hk
    nlinarith
  have pb : p ≤ b := by
    obtain ⟨β⟩ := hx
    obtain ⟨T,h,_⟩ := many_low_rank_components β budget
    have hh := Submodule.finrank_le T
    rw [Subspace.dual_finrank_eq,Module.finrank_fin_fun] at hh
    dsimp [p];omega
  have base := minspan_packing (d:=d) (σ:=σ) budget
  change Nat.card _ ≤ 2^(b*b+8*k*d*p+(b-p)*d.choose 2) at base
  refine base.trans (Nat.pow_le_pow_right (by decide) ?_)
  have D : d.choose 2 ≤ m*m := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self ..).trans (Nat.mul_le_mul hd ((Nat.sub_le ..).trans hd))
  have sub : b-p≤(b-(σ-1))+4*k := by dsimp [p];omega
  have charge := (Nat.mul_le_mul_right (d.choose 2) sub).trans_eq (Nat.add_mul ..)
  have B : b*b ≤ k*(m*m) := (Nat.mul_le_mul hb hb).trans (Nat.le_mul_of_pos_left _ hk)
  have mid : 8*k*d*p ≤ 8*k*(m*m) := by
    rw [Nat.mul_assoc];exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hd (pb.trans hb))
  have last := Nat.mul_le_mul_left (4*k) D
  change b*b+8*k*d*p+(b-p)*d.choose 2 ≤ (b-(σ-1))*d.choose 2+13*k*m^2
  nlinarith only [B,mid,last,charge]
end OrbitUp.MinSpan
end
section
namespace CentralKernelCount
open CategoryTheory Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
noncomputable def standardWord {t : ℕ} (v : BitGroup t) : List (Fin t) :=
  (bits_word t v).choose
theorem standardWord_correct {t : ℕ} (v : BitGroup t) : word bit (standardWord v)=v :=
  (bits_word t v).choose_spec
end CentralKernelCount
end
section
namespace OrbitUp
abbrev Face (J : Type) (p : ℕ) := {s : Finset J // s.card=p}
def exteriorStep {J : Type} [DecidableEq J] (i : J) : (Face J 2→K) →ₗ[K] (Face J 3→K) where
  toFun v s := if hi:i∈s.val then v ⟨s.val.erase i,by rw [Finset.card_erase_of_mem hi,s.property]⟩ else 0
  map_add' x y := by funext s;by_cases h : i∈s.val <;> simp [h]
  map_smul' c x := by funext s;by_cases h : i∈s.val <;> simp [h]
theorem exteriorStep_out {J : Type} [DecidableEq J] (i : J) (w : Face J 2→K) (s : Face J 3) (h : i∉s.val) :
    exteriorStep i w s=0 := by simp [exteriorStep,h]
theorem exteriorStep_insert {J : Type} [DecidableEq J] (i : J) (w : Face J 2→K) (s : Face J 2) (h : i∉s.val) :
    exteriorStep i w ⟨insert i s.val,by rw [Finset.card_insert_of_notMem h,s.property]⟩=w s := by
  simp [exteriorStep,h]
end OrbitUp
end
section
namespace OrbitUp.Shadow
universe u
variable {J : Type u} [Fintype J] [LinearOrder J]
def Leads (w : J→K) (i : J) : Prop := w i≠0 ∧ ∀j,i < j→w j=0
noncomputable def sites (F : Submodule K (J→K)) : Finset J := by
  classical exact Finset.univ.filter (fun i=>∃w:F,Leads w.val i)
theorem mem_sites (F : Submodule K (J→K)) (i : J) : i∈sites F ↔ ∃w:F,Leads w.val i := by
  classical simp [sites]
theorem count_sites (F : Submodule K (J→K)) : (sites F).card=Module.finrank K F := by
  classical
  let L := ↥(sites F)
  have witness (i : L) : ∃v:F,Leads v.val i.val := (mem_sites F i.val).mp i.property
  choose w hw using witness
  have ind : LinearIndependent K w := by
    rw [linearIndependent_iff']
    intro s c zero i hi
    by_contra hn
    let p := s.filter (fun j=>c j≠0)
    have non : p.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨hi,hn⟩⟩
    let k := p.max' non
    have hk := Finset.mem_filter.mp (show k∈p from p.max'_mem non)
    have z : (∑j∈s,c j*(w j).val k.val)=0 := by
      have h := congrArg (fun v:F=>v.val k.val) zero
      simpa only [Submodule.coe_sum,SetLike.val_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,ZeroMemClass.coe_zero,Pi.zero_apply] using h
    rw [Finset.sum_eq_single k] at z
    · exact (mul_ne_zero hk.2 (hw k).1) z
    · intro j hj ne
      by_cases cj : c j=0
      · simp [cj]
      have lt : j < k := lt_of_le_of_ne (p.le_max' j (Finset.mem_filter.mpr ⟨hj,cj⟩)) ne
      rw [(hw j).2 k.val lt,mul_zero]
    · exact fun h=>False.elim (h hk.1)
  have le := ind.fintype_card_le_finrank
  have ge : Module.finrank K F ≤ Fintype.card L := by
    let projection : F→ₗ[K] (L→K) := {toFun := fun w i=>w.val i.val,map_add' _ _ := rfl,map_smul' _ _ := rfl}
    have inj : Function.Injective projection := by
      apply LinearMap.ker_eq_bot.mp
      apply le_bot_iff.mp
      intro w hz
      change w=0
      by_contra nz
      have n : ∃i,w.val i≠0 := by
        by_contra! h
        exact nz (Subtype.ext (funext h))
      let support := Finset.univ.filter (fun i=>w.val i≠0)
      have hn : support.Nonempty := n.imp (fun i hi=>Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩)
      let i := support.max' hn
      have hi := (Finset.mem_filter.mp (show i∈support from support.max'_mem hn)).2
      have im : i∈sites F := (mem_sites F i).mpr ⟨w,hi,fun j hj=>by
        by_contra hyp
        exact hj.not_ge (support.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hyp⟩))⟩
      exact hi (congrFun (show projection w=0 from hz) ⟨i,im⟩)
    exact (LinearMap.finrank_le_finrank_of_injective inj).trans_eq (Module.finrank_fintype_fun_eq_card K)
  simpa only [L,Fintype.card_coe] using le_antisymm le ge
theorem union_defect {P Q : Type*} [DecidableEq Q] (f : P→Finset Q)
    (overlap : ∀i j,i≠j→((f i)∩(f j)).card ≤ 1) (s : Finset P) :
    (∑i∈s,(f i).card)≤(s.biUnion f).card+s.card.choose 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    have e := Finset.card_union_add_card_inter (f i) (s.biUnion f)
    have inter : ((f i)∩s.biUnion f).card ≤ s.card := by
      rw [Finset.inter_biUnion]
      exact (Finset.card_biUnion_le_card_mul _ _ 1 (fun j hj=>overlap i j (fun h=>hi (h ▸ hj)))).trans_eq (Nat.mul_one _)
    simp only [Finset.sum_insert hi,Finset.biUnion_insert,Finset.card_insert_of_notMem hi,Nat.choose_succ_succ,Nat.choose_one_right]
    change (f i).card+(∑j∈s,(f j).card)≤(f i∪s.biUnion f).card+(s.card+s.card.choose 2)
    omega
end OrbitUp.Shadow
end
section
namespace OrbitUp.Shadow
noncomputable section
variable {d n : ℕ}
noncomputable def monoWeight (s : Multiset (Fin d)) :=
  (MonomialOrder.lex (σ:=Fin d)).toSyn (Multiset.toFinsupp s)
noncomputable def symOrder (n : ℕ) : LinearOrder (Sym (Fin d) n) :=
  LinearOrder.lift' (fun s=>monoWeight s.val) (fun x y eq=>Subtype.ext (Multiset.toFinsupp.injective ((MonomialOrder.lex (σ:=Fin d)).toSyn.injective eq)))
local instance {n : ℕ} : LinearOrder (Sym (Fin d) n) := symOrder n
theorem mono_cons_lt (i : Fin d) (s t : Sym (Fin d) n) :
    Sym.cons i s < Sym.cons i t ↔ s < t := by
  change monoWeight (i ::ₘ s.val) < monoWeight (i ::ₘ t.val) ↔ monoWeight s.val < monoWeight t.val
  simp only [monoWeight,←Multiset.singleton_add,map_add,add_lt_add_iff_left]
def multiples (s : Sym (Fin d) n) : Finset (Sym (Fin d) (n+1)) :=
  Finset.univ.image (fun i=>Sym.cons i s)
theorem overlap_multiples {s t : Sym (Fin d) n} (h : s≠t) : ((multiples s)∩multiples t).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  obtain ⟨hx₁,hx₂⟩ := Finset.mem_inter.mp hx
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx₁
  obtain ⟨j,_,e⟩ := Finset.mem_image.mp hx₂
  obtain ⟨hy₁,hy₂⟩ := Finset.mem_inter.mp hy
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hy₁
  obtain ⟨v,_,f⟩ := Finset.mem_image.mp hy₂
  have ij : i≠j := fun he=>h ((Sym.cons_inj_right i s t).mp (he ▸ e.symm))
  have eq (p q : Fin d) (e : Sym.cons p s=Sym.cons q t) : ({p} : Multiset (Fin d))+s.val={q}+t.val := by
    rw [Multiset.singleton_add,Multiset.singleton_add];exact congrArg (fun z : Sym (Fin d) (n+1)=>z.val) e
  have h₁ := eq _ _ e.symm
  have h₂ := eq _ _ f.symm
  have mulEq : ({i}:Multiset (Fin d))+{v}={j}+{u} := by
    apply add_right_cancel (b:=s.val)
    calc ({i}+{v})+s.val = {v}+({i}+s.val) := by ac_rfl
         _ = {v}+({j}+t.val) := by rw [h₁]
         _ = {j}+({v}+t.val) := by ac_rfl
         _ = {j}+({u}+s.val) := by rw [←h₂]
         _ = ({j}+{u})+s.val := by ac_rfl
  have hi : i∈({j}+{u}:Multiset (Fin d)) := mulEq ▸ (show i∈({i}+{v}:Multiset (Fin d)) by simp)
  have iu : i=u := by simpa [ij] using hi
  rw [iu]
end
end OrbitUp.Shadow
end
section
namespace OrbitUp.Shadow
noncomputable section
variable {d n : ℕ}
def forgetFace (s : Face (Fin d) n) : Sym (Fin d) n := ⟨s.val.val,s.property⟩
theorem forgetFace_inj : Function.Injective (@forgetFace d n) := fun x y eq=>Subtype.ext (Finset.val_inj.mp (congrArg Subtype.val eq))
local instance {n : ℕ} : LinearOrder (Sym (Fin d) n) := symOrder n
local instance {n : ℕ} : LinearOrder (Face (Fin d) n) := LinearOrder.lift' forgetFace forgetFace_inj
def extendFace (s : Face (Fin d) 2) (i : Fin d) (hi : i∉s.val) : Face (Fin d) 3 :=
  ⟨insert i s.val,by rw [Finset.card_insert_of_notMem hi,s.property]⟩
theorem forget_extend (s : Face (Fin d) 2) (i : Fin d) (hi : i∉s.val) :
    forgetFace (extendFace s i hi)=Sym.cons i (forgetFace s) := Subtype.ext (Finset.insert_val_of_notMem hi)
theorem exterior_leads {w : Face (Fin d) 2→K} {s : Face (Fin d) 2} (hs : Leads w s) (i : Fin d) (hi : i∉s.val) :
    Leads (exteriorStep i w) (extendFace s i hi) := by
  refine ⟨fun eq=>hs.1 ((exteriorStep_insert i w s hi).symm.trans eq),?_⟩
  intro t ht
  by_cases h : i∈t.val
  · let u : Face (Fin d) 2 := ⟨t.val.erase i,by rw [Finset.card_erase_of_mem h,t.property]⟩
    have miss : i∉u.val := by simp [u]
    have eq : extendFace u i miss=t := Subtype.ext (Finset.insert_erase h)
    change forgetFace (extendFace s i hi) < forgetFace t at ht
    rw [←eq,forget_extend,forget_extend] at ht
    have hu : forgetFace s < forgetFace u := (mono_cons_lt i _ _).mp ht
    exact ((congrArg ((exteriorStep i) w) eq.symm).trans (exteriorStep_insert _ _ _ miss)).trans (hs.2 _ hu)
  · exact exteriorStep_out i w t h
def extensions (s : Face (Fin d) 2) : Finset (Face (Fin d) 3) :=
  Finset.univ.image (fun i : {i // i∉s.val}=>extendFace s i.val i.property)
theorem card_extensions (s : Face (Fin d) 2) : (extensions s).card=d-2 := by
  have inj : Function.Injective (fun i : {i // i∉s.val} =>extendFace s i.val i.property) := by
    intro i j eq
    have im := congrArg forgetFace eq
    rw [forget_extend,forget_extend] at im
    exact Subtype.ext ((Sym.cons_inj_left ..).mp im)
  rw [extensions,Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,s.property]
theorem extension_overlap {s t : Face (Fin d) 2} (hne : s≠t) :
    ((extensions s)∩extensions t).card ≤ 1 := by
  have inc (s : Face (Fin d) 2) (x : Face (Fin d) 3) (h : x∈extensions s) : forgetFace x∈multiples (forgetFace s) := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨i.val,Finset.mem_univ _,(forget_extend ..).symm⟩
  apply Finset.card_le_one.mpr
  intro x hx y hy
  apply forgetFace_inj
  have h := Finset.card_le_one.mp (overlap_multiples (fun eq=>hne (forgetFace_inj eq)))
  exact h _ (Finset.mem_inter.mpr ⟨inc _ _ (Finset.mem_inter.mp hx).1,inc _ _ (Finset.mem_inter.mp hx).2⟩)
    _ (Finset.mem_inter.mpr ⟨inc _ _ (Finset.mem_inter.mp hy).1,inc _ _ (Finset.mem_inter.mp hy).2⟩)
theorem sharp_exterior_shadow (d : ℕ) (F : Submodule K (Face (Fin d) 2 → K)) (W : Submodule K (Face (Fin d) 3 → K))
    (hs : ∀i,F.map (exteriorStep i) ≤ W) :
    (d-2)*Module.finrank K F ≤ Module.finrank K W+(Module.finrank K F).choose 2 := by
  classical
  have cov : (sites F).biUnion extensions⊆sites W := by
    intro x hx
    obtain ⟨s,h,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw⟩ := (mem_sites F s).mp h
    exact (mem_sites W _).mpr ⟨⟨_,hs i.val ⟨w.val,w.property,rfl⟩⟩,exterior_leads hw i.val i.property⟩
  have h := union_defect extensions (fun _ _ n=>extension_overlap n) (sites F)
  simp only [card_extensions,Finset.sum_const,smul_eq_mul,count_sites] at h
  rw [Nat.mul_comm]
  exact h.trans (Nat.add_le_add_right ((Finset.card_le_card cov).trans_eq (count_sites W)) _)
end
end OrbitUp.Shadow
end
section
namespace OrbitUp.Shadow
noncomputable def wedgeSum {d : ℕ} (F : Submodule K (Face (Fin d) 2→K)) :
    (Fin d→F)→ₗ[K] (Face (Fin d) 3→K) :=
  ∑i : Fin d,((exteriorStep i).comp F.subtype).comp (LinearMap.proj i)
theorem wedgeSum_apply {d : ℕ} (F : Submodule K (Face (Fin d) 2→K)) (c : Fin d→F) (s : Face (Fin d) 3) :
    wedgeSum F c s=∑i : Fin d,exteriorStep i (c i).val s := by
  simp only [wedgeSum,LinearMap.sum_apply,LinearMap.comp_apply,Submodule.subtype_apply,LinearMap.proj_apply,Finset.sum_apply]
end OrbitUp.Shadow
end
section
namespace BinaryFactor
variable {G : Type*} [Group G]
namespace Cocycle
end Cocycle
end BinaryFactor
end
section
namespace BinaryFactor.Cocycle
open BinaryFactor
variable {G : Type*} [Group G]
end BinaryFactor.Cocycle
end
section
namespace BinaryFactor
open Cocycle
variable (G : Type*) [Group G]
variable {G}
end BinaryFactor
end
section
namespace BinaryFactor
open Cocycle
variable (G : Type*) [Group G]
variable {G}
end BinaryFactor
end
section
namespace BinaryFactor
open Cocycle
variable {E G H : Type*} [Group E] [Group G] [Group H]
end BinaryFactor
end
section
namespace BinaryFactor.Elementary
open Erdos1160Growth.LowerTriangularUpper
open BinaryFactor
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open OrbitUp Cocycle Erdos1160Growth.LowerTriangularUpper
abbrev Pairs (d : ℕ) := Face (Fin d) 2 → Bit
def pair {d : ℕ} (i j : Fin d) (h : i ≠ j) : Face (Fin d) 2 := ⟨{i,j},Finset.card_pair h⟩
structure TripleRep {d : ℕ} (s : Face (Fin d) 3) where
  i : Fin d
  j : Fin d
  k : Fin d
  hij : i≠j
  hik : i≠k
  hjk : j≠k
  support : s.val={i,j,k}
noncomputable def tripleRep {d : ℕ} (s : Face (Fin d) 3) : TripleRep s :=
  Classical.choice (by obtain ⟨i,j,k,h₁,h₂,h₃,h₄⟩ := Finset.card_eq_three.mp s.property
                       exact ⟨⟨i,j,k,h₁,h₂,h₃,h₄⟩⟩)
end BinaryFactor.Elementary
end
section
namespace Erdos1160.Sims
open OrbitUp OrbitUp.Shadow
open BinaryFactor.Elementary (pair TripleRep tripleRep)
variable {d b : ℕ}
theorem partial_exterior_codimension (P : Submodule K (Face (Fin d) 2→K)) {v : ℕ}
    (hv : v ≤ Module.finrank K P) :
    Module.finrank K (LinearMap.ker (wedgeSum P))+(d-2)*v ≤ d*Module.finrank K P+v.choose 2 := by
  classical
  obtain ⟨h,inj⟩ := finrank_le_iff_exists_linearMap.mp
    (show Module.finrank K (V v) ≤ Module.finrank K P from (Module.finrank_fin_fun _).le.trans hv)
  let f := P.subtype.comp h
  have fi : Function.Injective f := P.subtype_injective.comp inj
  let U := f.range
  have rank : Module.finrank K U=v :=
    (LinearMap.finrank_range_of_inj fi).trans (Module.finrank_fin_fun K)
  let W := LinearMap.range (wedgeSum P)
  have inc (i : Fin d) : U.map (exteriorStep i) ≤ W := by
    rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    refine ⟨Pi.single i (h x),?_⟩
    funext z
    rw [wedgeSum_apply,Fintype.sum_eq_single i]
    · simp [f]
    · intro j hj;rw [Pi.single_eq_of_ne hj];simp
  have sh := sharp_exterior_shadow d U W inc
  rw [rank] at sh
  have rn := LinearMap.finrank_range_add_finrank_ker (wedgeSum P)
  rw [Module.finrank_pi_fintype] at rn
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at rn
  change Module.finrank K W+_=d*_ at rn
  omega
theorem eval_wedge_sum (P : Submodule K (Face (Fin d) 2→K)) (c : Fin d→P) (z : Face (Fin d) 3)
    (t : TripleRep z) :
    wedgeSum P c z=(c t.i).val (pair t.j t.k t.hjk)+(c t.j).val (pair t.i t.k t.hik)+(c t.k).val (pair t.i t.j t.hij) := by
  classical
  have entry (i j k : Fin d) (ne : j≠k) (hi : i≠j) (hk : i≠k) (eq : z.val=insert i (pair j k ne).val) :
      exteriorStep i (c i).val z=(c i).val (pair j k ne) := by
    have miss : i∉(pair j k ne).val := by simp [pair,hi,hk]
    exact (congrArg ((exteriorStep i) (c i).val) (show z=⟨insert i (pair j k ne).val,_⟩ from Subtype.ext eq)).trans (exteriorStep_insert _ _ _ miss)
  have hi := entry _ _ _ t.hjk t.hij t.hik t.support
  have hj := entry _ _ _ t.hik t.hij.symm t.hjk (t.support.trans (Finset.insert_comm ..))
  have hk := entry _ _ _ t.hij t.hik.symm t.hjk.symm (by rw [t.support];ext;simp [pair];tauto)
  rw [wedgeSum_apply,←Finset.sum_subset (Finset.subset_univ z.val) (fun i _ h=>exteriorStep_out _ _ _ h)]
  change (∑i∈z.val,exteriorStep i (c i).val z)=_
  conv_lhs => arg 1;rw [t.support]
  simp [hi,hj,hk,t.hij,t.hik,t.hjk,add_assoc]
end Erdos1160.Sims
end
section
namespace BinaryFactor.Elementary
open Erdos1160Growth.LowerTriangularUpper
end BinaryFactor.Elementary
end
section
namespace BinaryFactor.Elementary
open Cocycle
end BinaryFactor.Elementary
end
section
namespace Erdos1160.Sims
open OrbitUp OrbitUp.Shadow BinaryFactor BinaryFactor.Elementary Erdos1160.DeepJacobi
open Erdos1160.CentralLifts.Survival (jacobiRank)
open scoped commutatorElement
variable {Q : Type} [Group Q] [Finite Q] {r : ℕ}
private noncomputable def choosePair (z : Face (Fin r) 2) :
    {v : Fin r × Fin r // v.1≠v.2 ∧ z.val={v.1,v.2}} :=
  Classical.choice (by obtain ⟨i,j,hn,he⟩ := Finset.card_eq_two.mp z.property
                       exact ⟨⟨(i,j),hn,he⟩⟩)
private noncomputable def bracketMark (x : Fin r→Q) (z : Face (Fin r) 2) : Second Q :=
  secondBracket (x (choosePair z).val.1) (x (choosePair z).val.2)
private theorem bracket_pair (x : Fin r→Q) (hb : ∀w:Second Q,w*w=1) (i j : Fin r) (ne : i≠j) :
    bracketMark x (pair i j ne)=secondBracket (x i) (x j) := by
  let z := pair i j ne
  let u := (choosePair z).val.1
  let v := (choosePair z).val.2
  have he : ({i,j}:Finset (Fin r))={u,v} := (choosePair z).property.2
  have hs : ({i,j}:Set (Fin r))={u,v} := by simpa using congrArg (fun s:Finset (Fin r)=>(s:Set (Fin r))) he
  change secondBracket (x u) (x v)=secondBracket (x i) (x j)
  obtain ⟨hu,hv⟩|⟨hu,hv⟩ := Set.pair_eq_pair_iff.mp hs
  · rw [←hu,←hv]
  · rw [←hu,←hv]
    let w := secondBracket (x i) (x j)
    have inv : w⁻¹=w := inv_eq_of_mul_eq_one_left (hb w)
    exact (show secondBracket (x j) (x i)=w⁻¹ from Subtype.ext (commutatorElement_inv ..).symm).trans inv
private theorem bracket_gen (x : Fin r→Q) (hx : Subgroup.closure (Set.range x)=⊤)
    (hc : Second Q ≤ Subgroup.center Q) (hb : ∀w:Second Q,w*w=1) :
    Subgroup.closure (Set.range (bracketMark x))=⊤ := by
  let C := Subgroup.closure (Set.range (fun z=>(bracketMark x z).val))
  have cent : C ≤ Subgroup.center Q := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨z,rfl⟩;exact hc (bracketMark x z).property
  letI : C.Normal := ⟨fun a ha b=>by rw [Subgroup.mem_center_iff.mp (cent ha) b,mul_inv_cancel_right];exact ha⟩
  let f := QuotientGroup.mk' C
  have gen : Subgroup.closure (Set.range (f ∘ x))=⊤ := by
    rw [Set.range_comp,←MonoidHom.map_closure,hx,Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective _)]
  have comm : IsMulCommutative (Subgroup.closure (Set.range (f ∘ x))) := by
    apply Subgroup.isMulCommutative_closure
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    rcases eq_or_ne i j with rfl|hne
    · rfl
    · apply commutatorElement_eq_one_iff_mul_comm.mp
      change ⁅f (x i),f (x j)⁆=1
      rw [←map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.subset_closure ⟨pair i j hne,congrArg Subtype.val (bracket_pair x hb i j hne)⟩)
  rw [gen] at comm
  have derived : Second Q ≤ C := by
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    apply (QuotientGroup.eq_one_iff _).mp
    change f ⁅a,b⁆=1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (comm.is_comm.comm (⟨f a,trivial⟩:(⊤:Subgroup (Q⧸C))) ⟨f b,trivial⟩)
  apply Subgroup.map_injective (Second Q).subtype_injective
  rw [MonoidHom.map_closure,←Set.range_comp,←MonoidHom.range_eq_map,Subgroup.range_subtype]
  exact le_antisymm (by apply (Subgroup.closure_le _).mpr;rintro _ ⟨z,rfl⟩;exact (bracketMark x z).property) derived
private noncomputable def rowMap (x : Fin r→Q) : characters (Second Q)→ₗ[K] Pairs r where
  toFun a z := a.val (bracketMark x z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def toHom {A : Type} [Group A] (a : characters A) : A→*C₂ where
  toFun v := .ofAdd (a.val v)
  map_mul' u v := congrArg Multiplicative.ofAdd (a.property u v)
  map_one' := by change a.val 1=0;simpa using a.property 1 1
private theorem row_inj (x : Fin r→Q) (hx : Subgroup.closure (Set.range x)=⊤)
    (hc : Second Q ≤ Subgroup.center Q) (hb : ∀w:Second Q,w*w=1) :
    Function.Injective (rowMap x) := by
  intro a b he
  have equal : toHom a=toHom b := MonoidHom.eq_of_eqOn_dense (bracket_gen x hx hc hb) (by
    rintro _ ⟨z,rfl⟩;exact congrArg Multiplicative.ofAdd (congrFun he z))
  exact Subtype.ext (funext fun y=>congrArg (fun f : Second Q→*C₂=>(f y).toAdd) equal)
private def scalarRow (a : JacobiDual Q) (v : Q) : characters (Second Q) :=
  ⟨fun w=>(a.val w v).toAdd,fun w u=>congrArg (fun f : Q→*C₂=>(f v).toAdd) (a.val.map_mul w u)⟩
private noncomputable def rows (x : Fin r→Q) (a : JacobiDual Q) : Fin r→(rowMap x).range :=
  fun i=>⟨rowMap x (scalarRow a (x i)),⟨_,rfl⟩⟩
private theorem rows_cancel (x : Fin r→Q) (hb : ∀w:Second Q,w*w=1) (a : JacobiDual Q) :
    rows x a∈(wedgeSum (rowMap x).range).ker := by
  funext z
  let t := tripleRep z
  rw [eval_wedge_sum _ _ _ t]
  change (a.val (bracketMark x _) (x t.i)).toAdd+(a.val (bracketMark x _) (x t.j)).toAdd+
    (a.val (bracketMark x _) (x t.k)).toAdd=0
  rw [bracket_pair x hb,bracket_pair x hb,bracket_pair x hb]
  exact (show ∀u v w : C₂,u=v*w⁻¹→u.toAdd+v.toAdd+w.toAdd=0 by decide) _ _ _ (a.property ..)
private theorem rows_inj (x : Fin r→Q) (hx : Subgroup.closure (Set.range x)=⊤)
    (hc : Second Q ≤ Subgroup.center Q) (hb : ∀w:Second Q,w*w=1) : Function.Injective (rows x) := by
  intro a b he
  apply Subtype.ext
  apply MonoidHom.ext
  intro w
  apply MonoidHom.eq_of_eqOn_dense hx
  rintro _ ⟨i,rfl⟩
  have h := row_inj x hx hc hb (congrArg Subtype.val (congrFun he i))
  exact congrArg (fun f : characters (Second Q)=>Multiplicative.ofAdd (f.val w)) h
theorem marked_jacobi_rank_bound {b : ℕ} (x : Fin r→Q) (hx : Subgroup.closure (Set.range x)=⊤)
    (hc : Second Q ≤ Subgroup.center Q) (hb : ∀w:Second Q,w*w=1)
    (hw : Nat.card (Second Q)=2^b) (hr : r-1 ≤ b) :
    jacobiRank Q+(r-1).choose 2 ≤ r*b := by
  obtain ⟨e⟩ := Erdos1160Growth.LowerTriangularUpper.exist_elementary_coords hb hw
  let P := (rowMap x).range
  have hP : Module.finrank K P=b :=
    (LinearMap.finrank_range_of_inj (row_inj x hx hc hb)).trans
      ((characterCongr e).finrank_eq.symm.trans (vectors_char_rank b))
  let emb (a : JacobiDual Q) : (wedgeSum P).ker := ⟨rows x a,rows_cancel x hb a⟩
  have he : Function.Injective emb := fun a b eq=>rows_inj x hx hc hb (congrArg Subtype.val eq)
  have comp := Nat.card_le_card_of_injective emb he
  change Nat.card (Additive (JacobiDual Q)) ≤ Nat.card (wedgeSum P).ker at comp
  rw [Module.natCard_eq_pow_finrank (K:=K) (V:=Additive (JacobiDual Q)),
    Module.natCard_eq_pow_finrank (K:=K) (V:=(wedgeSum P).ker),Nat.card_zmod] at comp
  have dim : jacobiRank Q ≤ Module.finrank K (wedgeSum P).ker := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp comp
  have sh := partial_exterior_codimension P (v:=r-1) (hP ▸ hr)
  rw [hP] at sh
  have twice : 2*((r-1).choose 2)=(r-2)*(r-1) := by
    rcases r with _|(_|r)
    · decide
    · decide
    · change 2*(r+1).choose 2=r*(r+1)
      simpa only [Nat.choose_one_right,Nat.mul_comm] using (Nat.add_one_mul_choose_eq r 1).symm
  omega
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open CentralKernelCount OrbitUp OrbitUp.MinSpan
open Erdos1160.DeepJacobi (Second)
open Erdos1160.CentralLifts.Survival
open scoped commutatorElement
abbrev W (b : ℕ) := Multiplicative (V b)
structure Shape (m d σ : ℕ) where
  r : ℕ
  n : ℕ
  h : ℕ
  t : ℕ
  r_le : r≤σ
  n_le : n+σ ≤ d
  ht_le : h+t ≤ m
  rootOrder : Fin r→Fin (2^m)
  extOrder : Fin n→Fin (2^m)
  rootVec : Fin r→V d
  baseVec : Fin σ→V d
  extVec : Fin n→V d
def rootPattern {m d b σ} (S : Shape m d σ) (β : Tensor d b) (z : PairSlot S.r) : W b :=
  .ofAdd (β (S.rootVec z.1) (S.rootVec (second z)))
def extraPattern {m d b σ} (S : Shape m d σ) (β : Tensor d b) : ExtraSlot S.n σ→W b :=
  Sum.elim (fun p=>.ofAdd (β (S.extVec p.1) (S.baseVec p.2)))
    (fun z=>.ofAdd (β (S.extVec z.1) (S.extVec (second z))))
structure SimsFrame {m d b σ} (S : Shape m d σ) (β : Tensor d b) (E : FiniteGrp.{0}) where
  Q : FiniteGrp.{0}
  H : FiniteGrp.{0}
  root : ExtensionMark (W b) Q S.r
  central : root.incl.range ≤ Subgroup.center Q
  rootPowers : ∀i,∃v,root.x i^((S.rootOrder i).val+1)=root.incl v
  rootComms : ∀z:PairSlot S.r,⁅root.x z.1,root.x (second z)⁆=root.incl (rootPattern S β z)
  rootSize : (∏i,((S.rootOrder i).val+1))*Nat.card (W b) ≤ Nat.card Q
  qsize : Nat.card Q=2^S.h
  hsize : Nat.card H=2^(S.h+S.t)
  π : H→*Q
  onto : Function.Surjective π
  kerFrattini : π.ker ≤ frattini H
  kerSize : Nat.card π.ker ≤ 2^S.t
  base : Fin σ→H
  gen : Subgroup.closure (Set.range base)=⊤
  classTwo : Second Q ≤ Subgroup.center Q
  elementary : ∀w:Second Q,w*w=1
  dimDerived : Nat.card (Second Q)=2^b
  ext : ExtensionMark H E S.n
  powers : Fin S.n→H
  comms : ExtraSlot S.n σ→H
  patterns : ∀z,π (comms z)=root.incl (extraPattern S β z)
  fits : ExtensionFits ext base (fun i=>(S.extOrder i).val+1) powers comms
  size : (∏i,((S.extOrder i).val+1))*Nat.card H ≤ Nat.card E
  tail : S.t ≤ m-d-b
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open OrbitUp OrbitUp.MinSpan OrbitUp.BoundedMatrices
open Erdos1160.DeepJacobi (Second secondBracket)
open Erdos1160Growth.LowerTriangularUpper (squareCore exist_elementary_coords)
structure Seed (G : Type) [Group G] [Finite G] (d b σ : ℕ) where
  p : G→*W d
  onto : Function.Surjective p
  ker : p.ker=squareCore G
  a : Second (headQuot G)≃*W b
  β : minimalAlternating d b σ
  compatible : ∀x y,β.val (p x).toAdd (p y).toAdd=(a (secondBracket (headMap G x) (headMap G y))).toAdd
  H : Subgroup G
  x : Fin σ→H
  generates : Subgroup.closure (Set.range x)=⊤
  derived : (commutator H).map H.subtype=commutator G
  subrank : Module.finrank K (vectorSub (H.map p))=σ
theorem seed_exists {G : Type} [Group G] [Finite G] {d m : ℕ} (size : Nat.card G=2^m)
    (rank : Nat.card (G⧸squareCore G)=2^d) : ∃ b σ,d+b ≤ m ∧ σ ≤ d ∧ σ-1 ≤ b ∧ Nonempty (Seed G d b σ) := by
  classical
  have pg := IsPGroup.of_card size
  let π := QuotientGroup.mk' (squareCore G)
  have sq (v : G⧸squareCore G) : v*v=1 := by
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (squareCore G) v
    rw [←map_mul];exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨w,rfl⟩)
  obtain ⟨i⟩ := exist_elementary_coords sq rank
  let p := i.toMonoidHom.comp π
  have sp := i.surjective.comp (QuotientGroup.mk'_surjective (squareCore G))
  have kp : p.ker=squareCore G := by
    ext x
    change i (π x)=1 ↔ x∈_
    rw [←i.map_one,i.injective.eq_iff];exact QuotientGroup.eq_one_iff _
  obtain ⟨b,hb⟩ := ((pg.to_quotient (commutatorTail G)).to_subgroup (Second (headQuot G))).exists_card_eq
  obtain ⟨a⟩ := exist_elementary_coords (head_conditions G).2 hb
  obtain ⟨β,alt,full,spec⟩ := exists_head_tensor p sp kp (headMap G) (QuotientGroup.mk'_surjective _)
    (head_conditions G).1 a
  let prop (s : ℕ) := ∃S : Submodule K (V d),valuesOn β S=⊤ ∧Module.finrank K S=s
  have ex : ∃s,prop s := ⟨_,⊤,full,rfl⟩
  let σ := Nat.find ex
  obtain ⟨S,hS,hσ⟩ := Nat.find_spec ex
  have minimal (T : Submodule K (V d)) (hT : valuesOn β T=⊤) : σ ≤ Module.finrank K T :=
    Nat.find_min' ex ⟨T,hT,rfl⟩
  obtain ⟨H,x,hx,hs⟩ := lift_subspace p sp S
  have cov (u : S) : ∃x:H,(p x.val).toAdd=u.val := by
    obtain ⟨w,hw,eq⟩ := (show u.val∈vectorSub (H.map p) from hs ▸ u.property)
    exact ⟨⟨w,hw⟩,congrArg Multiplicative.toAdd eq⟩
  have hh := subgroup_of_spanning pg p a β spec H S hS cov
  have sd := minimal ⊤ full
  rw [finrank_top,Module.finrank_fin_fun] at sd
  obtain ⟨T,hT,small⟩ := minimal_commutator_span β alt full
  have ss := (minimal T hT).trans small
  rw [Module.finrank_fin_fun] at ss
  obtain ⟨t,ht⟩ := (pg.to_subgroup (commutatorTail G)).exists_card_eq
  have bound := head_size_budget size p sp kp hb ht
  refine ⟨b,σ,by omega,sd,by omega,⟨?_,?_,?_,?_,?_,?_,H,?_,?_,hh,?_⟩⟩
  · exact p
  · exact sp
  · exact kp
  · exact a
  · exact ⟨β,alt,full,⟨S,hS,hσ⟩,minimal⟩
  · exact spec
  · exact x ∘ (finCongr hσ).symm
  · rw [Set.range_comp,(finCongr hσ).symm.surjective.range_eq,Set.image_univ];exact hx
  · rw [hs];exact hσ
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open CentralKernelCount OrbitUp OrbitUp.MinSpan
open Erdos1160.DeepJacobi (Second secondBracket)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {d b σ : ℕ} (C : Seed G d b σ)
noncomputable def Seed.headEquiv : Second (headSub C.H)≃*W b :=
  (derivedHeadEquiv C.H C.derived).trans C.a
noncomputable def Seed.headIncl : W b→*headSub C.H :=
  (Second (headSub C.H)).subtype.comp C.headEquiv.symm.toMonoidHom
theorem Seed.headIncl_range : C.headIncl.range=Second (headSub C.H) := by
  rw [Seed.headIncl,MonoidHom.range_comp,MonoidHom.range_eq_top_of_surjective _ C.headEquiv.symm.surjective,
    ←MonoidHom.range_eq_map,Subgroup.range_subtype]
theorem Seed.headIncl_value (v : W b) : (C.headIncl v).val=(C.a.symm v).val := by
  have e := C.headEquiv.apply_symm_apply v
  change C.a (derivedHeadEquiv C.H C.derived (C.headEquiv.symm v))=v at e
  exact congrArg (fun z:Second (headQuot G)=>z.val) (C.a.injective (e.trans (C.a.apply_symm_apply v).symm))
theorem Seed.compatible_of_lift (x y : G) (u : C.H) (e : u.val=⁅x,y⁆) :
    toHeadSub C.H u=C.headIncl (.ofAdd (C.β.val (C.p x).toAdd (C.p y).toAdd)) := by
  apply Subtype.ext
  rw [C.headIncl_value,C.compatible]
  change _ = (C.a.symm (C.a (secondBracket _ _))).val
  rw [C.a.symm_apply_apply]
  change headMap G u.val=⁅headMap G x,headMap G y⁆
  rw [e,map_commutatorElement]
theorem Seed.commutator_le : commutator G ≤ C.H :=
  C.derived ▸ Subgroup.map_subtype_le _
theorem Seed.head_order : Nat.card (Second (headSub C.H))=2^b := by
  rw [Nat.card_congr C.headEquiv.toEquiv]
  change Nat.card (Fin b→ZMod 2)=_
  rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
end Erdos1160.Sims
end
section
namespace ClassTwoProfile
open scoped commutatorElement
abbrev Cyc (n : ℕ) := Multiplicative (ZMod (2^n))
abbrev Factors {r : ℕ} (e : Fin r → ℕ) := (i : Fin r) → Cyc (e i)
def gen {r : ℕ} (e : Fin r → ℕ) (i : Fin r) : Factors e :=
  Pi.mulSingle i (Multiplicative.ofAdd 1)
theorem gen_pow {r : ℕ} (e : Fin r → ℕ) (i : Fin r) : gen e i ^ (2^(e i)) = 1 := by
  rw [gen,← Pi.mulSingle_pow]
  have h : (Multiplicative.ofAdd (1 : ZMod (2^(e i)))) ^ (2^(e i)) = 1 := by
    change (2^(e i)) • (1 : ZMod (2^(e i))) = 0
    simp [nsmul_eq_mul]
  rw [h,Pi.mulSingle_one]
theorem gen_closure {r : ℕ} (e : Fin r → ℕ) : Subgroup.closure (Set.range (gen e)) = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  induction v using Pi.mulSingle_induction with
  | one => exact Subgroup.one_mem _
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy
  | mulSingle i x =>
    let j := x.toAdd.val
    have hx : x = (Multiplicative.ofAdd (1 : ZMod (2^(e i)))) ^ j := by
      change x.toAdd = j • (1 : ZMod (2^(e i)))
      simp [j,nsmul_eq_mul]
    rw [hx,Pi.mulSingle_pow]
    exact Subgroup.pow_mem _ (show gen e i ∈ Subgroup.closure (Set.range (gen e)) from Subgroup.subset_closure ⟨i,rfl⟩) _
theorem card_factors {r : ℕ} (e : Fin r → ℕ) : Nat.card (Factors e) = 2^(∑ i, e i) := by
  rw [Nat.card_pi,←Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => Nat.card_zmod _
namespace Data
abbrev Tor (k : ℕ) (b : Fin s→ℕ) := {w : Factors b // w^(2^k) = 1}
end Data
end ClassTwoProfile
end
section
namespace ClassTwoProfile
variable {d s : ℕ} (e : Fin d→ℕ) (b : Fin s→ℕ)
lemma card_tor (k : ℕ) :
    Nat.card (Data.Tor k b) = 2^(∑ i, min k (b i)) := by
  let f : Data.Tor k b ≃ ∀ i, (powMonoidHom (2^k) : Cyc (b i) →* Cyc (b i)).ker :=
    { toFun := fun w i => ⟨w.1 i,congrFun w.2 i⟩
      invFun := fun w => ⟨fun i => w i, funext (fun i => (w i).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr f,Nat.card_pi,←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [IsCyclic.card_powMonoidHom_ker]
  change (Nat.card (ZMod (2^(b i)))).gcd (2^k) = _
  rw [Nat.card_zmod]
  rcases le_total k (b i) with h|h
  · rw [min_eq_left h, Nat.gcd_eq_right (pow_dvd_pow 2 h)]
  · rw [min_eq_right h, Nat.gcd_eq_left (pow_dvd_pow 2 h)]
end ClassTwoProfile
end
section
namespace ClassTwoProfile
open Erdos1160Growth.LowerTriangularUpper
lemma squareCore_eq_range (A : Type*) [CommGroup A] : squareCore A = (powMonoidHom 2 : A→*A).range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a,rfl⟩
    exact ⟨a,sq a⟩
  · rintro _ ⟨u,rfl⟩
    exact Subgroup.subset_closure ⟨u,(sq u).symm⟩
lemma squareCore_size {A : Type} [CommGroup A] {s : ℕ} {b : Fin s→ℕ}
    (f : A ≃* Factors b) (hb : ∀ i,0 < b i) :
    Nat.card (squareCore A)*2^s = 2^(∑ i,b i) := by
  let g := (powMonoidHom 2 : A→*A)
  let kerE : g.ker ≃ Data.Tor 1 b :=
    { toFun := fun w => ⟨f w.val,by change (f w.val)^2=1; rw [←map_pow,show w.val^2=1 from w.2,map_one]⟩
      invFun := fun w => ⟨f.symm w.val,by change (f.symm w.val)^2=1; rw [←map_pow,show w.val^2=1 from w.2,map_one]⟩
      left_inv := by intro w; exact Subtype.ext (f.symm_apply_apply _)
      right_inv := by intro w; exact Subtype.ext (f.apply_symm_apply _) }
  have hk : Nat.card g.ker = 2^s := by
    rw [Nat.card_congr kerE,card_tor]
    have he (i : Fin s) : min 1 (b i)=1 := min_eq_left (show 1 ≤ b i from hb i)
    simp [he]
  have h := g.ker.index_mul_card
  rw [Subgroup.index_ker,hk, Nat.card_congr f.toEquiv, card_factors] at h
  rw [squareCore_eq_range]
  exact h
end ClassTwoProfile
end
section
namespace ClassTwoProfile
lemma exists_cyclic_coords (A : Type) [CommGroup A] [Finite A] {m : ℕ}
    (hc : Nat.card A = 2^m) :
    ∃ (d : ℕ) (e : Fin d → ℕ), (∀ i, 0 < e i) ∧ (∑ i, e i)=m ∧ Nonempty (A ≃* Factors e) := by
  classical
  obtain ⟨ι,_,n,hn,⟨f⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  have hor : ∏ i, n i = 2^m := by
    rw [←hc, Nat.card_congr f.toEquiv,Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => (Nat.card_zmod _).symm
  have pow (i : ι) : ∃ a ≤ m, n i = 2^a := by
    apply (Nat.dvd_prime_pow Nat.prime_two).mp
    rw [←hor]
    exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  let e' (i : ι) := (pow i).choose
  have hn' (i : ι) : n i = 2^(e' i) := (pow i).choose_spec.2
  let t := Fintype.equivFin ι
  let e := e' ∘ t.symm
  let reindex : ((i : ι) → Multiplicative (ZMod (n i))) ≃*
      ((j : Fin (Fintype.card ι)) → Multiplicative (ZMod (n (t.symm j)))) :=
    { Equiv.piCongrLeft' _ t with map_mul' := by intros; rfl }
  let factorIso : ((j : Fin (Fintype.card ι)) → Multiplicative (ZMod (n (t.symm j)))) ≃* Factors e :=
    MulEquiv.piCongrRight fun j => by change Multiplicative (ZMod (n (t.symm j))) ≃* Multiplicative (ZMod (2^(e' (t.symm j)))); rw [hn']
  let h := (f.trans reindex).trans factorIso
  refine ⟨_,e,?_,?_,⟨h⟩⟩
  · intro i
    have hni := hn (t.symm i)
    rw [hn'] at hni
    change 0 < e' _
    by_contra! he
    simp [Nat.eq_zero_of_le_zero he] at hni
  · apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2^(∑ i,e i) = 2^m
    rw [←hc, Nat.card_congr h.toEquiv,card_factors]
end ClassTwoProfile
end
section
namespace Erdos1160.Sims
open CentralKernelCount ClassTwoProfile OrbitUp
open Erdos1160Growth.LowerTriangularUpper (squareCore)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
structure QuotientMark (H : Subgroup G) [H.Normal] (n : ℕ) where
  ord : Fin n→ℕ
  positive : ∀i,0 < ord i
  bounded : ∀i,ord i ≤ Nat.card G
  y : Fin n→G
  powers : ∀i,y i^ord i∈H
  generates : adjoin H y=⊤
  size : (∏i,ord i)*Nat.card H=Nat.card G
  rank : (squareCore (G⧸H)).index=2^n
theorem exists_quotient_mark (hG : IsPGroup 2 G) (H : Subgroup G) [H.Normal] (hc : commutator G ≤ H) :
    ∃n,Nonempty (QuotientMark H n) := by
  classical
  let q := QuotientGroup.mk' H
  have sq := QuotientGroup.mk'_surjective H
  let commutes (a b : G⧸H) : a*b=b*a := by
    obtain ⟨u,rfl⟩ := sq a
    obtain ⟨v,rfl⟩ := sq b
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)))
  letI : CommGroup (G⧸H) := { (inferInstance : Group (G⧸H)) with mul_comm := commutes }
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m,hm⟩ := IsPGroup.iff_card.mp (hG.to_quotient H)
  obtain ⟨n,e,he,hes,⟨f⟩⟩ := exists_cyclic_coords (G⧸H) hm
  let π := f.toMonoidHom.comp q
  have hπ : Function.Surjective π := f.surjective.comp sq
  choose y hy using fun i=>hπ (gen e i)
  have hk : π.ker=H := by
    rw [show π.ker=(f.toMonoidHom.ker).comap q from rfl,MonoidHom.ker_eq_bot _ f.injective,
      MonoidHom.comap_bot,QuotientGroup.ker_mk']
  have prod : (∏i,2^(e i))=H.index := by rw [Finset.prod_pow_eq_pow_sum,hes,←hm];rfl
  have genc : adjoin H y=⊤ := by
    let A := adjoin H y
    have im : A.map π=⊤ := by
      rw [←top_le_iff,←gen_closure e,Subgroup.closure_le]
      rintro _ ⟨i,rfl⟩
      refine ⟨y i,?_,hy i⟩
      exact le_sup_right (a:=H) (Subgroup.subset_closure ⟨i,rfl⟩)
    have h := congrArg (Subgroup.comap π) im
    rw [Subgroup.comap_map_eq,Subgroup.comap_top,hk,sup_eq_left.mpr (show H ≤ A from le_sup_left)] at h
    exact h
  have hidx : (squareCore (G⧸H)).index=2^n := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α:=squareCore (G⧸H)))
    rw [Subgroup.card_mul_index,hm,←hes]
    exact (squareCore_size f he).symm
  refine ⟨n,⟨⟨(fun i=>2^(e i)),fun i=>Nat.two_pow_pos _,?_,y,?_,genc,prod ▸ H.index_mul_card,hidx⟩⟩⟩
  · intro i
    have hi : e i≤∑j,e j := Finset.single_le_sum (f:=e) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hi).trans ((hes ▸ hm.symm.le).trans (Nat.card_le_card_of_surjective q sq))
  · intro i
    rw [←hk,MonoidHom.mem_ker,map_pow,hy,gen_pow]
theorem outer_quotient_mark {d : ℕ} (hG : IsPGroup 2 G) (p : G→*Multiplicative (V d))
    (hp : Function.Surjective p) (hk : p.ker=squareCore G)
    (H : Subgroup G) [H.Normal] (hc : commutator G ≤ H) :
    ∃ n,Nonempty (QuotientMark H n) ∧ n+Module.finrank K (vectorSub (H.map p))=d := by
  obtain ⟨n,⟨M⟩⟩ := exists_quotient_mark hG H hc
  have hIdx : (H.map p).index=2^n := by
    let q := QuotientGroup.mk' H
    have sq := QuotientGroup.mk'_surjective H
    rw [←M.rank,←CentralKernelCount.squareCore_map q sq,Subgroup.index_map,Subgroup.index_map,
      p.range_eq_top_of_surjective hp,q.range_eq_top_of_surjective sq]
    simp only [Subgroup.index_top,mul_one, q,QuotientGroup.ker_mk',hk,sup_comm]
  have hCard : Nat.card (H.map p)=2^(Module.finrank K (vectorSub (H.map p))) := by
    change Nat.card (vectorSub (H.map p))=_
    rw [Module.natCard_eq_pow_finrank (K:=K),Nat.card_zmod]
  refine ⟨n,⟨M⟩,Nat.pow_right_injective (by decide : 1 < 2) ?_⟩
  change 2^(n+Module.finrank K (vectorSub (H.map p)))=2^d
  rw [pow_add,←hIdx,←hCard,Subgroup.index_mul_card]
  change Nat.card (Fin d→ZMod 2)=_
  rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
private theorem generator_square_index {A : Type} [Group A] [Finite A] {r : ℕ} (x : Fin r→A)
    (hx : Subgroup.closure (Set.range x)=⊤) : (squareCore A).index ≤ 2^r := by
  classical
  let H := squareCore A
  let π := QuotientGroup.mk' H
  have onto := QuotientGroup.mk'_surjective H
  have hb (v : A⧸H) : v^2=1 := by
    obtain ⟨u,rfl⟩ := onto v
    rw [←map_pow,pow_two]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨u,rfl⟩)
  have inv (v : A⧸H) : v⁻¹=v := inv_eq_of_mul_eq_one_left (by rw [←pow_two];exact hb _)
  letI : CommGroup (A⧸H) := { (inferInstance : Group (A⧸H)) with
    mul_comm := fun a b=>by rw [←inv (a*b),mul_inv_rev,inv,inv] }
  let y := π ∘ x
  let T := Finset.univ.image y
  have hT : (T:Set (A⧸H))=Set.range y := by ext;simp [T]
  have hgen : Subgroup.closure (T:Set (A⧸H))=⊤ := by
    rw [hT,Set.range_comp,←MonoidHom.map_closure,hx,Subgroup.map_top_of_surjective π onto]
  have rank : Group.rank (A⧸H) ≤ r := (Group.rank_le hgen).trans (Finset.card_image_le.trans_eq (by simp))
  exact (Nat.le_of_dvd (Nat.two_pow_pos _) (card_dvd_exponent_pow_rank' _ hb)).trans (Nat.pow_le_pow_right (by decide) rank)
theorem inner_quotient_mark {r : ℕ} (hG : IsPGroup 2 G) (x : Fin r→G)
    (hx : Subgroup.closure (Set.range x)=⊤) (H : Subgroup G) [H.Normal] (hc : commutator G ≤ H) :
    ∃ n,Nonempty (QuotientMark H n) ∧ n ≤ r := by
  obtain ⟨n,⟨M⟩⟩ := exists_quotient_mark hG H hc
  let q := QuotientGroup.mk' H
  have sq := QuotientGroup.mk'_surjective H
  have gen : Subgroup.closure (Set.range (q ∘ x))=⊤ := by
    rw [Set.range_comp,←MonoidHom.map_closure,hx,Subgroup.map_top_of_surjective q sq]
  refine ⟨n,⟨M⟩,(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ?_⟩
  rw [←M.rank]
  exact generator_square_index _ gen
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open CentralKernelCount OrbitUp OrbitUp.MinSpan
open Erdos1160.DeepJacobi (Second secondBracket)
open Erdos1160Growth.LowerTriangularUpper (squareCore)
open scoped commutatorElement
theorem frame_of_seed {m d b σ : ℕ} (E : FiniteGrp.{0}) (size : Nat.card E=2^m)
    (C : Seed E d b σ) : ∃ S : Shape m d σ, Nonempty (SimsFrame S C.β.val E) := by
  classical
  let H := C.H
  let Q := headSub H
  let π := toHeadSub H
  have sp := toHeadSub_surj H
  letI : H.Normal := Subgroup.Normal.of_commutator_le E C.commutator_le
  have pg := IsPGroup.of_card size
  have pH := pg.to_subgroup H
  have pQ := (pg.to_quotient (commutatorTail E)).to_subgroup Q
  have genQ : Subgroup.closure (Set.range (π ∘ C.x))=⊤ := by
    rw [Set.range_comp,←MonoidHom.map_closure,C.generates,Subgroup.map_top_of_surjective π sp]
  obtain ⟨n,⟨ext⟩,ns⟩ := outer_quotient_mark pg C.p C.onto C.ker H C.commutator_le
  rw [C.subrank] at ns
  obtain ⟨r,⟨root⟩,rs⟩ := inner_quotient_mark pQ (π ∘ C.x) genQ (commutator Q) le_rfl
  obtain ⟨h,hQ⟩ := pQ.exists_card_eq
  obtain ⟨t,ht⟩ := (pg.to_subgroup (commutatorTail E)).exists_card_eq
  have hs : Nat.card H=2^(h+t) := by
    rw [card_of_onto π sp,inside_tail_card H C.derived,ht,hQ,pow_add]
  have hHm : h+t ≤ m := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hs ▸ size ▸ Subgroup.card_le_card_group H)
  have hQm : Nat.card Q ≤ 2^m := (Nat.card_le_card_of_surjective π sp).trans (size ▸ Subgroup.card_le_card_group H)
  have hW : Nat.card (W b)=2^b := by change Nat.card (Fin b→ZMod 2)=_;rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  have hb : Nat.card (Second (headQuot E))=2^b := (Nat.card_congr C.a.toEquiv).trans hW
  have mt := head_size_budget size C.p C.onto C.ker hb ht
  choose lift hlift using fun j=>sp (root.y j)
  let ro (j : Fin r) : Fin (2^m) := ⟨root.ord j-1,by have := (root.bounded j).trans hQm;have := root.positive j;omega⟩
  let xo (j : Fin n) : Fin (2^m) := ⟨ext.ord j-1,by have := ext.bounded j;rw [size] at this;have := ext.positive j;omega⟩
  have rord (j : Fin r) : (ro j).val+1=root.ord j := by change root.ord j-1+1=_;have := root.positive j;omega
  have xord (j : Fin n) : (xo j).val+1=ext.ord j := by change ext.ord j-1+1=_;have := ext.positive j;omega
  let S : Shape m d σ := ⟨r,n,h,t,rs,ns.le,hHm,ro,xo,fun i=>(C.p (lift i).val).toAdd,
    fun i=>(C.p (C.x i).val).toAdd,fun i=>(C.p (ext.y i)).toAdd⟩
  let R : ExtensionMark (W b) Q r := ⟨C.headIncl,root.y,by rw [C.headIncl_range];exact root.generates⟩
  let X : ExtensionMark H E n := ⟨H.subtype,ext.y,by rw [H.range_subtype];exact ext.generates⟩
  let comm (x y : E) : H := ⟨⁅x,y⁆,C.commutator_le (secondBracket x y).property⟩
  let c : ExtraSlot n σ→H := Sum.elim (fun z=>comm (ext.y z.1) (C.x z.2).val)
    (fun z=>comm (ext.y z.1) (ext.y (second z)))
  let v (j : Fin n) : H := ⟨ext.y j^ext.ord j,ext.powers j⟩
  refine ⟨S,⟨⟨FiniteGrp.of Q,FiniteGrp.of H,R,?_,?_,?_,?_,hQ,hs,π,sp,?_,?_,C.x,C.generates,
    headSub_class_two H,headSub_derived_binary H C.derived,C.head_order,X,v,c,?_,?_,?_,by change t ≤ m-d-b;omega⟩⟩⟩
  · change C.headIncl.range ≤ Subgroup.center Q
    rw [C.headIncl_range];exact headSub_class_two H
  · intro i
    change ∃ v,root.y i^((ro i).val+1)=C.headIncl v
    rw [rord]
    obtain ⟨v,hv⟩ := (C.headIncl_range ▸ root.powers i : root.y i^root.ord i∈C.headIncl.range)
    exact ⟨v,hv.symm⟩
  · intro z
    change ⁅root.y z.1,root.y (second z)⁆=C.headIncl (.ofAdd (C.β.val _ _))
    rw [←hlift,←hlift,←map_commutatorElement]
    exact C.compatible_of_lift _ _ ⁅lift z.1,lift (second z)⁆ rfl
  · change (∏i,((ro i).val+1))*Nat.card (W b) ≤ Nat.card Q
    simp only [rord,hW,←C.head_order]
    exact root.size.le
  · exact headSub_kernel_frattini H hs C.derived
  · exact ((inside_tail_card H C.derived).trans ht).le
  · intro z
    rcases z with z|z <;> exact C.compatible_of_lift _ _ _ rfl
  · refine ⟨fun i=>?_,fun _ _=>rfl,fun _=>rfl⟩
    change ext.y i^((xo i).val+1)=ext.y i^ext.ord i
    rw [xord]
  · change (∏i,((xo i).val+1))*Nat.card H ≤ Nat.card E
    simpa only [xord] using ext.size.le
theorem group_frame {m d : ℕ} (E : FiniteGrp.{0}) (size : Nat.card E=2^m)
    (rank : Nat.card (E⧸squareCore E)=2^d) :
    ∃ b σ,d+b ≤ m ∧ σ ≤ d ∧ σ-1 ≤ b ∧ ∃(β : minimalAlternating d b σ)(S : Shape m d σ),
      Nonempty (SimsFrame S β.val E) := by
  obtain ⟨b,σ,hd,hs,hb,⟨C⟩⟩ := seed_exists size rank
  obtain ⟨S,frame⟩ := frame_of_seed E size C
  exact ⟨b,σ,hd,hs,hb,C.β,S,frame⟩
end Erdos1160.Sims
end
section
namespace Erdos1160.OuterExtensions
open CategoryTheory
abbrev ClassOf (n : ℕ) := Tables.orderClasses n
noncomputable def orderRep {n : ℕ} (c : ClassOf n) : FiniteGrp.{0} := c.property.choose
theorem rep_size {n : ℕ} (c : ClassOf n) : Nat.card (orderRep c) = n := c.property.choose_spec.1
end Erdos1160.OuterExtensions
end
section
namespace Erdos1160.OuterExtensions
open CategoryTheory
open scoped BigOperators
noncomputable instance classFintype (n : ℕ) : Fintype (ClassOf n) := (Tables.orderClasses_finite n).fintype
end Erdos1160.OuterExtensions
end
section
namespace Erdos1160.Paper85
open OuterExtensions
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160Growth.LowerTriangularUpper
open scoped Classical
def inCentralStrip (m d : ℕ) : Prop :=
  1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d
noncomputable def generatorRank {m : ℕ} (c : ClassOf (2^m)) :=
  Nat.log 2 (frattini (orderRep c)).index
end Erdos1160.Paper85
end
section
namespace Erdos1160.Sims
open Erdos1160.OuterExtensions Erdos1160.Paper85 OrbitUp.MinSpan
open Erdos1160Growth.LowerTriangularUpper (squareCore frattini_eq_squareCore)
theorem frame_coverage {m : ℕ} (c : ClassOf (2^m)) :
    let d := generatorRank c
    ∃ b σ,d+b ≤ m ∧ σ ≤ d ∧ σ-1 ≤ b ∧ ∃(β : minimalAlternating d b σ)(S : Shape m d σ),
      Nonempty (SimsFrame S β.val (orderRep c)) := by
  let G := orderRep c
  have hG : Nat.card G=2^m := rep_size c
  obtain ⟨d,hd⟩ := ((IsPGroup.of_card hG).to_quotient (frattini G)).exists_card_eq
  change (frattini G).index=2^d at hd
  have hd' : generatorRank c=d := by
    change Nat.log 2 (frattini G).index=d
    rw [hd,Nat.log_pow (by decide : 1 < 2)]
  dsimp only
  rw [hd']
  exact group_frame G hG (by rw [←frattini_eq_squareCore hG];exact hd)
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open CentralKernelCount OrbitUp.MinSpan
open scoped commutatorElement
theorem bits_generate (b : ℕ) : Subgroup.closure (Set.range (bit : Fin b→W b))=⊤ := by
  apply top_unique
  intro v _
  rw [←standardWord_correct v]
  exact word_mem (Subgroup.closure (Set.range (bit : Fin b→W b))) bit (fun i=>Subgroup.subset_closure ⟨i,rfl⟩) _
theorem homs_of_gens {H Q : Type} [Group H] [Group Q] [Finite Q] {s : ℕ}
    (a : Fin s→H) (ha : Subgroup.closure (Set.range a)=⊤) : Nat.card (H→*Q) ≤ Nat.card Q^s := by
  let ev (f : H→*Q) (i : Fin s) := f (a i)
  have inj : Function.Injective ev := by
    intro f g eq
    apply MonoidHom.eq_of_eqOn_dense ha
    rintro _ ⟨i,rfl⟩
    exact congrFun eq i
  simpa only [Nat.card_fun,Nat.card_fin] using Nat.card_le_card_of_injective ev inj
structure FixedPair {m d b σ} (S : Shape m d σ) (β : Tensor d b)
    (H Q E : FiniteGrp.{0}) where
  base : Fin σ→H
  gen : Subgroup.closure (Set.range base)=⊤
  π : H→*Q
  kerSize : Nat.card π.ker ≤ 2^S.t
  incl : W b→*Q
  mark : ExtensionMark H E S.n
  pw : Fin S.n→H
  co : ExtraSlot S.n σ→H
  pat : ∀z,π (co z)=incl (extraPattern S β z)
  fits : ExtensionFits mark base (fun i=>(S.extOrder i).val+1) pw co
  size : (∏i,((S.extOrder i).val+1))*Nat.card H ≤ Nat.card E
def SimsFrame.overPair {m d b σ} {S : Shape m d σ} {β : Tensor d b} {E H Q : FiniteGrp.{0}}
    (D : SimsFrame S β E) (e : D.H≃*H) (v : D.Q≃*Q) : FixedPair S β H Q E := by
  let π := v.toMonoidHom.comp (D.π.comp e.symm.toMonoidHom)
  have ke : D.π.ker.map e.toMonoidHom=π.ker := by
    ext w
    constructor
    · rintro ⟨x,hx,rfl⟩
      change v (D.π (e.symm (e x)))=1
      rw [e.symm_apply_apply,show D.π x=1 from hx,v.map_one]
    · intro hw
      refine ⟨e.symm w,?_,e.apply_symm_apply w⟩
      apply v.injective
      exact (show v (D.π (e.symm w))=1 from hw).trans v.map_one.symm
  let z : ExtensionMark H E S.n := {
    incl := D.ext.incl.comp e.symm.toMonoidHom
    x := D.ext.x
    generate := by
      change adjoin (D.ext.incl.comp e.symm.toMonoidHom).range D.ext.x=⊤
      rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,←MonoidHom.range_eq_map];exact D.ext.generate }
  refine ⟨e ∘ D.base,?_,π,?_,v.toMonoidHom.comp D.root.incl,z,e ∘ D.powers,e ∘ D.comms,?_,?_,?_⟩
  · change Subgroup.closure (Set.range (e.toMonoidHom ∘ D.base))=⊤
    rw [Set.range_comp,←MonoidHom.map_closure (f:=e.toMonoidHom),D.gen,←MonoidHom.range_eq_map,
      MonoidHom.range_eq_top];exact e.surjective
  · rw [←ke,Subgroup.card_map_of_injective e.injective];exact D.kerSize
  · intro j;change v (D.π (e.symm (e (D.comms j))))=v (D.root.incl _)
    rw [e.symm_apply_apply,D.patterns]
  · refine ⟨fun i=>?_,fun i j=>?_,fun z=>?_⟩
    · change D.ext.x i^_=D.ext.incl (e.symm (e (D.powers i)))
      simpa only [e.symm_apply_apply] using D.fits.1 i
    · change ⁅D.ext.x i,D.ext.incl (e.symm (e (D.base j)))⁆=D.ext.incl (e.symm (e (D.comms (.inl (i,j)))))
      simpa only [e.symm_apply_apply] using D.fits.2.1 i j
    · change ⁅_,_⁆=D.ext.incl (e.symm (e (D.comms (.inr z))))
      simpa only [e.symm_apply_apply] using D.fits.2.2 z
  · rw [←Nat.card_congr e.toEquiv];exact D.size
theorem fixed_pair_count {I : Type} [Finite I] {m d b σ} {S : Shape m d σ} {β : Tensor d b}
    {H Q : FiniteGrp.{0}} (E : I→FiniteGrp.{0}) (D : ∀i,FixedPair S β H Q (E i))
    (sep : ∀i j,Nonempty (E i≃*E j)→i=j) :
    Nat.card I≤(Nat.card H^σ*(Nat.card Q^σ*Nat.card Q^b))*
      (Nat.card H^S.n*(2^S.t)^(S.n*σ+S.n*(S.n-1)/2)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    let i0 := h.some
    let A := (Fin σ→H) × (H→*Q) × (W b→*Q)
    let key (i:I) : A := ((D i).base,(D i).π,(D i).incl)
    haveI : Finite (H→*Q) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
    haveI : Finite (W b→*Q) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
    have cov : Nat.card A ≤ Nat.card H^σ*(Nat.card Q^σ*Nat.card Q^b) := by
      dsimp only [A]
      rw [Nat.card_prod,Nat.card_prod,Nat.card_fun,Nat.card_fin]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (homs_of_gens (D i0).base (D i0).gen)
        (homs_of_gens bit (bits_generate b)))
    refine (PresentationCount.card_le_of_fiber_bound key _ (fun a=>?_)).trans (Nat.mul_le_mul_right _ cov)
    let F := {i:I // key i=a}
    by_cases hf : Nonempty F
    swap
    · haveI : IsEmpty F := not_nonempty_iff.mp hf
      change Nat.card F≤_;simp
    let j := hf.some
    have parts (i:F) : (D i.val).base=(D j.val).base ∧ (D i.val).π=(D j.val).π ∧ (D i.val).incl=(D j.val).incl := by
      have h := i.property.trans j.property.symm
      exact ⟨congrArg Prod.fst h,congrArg (fun z:A=>z.2.1) h,congrArg (fun z:A=>z.2.2) h⟩
    let pat := (D j.val).incl ∘ extraPattern S β
    have step := restricted_extension_count (fun i:F=>(E i.val : Type)) (fun i=>(D i.val).mark)
      (D j.val).base (D j.val).gen (fun i=>(S.extOrder i).val+1) (fun _=>Nat.succ_pos _)
      (D j.val).π pat (fun i=>(D i.val).pw) (fun i=>(D i.val).co)
      (fun i z=>by dsimp [pat];rw [←(parts i).2.1,←(parts i).2.2];exact (D i.val).pat z)
      (fun i=>by rw [←(parts i).1];exact (D i.val).fits)
      (fun i=>(D i.val).size) (fun i j e=>Subtype.ext (sep _ _ e))
    exact step.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (D j.val).kerSize _))
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open CategoryTheory CentralKernelCount OrbitUp.MinSpan
open Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi (Second)
abbrev IsoClass := Quotient (isIsomorphicSetoid FiniteGrp.{0})
abbrev cls (G:FiniteGrp.{0}) : IsoClass := Quotient.mk _ G
private theorem same_of_iso {G H:FiniteGrp.{0}} (h:Nonempty (G≃*H)) : cls G=cls H :=
  Quotient.sound ⟨InducedCategory.isoMk (F:=FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X:=G.toGrp) (Y:=H.toGrp) h.some)⟩
private noncomputable def iso_of_same {G H:FiniteGrp.{0}} (h:cls G=cls H) : G≃*H :=
  ((inducedFunctor FiniteGrp.toGrp).mapIso (Quotient.exact h).some).groupIsoToMulEquiv
theorem by_iso_cohorts {I:Type} [Finite I] (X:I→FiniteGrp.{0}) {B M:ℕ}
    (keys : ∀{P:Type} [Finite P] (f:P→I), (∀a b,Nonempty (X (f a)≃*X (f b))→a=b)→Nat.card P ≤ B)
    (fiber : ∀{P:Type} [Finite P] (f:P→I),Function.Injective f→∀ r:I,
      (∀a,Nonempty (X (f a)≃*X r))→Nat.card P ≤ M) : Nat.card I ≤ B*M := by
  classical
  let R := Setoid.ker (fun i=>cls (X i))
  let P := Quotient R
  let key : I→P := Quotient.mk _
  have keybd : Nat.card P ≤ B := keys (fun c:P=>c.out) (fun a b h=>by
    have eq : key a.out=key b.out := Quotient.sound (same_of_iso h)
    simpa only [key,Quotient.out_eq] using eq)
  apply (PresentationCount.card_le_of_fiber_bound key M (fun p=>?_)).trans (Nat.mul_le_mul_right M keybd)
  apply fiber (fun a:{i:I // key i=p}=>a.val) Subtype.val_injective p.out
  intro a
  have e : key a.val=key p.out := a.property.trans (Quotient.out_eq p).symm
  exact ⟨iso_of_same (Quotient.exact e)⟩
theorem root_class_bound {I:Type} [Finite I] {m d b σ} {S : Shape m d σ} {β : Tensor d b}
    (E : I→FiniteGrp.{0}) (D : ∀i,SimsFrame S β (E i))
    (sep : ∀i j,Nonempty ((D i).Q≃*(D j).Q)→i=j) : Nat.card I ≤ 2^(b*S.r) := by
  have h := root_pattern_count (fun i=>(D i).Q) (fun i=>(D i).root) bit (bits_generate b)
    (fun i=>(D i).central) (fun i=>(S.rootOrder i).val+1) (fun _=>Nat.succ_pos _) (rootPattern S β)
    (fun i=>(D i).rootPowers) (fun i=>(D i).rootComms) (fun i=>(D i).rootSize) sep
  exact h.trans_eq (by change (Nat.card (Fin b→ZMod 2))^S.r=_;rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod,←pow_mul])
theorem tower_class_bound {I:Type} [Finite I] {m d b σ} {S : Shape m d σ} {β : Tensor d b}
    (E : I→FiniteGrp.{0}) (D : ∀i,SimsFrame S β (E i)) {E₀:FiniteGrp.{0}} (A:SimsFrame S β E₀)
    (same : ∀i,Nonempty ((D i).Q≃*A.Q))
    (sep : ∀i j,Nonempty ((D i).H≃*(D j).H)→i=j) :
    Nat.card I ≤ 2^(S.t*(σ*(σ+1)/2+jacobiRank A.Q)+σ*S.t.choose 2) := by
  classical
  let Q := A.Q
  let T := frattiniClasses S.h S.t Q
  have fin : T.Finite := (Tables.orderClasses_finite (2^(S.h+S.t))).subset (by
    rintro _ ⟨G,sz,_,rfl⟩;exact ⟨G,sz,rfl⟩)
  haveI : Finite T := fin.to_subtype
  let key (i:I) : T := ⟨cls (D i).H,(D i).H,(D i).hsize,⟨(same i).some.toMonoidHom.comp (D i).π,
    (same i).some.surjective.comp (D i).onto,by
      intro x hx
      apply (D i).kerFrattini
      apply (same i).some.injective
      exact (show (same i).some ((D i).π x)=1 from hx).trans (same i).some.map_one.symm⟩,rfl⟩
  have inj : Function.Injective key := fun i j h=>sep i j ⟨iso_of_same (congrArg Subtype.val h)⟩
  have keyBound : Nat.card I ≤ T.ncard := (Nat.card_le_card_of_injective _ inj).trans_eq (Nat.card_coe_set_eq ..)
  let a : Fin σ→Q := A.π ∘ A.base
  have gen : Subgroup.closure (Set.range a)=⊤ := by
    dsimp [a]
    rw [Set.range_comp,←MonoidHom.map_closure, A.gen,←MonoidHom.range_eq_map,MonoidHom.range_eq_top]
    exact A.onto
  have hi := marked_jacobi_fiber_product (FreeGroup.lift a) (MonoidHom.range_eq_top.mp ((FreeGroup.range_lift_eq_closure).trans gen))
    A.qsize A.classTwo S.t
  refine keyBound.trans (hi.trans ?_)
  calc
    _ ≤ ∏i ∈ Finset.range S.t,2^(σ*(σ+1)/2+jacobiRank Q+i*σ) :=
      Finset.prod_le_prod' (fun _ _=>Nat.sub_le ..)
    _ = _ := by
      rw [Finset.prod_pow_eq_pow_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
        ←Finset.sum_mul,Finset.sum_range_id,←Nat.choose_two_right,Nat.mul_comm (S.t.choose 2)]
      rfl
end Erdos1160.Sims
end
section
namespace Erdos1160.GeneratorLocalization
noncomputable def F (x : ℝ) := x^2*(1-x)/2
noncomputable def weakCount (x y z w : ℝ) :=
  x^2*(y+z-w)/2+x*y*w/2+(w*y-w^2/2)*z+w*z^2/2
noncomputable def strongCount (x y z w : ℝ) :=
  x^2*(y+z-w)/2+(w*y-w^2/2)*z+w*z^2/2
theorem peak_gap (x : ℝ) : 2/27 - F x = (x-2/3)^2*(x+1/3)/2 := by unfold F; ring
theorem high_rank {x y z w : ℝ} (hs : x+y+z=1) (hx : 3/5 ≤ x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) : weakCount x y z w ≤ F x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have h : x/2-x^2+(1-3*x/2)*z-z^2/2-w*z/2 ≤ 0 := by
    nlinarith only [hx,mul_nonneg hx0 (sub_nonneg.mpr hx1),
      sq_nonneg (z-(1-3*x/2)),mul_nonneg hw hz]
  have hy' : y=1-x-z := by linarith
  unfold weakCount F
  rw [hy']
  nlinarith only [mul_nonpos_of_nonneg_of_nonpos hw h]
private theorem monotone_F {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2/3) : F x ≤ F y := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have h₁ : x^2+x*y+y^2 ≤ 3*y*(x+y)/2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 2*x+y by linarith)]
  have h₂ : x^2+x*y+y^2 ≤ x+y := by nlinarith only [h₁,mul_nonneg (show 0 ≤ 2-3*y by linarith) (add_nonneg hx hy0)]
  unfold F
  nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr h₂)]
private noncomputable def envelope (x w : ℝ) := F x+w*(1-2*x)/2-w^2*(1-x)/2
private theorem bound_envelope {x y z w : ℝ} (hs : x+y+z=1) (hw : 0 ≤ w)
    (hy : w ≤ y) : strongCount x y z w ≤ envelope x w := by
  have hz : z=1-x-y := by linarith
  unfold strongCount envelope F
  rw [hz]
  nlinarith only [mul_nonneg (mul_nonneg hw (hw.trans hy)) (sub_nonneg.mpr hy)]
private theorem envelope_low {x w : ℝ} (hx : 0 ≤ x) (hw : 0 ≤ w) (hwx : w ≤ x)
    (hx' : x ≤ 1/2) : envelope x w ≤ 1/16 := by
  by_cases hlow : x ≤ 2/7
  · have base : 0 ≤ 1-4*x+2*x^2 := by
      have h : 0 ≤ (2/7-x)*(4-2*(x+2/7)) := by
        apply mul_nonneg <;> linarith
      nlinarith only [h]
    have delta : 0 ≤ (1-2*x)-(1-x)*(w+x) := by
      nlinarith only [base,mul_nonneg (sub_nonneg.mpr hwx) (show 0 ≤ 1-x by linarith)]
    unfold envelope F
    nlinarith only [mul_nonneg (sub_nonneg.mpr hwx) delta, sq_nonneg (x-1/4)]
  · have xlo : 2/7 ≤ x := by linarith
    have b : 0 ≤ 4*((x-1/2)^2+(1/2-x)*(3/14)+(3/14)^2)+2 := by
      nlinarith only [sq_nonneg (x-1/2),hx']
    have poly : 0 ≤ 4*x^3-6*x^2+5*x-1 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr xlo) b]
    have bound : 16*(1-x)*(envelope x w-1/16) ≤ 0 := by
      unfold envelope F
      nlinarith only [mul_nonneg (show 0 ≤ 1-2*x by linarith) poly,
        sq_nonneg (2*(1-x)*w-(1-2*x))]
    by_contra! h
    exact (not_lt_of_ge bound) (mul_pos (by linarith) (sub_pos.mpr h))
theorem low_rank {x y z w : ℝ} (hs : x+y+z=1) (hx : 0 ≤ x) (hhi : x ≤ 3/5)
    (hw : 0 ≤ w) (hwy : w ≤ y) (hwx : w ≤ x) (hz : 0 ≤ z) : strongCount x y z w ≤ 9/125 := by
  by_cases hm : x ≤ 1/2
  · exact ((bound_envelope hs hw hwy).trans (envelope_low hx hw hwx hm)).trans (by norm_num)
  · have ys : z=1-x-y := by linarith
    have hb : strongCount x y z w ≤ F x := by
      have hneg : 0 ≤ w*(2*x-1+y^2)+w^2*z := by
        apply add_nonneg
        · apply mul_nonneg hw; nlinarith only [hm,sq_nonneg y]
        · exact mul_nonneg (sq_nonneg w) hz
      rw [ys] at hneg ⊢
      unfold strongCount F
      nlinarith only [hneg]
    have hf := monotone_F hx hhi (by norm_num : (3:ℝ)/5 ≤ 2/3)
    exact hb.trans (hf.trans (by norm_num [F]))
theorem separated_high_rank {x y z w ε : ℝ} (hs : x+y+z=1) (hx : 3/5 ≤ x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) (hε : ε^2 ≤ (x-2/3)^2) :
    weakCount x y z w ≤ 2/27-7*ε^2/15 := by
  have coef : (14:ℝ)/15 ≤ x+1/3 := by linarith
  have h₁ := mul_le_mul_of_nonneg_left coef (sq_nonneg (x-2/3))
  linarith only [high_rank hs hx hy hz hw,peak_gap x,hε,h₁]
end Erdos1160.GeneratorLocalization
end
section
namespace Erdos1160.GeneratorLocalization
def profileExponent (d b u q : ℕ) : ℕ :=
  (b-q)*d.choose 2 + (d.choose 2)*u + (q*b-q.choose 2)*u + q*u.choose 2
private theorem strip_gap {m d : ℕ} (hm : 0 < m)
    (out : ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)) :
    (1/3000:ℝ)^2≤((d:ℝ)/m-2/3)^2 := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have split : 3000*d+ m ≤ 2000*m ∨ 2000*m + m ≤ 3000*d := by omega
  rcases split with h|h
  · have hR : 3000*(d:ℝ)+m ≤ 2000*m := by exact_mod_cast h
    have low : (d:ℝ)/m ≤ 2/3-1/3000 := (div_le_iff₀ hmR).mpr (by linarith)
    nlinarith only [mul_nonneg (show 0 ≤ 2/3-(d:ℝ)/m-1/3000 by linarith)
      (show 0 ≤ 2/3-(d:ℝ)/m+1/3000 by linarith)]
  · have hR : 2000*(m:ℝ)+m ≤ 3000*d := by exact_mod_cast h
    have high : (2/3+1/3000:ℝ) ≤ d/m := (le_div_iff₀ hmR).mpr (by linarith)
    nlinarith only [mul_nonneg (show 0≤(d:ℝ)/m-2/3-1/3000 by linarith)
      (show 0≤(d:ℝ)/m-2/3+1/3000 by linarith)]
theorem offstrip_profile_cubic {m d b u q : ℕ} (hm : 0 < m) (sum : d+b+u=m)
    (hqb : q ≤ b) (hqd : q ≤ d)
    (out : ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)) :
    27*100000000*profileExponent d b u q + 27*m^3 ≤ 2*100000000*m^3 := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  let x : ℝ := d/m
  let y : ℝ := b/m
  let z : ℝ := u/m
  let w : ℝ := q/m
  have hh : x+y+z=1 := by
    have H : (d:ℝ)+b+u=m := by exact_mod_cast sum
    dsimp [x,y,z];rw [←add_div,←add_div,H,div_self hmR.ne']
  have hx : 0 ≤ x := by dsimp [x];positivity
  have hy : 0 ≤ y := by dsimp [y];positivity
  have hz : 0 ≤ z := by dsimp [z];positivity
  have hw : 0 ≤ w := by dsimp [w];positivity
  have hwx : w ≤ x := div_le_div_of_nonneg_right (by exact_mod_cast hqd) hmR.le
  have hwy : w ≤ y := div_le_div_of_nonneg_right (by exact_mod_cast hqb) hmR.le
  have upper : strongCount x y z w ≤ 2/27-1/100000000 := by
    by_cases hi : 3/5 ≤ x
    · have h := separated_high_rank hh hi hy hz hw (strip_gap hm out)
      have leweak : strongCount x y z w ≤ weakCount x y z w := by
        unfold strongCount weakCount
        nlinarith only [mul_nonneg (mul_nonneg hx hy) hw]
      linarith
    · have h := low_rank hh hx (le_of_not_ge hi) hw hwy hwx hz
      linarith
  have scale : strongCount x y z w*(m:ℝ)^3 =
      (d:ℝ)^2*(b+u-q)/2+((q:ℝ)*b-(q:ℝ)^2/2)*u+(q:ℝ)*u^2/2 := by
    dsimp [x,y,z,w,strongCount]
    field_simp [hmR.ne']
  have small : (profileExponent d b u q : ℝ) ≤ strongCount x y z w*(m:ℝ)^3 := by
    have qq : q.choose 2 ≤ q*b := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self ..).trans (Nat.mul_le_mul_left _ ((Nat.sub_le ..).trans hqb))
    rw [scale,profileExponent]
    push_cast [Nat.cast_sub hqb,Nat.cast_sub qq,Nat.cast_choose_two]
    nlinarith only [mul_nonneg (show 0≤(b:ℝ)-q by exact sub_nonneg.mpr (by exact_mod_cast hqb))
      (Nat.cast_nonneg d (α:=ℝ)),mul_nonneg (Nat.cast_nonneg d (α:=ℝ)) (Nat.cast_nonneg u (α:=ℝ))]
  have bnd := mul_le_mul_of_nonneg_right upper (show 0≤(m:ℝ)^3 by positivity)
  have ans : 27*100000000*(profileExponent d b u q : ℝ)+27*(m:ℝ)^3 ≤ 2*100000000*(m:ℝ)^3 := by
    linarith only [small,bnd]
  exact_mod_cast ans
end Erdos1160.GeneratorLocalization
end
section
namespace Erdos1160.GeneratorLocalization
private theorem choose_two_add (a b : ℕ) :
    (a+b).choose 2 = a.choose 2 + a*b + b.choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ,Nat.choose_succ_succ,Nat.choose_succ_succ b,
      Nat.choose_one_right,Nat.choose_one_right,ih]
    ring
theorem sims_extension_price {m d b σ n q ν t u : ℕ} (hdb : d+b ≤ m)
    (hu : u=m-d-b) (ht : t ≤ u) (hn : n+σ ≤ d) (hq : q=σ-1) (hb : q ≤ b)
    (hν : ν+q.choose 2≤σ*b) :
    t*(σ*(σ+1)/2+ν)+σ*t.choose 2+t*(n*σ+n.choose 2) ≤
      d.choose 2*u+(q*b-q.choose 2)*u+q*u.choose 2+4*m^2 := by
  have choose_bound (a : ℕ) : a.choose 2 ≤ a*a := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
  have qsub : q.choose 2 ≤ q*b := (choose_bound q).trans (Nat.mul_le_mul_left q hb)
  have hσ : σ ≤ q+1 := by omega
  have hs : σ*b ≤ q*b+b := by simpa [Nat.add_mul] using Nat.mul_le_mul_right b hσ
  have nu : ν ≤ q*b-q.choose 2+b := by omega
  have tr : σ*(σ+1)/2=σ.choose 2+σ := by
    calc
      _ = (σ+1).choose 2 := by rw [Nat.choose_two_right];simp [Nat.mul_comm]
      _ = _ := by rw [Nat.choose_succ_succ,Nat.choose_one_right,add_comm]
  have bin := Nat.choose_le_choose 2 hn
  rw [choose_two_add] at bin
  have block : σ*(σ+1)/2+(n*σ+n.choose 2) ≤ d.choose 2+σ := by rw [tr];omega
  have uM : u ≤ m := by omega
  have dM : σ ≤ m := by omega
  have tM := ht.trans uM
  have bM : b ≤ m := by omega
  have tσ := Nat.mul_le_mul tM dM
  have tb := Nat.mul_le_mul tM bM
  have tu := Nat.choose_le_choose 2 ht
  have uu := (choose_bound u).trans (Nat.mul_le_mul uM uM)
  have hw := Nat.mul_le_mul hσ tu
  have p₁ := Nat.mul_le_mul_left t block
  have p₂ := Nat.mul_le_mul_left t nu
  have dt := Nat.mul_le_mul_left (d.choose 2) ht
  have qt := Nat.mul_le_mul_left (q*b-q.choose 2) ht
  nlinarith only [p₁,p₂,tσ,tb,hw,uu,dt,qt]
end Erdos1160.GeneratorLocalization
end
section
namespace Erdos1160.Sims
open CentralKernelCount OrbitUp.MinSpan Erdos1160.CentralLifts.Survival
open GeneratorLocalization
theorem sims_fixed_count {I:Type} [Finite I] {m d b σ} {S : Shape m d σ} {β : Tensor d b}
    (E : I→FiniteGrp.{0}) (D : ∀i,SimsFrame S β (E i)) (hdb : d+b ≤ m) (hq : σ-1 ≤ b)
    (sep : ∀i j,Nonempty (E i≃*E j)→i=j) :
    let t := m-d-b
    Nat.card I ≤ 2^(d.choose 2*t+((σ-1)*b-(σ-1).choose 2)*t+(σ-1)*t.choose 2+9*m^2) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    let q := σ-1
    let u := m-d-b
    let L := σ*b-q.choose 2
    let head := S.t*(σ*(σ+1)/2+L)+σ*S.t.choose 2
    let extra := S.t*(S.n*σ+S.n.choose 2)
    have hl : L+q.choose 2≤σ*b := by
      have ch : q.choose 2 ≤ q*b := by
        rw [Nat.choose_two_right]
        exact (Nat.div_le_self ..).trans (Nat.mul_le_mul_left _ ((Nat.sub_le ..).trans hq))
      dsimp only [L];rw [Nat.sub_add_cancel (ch.trans (Nat.mul_le_mul_right b (Nat.sub_le σ 1)))]
    have hd : d ≤ m := by omega
    have hb : b ≤ m := by omega
    have hs : σ ≤ m := by have := S.n_le;omega
    have hn : S.n ≤ m := by have := S.n_le;omega
    have cost := sims_extension_price hdb (u:=u) rfl (D h.some).tail S.n_le (q:=q) rfl hq hl
    have total : Nat.card I ≤ 2^(m^2)*(2^head * 2^(4*m^2+extra)) := by
      apply by_iso_cohorts (fun i=>(D i).Q)
      · intro P _ f separated
        exact (root_class_bound (fun i=>E (f i)) (fun i=>D (f i)) separated).trans
          (Nat.pow_le_pow_right (by decide) (by simpa only [pow_two] using Nat.mul_le_mul hb (S.r_le.trans hs)))
      · intro P _ f hf r same
        apply by_iso_cohorts (fun i:P=>(D (f i)).H)
        · intro J _ g disj
          have bnd := tower_class_bound (fun i:J=>E (f (g i))) (fun i=>D (f (g i))) (D r) (fun i=>same (g i)) disj
          have gen : Subgroup.closure (Set.range ((D r).π ∘ (D r).base))=⊤ := by
            rw [Set.range_comp,←MonoidHom.map_closure,(D r).gen,←MonoidHom.range_eq_map,MonoidHom.range_eq_top]
            exact (D r).onto
          have cap := marked_jacobi_rank_bound _ gen (D r).classTwo (D r).elementary (D r).dimDerived hq
          have bound : jacobiRank (D r).Q ≤ L := by dsimp [L,q];omega
          exact bnd.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right
            (Nat.mul_le_mul_left _ (Nat.add_le_add_left bound _)) _))
        · intro J _ g hg s sameH
          let H := (D (f s)).H
          let Q := (D r).Q
          let M (i:J) : FixedPair S β H Q (E (f (g i))) :=
            (D (f (g i))).overPair (sameH i).some (same (g i)).some
          have ext := fixed_pair_count (fun i=>E (f (g i))) M (fun i j e=>hg (hf (sep _ _ e)))
          have cH : Nat.card H ≤ 2^m := (D (f s)).hsize.le.trans (Nat.pow_le_pow_right (by decide) S.ht_le)
          have cQ : Nat.card Q ≤ 2^m := (D r).qsize.le.trans (Nat.pow_le_pow_right (by decide) ((Nat.le_add_right ..).trans S.ht_le))
          have field {X l : ℕ} (a : X ≤ 2^m) (c : l ≤ m) : X^l ≤ 2^(m^2) := by
            refine (Nat.pow_le_pow_left a _).trans ?_;rw [←pow_mul,pow_two];exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ c)
          have rem : (2^S.t)^(S.n*σ+S.n*(S.n-1)/2)=2^extra := by rw [←pow_mul,←Nat.choose_two_right]
          apply ext.trans
          rw [rem]
          refine (Nat.mul_le_mul (Nat.mul_le_mul (field cH hs) (Nat.mul_le_mul (field cQ hs) (field cQ hb)))
              (Nat.mul_le_mul_right _ (field cH hn))).trans_eq ?_
          simp only [←pow_add]
          congr 1;ring
    refine total.trans ?_
    rw [←pow_add,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    change m^2+(head+(4*m^2+extra))≤_
    dsimp only [head,extra,u,q,L] at *
    omega
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open OrbitUp
private abbrev Sizes (m d σ : ℕ) := Fin (σ+1) × Fin (d+1) × Fin (m+1) × Fin (m+1)
private abbrev Entries (m d σ : ℕ) (v : Sizes m d σ) :=
  (Fin v.1.val → Fin (2^m)) × (Fin v.2.1.val → Fin (2^m)) ×
  (Fin v.1.val → V d) × (Fin σ → V d) × (Fin v.2.1.val → V d)
private abbrev Record (m d σ : ℕ) := (v : Sizes m d σ) × Entries m d σ v
private def record {m d σ : ℕ} (x : Shape m d σ) : Record m d σ :=
  ⟨(⟨x.r,by have := x.r_le;omega⟩,⟨x.n,by have := x.n_le;omega⟩,
    ⟨x.h,by have := x.ht_le;omega⟩,⟨x.t,by have := x.ht_le;omega⟩),
    x.rootOrder,x.extOrder,x.rootVec,x.baseVec,x.extVec⟩
private def readRecord {m d σ : ℕ} (v : Record m d σ) : Option (Shape m d σ) :=
  if hn : v.1.2.1.val+σ ≤ d then
    if ht : v.1.2.2.1.val+v.1.2.2.2.val ≤ m then
      some ⟨v.1.1.val,v.1.2.1.val,v.1.2.2.1.val,v.1.2.2.2.val,by have := v.1.1.isLt;omega,hn,ht,
        v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2.1,v.2.2.2.2.2⟩
    else none
  else none
private theorem read_record {m d σ : ℕ} (x : Shape m d σ) : readRecord (record x)=some x := by
  cases x with
  | mk r n h t hr hn ht a b c e f => simp [record,readRecord,hn,ht]
private theorem record_inj {m d σ : ℕ} : Function.Injective (@record m d σ) := by
  intro x y h
  exact Option.some.inj ((read_record x).symm.trans ((congrArg readRecord h).trans (read_record y)))
instance (m d σ : ℕ) : Finite (Shape m d σ) := Finite.of_injective record record_inj
theorem shape_size {m d σ : ℕ} (hs : σ ≤ d) (hd : d ≤ m) :
    Nat.card (Shape m d σ) ≤ 2^(10*m^2+10) := by
  classical
  have initial := Nat.card_le_card_of_injective (@record m d σ) record_inj
  apply initial.trans
  rw [Nat.card_sigma]
  have per (v : Sizes m d σ) : Nat.card (Entries m d σ v) ≤ 2^(5*m^2) := by
    have r : v.1.val ≤ m := by have := v.1.isLt;omega
    have n : v.2.1.val ≤ m := by have := v.2.1.isLt;omega
    have s := hs.trans hd
    simp only [Entries,Nat.card_prod,Nat.card_fun,Nat.card_fin,V,K,Nat.card_zmod,
      ←pow_mul,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [Nat.mul_le_mul (le_refl m) r,Nat.mul_le_mul (le_refl m) n,
      Nat.mul_le_mul hd r,Nat.mul_le_mul hd s,Nat.mul_le_mul hd n]
  apply (Finset.sum_le_sum (g:=fun _=>2^(5*m^2)) (fun v _=>per v)).trans
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul]
  have n : m+1 ≤ 2^m := Nat.lt_two_pow_self
  have b : Nat.card (Sizes m d σ) ≤ 2^(4*m) := by
    simp only [Sizes,Nat.card_prod,Nat.card_fin]
    calc
      _ ≤ 2^m*(2^m*(2^m*2^m)) := Nat.mul_le_mul ((Nat.add_le_add_right (hs.trans hd) 1).trans n)
        (Nat.mul_le_mul ((Nat.add_le_add_right hd 1).trans n) (Nat.mul_le_mul n n))
      _ = _ := by rw [←pow_add,←pow_add,←pow_add];congr 1;omega
  apply (Nat.mul_le_mul_right _ b).trans
  rw [←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.le_self_pow (by decide : 2≠0) m]
end Erdos1160.Sims
end
section
namespace Erdos1160.Sims
open OrbitUp.MinSpan GeneratorLocalization
open OrbitUp (V K)
theorem sims_profile_count {I:Type} [Finite I] {m d b σ} (E : I→FiniteGrp.{0})
    (frames : ∀i,∃(β:minimalAlternating d b σ) (S:Shape m d σ),Nonempty (SimsFrame S β.val (E i)))
    (hdb : d+b ≤ m) (hs : σ ≤ d) (hq : σ-1 ≤ b) (sep : ∀i j,Nonempty (E i≃*E j)→i=j) :
    Nat.card I ≤ 2^(profileExponent d b (m-d-b) (σ-1)+13*(m.sqrt+1)*m^2+19*m^2+19) := by
  classical
  letI : Finite (V d→ₗ[K]V b) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI : Finite (Tensor d b) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI : Finite (minimalAlternating d b σ) := inferInstanceAs (Finite (Subtype _))
  choose β S H using frames
  let key (i:I) : minimalAlternating d b σ × Shape m d σ := (β i,S i)
  let q := σ-1
  let u := m-d-b
  let P := d.choose 2*u+(q*b-q.choose 2)*u+q*u.choose 2+9*m^2
  have total := PresentationCount.card_le_of_fiber_bound key (2^P) (fun a=>by
    let F := {i:I // key i=a}
    have D (i:F) : SimsFrame a.2 a.1.val (E i.val) := by
      have eq := i.property
      have eb : β i.val=a.1 := congrArg Prod.fst eq
      have es : S i.val=a.2 := congrArg Prod.snd eq
      rw [←eb,←es];exact (H i.val).some
    exact sims_fixed_count (fun i:F=>E i.val) D hdb hq (fun i j e=>Subtype.ext (sep _ _ e)))
  have hd : d ≤ m := by omega
  have hb : b ≤ m := by omega
  rw [Nat.card_prod] at total
  refine total.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul (minspan_entropy hd hb) (shape_size hs hd))).trans ?_)
  rw [←pow_add,←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  dsimp [P,q,u,profileExponent]
  omega
end Erdos1160.Sims
end
section
namespace Erdos1160.GeneratorLocalization
open Filter
private theorem entropy_vanishes (C J : ℕ) : ∀ᶠ m:ℕ in atTop,
    J*(13*(m.sqrt+1)*m^2 + C*m^2 + C + 3*m) ≤ m^3 := by
  let B := J*(29+2*C)
  filter_upwards [eventually_ge_atTop (max 1 (B*B))] with m hm
  have h1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hs : 1 ≤ m.sqrt := Nat.le_sqrt.mpr h1
  have big : B ≤ m.sqrt := Nat.le_sqrt.mpr ((le_max_right _ _).trans hm)
  have self := (Nat.mul_le_mul_right m.sqrt big).trans (Nat.sqrt_le m)
  have cap := Nat.mul_le_mul_right (m^2) self
  have mq : 1 ≤ m^2 := Nat.one_le_pow _ _ h1
  have mq' : m ≤ m^2 := by nlinarith only [Nat.mul_le_mul_right m h1]
  have error : 13*(m.sqrt+1)*m^2 + C*m^2 + C + 3*m ≤ (29+2*C)*m.sqrt*m^2 := by
    have h := Nat.mul_le_mul_right (m^2) (Nat.mul_le_mul_left (16+2*C) hs)
    have c := Nat.mul_le_mul_left C mq
    nlinarith only [h,c,mq']
  have h := Nat.mul_le_mul_left J error
  dsimp [B] at cap
  nlinarith only [cap,h]
theorem offstrip_profile_sum (C : ℕ) :
    ∀ᶠ m:ℕ in atTop,
    ∀ {I : Type} [Fintype I] (f : I→ℕ),
      Fintype.card I≤(m+1)^3 →
      (∀i, f i=0 ∨ ∃d b u q, d+b+u=m ∧ q ≤ b ∧ q ≤ d ∧
        ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d) ∧
        f i ≤ 2^(profileExponent d b u q+13*(m.sqrt+1)*m^2+C*m^2+C)) →
      (∑i,f i)^(27*100000000)*2^(m^3) ≤ 2^(2*100000000*m^3) := by
  filter_upwards [entropy_vanishes C (27*100000000),eventually_ge_atTop 1] with m hm h1
  classical
  intro I _ f card price
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    obtain ⟨i,_,maxi⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    have size : ∑i,f i ≤ 2^(3*m)*f i := by
      have sum := Finset.sum_le_card_nsmul Finset.univ f (f i) maxi
      rw [Finset.card_univ,nsmul_eq_mul] at sum
      have bound := Nat.pow_le_pow_left (show m+1 ≤ 2^m from Nat.lt_two_pow_self) 3
      rw [←pow_mul,Nat.mul_comm m] at bound
      exact sum.trans (Nat.mul_le_mul_right _ (card.trans bound))
    rcases price i with zero|⟨d,b,u,q,total,qb,qd,out,pr⟩
    · rw [zero,Nat.mul_zero] at size
      simp [Nat.le_zero.mp size]
    · have single := offstrip_profile_cubic h1 total qb qd out
      have tot := size.trans (Nat.mul_le_mul_left _ pr)
      rw [←pow_add] at tot
      apply (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left tot _)).trans
      rw [←pow_mul,←pow_add]
      apply Nat.pow_le_pow_right (by decide)
      nlinarith only [single,hm]
end Erdos1160.GeneratorLocalization
end
section
namespace Erdos1160.Sims
open OuterExtensions Paper85 GeneratorLocalization Filter
private theorem rep_separates {m : ℕ} (a b : ClassOf (2^m)) (e : Nonempty (orderRep a ≃* orderRep b)) : a=b := by
  apply Subtype.ext
  rw [←a.property.choose_spec.2,←b.property.choose_spec.2]
  apply Quotient.sound
  exact ⟨CategoryTheory.InducedCategory.isoMk (F:=FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X:=(orderRep a).toGrp) (Y:=(orderRep b).toGrp) e.some)⟩
theorem su_xia_3_5 : ∀ᶠ m:ℕ in atTop,
    (Nat.card {c:ClassOf (2^m) // ¬inCentralStrip m (generatorRank c)})^(27*100000000) *
      2^(m^3) ≤ 2^(2*100000000*m^3) := by
  classical
  filter_upwards [offstrip_profile_sum 19] with m bound
  let I := {c:ClassOf (2^m) // ¬inCentralStrip m (generatorRank c)}
  let J := Fin (m+1) × Fin (m+1) × Fin (m+1)
  let d (i:I) := generatorRank i.val
  choose b σ db sd qb frames using fun i:I=>frame_coverage i.val
  let key (i:I) : J := (⟨d i,by have := db i;change d i+b i ≤ m at this;omega⟩,
    ⟨b i,by have := db i;omega⟩,⟨σ i,by have := sd i;have := db i;omega⟩)
  let C (j:J) := {i:I // key i=j}
  let f (j:J) := Nat.card (C j)
  have partition : Nat.card I=∑j:J,f j := by
    rw [←Nat.card_sigma]
    exact (Nat.card_congr (Equiv.sigmaFiberEquiv key)).symm
  change (Nat.card I)^_*_≤_
  rw [partition]
  apply bound f (by dsimp [J];simp [pow_succ,Nat.mul_assoc])
  intro j
  by_cases hj : Nonempty (C j)
  swap
  · left
    haveI : IsEmpty (C j) := not_nonempty_iff.mp hj
    exact Nat.card_of_isEmpty
  right
  let r := hj.some.val
  have parts (i:C j) : d i.val=d r ∧ b i.val=b r ∧ σ i.val=σ r := by
    have eq := i.property.trans hj.some.property.symm
    exact ⟨congrArg (fun k:J=>k.1.val) eq,congrArg (fun k:J=>k.2.1.val) eq,congrArg (fun k:J=>k.2.2.val) eq⟩
  have s : σ r ≤ d r := sd r
  have sum : d r+b r ≤ m := db r
  refine ⟨d r,b r,m-d r-b r,σ r-1,by omega,qb r,by omega,r.property,?_⟩
  let e := (Fintype.equivFin (C j)).symm
  change Nat.card (C j)≤_
  rw [←Nat.card_congr e]
  refine sims_profile_count (fun i=>orderRep (e i).val.val) ?_ sum s (qb r) ?_
  · intro i
    rw [←(parts (e i)).1,←(parts (e i)).2.1,←(parts (e i)).2.2]
    exact frames (e i).val
  · intro i k h
    exact e.injective (Subtype.ext (Subtype.ext (rep_separates _ _ h)))
end Erdos1160.Sims
end
namespace Erdos1160.Sims
open Filter OuterExtensions Paper85
theorem four_times_offstrip_count : ∀ᶠ m:ℕ in atTop, ∀ C : Set (ClassOf (2^m)),
    (∀c∈C,¬inCentralStrip m (generatorRank c)) →
    (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3) := by
  classical
  filter_upwards [su_xia_3_5,eventually_ge_atTop (100*100000000)] with m cap hm
  intro C hc
  let X := {c:ClassOf (2^m) // ¬inCentralStrip m (generatorRank c)}
  let emb : C→X := fun c=>⟨c.val,hc c.val c.property⟩
  have sub : C.ncard ≤ Nat.card X := by
    rw [←Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective emb (fun _ _ e=>Subtype.ext (congrArg (fun v:X=>v.val) e))
  have cost : (54+9*m^2)*100000000 ≤ m^3 := by
    have h1 : 1 ≤ m^2 := Nat.one_le_pow _ _ (by omega)
    have big := Nat.mul_le_mul_right (m^2) hm
    nlinarith only [h1,big]
  apply (Nat.pow_le_pow_iff_left (by decide : 100000000≠0)).mp
  calc
    _ = C.ncard^(27*100000000)*2^((54+9*m^2)*100000000) := by
      have z : (4*C.ncard)^27*2^(9*m^2) = C.ncard^27*2^(54+9*m^2) := by
        rw [mul_pow,pow_add]
        rw [Nat.mul_comm (4^27),Nat.mul_assoc]
        rfl
      rw [z,mul_pow,←pow_mul,←pow_mul]
    _ ≤ (Nat.card X)^(27*100000000)*2^(m^3) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left sub _) (Nat.pow_le_pow_right (by decide) cost)
    _ ≤ 2^(2*100000000*m^3) := cap
    _ = _ := by rw [←pow_mul];congr 1;ring
end Erdos1160.Sims
end PartUH4
namespace LargeSquareIndex
open Filter CategoryTheory Erdos1160
open Erdos1160.OuterExtensions Erdos1160.Paper85
open Erdos1160Growth.LowerTriangularUpper
lemma square_index_iso {G H : FiniteGrp.{0}} (e : G ≃* H) :
    (squareCore G).index = (squareCore H).index := by
  rw [← CentralKernelCount.squareCore_map e.toMonoidHom e.surjective]
  exact (Subgroup.index_map_of_bijective e.bijective (squareCore G)).symm
lemma rank_of_witness {k : ℕ} (c : ClassOf (2^k)) (G : FiniteGrp.{0})
    (hc : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G = c.val) :
    generatorRank c = Nat.log 2 (squareCore G).index := by
  have he : Nonempty (orderRep c ≅ G) :=
    Quotient.exact (c.property.choose_spec.2.trans hc.symm)
  let e : orderRep c ≃* G :=
    ((inducedFunctor FiniteGrp.toGrp).mapIso he.some).groupIsoToMulEquiv
  change Nat.log 2 (frattini (orderRep c)).index = _
  rw [frattini_eq_squareCore (rep_size c), square_index_iso e]
lemma outside_strip {k d : ℕ} (hk : 0 < k) (hd : 5*k ≤ 6*d) :
    ¬ inCentralStrip k d := by
  unfold inCentralStrip
  omega
lemma exp_growth {b : ℕ} (hb : 20 ≤ b) :
    27*(2*(b+2)+1) + 2*b^3 + 13*(b+2)^2 ≤ 2*(b+2)^3 + 9*b^2 := by
  nlinarith [Nat.mul_le_mul_left b hb]
lemma compare {b x y : ℕ} (hb : 20 ≤ b)
    (upper : x^27 * 2^(9*b^2) ≤ 2^(2*b^3))
    (lower : 2^(2*(b+2)^3) ≤ y^27 * 2^(13*(b+2)^2)) :
    2^(2*(b+2)+1)*x ≤ y := by
  apply (Nat.pow_le_pow_iff_left (by decide : 27 ≠ 0)).mp
  have hpos : 0 < 2^(9*b^2)*2^(13*(b+2)^2) := by positivity
  apply Nat.le_of_mul_le_mul_right (c := 2^(9*b^2)*2^(13*(b+2)^2)) _ hpos
  calc
    _ = 2^(27*(2*(b+2)+1)) * (x^27 * 2^(9*b^2)) * 2^(13*(b+2)^2) := by
      rw [mul_pow, ← pow_mul]; ring_nf
    _ ≤ 2^(27*(2*(b+2)+1)) * 2^(2*b^3) * 2^(13*(b+2)^2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ upper)
    _ = 2^(27*(2*(b+2)+1) + 2*b^3 + 13*(b+2)^2) := by rw [pow_add, pow_add]
    _ ≤ 2^(2*(b+2)^3 + 9*b^2) := Nat.pow_le_pow_right (by decide) (exp_growth hb)
    _ = 2^(2*(b+2)^3)*2^(9*b^2) := pow_add ..
    _ ≤ (y^27*2^(13*(b+2)^2))*2^(9*b^2) := Nat.mul_le_mul_right _ lower
    _ = _ := by ring
theorem solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R1.H1 := by
  classical
  obtain ⟨NU, hNU⟩ := eventually_atTop.mp Erdos1160.Sims.four_times_offstrip_count
  obtain ⟨NL, hNL⟩ := eventually_atTop.mp InlinedL.lower
  refine eventually_atTop.mpr ⟨NU+NL+22, fun m hm => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = b+2 := ⟨m-2, by omega⟩
  have hsub : b+2-2 = b := by omega
  rw [hsub]
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^b ∧
      5*b ≤ 6*Nat.log 2 (squareCore G).index}
  let C : Set (ClassOf (2^b)) := {c | c.val ∈ A}
  have hcard : C.ncard = A.ncard := by
    have himage : Subtype.val '' C = A := by
      ext q
      constructor
      · rintro ⟨c, hc, rfl⟩; exact hc
      · intro hq
        have horder : q ∈ Tables.orderClasses (2^b) := by
          obtain ⟨G, hG, he⟩ := hq
          exact ⟨G, hG.1, he⟩
        exact ⟨⟨q, horder⟩, hq, rfl⟩
    rw [← himage]
    exact (Set.ncard_image_of_injective C Subtype.val_injective).symm
  have hcount := hNU b (by omega) C (by
    intro c hc
    obtain ⟨G, hG, he⟩ := hc
    apply outside_strip (by omega : 0 < b)
    rw [rank_of_witness c G he]
    exact hG.2)
  rw [hcard] at hcount
  have hu : A.ncard^27 * 2^(9*b^2) ≤ 2^(2*b^3) := by
    apply (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (show A.ncard ≤ 4*A.ncard by omega) 27)).trans hcount
  exact compare (by omega) hu (hNL (b+2) (by omega))
end LargeSquareIndex
theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R1.H1 :=
  LargeSquareIndex.solution
