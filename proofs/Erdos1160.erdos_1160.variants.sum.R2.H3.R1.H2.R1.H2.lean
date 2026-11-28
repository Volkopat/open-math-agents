import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R1_H2_R1
-- Credit: @Thomassien
/-!
Reuses PR 7063 through PartUH2 (including PRs 393, 2283 and 2310) from open-math-agents (Apache-2.0).
The target is the corresponding independent hypothesis of the H2 reduction.
-/
section InlinedTargets
open Filter Erdos1160 CategoryTheory
open scoped commutatorElement
namespace InlinedL
def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop, 2 ^ (2 * m^3) ≤ g (2^m)^27 * 2 ^ (13 * m^2)
def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop, g (2^m)^27 * 2 ^ (9 * m^2) ≤ 2 ^ (2 * m^3)
end InlinedL
namespace InlinedU
def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)
def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    Nat.card F ≤ 2^192000*Nat.card K}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)
def H3 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ 2^192000*Nat.card K < Nat.card F ∧ (1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)
def H4 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)
lemma count_from_cover {X : Type*} (B C D E : Set X)
    (cover : ∀x, x∈B ∨ x∈C ∨ x∈D ∨ x∈E) :
    Nat.card X ≤ B.ncard+C.ncard+D.ncard+E.ncard := by
  classical
  by_cases h : Finite X
  · let _ := h
    have eq : Set.univ = (B∪C∪D∪E) := by
      ext x
      simpa only [Set.mem_univ,Set.mem_union,true_iff,or_assoc] using cover x
    rw [←Set.ncard_univ,eq]
    have a := Set.ncard_union_le (B∪C∪D) E
    have b := Set.ncard_union_le (B∪C) D
    have c := Set.ncard_union_le B C
    omega
  · let _ : Infinite X := not_finite_iff_infinite.mp h
    simp
lemma max_budget (a b c d n f z : ℕ) (h : n≤a+b+c+d)
    (ha : (4*a)^27*f≤z) (hb : (4*b)^27*f≤z)
    (hc : (4*c)^27*f≤z) (hd : (4*d)^27*f≤z) : n^27*f≤z := by
  let T := max (max a b) (max c d)
  have H : (4*T)^27*f≤z := by
    have hT : T=a ∨ T=b ∨ T=c ∨ T=d := by dsimp [T];omega
    rcases hT with e|e|e|e <;> rw [e] <;> assumption
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by dsimp [T];omega : n≤4*T) 27)).trans H
theorem main : H1 → H2 → H3 → H4 → InlinedL.H2 := by
  intro roots narrow wide outer
  filter_upwards [roots,narrow,wide,outer] with m hr hn hw ho
  classical
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let B : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    Nat.card F ≤ 2^192000*Nat.card K}
  let D : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ 2^192000*Nat.card K < Nat.card F ∧ (1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  let E : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  have cover (x : A) : x∈B ∨ x∈C ∨ x∈D ∨ x∈E := by
    dsimp only [B,C,D,E,Set.mem_ofPred_eq]
    let G := x.property.choose
    let F := Subgroup.closure (Set.range (fun y : G => y*y))
    let K := Subgroup.closure (Set.range (fun y : F => y.val*y.val) ∪ Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    by_cases root : K=⊥
    · exact .inl root
    · right
      by_cases small : Nat.card F ≤ 2^192000*Nat.card K
      · exact .inl small
      · right
        by_cases strip : (1000*(2*m-3*d)≤2*d ∧ 1000*(3*d-2*m)≤2*d)
        · exact .inl ⟨root,lt_of_not_ge small,strip⟩
        · exact .inr ⟨root,strip⟩
  exact max_budget _ _ _ _ _ _ _ (count_from_cover B C D E cover) hr hn hw ho
end InlinedU
end InlinedTargets
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
theorem InlinedU.solH1 : InlinedU.H1 := by
  classical
  apply Filter.eventually_atTop.mpr
  refine ⟨10000000, fun m hm => ?_⟩
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := squareCore G
    Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆)) = ⊥}
  change (4*C.ncard)^27 * 2^(9*m^2) ≤ _
  let target := frattiniOrderClasses m
  let _ : Finite target := (finite_frattiniOrderClasses m).to_subtype
  let f (c : C) : target := by
    let G := c.val.property.choose
    let F := squareCore G
    have spec := c.val.property.choose_spec
    have zero : Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆)) = ⊥ := c.property
    refine ⟨c.val.val,G,⟨spec.1,?_,?_⟩,spec.2⟩
    · rw [frattini_eq_squareCore spec.1]
      intro x hx
      apply Subgroup.mem_center_iff.mpr
      intro y
      have mem := Subgroup.subset_closure (k := Set.range (fun w : F => w.val*w.val) ∪
        Set.range (fun z : F × G => ⁅z.1.val,z.2⁆)) (Or.inr ⟨(⟨x,hx⟩,y),rfl⟩)
      rw [zero] at mem
      exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp mem)).symm
    · rw [frattini_eq_squareCore spec.1]
      intro x
      apply Subtype.ext
      have mem := Subgroup.subset_closure (k := Set.range (fun w : F => w.val*w.val) ∪
        Set.range (fun z : F × G => ⁅z.1.val,z.2⁆)) (Or.inl ⟨x,rfl⟩)
      rw [zero] at mem
      exact Subgroup.mem_bot.mp mem
  have hi : Function.Injective f := fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : target => z.val) h))
  have le := Nat.card_le_card_of_injective f hi
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at le
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left 4 le) 27)).trans (root_population_upper m hm)
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
theorem InlinedU.solH2 : InlinedU.H2 :=
  Erdos1160.DescendantTree.Actual.population_bound 192000
end PartUH2
namespace SmallSquareCombined
open Filter CategoryTheory Erdos1160
open scoped commutatorElement
lemma union_budget {a b c f z : ℕ} (hc : c ≤ a+b)
    (ha : (4*a)^27*f ≤ z) (hb : (4*b)^27*f ≤ z) :
    (2*c)^27*f ≤ z := by
  let T := max a b
  have ht : (4*T)^27*f ≤ z := by
    have he : T = a ∨ T = b := by dsimp [T]; omega
    rcases he with he | he <;> rw [he] <;> assumption
  exact (Nat.mul_le_mul_right f
    (Nat.pow_le_pow_left (show 2*c ≤ 4*T by dsimp [T]; omega) 27)).trans ht
theorem solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R1_H2_R1.H2 := by
  filter_upwards [InlinedU.solH1, InlinedU.solH2] with m hr hn
  classical
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let B : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    Nat.card F ≤ 2^192000*Nat.card K}
  let D : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥ ∨ Nat.card F ≤ 2^192000*Nat.card K}
  have he : D = B ∪ C := by
    ext c
    simp only [D, B, C, Set.mem_ofPred_eq, Set.mem_union]
  have hc : D.ncard ≤ B.ncard + C.ncard := by
    rw [he]
    exact Set.ncard_union_le B C
  exact union_budget hc hr hn
end SmallSquareCombined
theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R1_H2_R1.H2 :=
  SmallSquareCombined.solution
