import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1_H2_R1
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Tactic.Abel
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fin.Basic

/- Erdos1160Tables -/
section

/-! Relating the canonical count of group isomorphism classes to finite
multiplication tables modulo simultaneous relabeling of their entries. -/

namespace Erdos1160.Tables

open CategoryTheory

/-- The group isomorphism classes counted by the upstream function. -/
def orderClasses (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n}

/-- A labeled multiplication table which is realized by a group law. -/
def GroupTable (n : ℕ) :=
  { t : Fin n → Fin n → Fin n // ∃ s : Group (Fin n), s.mul = t }

instance {n : ℕ} : Finite (GroupTable n) := by
  unfold GroupTable
  infer_instance

/-- Bundle a labeled table as a finite group. -/
noncomputable abbrev model {n : ℕ} (t : GroupTable n) : FiniteGrp.{0} :=
  @FiniteGrp.of (Fin n) t.property.choose inferInstance

/-- Evaluate a product using the multiplication of the specified bundled group. -/
def product (G : FiniteGrp) (a b : G) : G := a * b

theorem model_mul {n : ℕ} (t : GroupTable n) (a b : Fin n) :
    product (model t) a b = t.val a b :=
  congrFun (congrFun t.property.choose_spec a) b

/-- The isomorphism class of a labeled table. -/
noncomputable def groupClass {n : ℕ} (t : GroupTable n) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (model t)

/-- A multiplication-preserving bijection gives an isomorphism in the category
of finite groups. -/
theorem iso_of_mul_equiv {G H : FiniteGrp} (e : G ≃ H)
    (h : ∀ a b, e (product G a b) = product H (e a) (e b)) : Nonempty (G ≅ H) := by
  let f : G ≃* H := { e with map_mul' := h }
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩

/-- Equality of the isomorphism classes is exactly simultaneous relabeling
of the two input positions and the output by one permutation. -/
theorem groupClass_eq_iff {n : ℕ} (s t : GroupTable n) :
    groupClass s = groupClass t ↔
      ∃ e : Equiv.Perm (Fin n), ∀ a b, e (s.val a b) = t.val (e a) (e b) := by
  constructor
  · intro h
    obtain ⟨i⟩ := Quotient.exact h
    let e := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv
    refine ⟨e.toEquiv, fun a b => ?_⟩
    have hmul (a b : model s) :
        e (product (model s) a b) = product (model t) (e a) (e b) := e.map_mul a b
    exact (congrArg (fun z => e z) (model_mul s a b)).symm.trans
      ((hmul a b).trans (model_mul t (e a) (e b)))
  · rintro ⟨e,h⟩
    apply Quotient.sound
    apply iso_of_mul_equiv e
    intro a b
    exact (congrArg (fun z => e z) (model_mul s a b)).trans
      ((h a b).trans (model_mul t (e a) (e b)).symm)

/-- Every group of order n can be labeled with the elements of Fin n. -/
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

/-- The kernel relation has the explicit relabeling description in
`groupClass_eq_iff`. -/
noncomputable def relabelSetoid (n : ℕ) : Setoid (GroupTable n) :=
  Setoid.ker (@groupClass n)

/-- Group isomorphism classes of order n are in bijection with group
multiplication tables on n labels up to relabeling. -/
noncomputable def tablesEquivClasses (n : ℕ) :
    Quotient (relabelSetoid n) ≃ orderClasses n :=
  (Setoid.quotientKerEquivRange (@groupClass n)).trans (Equiv.setCongr (range_groupClass n))

theorem g_eq_card_tables (n : ℕ) : Erdos1160.g n = Nat.card (Quotient (relabelSetoid n)) :=
  (Nat.card_congr (tablesEquivClasses n)).symm

/-- A coarse upper bound obtained by ignoring the group axioms and counting all
binary operations on the labeled carrier. -/
theorem g_le_table_count (n : ℕ) : Erdos1160.g n ≤ n ^ (n * n) := by
  rw [g_eq_card_tables]
  calc
    Nat.card (Quotient (relabelSetoid n)) ≤ Nat.card (GroupTable n) :=
      Nat.card_le_card_of_surjective _ Quotient.mk_surjective
    _ ≤ Nat.card (Fin n → Fin n → Fin n) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = n ^ (n * n) := by rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, pow_mul]

theorem orderClasses_finite (n : ℕ) : (orderClasses n).Finite := by
  rw [← range_groupClass]
  exact Set.finite_range _

theorem g_pos {n : ℕ} (hn : 0 < n) : 0 < Erdos1160.g n := by
  let : NeZero n := ⟨hn.ne'⟩
  let G := @FiniteGrp.of (Multiplicative (Fin n)) inferInstance (inferInstanceAs (Finite (Fin n)))
  change 0 < (orderClasses n).ncard
  exact ((Set.ncard_pos (orderClasses_finite n)).2
    ⟨Quotient.mk _ G, G, Nat.card_fin n, rfl⟩)

end Erdos1160.Tables

end

/- DirectFactorExchange -/
section

namespace Erdos1160.DirectFactors

open Function

/-- A finite monoid element has an idempotent positive power. -/
theorem idempotent_power {M : Type*} [Monoid M] [Finite M] (x : M) :
    ∃ n : ℕ, 0 < n ∧ x^(n+n) = x^n := by
  obtain ⟨i,j,hij,he⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun k : ℕ => x^k) (fun _ => Set.mem_univ _)
  let d := j-i
  have hd : 0 < d := by dsimp [d]; omega
  have hp : x^i * x^d = x^i := by
    rw [← pow_add, show i+d=j by dsimp [d]; omega]
    exact he.symm
  have periodic (k : ℕ) : x^i * x^(d*k) = x^i := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, ← mul_assoc, ih, hp]
  let n := d*(i+1)
  have hi : i ≤ n := by
    dsimp [n]
    have := Nat.mul_le_mul_right (i+1) hd
    omega
  refine ⟨n, Nat.mul_pos hd (Nat.succ_pos _), ?_⟩
  calc
    x^(n+n) = x^(n-i) * (x^i * x^n) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hi, ← pow_add]
    _ = x^n := by rw [show x^i*x^n=x^i from periodic (i+1), ← pow_add, Nat.sub_add_cancel hi]

/-- A directly indecomposable finite group has no decomposition with two
nontrivial group factors. -/
def Indecomp (A : Type) [Group A] : Prop :=
  ∀ (B C : Type) [Group B] [Group C] [Finite B] [Finite C],
    (A ≃* B × C) → Subsingleton B ∨ Subsingleton C

private def multiply {A B C : Type*} [Group A] [Group B] [Group C]
    (u : A →* C) (v : B →* C) (h : ∀ a b, Commute (u a) (v b)) : A × B →* C where
  toFun x := u x.1 * v x.2
  map_one' := by simp
  map_mul' x y := by
    change u (x.1*y.1) * v (x.2*y.2) = (u x.1*v x.2)*(u y.1*v y.2)
    rw [map_mul, map_mul, mul_assoc, ← mul_assoc (u y.1), (h y.1 x.2).eq]
    simp only [mul_assoc]

private theorem bijective_split {A B : Type*} [Group A] [Group B]
    (p : A →* B) (s : B →* A) (hs : ∀ b, p (s b) = b)
    (hc : ∀ b (k : p.ker), Commute (s b) k.val) :
    Bijective (multiply s p.ker.subtype hc) := by
  constructor
  · apply (injective_iff_map_eq_one _).mpr
    rintro ⟨b,k⟩ hk
    change s b * k.val = 1 at hk
    have hb := congrArg p hk
    rw [map_mul, hs, k.property, mul_one, map_one] at hb
    subst b
    simpa using hk
  · intro a
    refine ⟨⟨p a, ⟨(s (p a))⁻¹*a, ?_⟩⟩, ?_⟩
    · change p ((s (p a))⁻¹*a) = 1
      simp [hs]
    · change s (p a) * ((s (p a))⁻¹ * a) = a
      simp

private def normalMap {A : Type} [Group A] (f : Monoid.End A) : Prop :=
  ∀ a x, f (a*x*a⁻¹) = a*f x*a⁻¹

private theorem normal_pow {A : Type} [Group A] {f : Monoid.End A}
    (hf : normalMap f) (n : ℕ) : normalMap (f^n) := by
  induction n with
  | zero => intro a x; rfl
  | succ n ih =>
    intro a x
    rw [pow_succ]
    change (f^n) (f (a*x*a⁻¹)) = a * (f^n) (f x) * a⁻¹
    rw [hf, ih]

/-- Fitting's dichotomy for a normal endomorphism on a finite directly
indecomposable group. The power is taken under composition. -/
private theorem normal_dichotomy {A : Type} [Group A] [Finite A]
    (hA : Indecomp A) (f : Monoid.End A) (hf : normalMap f) :
    Bijective f ∨ ∃ n : ℕ, 0 < n ∧ ∀ x, (f^n) x = 1 := by
  classical
  letI : Finite (Monoid.End A) := Finite.of_injective _ (DFunLike.coe_injective :
    Injective (fun z : Monoid.End A => (z : A → A)))
  obtain ⟨n,hn,hh⟩ := idempotent_power f
  let e := f^n
  have idem (x : A) : e (e x) = e x := by
    rw [pow_add] at hh
    exact DFunLike.congr_fun hh x
  let p := e.rangeRestrict
  let s := e.range.subtype
  have hs (b : e.range) : p (s b) = b := by
    apply Subtype.ext
    obtain ⟨x,hx⟩ := b.property
    change e b.val = b.val
    rw [← hx]
    exact idem x
  have hc (b : e.range) (k : p.ker) : Commute (s b) k.val := by
    obtain ⟨x,hx⟩ := b.property
    have hk : e k.val = 1 := congrArg Subtype.val k.property
    have h := normal_pow hf n k.val x
    change e (k.val*x*k.val⁻¹) = k.val*e x*k.val⁻¹ at h
    rw [map_mul, map_mul, map_inv, hk, one_mul, inv_one, mul_one] at h
    change b.val * k.val = k.val * b.val
    rw [← hx]
    exact (eq_mul_inv_iff_mul_eq.mp h)
  let iso := MulEquiv.ofBijective _ (bijective_split p s hs hc)
  rcases hA _ _ iso.symm with h | h
  · right
    exact ⟨n,hn,fun x => congrArg Subtype.val (@Subsingleton.elim _ h (p x) 1)⟩
  · left
    have he : Injective p := (injective_iff_map_eq_one _).mpr fun x hx =>
      congrArg Subtype.val (@Subsingleton.elim _ h (⟨x,hx⟩ : p.ker) 1)
    apply (Finite.injective_iff_bijective).mp
    intro x y hxy
    apply he
    apply Subtype.ext
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    change (f^n) x = (f^n) y
    rw [hk,pow_succ]
    exact congrArg (f^k) hxy

section Exchange

variable {A B H K : Type} [Group A] [Group B] [Group H] [Group K]

private def leftIn (e : A × B ≃* H × K) : A →* H :=
  (MonoidHom.fst H K).comp (e.toMonoidHom.comp (MonoidHom.inl A B))

private def leftOut (e : A × B ≃* H × K) : H →* A := leftIn e.symm

private def component (e : A × B ≃* H × K) : Monoid.End A := (leftOut e).comp (leftIn e)

private theorem component_normal (e : A × B ≃* H × K) : normalMap (component e) := by
  intro a x
  let u := e (a,1)
  let v := e (x,1)
  have conj : e (a*x*a⁻¹,1) = u*v*u⁻¹ := by
    change e (a*x*a⁻¹,1) = e (a,1)*e (x,1)*(e (a,1))⁻¹
    rw [←map_inv, ←map_mul, ←map_mul]
    simp
  have proj : ((u*v*u⁻¹).1, (1:K)) = u * (v.1,1) * u⁻¹ := by ext <;> simp
  change (e.symm ((e (a*x*a⁻¹,1)).1,1)).1 = a*(e.symm (v.1,1)).1*a⁻¹
  rw [conj, proj, map_mul, map_mul, map_inv]
  simp [u]

private theorem component_choice [Finite A] (ha : Indecomp A)
    (e : A × B ≃* H × K) :
    Bijective (component e) ∨ Bijective (component (e.trans (MulEquiv.prodComm (M:=H) (N:=K)))) := by
  let f := component e
  let g := component (e.trans (MulEquiv.prodComm (M:=H) (N:=K)))
  have split (x : A) : f x * g x = x := by
    change (e.symm ((e (x,1)).1,1)).1 * (e.symm (1,(e (x,1)).2)).1 = x
    rw [← Prod.fst_mul, ← map_mul]
    simp
  rcases normal_dichotomy ha f (component_normal e) with h | ⟨n,hn,h⟩
  · exact Or.inl h
  · right
    apply Finite.injective_iff_bijective.mp
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have fix : f x = x := by simpa only [show g x = 1 from hx,mul_one] using split x
    have iter (k : ℕ) : (f^k) x = x := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ]
        change (f^k) (f x) = x
        rw [fix, ih]
    exact (iter n).symm.trans (h x)

/-- If the projection through the first factor is invertible, that factor
absorbs the indecomposable group and the complementary factors can be read
off from the kernel of the opposite projection. -/
private theorem exchange_left (e : A × B ≃* H × K) (hf : Bijective (component e)) :
    ∃ (T : Subgroup H), Nonempty (H ≃* A × T) ∧ Nonempty (B ≃* T × K) := by
  let p := leftOut e
  let i := leftIn e
  let f := MulEquiv.ofBijective (component e) hf
  let s := i.comp f.symm.toMonoidHom
  have hs (a : A) : p (s a) = a := f.apply_symm_apply a
  have hc (a : A) (k : p.ker) : Commute (s a) k.val := by
    have hk : (e.symm (k.val,1)).1 = 1 := k.property
    have cs : Commute (f.symm a,(1:B)) (e.symm (k.val,1)) := by
      change (_,_) * _ = _ * (_,_)
      ext <;> simp [hk]
    have hc' := (cs.map e.toMonoidHom).map (MonoidHom.fst H K)
    simpa [s, i, leftIn] using hc'
  refine ⟨p.ker, ⟨(MulEquiv.ofBijective _ (bijective_split p s hs hc)).symm⟩, ?_⟩
  let w : p.ker × K →* B := (MonoidHom.snd A B).comp
    (e.symm.toMonoidHom.comp (p.ker.subtype.prodMap (MonoidHom.id K)))
  have inj : Injective w := by
    apply (injective_iff_map_eq_one _).mpr
    rintro ⟨h,k⟩ hk
    change (e.symm (h.val,k)).2 = 1 at hk
    let a := (e.symm (h.val,k)).1
    have ea : e (a,1) = (h.val,k) := by
      apply e.symm.injective
      rw [e.symm_apply_apply]
      exact Prod.ext rfl hk.symm
    have fa : f a = 1 := by
      change p (e (a,1)).1 = 1
      rw [ea]
      exact h.property
    have ha : a = 1 := f.injective (fa.trans f.map_one.symm)
    rw [ha, show ((1,1) : A × B) = 1 from rfl, map_one] at ea
    exact Prod.ext (Subtype.ext (congrArg Prod.fst ea.symm)) (congrArg (Prod.snd (α:=H)) ea.symm)
  have sur : Surjective w := by
    intro b
    let v := e (1,b)
    let a := f.symm (p v.1)
    let z := e (a,1)
    have hz : p z.1 = p v.1 := f.apply_symm_apply _
    refine ⟨⟨⟨(z⁻¹*v).1, ?_⟩,(z⁻¹*v).2⟩, ?_⟩
    · change p (z.1⁻¹*v.1) = 1
      simp [hz]
    · change (e.symm (z⁻¹*v)).2 = b
      simp [z,v]
  exact ⟨(MulEquiv.ofBijective w ⟨inj,sur⟩).symm⟩

/-- Exchange an indecomposable factor into one side of a second binary
decomposition and decompose its original complement at the same time. -/
theorem exchange [Finite A] (ha : Indecomp A) (e : A × B ≃* H × K) :
    (∃ T : Subgroup H, Nonempty (H ≃* A × T) ∧ Nonempty (B ≃* T × K)) ∨
    (∃ T : Subgroup K, Nonempty (K ≃* A × T) ∧ Nonempty (B ≃* H × T)) := by
  rcases component_choice ha e with l | r
  · exact Or.inl (exchange_left e l)
  · obtain ⟨T,h,⟨b⟩⟩ := exchange_left (e.trans (MulEquiv.prodComm (M:=H) (N:=K))) r
    exact Or.inr ⟨T,h,⟨b.trans MulEquiv.prodComm⟩⟩

end Exchange

open CategoryTheory Tables

abbrev Class := Quotient (isIsomorphicSetoid FiniteGrp.{0})
private abbrev cl (A : FiniteGrp.{0}) : Class := Quotient.mk _ A
private abbrev prodGrp (A B : FiniteGrp.{0}) := FiniteGrp.of (A × B)

private theorem cl_congr {A B : FiniteGrp.{0}} (e : A ≃* B) : cl A = cl B :=
  Quotient.sound ⟨InducedCategory.isoMk (F:=FiniteGrp.toGrp) e.toGrpIso⟩

private noncomputable def equivOfEq {A B : FiniteGrp.{0}} (h : cl A = cl B) : A ≃* B :=
  ((inducedFunctor FiniteGrp.toGrp).mapIso (Quotient.exact h).some).groupIsoToMulEquiv

private def attach (A : FiniteGrp.{0}) : Class → Class :=
  Quotient.map (prodGrp A) (by
    rintro B C ⟨e⟩
    apply Quotient.exact
    exact cl_congr ((MulEquiv.refl A).prodCongr
      ((inducedFunctor FiniteGrp.toGrp).mapIso e).groupIsoToMulEquiv))

/-- The ordered pairs of isomorphism types whose direct product has type G. -/
def pairs (G : FiniteGrp.{0}) : Set (Class × Class) :=
  {p | ∃ H K : FiniteGrp.{0}, p = (cl H,cl K) ∧ Nonempty (G ≃* H × K)}

private theorem cover {G A B : FiniteGrp.{0}} (e : G ≃* A × B) (ha : Indecomp A) :
    pairs G ⊆ (fun p : Class × Class => (attach A p.1,p.2)) '' pairs B ∪
      (fun p : Class × Class => (p.1,attach A p.2)) '' pairs B := by
  rintro _ ⟨H,K,rfl,⟨v⟩⟩
  rcases exchange ha (e.symm.trans v) with ⟨T,⟨h⟩,⟨b⟩⟩ | ⟨T,⟨h⟩,⟨b⟩⟩
  · let F := FiniteGrp.of T
    exact Or.inl ⟨(cl F,cl K),⟨F,K,rfl,⟨b⟩⟩,Prod.ext (cl_congr h.symm) rfl⟩
  · let F := FiniteGrp.of T
    exact Or.inr ⟨(cl H,cl F),⟨H,F,rfl,⟨b⟩⟩,Prod.ext rfl (cl_congr h.symm)⟩

private theorem atom (G : FiniteGrp.{0}) (hg : 1 < Nat.card G) :
    ∃ A B : FiniteGrp.{0}, Indecomp A ∧ 1 < Nat.card A ∧ Nonempty (G ≃* A × B) := by
  classical
  by_cases h : Indecomp G
  · let e : G × PUnit ≃* G := MulEquiv.prodUnique
    exact ⟨G,FiniteGrp.of PUnit,h,hg,⟨e.symm⟩⟩
  · unfold Indecomp at h
    push Not at h
    obtain ⟨X,Y,gx,gy,fx,fy,e,nx,ny⟩ := h
    let _ := gx
    let _ := gy
    let _ := fx
    let _ := fy
    have hx : 1 < Nat.card X := by
      have hn : Nat.card X ≠ 1 := fun h => not_subsingleton X (Nat.card_eq_one_iff_unique.mp h).1
      have := Nat.card_pos (α:=X)
      omega
    have hy : 1 < Nat.card Y := by
      have hn : Nat.card Y ≠ 1 := fun h => not_subsingleton Y (Nat.card_eq_one_iff_unique.mp h).1
      have := Nat.card_pos (α:=Y)
      omega
    have hc : Nat.card G = Nat.card X * Nat.card Y :=
      (Nat.card_congr e.toEquiv).trans (Nat.card_prod _ _)
    obtain ⟨A,B,ha,hcard,⟨u⟩⟩ := atom (FiniteGrp.of X) hx
    exact ⟨A,prodGrp B (FiniteGrp.of Y),ha,hcard,
      ⟨(e.trans (u.prodCongr (MulEquiv.refl Y))).trans MulEquiv.prodAssoc⟩⟩
termination_by Nat.card G
decreasing_by change Nat.card X < Nat.card G; rw [hc]; nlinarith

private theorem trivialClass {G : FiniteGrp.{0}} (h : Nat.card G = 1) :
    cl G = cl (FiniteGrp.of PUnit) := by
  haveI := (Nat.card_eq_one_iff_unique.mp h).1
  letI : Unique G := uniqueOfSubsingleton 1
  let e : G ≃ PUnit := Equiv.ofUnique G PUnit
  exact cl_congr (B:=FiniteGrp.of PUnit) { e with map_mul' := fun _ _ => rfl }

/-- All ordered direct product decompositions, up to isomorphism of the
two factors, have total count at most the order of the original group. -/
theorem pairs_count (G : FiniteGrp.{0}) :
    (pairs G).Finite ∧ (pairs G).ncard ≤ Nat.card G := by
  classical
  by_cases hg : 1 < Nat.card G
  · obtain ⟨A,B,ha,hA,⟨e⟩⟩ := atom G hg
    have hc : Nat.card G = Nat.card A * Nat.card B :=
      (Nat.card_congr e.toEquiv).trans (Nat.card_prod _ _)
    obtain ⟨fin,cnt⟩ := pairs_count B
    have ff := (fin.image (fun p : Class × Class => (attach A p.1,p.2))).union
      (fin.image (fun p : Class × Class => (p.1,attach A p.2)))
    refine ⟨ff.subset (cover e ha), ?_⟩
    apply (Set.ncard_le_ncard (cover e ha) ff).trans
    apply (Set.ncard_union_le _ _).trans
    have hh := Nat.add_le_add (Set.ncard_image_le (s:=pairs B)
      (f:=fun p => (attach A p.1,p.2)) fin) (Set.ncard_image_le (s:=pairs B)
      (f:=fun p => (p.1,attach A p.2)) fin)
    exact hh.trans (by rw [hc]; nlinarith)
  · have pos : 0 < Nat.card G := Nat.card_pos
    let t := cl (FiniteGrp.of PUnit)
    have sub : pairs G ⊆ ({(t,t)} : Set (Class × Class)) := by
      rintro _ ⟨H,K,rfl,⟨v⟩⟩
      have h : Nat.card G = Nat.card H * Nat.card K :=
        (Nat.card_congr v.toEquiv).trans (Nat.card_prod _ _)
      have eq : Nat.card H * Nat.card K = 1 := by omega
      have hH := Nat.eq_one_of_mul_eq_one_right eq
      have hK : Nat.card K = 1 := by simpa [hH] using eq
      exact Prod.ext (trivialClass hH) (trivialClass hK)
    exact ⟨(Set.finite_singleton _).subset sub,
      (Set.ncard_le_ncard sub (Set.finite_singleton _)).trans (by simp; omega)⟩
termination_by Nat.card G
decreasing_by rw [hc]; have := Nat.card_pos (α:=B); nlinarith


/-- Uniform product estimate for the number of finite groups. -/
theorem product_count (a b : ℕ) : g a * g b ≤ (a*b) * g (a*b) := by
  classical
  let F := (orderClasses_finite (a*b)).toFinset
  let S (c : Class) := pairs c.out
  have mem (c : Class) : c ∈ F ↔ c ∈ orderClasses (a*b) := Set.Finite.mem_toFinset _
  have sub : orderClasses a ×ˢ orderClasses b ⊆ ⋃ c ∈ F, S c := by
    rintro ⟨x,y⟩ ⟨⟨H,hH,rfl⟩,⟨K,hK,rfl⟩⟩
    let G := prodGrp H K
    have card : Nat.card G = a*b := (Nat.card_prod H K).trans (congrArg₂ (·*·) hH hK)
    refine Set.mem_iUnion.mpr ⟨cl G,Set.mem_iUnion.mpr ⟨(mem _).mpr ⟨G,card,rfl⟩, ?_⟩⟩
    exact ⟨H,K,rfl,⟨equivOfEq (Quotient.out_eq (cl G))⟩⟩
  have fin : (⋃ c ∈ F, S c).Finite :=
    F.finite_toSet.biUnion (fun c _ => (pairs_count c.out).1)
  have H : ∀ c ∈ F, (S c).ncard ≤ a*b := by
    intro c hc
    obtain ⟨G,hG,e⟩ := (mem c).mp hc
    have h := Nat.card_congr (equivOfEq (c.out_eq.trans e.symm)).toEquiv
    exact (pairs_count c.out).2.trans (h.trans hG).le
  calc
    g a * g b = (orderClasses a ×ˢ orderClasses b).ncard := Set.ncard_prod.symm
    _ ≤ _ := Set.ncard_le_ncard sub fin
    _ ≤ ∑ c ∈ F, (S c).ncard := F.set_ncard_biUnion_le S
    _ ≤ ∑ _c ∈ F, a*b := Finset.sum_le_sum H
    _ = (a*b)*g (a*b) := by
      have hf : F.card = g (a*b) := (Set.ncard_eq_toFinset_card _ (orderClasses_finite (a*b))).symm
      simp [hf,Nat.mul_comm]


end Erdos1160.DirectFactors

end

/- NilpotentCounts -/
section

/-! Bounds for isomorphism classes of nilpotent groups via their Sylow subgroups. -/

open CategoryTheory
open scoped BigOperators

namespace Erdos1160.NilpotentCounts
open Erdos1160.Tables

/-- An abstract Sylow profile records one isomorphism class for each prime dividing the order. -/
abbrev Profile (n : ℕ) := ∀ p : n.primeFactors, orderClasses (p.val ^ n.factorization p.val)

def nilpotentClasses (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsNilpotent G}

noncomputable def rep {k : ℕ} (c : orderClasses k) : FiniteGrp.{0} :=
  Classical.choose c.property

theorem rep_class {k : ℕ} (c : orderClasses k) :
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep c) = c.val :=
  (Classical.choose_spec c.property).2

theorem rep_card {k : ℕ} (c : orderClasses k) : Nat.card (rep c) = k :=
  (Classical.choose_spec c.property).1

noncomputable def realize {n : ℕ} (x : Profile n) : FiniteGrp.{0} :=
  FiniteGrp.of (∀ p, rep (x p))

noncomputable def realizeClass {n : ℕ} (x : Profile n) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) := Quotient.mk _ (realize x)

noncomputable def sylowProfile (G : FiniteGrp.{0}) : Profile (Nat.card G) := by
  intro p
  letI : Fact (Nat.Prime p.val) := ⟨Nat.prime_of_mem_primeFactors p.property⟩
  let P : Sylow p.val G := default
  exact ⟨Quotient.mk _ (FiniteGrp.of P), FiniteGrp.of P, P.card_eq_multiplicity, rfl⟩

theorem realize_sylowProfile (G : FiniteGrp.{0}) [Group.IsNilpotent G] :
    realizeClass (sylowProfile G) = Quotient.mk _ G := by
  apply Quotient.sound
  let E : (∀ p : (Nat.card G).primeFactors,
      ∀ P : Sylow p.val G, P) ≃* G := Sylow.directProductOfNormal fun _ => inferInstance
  let L (p : (Nat.card G).primeFactors) :
      (∀ P : Sylow p.val G, P) ≃* rep (sylowProfile G p) := by
    letI : Fact (Nat.Prime p.val) := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    let P : Sylow p.val G := default
    have h : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep (sylowProfile G p)) =
        Quotient.mk _ (FiniteGrp.of P) := rep_class _
    let i := Classical.choice (Quotient.exact h)
    let e := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv
    letI : Unique (Sylow p.val G) := Sylow.unique_of_normal P inferInstance
    exact (MulEquiv.piUnique (fun Q : Sylow p.val G => Q)).trans e.symm
  let e : realize (sylowProfile G) ≃* G := (MulEquiv.piCongrRight L).symm.trans E
  exact iso_of_mul_equiv e.toEquiv e.map_mul

theorem classes_subset_range (n : ℕ) :
    nilpotentClasses n ⊆ Set.range (@realizeClass n) := by
  rintro _ ⟨G, ⟨rfl,h⟩,rfl⟩
  letI := h
  exact ⟨sylowProfile G, realize_sylowProfile G⟩

instance profilesFinite (n : ℕ) : Finite (Profile n) := by
  letI (p : n.primeFactors) : Finite (orderClasses (p.val ^ n.factorization p.val)) :=
    (orderClasses_finite _).to_subtype
  unfold Profile
  infer_instance

/-- The nilpotent contribution at a fixed order is bounded by the product of the
numbers of groups of its prime-power orders. -/
theorem nilpotent_ncard_le (n : ℕ) :
    (nilpotentClasses n).ncard ≤ ∏ p ∈ n.primeFactors, g (p ^ n.factorization p) := by
  calc
    _ ≤ (Set.range (@realizeClass n)).ncard :=
      Set.ncard_le_ncard (classes_subset_range n) (Set.finite_range _)
    _ ≤ Nat.card (Profile n) := Nat.card_le_card_of_surjective (Set.rangeFactorization _) Set.rangeFactorization_surjective
    _ = ∏ p : n.primeFactors, g (p.val ^ n.factorization p.val) := by
      rw [Nat.card_pi]
      rfl
    _ = _ := Finset.prod_finset_coe (fun p => g (p ^ n.factorization p)) n.primeFactors

end Erdos1160.NilpotentCounts

end

/- LiftPresentations -/
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

theorem card_lift (R : J → FreeGroup I) (c : J → Fin p) [Finite (Grp R)] (hp : 0 < p) :
    Nat.card (Lift R c) ≤ Nat.card (Grp R) * p := by
  let N := Subgroup.zpowers (z R c)
  have hc : Nat.card N ≤ p := by
    rw [show Nat.card N = orderOf (z R c) from Nat.card_zpowers _]
    exact Nat.le_of_dvd hp (orderOf_dvd_iff_pow_eq_one.mpr (z_pow R c))
  rw [Nat.card_congr (Subgroup.groupEquivQuotientProdSubgroup (s := N)), Nat.card_prod]
  exact Nat.mul_le_mul (Nat.card_le_card_of_surjective (quotientMap R c) (quotientMap_surjective R c)) hc

theorem finite_lift (R : J → FreeGroup I) (c : J → Fin p) [Finite (Grp R)] (hp : 0 < p) :
    Finite (Lift R c) := by
  let N := Subgroup.zpowers (z R c)
  have hd := orderOf_dvd_iff_pow_eq_one.mpr (z_pow R c)
  let : Finite N := Nat.finite_of_card_ne_zero (by rw [show Nat.card N = orderOf (z R c) from Nat.card_zpowers _]; exact fun e => by simp [e] at hd; omega)
  let : Finite (Lift R c ⧸ N) := Finite.of_surjective (quotientMap R c) (quotientMap_surjective R c)
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := N)).symm

end Erdos1160.CentralLifts

end

/- RealizeLift -/
section

namespace Erdos1160.CentralLifts

open scoped commutatorElement

variable {I J : Type} {p : ℕ}

theorem lift_surjection {U Q : Type} [Group U] [Group Q] [Finite U]
    (R : J → FreeGroup I) (q : U →* Q) (hq : Function.Surjective q)
    (u : U) (hu : orderOf u = p) (hcenter : u ∈ Subgroup.center U)
    (hker : q.ker = Subgroup.zpowers u) (e : Grp R →* Q) (he : Function.Surjective e) :
    ∃ c : J → Fin p, ∃ f : Lift R c →* U, Function.Surjective f := by
  classical
  choose x hx using (fun i : I => hq (e (PresentedGroup.of i)))
  let X := FreeGroup.lift x
  have hqX : q.comp X = e.comp (PresentedGroup.mk (Set.range R)) :=
    FreeGroup.ext_hom _ _ (fun i => by simpa [X, PresentedGroup.of] using hx i)
  have hrel (j : J) : X (R j) ∈ Subgroup.zpowers u := by
    rw [← hker, MonoidHom.mem_ker]
    change (q.comp X) (R j) = 1
    rw [hqX, MonoidHom.comp_apply, relation, map_one]
  have existsTwist (j : J) : ∃ t : Fin p, X (R j) = u ^ t.val := by
    have h := (isOfFinOrder_of_finite u).mem_zpowers_iff_mem_range_orderOf.mp (hrel j)
    obtain ⟨k,hk,heq⟩ := Finset.mem_image.mp h
    exact ⟨⟨k,hu ▸ Finset.mem_range.mp hk⟩,heq.symm⟩
  choose c hc using existsTwist
  let y : Option I → U := fun o => o.elim u x
  let Y := FreeGroup.lift y
  have hu1 : Y (FreeGroup.of none) = u := by simp [Y,y]
  have hxi (i : I) : Y (FreeGroup.of (some i)) = x i := by simp [Y,y]
  have hXY : Y.comp (FreeGroup.map some) = X := FreeGroup.ext_hom _ _ (fun i => by simp [Y,X,y])
  have rels : ∀ w ∈ Set.range (newRel R c), Y w = 1 := by
    rintro w ⟨(_ | (i | j)),rfl⟩
    · simpa only [newRel, map_pow, hu1, ← hu] using pow_orderOf_eq_one u
    · rw [newRel, map_commutatorElement, hu1, hxi, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hcenter _).symm
    · simp only [newRel,map_mul,map_inv,map_pow,hu1]
      change (Y.comp (FreeGroup.map some)) (R j) * (u ^ (c j).val)⁻¹ = 1
      rw [hXY,hc,mul_inv_cancel]
  let f : Lift R c →* U := PresentedGroup.toGroup rels
  have fgen (i : Option I) : f (PresentedGroup.of i) = y i := PresentedGroup.toGroup.of rels
  have hcomp : (q.comp f).comp (inc R c) = e.comp (PresentedGroup.mk (Set.range R)) := by
    apply FreeGroup.ext_hom
    intro i
    change q (f (PresentedGroup.of (some i))) = e (PresentedGroup.of i)
    rw [fgen]
    exact hx i
  refine ⟨c,f,?_⟩
  have uin : u ∈ f.range := ⟨PresentedGroup.of none, fgen none⟩
  have kernel : q.ker ≤ f.range := hker ▸ (Subgroup.zpowers_le.mpr uin)
  intro a
  obtain ⟨b,hb⟩ := he (q a)
  obtain ⟨w,rfl⟩ := PresentedGroup.mk_surjective (Set.range R) b
  let v := inc R c w
  have qv : q (f v) = q a := (DFunLike.congr_fun hcomp w).trans hb
  have ha : a * (f v)⁻¹ ∈ q.ker := by rw [MonoidHom.mem_ker,map_mul,map_inv,qv,mul_inv_cancel]
  obtain ⟨r,hr⟩ := kernel ha
  exact ⟨r*v,by rw [map_mul,hr,inv_mul_cancel_right]⟩

theorem exists_central_prime {p k : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (h : Nat.card G = p^(k+1)) :
    ∃ u : G, u ∈ Subgroup.center G ∧ orderOf u = p := by
  obtain ⟨j,hj,hz⟩ := IsPGroup.card_center_eq_prime_pow h (by omega)
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) p
    (hz ▸ (dvd_pow_self _ (Nat.ne_of_gt hj)))
  exact ⟨t.val,t.property,(Subgroup.orderOf_coe t).trans ht⟩

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

/- LiftCodes -/
section

namespace Erdos1160.CentralLifts

def Gen : ℕ → Type
  | 0 => Empty
  | k + 1 => Option (Gen k)

def Rel : ℕ → Type
  | 0 => Empty
  | k + 1 => Unit ⊕ (Gen k ⊕ Rel k)

def Codes (p : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Codes p k × (Rel k → Fin p)

def relations {p : ℕ} : {k : ℕ} → Codes p k → Rel k → FreeGroup (Gen k)
  | 0, _, r => nomatch r
  | k + 1, c, r => newRel (relations (k := k) c.1) c.2 r

instance genFinite (k : ℕ) : Finite (Gen k) := by
  induction k with
  | zero => exact inferInstanceAs (Finite Empty)
  | succ k ih => exact inferInstanceAs (Finite (Option (Gen k)))

instance relFinite (k : ℕ) : Finite (Rel k) := by
  induction k with
  | zero => exact inferInstanceAs (Finite Empty)
  | succ k ih => exact inferInstanceAs (Finite (Unit ⊕ (Gen k ⊕ Rel k)))

instance codeFinite (p k : ℕ) : Finite (Codes p k) := by
  induction k with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ k ih => exact inferInstanceAs (Finite (Codes p k × (Rel k → Fin p)))

theorem card_gen (k : ℕ) : Nat.card (Gen k) = k := by
  induction k with
  | zero => simp [Gen]
  | succ k ih =>
    change Nat.card (Option (Gen k)) = k+1
    letI := Fintype.ofFinite (Gen k)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option] using congrArg (· + 1) ih

theorem twice_card_rel (k : ℕ) : 2 * Nat.card (Rel k) = k*(k+1) := by
  induction k with
  | zero => simp [Rel]
  | succ k ih =>
    change 2 * Nat.card (Unit ⊕ (Gen k ⊕ Rel k)) = (k+1)*(k+1+1)
    simp only [Nat.card_sum, Nat.card_unique, card_gen]
    nlinarith only [ih]

theorem card_codes_succ (p k : ℕ) :
    Nat.card (Codes p (k+1)) = Nat.card (Codes p k) * p ^ Nat.card (Rel k) := by
  change Nat.card (Codes p k × (Rel k → Fin p)) = _
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]

theorem card_codes_pow_six_le (p k : ℕ) (hp : 0 < p) :
    (Nat.card (Codes p k))^6 ≤ p^(k^3) := by
  induction k with
  | zero => simp [Codes]
  | succ k ih =>
    rw [card_codes_succ, mul_pow, ← pow_mul]
    calc
      _ ≤ p^(k^3) * p^(Nat.card (Rel k)*6) := Nat.mul_le_mul_right _ ih
      _ = p^(k^3 + Nat.card (Rel k)*6) := (pow_add _ _ _).symm
      _ ≤ p^((k+1)^3) := Nat.pow_le_pow_right hp (by
        have h := twice_card_rel k
        nlinarith only [h])

end Erdos1160.CentralLifts

end

/- PrimePowerUpper -/
section

namespace Erdos1160.CentralLifts

open CategoryTheory

abbrev Model {p k : ℕ} (c : Codes p k) := Grp (relations c)

theorem trivial_zero {p : ℕ} (c : Codes p 0) : Subsingleton (Model c) := by
  let : IsEmpty (Gen 0) := inferInstanceAs (IsEmpty Empty)
  have h := PresentedGroup.closure_range_of (Set.range (relations c))
  rw [Set.range_eq_empty (PresentedGroup.of : Gen 0 → Model c), Subgroup.closure_empty] at h
  exact (subsingleton_iff_forall_eq (1 : Model c)).2 (fun g =>
    ((Subgroup.eq_bot_iff_forall _).mp h.symm) g trivial)

theorem finite_model {p : ℕ} (hp : 0 < p) (k : ℕ) (c : Codes p k) : Finite (Model c) := by
  induction k with
  | zero => let := trivial_zero c; infer_instance
  | succ k ih =>
    let : Finite (Model c.1) := ih c.1
    exact finite_lift (relations c.1) c.2 hp

theorem card_model {p : ℕ} (hp : 0 < p) (k : ℕ) (c : Codes p k) : Nat.card (Model c) ≤ p^k := by
  induction k with
  | zero =>
    let := trivial_zero c
    rw [Nat.card_unique, pow_zero]
  | succ k ih =>
    let : Finite (Model c.1) := finite_model hp _ _
    exact (card_lift (relations c.1) c.2 hp).trans (by
      rw [pow_succ]; exact Nat.mul_le_mul_right _ (ih c.1))

theorem covered {p : ℕ} (hp : p.Prime) (k : ℕ) (G : Type) [Group G] [Finite G]
    (hG : Nat.card G = p^k) :
    ∃ c : Codes p k, ∃ f : Model c →* G, Function.Surjective f := by
  let : Fact p.Prime := ⟨hp⟩
  induction k generalizing G with
  | zero =>
    have hone : Nat.card G = 1 := hG.trans (pow_zero _)
    let : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hone).1
    exact ⟨(),1,fun g => ⟨1,Subsingleton.elim _ _⟩⟩
  | succ k ih =>
    obtain ⟨u,hz,ho⟩ := exists_central_prime hG
    let N := Subgroup.zpowers u
    let : N.Normal := normal_zpowers_of_central u hz
    have hQ := card_quotient_prime hp.pos ho hG
    obtain ⟨c,f,hf⟩ := ih (G ⧸ N) hQ
    obtain ⟨j,v,hv⟩ := lift_surjection (relations c) (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      u ho hz (QuotientGroup.ker_mk' N) f hf
    exact ⟨(c,j),v,hv⟩

noncomputable def classOfModel {p k : ℕ} (hp : 0 < p) (c : Codes p k) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
  let : Finite (Model c) := finite_model hp _ _
  exact Quotient.mk _ (FiniteGrp.of (Model c))

theorem g_le_card_codes {p : ℕ} (hp : p.Prime) (k : ℕ) :
    g (p^k) ≤ Nat.card (Codes p k) := by
  let f := @classOfModel p k hp.pos
  have h : Tables.orderClasses (p^k) ⊆ Set.range f := by
    rintro _ ⟨G,hG,rfl⟩
    obtain ⟨c,v,hv⟩ := covered hp k G hG
    let : Finite (Model c) := finite_model hp.pos _ _
    have hcard : Nat.card (Model c) = Nat.card G :=
      le_antisymm ((card_model hp.pos _ _).trans (le_of_eq (show Nat.card G = p^k from hG).symm))
        (Nat.card_le_card_of_surjective v hv)
    let e := MulEquiv.ofBijective v ((Nat.bijective_iff_surjective_and_card v).2 ⟨hv,hcard⟩)
    exact ⟨c,Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.toGrpIso⟩⟩
  calc
    g (p^k) ≤ (Set.range f).ncard := Set.ncard_le_ncard h (Set.finite_range f)
    _ ≤ Nat.card (Codes p k) := Nat.card_le_card_of_surjective (Set.rangeFactorization f) Set.rangeFactorization_surjective

/-- Uniform elementary upper bound for the number of groups of prime-power order. -/
theorem prime_power_upper {p : ℕ} (hp : p.Prime) (k : ℕ) :
    g (p^k)^6 ≤ p^(k^3) :=
  (Nat.pow_le_pow_left (g_le_card_codes hp k) 6).trans (card_codes_pow_six_le p k hp.pos)

end Erdos1160.CentralLifts

end

/- OddPowerComparison -/
section

namespace Erdos1160Enumeration

/-- If an odd prime power lies below 2^m, its exponent k is at most 7m/11. -/
theorem odd_power_exponent {p k m : ℕ} (hp : 3 ≤ p) (hn : p^k ≤ 2^m) :
    11*k ≤ 7*m := by
  apply (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp
  calc
    (2 : ℕ)^(11*k) = (2^11)^k := Nat.pow_mul _ _ _
    _ ≤ (3^7)^k := Nat.pow_le_pow_left (by decide) _
    _ = (3^k)^7 := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm 7 k]
    _ ≤ (2^m)^7 := Nat.pow_le_pow_left ((Nat.pow_le_pow_left hp k).trans hn) 7
    _ = 2^(7*m) := by rw [← Nat.pow_mul, Nat.mul_comm]

private theorem slope_margin (r k : ℕ) (hr : 400 ≤ r) (hk : 11*k ≤ 7*(r+1)) :
    162*(r+3) + 27*((r+1)*k^2) + 72*r^2 ≤ 12*r^3 := by
  have hs := Nat.mul_le_mul hk hk
  have hcube := Nat.mul_le_mul_left (r+1) hs
  have h3 : 400*r^2 ≤ r^3 := by
    simpa only [pow_succ, pow_zero, Nat.one_mul, Nat.mul_assoc] using Nat.mul_le_mul_right (r*r) hr
  have h2 : 400*r ≤ r^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right r hr
  nlinarith only [hcube,h3,h2,hr]

/-- Compare a sixth-power count with the cubic lower bound for the previous dyadic order. -/
theorem count_compare_of_slope_fourfold {k r x y : ℕ} (hr : 400 ≤ r)
    (hk : 11*k ≤ 7*(r+1)) (hxh : x^6 ≤ 2^((r+1)*k^2))
    (hy : 2^(2*r^3) ≤ y^27 * 2^(12*r^2)) :
    2^(r+3) * x ≤ y := by
  have hyleft : (2 : ℕ)^(12*r^3) ≤ y^162 * 2^(72*r^2) := calc
    _ = (2^(2*r^3))^6 := by rw [← Nat.pow_mul]; congr 1; ring
    _ ≤ (y^27 * 2^(12*r^2))^6 := Nat.pow_le_pow_left hy _
    _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]; congr 2 <;> ring
  have hxl : x^162 ≤ 2^(27*((r+1)*k^2)) := calc
    _ = (x^6)^27 := Nat.pow_mul _ _ _
    _ ≤ (2^((r+1)*k^2))^27 := Nat.pow_le_pow_left hxh _
    _ = _ := by rw [← Nat.pow_mul, Nat.mul_comm 27]
  have lhs : (2^(r+3) * x)^162 * 2^(72*r^2) ≤ 2^(12*r^3) := calc
    _ = ((2^(r+3))^162 * x^162) * 2^(72*r^2) := by rw [Nat.mul_pow]
    _ ≤ ((2^(r+3))^162 * 2^(27*((r+1)*k^2))) * 2^(72*r^2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hxl)
    _ = 2^(162*(r+3) + 27*((r+1)*k^2) + 72*r^2) := by
      rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add, Nat.mul_comm (r+3) 162]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (slope_margin r k hr hk)
  have small : (2^(r+3) * x)^162 ≤ y^162 :=
    Nat.le_of_mul_le_mul_right (lhs.trans hyleft) (by positivity)
  exact (Nat.pow_le_pow_iff_left (by decide : 162 ≠ 0)).mp small

theorem count_compare_of_slope {k r x y : ℕ} (hr : 400 ≤ r)
    (hk : 11*k ≤ 7*(r+1)) (hxh : x^6 ≤ 2^((r+1)*k^2))
    (hy : 2^(2*r^3) ≤ y^27 * 2^(12*r^2)) :
    2^(r+2) * x ≤ y :=
  (Nat.mul_le_mul_right x (Nat.pow_le_pow_right (by decide) (by omega : r+2 ≤ r+3))).trans
    (count_compare_of_slope_fourfold hr hk hxh hy)

/-- A coarse prime-power presentation count is enough for the total contribution
of odd prime powers when compared with the sharp lower bound for 2-groups. -/
theorem odd_count_compare {p k r x y : ℕ} (hp : 3 ≤ p) (hr : 400 ≤ r)
    (hn : p^k ≤ 2^(r+1)) (hx : x^6 ≤ p^(k^3))
    (hy : 2^(2*r^3) ≤ y^27 * 2^(12*r^2)) :
    2^(r+2) * x ≤ y := by
  have hxh : x^6 ≤ 2^((r+1)*k^2) := calc
    x^6 ≤ p^(k^3) := hx
    _ = (p^k)^(k^2) := by rw [← Nat.pow_mul]; congr 1; ring
    _ ≤ (2^(r+1))^(k^2) := Nat.pow_le_pow_left hn _
    _ = _ := (Nat.pow_mul _ _ _).symm
  exact count_compare_of_slope hr (odd_power_exponent hp hn) hxh hy

/-- Sum a common pointwise budget over a finite set of at most N orders. -/
theorem sum_le_of_budget {A : Type*} (s : Finset A) (a : A → ℕ) {N b c : ℕ}
    (hN : 0 < N) (hs : s.card ≤ N) (ha : ∀ i ∈ s, (c*N)*a i ≤ b) :
    c*(∑ i ∈ s, a i) ≤ b := by
  apply Nat.le_of_mul_le_mul_left (c := N)
  · calc
      N*(c*∑ i ∈ s, a i) = ∑ i ∈ s, (c*N)*a i := by
        rw [← Finset.mul_sum, ← Nat.mul_assoc, Nat.mul_comm N c]
      _ ≤ ∑ _i ∈ s, b := Finset.sum_le_sum ha
      _ = s.card * b := by simp
      _ ≤ N*b := Nat.mul_le_mul_right _ hs
  · exact hN

/-- Sum a common pointwise budget over a finite set of at most N orders. -/
theorem twice_sum_le_of_budget {A : Type*} (s : Finset A) (a : A → ℕ) {N b : ℕ}
    (hN : 0 < N) (hs : s.card ≤ N) (ha : ∀ i ∈ s, (2*N)*a i ≤ b) :
    2*(∑ i ∈ s, a i) ≤ b := by
  apply Nat.le_of_mul_le_mul_left (c := N)
  · calc
      N*(2*∑ i ∈ s, a i) = ∑ i ∈ s, (2*N)*a i := by
        rw [← Finset.mul_sum, ← Nat.mul_assoc, Nat.mul_comm N 2]
      _ ≤ ∑ _i ∈ s, b := Finset.sum_le_sum ha
      _ = s.card * b := by simp
      _ ≤ N*b := Nat.mul_le_mul_right _ hs
  · exact hN

end Erdos1160Enumeration

end

/- NilpotentMixed -/
section

/-! A split upper bound retaining the exact contribution from the Sylow 2-subgroup. -/

namespace Erdos1160.NilpotentCounts
open Erdos1160.Tables
open scoped BigOperators

theorem mixed_nilpotent_upper {m n : ℕ} (hn : 0 < n) (hnm : n ≤ 2^m) :
    (nilpotentClasses n).ncard^6 ≤ g (2^(n.factorization 2))^6 *
      2^((m - n.factorization 2) * (7*(m - n.factorization 2)/11)^2) := by
  let a := n.factorization 2
  let K := 7*(m-a)/11
  let s := n.primeFactors.erase 2
  let q := ∏ p ∈ s, p ^ n.factorization p
  have ha : a ≤ m := Nat.factorization_le_of_le_pow hnm
  have he : 2^a * q = n := by
    rw [Nat.prod_primeFactors_pow_factorization hn.ne']
    change 2^a * q = ∏ p ∈ n.primeFactors, p^n.factorization p
    by_cases h2 : 2 ∈ n.primeFactors
    · exact Finset.mul_prod_erase _ (fun p => p ^ n.factorization p) h2
    · have hzero : a = 0 := Finsupp.notMem_support_iff.mp h2
      simp [q,s,hzero,Finset.erase_eq_of_notMem h2]
  have hq : 0 < q := Finset.prod_pos (fun p hp => Nat.pow_pos
    (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).pos)
  have hqm : q ≤ 2^(m-a) := by
    apply Nat.le_of_mul_le_mul_left (c := 2^a) _ (Nat.pow_pos (by decide : 0 < 2))
    rw [he, ← pow_add, Nat.add_sub_of_le ha]
    exact hnm
  have split : ∏ p ∈ n.primeFactors, g (p^n.factorization p) ≤
      g (2^a) * ∏ p ∈ s, g (p^n.factorization p) := by
    by_cases h2 : 2 ∈ n.primeFactors
    · exact (Finset.mul_prod_erase _ (fun p => g (p ^ n.factorization p)) h2).ge
    · have hpos := g_pos (Nat.pow_pos (by decide : 0 < 2) (n := a))
      simpa [s,Finset.erase_eq_of_notMem h2] using
        (Nat.mul_le_mul_right (∏ p ∈ n.primeFactors, g (p ^ n.factorization p))
          (show 1 ≤ g (2^a) from hpos))
  have hbound (p : ℕ) (hp : p ∈ s) :
      g (p^n.factorization p)^6 ≤ (p^n.factorization p)^(K^2) := by
    let k := n.factorization p
    have hpr := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    have hge : 3 ≤ p := by
      have := Finset.ne_of_mem_erase hp
      have := hpr.two_le
      omega
    have hd : p^k ∣ q := Finset.dvd_prod_of_mem (fun z => z ^ n.factorization z) hp
    have hslope := Erdos1160Enumeration.odd_power_exponent hge ((Nat.le_of_dvd hq hd).trans hqm)
    have hk : k ≤ K := by dsimp [K]; omega
    calc
      _ ≤ p^(k^3) := Erdos1160.CentralLifts.prime_power_upper hpr k
      _ = (p^k)^(k^2) := by rw [← Nat.pow_mul]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (Nat.pow_pos hpr.pos) (Nat.pow_le_pow_left hk 2)
  calc
    _ ≤ (g (2^a) * ∏ p ∈ s, g (p^n.factorization p))^6 :=
      Nat.pow_le_pow_left ((nilpotent_ncard_le n).trans split) 6
    _ = g (2^a)^6 * ∏ p ∈ s, g (p^n.factorization p)^6 := by rw [mul_pow, Finset.prod_pow]
    _ ≤ g (2^a)^6 * ∏ p ∈ s, (p^n.factorization p)^(K^2) :=
      Nat.mul_le_mul_left _ (Finset.prod_le_prod' hbound)
    _ = g (2^a)^6 * q^(K^2) := by rw [Finset.prod_pow]
    _ ≤ g (2^a)^6 * (2^(m-a))^(K^2) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqm _)
    _ = _ := by rw [← Nat.pow_mul]

end Erdos1160.NilpotentCounts

end

/- PresentationCount -/
section

/-!
Counting abstract groups using marked presentations. A finite family may
contain several isomorphic groups. If an isomorphism preserving all marks
determines the parameter, each class has at most as many parameters as
there are ordered tuples of marks in one representative.
-/

namespace Erdos1160.PresentationCount

open CategoryTheory

/-- Count by the fibers of a map between finite types. -/
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

/-- An isomorphism preserving all the marked elements distinguishes parameter
values. Forgetting the k marks can identify at most n^k parameters per class. -/
theorem card_le_of_marked_family {A : Type*} [Finite A] {n k : ℕ}
    (X : A → FiniteGrp.{0}) (hN : ∀ a, Nat.card (X a) = n)
    (mark : (a : A) → Fin k → X a)
    (sep : ∀ (a b : A) (e : X a ≃* X b),
      (∀ i, e (mark a i) = mark b i) → a = b) :
    Nat.card A ≤ Erdos1160.g n * n ^ k := by
  classical
  let f (a : A) : Tables.orderClasses n := ⟨Quotient.mk _ (X a), X a, hN a, rfl⟩
  let : Finite (Tables.orderClasses n) := (Tables.orderClasses_finite n).to_subtype
  apply card_le_of_fiber_bound f (n ^ k)
  intro c
  let F := {a : A // f a = c}
  by_cases hn : Nonempty F
  · let r := Classical.choice hn
    have sameClass (a : F) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (X a.val)
        = Quotient.mk _ (X r.val) :=
      congrArg Subtype.val (a.property.trans r.property.symm)
    let transport (a : F) : X a.val ≃* X r.val :=
      ((inducedFunctor FiniteGrp.toGrp).mapIso
        (Classical.choice (Quotient.exact (sameClass a)))).groupIsoToMulEquiv
    let encode (a : F) (i : Fin k) : X r.val := transport a (mark a.val i)
    have uniqueCode : Function.Injective encode := by
      intro a b he
      apply Subtype.ext
      apply sep a.val b.val ((transport a).trans (transport b).symm)
      intro i
      apply (transport b).injective
      change transport b ((transport b).symm (transport a (mark a.val i))) =
        transport b (mark b.val i)
      rw [MulEquiv.apply_symm_apply]
      exact congrFun he i
    calc
      Nat.card F ≤ Nat.card (Fin k → X r.val) :=
        Nat.card_le_card_of_injective encode uniqueCode
      _ = n ^ k := by rw [Nat.card_fun, hN, Nat.card_fin]
  · have empty : IsEmpty F := not_nonempty_iff.mp hn
    change Nat.card F ≤ n ^ k
    simp

end Erdos1160.PresentationCount

end

/- RelativeCodes -/
section

namespace Erdos1160.PresentationCount

open CategoryTheory

/-- If comparisons with one fixed representative have finite codes, and a
code determines the source parameter, the number of isomorphic parameters
in each class is at most the size of the code space. -/
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

end

/- BilinearExtension -/
section

namespace Erdos1160Growth

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- The central extension built from an arbitrary biadditive map, with two visible coordinates. -/
structure BilinearExtension (B : V →+ V →+ W) where
  base : V
  fiber : W

namespace BilinearExtension

variable {B : V →+ V →+ W}

theorem ext {x y : BilinearExtension B} (hb : x.base = y.base)
    (hf : x.fiber = y.fiber) : x = y := by
  cases x
  cases y
  congr

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

def projection (B : V →+ V →+ W) : BilinearExtension B →* Multiplicative V where
  toFun x := Multiplicative.ofAdd x.base
  map_mul' _ _ := rfl
  map_one' := rfl

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

theorem commutator_le_kernel (B : V →+ V →+ W) :
    commutator (BilinearExtension B) ≤ (projection B).ker := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  rw [commutator_formula]
  rfl

theorem central_fiber (w : W) :
    (⟨0,w⟩ : BilinearExtension B) ∈ Subgroup.center (BilinearExtension B) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply BilinearExtension.ext <;> simp
  abel

/-- Surjectivity of the alternating commutator on pairs ensures that the fiber is characteristic. -/
def AllFiberCommutators (B : V →+ V →+ W) : Prop :=
  ∀ w : W, ∃ u v : V, B u v - B v u = w

theorem commutator_eq_kernel (h : AllFiberCommutators B) :
    commutator (BilinearExtension B) = (projection B).ker := by
  apply le_antisymm (commutator_le_kernel B)
  intro x hx
  have hx0 : x.base = 0 := hx
  obtain ⟨u, v, huv⟩ := h x.fiber
  let a : BilinearExtension B := ⟨u, 0⟩
  let b : BilinearExtension B := ⟨v, 0⟩
  have heq : ⁅a, b⁆ = x := by
    rw [commutator_formula]
    exact BilinearExtension.ext hx0.symm huv
  rw [← heq]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

variable {V' W' : Type*} [AddCommGroup V'] [AddCommGroup W'] {C : V' →+ V' →+ W'}

theorem map_fiber_base (h : AllFiberCommutators B)
    (f : BilinearExtension B →* BilinearExtension C) (w : W) :
    (f ⟨0, w⟩).base = 0 := by
  obtain ⟨u, v, huv⟩ := h w
  let a : BilinearExtension B := ⟨u, 0⟩
  let b : BilinearExtension B := ⟨v, 0⟩
  have heq : ⁅a, b⁆ = ⟨0, w⟩ := by
    rw [commutator_formula]
    exact BilinearExtension.ext rfl huv
  rw [← heq, map_commutatorElement, commutator_formula]

theorem map_base_lift (h : AllFiberCommutators B)
    (f : BilinearExtension B →* BilinearExtension C) (x : BilinearExtension B) :
    (f x).base = (f ⟨x.base, 0⟩).base := by
  have decomp : x = (⟨x.base, 0⟩ : BilinearExtension B) * ⟨0, x.fiber⟩ := by
    apply BilinearExtension.ext <;> simp
  conv => lhs; rw [decomp, map_mul, mul_base, map_fiber_base h, add_zero]

def inducedBase (h : AllFiberCommutators B) (f : BilinearExtension B →* BilinearExtension C) :
    V →+ V' where
  toFun u := (f ⟨u, 0⟩).base
  map_zero' := by change (f 1).base = 0; rw [map_one, one_base]
  map_add' u v := by
    let x : BilinearExtension B := ⟨u, 0⟩
    let y : BilinearExtension B := ⟨v, 0⟩
    exact (map_base_lift h f (x*y)).symm.trans (by rw [map_mul, mul_base])

def inducedFiber (h : AllFiberCommutators B) (f : BilinearExtension B →* BilinearExtension C) :
    W →+ W' where
  toFun w := (f ⟨0, w⟩).fiber
  map_zero' := by change (f 1).fiber = 0; rw [map_one, one_fiber]
  map_add' w z := by
    let x : BilinearExtension B := ⟨0, w⟩
    let y : BilinearExtension B := ⟨0, z⟩
    have eqn : (⟨0, w+z⟩ : BilinearExtension B) = x*y := by apply BilinearExtension.ext <;> simp [x,y]
    rw [eqn, map_mul, mul_fiber]
    simp [x, y, map_fiber_base h]

theorem inducedBase_apply (h : AllFiberCommutators B)
    (f : BilinearExtension B →* BilinearExtension C) (x : BilinearExtension B) :
    inducedBase h f x.base = (f x).base := (map_base_lift h f x).symm

theorem map_lift_fiber (h : AllFiberCommutators B)
    (f : BilinearExtension B →* BilinearExtension C) (w : W) :
    f ⟨0, w⟩ = ⟨0, inducedFiber h f w⟩ :=
  BilinearExtension.ext (map_fiber_base h f w) rfl

theorem intertwinement (h : AllFiberCommutators B)
    (f : BilinearExtension B →* BilinearExtension C) (u v : V) :
    inducedFiber h f (B u v - B v u) =
    C (inducedBase h f u) (inducedBase h f v) - C (inducedBase h f v) (inducedBase h f u) := by
  let x : BilinearExtension B := ⟨u, 0⟩
  let y : BilinearExtension B := ⟨v, 0⟩
  have hm := map_commutatorElement f x y
  rw [commutator_formula, commutator_formula] at hm
  exact congrArg BilinearExtension.fiber hm

theorem inducedBase_leftInv (hB : AllFiberCommutators B) (hC : AllFiberCommutators C)
    (e : BilinearExtension B ≃* BilinearExtension C) :
    Function.LeftInverse (inducedBase hC e.symm.toMonoidHom) (inducedBase hB e.toMonoidHom) := by
  intro u
  let x : BilinearExtension B := ⟨u, 0⟩
  change inducedBase hC e.symm.toMonoidHom (e x).base = u
  rw [inducedBase_apply]
  change (e.symm (e x)).base = u
  rw [e.symm_apply_apply]

theorem inducedFiber_leftInv (hB : AllFiberCommutators B) (hC : AllFiberCommutators C)
    (e : BilinearExtension B ≃* BilinearExtension C) :
    Function.LeftInverse (inducedFiber hC e.symm.toMonoidHom) (inducedFiber hB e.toMonoidHom) := by
  intro w
  change (e.symm ⟨0, inducedFiber hB e.toMonoidHom w⟩).fiber = w
  rw [← map_lift_fiber hB e.toMonoidHom w]
  change (e.symm (e ⟨0,w⟩)).fiber = w
  rw [e.symm_apply_apply]

/-- Any isomorphism of the constructed groups gives a change of coordinates on the
abelian quotient and the commutator subgroup that preserves the alternating map. -/
theorem isomorphism_preserves_alternating (hB : AllFiberCommutators B) (hC : AllFiberCommutators C)
    (e : BilinearExtension B ≃* BilinearExtension C) :
    ∃ (s : V ≃+ V') (t : W ≃+ W'), ∀ u v,
      t (B u v - B v u) = C (s u) (s v) - C (s v) (s u) := by
  let s : V ≃+ V' :=
    { inducedBase hB e.toMonoidHom with
      invFun := inducedBase hC e.symm.toMonoidHom
      left_inv := inducedBase_leftInv hB hC e
      right_inv := inducedBase_leftInv hC hB e.symm }
  let t : W ≃+ W' :=
    { inducedFiber hB e.toMonoidHom with
      invFun := inducedFiber hC e.symm.toMonoidHom
      left_inv := inducedFiber_leftInv hB hC e
      right_inv := inducedFiber_leftInv hC hB e.symm }
  exact ⟨s, t, intertwinement hB e.toMonoidHom⟩

end BilinearExtension

end Erdos1160Growth

end

/- SharpFamily -/
section

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

end

/- SharpAux -/
section

namespace Erdos1160Growth.BilinearExtension

open scoped commutatorElement

private theorem sharpAux_double_zero {s : ℕ} (w : Fin s → ZMod 2) : w+w = 0 := by
  funext i
  have h : ∀ z : ZMod 2, z+z = 0 := by decide
  exact h (w i)

theorem lift_square_eq_of_base_eq {V : Type*} [AddCommGroup V] {s : ℕ}
    {B : V →+ V →+ (Fin s → ZMod 2)} {a b : BilinearExtension B} (h : a.base = b.base) :
    a * a = b * b := by
  apply BilinearExtension.ext
  · simp only [mul_base, h]
  · simp only [mul_fiber, sharpAux_double_zero, zero_add, h]

theorem lift_commutator_eq_of_base_eq {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    {B : V →+ V →+ W} {a b c d : BilinearExtension B}
    (hac : a.base = c.base) (hbd : b.base = d.base) :
    ⁅a,b⁆ = ⁅c,d⁆ := by
  rw [commutator_formula, commutator_formula, hac, hbd]

end Erdos1160Growth.BilinearExtension

end

/- SharpRecovery -/
section

namespace Erdos1160Growth.SharpFamily

open scoped commutatorElement

variable {d s : ℕ}

/-- Two homomorphisms from different presentations that agree on all coordinate fibers
agree on every element of the common central vector space. -/
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

/-- Projecting the images of the d generators into the elementary abelian quotient
gives a complete code for presentations mapping isomorphically into one fixed target. -/
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

end

/- SharpSlots -/
section

namespace Erdos1160Growth.SharpFamily

theorem triangular_card (d : ℕ) :
    Nat.card ((i : Fin d) × Fin i.val) = d * (d - 1) / 2 := by
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)

end Erdos1160Growth.SharpFamily

end

/- SharpCount -/
section

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

/-- Lower bound from the explicit family with s diagonal squares fixed to a
fiber basis. A comparison with a representative needs only d base vectors
of d bits each. -/
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

end

/- SharpAllOrders -/
section

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

/-- The sharp cubic and quadratic terms of Higman's lower bound, with all denominators
cleared and a single estimate valid in each of the three residue classes. -/
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

end

/- Cancellation -/
section

namespace Erdos1160.Cancellation

abbrev C₂ := Multiplicative (Fin 2)

lemma c2_square (x : C₂) : x*x=1 := by
  have h : ∀ t : C₂, t * t = 1 := by decide
  exact h x

lemma endo_dichotomy (f : C₂ →* C₂) : (∀ x, f x = x) ∨ (∀ x, f x = 1) := by
  let t : C₂ := Multiplicative.ofAdd 1
  have exhaust : ∀ x : C₂, x = 1 ∨ x = t := by decide
  rcases exhaust (f t) with ht | ht
  · right
    intro x
    rcases exhaust x with rfl | rfl
    · exact map_one _
    · exact ht
  · left
    intro x
    rcases exhaust x with rfl | rfl
    · exact map_one _
    · exact ht

lemma mul_middle {K : Type*} [Group K] {x y u v : K} (h : Commute y u) :
    (x*y)*(u*v) = (x*u)*(y*v) := by
  calc
    _ = x * ((y*u)*v) := by simp [mul_assoc]
    _ = x * ((u*y)*v) := by rw [h.eq]
    _ = _ := by simp [mul_assoc]

def pairMul {A K : Type*} [Group A] [Group K] (f g : A →* K)
    (hc : ∀ x y, Commute (g x) (f y)) : A →* K where
  toFun x := f x * g x
  map_one' := by simp
  map_mul' x y := by simpa only [map_mul] using (mul_middle (x := f x) (v := g y) (hc x y)).symm

lemma common_section {K : Type*} [Group K] (p q : K →* C₂) (s t : C₂ →* K)
    (hs : ∀ x, p (s x) = x) (ht : ∀ x, q (t x) = x)
    (sc : ∀ x k, Commute (s x) k) (tc : ∀ x k, Commute (t x) k) :
    ∃ u : C₂ →* K, (∀ x, p (u x) = x) ∧ (∀ x, q (u x) = x) ∧ (∀ x k, Commute (u x) k) := by
  rcases endo_dichotomy (q.comp s) with h | h
  · exact ⟨s,hs,h,sc⟩
  rcases endo_dichotomy (p.comp t) with j | j
  · exact ⟨t,j,ht,tc⟩
  refine ⟨pairMul s t (fun x y => tc x (s y)), ?_, ?_, ?_⟩
  · intro x
    change p (s x * t x) = x
    have htx : p (t x) = 1 := j x
    simp [hs, htx]
  · intro x
    change q (s x * t x) = x
    have hsx : q (s x) = 1 := h x
    simp [ht, hsx]
  · intro x k
    exact (sc x k).mul_left (tc x k)

def project {K : Type*} [Group K] (p : K →* C₂) (s : C₂ →* K)
    (sc : ∀ x k, Commute (s x) k) : K →* K :=
  pairMul (MonoidHom.id K) (s.comp p) (fun x y => sc (p x) y)

lemma project_mem {K : Type*} [Group K] (p : K →* C₂) (s : C₂ →* K)
    (hs : ∀ x, p (s x) = x) (sc : ∀ x k, Commute (s x) k) (x : K) :
    project p s sc x ∈ p.ker := by
  change p (x * s (p x)) = 1
  rw [map_mul, hs, c2_square]

lemma project_roundtrip {K : Type*} [Group K] (p q : K →* C₂) (s : C₂ →* K)
    (hp : ∀ x, p (s x) = x) (sc : ∀ x k, Commute (s x) k) (x : K) (hx : p x = 1) :
    project p s sc (project q s sc x) = x := by
  change (x * s (q x)) * s (p (x * s (q x))) = x
  rw [map_mul, hx, one_mul, hp, mul_assoc, ← map_mul, c2_square, map_one, mul_one]

def kernelEquiv {K : Type*} [Group K] (p q : K →* C₂) (s : C₂ →* K)
    (hp : ∀ x, p (s x) = x) (hq : ∀ x, q (s x) = x) (sc : ∀ x k, Commute (s x) k) :
    p.ker ≃* q.ker where
  toFun x := ⟨project q s sc x, project_mem q s hq sc x⟩
  invFun y := ⟨project p s sc y, project_mem p s hp sc y⟩
  left_inv x := Subtype.ext (project_roundtrip p q s hp sc x x.property)
  right_inv y := Subtype.ext (project_roundtrip q p s hq sc y y.property)
  map_mul' x y := Subtype.ext (map_mul (project q s sc) x.val y.val)

def factorKernel {K H : Type*} [Group K] [Group H] (e : K ≃* H × C₂) :
    H ≃* ((MonoidHom.snd H C₂).comp e.toMonoidHom).ker where
  toFun h := ⟨e.symm (h,1), by change (e (e.symm (h,1))).2 = 1; simp⟩
  invFun x := (e x.val).1
  left_inv h := by simp
  right_inv x := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext rfl x.property.symm
  map_mul' h k := by
    apply Subtype.ext
    exact map_mul e.symm (h,1) (k,1)

def sectionOfEquiv {K H : Type*} [Group K] [Group H] (e : K ≃* H × C₂) : C₂ →* K :=
  e.symm.toMonoidHom.comp (MonoidHom.inr H C₂)

lemma sectionOfEquiv_right {K H : Type*} [Group K] [Group H] (e : K ≃* H × C₂) (z : C₂) :
    ((MonoidHom.snd H C₂).comp e.toMonoidHom) (sectionOfEquiv e z) = z := by
  change (e (e.symm (1,z))).2 = z
  simp

lemma sectionOfEquiv_central {K H : Type*} [Group K] [Group H] (e : K ≃* H × C₂) (z : C₂) (k : K) :
    Commute (sectionOfEquiv e z) k := by
  apply e.injective
  change e (e.symm (1,z) * k) = e (k * e.symm (1,z))
  simp only [map_mul, e.apply_symm_apply]
  apply Prod.ext
  · simp
  · simp [mul_comm]

theorem c2_cancel {G H : Type*} [Group G] [Group H] (e : G × C₂ ≃* H × C₂) :
    Nonempty (G ≃* H) := by
  let i := MulEquiv.refl (G × C₂)
  let p := (MonoidHom.snd G C₂).comp i.toMonoidHom
  let q := (MonoidHom.snd H C₂).comp e.toMonoidHom
  obtain ⟨s,hp,hq,hc⟩ := common_section p q (sectionOfEquiv i) (sectionOfEquiv e)
    (sectionOfEquiv_right i) (sectionOfEquiv_right e)
    (sectionOfEquiv_central i) (sectionOfEquiv_central e)
  exact ⟨((factorKernel i).trans (kernelEquiv p q s hp hq hc)).trans (factorKernel e).symm⟩

end Erdos1160.Cancellation

end

/- Monotonicity -/
section

namespace Erdos1160.Cancellation

open CategoryTheory
open Erdos1160.Tables

abbrev GroupClass := Quotient (isIsomorphicSetoid FiniteGrp.{0})

def withC2 (G : FiniteGrp.{0}) : FiniteGrp.{0} := FiniteGrp.of (G × C₂)

def doubleClass : GroupClass → GroupClass :=
  Quotient.map withC2 (by
    rintro G H ⟨i⟩
    let e : G ≃* H := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv
    let f : withC2 G ≃* withC2 H := e.prodCongr (MulEquiv.refl C₂)
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩)

lemma doubleClass_mk (G : FiniteGrp.{0}) :
    doubleClass (Quotient.mk _ G) = Quotient.mk _ (withC2 G) := rfl

lemma doubleClass_injective : Function.Injective doubleClass := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | _ G H =>
    intro h
    obtain ⟨i⟩ := Quotient.exact (show Quotient.mk _ (withC2 G) = Quotient.mk _ (withC2 H) from h)
    let f : G × C₂ ≃* H × C₂ := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv
    obtain ⟨e⟩ := c2_cancel f
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.toGrpIso⟩

lemma doubleClass_maps (n : ℕ) : Set.MapsTo doubleClass (orderClasses n) (orderClasses (n * 2)) := by
  rintro _ ⟨G,hG,rfl⟩
  refine ⟨withC2 G, ?_, rfl⟩
  change Nat.card (G × C₂) = n * 2
  rw [Nat.card_prod, show Nat.card G = n from hG]
  exact congrArg (n * ·) (Nat.card_fin 2)

lemma mem_doubleClass_image_iff (n : ℕ) (y : GroupClass) :
    y ∈ doubleClass '' orderClasses n ↔ ∃ G : FiniteGrp.{0}, Nat.card G = n ∧
      Quotient.mk _ (withC2 G) = y := by
  constructor
  · rintro ⟨_, ⟨G,hG,rfl⟩, h⟩
    exact ⟨G,hG,h⟩
  · rintro ⟨G,hG,rfl⟩
    exact ⟨Quotient.mk _ G, ⟨G,hG,rfl⟩, rfl⟩

lemma ncard_doubleClass_image (n : ℕ) : (doubleClass '' orderClasses n).ncard = g n :=
  (Set.injOn_of_injective doubleClass_injective).ncard_image

theorem g_le_g_double (n : ℕ) : g n ≤ g (n * 2) :=
  Set.ncard_le_ncard_of_injOn doubleClass (doubleClass_maps n)
    (Set.injOn_of_injective doubleClass_injective) (orderClasses_finite _)

theorem g_two_pow_mono (m : ℕ) : g (2 ^ m) ≤ g (2 ^ (m + 1)) := by
  simpa only [pow_succ] using g_le_g_double (2 ^ m)

end Erdos1160.Cancellation

end

/- NilpotentViaProducts -/
section

namespace Erdos1160.DirectFactors

open Filter NilpotentCounts

private theorem odd_cost {t : ℕ} (ht : 1000 ≤ t) :
    2^(t*(7*t/11)^2) ≤ g (2^(t-2))^6 := by
  let k := 7*t/11
  have hk : 11*k ≤ 7*t := by dsimp [k]; omega
  have cub : 27*(t*k^2) ≤ 11*t^3 := by
    have h := Nat.mul_le_mul_left t (Nat.mul_le_mul hk hk)
    nlinarith only [h]
  have margin : 11*t^3 + 72*(t-2)^2 ≤ 12*(t-2)^3 := by
    obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show 1000+u-2=998+u by omega]
    ring_nf
    omega
  let r := t-2
  let y := g (2^r)
  have lower := Erdos1160Growth.SharpFamily.higman_lower_all r (by dsimp [r]; omega)
  have raised : (2:ℕ)^(12*r^3) ≤ y^(6*27)*2^(72*r^2) := by
    have p := Nat.pow_le_pow_left lower 6
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at p
    convert p using 2 <;> ring
  have cap : (2:ℕ)^(27*(t*k^2))*2^(72*r^2) ≤ y^(6*27)*2^(72*r^2) := by
    rw [←Nat.pow_add]
    apply le_trans _ raised
    apply Nat.pow_le_pow_right (by decide)
    dsimp [r]
    omega
  apply (Nat.pow_le_pow_iff_left (by decide : 27 ≠ 0)).mp
  change ((2:ℕ)^(t*k^2))^27 ≤ (y^6)^27
  rw [←Nat.pow_mul, ←Nat.pow_mul, Nat.mul_comm (t*k^2)]
  exact Nat.le_of_mul_le_mul_right cap (by positivity)

/-- There is one threshold for every mixed order below the cutoff. -/
theorem all_mixed_nilpotent :
    ∀ᶠ m : ℕ in atTop, ∀ n ∈ Finset.Ico 1 (2^m), (¬ ∃ k : ℕ, n=2^k) →
      (nilpotentClasses n).ncard ≤ 2^(m-2)*g (2^(m-2)) := by
  refine eventually_atTop.mpr ⟨1000000002, ?_⟩
  intro m hm n hn hmix
  obtain ⟨hpos,hlt⟩ := Finset.mem_Ico.mp hn
  let a := n.factorization 2
  let t := m-a
  have ham : a ≤ m := Nat.factorization_le_of_le_pow hlt.le
  have hsum : a+t=m := by dsimp [t]; omega
  obtain ⟨q,hq⟩ := Nat.ordProj_dvd n 2
  change n = 2^a*q at hq
  have hq' : 2 ≤ q := by
    by_contra! h
    rcases (show q=0 ∨ q=1 by omega) with rfl|rfl
    · simp [hq] at hpos
    · exact hmix ⟨a,by simpa using hq⟩
  have ha : 2^(a+1) ≤ n := by rw [hq,Nat.pow_succ]; exact Nat.mul_le_mul_left _ hq'
  have ha' := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2:ℕ))).mp (ha.trans_lt hlt)
  have h := mixed_nilpotent_upper hpos hlt.le
  change (nilpotentClasses n).ncard^6 ≤ g (2^a)^6 * 2^(t*(7*t/11)^2) at h
  by_cases ht : 1000 ≤ t
  · have hxy : (nilpotentClasses n).ncard ≤ g (2^a)*g (2^(t-2)) := by
      apply (Nat.pow_le_pow_iff_left (by decide : 6 ≠ 0)).mp
      rw [Nat.mul_pow]
      exact h.trans (Nat.mul_le_mul_left _ (odd_cost ht))
    have eq : 2^a*2^(t-2) = 2^(m-2) := by rw [←Nat.pow_add, show a+(t-2)=m-2 by omega]
    exact hxy.trans (eq ▸ product_count (2^a) (2^(t-2)))
  · have ht' : t ≤ 1000 := by omega
    have hk : 7*t/11 ≤ 1000 := by omega
    have exp : t*(7*t/11)^2 ≤ 6*(m-2) := by
      have b := Nat.mul_le_mul ht' (Nat.pow_le_pow_left hk 2)
      omega
    have mono := monotone_nat_of_le_succ Cancellation.g_two_pow_mono
    apply (Nat.pow_le_pow_iff_left (by decide : 6 ≠ 0)).mp
    apply h.trans
    rw [Nat.mul_pow, ←Nat.pow_mul, Nat.mul_comm (m-2) 6, Nat.mul_comm (2^_)]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (mono (show a ≤ m-2 by omega)) 6)
      (Nat.pow_le_pow_right (by decide) exp)

theorem nested_leaf :
    OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1_H2_R1.H2 := by
  filter_upwards [all_mixed_nilpotent] with m h
  exact fun n hn hmix _ => h n hn hmix


end Erdos1160.DirectFactors

end

/-- The remaining large two-part range of the nilpotent step in reduction 7374. -/
theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H2_R1_H2_R1.H2 :=
  Erdos1160.DirectFactors.nested_leaf
