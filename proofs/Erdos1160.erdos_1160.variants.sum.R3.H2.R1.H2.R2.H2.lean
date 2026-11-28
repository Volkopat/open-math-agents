import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1_H2_R2

-- Step Erdos1160.erdos_1160.variants.sum.R3.H2.R1.H2.R2.H2: hypothesis H2 of reduction Erdos1160.erdos_1160.variants.sum.R3.H2.R1.H2.R2
-- Credit: the moment estimate wide_moment_envelope and all supporting lemmas are from @kamaleshanantha (PR 2379, checker-accepted).
-- New here: the sigma-type count of automorphism tuples and the final assembly (moment_large_leaf).

namespace Erdos1160.CentralLifts
end Erdos1160.CentralLifts
namespace Erdos1160.SylowActions
end Erdos1160.SylowActions

/- BinaryFactor -/
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

/- BinaryDescent -/
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

/- BinaryInflation -/
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

/- BinarySpaces -/
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

/- BinaryTwist -/
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

/- BinaryMarks -/
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

/- BinaryGauges -/
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

/- BinaryBetti -/
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

/- BilinearExtension -/
section
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

/- LowerTriangularUpper -/
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
end Erdos1160Growth.LowerTriangularUpper
end

/- Normalize -/
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

/- AllBilinear -/
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

/- ExtensionBasics -/
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

/- ElementaryCoords -/
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

/- SectionEquiv -/
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
end Erdos1160Growth.LowerTriangularUpper.CentralData
end

/- CommCode -/
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

/- Collect -/
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

/- SectionCoverage -/
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

/- SquareCoreCount -/
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
def squareCore (E : Type*) [Group E] : Subgroup E :=
  Subgroup.closure (Set.range fun x : E => x*x)
end Erdos1160Growth.LowerTriangularUpper
end

/- FrattiniContainment -/
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

/- FrattiniSquare -/
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

/- FrattiniCount -/
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
theorem frattini_eq_squareCore {G : Type*} [Group G] [Finite G] {m : ℕ}
    (h : Nat.card G = 2^m) : frattini G = squareCore G :=
  le_antisymm frattini_le_squareCore (squares_le_frattini h)
end Erdos1160Growth.LowerTriangularUpper
end

/- BinaryRecurrence -/
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

/- InflationMap -/
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

/- CochainAlternation -/
section
namespace BinaryFactor
open Cocycle
variable {A : Type*} [CommGroup A]
def antisym₃ (θ : C₃ A) (x y z : A) : Bit :=
  θ x y z+θ x z y+θ y x z+θ y z x+θ z x y+θ z y x
theorem antisym₃_boundary (u : C₂ A) (x y z : A) : antisym₃ (d₂ u) x y z=0 := by
  simp only [antisym₃,d₂,mul_comm y x,mul_comm z x,mul_comm z y]
  ring_nf <;> simp [show (2:Bit)=0 by decide]
def exteriorProj {I : Type*} (e : I → A) : (C₃ A ⧸ boundaries₃ A) →ₗ[Bit] (I→I→I→Bit) :=
  (boundaries₃ A).liftQ ({
    toFun := fun θ i j k => antisym₃ θ (e i) (e j) (e k)
    map_add' := by intro θ σ;funext i j k;dsimp [antisym₃];abel
    map_smul' := by intro r θ;funext i j k;dsimp [antisym₃];ring
    } : C₃ A →ₗ[Bit] (I→I→I→Bit)) (by
    rintro _ ⟨u,rfl⟩
    funext i j k
    exact antisym₃_boundary u.val _ _ _)
def cupRaw {X : Type*} (chi : C₁ X) (u : C₂ X) (x y z : X) : Bit := chi x*u y z
def wedgeCoeffs {I : Type*} (chi : I→Bit) (B : I→I→Bit) (i j k : I) : Bit :=
  chi i*B j k+chi j*B i k+chi k*B i j
def antisym₂ {X : Type*} (u : C₂ X) (x y : X) := u x y+u y x
theorem exteriorProj_cup {I : Type*} (e : I→A) (chi : C₁ A) (u : C₂ A) :
    exteriorProj e ((boundaries₃ A).mkQ (cupRaw chi u)) =
      wedgeCoeffs (fun i=>chi (e i)) (fun i j=> antisym₂ u (e i) (e j)) := by
  funext i j k
  change antisym₃ (cupRaw chi u) (e i) (e j) (e k)=_
  dsimp [antisym₃,antisym₂,cupRaw,wedgeCoeffs]
  ring
variable {Y : Type*} [Group Y]
end BinaryFactor
end

/- TwistRealization -/
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

/- GenuineInflation -/
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

/- CupFunctor -/
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

/- BinaryNonsplit -/
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

/- GaugeClasses -/
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

/- BockFunctor -/
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
end BinaryFactor
end

/- ElementaryParameters -/
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

/- ElementaryH2 -/
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

/- ElementaryDimension -/
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
end BinaryFactor.Elementary
end

/- CharacterBasis -/
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

/- AdaptedCoordinates -/
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

/- OrbitUp -/
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

/- Rigid -/
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

/- Mixed -/
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

/- Conjugate -/
section
namespace OrbitUp
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

/- LargeMove -/
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

/- RankCount -/
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

/- RectangleRank -/
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

/- RankMinor -/
section
namespace OrbitUp
theorem select_independent {ι M : Type} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : ι → M) (k : ℕ) (hk : k ≤ Module.finrank K (Submodule.span K (Set.range f))) :
    ∃ e : Fin k ↪ ι, LinearIndependent K (f ∘ e) := by
  classical
  obtain ⟨T, hsub, hcard, _, hind⟩ := Submodule.exists_finset_span_eq_linearIndepOn K (Set.range f)
  let j : Fin k ↪ T := (Fin.castLEEmb (hk.trans_eq hcard.symm)).trans T.equivFin.symm.toEmbedding
  have hv (i : Fin k) : ∃ z : ι, f z = (j i).val := hsub (j i).property
  choose z hz using hv
  have hfamily : (f ∘ z) = fun i => (j i).val := funext hz
  have hli : LinearIndependent K (f ∘ z) := by
    rw [hfamily]
    exact hind.comp j j.injective
  exact ⟨⟨z,fun i l h => hli.injective (congrArg f h)⟩, hli⟩
theorem exists_unit_minor {d t k : ℕ} (A : Matrix (Fin d) (Fin t) K) (hk : k ≤ A.rank) :
    ∃ rows : Fin k ↪ Fin d, ∃ cols : Fin k ↪ Fin t, IsUnit (A.submatrix rows cols) := by
  classical
  obtain ⟨rows, hr⟩ := select_independent A.row k (A.rank_eq_finrank_span_row ▸ hk)
  let B := A.submatrix rows id
  have hrows : LinearIndependent K B.row := hr
  have hcol : k ≤ Module.finrank K (Submodule.span K (Set.range B.col)) := by
    rw [← B.rank_eq_finrank_span_cols, hrows.rank_matrix, Fintype.card_fin]
  obtain ⟨cols, hc⟩ := select_independent B.col k hcol
  exact ⟨rows,cols,Matrix.linearIndependent_cols_iff_isUnit.mp hc⟩
end OrbitUp
end

/- CoordinateSupport -/
section
namespace OrbitUp
theorem information_coordinates {J : Type} [Fintype J] (W : Submodule K (J→K)) :
    ∃p : Fin (Module.finrank K W) ↪ J,Function.Injective (fun w : W=>fun i=>w.val (p i)) := by
  classical
  let B := Module.finBasis K W
  let r := Module.finrank K W
  let A : Matrix (Fin r) J K := fun i j=>(B i).val j
  have hi : LinearIndependent K A.row := B.linearIndependent.map' W.subtype W.ker_subtype
  have hspan : r ≤ Module.finrank K (Submodule.span K (Set.range A.col)) := by
    rw [← A.rank_eq_finrank_span_cols,hi.rank_matrix,Fintype.card_fin]
  obtain ⟨p,hp⟩ := select_independent A.col r hspan
  let M := A.submatrix id p
  have unit : IsUnit M := Matrix.linearIndependent_cols_iff_isUnit.mp hp
  have coords (w : W) : Matrix.vecMul (fun i=>B.repr w i) M = fun i=>w.val (p i) := by
    funext j
    have h := congrArg (fun z : W=>z.val (p j)) (B.sum_repr w)
    change (∑ i,(B.repr w) i * (B i).val (p j))=w.val (p j)
    simpa only [Submodule.coe_sum,SetLike.val_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using h
  refine ⟨p,?_⟩
  intro w z eq
  have h := Matrix.vecMul_injective_iff_isUnit.mpr unit ((coords w).trans (eq.trans (coords z).symm))
  exact B.repr.injective (Finsupp.ext (fun i=>congrFun h i))
theorem sum_supported_finrank {I J : Type} [Fintype I] [Fintype J] (W : Submodule K (J→K))
    (U : I→Submodule K (J→K)) (incl : ∀i,U i ≤ W) (touch : J→Finset I) (h : ℕ)
    (deg : ∀j,(touch j).card ≤ h)
    (support : ∀i (w:U i) j,i∉touch j→w.val j=0) :
    (∑i,Module.finrank K (U i)) ≤ h*Module.finrank K W := by
  classical
  obtain ⟨p,hp⟩ := information_coordinates W
  let r := Module.finrank K W
  have bound (i : I) : Module.finrank K (U i) ≤ (Finset.univ.filter (fun j:Fin r=>i∈touch (p j))).card := by
    let S := {j : Fin r // i∈touch (p j)}
    let f : U i →ₗ[K] (S→K) :=
      { toFun := fun v j=>v.val (p j.val),map_add' := fun _ _=>rfl,map_smul' := fun _ _=>rfl }
    have inj : Function.Injective f := by
      intro x y eq
      let im (v : U i) : W := ⟨v.val,incl i v.property⟩
      have hx : im x=im y := hp (funext (fun j => by
        by_cases hj : i∈touch (p j)
        · exact congrFun eq ⟨j,hj⟩
        · exact (support i x (p j) hj).trans (support i y (p j) hj).symm))
      exact Subtype.ext (congrArg (fun o : W=>o.val) hx)
    have hs := LinearMap.finrank_le_finrank_of_injective inj
    simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,
      S,Fintype.card_subtype,Finset.card_filter] using hs
  calc
    _ ≤ ∑i,(Finset.univ.filter (fun j:Fin r=>i∈touch (p j))).card := Finset.sum_le_sum (fun i _=>bound i)
    _ = ∑j : Fin r,(touch (p j)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp [Finset.sum_ite]
    _ ≤ ∑_j : Fin r,h := Finset.sum_le_sum (fun j _=>deg _)
    _ = _ := by simp [r,Nat.mul_comm]
end OrbitUp
end

/- ExteriorSupport -/
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
theorem exterior_support_bound {I J : Type} [Fintype I] [Fintype J] [DecidableEq J] (idx : I↪J)
    (F : Submodule K (Face J 2→K)) (W : Submodule K (Face J 3→K))
    (span : ∀i,(F.map (exteriorStep (idx i))) ≤ W) :
    Fintype.card I*Module.finrank K F ≤ 2*Module.finrank K F+3*Module.finrank K W := by
  classical
  let T (i : I) := (exteriorStep (idx i)).comp F.subtype
  let R (i : I) := LinearMap.range (T i)
  let N (i : I) := (LinearMap.ker (T i)).map F.subtype
  let touch {p : ℕ} (s : Face J p) := Finset.univ.filter (fun i : I=>idx i∈s.val)
  have touch_le {p : ℕ} (s : Face J p) : (touch s).card ≤ p := by
    let f (i : ↥(touch s)) : ↥s.val := ⟨idx i.val,(Finset.mem_filter.mp i.property).2⟩
    have inj : Function.Injective f := fun x y h=>Subtype.ext (idx.injective (congrArg Subtype.val h))
    simpa only [Fintype.card_coe,s.property] using Fintype.card_le_of_injective f inj
  have rn (i) : R i ≤ W := by
    rintro _ ⟨f,rfl⟩
    exact span i ⟨f.val,f.property,rfl⟩
  have out := sum_supported_finrank W R rn (touch (p:=3)) 3 touch_le (by
    intro i v s hi
    obtain ⟨f,hf⟩ := v.property
    rw [←hf]
    exact exteriorStep_out _ _ _ (by simpa [touch] using hi))
  have nin (i) : N i ≤ F := by rintro _ ⟨x,_,rfl⟩;exact x.property
  have nulls := sum_supported_finrank F N nin (touch (p:=2)) 2 touch_le (by
    intro i v s hi
    obtain ⟨x,hx,eq⟩ := v.property
    have hmiss : idx i∉s.val := by simpa [touch] using hi
    let t : Face J 3 := ⟨insert (idx i) s.val,by rw [Finset.card_insert_of_notMem hmiss,s.property]⟩
    rw [← eq]
    have hh : (T i x) t=0 := congrFun (show T i x=0 from hx) t
    exact (exteriorStep_insert _ _ _ hmiss).symm.trans hh)
  have rank (i : I) : Module.finrank K (R i) + Module.finrank K (N i)=Module.finrank K F := by
    have f := Submodule.equivMapOfInjective F.subtype F.subtype_injective (LinearMap.ker (T i))
    change Module.finrank K (LinearMap.range (T i))+Module.finrank K ((LinearMap.ker (T i)).map F.subtype)=_
    rw [←f.finrank_eq]
    exact LinearMap.finrank_range_add_finrank_ker _
  have sum : (∑i,Module.finrank K (R i))+(∑i,Module.finrank K (N i))= Fintype.card I*Module.finrank K F := by
    rw [←Finset.sum_add_distrib];simp [rank]
  omega
end OrbitUp
end

/- PairCup -/
section
namespace BinaryFactor.Elementary
open OrbitUp Cocycle Erdos1160Growth.LowerTriangularUpper
abbrev Pairs (d : ℕ) := Face (Fin d) 2 → Bit
abbrev Triples (d : ℕ) := Face (Fin d) 3 → Bit
def pair {d : ℕ} (i j : Fin d) (h : i ≠ j) : Face (Fin d) 2 := ⟨{i,j},Finset.card_pair h⟩
def pairParams (d : ℕ) : Pairs d →ₗ[Bit] Coeffs d where
  toFun w l := match l with
    | .inl ⟨i,j⟩ => w (pair i ⟨j.val,lt_trans j.isLt i.isLt⟩ (Fin.ne_of_gt j.isLt))
    | .inr _ => 0
  map_add' x y := by funext l;cases l <;> rfl
  map_smul' c x := by funext l;cases l <;> rfl
def pairClass (d : ℕ) : Pairs d →ₗ[Bit] H₂ (Vectors d) := (coeffMap d).comp (pairParams d)
def unitVec {d : ℕ} (i : Fin d) : Vectors d := Multiplicative.ofAdd (bit i)
private theorem eval_pair_low {d : ℕ} (w : Pairs d) {i j : Fin d} (h : j < i) :
    (coeffCycles d (pairParams d w)).val.val (unitVec i) (unitVec j) = w (pair i j h.ne') := by
  let l : Slot d := .inl ⟨i,⟨j.val,h⟩⟩
  exact congrFun (form_at_slot (expand (pairParams d w)) l) 0
private theorem eval_pair_high {d : ℕ} (w : Pairs d) {i j : Fin d} (h : i < j) :
    (coeffCycles d (pairParams d w)).val.val (unitVec i) (unitVec j) = 0 :=
  congrFun (form_above (expand (pairParams d w)) _ _ h) 0
theorem antisym_pair {d : ℕ} (w : Pairs d) (i j : Fin d) (h : i≠j) :
    antisym₂ ((coeffCycles d (pairParams d w)).val.val) (unitVec i) (unitVec j) = w (pair i j h) := by
  rcases lt_or_gt_of_ne h with hij|hji
  · rw [antisym₂,eval_pair_high _ hij,eval_pair_low _ hij,zero_add]
    congr 1
    exact Subtype.ext (Finset.pair_comm _ _)
  · rw [antisym₂,eval_pair_high _ hji,eval_pair_low _ hji,add_zero]
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
noncomputable def evalTriples (d : ℕ) : (Fin d→Fin d→Fin d→Bit) →ₗ[Bit] Triples d where
  toFun θ s := θ (tripleRep s).i (tripleRep s).j (tripleRep s).k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def tripleProj (d : ℕ) : (C₃ (Vectors d) ⧸ boundaries₃ (Vectors d)) →ₗ[Bit] Triples d :=
  (evalTriples d).comp (exteriorProj unitVec)
set_option maxHeartbeats 3000000 in
theorem tripleProj_pair {d : ℕ} (a : characters (Vectors d)) (i : Fin d)
    (ha : ∀j,a.val (unitVec j) = if j=i then 1 else 0) (w : Pairs d) :
    tripleProj d (cupClass a (pairClass d w)) = exteriorStep i w := by
  change evalTriples d (exteriorProj unitVec ((boundaries₃ (Vectors d)).mkQ (cupRaw a.val ((coeffCycles d (pairParams d w)).val.val))))=_
  rw [exteriorProj_cup]
  funext s
  let t := tripleRep s
  change wedgeCoeffs (fun j=>(a.val (unitVec j))) (fun j k=>antisym₂ ((coeffCycles d (pairParams d w)).val.val) (unitVec j) (unitVec k)) t.i t.j t.k = exteriorStep i w s
  rw [wedgeCoeffs,antisym_pair _ _ _ t.hjk,antisym_pair _ _ _ t.hik,antisym_pair _ _ _ t.hij,ha,ha,ha]
  rcases eq_or_ne t.i i with h|h
  · subst i
    simp only [if_true,if_neg t.hij.symm,if_neg t.hik.symm,one_mul,zero_mul,add_zero]
    have e : s.val = insert t.i (pair t.j t.k t.hjk).val := t.support
    have hs : s=⟨insert t.i (pair t.j t.k t.hjk).val,by rw [← e];exact s.property⟩ := Subtype.ext e
    exact ((exteriorStep_insert t.i w (pair t.j t.k t.hjk) (by simp [pair,t.hij,t.hik])).symm).trans (congrArg ((exteriorStep t.i) w) hs.symm)
  rcases eq_or_ne t.j i with h'|h'
  · subst i
    simp only [if_true,if_neg h,if_neg t.hjk.symm,one_mul,zero_mul,zero_add,add_zero]
    have e : s.val = insert t.j (pair t.i t.k t.hik).val := t.support.trans (Finset.insert_comm ..)
    have hs : s=⟨insert t.j (pair t.i t.k t.hik).val,by rw [← e];exact s.property⟩ := Subtype.ext e
    exact ((exteriorStep_insert t.j w (pair t.i t.k t.hik) (by simp [pair,t.hij.symm,t.hjk])).symm).trans (congrArg ((exteriorStep t.j) w) hs.symm)
  rcases eq_or_ne t.k i with h''|h''
  · subst i
    simp only [if_true,if_neg h,if_neg h',one_mul,zero_mul,zero_add]
    have e : s.val = insert t.k (pair t.i t.j t.hij).val := by rw [t.support];ext; simp [pair];tauto
    have hs : s=⟨insert t.k (pair t.i t.j t.hij).val,by rw [← e];exact s.property⟩ := Subtype.ext e
    exact ((exteriorStep_insert t.k w (pair t.i t.j t.hij) (by simp [pair,t.hik.symm,t.hjk.symm])).symm).trans (congrArg ((exteriorStep t.k) w) hs.symm)
  simp only [if_neg h,if_neg h',if_neg h'',zero_mul,zero_add]
  exact (exteriorStep_out _ _ _ (by rw [t.support];simp [Ne.symm h,Ne.symm h',Ne.symm h''])).symm
end BinaryFactor.Elementary
end

/- FixedCupDirections -/
section
namespace BinaryFactor.Elementary
open OrbitUp Cocycle
variable {Y : Type} [Group Y] [Finite Y] {d r : ℕ}
noncomputable def cupTuple (a : Fin r→characters Y) :
    H₂ Y →ₗ[Bit] (Fin r→C₃ Y ⧸ boundaries₃ Y) :=
  LinearMap.pi (fun i=>cupClass (a i))
theorem pair_kernel_shadow (f : Y→*Vectors d) (idx : Fin r↪Fin d)
    (a : Fin r→characters (Vectors d)) (ha : ∀i j,(a i).val (unitVec j)=if j=idx i then 1 else 0) :
    let H := (cupTuple (fun i=>characterPull f (a i))).comp ((inflate₂ f).comp (pairClass d))
    (r-2)*Module.finrank Bit (LinearMap.ker H) ≤ 3*Module.finrank Bit (LinearMap.ker (inflate₃ f)) := by
  classical
  dsimp only
  let H := (cupTuple (fun i=>characterPull f (a i))).comp ((inflate₂ f).comp (pairClass d))
  let F := LinearMap.ker H
  let W := (LinearMap.ker (inflate₃ f)).map (tripleProj d)
  have inside (i : Fin r) : F.map (exteriorStep (idx i)) ≤ W := by
    rintro _ ⟨w,hw,rfl⟩
    refine ⟨cupClass (a i) (pairClass d w),?_,tripleProj_pair _ _ (ha i) _⟩
    change inflate₃ f (cupClass (a i) (pairClass d w))=0
    rw [cup_natural]
    exact congrFun (show H w=0 from hw) i
  have h := exterior_support_bound idx F W inside
  rw [Fintype.card_fin] at h
  change r*Module.finrank Bit F ≤ 2*Module.finrank Bit F+3*Module.finrank Bit W at h
  have z := Submodule.finrank_map_le (tripleProj d) (LinearMap.ker (inflate₃ f))
  change Module.finrank Bit W ≤ _ at z
  change (r-2)*Module.finrank Bit F ≤ _
  by_cases hr : 2 ≤ r
  · have eq := Nat.sub_mul r 2 (Module.finrank Bit F)
    omega
  · simp [Nat.sub_eq_zero_of_le (by omega : r ≤ 2)]
theorem fixed_directions_density {S : Type} [AddCommGroup S] [Module Bit S] [Finite S]
    (f : Y→*Vectors d) (idx : Fin r↪Fin d) (a : Fin r→characters (Vectors d))
    (ha : ∀i j,(a i).val (unitVec j)=if j=idx i then 1 else 0)
    (sample : S→ₗ[Bit] H₂ Y) (pairs : Pairs d→ₗ[Bit] S)
    (agree : sample.comp pairs=(inflate₂ f).comp (pairClass d))
    (baseClass : H₂ Y) (hr : 2 < r) (K₀ : ℕ)
    (hK : Module.finrank Bit (LinearMap.ker (inflate₃ f)) ≤ K₀) :
    Nat.card {x : S // ∀i,cupClass (characterPull f (a i)) (baseClass+sample x)=0} * 2^(d.choose 2)
     ≤ Nat.card S * 2^(3*K₀/(r-2)) := by
  classical
  let C := cupTuple (fun i=>characterPull f (a i))
  let T := C.comp sample
  let U := T.comp pairs
  let P := {x : S // ∀i,cupClass (characterPull f (a i)) (baseClass+sample x)=0}
  have loss := pair_kernel_shadow f idx a ha
  change (r-2)*Module.finrank Bit (LinearMap.ker (C.comp ((inflate₂ f).comp (pairClass d)))) ≤ _ at loss
  rw [←agree] at loss
  change (r-2)*Module.finrank Bit (LinearMap.ker U) ≤ _ at loss
  have hk : Module.finrank Bit (LinearMap.ker U)≤ 3*K₀/(r-2) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < r-2)).2
    rw [Nat.mul_comm]
    exact loss.trans (Nat.mul_le_mul_left _ hK)
  have hu := LinearMap.finrank_range_add_finrank_ker U
  have ht := LinearMap.finrank_range_add_finrank_ker T
  have hrt : Module.finrank Bit (LinearMap.range U) ≤ Module.finrank Bit (LinearMap.range T) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have dimP : Module.finrank Bit (Pairs d)=d.choose 2 := by
    change Module.finrank Bit (Face (Fin d) 2→Bit)=_
    rw [Module.finrank_fintype_fun_eq_card,Fintype.card_finset_len,Fintype.card_fin]
  rw [dimP] at hu
  have expbd : Module.finrank Bit (LinearMap.ker T)+d.choose 2 ≤ Module.finrank Bit S + 3*K₀/(r-2) := by omega
  have injbd : Nat.card P ≤ Nat.card (LinearMap.ker T) := by
    by_cases non : Nonempty P
    · let y := Classical.choice non
      have cy (x : P) : C (baseClass+sample x.val)=0 := funext x.property
      let code (x : P) : LinearMap.ker T := ⟨x.val-y.val,by
        rw [LinearMap.mem_ker,map_sub,sub_eq_zero]
        exact add_left_cancel (a:=C baseClass) ((map_add C _ _).symm.trans
          ((cy x).trans ((cy y).symm.trans (map_add C _ _))))⟩
      exact Nat.card_le_card_of_injective code (fun x z h=>Subtype.ext (sub_left_inj.mp (congrArg Subtype.val h)))
    · haveI : IsEmpty P := not_nonempty_iff.mp non
      simp
  change Nat.card P * _ ≤ _
  apply (Nat.mul_le_mul_right _ injbd).trans
  rw [Module.natCard_eq_pow_finrank (K:=Bit) (V:=LinearMap.ker T),Module.natCard_eq_pow_finrank (K:=Bit) (V:=S),Nat.card_zmod,←pow_add,←pow_add]
  exact Nat.pow_le_pow_right (by decide) expbd
end BinaryFactor.Elementary
end

/- FixedAffineCup -/
section
namespace BinaryFactor.Elementary
open Cocycle
variable {Y : Type} [Group Y] [Finite Y] {d r : ℕ}
theorem fixed_affine_cup (f : Y→*Vectors d) (a : Fin r→characters (Vectors d))
    (ha : LinearIndependent Bit a) (baseClass : H₂ Y) (hr : 2 < r) (K₀ : ℕ)
    (hK : Module.finrank Bit (LinearMap.ker (inflate₃ f)) ≤ K₀) :
    Nat.card {x : LinearMap.range (inflate₂ f) //
      ∀i,cupClass (characterPull f (a i)) (baseClass+x.val)=0} * 2^(d.choose 2)
      ≤ Nat.card (LinearMap.range (inflate₂ f)) * 2^(3*K₀/(r-2)) := by
  classical
  obtain ⟨φ,idx,hφ⟩ := adapted_coordinate_iso a ha
  let g := φ.symm.toMonoidHom.comp f
  let b (i : Fin r) := characterPull φ.toMonoidHom (a i)
  have hb (i : Fin r) (j : Fin d) : (b i).val (unitVec j)=if j=idx i then 1 else 0 := by
    change (a i).val (φ (unitVec j))=_
    rw [hφ]
    simp only [unitVec,Erdos1160Growth.LowerTriangularUpper.bit,Pi.single_apply]
    split <;> rename_i h <;> simp_all
  have chars (i : Fin r) : characterPull g (b i)=characterPull f (a i) := by
    apply Subtype.ext;funext x
    change (a i).val (φ (φ.symm (f x)))=_
    rw [φ.apply_symm_apply]
    rfl
  let I := LinearMap.range (inflate₂ f)
  let pre := (inflate₂ φ.symm.toMonoidHom).comp (pairClass d)
  let pairs : Pairs d→ₗ[Bit] I := (inflate₂ f).rangeRestrict.comp pre
  have agree : I.subtype.comp pairs=(inflate₂ g).comp (pairClass d) := by
    have eq : inflate₂ g=(inflate₂ f).comp (inflate₂ φ.symm.toMonoidHom) := by
      apply LinearMap.ext;intro z
      induction z using Submodule.Quotient.induction_on with
      | _ v => rfl
    rw [eq];rfl
  have hk : Module.finrank Bit (LinearMap.ker (inflate₃ g)) ≤ K₀ := by
    rw [show inflate₃ g=(inflate₃ f).comp (inflate₃ φ.symm.toMonoidHom) from inflate₃_comp ..]
    let A := inflate₃ f
    let B := inflate₃ φ.symm.toMonoidHom
    let X := LinearMap.ker (A.comp B)
    let t : X →ₗ[Bit] LinearMap.ker A := (B.comp X.subtype).codRestrict _ (fun x=>x.property)
    have inj : Function.Injective t := fun x y eq=>Subtype.ext (inflate₃_iso_inj φ.symm (congrArg Subtype.val eq))
    exact (LinearMap.finrank_le_finrank_of_injective inj).trans hK
  letI : Finite (H₂ Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have res := fixed_directions_density g idx b hb I.subtype pairs agree baseClass hr K₀ hk
  simpa only [chars,Submodule.subtype_apply] using res
end BinaryFactor.Elementary
end

/- CupRegular -/
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

/- AdmissibleAffine -/
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

/- CupSingle -/
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

/- Erdos1160Tables -/
section
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
end Erdos1160.CentralLifts
end

/- QuotientFiber -/
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

/- InflationTower -/
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

/- FixedFrattiniCup -/
section
namespace BinaryFactor.Elementary
open Cocycle
theorem vectors_card (d : ℕ) : Nat.card (Vectors d)=2^d := by
  change Nat.card (Fin d→Bit)=_
  rw [Nat.card_fun,Nat.card_zmod,Nat.card_fin]
theorem vectors_char_rank (d : ℕ) : r₁ (Vectors d)=d := by
  change Module.finrank Bit (characters (Vectors d))=_
  rw [(characterDual d).finrank_eq,Subspace.dual_finrank_eq,Module.finrank_fin_fun]
private theorem independent_subspace_basis {U : Type} [AddCommGroup U] [Module Bit U] (A : Submodule Bit U) {ι : Type} (B : Module.Basis ι Bit A) : LinearIndependent Bit (fun i=>(B i).val) :=
  B.linearIndependent.map' A.subtype A.ker_subtype
set_option maxHeartbeats 500000 in


theorem frattini_fixed_cup {Y : Type} [Group Y] [Finite Y] {d n r : ℕ}
    (hY : Nat.card Y=2^(d+n)) (f : Y→*Vectors d) (hf : Function.Surjective f)
    (hΦ : f.ker ≤ frattini Y) (A : Submodule Bit (characters Y)) (hA : Module.finrank Bit A=r)
    (baseClass : H₂ Y) (hr : 2 < r) :
    Nat.card {x : LinearMap.range (inflate₂ f) // ∀a : A,cupClass a.val (baseClass+x.val)=0} * 2^(d.choose 2)
    ≤ Nat.card (LinearMap.range (inflate₂ f))*2^(3*(d*n+(d*(d-1)/2+d)-r₂ Y)/(r-2)) := by
  classical
  letI : Finite (H₂ Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  obtain ⟨bound,rank⟩ := inflation_tower (vectors_card d) n hY f hf hΦ
  rw [vectors_char_rank,elementary_r₂,Nat.mul_comm n d] at bound
  have kerBd : Module.finrank Bit (LinearMap.ker (inflate₃ f))≤ d*n+(d*(d-1)/2+d)-r₂ Y := by omega
  let F := characterPull f
  have inj : Function.Injective F := by
    intro a b eq
    apply Subtype.ext;funext x
    obtain ⟨y,rfl⟩ := hf x
    exact congrArg (fun χ : characters Y=>χ.val y) eq
  have sur : Function.Surjective F := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rank.symm).1 inj
  let B := (Module.finBasis Bit A).reindex (finCongr hA)
  choose a ha using fun i=>sur (B i).val
  have independent : LinearIndependent Bit a := by
    apply LinearIndependent.of_comp F
    have eq : F ∘ a = fun i=>(B i).val := funext ha
    rw [eq]
    exact independent_subspace_basis A B
  have res := fixed_affine_cup f a independent baseClass hr _ kerBd
  let X := {x : LinearMap.range (inflate₂ f) // ∀z : A,cupClass z.val (baseClass+x.val)=0}
  let T := {x : LinearMap.range (inflate₂ f) // ∀i,cupClass (characterPull f (a i)) (baseClass+x.val)=0}
  let incl (x : X) : T := ⟨x.val,fun i=>by change cupClass (F (a i)) _=0;rw [ha];exact x.property (B i)⟩
  exact (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective incl (fun x z h=>Subtype.ext (congrArg (fun v:T=>v.val) h)))).trans res
end BinaryFactor.Elementary
end

/- IndependentFrames -/
section
namespace BinaryFactor
private def frameProduct (b r : ℕ) : ℕ := ∏i ∈ Finset.range r,(b-2^i)
private lemma product_le (b r : ℕ) : frameProduct b r ≤ b^r := by
  have h := Finset.prod_le_prod' (s:=Finset.range r) (f:=fun i=>b-2^i) (g:=fun _=>b)
    (fun i _=>Nat.sub_le _ _)
  simpa [frameProduct] using h
private lemma product_loss (b r : ℕ) (h : 2^r ≤ b) :
    b^r*b ≤ frameProduct b r*b+(2^r-1)*b^r := by
  induction r with
  | zero => simp [frameProduct]
  | succ r ih =>
    have hr : 2^r ≤ b := (Nat.pow_le_pow_right (by decide) (Nat.le_succ r)).trans h
    have hb := Nat.sub_add_cancel hr
    have hp := product_le b r
    have hi := Nat.mul_le_mul_right b (ih hr)
    have hu := Nat.mul_le_mul_right (2^r*b) hp
    have he₁ := Nat.sub_add_cancel (show 1 ≤ 2^r from Nat.two_pow_pos _)
    have he₂ := Nat.sub_add_cancel (show 1 ≤ 2^(r+1) from Nat.two_pow_pos _)
    have hfac : frameProduct b (r+1)=frameProduct b r*(b-2^r) := Finset.prod_range_succ ..
    simp only [hfac,pow_succ]
    rw [pow_succ] at he₂
    nlinarith only [hi,hu,congrArg (fun t=>t*(frameProduct b r*b)) hb,
      congrArg (fun t=>t*(b^r*b)) he₁,congrArg (fun t=>t*(b^r*b)) he₂]
lemma frame_quarter (k r : ℕ) (hr : r ≤ k) :
    2^(k*r) ≤ 4*(∏i : Fin r,(2^k-2^i.val)) := by
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ=>2^k-2^i) r]
  change 2^(k*r) ≤ 4*frameProduct (2^k) r
  rw [pow_mul]
  cases r with
  | zero => simp [frameProduct]
  | succ n =>
    let b := 2^k
    have hd : 2^n*2 ≤ b := by simpa only [pow_succ] using (Nat.pow_le_pow_right (n:=2) (by decide) hr)
    have hl := product_loss b n (by omega)
    have hx := Nat.sub_add_cancel (show 1 ≤ 2^n from Nat.two_pow_pos _)
    have hh : b^n*b ≤ 2*(frameProduct b n)*b := by
      nlinarith only [hl,Nat.mul_le_mul_right (b^n) hd,congrArg (fun t=>t*b^n) hx]
    have hb : 0 < b := by dsimp [b];positivity
    have half : b^n ≤ 2*frameProduct b n := (Nat.le_of_mul_le_mul_right hh hb)
    have step : b ≤ 2*(b-2^n) := by omega
    have hprod := Nat.mul_le_mul half step
    have hfac : frameProduct b (n+1)=frameProduct b n*(b-2^n) := Finset.prod_range_succ ..
    change b^(n+1) ≤ _
    rw [pow_succ,hfac]
    nlinarith only [hprod]
end BinaryFactor
end

/- FrameIncidence -/
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

/- CupAnnihilator -/
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

/- CupUnion -/
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

/- SuXia55 -/
section
namespace BinaryFactor.Elementary
open Cocycle
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
end BinaryFactor.Elementary
end

/- CollapseLift -/
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

/- TrimRelators -/
section
namespace Erdos1160.CentralLifts.Survival
abbrev Twist (r : ℕ) := {c : Fin r → Fin 2 // c ≠ 0}
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
theorem finite_short {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) [Finite (Grp R)] :
    Finite (Grp (shortRel R c)) := by
  let _ := finite_lift R c.val (by decide)
  exact Finite.of_surjective _ (contractShort_surj R c)
theorem card_short {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) [Finite (Grp R)] :
    Nat.card (Grp (shortRel R c)) ≤ Nat.card (Grp R)*2 := by
  let _ := finite_lift R c.val (by decide)
  exact (Nat.card_le_card_of_surjective _ (contractShort_surj R c)).trans (card_lift R c.val (by decide))
end Erdos1160.CentralLifts.Survival
end

/- ScalarChild -/
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
theorem child_cover (R : Fin r → FreeGroup (Fin d)) [Finite (Grp R)] (g : Grp R →* H)
    (hg : Function.Surjective g) (hcard : Nat.card (Grp R) < Nat.card G)
    (q : G →* H) (hq : Function.Surjective q) (hΦ : q.ker ≤ frattini G)
    (u : G) (ho : orderOf u=2) (hz : u ∈ Subgroup.center G) (hker : q.ker = Subgroup.zpowers u) :
    ∃ c : Twist r, ∃ v : Grp (shortRel R c) →* G, Function.Surjective v :=
  child_cover_of_no_epi R g hg (fun v hv => hcard.not_ge (Nat.card_le_card_of_surjective v hv))
    q hq hΦ u ho hz hker
end Erdos1160.CentralLifts.Survival
end

/- DescendantCount -/
section
namespace Erdos1160.CentralLifts.Survival
open CategoryTheory
def RelDim (d r : ℕ) : ℕ → ℕ
  | 0 => r
  | j+1 => RelDim d r j+d
def ChildCodes (d r : ℕ) : ℕ → Type
  | 0 => Unit
  | j+1 => ChildCodes d r j × Twist (RelDim d r j)
theorem rel_dim (d r j : ℕ) : RelDim d r j=r+j*d := by
  induction j with
  | zero => simp [RelDim]
  | succ j ih => simp [RelDim,ih,Nat.succ_mul,Nat.add_assoc]
noncomputable def run {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) :
    {j : ℕ} → ChildCodes d r j → Fin (RelDim d r j) → FreeGroup (Fin d)
  | 0, _ => R
  | _+1,c => shortRel (run R c.1) c.2
theorem run_finite {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) [Finite (Grp R)]
    (j : ℕ) (c : ChildCodes d r j) : Finite (Grp (run R c)) := by
  induction j with
  | zero => exact inferInstanceAs (Finite (Grp R))
  | succ j ih =>
    let _ := ih c.1
    exact finite_short (run R c.1) c.2
theorem run_card {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) [Finite (Grp R)]
    (j : ℕ) (c : ChildCodes d r j) : Nat.card (Grp (run R c)) ≤ Nat.card (Grp R)*2^j := by
  induction j with
  | zero => rw [pow_zero,Nat.mul_one]; exact Nat.le_refl _
  | succ j ih =>
    let _ := run_finite R j c.1
    exact (card_short (run R c.1) c.2).trans ((Nat.mul_le_mul_right 2 (ih c.1)).trans (by rw [pow_succ,Nat.mul_assoc]))
variable {d r m : ℕ} {Q G : Type} [Group Q] [Group G] [Finite Q] [Finite G]
omit [Finite Q] in
theorem frattini_cover (R : Fin r → FreeGroup (Fin d)) [Finite (Grp R)] (hR : Nat.card (Grp R)=2^m)
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
    let _ := run_finite R j c
    have hc : Nat.card (Grp (run R c)) < Nat.card G := by
      have h := run_card R j c
      rw [hR,←pow_add] at h
      rw [hG]
      exact h.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    have hk : π.ker ≤ frattini G := (QuotientGroup.ker_mk' N).le.trans (hN.trans hΦ)
    obtain ⟨t,w,hw⟩ := child_cover (run R c) g hg hc π hπ hk u ho hz (QuotientGroup.ker_mk' N)
    exact ⟨(c,t),w,hw⟩
end Erdos1160.CentralLifts.Survival
end

/- JacobiCount -/
section
namespace Erdos1160.DeepJacobi
abbrev Bit := ZMod 2
abbrev V (s : ℕ) := Fin s → Bit
abbrev W (q s : ℕ) := V q × V s
abbrev Pair (n : ℕ) := (i : Fin n) × Fin i.val
abbrev Old (q n : ℕ) := Pair q ⊕ (Fin q × Fin n)
abbrev Array (q n s : ℕ) := (Old q n → W q s) × (Pair n → W q s)
abbrev Code (q n s : ℕ) := (Old q n → W q s) × (Pair n → V s)
variable {q n s : ℕ}
def encode (a : Array q n s) : Code q n s := (a.1, fun ij => (a.2 ij).2)
def mixed (a : Array q n s) (c : Fin q) (i : Fin n) : W q s := a.1 (.inr (c,i))
def low (ij : Pair n) : Fin n := ⟨ij.2.val, lt_trans ij.2.isLt ij.1.isLt⟩
def compatible (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    (a : Array q n s) : Prop :=
  ∀ ij : Pair n, ∀ c : Fin q, core (a.2 ij) c =
    outside ij.1 (mixed a c (low ij)) - outside (low ij) (mixed a c ij.1)
lemma pivot_separates (core : W q s →+ V q)
    (h : Function.Injective (fun v : V q => core (v,0)))
    {u v : W q s} (hs : u.2 = v.2) (hc : core u = core v) : u = v := by
  apply Prod.ext _ hs
  apply h
  have hu : u = (u.1,0) + (0,u.2) := by simp
  have hv : v = (v.1,0) + (0,v.2) := by simp
  calc
    core (u.1,0) = core u - core (0,u.2) := by conv => rhs; rw [hu,map_add]; simp
    _ = core v - core (0,v.2) := by rw [hc,hs]
    _ = core (v.1,0) := by conv => lhs; rw [hv,map_add]; simp
theorem recover (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    (h : Function.Injective (fun v : V q => core (v,0)))
    {a b : Array q n s} (ha : compatible core outside a) (hb : compatible core outside b)
    (e : encode a = encode b) : a = b := by
  have hOld : a.1 = b.1 := congrArg (fun w : Code q n s => w.1) e
  have hRest : ∀ ij, (a.2 ij).2 = (b.2 ij).2 := congrFun (congrArg (fun w : Code q n s => w.2) e)
  apply Prod.ext hOld
  funext ij
  apply pivot_separates core h (hRest ij)
  funext c
  rw [ha ij c, hb ij c]
  simp only [mixed,hOld]
theorem card_saved (q n s : ℕ) :
    Nat.card (Code q n s) * 2^(q*(n*(n-1)/2)) = Nat.card (Array q n s) := by
  change Nat.card ((Old q n → W q s) × (Pair n → V s)) * _ =
    Nat.card ((Old q n → W q s) × (Pair n → W q s))
  rw [Nat.card_prod,Nat.card_prod,Nat.mul_assoc]
  apply congrArg (Nat.card (Old q n → W q s) * ·)
  simp only [W,V,Nat.card_fun,Nat.card_prod,Nat.card_fin,Nat.card_zmod,
    ← pow_add, ← pow_mul, Erdos1160Growth.SharpFamily.triangular_card n]
  congr 1
  ring
theorem fixed_tensor_count (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    (h : Function.Injective (fun v : V q => core (v,0))) :
    Nat.card {a : Array q n s // compatible core outside a} * 2^(q*(n*(n-1)/2))
      ≤ Nat.card (Array q n s) := by
  have he : Function.Injective (fun a : {a : Array q n s // compatible core outside a} => encode a.val) :=
    fun a b hab => Subtype.ext (recover core outside h a.property b.property hab)
  simpa only [card_saved] using Nat.mul_le_mul_right (2^(q*(n*(n-1)/2))) (Nat.card_le_card_of_injective _ he)
end Erdos1160.DeepJacobi
end

/- ClassThreeJacobi -/
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

/- DetectedTriple -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {G : Type*} [Group G]
lemma lower_map_top {K : Type*} [Group K] (f : G →* K) (hf : Function.Surjective f) (n : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries n).map f = (⊤ : Subgroup K).lowerCentralSeries n := by
  rw [Subgroup.map_lowerCentralSeries,← MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective f hf]
end Erdos1160.DeepJacobi
end

/- IntrinsicTensor -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {G : Type*} [Group G]
abbrev Second (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries 1
def secondBracket (x y : G) : Second G :=
  ⟨⁅x,y⁆,Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩
end Erdos1160.DeepJacobi
end

/- TerminalAlgebra -/
section
namespace FrattiniSurvival
open scoped commutatorElement
private theorem square_commutator {E : Type*} [Group E] (x y : E)
    (hx : x*x ∈ Subgroup.center E) (hc : ⁅x,y⁆ ∈ Subgroup.center E) :
    ⁅x,y⁆ * ⁅x,y⁆=1 := by
  have h : ⁅x*x,y⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp hx y).symm
  rw [commutatorElement_mul_left_eq_conj_mul,Subgroup.mem_center_iff.mp hc x,
    mul_inv_cancel_right] at h
  exact h
theorem derived_square_one {E : Type*} [Group E]
    (hcomm : commutator E ≤ Subgroup.center E) (hsq : ∀ x : E, x*x ∈ Subgroup.center E) :
    ∀ w ∈ commutator E, w*w=1 := by
  let z : Subgroup E := {
    carrier := {w | w ∈ Subgroup.center E ∧ w*w=1}
    one_mem' := ⟨Subgroup.one_mem _,one_mul _⟩
    mul_mem' := by
      rintro u v ⟨hu,hus⟩ ⟨hv,hvs⟩
      refine ⟨Subgroup.mul_mem _ hu hv,?_⟩
      change (u*v)*(u*v)=1
      calc (u*v)*(u*v) = (u*u)*(v*v) := by
             calc (u*v)*(u*v) = u*(v*u)*v := by group
                  _ = u*(u*v)*v := by rw [Subgroup.mem_center_iff.mp hu v]
                  _ = _ := by group
           _ = 1 := by rw [hus,hvs,one_mul]
    inv_mem' := by
      rintro w ⟨hw,hs⟩
      exact ⟨Subgroup.inv_mem _ hw,by change w⁻¹*w⁻¹=1; rw [←mul_inv_rev,hs,inv_one]⟩ }
  have hz : commutator E ≤ z := by
    rw [commutator_eq_closure]
    apply (Subgroup.closure_le _).mpr
    intro _ hg
    obtain ⟨u,v,rfl⟩ := mem_commutatorSet_iff.mp hg
    have hc : ⁅u,v⁆ ∈ Subgroup.center E := hcomm
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v))
    exact ⟨hc,square_commutator u v (hsq u) hc⟩
  intro w hw
  exact (hz hw).2
end FrattiniSurvival
end

/- JacobiTerminal -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
abbrev C₂ := Multiplicative Bit
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
end Erdos1160.DeepJacobi
end

/- DerivedThird -/
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

/- CentralCode -/
section
namespace CentralKernelCount
open scoped commutatorElement
def word {G : Type*} [Group G] {t : ℕ} (y : Fin t → G) (w : List (Fin t)) := (w.map y).prod
end CentralKernelCount
end

/- CentralCoordinates -/
section
namespace CentralKernelCount
open scoped commutatorElement
abbrev BitGroup (d : ℕ) := Multiplicative (Fin d → ZMod 2)
def bit {d : ℕ} (i : Fin d) : BitGroup d := Multiplicative.ofAdd (Pi.single i 1)
theorem word_map {G H : Type*} [Group G] [Group H] {t : ℕ}
    (f : G →* H) (y : Fin t → G) (l : List (Fin t)) :
    f (word y l) = word (fun i => f (y i)) l := by
  induction l with
  | nil => exact f.map_one
  | cons i l h => exact (f.map_mul ..).trans (congrArg _ h)
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

/- PresentationCount -/
section
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
end

/- CentralQuotient -/
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

/- TerminalTree -/
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

/- RelationCharacters -/
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
end Erdos1160.CentralLifts.Survival
end

/- MultiplicatorCount -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi (C₂)
variable {d m : ℕ} {Q : Type} [Group Q] [Finite Q]
noncomputable def relRank (π : FreeGroup (Fin d) →* Q) :=
  Module.finrank (ZMod 2) (Additive (RelCharacters π))
end Erdos1160.CentralLifts.Survival
end

/- UniversalTwoCover -/
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

/- BinaryNucleus -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
variable {d : ℕ} {Q : Type} [Group Q]
noncomputable def nucleusRank (π : FreeGroup (Fin d) →* Q) := Nat.log 2 (Nat.card (binaryThird (Cover π)))
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
lemma nucleus_card [Finite Q] {m : ℕ} (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) : Nat.card (binaryThird (Cover π))=2^(nucleusRank π) := by
  have hc := cover_card π hπ
  rw [hQ,←pow_add] at hc
  let _ : Finite (Cover π) := Nat.finite_of_card_ne_zero (hc ▸ Nat.ne_of_gt (Nat.two_pow_pos _))
  obtain ⟨j,hj⟩ := ((IsPGroup.of_card hc).to_subgroup (binaryThird (Cover π))).exists_card_eq
  rw [nucleusRank,hj,Nat.log_pow (by decide : 1 < 2)]
end Erdos1160.CentralLifts.Survival
end

/- NucleusDescendants -/
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
omit [Finite Q] in
theorem cover_factors_scalar (π : FreeGroup (Fin d) →* Q)
    {Y : Type} [Group Y] (k : Y →* Q) (hker : Nat.card k.ker=2)
    (hc : k.ker ≤ Subgroup.center Y) (F : FreeGroup (Fin d) →* Y) (he : k.comp F=π) :
    ∃ h : Cover π →* Y,h.comp (QuotientGroup.mk' (universalKernel π))=F := by
  have mem (r : π.ker) : F r.val∈k.ker := he ▸ r.property
  let f := (F.comp π.ker.subtype).codRestrict k.ker mem
  let b : k.ker ≃* C₂ := mulEquivOfPrimeCardEq hker (Nat.card_zmod 2)
  let a := b.toMonoidHom.comp f
  have inv (g : FreeGroup (Fin d)) (r : π.ker) : a (conjugateRelation π g r)=a r := by
    apply congrArg b
    apply Subtype.ext
    change F (g*r.val*g⁻¹)=F r.val
    rw [map_mul,map_mul,map_inv,Subgroup.mem_center_iff.mp (hc (mem r)) (F g),mul_inv_cancel_right]
  let c : RelCharacters π := ⟨a,inv⟩
  have hN : universalKernel π ≤ F.ker := by
    rintro _ ⟨r,hr,rfl⟩
    have h := congrArg (fun v : Multiplicative (Adual π) => v.toAdd (Additive.ofMul c)) (show evalHom π r=1 from hr)
    have heq : b (f r)=b 1 := (show a r=1 from h).trans b.map_one.symm
    exact congrArg Subtype.val (b.injective heq)
  exact ⟨QuotientGroup.lift _ F hN,rfl⟩
theorem zero_nucleus_no_descendants (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (hν : nucleusRank π=0)
    {G : Type} [Group G] [Finite G] (j : ℕ) (hG : Nat.card G=2^(m+(j+1)))
    (f : G →* Q) (hf : Function.Surjective f) (hk : f.ker ≤ binaryThird G) : False := by
  have hb : binaryThird (Cover π)=⊥ := (binaryThird (Cover π)).eq_bot_of_card_eq
    (by rw [nucleus_card π hπ hQ,hν,pow_zero])
  obtain ⟨Y,q,k,sq,sk,eq,hY⟩ := one_step_factor hQ j hG f hf
  have hker : Nat.card k.ker=2 := by simpa using ker_card_of_epi Nat.prime_two hY hQ k sk
  have hle := (kernel_image q sq k f eq).trans ((Subgroup.map_mono (f := q) hk).trans (binaryThird_map q sq))
  have hΦ := hle.trans ((binaryThird_le_squares Y).trans (squares_le_frattini hY))
  choose x hx using fun i : Fin d => sk (π (FreeGroup.of i))
  let F := FreeGroup.lift x
  have heq : k.comp F=π := FreeGroup.ext_hom _ _ (fun i => by simpa [F] using hx i)
  have hF := onto_lifts k hΦ F (heq ▸ hπ)
  obtain ⟨h,hh⟩ := cover_factors_scalar π k hker (ThirdLowerCentral.order_two_central _ hker) F heq
  have sh : Function.Surjective h := by
    intro a
    obtain ⟨g,rfl⟩ := hF a
    exact ⟨QuotientGroup.mk' _ g,DFunLike.congr_fun hh g⟩
  have he := binaryThird_map_eq h sh
  rw [hb,Subgroup.map_bot] at he
  have bot := le_antisymm (hle.trans he.ge) bot_le
  simp [bot] at hker
end Erdos1160.CentralLifts.Survival
end

/- ExtensionClasses -/
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

/- TreeMoments -/
section
namespace Erdos1160.DescendantTree
def leaves {X : Type*} (ch : ℕ → X → Finset X) : ℕ → ℕ → X → ℕ
  | 0, _, _ => 1
  | k+1, i, x => ∑ y ∈ ch i x, leaves ch k (i+1) y
def suffixCost (U k : ℕ) := 100 * ∑ j ∈ Finset.range (min k U), j
theorem suffix_succ (U k : ℕ) : suffixCost U (k+1) = suffixCost U k + (if k < U then 100*k else 0) := by
  by_cases hk : k < U
  · simp [suffixCost,hk,min_eq_left (Nat.succ_le_of_lt hk),min_eq_left hk.le,Finset.sum_range_succ,Nat.mul_add]
  · have h := Nat.le_of_not_gt hk
    simp [suffixCost,hk,min_eq_right h,min_eq_right (h.trans (Nat.le_succ k))]
theorem suffix_le (U k : ℕ) : suffixCost U k ≤ 50*U*(U+1) := by
  have hsum : (∑ j ∈ Finset.range (min k U), j) ≤ ∑ j ∈ Finset.range U,j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_right ..)) (by simp)
  have hs := Finset.sum_range_id_mul_two U
  unfold suffixCost
  have hle := Nat.mul_le_mul_left U (show U-1 ≤ U+1 by omega)
  nlinarith only [hs,hsum,hle]
private theorem clip_step {i k t α B A h : ℕ} (ht : i+(k+1)=t) (hc : h ≤ B+A*i) :
    h + min k α*h + (k-α)*(B+A*(t-α)) ≤ min (k+1) α*h+((k+1)-α)*(B+A*(t-α)) := by
  by_cases hl : k < α
  · rw [min_eq_left hl.le,min_eq_left (Nat.succ_le_of_lt hl),Nat.sub_eq_zero_of_le hl.le,
      Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt hl)]
    simp [Nat.succ_mul,Nat.add_comm]
  · have hα := Nat.le_of_not_gt hl
    rw [min_eq_right hα,min_eq_right (hα.trans (Nat.le_succ k))]
    have hle : h ≤ B+A*(t-α) := hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : i ≤ t-α)) _)
    rw [show k+1-α=(k-α)+1 by omega, Nat.add_mul, one_mul]
    omega
theorem clipped_bound {X : Type*} (ch : ℕ → X → Finset X) (height : ℕ → X → ℕ)
    (gain : ℕ → X → X → ℕ) (budget : ℕ → X → ℕ) (t b α B A d U : ℕ)
    (hc : ∀ i < t, ∀x, height i x ≤ B+A*i)
    (hb : ∀ i < t, ∀x, budget i x ≤ 2^(b+height i x))
    (hg : ∀ i < t, ∀x, ∀ y ∈ ch i x, height (i+1) y ≤ height i x+gain i x y)
    (hm : ∀ i u, i+(u+1)=t → ∀x, (∑ y ∈ ch i x, 2^(min u α*gain i x y)) ≤
      budget i x*((d+3)*2^(if u < U then 100*u else 0))) (root : X) :
    leaves ch t 0 root ≤ (d+3)^t * 2^(t*(b+height 0 root)+(t-α)*(B+A*(t-α))+50*U*(U+1)) := by
  let C := B+A*(t-α)
  have aux (k i : ℕ) (hi : i+k=t) (x : X) :
      leaves ch k i x ≤ (d+3)^k * 2^(k*b+min k α*height i x+(k-α)*C+suffixCost U k) := by
    induction k generalizing i x with
    | zero => simp [leaves,suffixCost]
    | succ k ih =>
      let z := min k α
      let h := height i x
      let L := k*b+z*h+(k-α)*C+suffixCost U k
      let w := if k < U then 100*k else 0
      have hit : i < t := by omega
      have f (y) (hy : y ∈ ch i x) : leaves ch k (i+1) y ≤
          ((d+3)^k*2^L)*2^(z*gain i x y) := by
        apply (ih (i+1) (by omega) y).trans
        rw [Nat.mul_assoc,←pow_add]
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by decide)
        have hg' := Nat.mul_le_mul_left z (hg i hit x y hy)
        change k*b+z*height (i+1) y+(k-α)*C+suffixCost U k ≤ _
        dsimp [L,h]
        rw [Nat.mul_add] at hg'
        omega
      have hh := (hm i k hi x).trans (Nat.mul_le_mul_right _ (hb i hit x))
      have step := clip_step (α:=α) hi (hc i hit x)
      calc
        _ ≤ ∑ y ∈ ch i x, ((d+3)^k*2^L)*2^(z*gain i x y) := Finset.sum_le_sum f
        _ = ((d+3)^k*2^L)*(∑ y ∈ ch i x, 2^(z*gain i x y)) := (Finset.mul_sum ..).symm
        _ ≤ ((d+3)^k*2^L)*(2^(b+h)*((d+3)*2^w)) := Nat.mul_le_mul_left _ hh
        _ = (d+3)^(k+1)*2^(L+(b+h)+w) := by rw [pow_succ (d+3),pow_add,pow_add]; ring
        _ ≤ _ := by
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_right (by decide)
          dsimp only [L,h,z,w,C]
          rw [suffix_succ,Nat.succ_mul k b]
          omega
  apply (aux t 0 (by simp) root).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by decide)
  have hl := Nat.mul_le_mul_right (height 0 root) (min_le_left t α)
  have hs := suffix_le U t
  dsimp [C]
  rw [Nat.mul_add t b (height 0 root)]
  omega
end Erdos1160.DescendantTree
end

/- ActualTree -/
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

/- MinimalCharacters -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160Growth.LowerTriangularUpper
theorem minimal_chars_factor {d m : ℕ} {Q : Type*} [Group Q] [Finite Q]
    (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hm : Nat.card Q=2^m) (hd : Nat.card (Q ⧸ frattini Q)=2^d)
    (χ : FreeGroup (Fin d) →* Multiplicative (ZMod 2)) :
    ∃ h : Q →* Multiplicative (ZMod 2), h.comp π=χ := by
  classical
  let p := QuotientGroup.mk' (frattini Q)
  have hs (x : Q ⧸ frattini Q) : x*x=1 := by
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) x
    rw [←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (squares_le_frattini hm (Subgroup.subset_closure ⟨y,rfl⟩))
  obtain ⟨E⟩ := exist_elementary_coords hs hd
  let P := E.toMonoidHom.comp p
  let u := P.comp π
  have hu : Function.Surjective u := E.surjective.comp ((QuotientGroup.mk'_surjective _).comp hπ)
  let dot (v : V d) : Multiplicative (V d) →* Multiplicative (ZMod 2) := {
    toFun w := .ofAdd (∑j,v j*w.toAdd j)
    map_one' := by change (∑j,v j*0)=0; simp
    map_mul' x y := by
      change (∑j,v j*(x.toAdd j+y.toAdd j))=_
      simp [mul_add,Finset.sum_add_distrib];rfl }
  have at_single (v : V d) (i : Fin d) :
      (dot v (.ofAdd (Pi.single i 1))).toAdd=v i := by
    change (∑j,v j*((Pi.single i 1 : V d) j))=v i
    simp [Pi.single_apply,mul_ite]
  let ev (v : V d) (j : Fin d) := (dot v (u (FreeGroup.of j))).toAdd
  have inj : Function.Injective ev := by
    intro v w hv
    have he : (dot v).comp u=(dot w).comp u := FreeGroup.ext_hom _ _ (fun j => congrFun hv j)
    funext j
    obtain ⟨x,hx⟩ := hu (.ofAdd (Pi.single j 1))
    rw [←at_single v j,←at_single w j,←hx]
    exact congrArg Multiplicative.toAdd (DFunLike.congr_fun he x)
  obtain ⟨w,hw⟩ := Finite.surjective_of_injective inj (fun j => (χ (FreeGroup.of j)).toAdd)
  exact ⟨(dot w).comp P, FreeGroup.ext_hom _ _ (fun i => congrFun hw i)⟩
theorem minimal_chars_kill_ker {d m : ℕ} {Q : Type*} [Group Q] [Finite Q]
    (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hm : Nat.card Q=2^m) (hd : Nat.card (Q ⧸ frattini Q)=2^d)
    (χ : FreeGroup (Fin d) →* Multiplicative (ZMod 2)) : π.ker ≤ χ.ker := by
  obtain ⟨h,rfl⟩ := minimal_chars_factor π hπ hm hd χ
  intro x hx
  change h (π x)=1
  rw [show π x=1 from hx,map_one]
end Erdos1160.CentralLifts.Survival
end

/- FrattiniTransgression -/
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

/- InflationTransgression -/
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

/- OrbitMargins -/
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
end OrbitUp
end

/- AllowableDimension -/
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

/- SuXia53 -/
section
namespace BinaryFactor.Elementary
open Cocycle
variable {Y : Type} [Group Y] [Finite Y]
theorem gaussian_affine {d n r a : ℕ} (hY : Nat.card Y=2^(d+n))
    (f : Y→*Vectors d) (hf : Function.Surjective f) (hΦ : f.ker ≤ frattini Y)
    (z : H₂ Y) (hr : 2 < r) (hra : r ≤ a) (had : a ≤ d) :
    Nat.card {x : LinearMap.range (inflate₂ f) // a ≤ annRank (z+x.val)} *
      numFrames a r * 2^(d.choose 2) ≤ numFrames d r *
      (Nat.card (LinearMap.range (inflate₂ f))*2^(3*(d*n+(d*(d-1)/2+d)-r₂ Y)/(r-2))) := by
  classical
  letI : Finite (H₂ Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have dim : Module.finrank Bit (characters Y)=d :=
    (inflation_tower (vectors_card d) n hY f hf hΦ).2.trans (vectors_char_rank d)
  let L := LinearMap.range (inflate₂ f)
  let S (x : L) := LinearMap.ker (cupWith (z+x.val))
  have fixed (v : Fin r→characters Y) (h : LinearIndependent Bit v) :
      Nat.card {x : L // ∀i,v i∈S x}*2^(d.choose 2) ≤
        Nat.card L*2^(3*(d*n+(d*(d-1)/2+d)-r₂ Y)/(r-2)) := by
    let A := Submodule.span Bit (Set.range v)
    have hA : Module.finrank Bit A=r := by unfold A;rw [finrank_span_eq_card h,Fintype.card_fin]
    let embed (x : {x : L // ∀i,v i∈S x}) :
        {x : L // ∀b : A,cupClass b.val (z+x.val)=0} :=
      ⟨x.val,fun b=>by
        have sub : A ≤ S x.val := Submodule.span_le.mpr (fun y ⟨i,hi⟩=>hi ▸ x.property i)
        exact sub b.property⟩
    have hi : Function.Injective embed := fun _ _ he=>Subtype.ext (congrArg (fun w : {x : L // ∀b : A,cupClass b.val (z+x.val)=0}=>w.val) he)
    exact (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective embed hi)).trans
      (frattini_fixed_cup hY f hf hΦ A hA z hr)
  have bound := frame_incidence S hra (had.trans_eq dim.symm) fixed
  rw [dim] at bound
  exact bound
lemma frames_le (d r : ℕ) : numFrames d r ≤ 2^(d*r) := by
  have h := Finset.prod_le_prod' (s:=(Finset.univ : Finset (Fin r)))
    (f:=fun i=>2^d-2^i.val) (g:=fun _=>2^d) (fun i _=>Nat.sub_le _ _)
  simpa [numFrames,pow_mul] using h
lemma round_gaussian {c z a d r M k : ℕ} (hr : r ≤ a) (hd : a ≤ d)
    (h : c*numFrames a r*M ≤ numFrames d r*(z*2^k)) :
    c*M ≤ z*2^(2+r*(d-a)+k) := by
  have hlow := Nat.mul_le_mul_right (c*M) (frame_quarter a r hr)
  have hupper := Nat.mul_le_mul_left 4 (h.trans (Nat.mul_le_mul_right _ (frames_le d r)))
  have eq : d*r=a*r+r*(d-a) := by
    have h := Nat.sub_add_cancel hd
    nlinarith only [congrArg (fun t=>t*r) h]
  rw [eq,pow_add] at hupper
  apply Nat.le_of_mul_le_mul_right (c:=2^(a*r)) _ (Nat.two_pow_pos _)
  rw [pow_add,pow_add]
  change c*M*2^(a*r) ≤ z*(4*2^(r*(d-a))*2^k)*2^(a*r)
  change 2^(a*r)*(c*M) ≤ 4*numFrames a r*(c*M) at hlow
  nlinarith only [hlow,hupper]
theorem su_xia_5_3_affine {d n r a : ℕ} (hY : Nat.card Y=2^(d+n))
    (f : Y→*Vectors d) (hf : Function.Surjective f) (hΦ : f.ker ≤ frattini Y)
    (z : H₂ Y) (hr : 2 < r) (hra : r ≤ a) (had : a ≤ d) :
    Nat.card {x : LinearMap.range (inflate₂ f) // a ≤ annRank (z+x.val)} * 2^(d.choose 2) ≤
      Nat.card (LinearMap.range (inflate₂ f))*2^(2+r*(d-a)+3*(d*n+(d*(d-1)/2+d)-r₂ Y)/(r-2)) :=
  round_gaussian hra had (gaussian_affine hY f hf hΦ z hr hra had)
theorem su_xia_5_3_allowable {d n r a : ℕ} (hY : Nat.card Y=2^(d+n))
    (f : Y→*Vectors d) (hf : Function.Surjective f) (hΦ : f.ker ≤ frattini Y)
    (hr : 2 < r) (hra : r ≤ a) (had : a ≤ d) :
    Nat.card {x : H₂ Y // x∉LinearMap.range (inflate₂ f) ∧ a ≤ annRank x} * 2^(d.choose 2) ≤
      Nat.card {x : H₂ Y // x∉LinearMap.range (inflate₂ f)} *
        2^(2+r*(d-a)+3*(d*n+(d*(d-1)/2+d)-r₂ Y)/(r-2)) := by
  letI : Finite (H₂ Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  exact admissible_density_of_affine _ (a ≤ annRank ·) _ _ (fun z=>
    su_xia_5_3_affine hY f hf hΦ z hr hra had)
end BinaryFactor.Elementary
end

/- ActualNodes -/
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
theorem gain_le (i : ℕ) {x y : Vertex Q (d+s)} (hy : y∈children i x)
    (p : Q→*Vectors d) (hf : Function.Surjective p) (hp : p.ker=squareCore Q) :
    y.gain ≤ d := by
  obtain ⟨_,z,rfl⟩ := mem_children.mp hy
  have hs : Nat.card x.group=2^(d+(s+x.depth)) := by rw [x.size,Nat.add_assoc]
  have rank := (inflation_tower (vectors_card d) (s+x.depth) hs (toVectors p x) (hf.comp x.onto)
    ((toVectors_ker p hp x).le.trans (squares_le_frattini hs))).2.trans (vectors_char_rank d)
  change Module.finrank Bit (LinearMap.ker (cupWith z.val)) ≤ d
  exact (Submodule.finrank_le _).trans_eq rank
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

/- BitLifts -/
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

/- BitKeyDetection -/
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

/- AllowableBit -/
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

/- TreeTails -/
section
namespace Erdos1160.DescendantTree
def tail {X : Type*} (S : Finset X) (a : X → ℕ) (j : ℕ) := (S.filter (fun x => j ≤ a x)).card
private theorem fiber_le_tail {X : Type*} (S : Finset X) (a : X → ℕ) {j r : ℕ} (h : r ≤ j) :
    (S.filter (fun x => a x=j)).card ≤ tail S a r := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hm,he⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hm,he ▸ h⟩
private theorem weighted_tail {X : Type*} (S : Finset X) (a : X → ℕ) {j r k E pay M : ℕ} (h : r ≤ j)
    (hk : k+pay ≤ E) (ht : tail S a r * 2^E ≤ M*2^pay) :
    (S.filter (fun x => a x=j)).card * 2^k ≤ M := by
  apply Nat.le_of_mul_le_mul_right (c := 2^pay) _ (by positivity)
  rw [Nat.mul_assoc,←pow_add]
  exact (Nat.mul_le_mul (fiber_le_tail S a h) (Nat.pow_le_pow_right (by decide) hk)).trans ht
private theorem far_exponent {d s i t u Δ : ℕ} (hd : 10000 ≤ d) (hs : s ≤ d)
    (hi : i+u+1=t) (ht : 2*(s+t) ≤ d+2*Δ+1) (hu : 2*Δ+12 ≤ u) :
    u*(d/100)+d+(d*(s+i)+s) ≤ (d-1)*(d-2)/2 := by
  have hq : 2*(d/100) ≤ d := by omega
  have hsize : 2*(s+i)+2*u+1 ≤ d+2*Δ := by omega
  have h₁ := Nat.mul_le_mul_left d hsize
  have h₂ := Nat.mul_le_mul_left d hu
  have h₃ := Nat.mul_le_mul_left u hq
  have hd1 : d = (d-2)+2 := by omega
  have hd2 : d-1=(d-2)+1 := by omega
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  rw [hd2]
  nlinarith only [h₁,h₂,h₃,hs,hd1,congrArg (fun x : ℕ => x*x) hd1,Nat.zero_le d]
private theorem near_exponent {d u Δ : ℕ} (hd : 10000 ≤ d) (hΔ : 1000*Δ ≤ d+1000) (hu : u < 2*Δ+12) :
    u*d ≤ 9*d^2/20 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 20)).mpr
  have h : 20*u ≤ 9*d := by omega
  have hh := Nat.mul_le_mul_right d h
  nlinarith only [hh]
theorem clipped_moment_from_tails {X : Type*} (S : Finset X) (a : X → ℕ)
    {M d s t i u Δ K : ℕ} (hM : S.card ≤ M) (hd : 10000 ≤ d) (hs : s ≤ d) (hΔ : 1000*Δ ≤ d+1000)
    (hi : i+u+1=t) (ht : 2*(s+t) ≤ d+2*Δ+1) (hK : K ≤ d*(s+i)+s)
    (had : ∀x∈S,a x ≤ d)
    (hone : tail S a 1 * 2^((d-1)*(d-2)/2) ≤ M * 2^(d+K))
    (hmid : ∀ j, d/100 ≤ j → j ≤ d → tail S a j * 2^((d/2-1000)*j) ≤ M)
    (hhundred : tail S a 100 * 2^(9*d^2/20) ≤ M) :
    (∑ x ∈ S, 2^(min u (d/2-1000)*a x)) ≤
      M*((d+3)*2^(if u < 2*Δ+12 then 100*u else 0)) := by
  let z := min u (d/2-1000)
  let cost := if u < 2*Δ+12 then 100*u else 0
  have hz : z ≤ u := min_le_left ..
  have hza : z ≤ d/2-1000 := min_le_right ..
  have price (j : ℕ) (hj : j ≤ d) :
      (S.filter (fun x => a x=j)).card*2^(z*j) ≤ M*2^cost := by
    by_cases hnear : u < 2*Δ+12
    · change _ ≤ M*2^(if _ then _ else _)
      rw [if_pos hnear]
      by_cases hj100 : 100 ≤ j
      · have hprod : z*j+0 ≤ 9*d^2/20 := by
          rw [Nat.add_zero]; exact (Nat.mul_le_mul hz hj).trans (near_exponent hd hΔ hnear)
        have hb := weighted_tail S a (k:=z*j) hj100 hprod (by simpa using hhundred)
        exact hb.trans (Nat.le_mul_of_pos_right _ (by positivity))
      · apply Nat.mul_le_mul ((Finset.card_filter_le _ _).trans hM)
        apply Nat.pow_le_pow_right (by decide)
        rw [Nat.mul_comm 100]
        exact Nat.mul_le_mul hz (by omega)
    · change _ ≤ M*2^(if _ then _ else _)
      rw [if_neg hnear,pow_zero,Nat.mul_one]
      by_cases hj0 : j=0
      · simpa [hj0] using ((Finset.card_filter_le S (fun x => a x = 0)).trans hM)
      by_cases hm : d/100 ≤ j
      · exact (Nat.mul_le_mul (fiber_le_tail S a (le_refl j))
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hza))).trans (hmid j hm hj)
      · apply weighted_tail S a (r:=1) (by omega) _ hone
        have h₁ := Nat.mul_le_mul hz (show j ≤ d/100 by omega)
        have h₂ := far_exponent hd hs hi ht (Nat.le_of_not_gt hnear)
        omega
  have hmaps : ∀ x ∈ S, a x ∈ Finset.range (d+1) := fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le (had x hx))
  change (∑ x ∈ S, 2^(z*a x)) ≤ M*((d+3)*2^cost)
  rw [←Finset.sum_fiberwise_of_maps_to' hmaps (fun j => 2^(z*j))]
  calc
    _ ≤ ∑ _j ∈ Finset.range (d+1), M*2^cost := by
      apply Finset.sum_le_sum
      intro j hj
      simpa using price j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = (d+1)*(M*2^cost) := by simp
    _ ≤ (d+3)*(M*2^cost) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
end Erdos1160.DescendantTree
end

/- GaussianTails -/
section
namespace Erdos1160.DescendantTree
private theorem quotient_loss {d K : ℕ} (hd : 10000 ≤ d) (hK : 5*K ≤ 3*d^2) :
    3*K/(d/100-2) ≤ 400*d := by
  let r := d/100-2
  let v := 3*K/r
  have h₂ : d ≤ 200*r := by dsimp [r]; omega
  have h₃ : v*r ≤ 3*K := Nat.div_mul_le_self _ _
  have h₄ := Nat.mul_le_mul_right v h₂
  have h₅ := Nat.mul_le_mul_left 200 h₃
  have hx : d*v ≤ d*(400*d) := by nlinarith only [hK,h₄,h₅,Nat.zero_le (d^2)]
  exact Nat.le_of_mul_le_mul_left hx (by omega)
private theorem gaussian_mid_exponent {d K j : ℕ} (hd : 10000 ≤ d) (hK : 5*K ≤ 3*d^2) (hdj : j ≤ d) :
    (d/2-1000)*j + (3+(d/100)*(d-j)+3*K/(d/100-2)) ≤ d*(d-1)/2 := by
  have hz : d/100 ≤ d/2-1000 := by omega
  have hq := Nat.mul_le_mul_right (d-j) hz
  have he : (d/2-1000)*j+(d/2-1000)*(d-j) = (d/2-1000)*d := by rw [←Nat.mul_add, Nat.add_sub_of_le hdj]
  have hcost := quotient_loss hd hK
  have half : (d/2-1000)*2+2000 ≤ d := by omega
  have hm := Nat.mul_le_mul_left d half
  have hsub : d-1+1=d := by omega
  have hsub' := congrArg (d*·) hsub
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  nlinarith only [hq,he,hcost,hm,hsub',hd]
private theorem gaussian_hundred_exponent {d K : ℕ} (hd : 10000 ≤ d) (hK : 5*K ≤ 3*d^2) :
    9*d^2/20 + (3+100*(d-100)+3*K/(100-2)) ≤ d*(d-1)/2 := by
  change 9*d^2/20+(3+100*(d-100)+3*K/98) ≤ d*(d-1)/2
  have hq := Nat.div_mul_le_self (3*K) 98
  have hth := Nat.div_mul_le_self (9*d^2) 20
  have hsub := congrArg (d*·) (show d-1+1=d by omega)
  have hpos := Nat.mul_le_mul_left d hd
  have hle : d-100 ≤ d := Nat.sub_le _ _
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  nlinarith only [hq,hth,hsub,hpos,hle,hK,hd]
private theorem cancel_tail {n c X B k : ℕ} (he : n*2^X ≤ c*2^B) (hk : k+B ≤ X) :
    n*2^k ≤ c := by
  apply Nat.le_of_mul_le_mul_right (c := 2^B) _ (by positivity)
  rw [Nat.mul_assoc,←pow_add]
  exact (Nat.mul_le_mul_left n (Nat.pow_le_pow_right (by decide) hk)).trans he
theorem gaussian_clipped_tails {X : Type*} (S : Finset X) (a : X → ℕ) {M d K : ℕ}
    (hd : 10000 ≤ d) (hK : 5*K ≤ 3*d^2)
    (hg : ∀ r j : ℕ, 3 ≤ r → r ≤ j → j ≤ d →
      tail S a j*2^(d*(d-1)/2) ≤ M*2^(3+r*(d-j)+3*K/(r-2))) :
    (∀ j, d/100 ≤ j → j ≤ d → tail S a j*2^((d/2-1000)*j) ≤ M) ∧
      tail S a 100*2^(9*d^2/20) ≤ M := by
  constructor
  · intro j hj hdj
    exact cancel_tail (hg (d/100) j (by omega) hj hdj) (gaussian_mid_exponent hd hK hdj)
  · exact cancel_tail (hg 100 100 (by decide) le_rfl (by omega)) (gaussian_hundred_exponent hd hK)
end Erdos1160.DescendantTree
end

/- DescendantTreeBound -/
section
namespace Erdos1160.DescendantTree
private theorem kernel_capacity {d s t i u Δ K : ℕ} (hd : 10000 ≤ d) (hs : s ≤ d)
    (hΔ : 1000*Δ ≤ d+1000) (ht : 2*(s+t) ≤ d+2*Δ+1) (hi : i+u+1=t) (hK : K ≤ d*(s+i)+s) :
    5*K ≤ 3*d^2 := by
  have h₁ : 2*(s+i) ≤ d+2*Δ+1 := by omega
  have h₂ := Nat.mul_le_mul_left d h₁
  have h₃ := Nat.mul_le_mul_left d hΔ
  nlinarith only [h₂,h₃,hK,hs,Nat.mul_le_mul_left d hd]
theorem fixed_root_leaf_bound {X : Type*} (ch : ℕ → X → Finset X) (h : ℕ → X → ℕ)
    (a : ℕ → X → X → ℕ) (K : ℕ → X → ℕ) {d s t b Δ : ℕ}
    (hd : 10000 ≤ d) (hs : s ≤ d) (hΔ : 1000*Δ ≤ d+1000) (ht : 2*(s+t) ≤ d+2*Δ+1)
    (hcap : ∀ i < t, ∀x, h i x ≤ (2*s+1)*s+2*s*i)
    (hcard : ∀ i < t, ∀x, (ch i x).card ≤ 2^(b+h i x))
    (hstep : ∀ i < t, ∀x, ∀y∈ch i x, h (i+1) y ≤ h i x + a i x y)
    (hgain : ∀ i < t, ∀x, ∀y∈ch i x, a i x y ≤ d)
    (hK : ∀ i < t, ∀x, K i x ≤ d*(s+i)+s)
    (hone : ∀ i < t, ∀x, tail (ch i x) (a i x) 1*2^((d-1)*(d-2)/2) ≤ 2^(b+h i x)*2^(d+K i x))
    (hgauss : ∀ i < t, ∀x, ∀r j : ℕ, 3 ≤ r → r ≤ j → j ≤ d →
      tail (ch i x) (a i x) j*2^(d*(d-1)/2) ≤ 2^(b+h i x)*2^(3+r*(d-j)+3*K i x/(r-2)))
    (root : X) :
    let w := t-(d/2-1000)
    let U := 2*Δ+12
    leaves ch t 0 root ≤ (d+3)^t * 2^(t*(b+h 0 root)+(2*s+1)*w*(s+w)+50*U*(U+1)) := by
  dsimp only
  have hm (i u) (hi : i+(u+1)=t) (x : X) :
      (∑ y ∈ ch i x,2^(min u (d/2-1000)*a i x y)) ≤
       2^(b+h i x)*((d+3)*2^(if u < 2*Δ+12 then 100*u else 0)) := by
    have hit : i < t := by omega
    have hi' : i+u+1=t := by omega
    have hK' := hK i hit x
    obtain ⟨hmid,hhundred⟩ := gaussian_clipped_tails _ _ hd (kernel_capacity hd hs hΔ ht hi' hK') (hgauss i hit x)
    exact clipped_moment_from_tails _ _ (hcard i hit x) hd hs hΔ hi' ht hK' (hgain i hit x) (hone i hit x) hmid hhundred
  apply (clipped_bound ch h a (fun i x => 2^(b+h i x)) t b (d/2-1000) ((2*s+1)*s) (2*s) d (2*Δ+12)
    hcap (fun _ _ _ => le_refl _) hstep hm root).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by decide)
  let w := t-(d/2-1000)
  have hcost : w*((2*s+1)*s+2*s*w)≤(2*s+1)*w*(s+w) := by nlinarith only [Nat.zero_le (w^2)]
  exact Nat.add_le_add_right (Nat.add_le_add_left hcost _) _
end Erdos1160.DescendantTree
end

/- ActualTails -/
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
theorem local_gaussian {i r j : ℕ} (x : Layer R) (hr : 3 ≤ r) (hrj : r ≤ j) (hjd : j ≤ d) :
    tail (children i x) Vertex.gain j * 2^(d*(d-1)/2) ≤
      2^(b₀ d s+height (b₀ d s) i x)*2^(3+r*(d-j)+3*loss R i x/(r-2)) := by
  classical
  by_cases hi : i=x.depth
  · subst i
    have est := su_xia_5_3_allowable (order_at R x) (toVectors R.elementary x) (R.onto.comp x.onto) (frattini_at R x)
      (by omega : 2 < r) hrj hjd
    rw [Nat.choose_two_right] at est
    have h := normalize R (i:=x.depth) x (fun z=>j ≤ annRank z) (fun v=>j ≤ v.gain) (fun _ h=>h) est
    rw [forest_ambient,loss,if_pos rfl]
    exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
  · simp [tail,children,hi]
theorem local_one {i : ℕ} (x : Layer R) (hd : 1 ≤ d) :
    tail (children i x) Vertex.gain 1 * 2^((d-1)*(d-2)/2) ≤
      2^(b₀ d s+height (b₀ d s) i x)*2^(d+loss R i x) := by
  classical
  by_cases hi : i=x.depth
  · subst i
    let L := LinearMap.range (inflate₂ (toVectors R.elementary x))
    let D := d*(d-1)/2
    let K := d*(s+x.depth)+(D+d)-r₂ x.group
    have cc : Nat.card {z : H₂ x.group // z∉L ∧ 0 < annRank z}*2^(D+d) ≤
        Nat.card {z : H₂ x.group // z∉L}*2^(d+K) := by
      apply admissible_density_of_affine
      intro z
      have h := cup_union_density (order_at R x) (toVectors R.elementary x) (R.onto.comp x.onto) (frattini_at R x) hd z
      apply h.trans
      rw [pow_add]
      exact (Nat.mul_le_mul_right _ (Nat.sub_le ..)).trans_eq (by ring)
    have h := normalize R (i:=x.depth) x (fun z=>0 < annRank z) (fun v=>1 ≤ v.gain) (fun _ h=>h) cc
    have he : (d-1)*(d-2)/2 ≤ D+d := (Nat.div_le_div_right (Nat.mul_le_mul (Nat.sub_le ..) (by omega))).trans (Nat.le_add_right ..)
    rw [forest_ambient,loss,if_pos rfl]
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2) he)).trans h
  · simp [tail,children,hi]
end Erdos1160.DescendantTree.Actual
end

/- SubgroupCriterion -/
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

/- ThirdCriterion -/
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

/- PullThird -/
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

/- BracketGenerators -/
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

/- ElementaryKernel -/
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

/- SmallSubgroup -/
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

/- RestrictDimension -/
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

/- UnrestrictedCapacity -/
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

/- ChartSize -/
section
namespace Erdos1160.DeepJacobi
lemma double_pairs (d : ℕ) : 2*(d*(d-1)/2) = d*(d-1) := by
  rw [mul_comm 2,Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self d)]
lemma pairs_add (n q : ℕ) : q*(q-1)/2 + q*n + n*(n-1)/2 = (n+q)*(n+q-1)/2 := by
  cases n with
  | zero => simp
  | succ n =>
    cases q with
    | zero => simp
    | succ q =>
      have ha := double_pairs (q+1)
      have hb := double_pairs (n+1)
      have hc := double_pairs (n+1+(q+1))
      have hs : n+1+(q+1)-1 = n+q+1 := by omega
      simp only [Nat.add_sub_cancel,hs] at ha hb hc ⊢
      nlinarith only [ha,hb,hc]
theorem array_card (q n s : ℕ) :
    Nat.card (Array q n s) = 2^((q+s)*((n+q)*((n+q)-1)/2)) := by
  simp only [Array,Old,W,V,Nat.card_prod,Nat.card_fun,Nat.card_sum,Nat.card_fin,Nat.card_zmod,
    Erdos1160Growth.SharpFamily.triangular_card,← pow_add,← pow_mul,← Nat.mul_add,pairs_add]
end Erdos1160.DeepJacobi
end

/- JointOrbit -/
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
end Erdos1160Growth.LowerTriangularUpper
end

/- FreeBinaryRoot -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160Growth Erdos1160Growth.LowerTriangularUpper Erdos1160.DeepJacobi
open scoped commutatorElement
private lemma slot_card (d : ℕ) : Fintype.card (Slot d)=d*(d+1)/2 := by
  classical
  change Fintype.card (((i : Fin d) × Fin i.val) ⊕ Fin d)=_
  rw [Fintype.card_sum,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d,Finset.sum_range_id]
  have h := Erdos1160.DeepJacobi.double_pairs d
  cases d with
  | zero => decide
  | succ n =>
    simp only [Nat.add_sub_cancel] at h ⊢
    have h' := Erdos1160.DeepJacobi.double_pairs (n+2)
    have : n+2-1=n+1 := by omega
    rw [this,Nat.mul_comm (n+2) (n+1)] at h'
    change (n+1)*n/2+(n+1)=(n+1)*(n+2)/2
    nlinarith only [h,h']
private noncomputable def slots (d : ℕ) : Slot d ≃ Fin (d*(d+1)/2) :=
  Fintype.equivFinOfCardEq (slot_card d)
noncomputable def freeArray (d : ℕ) : P d (d*(d+1)/2) := fun l => bit ((slots d) l)
abbrev FreeRoot (d : ℕ) := G (freeArray d)
variable (d : ℕ)
private noncomputable def xfree (i : Fin d) : FreeRoot d := ⟨bit i,0⟩
noncomputable def freeMark : FreeGroup (Fin d) →* FreeRoot d := FreeGroup.lift (xfree d)
private def zw (w : CentralKernelCount.BitGroup (d*(d+1)/2)) : FreeRoot d := ⟨0,w.toAdd⟩
noncomputable def freeFiber : CentralKernelCount.BitGroup (d*(d+1)/2) →* FreeRoot d where
  toFun w := zw d w
  map_one' := rfl
  map_mul' u v := by apply BilinearExtension.ext <;> simp [zw]
private lemma xsq (i : Fin d) : xfree d i * xfree d i = freeFiber d (CentralKernelCount.bit ((slots d) (.inr i))) := by
  apply BilinearExtension.ext
  · change bit i+bit i=0;exact two_copies_zero _
  · change 0+0+form (freeArray d) (bit i) (bit i)=_
    rw [zero_add,zero_add]
    exact form_at_slot _ (.inr i)
private lemma xcomm (p : (i : Fin d) × Fin i.val) :
    ⁅xfree d p.1,xfree d ⟨p.2.val,p.2.isLt.trans p.1.isLt⟩⁆ =
      freeFiber d (CentralKernelCount.bit ((slots d) (.inl p))) := by
  rw [BilinearExtension.commutator_formula]
  apply BilinearExtension.ext
  · rfl
  · change form (freeArray d) (bit (row (.inl p))) (bit (col (.inl p))) -
        form (freeArray d) (bit (col (.inl p))) (bit (row (.inl p)))=_
    rw [form_at_slot,form_above _ _ _ (show col (.inl p) < row (.inl p) from p.2.isLt),sub_zero]
    rfl
lemma freeMark_onto : Function.Surjective (freeMark d) := by
  let H := (freeMark d).range
  have hx (i : Fin d) : xfree d i∈H := ⟨FreeGroup.of i,FreeGroup.lift_apply_of⟩
  have hz (i : Fin (d*(d+1)/2)) : freeFiber d (CentralKernelCount.bit i)∈H := by
    obtain ⟨l,rfl⟩ := (slots d).surjective i
    rcases l with p|j
    · rw [←xcomm]
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem (hx _) (hx _)) (H.inv_mem (hx _))) (H.inv_mem (hx _))
    · rw [←xsq]
      exact H.mul_mem (hx _) (hx _)
  have hall (w : CentralKernelCount.BitGroup (d*(d+1)/2)) : freeFiber d w∈H := by
    obtain ⟨l,rfl⟩ := CentralKernelCount.bits_word _ w
    rw [CentralKernelCount.word_map]
    exact CentralKernelCount.word_mem H _ hz _
  let proj := BilinearExtension.projection (form (freeArray d))
  have hb : Function.Surjective (proj.comp (freeMark d)) := by
    intro v
    obtain ⟨l,rfl⟩ := CentralKernelCount.bits_word _ v
    change CentralKernelCount.word CentralKernelCount.bit l ∈ (proj.comp (freeMark d)).range
    apply CentralKernelCount.word_mem
    intro i
    exact ⟨FreeGroup.of i,by change proj (FreeGroup.lift (xfree d) (FreeGroup.of i))=_; rw [FreeGroup.lift_apply_of];rfl⟩
  intro v
  obtain ⟨u,hu⟩ := hb (proj v)
  let h := v*(freeMark d u)⁻¹
  have hh : proj h=1 := by
    change proj (v*(freeMark d u)⁻¹)=1
    rw [map_mul,map_inv,show proj (freeMark d u)=proj v from hu,mul_inv_cancel]
  have he : freeFiber d (.ofAdd h.fiber)=h := BilinearExtension.ext (show 0=h.base from hh.symm) rfl
  have hm : h∈H := he ▸ hall (.ofAdd h.fiber)
  have hmem := H.mul_mem hm (show freeMark d u∈H from ⟨u,rfl⟩)
  change v∈H
  simpa [h] using hmem
lemma freeRoot_order : Nat.card (FreeRoot d)=2^(d+d*(d+1)/2) := by
  change Nat.card (BilinearExtension (form (freeArray d)))=_
  simp [BilinearExtension.card,LowerTriangularUpper.V,←pow_add]
lemma freeRoot_binaryThird : binaryThird (FreeRoot d)=⊥ := by
  let proj := BilinearExtension.projection (form (freeArray d))
  have hs : squareCore (FreeRoot d) ≤ proj.ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨v,rfl⟩
    change v.base+v.base=0
    exact two_copies_zero _
  have hc : proj.ker ≤ Subgroup.center (FreeRoot d) := by
    rintro ⟨x,w⟩ h
    have hx : x=0 := h
    subst x
    exact BilinearExtension.central_fiber _
  have hb (u : proj.ker) : u*u=1 := by
    obtain ⟨⟨x,w⟩,hx⟩ := u
    have he : x=0 := hx
    subst x
    apply Subtype.ext
    apply BilinearExtension.ext
    · simp
    · change w+w+form (freeArray d) 0 0=0
      rw [two_copies_zero,map_zero];rfl
  apply binaryThird_eq_bot (freeRoot_order d)
  · exact (frattini_le_squareCore.trans hs).trans hc
  · intro u
    exact Subtype.ext (congrArg (fun z : proj.ker => z.val) (hb ⟨u.val,hs (frattini_le_squareCore u.property)⟩))
end Erdos1160.CentralLifts.Survival
end

/- ClassTwoCoverSize -/
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

/- SpecialCoverSize -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
theorem generated_special_cover_order {d : ℕ} {Y Q : Type} [Group Y] [Group Q] [Finite Y] [Finite Q]
    (f : Y →* Q) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center Y)
    (hker2 : ∀ x : f.ker, x*x=1) (hY : Second Y ≤ Subgroup.center Y)
    (hQ : ∀ q : Q, q*q ∈ Second Q)
    (g : FreeGroup (Fin d) →* Y) (hg : Function.Surjective g) :
    Nat.card Y ≤ 2^(d+d*(d+1)/2) := by
  classical
  have hmap := lower_map_top f hf 1
  change (Second Y).map f = Second Q at hmap
  have split (y : Y) : ∃ w ∈ Second Y, ∃ k ∈ f.ker, y*y = w*k := by
    obtain ⟨w,hw,he⟩ := (show f (y*y)∈(Second Y).map f by rw [hmap,map_mul]; exact hQ _)
    refine ⟨w,hw,w⁻¹*(y*y),?_,(mul_inv_cancel_left w _).symm⟩
    change f (w⁻¹*(y*y))=1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hcent (y : Y) : y*y∈Subgroup.center Y := by
    obtain ⟨w,hw,k,hk',e⟩ := split y
    rw [e]
    exact (Subgroup.center Y).mul_mem (hY hw) (hk hk')
  have hderived := FrattiniSurvival.derived_square_one hY hcent
  let Z : Subgroup Y := {
    carrier := {v | v∈Subgroup.center Y ∧ v*v=1}
    one_mem' := ⟨(Subgroup.center Y).one_mem,one_mul _⟩
    mul_mem' := by
      rintro u v ⟨hu,hs⟩ ⟨hv,ht⟩
      refine ⟨(Subgroup.center Y).mul_mem hu hv,?_⟩
      change (u*v)*(u*v)=1
      have eq1 := (show Commute u v from (Subgroup.mem_center_iff.mp hv u)).mul_pow 2
      simpa only [pow_two,hs,ht,one_mul] using eq1
    inv_mem' := by rintro u ⟨hu,hs⟩; exact ⟨(Subgroup.center Y).inv_mem hu,by rw [←mul_inv_rev,hs,inv_one]⟩ }
  have hsq (y : Y) : y*y∈Z := by
    obtain ⟨w,hw,k,hk',e⟩ := split y
    have h1 : w∈Z := ⟨hY hw,hderived w hw⟩
    have h2 : k∈Z := ⟨hk hk',congrArg Subtype.val (hker2 ⟨k,hk'⟩)⟩
    exact e ▸ Z.mul_mem h1 h2
  letI : Z.Normal := ⟨fun x hx y => by
    rw [Subgroup.mem_center_iff.mp hx.1 y,mul_inv_cancel_right]; exact hx⟩
  let π := QuotientGroup.mk' Z
  have hπ := QuotientGroup.mk'_surjective Z
  have hpow (q : Y ⧸ Z) : q^2=1 := by
    obtain ⟨y,rfl⟩ := hπ q
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (by rw [pow_two]; exact hsq _)
  have hinv (q : Y ⧸ Z) : q⁻¹=q := inv_eq_of_mul_eq_one_left (by have e:=hpow q; rwa [pow_two] at e)
  let groupQ : Group (Y ⧸ Z) := inferInstance
  letI : CommGroup (Y ⧸ Z) := { groupQ with
    mul_comm := fun a b => by rw [←hinv (a*b),mul_inv_rev,hinv,hinv] }
  let v (i : Fin d) := (π.comp g) (FreeGroup.of i)
  have hgen : Subgroup.closure (Set.range v)=⊤ := by
    change Subgroup.closure (Set.range ((π.comp g) ∘ FreeGroup.of))=⊤
    rw [Set.range_comp,←MonoidHom.map_closure,FreeGroup.closure_range_of,
      Subgroup.map_top_of_surjective (π.comp g) (show Function.Surjective (π.comp g) from hπ.comp hg)]
  let T := Finset.univ.image v
  have ht : (T : Set (Y ⧸ Z)) = Set.range v := by ext x; simp [T]
  have hr : Group.rank (Y ⧸ Z) ≤ d := (Group.rank_le (show Subgroup.closure (T:Set (Y ⧸ Z))=⊤ by rw [ht,hgen])).trans
    (Finset.card_image_le.trans_eq (by simp))
  have hcard : Nat.card (Y ⧸ Z) ≤ 2^d := (Nat.le_of_dvd (Nat.two_pow_pos _)
    (card_dvd_exponent_pow_rank' _ hpow)).trans (Nat.pow_le_pow_right (by decide) hr)
  have bits (k : π.ker) : k*k=1 := by
    apply Subtype.ext
    have hZ : k.val∈Z := (QuotientGroup.eq_one_iff _).mp k.property
    exact hZ.2
  exact (generated_class_two_cover_bound π hπ bits hY g hg).trans
    ((Nat.mul_le_mul_right _ hcard).trans_eq (pow_add _ _ _).symm)
end Erdos1160.DeepJacobi
end

/- CohomologyMultiplicator -/
section
namespace Erdos1160.CentralLifts.Survival
open BinaryFactor
open Erdos1160.DeepJacobi (C₂)
variable {d : ℕ} {Q : Type} [Group Q]
variable (π : FreeGroup (Fin d) →* Q)
def twistMap (c : Cocycle Q) : FreeGroup (Fin d) →* c.Twist :=
  FreeGroup.lift (fun i => (π (FreeGroup.of i),0))
theorem twistMap_base (c : Cocycle Q) (w : FreeGroup (Fin d)) : (twistMap π c w).1=π w := by
  have he : c.projTwist.comp (twistMap π c)=π := FreeGroup.ext_hom _ _ (fun i => by
    exact congrArg (fun z : c.Twist => z.1) (FreeGroup.lift_apply_of (β := c.Twist) (f := fun j : Fin d => ((π (FreeGroup.of j),0) : c.Twist)) (x := i)))
  exact DFunLike.congr_fun he w
theorem twistMap_product (c : Cocycle Q) (u v : FreeGroup (Fin d)) :
    (twistMap π c (u*v)).2=(twistMap π c u).2+(twistMap π c v).2+c.val (π u) (π v) := by
  rw [map_mul]
  change _+_+c.val (twistMap π c u).1 (twistMap π c v).1=_
  rw [twistMap_base,twistMap_base]
def cocycleChar (c : Cocycle Q) : π.ker →* Erdos1160.DeepJacobi.C₂ where
  toFun w := .ofAdd (twistMap π c w.val).2
  map_one' := congrArg (fun z : c.Twist => Multiplicative.ofAdd z.2) (twistMap π c).map_one
  map_mul' u v := by
    change (twistMap π c (u.val*v.val)).2= (twistMap π c u.val).2+(twistMap π c v.val).2
    rw [twistMap_product,show π u.val=1 from u.property,c.norm_left,add_zero]
def cocycleRelCharacter (c : Cocycle Q) : RelCharacters π :=
  ⟨cocycleChar π c,by
    intro g w
    have h : twistMap π c w.val ∈ c.projTwist.ker := (twistMap_base π c w.val).trans w.property
    have hc := Subgroup.mem_center_iff.mp (c.projTwist_central h) (twistMap π c g)
    change Multiplicative.ofAdd (twistMap π c (g*w.val*g⁻¹)).2=Multiplicative.ofAdd (twistMap π c w.val).2
    rw [map_mul,map_mul,map_inv,hc,mul_inv_cancel_right]⟩
private def sectionRelation (s : Q → FreeGroup (Fin d)) (hs : ∀x,π (s x)=x) (x y : Q) : π.ker :=
  ⟨s x*s y*(s (x*y))⁻¹,by change π _=1;rw [map_mul,map_mul,map_inv,hs,hs,hs,mul_inv_cancel]⟩
private theorem section_factor (s : Q → FreeGroup (Fin d)) (hs : ∀x,π (s x)=x) (c : Cocycle Q) (x y : Q) :
    (twistMap π c (s x)).2+(twistMap π c (s y)).2+c.val x y =
      ((cocycleRelCharacter π c).val (sectionRelation π s hs x y)).toAdd+(twistMap π c (s (x*y))).2 := by
  have h : s x*s y=(sectionRelation π s hs x y).val*s (x*y) := by simp [sectionRelation]
  have he := congrArg (fun z : FreeGroup (Fin d) => (twistMap π c z).2) h
  change _=(twistMap π c (sectionRelation π s hs x y).val).2+(twistMap π c (s (x*y))).2
  simpa only [twistMap_product,hs,show π (sectionRelation π s hs x y).val=1 from (sectionRelation π s hs x y).property,
    c.norm_left,add_zero] using he
theorem cohomology_le_multiplicator [Finite Q] (hπ : Function.Surjective π) : r₂ Q ≤ relRank π := by
  classical
  let s (x : Q) : FreeGroup (Fin d) := if x=1 then 1 else (hπ x).choose
  have hs (x : Q) : π (s x)=x := by
    dsimp only [s];split
    · rename_i h;rw [h,map_one]
    · exact (hπ x).choose_spec
  let rep (x : H₂ Q) := ((Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear Q))) x).choose
  let f (x : H₂ Q) := cocycleRelCharacter π (ofCycle (rep x))
  have hf : Function.Injective f := by
    intro x y he
    let c := ofCycle (rep x)
    let h := ofCycle (rep y)
    let t (z : Q) := (twistMap π c (s z)).2 - (twistMap π h (s z)).2
    have ht : t 1=0 := by simp only [t,s];exact sub_self (0:Bit)
    have hdh (u v : Q) : t v+t (u*v)+t u=c.val u v-h.val u v := by
      have hc := section_factor π s hs c u v
      have hh := section_factor π s hs h u v
      have he' : (cocycleRelCharacter π c).val (sectionRelation π s hs u v)=
        (cocycleRelCharacter π h).val (sectionRelation π s hs u v) :=
        congrArg (fun a : RelCharacters π => a.val (sectionRelation π s hs u v)) he
      rw [he'] at hc
      dsimp only [t]
      linear_combination (norm := (ring_nf; simp [show (2:Bit)=0 by decide])) hc-hh
    have hb : (Submodule.Quotient.mk (rep x) : H₂ Q)=Submodule.Quotient.mk (rep y) := by
      apply (Submodule.Quotient.eq _).mpr
      refine ⟨⟨t,ht⟩,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      funext u v
      exact hdh u v
    exact ((Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear Q))) x).choose_spec.symm.trans
      (hb.trans ((Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear Q))) y).choose_spec)
  let _ : Finite (cycles₂ Q) := Finite.of_injective (fun a : cycles₂ Q => a.val.val) (fun _ _ e => Subtype.ext (Subtype.ext e))
  let _ : Finite (H₂ Q) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear Q)))
  let _ := Fintype.ofFinite (H₂ Q)
  let _ := Fintype.ofFinite (Additive (RelCharacters π))
  have hcard := Nat.card_le_card_of_injective (fun x => Additive.ofMul (f x)) (Additive.ofMul.injective.comp hf)
  have h₁ := Module.card_eq_pow_finrank (K := Bit) (V := H₂ Q)
  have h₂ := Module.card_eq_pow_finrank (K := Bit) (V := Additive (RelCharacters π))
  rw [←Nat.card_eq_fintype_card,ZMod.card] at h₁ h₂
  rw [h₁,h₂] at hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
end Erdos1160.CentralLifts.Survival
end

/- ExactRootInequality -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
variable {d s m : ℕ} {Q : Type} [Group Q] [Finite Q]
theorem binary_quotient_cover_order (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) :
    Nat.card (Cover π ⧸ binaryThird (Cover π)) ≤ 2^(d+d*(d+1)/2) := by
  have hp := cover_card π hπ
  rw [hQ,←pow_add] at hp
  let _ : Finite (Cover π) := Nat.finite_of_card_ne_zero (hp ▸ Nat.ne_of_gt (Nat.two_pow_pos _))
  let Y := Cover π ⧸ binaryThird (Cover π)
  let p := QuotientGroup.mk' (binaryThird (Cover π))
  let q := QuotientGroup.mk' (squareCore Y)
  obtain ⟨hc,hb⟩ := third_quot_squares (Cover π)
  have hkc : q.ker ≤ Subgroup.center Y := (QuotientGroup.ker_mk' _).le.trans hc
  have hkb (u : q.ker) : u*u=1 := by
    apply Subtype.ext
    exact congrArg (fun v : squareCore Y => v.val) (hb ⟨u.val,(QuotientGroup.ker_mk' _).le u.property⟩)
  have hx (u : Y ⧸ squareCore Y) : u*u ∈ Second (Y ⧸ squareCore Y) := by
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (squareCore Y) u
    rw [←map_mul,show q (w*w)=1 from (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨w,rfl⟩)]
    exact Subgroup.one_mem _
  let g := p.comp (QuotientGroup.mk' (universalKernel π))
  exact generated_special_cover_order q (QuotientGroup.mk'_surjective _) hkc hkb
    ((derived_le_squares Y).trans hc) hx g ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
end Erdos1160.CentralLifts.Survival
end

/- MultiplicatorGrowth -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi (C₂)
variable {d r m : ℕ} {Q : Type} [Group Q] [Finite Q]
def extensionKer (π : FreeGroup (Fin d) →* Q) (a : RelCharacters π) : Subgroup (FreeGroup (Fin d)) :=
  a.val.ker.map π.ker.subtype
instance (π : FreeGroup (Fin d) →* Q) (a : RelCharacters π) : (extensionKer π a).Normal where
  conj_mem := by
    rintro _ ⟨w,hw,rfl⟩ g
    exact ⟨conjugateRelation π g w,(a.property g w).trans hw,rfl⟩
omit [Finite Q] in
theorem character_onto (π : FreeGroup (Fin d) →* Q) (a : RelCharacters π) (hn : a≠1) :
    Function.Surjective a.val := by
  classical
  have h : ∃ w,a.val w≠1 := by
    by_contra! he
    exact hn (Subtype.ext (MonoidHom.ext he))
  obtain ⟨w,hw⟩ := h
  intro b
  rcases (show ∀b : C₂,b=1 ∨ b=Multiplicative.ofAdd 1 by decide) b with rfl|rfl
  · exact ⟨1,a.val.map_one⟩
  · exact ⟨w,((show ∀b : C₂,b=1 ∨ b=Multiplicative.ofAdd 1 by decide) _).resolve_left hw⟩
omit [Finite Q] in
theorem extension_card (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (a : RelCharacters π) (ha : a≠1) :
    Nat.card (FreeGroup (Fin d) ⧸ extensionKer π a)=2*Nat.card Q := by
  rw [←Subgroup.index_eq_card,extensionKer,Subgroup.index_map_subtype,Subgroup.index_ker,Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (character_onto π a ha),MonoidHom.range_eq_top.mpr hπ,Subgroup.card_top,
    Subgroup.card_top]
  exact congrArg (·*Nat.card Q) (Nat.card_zmod 2)
end Erdos1160.CentralLifts.Survival
end

/- TransgressionEquality -/
section
namespace Erdos1160.CentralLifts.Survival
open BinaryFactor
open Erdos1160.DeepJacobi (C₂)
variable {d m : ℕ} {Q : Type} [Group Q] [Finite Q]
private def differenceMark (π : FreeGroup (Fin d) →* Q) (c : Cocycle Q) (L : FreeGroup (Fin d) →* c.Twist)
    (hL : c.projTwist.comp L=π) : FreeGroup (Fin d) →* Erdos1160.DeepJacobi.C₂ where
  toFun u := .ofAdd ((twistMap π c u).2-(L u).2)
  map_one' := by rw [map_one,map_one];exact sub_self (0 : Bit)
  map_mul' u v := by
    have base (w : FreeGroup (Fin d)) : (L w).1=π w := DFunLike.congr_fun hL w
    change (twistMap π c (u*v)).2-(L (u*v)).2=(twistMap π c u).2-(L u).2+((twistMap π c v).2-(L v).2)
    rw [twistMap_product,map_mul]
    change _-((L u).2+(L v).2+c.val (L u).1 (L v).1)=_
    rw [base,base];abel
private theorem read_mark (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π) (hm : Nat.card Q=2^m)
    (hd : Nat.card (Q ⧸ frattini Q)=2^d) (c : Cocycle Q) (L : FreeGroup (Fin d) →* c.Twist)
    (hL : c.projTwist.comp L=π) (w : π.ker) : ((cocycleRelCharacter π c).val w).toAdd=(L w.val).2 :=
  sub_eq_zero.mp (show (twistMap π c w.val).2-(L w.val).2=0 from
    minimal_chars_kill_ker π hπ hm hd (differenceMark π c L hL) w.property)
private def splitCocycle (Q : Type) [Group Q] : Cocycle Q :=
  ⟨0,fun _ => rfl,fun _ => rfl,fun _ _ _ => by simp [d₂]⟩
private def splitSection : Q →* (splitCocycle Q).Twist where
  toFun x := (x,0)
  map_one' := rfl
  map_mul' x y := Prod.ext rfl (by change (0:Bit)=0+0+0;simp)
theorem relation_character_over_cohomology (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hm : Nat.card Q=2^m) (hd : Nat.card (Q ⧸ frattini Q)=2^d) :
    Function.Surjective (fun x : H₂ Q => cocycleRelCharacter π (classCocycle x)) := by
  classical
  intro a
  by_cases he : a=1
  · subst a
    obtain ⟨x,e,he⟩ := exists_class_equiv (splitCocycle Q)
    let L := (e.toMonoidHom.comp splitSection).comp π
    have hL : (classCocycle x).projTwist.comp L=π :=
      MonoidHom.ext (fun u => he (splitSection (π u)))
    refine ⟨x,Subtype.ext (MonoidHom.ext (fun w => ?_))⟩
    change ((cocycleRelCharacter π (classCocycle x)).val w).toAdd=0
    rw [read_mark π hπ hm hd _ L hL w]
    have h : L w.val=1 := by change (e.toMonoidHom.comp splitSection) (π w.val)=1;rw [show π w.val=1 from w.property,map_one]
    exact congrArg (fun z : (classCocycle x).Twist => z.2) h
  · let N := extensionKer π a
    let E := FreeGroup (Fin d) ⧸ N
    let p := QuotientGroup.mk' N
    let k : E →* Q := QuotientGroup.lift N π (fun _ ⟨w,_,h⟩ => h ▸ w.property)
    have hk : Function.Surjective k := fun y => by obtain ⟨w,rfl⟩ := hπ y;exact ⟨p w,rfl⟩
    have hE : Nat.card E=2^(m+1) := (extension_card π hπ a he).trans (by rw [hm,pow_succ,Nat.mul_comm])
    have hc : Nat.card k.ker=2 := by simpa using ker_card_of_epi Nat.prime_two hE hm k hk
    obtain ⟨x,e,hx⟩ := twist_classifies k hk (ThirdLowerCentral.order_two_central k.ker hc) hc
    let L := e.toMonoidHom.comp p
    have hL : (classCocycle x).projTwist.comp L=π := MonoidHom.ext (fun u => hx (p u))
    refine ⟨x,Subtype.ext (MonoidHom.ext (fun w => ?_))⟩
    change ((cocycleRelCharacter π (classCocycle x)).val w).toAdd=(a.val w).toAdd
    rw [read_mark π hπ hm hd _ L hL w]
    have hz : (L w.val).2=0 ↔ (a.val w).toAdd=0 := by
      have hb : (L w.val).1=1 := (DFunLike.congr_fun hL w.val).trans w.property
      have hl : (L w.val).2=0 ↔ L w.val=1 := ⟨fun h => Prod.ext hb h,fun h => congrArg (fun z : (classCocycle x).Twist => z.2) h⟩
      rw [hl,show L w.val=1 ↔ p w.val=1 from ⟨fun h => e.injective (h.trans e.map_one.symm),fun h => by change e (p w.val)=1;rw [h,e.map_one]⟩]
      change (QuotientGroup.mk' N) w.val=1 ↔ _
      rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
      constructor
      · rintro ⟨v,hv,h⟩
        have heq : v=w := Subtype.ext h
        exact heq ▸ hv
      · exact fun h => ⟨w,h,rfl⟩
    rcases bit_cases (L w.val).2 with h|h
    · exact h.trans (hz.mp h).symm
    · exact h.trans ((bit_cases (a.val w).toAdd).resolve_left (fun z => by have := hz.mpr z;rw [h] at this;exact (by decide : (1:Bit)≠0) this)).symm
theorem minimal_cohomology_eq_multiplicator (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hm : Nat.card Q=2^m) (hd : Nat.card (Q ⧸ frattini Q)=2^d) : r₂ Q=relRank π := by
  apply le_antisymm (cohomology_le_multiplicator π hπ)
  let _ : Finite (cycles₂ Q) := Finite.of_injective (fun a : cycles₂ Q => a.val.val) (fun _ _ e => Subtype.ext (Subtype.ext e))
  let _ : Finite (H₂ Q) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective (LinearMap.range (boundaryLinear Q)))
  let _ := Fintype.ofFinite (H₂ Q)
  let _ := Fintype.ofFinite (Additive (RelCharacters π))
  have hcard := Nat.card_le_card_of_surjective _ (relation_character_over_cohomology π hπ hm hd)
  change Nat.card (Additive (RelCharacters π)) ≤ Nat.card (H₂ Q) at hcard
  have h₁ := Module.card_eq_pow_finrank (K := Bit) (V := H₂ Q)
  have h₂ := Module.card_eq_pow_finrank (K := Bit) (V := Additive (RelCharacters π))
  rw [←Nat.card_eq_fintype_card,ZMod.card] at h₁ h₂
  rw [h₁,h₂] at hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
end Erdos1160.CentralLifts.Survival
end

/- FreeRootQuotient -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160Growth Erdos1160Growth.LowerTriangularUpper Erdos1160.DeepJacobi
private def atBit {d : ℕ} (i : Fin d) : CentralKernelCount.BitGroup d →* C₂ where
  toFun w := .ofAdd (w.toAdd i)
  map_one' := rfl
  map_mul' _ _ := rfl
variable {d m : ℕ} {Q : Type} [Group Q] [Finite Q]
theorem free_root_factor (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π) (hm : Nat.card Q=2^m)
    (hd : Nat.card (Q ⧸ frattini Q)=2^d) :
    ∃ h : Cover π →* FreeRoot d, Function.Surjective h := by
  let F := freeMark d
  let proj := BilinearExtension.projection (form (freeArray d))
  have mem (w : π.ker) : (F w.val).base=0 := by
    funext j
    exact minimal_chars_kill_ker π hπ hm hd ((atBit j).comp (proj.comp F)) w.property
  have zmem (w : π.ker) : F w.val ∈ Subgroup.center (FreeRoot d) := by
    have h : (⟨0,(F w.val).fiber⟩ : FreeRoot d)=F w.val := BilinearExtension.ext (mem w).symm rfl
    exact h ▸ BilinearExtension.central_fiber _
  let char (j : Fin (d*(d+1)/2)) : π.ker →* C₂ := {
    toFun w := .ofAdd ((F w.val).fiber j)
    map_one' := congrArg (fun v : FreeRoot d => Multiplicative.ofAdd (v.fiber j)) F.map_one
    map_mul' u v := by
      change (F (u.val*v.val)).fiber j=(F u.val).fiber j+(F v.val).fiber j
      rw [map_mul,BilinearExtension.mul_fiber,mem u,map_zero];simp }
  have inv (j : Fin (d*(d+1)/2)) (g : FreeGroup (Fin d)) (w : π.ker) :
      char j (conjugateRelation π g w)=char j w := by
    change Multiplicative.ofAdd ((F (g*w.val*g⁻¹)).fiber j)=_
    rw [map_mul,map_mul,map_inv,Subgroup.mem_center_iff.mp (zmem w) (F g),mul_inv_cancel_right]
    rfl
  have hN : universalKernel π ≤ F.ker := by
    rintro _ ⟨w,hw,rfl⟩
    apply BilinearExtension.ext (mem w)
    funext j
    let a : RelCharacters π := ⟨char j,inv j⟩
    exact congrArg (fun v : Multiplicative (Adual π) => v.toAdd (Additive.ofMul a)) (show evalHom π w=1 from hw)
  let h : Cover π →* FreeRoot d := QuotientGroup.lift _ F hN
  refine ⟨h,fun z => ?_⟩
  obtain ⟨w,rfl⟩ := freeMark_onto d z
  exact ⟨QuotientGroup.mk' _ w,rfl⟩
theorem universal_binary_root (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hm : Nat.card Q=2^m) (hd : Nat.card (Q ⧸ frattini Q)=2^d) :
    Nonempty ((Cover π ⧸ binaryThird (Cover π)) ≃* FreeRoot d) := by
  obtain ⟨h,hh⟩ := free_root_factor π hπ hm hd
  have hN : binaryThird (Cover π) ≤ h.ker := (Subgroup.map_eq_bot_iff _).mp
    ((binaryThird_map_eq h hh).trans (freeRoot_binaryThird d))
  let g := QuotientGroup.lift _ h hN
  have hg : Function.Surjective g := fun z => by obtain ⟨x,rfl⟩ := hh z;exact ⟨QuotientGroup.mk' _ x,rfl⟩
  have hcap := binary_quotient_cover_order π hπ hm
  rw [←freeRoot_order d] at hcap
  have hc := cover_card π hπ
  rw [hm,←pow_add] at hc
  let _ : Finite (Cover π) := Nat.finite_of_card_ne_zero (hc ▸ Nat.ne_of_gt (Nat.two_pow_pos _))
  exact ⟨MulEquiv.ofBijective g ((Nat.bijective_iff_surjective_and_card g).2
    ⟨hg,le_antisymm hcap (Nat.card_le_card_of_surjective g hg)⟩)⟩
theorem exact_root_cohomology (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    {s : ℕ} (hQ : Nat.card Q=2^(d+s)) (hd : Nat.card (Q ⧸ frattini Q)=2^d) :
    BinaryFactor.r₂ Q+s = d*(d+1)/2+nucleusRank π := by
  obtain ⟨e⟩ := universal_binary_root π hπ hQ hd
  have h := (binaryThird (Cover π)).card_eq_card_quotient_mul_card_subgroup
  rw [cover_card π hπ,hQ,(Nat.card_congr e.toEquiv).trans (freeRoot_order d),nucleus_card π hπ hQ,←pow_add,←pow_add] at h
  have h' := Nat.pow_right_injective (by decide : 2 ≤ 2) h
  rw [minimal_cohomology_eq_multiplicator π hπ hQ hd]
  omega
end Erdos1160.CentralLifts.Survival
end

/- StripOptimization -/
section
namespace Erdos1160.DescendantTree
noncomputable def rootExponent (d z : ℝ) := z*d*(d+1)/2-d^2-z^2
noncomputable def leadingExponent (m : ℝ) := 2*m^3/27-4*m^2/9
def roundedDelta (d s t : ℕ) := s+t-d/2
def clippingCharge (d s t : ℕ) :=
  let w := t-(d/2-1000)
  let U := 2*roundedDelta d s t+12
  (2*s+1)*w*(s+w)+50*U*(U+1)
private theorem clipping_nat {d s t : ℕ} (hd : 2000 ≤ d) :
    let Δ := roundedDelta d s t
    clippingCharge d s t ≤ 3*(Δ+1001)^3+50*(2*Δ+12)*(2*Δ+13) := by
  dsimp only
  let Δ := roundedDelta d s t
  let w := t-(d/2-1000)
  have hc : (2*s+1)*w*(s+w) ≤ 3*(Δ+1001)^3 := by
    by_cases h : w=0
    · simp [h]
    · have hh : s+w ≤ Δ+1001 := by dsimp [w,Δ,roundedDelta] at *; omega
      have h₁ : 2*s+1 ≤ 3*(Δ+1001) := by omega
      have h₂ := Nat.mul_le_mul (Nat.mul_le_mul h₁ (show w≤Δ+1001 by omega)) hh
      nlinarith only [h₂]
  change _+50*(2*Δ+12)*(2*Δ+12+1) ≤ _
  exact Nat.add_le_add_right hc _
private theorem rounded_delta_bound (d s t : ℕ) :
    (roundedDelta d s t : ℝ) ≤ max 0 ((s:ℝ)+t-d/2)+1 := by
  have hd : d ≤ 2*(d/2)+1 := by omega
  have hh : (d:ℝ) ≤ 2*(d/2:ℕ)+1 := by exact_mod_cast hd
  by_cases hl : d/2 ≤ s+t
  · unfold roundedDelta
    rw [Nat.cast_sub hl,Nat.cast_add]
    linarith only [le_max_right (0:ℝ) ((s:ℝ)+t-d/2), hh]
  · rw [roundedDelta,Nat.sub_eq_zero_of_le (by omega : s+t ≤ d/2),Nat.cast_zero]
    linarith only [le_max_left (0:ℝ) ((s:ℝ)+t-d/2)]
private theorem clipping_real {d s t : ℕ} (hd : 2000 ≤ d) :
    let y := max 0 ((s:ℝ)+t-d/2)
    (clippingCharge d s t : ℝ) ≤ 3*y^3+10000000000*(y^2+y+1) := by
  dsimp only
  let y := max 0 ((s:ℝ)+t-d/2)
  have hy : 0 ≤ y := le_max_left _ _
  let Δ : ℝ := roundedDelta d s t
  have hΔ : Δ ≤ y+1 := rounded_delta_bound d s t
  have hnat : (clippingCharge d s t : ℝ) ≤ 3*(Δ+1001)^3+50*(2*Δ+12)*(2*Δ+13) := by
    dsimp only [Δ]
    have h := clipping_nat (s:=s) (t:=t) hd
    dsimp only at h
    exact_mod_cast h
  have hd0 : 0≤Δ := by dsimp [Δ]; positivity
  have hcube := pow_le_pow_left₀ (by positivity : 0≤Δ+1001) (show Δ+1001 ≤ y+1002 by linarith) 3
  have hprod := mul_le_mul (show 2*Δ+12 ≤ 2*y+14 by linarith) (show 2*Δ+13 ≤ 2*y+15 by linarith)
    (by linarith : 0 ≤ 2*Δ+13) (by linarith : 0 ≤ 2*y+14)
  nlinarith only [hy, sq_nonneg y,hcube,hprod,hnat]
private theorem strip_polynomial {d z e k charge : ℝ} (hd : 1000000000000 ≤ d) (hk : 0 ≤ k)
    (hdz : z=d/2+e) (hl : -d/1000 ≤ e) (hu : e ≤ d/1000)
    (hc : charge ≤ 3*(max 0 e)^3+10000000000*((max 0 e)^2+(max 0 e)+1)) :
    rootExponent d z+charge+k*d*z ≤ leadingExponent (d+z)+(2*k/9)*(d+z)^2+
      (1+k/3)^2*d+10000000000 := by
  have hd0 : 0 ≤ d := by linarith
  have heq : rootExponent d z + k*d*z - leadingExponent (d+z) - (2*k/9)*(d+z)^2 =
      (5/6+k/3)*d*e - (d/3+5/9+2*e/27+2*k/9)*e^2 := by rw [hdz]; unfold rootExponent leadingExponent; ring
  have hcoef : 0 ≤ d/3+5/9+2*e/27+2*k/9 := by linarith
  by_cases he : e ≤ 0
  · rw [max_eq_left he] at hc
    have h₁ := mul_nonpos_of_nonneg_of_nonpos (show 0≤(5/6+k/3)*d by positivity) he
    have h₂ := mul_nonneg hcoef (sq_nonneg e)
    have h₃ := mul_nonneg (sq_nonneg (1+k/3)) hd0
    linarith only [heq,hc,h₁,h₂,h₃]
  · have he0 := le_of_not_ge he
    rw [max_eq_right he0] at hc
    have h₁ := mul_le_mul_of_nonneg_right hu (sq_nonneg e)
    have h₂ := mul_le_mul_of_nonneg_right hd (sq_nonneg e)
    have h₃ := mul_le_mul_of_nonneg_right hd he0
    have h₄ := mul_nonneg he0 (sq_nonneg e)
    have h₅ := mul_nonneg hk (sq_nonneg e)
    have h₆ := mul_nonneg hd0 (sq_nonneg (e/2-(1+k/3)))
    have h₇ := mul_nonneg hd0 (sq_nonneg e)
    nlinarith only [heq,hc,h₁,h₂,h₃,h₄,h₅,h₆,h₇,sq_nonneg e, mul_nonneg hd0 he0]
theorem strip_optimization (d s t k : ℕ) (hd : 1000000000000 ≤ d)
    (hl : -(d:ℝ)/1000 ≤ (s:ℝ)+t-d/2) (hu : (s:ℝ)+t-d/2 ≤ d/1000) :
    rootExponent d ((s:ℝ)+t)+(clippingCharge d s t:ℝ)+k*d*((s:ℝ)+t) ≤
      leadingExponent ((d:ℝ)+s+t)+(2*(k:ℝ)/9)*((d:ℝ)+s+t)^2+
        (1+(k:ℝ)/3)^2*d+10000000000 := by
  have h := strip_polynomial (d:= (d:ℝ)) (z:=(s:ℝ)+t) (e:=(s:ℝ)+t-d/2) (k:=(k:ℝ))
    (by exact_mod_cast hd) (by positivity) (by ring) hl hu (clipping_real (by omega : 2000 ≤ d))
  simpa [add_assoc] using h
end Erdos1160.DescendantTree
end

/- Actual56 -/
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
theorem root_frattini_order : Nat.card (R.group ⧸ frattini R.group)=2^d := by
  have he := QuotientGroup.quotientKerEquivOfSurjective R.elementary R.onto
  have h := (Nat.card_congr he.toEquiv).trans (vectors_card d)
  rwa [R.ker_eq,←frattini_eq_squareCore R.size] at h
theorem root_at_height (π : FreeGroup (Fin d) →* R.group) (hπ : Function.Surjective π) :
    height (b₀ d s) 0 (initial R.size)=nucleusRank π := by
  have h := exact_root_cohomology π hπ R.size (root_frattini_order R)
  have hs := actual_image_dimension R.elementary R.onto R.ker_eq R.deep_trivial R.width (initial R.size)
  rw [show height (b₀ d s) 0 (initial R.size)=r₂ R.group-(d*(d+1)/2-s) by simp [height,initial,b₀];rfl]
  omega
theorem su_xia_5_6 (π : FreeGroup (Fin d) →* R.group) (hπ : Function.Surjective π)
    {t Δ : ℕ} (hd : 10000 ≤ d) (hs : s ≤ d) (hΔ : 1000*Δ ≤ d+1000) (ht : 2*(s+t) ≤ d+2*Δ+1) :
    let w := t-(d/2-1000)
    let U := 2*Δ+12
    (descendants R.group (d+s) t).ncard ≤
      (d+3)^t*2^(t*(b₀ d s+nucleusRank π)+(2*s+1)*w*(s+w)+50*U*(U+1)) := by
  dsimp only
  have h := fixed_root_leaf_bound children (height (b₀ d s)) (fun _ _ y=>y.gain) (loss R)
    (b:=b₀ d s) hd hs hΔ ht (fun i _ x=>node_capacity R i x) (fun i _ x=>node_branch R i x)
    (fun i _ x y hy=>(node_step R i hy).1)
    (fun i _ x y hy=>gain_le i hy R.elementary R.onto R.ker_eq)
    (fun i _ x=>loss_bound R i x) (fun i _ x=>local_one R x (by omega)) (fun i _ x r j=>local_gaussian R (r:=r) (j:=j) x)
    (initial R.size)
  rw [root_at_height R π hπ] at h
  exact (count_le_leaves R.size t).trans h
theorem zero_nucleus_empty (π : FreeGroup (Fin d) →* R.group) (hπ : Function.Surjective π)
    (hν : nucleusRank π=0) (j : ℕ) : descendants R.group (d+s) (j+1)=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨G,hG,⟨f,hf,hk⟩,_⟩
  exact zero_nucleus_no_descendants π hπ R.size hν j hG f hf hk
end Erdos1160.DescendantTree.Actual
end

/- ActualSmall -/
section
namespace Erdos1160.DescendantTree.Actual
open BinaryFactor BinaryFactor.Cocycle BinaryFactor.Elementary CategoryTheory
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
theorem descendants_finite (Q : Type) [Group Q] [Finite Q] {m : ℕ} (hQ : Nat.card Q=2^m) (t : ℕ) :
    (descendants Q m t).Finite := by
  classical
  let v := initial hQ
  apply (terminals label children t 0 v).finite_toSet.subset
  rintro _ ⟨G,hG,⟨f,hf,hk⟩,rfl⟩
  exact covered t v hG f hf hk
end Erdos1160.DescendantTree.Actual
end

/- BoundedWidthPopulation -/
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
end Erdos1160.DescendantTree.Actual
end

/- KernelAutomorphisms -/
section
namespace Erdos1160.KernelAutomorphisms
def quotientAction {G : Type*} [Group G] (N : Subgroup G) [N.Characteristic] :
    MulAut G →* MulAut (G ⧸ N) where
  toFun e := QuotientGroup.congr N N e (Subgroup.characteristic_iff_map_eq.mp inferInstance e)
  map_one' := by apply MulEquiv.ext; rintro ⟨x⟩; rfl
  map_mul' _ _ := by apply MulEquiv.ext; rintro ⟨x⟩; rfl
end Erdos1160.KernelAutomorphisms
end

/- FrattiniKernel -/
section
namespace Erdos1160.KernelAutomorphisms
variable {G : Type*} [Group G] {d : ℕ}
abbrev FrattiniKernel (G : Type*) [Group G] := (quotientAction (frattini G)).ker
def GeneratingLifts (g : Fin d → G) := {x : Fin d → G // ∀ i,
  QuotientGroup.mk' (frattini G) (x i) = QuotientGroup.mk' (frattini G) (g i)}
private def liftCoord (g : Fin d → G) : GeneratingLifts g ≃ (Fin d → frattini G) where
  toFun x i := ⟨(g i)⁻¹*(x.val i), (QuotientGroup.eq_one_iff _).mp (by
    change QuotientGroup.mk' (frattini G) _ = 1
    rw [map_mul,map_inv,x.property,inv_mul_cancel])⟩
  invFun w := ⟨fun i => g i*w i,fun i => by simp⟩
  left_inv x := Subtype.ext (funext (fun i => mul_inv_cancel_left _ _))
  right_inv w := funext (fun i => Subtype.ext (inv_mul_cancel_left _ _))
theorem generating_lifts_generate [Finite G] (g : Fin d → G)
    (hg : Subgroup.closure (Set.range g) = ⊤) (x : GeneratingLifts g) :
    Subgroup.closure (Set.range x.val) = ⊤ := by
  apply frattini_nongenerating
  apply top_unique
  rw [← hg]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  have hm : (x.val i)⁻¹*g i ∈ frattini G := (QuotientGroup.eq_one_iff _).mp (by
    change QuotientGroup.mk' (frattini G) _ = 1
    rw [map_mul,map_inv,x.property,inv_mul_cancel])
  have hl : x.val i ∈ Subgroup.closure (Set.range x.val) := Subgroup.subset_closure ⟨i,rfl⟩
  let H := Subgroup.closure (Set.range x.val)
  have he := (H ⊔ frattini G).mul_mem ((show H ≤ H ⊔ frattini G from le_sup_left) hl)
    ((show frattini G ≤ H ⊔ frattini G from le_sup_right) hm)
  simpa using he
private instance liftAction (g : Fin d → G) : MulAction (FrattiniKernel G) (GeneratingLifts g) where
  smul a x := ⟨fun i => a.val (x.val i),fun i => by
    have ha : quotientAction (frattini G) a.val = 1 := a.property
    have he := DFunLike.congr_fun ha (QuotientGroup.mk' (frattini G) (x.val i))
    exact he.trans (x.property i)⟩
  one_smul x := rfl
  mul_smul a b x := rfl
theorem frattini_kernel_card_dvd [Finite G] (g : Fin d → G)
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    Nat.card (FrattiniKernel G) ∣ (Nat.card (frattini G))^d := by
  classical
  let X := GeneratingLifts g
  let A := FrattiniKernel G
  let _ : Finite X := Finite.of_equiv _ (liftCoord g).symm
  have hi (x : X) : Function.Injective (fun a : A => a • x) := by
    intro a b he
    apply Subtype.ext
    apply MulEquiv.toMonoidHom_injective
    apply MonoidHom.eq_of_eqOn_dense (generating_lifts_generate g hg x)
    rintro _ ⟨i,rfl⟩
    exact congrFun (congrArg Subtype.val he) i
  have hc (x : X) : Nat.card A = Nat.card (MulAction.orbit A x) := by
    let f (a : A) : MulAction.orbit A x := ⟨a • x, ⟨a,rfl⟩⟩
    have onto : Function.Surjective f := by
      rintro ⟨y,⟨a,rfl⟩⟩
      exact ⟨a,rfl⟩
    exact Nat.card_congr (Equiv.ofBijective f ⟨fun _ _ h => hi x (congrArg Subtype.val h),onto⟩)
  have hcard : Nat.card X = (Nat.card (frattini G))^d := by
    rw [Nat.card_congr (liftCoord g),Nat.card_fun,Nat.card_fin]
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient A X)
  rw [← hcard,Nat.card_congr (MulAction.selfEquivSigmaOrbits A X),Nat.card_sigma]
  apply Finset.dvd_sum
  intro q _
  exact dvd_of_eq (hc q.out)
end Erdos1160.KernelAutomorphisms
end

/- SmallGenerators -/
section
namespace Erdos1160Enumeration
variable {G : Type*} [Group G] [Finite G]
private theorem double_card_le {H K : Subgroup G} (h : H < K) :
    2 * Nat.card H ≤ Nat.card K := by
  have hc : Nat.card H < Nat.card K := by
    change Nat.card (H : Set G) < Nat.card (K : Set G)
    simpa only [Nat.card_coe_set_eq] using
      (Set.ncard_lt_ncard (show (H : Set G) ⊂ (K : Set G) from h))
  obtain ⟨q, hq⟩ := Subgroup.card_dvd_of_le h.le
  have htwo : 2 ≤ q := by
    by_contra! hx
    have : q = 0 ∨ q = 1 := by omega
    rcases this with rfl | rfl <;> simp_all
  simpa [hq, Nat.mul_comm] using Nat.mul_le_mul_left (Nat.card H) htwo
private theorem compressed_generators (s : Finset G) :
    ∃ t : Finset G, Subgroup.closure (s : Set G) = Subgroup.closure (t : Set G) ∧
      2 ^ t.card ≤ Nat.card (Subgroup.closure (t : Set G)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, rfl, ?_⟩
    simpa using Nat.card_pos (α := ↥(Subgroup.closure ((∅ : Finset G) : Set G)))
  | @insert x s hx ih =>
    obtain ⟨t, hst, ht⟩ := ih
    have hnew : Subgroup.closure ((insert x s : Finset G) : Set G) =
        Subgroup.closure ((insert x t : Finset G) : Set G) := by
      simp only [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union, hst]
    by_cases hmem : x ∈ Subgroup.closure (t : Set G)
    · refine ⟨t, hnew.trans ?_, ht⟩
      apply le_antisymm
      · apply (Subgroup.closure_le _).mpr
        rw [Finset.coe_insert]
        exact Set.insert_subset hmem Subgroup.subset_closure
      · exact Subgroup.closure_mono (by simp)
    · have hlt : Subgroup.closure (t : Set G) <
          Subgroup.closure ((insert x t : Finset G) : Set G) := by
        apply lt_of_le_of_ne (Subgroup.closure_mono (by simp))
        intro he
        apply hmem
        rw [he]
        exact Subgroup.subset_closure (by simp)
      have hout : x ∉ t := fun hx => hmem (Subgroup.subset_closure hx)
      refine ⟨insert x t, hnew, ?_⟩
      rw [Finset.card_insert_of_notMem hout, pow_succ, Nat.mul_comm]
      exact (Nat.mul_le_mul_left 2 ht).trans (double_card_le hlt)
theorem exists_generating_tuple (G : Type*) [Group G] [Finite G] {m : ℕ}
    (hcard : Nat.card G ≤ 2^m) :
    ∃ f : Fin m → G, Subgroup.closure (Set.range f) = ⊤ := by
  classical
  letI := Fintype.ofFinite G
  obtain ⟨s, hgen, hs⟩ := compressed_generators (Finset.univ : Finset G)
  have hs' : Subgroup.closure (s : Set G) = ⊤ := by simpa using hgen.symm
  have hsize : s.card ≤ m := (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp <|
    hs.trans <| (Nat.card_le_card_of_injective _ Subtype.val_injective).trans hcard
  let f (i : Fin m) : G := if hi : i.val < s.card then
    (s.equivFin.symm ⟨i.val, hi⟩ : s).val else 1
  refine ⟨f, top_unique ?_⟩
  rw [← hs']
  apply Subgroup.closure_mono
  intro x hx
  let i := s.equivFin ⟨x, hx⟩
  refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hsize⟩, ?_⟩
  dsimp only [f]
  rw [dif_pos i.isLt]
  exact congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨x, hx⟩)
end Erdos1160Enumeration
end

/- TwoValuation -/
section
namespace Erdos1160.KernelAutomorphisms
open Matrix
theorem frattini_has_rank_tuple {G : Type*} [Group G] [Finite G] {r : ℕ}
    (hq : (frattini G).index=2^r) : ∃ g : Fin r → G, Subgroup.closure (Set.range g)=⊤ := by
  let N := frattini G
  let π := QuotientGroup.mk' N
  obtain ⟨v,hv⟩ := Erdos1160Enumeration.exists_generating_tuple (G ⧸ N) (show Nat.card (G ⧸ N) ≤ 2^r from hq.le)
  choose g hg using fun i => QuotientGroup.mk'_surjective N (v i)
  refine ⟨g,frattini_nongenerating ?_⟩
  let D := Subgroup.closure (Set.range g)
  have hmap : D.map π = ⊤ := by
    change (Subgroup.closure (Set.range g)).map π = ⊤
    rw [MonoidHom.map_closure,←Set.range_comp]
    have he : π ∘ g = v := funext hg
    rwa [he]
  apply top_unique
  intro x _
  obtain ⟨y,hy,hxy⟩ := (show π x ∈ D.map π by rw [hmap]; trivial)
  have hn : y⁻¹*x ∈ N := (QuotientGroup.eq_one_iff _).mp (by
    change π _ = 1
    rw [map_mul,map_inv,hxy,inv_mul_cancel])
  have h := (D ⊔ N).mul_mem ((show D ≤ D ⊔ N from le_sup_left) hy)
    ((show N ≤ D ⊔ N from le_sup_right) hn)
  simpa using h
end Erdos1160.KernelAutomorphisms
end

/- MomentAutomorphisms25 -/
section
namespace Erdos1160.Paper85
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160.KernelAutomorphisms OrbitUp
private def linearAction {X : Type} [Group X] {d : ℕ}
    (v : X ≃* Multiplicative (V d)) (u : MulAut X) : L d :=
  let f : V d ≃+ V d := MulEquiv.toAdditive (v.symm.trans (u.trans v))
  { f with map_smul' := ZMod.map_smul f.toAddMonoidHom }
private theorem linearAction_coord {X : Type} [Group X] {d : ℕ}
    (v : X ≃* Multiplicative (V d)) (u : MulAut X) (x : X) :
    linearAction v u ((v x).toAdd) = (v (u x)).toAdd := by
  change (v (u (v.symm (v x)))).toAdd = _
  rw [v.symm_apply_apply]
private theorem linearAction_inj {X : Type} [Group X] {d : ℕ}
    (v : X ≃* Multiplicative (V d)) : Function.Injective (linearAction v) := by
  intro x y he
  apply MulEquiv.ext
  intro z
  apply v.injective
  exact congrArg Multiplicative.ofAdd ((linearAction_coord v x z).symm.trans
    ((DFunLike.congr_fun he _).trans (linearAction_coord v y z)))
variable {P : Type} [Group P] [Finite P] {d s : ℕ}
theorem automorphism_stabilizer_25
    (v : P ⧸ frattini P ≃* Multiplicative (V d))
    (w : frattini (P ⧸ binaryThird P) ≃* Multiplicative (V s)) (q : Q d s)
    (hsq : ∀ x : P, (w.symm (Multiplicative.ofAdd (q (v (QuotientGroup.mk' (frattini P) x)).toAdd)) : (P ⧸ binaryThird P))=
      (QuotientGroup.mk' (binaryThird P) x)^2) :
    Nat.card (MulAut P) ≤ Nat.card (MulAction.stabilizer (Change d s) q) * Nat.card (frattini P)^d := by
  classical
  let F := frattini P
  let f := quotientAction F
  let π := QuotientGroup.mk' F
  let ρ := QuotientGroup.mk' (binaryThird P)
  let base (x : P) := (v (π x)).toAdd
  have baseSurj : Function.Surjective base := fun x => by
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective F (v.symm (Multiplicative.ofAdd x))
    refine ⟨a,?_⟩
    exact congrArg (fun z => (v z).toAdd) ha |>.trans (congrArg Multiplicative.toAdd (v.apply_symm_apply _))
  let changes (u : MulAut P) : Change d s :=
    (linearAction v (f u),linearAction w (MulAut.characteristic (frattini (P ⧸ binaryThird P)) (quotientAction (binaryThird P) u)))
  have first (u : MulAut P) (x : P) : (changes u).1 (base x)=base (u x) := linearAction_coord v (f u) (π x)
  have inSt (u : MulAut P) : changes u ∈ MulAction.stabilizer (Change d s) q := by
    let k := quotientAction (binaryThird P) u
    let l := MulAut.characteristic (frattini (P ⧸ binaryThird P)) k
    have intertwine (x : P) : (changes u).2 (q (base x))=q (base (u x)) := by
      let z := w.symm (Multiplicative.ofAdd (q (base x)))
      have rz : (z : (P ⧸ binaryThird P))=(ρ x)^2 := hsq x
      have he : l z=w.symm (Multiplicative.ofAdd (q (base (u x)))) := by
        apply Subtype.ext
        change k (z : (P ⧸ binaryThird P))=_
        rw [rz,map_pow,hsq]
        rfl
      have conv := linearAction_coord w l z
      change linearAction w l (q (base x))=_
      dsimp only [z] at conv
      rw [w.apply_symm_apply] at conv
      exact conv.trans (congrArg (fun y => (w y).toAdd) he |>.trans (congrArg Multiplicative.toAdd (w.apply_symm_apply _)))
    rw [MulAction.mem_stabilizer_iff]
    apply QuadraticMap.ext
    intro t
    change (changes u).2 (q ((changes u).1.symm t)) = q t
    obtain ⟨x,hx⟩ := baseSurj ((changes u).1.symm t)
    have ht : (changes u).1 (base x)=t := by rw [hx,LinearEquiv.apply_symm_apply]
    rw [←hx,intertwine,←first,ht]
  choose pre hp using (f.rangeRestrict_surjective : Function.Surjective f.rangeRestrict)
  let encode (x : f.range) : MulAction.stabilizer (Change d s) q := ⟨changes (pre x),inSt _⟩
  have hi : Function.Injective encode := by
    intro x y he
    have eq : linearAction v (f (pre x))=linearAction v (f (pre y)) := congrArg (fun z => z.val.1) he
    have e₁ := congrArg Subtype.val (hp x)
    have e₂ := congrArg Subtype.val (hp y)
    exact Subtype.ext (e₁.symm.trans ((linearAction_inj v eq).trans e₂))
  have hr : F.index=2^d := by
    change Nat.card (P ⧸ frattini P)=_
    rw [Nat.card_congr v.toEquiv]
    change Nat.card (Fin d → ZMod 2) = _
    rw [Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card,ZMod.card]
  obtain ⟨g,hg⟩ := frattini_has_rank_tuple (G := P) hr
  have hc : Nat.card (MulAut P)=Nat.card f.range * Nat.card f.ker := by
    rw [←Subgroup.index_ker,Subgroup.index_mul_card]
  rw [hc]
  exact Nat.mul_le_mul (Nat.card_le_card_of_injective encode hi)
    (Nat.le_of_dvd (Nat.pow_pos Nat.card_pos) (frattini_kernel_card_dvd g hg))
end Erdos1160.Paper85
end

/- RootSquareCoordinates25 -/
section
namespace Erdos1160.Paper85
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160.CentralLifts.Survival (third_quot_squares binaryThird_le_squares)
open Erdos1160Growth.LowerTriangularUpper
open OrbitUp (Q)
variable {P : Type} [Group P] [Finite P]
private theorem quotient_base_equiv {m : ℕ} (hm : Nat.card P=2^m) :
    ∃ e : P ⧸ frattini P ≃* (P ⧸ binaryThird P) ⧸ frattini (P ⧸ binaryThird P), ∀ x : P,
      e (QuotientGroup.mk' (frattini P) x) =
      QuotientGroup.mk' (frattini (P ⧸ binaryThird P)) (QuotientGroup.mk' (binaryThird P) x) := by
  let π := QuotientGroup.mk' (binaryThird P)
  let φ := (QuotientGroup.mk' (frattini (P ⧸ binaryThird P))).comp π
  have hπ := QuotientGroup.mk'_surjective (binaryThird P)
  obtain ⟨b,hb⟩ := ((IsPGroup.of_card hm).to_quotient (binaryThird P)).exists_card_eq
  have hmF : (frattini P).map π=frattini (P ⧸ binaryThird P) := by
    rw [frattini_eq_squareCore hm,frattini_eq_squareCore hb]
    exact CentralKernelCount.squareCore_map π hπ
  have hk : π.ker ≤ frattini P := by
    rw [QuotientGroup.ker_mk',frattini_eq_squareCore hm]
    exact binaryThird_le_squares P
  have he : φ.ker=frattini P := by
    change (((QuotientGroup.mk' (frattini (P ⧸ binaryThird P))).comp π).ker)=_
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk',←hmF,Subgroup.comap_map_eq_self hk]
  let e := (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ ((QuotientGroup.mk'_surjective _).comp hπ))
  refine ⟨e,fun x=>?_⟩
  rfl
theorem root_form_automorphism_model {m d s : ℕ} (hm : Nat.card P=2^m)
    (hd : (frattini P).index=2^d) (hs : Nat.card (frattini (P ⧸ binaryThird P))=2^s) :
    ∃ (q : Q d s) (v : P ⧸ frattini P ≃* Multiplicative (OrbitUp.V d))
        (w : frattini (P ⧸ binaryThird P) ≃* Multiplicative (OrbitUp.V s)),
      (∀x : P,(w.symm (Multiplicative.ofAdd (q (v (QuotientGroup.mk' (frattini P) x)).toAdd)) : (P ⧸ binaryThird P))=
        (QuotientGroup.mk' (binaryThird P) x)^2) ∧
      (∀ k : ℕ, Nat.card (MulAut P)^k ≤ 2^(k*d*(m-d))*
        Nat.card (MulAction.stabilizer (OrbitUp.Change d s) q)^k) ∧
      ∃ B : OrbitUp.V d →+ OrbitUp.V d →+ OrbitUp.V s, q=diagonalQ B ∧
        Nonempty (Erdos1160Growth.BilinearExtension B ≃* (P ⧸ binaryThird P)) := by
  classical
  obtain ⟨b,hb⟩ := ((IsPGroup.of_card hm).to_quotient (binaryThird P)).exists_card_eq
  have st := third_quot_squares P
  dsimp only at st
  rw [←frattini_eq_squareCore hb] at st
  obtain ⟨e,he⟩ := quotient_base_equiv hm
  obtain ⟨w⟩ := exist_elementary_coords st.2 hs
  have hidx : Nat.card ((P ⧸ binaryThird P) ⧸ frattini (P ⧸ binaryThird P))=2^d := (Nat.card_congr e.toEquiv).symm.trans hd
  have hz (x : (P ⧸ binaryThird P) ⧸ frattini (P ⧸ binaryThird P)) : x*x=1 := by
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (frattini (P ⧸ binaryThird P)) x
    rw [←map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [frattini_eq_squareCore hb]
    exact Subgroup.subset_closure ⟨y,rfl⟩
  obtain ⟨vQ⟩ := exist_elementary_coords hz hidx
  let v := e.trans vQ
  let S := dataOfSubgroup (frattini (P ⧸ binaryThird P)) st.1 w vQ
  obtain ⟨σ,B,hσ,hmul⟩ := S.exists_bilinear_section
  let q := diagonalQ B
  have hsq (x : P) : (w.symm (Multiplicative.ofAdd (q (v (QuotientGroup.mk' (frattini P) x)).toAdd)) : (P ⧸ binaryThird P))=
      (QuotientGroup.mk' (binaryThird P) x)^2 := by
    let z := QuotientGroup.mk' (binaryThird P) x
    have hb' : (v (QuotientGroup.mk' (frattini P) x)).toAdd = S.base z := by
      change (vQ (e _)).toAdd=_
      rw [he]; rfl
    rw [hb']
    change S.liftK (B (S.base z) (S.base z))=z^2
    obtain ⟨t,ht⟩ := S.section_decomp σ hσ z
    have hsq' : (S.liftK t * σ (S.base z))*(S.liftK t * σ (S.base z)) =
        S.liftK (B (S.base z) (S.base z)) := by
      rw [mul_assoc,(S.liftK_comm t (σ (S.base z))).symm.left_comm,←mul_assoc,←S.liftK_add,
        two_copies_zero,S.liftK_zero,one_mul,hmul,two_copies_zero,S.section_zero σ B hmul,mul_one]
    rwa [ht,←pow_two,eq_comm] at hsq'
  refine ⟨q,v,w,hsq,(fun k => ?_),B,rfl,⟨S.sectionEquiv σ B hσ hmul⟩⟩
  have h := automorphism_stabilizer_25 v w q hsq
  obtain ⟨sP,hsP⟩ := ((IsPGroup.of_card hm).to_subgroup (frattini P)).exists_card_eq
  have hc := (frattini P).index_mul_card
  rw [hd,hsP,hm,←pow_add] at hc
  have hds := Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  have exp : sP=m-d := by omega
  rw [hsP,exp] at h
  calc
    _ ≤ (Nat.card (MulAction.stabilizer (OrbitUp.Change d s) q)*(2^(m-d))^d)^k := Nat.pow_le_pow_left h _
    _ = _ := by rw [Nat.mul_pow,←Nat.pow_mul,←Nat.pow_mul,Nat.mul_comm];congr 2;ring
end Erdos1160.Paper85
end

/- StabilizerMoments33 -/
section
namespace Erdos1160.Paper85
open Finset Fintype
open scoped Classical
variable {G X : Type*} [Fintype G] [Fintype X]
noncomputable def stabilizing (fix : G → Finset X) (x : X) : Finset G := univ.filter (fun g=>x∈fix g)
noncomputable def commonFix {h : ℕ} (fix : G → Finset X) (t : Fin h → G) : Finset X :=
  univ.filter (fun x=>∀ i,x∈fix (t i))
theorem stabilizer_moment_expand (fix : G → Finset X) (h : ℕ) :
    (∑ x : X,(stabilizing fix x).card^h)=∑ t : Fin h → G,(commonFix fix t).card := by
  classical
  have row (x : X) : (stabilizing fix x).card^h=∑ t : Fin h → G, if ∀ i,x∈fix (t i) then 1 else 0 := by
    rw [←Fintype.card_piFinset_const]
    have he : Fintype.piFinset (fun _ : Fin h=>stabilizing fix x) =
        univ.filter (fun t : Fin h → G=>∀ i,x∈fix (t i)) := by ext t;simp [stabilizing]
    rw [he];simp
  simp_rw [row]
  rw [Finset.sum_comm]
  congr 1
  funext t
  simp [commonFix]
theorem stabilizer_moment_bounds (fix : G → Finset X) (h L H : ℕ) (Z B : Finset G)
    (hz : ∀ g∈Z,fix g=Finset.univ) (hL : ∀ g∉B,(fix g).card ≤ L)
    (hH : ∀ g∈B,g∉Z → (fix g).card ≤ H) :
    Fintype.card X*Z.card^h ≤ ∑ x : X,(stabilizing fix x).card^h ∧
    (∑ x : X,(stabilizing fix x).card^h) ≤
      Fintype.card X*Z.card^h + L*(Fintype.card G)^h + H*B.card^h := by
  classical
  constructor
  · calc
      _ = ∑ _x : X,Z.card^h := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x _=>Nat.pow_le_pow_left (Finset.card_le_card (show Z⊆stabilizing fix x from
        fun g hg=>by simp [stabilizing,hz g hg])) _)
  rw [stabilizer_moment_expand]
  let T (s : Finset G) := Fintype.piFinset (fun _ : Fin h=>s)
  have ht (s : Finset G) : (T s).card=s.card^h := Fintype.card_piFinset_const _ _
  have sub (t : Fin h → G) (i : Fin h) : commonFix fix t⊆fix (t i) := fun x hx=>(Finset.mem_filter.mp hx).2 i
  have cap (t : Fin h → G) : (commonFix fix t).card ≤
      (if t∈T Z then Fintype.card X else 0)+L+(if t∈T B then H else 0) := by
    by_cases z : t∈T Z
    · have hx := Finset.card_le_univ (commonFix fix t)
      simp only [if_pos z]; omega
    by_cases b : t∈T B
    · have zz : ¬∀i,t i∈Z := by simpa [T] using z
      obtain ⟨i,hi⟩ := not_forall.mp zz
      have bb : ∀i,t i∈B := by simpa [T] using b
      simp only [if_pos b,if_neg z,zero_add]
      exact (Finset.card_le_card (sub t i)).trans ((hH _ (bb i) hi).trans (Nat.le_add_left ..))
    · have bb : ¬∀i,t i∈B := by simpa [T] using b
      obtain ⟨i,hi⟩ := not_forall.mp bb
      simpa only [if_neg z,if_neg b,zero_add,add_zero] using (Finset.card_le_card (sub t i)).trans (hL _ hi)
  apply (Finset.sum_le_sum (fun t _=>cap t)).trans_eq
  simp [Finset.sum_add_distrib, Finset.sum_ite_mem, ht, Nat.mul_comm]
theorem action_moment_bounds [Group G] [MulAction G X] (h L H : ℕ) (Z B : Finset G)
    (hz : ∀ g∈Z,∀ x : X,g • x=x)
    (hL : ∀ g∉B,(Finset.univ.filter (fun x : X=>g • x=x)).card ≤ L)
    (hH : ∀ g∈B,g∉Z → (Finset.univ.filter (fun x : X=>g • x=x)).card ≤ H) :
    Fintype.card X*Z.card^h ≤ ∑ x : X,Nat.card (MulAction.stabilizer G x)^h ∧
    (∑ x : X,Nat.card (MulAction.stabilizer G x)^h) ≤
      Fintype.card X*Z.card^h + L*(Fintype.card G)^h + H*B.card^h := by
  classical
  let fixes (g : G) := univ.filter (fun x : X=>g • x=x)
  have hc (x : X) : (stabilizing fixes x).card=Nat.card (MulAction.stabilizer G x) := by
    let e : ↥(stabilizing fixes x) ≃ MulAction.stabilizer G x :=
      Equiv.subtypeEquivRight (fun g=>by simp [stabilizing,fixes,MulAction.mem_stabilizer_iff])
    simpa using Nat.card_congr e
  simpa only [hc] using stabilizer_moment_bounds fixes h L H Z B
    (fun g hg=>by ext x;simp [fixes,hz g hg]) hL hH
theorem action_moment_scaled [Group G] [MulAction G X] (h u : ℕ) (hu : 0 < u) (B : Finset G)
    (hL : ∀ g∉B,(Finset.univ.filter (fun x : X=>g • x=x)).card*
      (Fintype.card G)^h*u ≤ Fintype.card X)
    (hH : ∀ g∈B,g≠1 → (Finset.univ.filter (fun x : X=>g • x=x)).card*
      B.card^h*u ≤ Fintype.card X) :
    (∑ x : X,Nat.card (MulAction.stabilizer G x)^h)*u ≤ Fintype.card X*(u+2) := by
  classical
  let F (g : G) := (Finset.univ.filter (fun x : X=>g • x=x)).card
  let L := (Finset.univ \ B).sup F
  let H := (B.erase 1).sup F
  have hl : L*(Fintype.card G)^h*u ≤ Fintype.card X := by
    apply Finset.sup_induction (p:=fun z=>z*(Fintype.card G)^h*u ≤ Fintype.card X) (s:=Finset.univ \ B) (f:=F)
    · simp
    · intro a ha b hb
      rcases le_total a b with h|h
      · simpa [sup_eq_right.mpr h] using hb
      · simpa [sup_eq_left.mpr h] using ha
    · intro g hg
      exact hL g (Finset.mem_sdiff.mp hg).2
  have hh : H*B.card^h*u ≤ Fintype.card X := by
    apply Finset.sup_induction (p:=fun z=>z*B.card^h*u ≤ Fintype.card X) (s:=B.erase 1) (f:=F)
    · simp
    · intro a ha b hb
      rcases le_total a b with h|h
      · simpa [sup_eq_right.mpr h] using hb
      · simpa [sup_eq_left.mpr h] using ha
    · intro g hg
      exact hH g (Finset.mem_of_mem_erase hg) (Finset.ne_of_mem_erase hg)
  have htop := (action_moment_bounds h L H ({1} : Finset G) B
    (fun g hg x=>by simp only [Finset.mem_singleton] at hg; simp [hg])
    (fun g hg=>Finset.le_sup (f:=F) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hg⟩))
    (fun g hg hn=>Finset.le_sup (f:=F) (Finset.mem_erase.mpr ⟨by simpa using hn,hg⟩))).2
  simp only [Finset.card_singleton,one_pow,mul_one] at htop
  have hm := Nat.mul_le_mul_right u htop
  rw [Nat.add_mul,Nat.add_mul] at hm
  nlinarith only [hm,hl,hh]
end Erdos1160.Paper85
end

/- TensorMomentMargins -/
section
namespace OrbitUp.Moment
abbrev divisor (A B h : ℕ) := 64*A*h*(B+1)+8
abbrev mass (h B : ℕ) := h*(1+B^2)+1
abbrev threshold (A B h : ℕ) := divisor A B h * (16*A*divisor A B h*mass h B + 8*mass h B + 8)
abbrev cut (d A B h : ℕ) := d/divisor A B h
abbrev saving (d A : ℕ) := d^2/(32*A)
abbrev nearExponent (d s A B h : ℕ) := h*(2*d*cut d A B h+2*s*cut d A B h)
abbrev farExponent (d s h : ℕ) := h*(d^2+s^2)
private theorem near_budget {d s A B h : ℕ} (hB : s ≤ B*d) :
    8*A*(nearExponent d s A B h + saving d A) ≤ d^2 := by
  let M := divisor A B h
  let R := cut d A B h
  have small : M*R ≤ d := Nat.mul_div_le ..
  have hmul := Nat.mul_le_mul_left (64*A*h*R) (Nat.add_le_add_left hB d)
  have cap := Nat.mul_le_mul_right d small
  have sav : 32*A*saving d A ≤ d^2 := Nat.mul_div_le _ _
  change 8*A*(h*(2*d*R+2*s*R)+saving d A) ≤ _
  dsimp only [M,divisor] at cap
  nlinarith only [hmul,cap,sav,Nat.zero_le (R*d)]
private theorem far_budget {d s h B A : ℕ} (hB : s ≤ B*d) :
    farExponent d s h+saving d A ≤ mass h B*d^2 := by
  have hb := Nat.mul_le_mul_left h (Nat.pow_le_pow_left hB 2)
  have hs := Nat.div_le_self (d^2) (32*A)
  dsimp only [farExponent,mass,saving]
  nlinarith only [hb,hs]
private theorem cut_bound (d A B h : ℕ) : 4*cut d A B h ≤ d := by
  exact (Nat.mul_le_mul_right _ (show 4 ≤ divisor A B h by dsimp [divisor];omega)).trans (Nat.mul_div_le ..)
private theorem fixed_big {d A B h f r : ℕ} (hr : r ≤ cut d A B h) (hf : r+f=d) (hd : 4 ≤ d) :
    d ≤ 2*(f-1) := by have := cut_bound d A B h;omega
theorem near_nontrivial_output {d s A B h f r : ℕ} (hA : 1 ≤ A) (hB : s ≤ B*d) (hd : 4 ≤ d)
    (hr : r ≤ cut d A B h) (hf : r+f=d) :
    nearExponent d s A B h+saving d A ≤ slotsN f := by
  have hb := near_budget (A:=A) (h:=h) hB
  have hf' : d ≤ 2*f := by have := fixed_big hr hf hd;omega
  have hh := (Nat.pow_le_pow_left hf' 2).trans (show (2*f)^2 ≤ 8*slotsN f by have := twice_slots f; nlinarith only [this])
  have ha := Nat.mul_le_mul_right (8*(nearExponent d s A B h+saving d A)) hA
  nlinarith only [hb,hh,ha]
theorem near_nontrivial_input {d s A B h f r : ℕ} (hA : 0 < A) (hlo : d ≤ A*s) (hB : s ≤ B*d) (hd : 4 ≤ d)
    (hr : r ≤ cut d A B h) (hf : r+f=d) :
    nearExponent d s A B h+saving d A ≤ s*(f-1) := by
  have hb := near_budget (A:=A) (h:=h) hB
  have hmul := Nat.mul_le_mul hlo (fixed_big hr hf hd)
  apply Nat.le_of_mul_le_mul_left _ (show 0 < 8*A by omega)
  nlinarith only [hmul,hb,Nat.zero_le (A*s*(f-1))]
private theorem cut_large {d A B h : ℕ} (hd : threshold A B h ≤ d) :
    16*A*divisor A B h*mass h B+8*mass h B+8 ≤ cut d A B h := by
  apply (Nat.le_div_iff_mul_le (by dsimp [divisor];omega)).mpr
  simpa only [threshold,Nat.mul_comm] using hd
theorem far_nontrivial_output {d s A B h f r u : ℕ} (hB : s ≤ B*d) (hd : threshold A B h ≤ d)
    (hr : r ≤ cut d A B h) (hf : r+f=d) (hu : cut d A B h < u) :
    farExponent d s h+saving d A ≤ u*slotsN f := by
  have dmin : 4 ≤ d := by have := cut_large hd;have := cut_bound d A B h;omega
  have df : d ≤ 2*f := by have := fixed_big hr hf dmin;omega
  have q := twice_slots f
  have sd : d^2 ≤ 8*slotsN f := by have hh := Nat.pow_le_pow_left df 2;nlinarith only [hh,q]
  have sl := Nat.mul_le_mul_left (mass h B) sd
  have big : 8*mass h B ≤ u := by have := cut_large hd;omega
  exact (far_budget hB).trans (sl.trans (by simpa only [←Nat.mul_assoc,Nat.mul_comm (mass h B) 8] using Nat.mul_le_mul_right (slotsN f) big))
theorem far_nontrivial_input {d s A B h r k : ℕ} (hlo : d ≤ A*s) (hB : s ≤ B*d)
    (hd : threshold A B h ≤ d) (hr : cut d A B h < r) (hk : r ≤ 2*k+2) :
    farExponent d s h+saving d A ≤ s*slotsN k := by
  let M := divisor A B h
  let C := mass h B
  have hi := cut_large hd
  have dM : d≤ M*r := (Nat.lt_mul_div_succ d (by dsimp [M,divisor];omega : 0 < M)).le.trans
    (Nat.mul_le_mul_left M (Nat.succ_le_of_lt hr))
  have kmin : 8*A*M*C ≤ k := by
    change 16*A*M*C+8*C+8 ≤ cut d A B h at hi
    rw [show 16*A*M*C=2*(8*A*M*C) by ring] at hi
    omega
  have kr : r ≤ 4*k := by omega
  have ds := (Nat.mul_le_mul_left M kr)
  have big := Nat.mul_le_mul_right (s*k) kmin
  have mult := Nat.mul_le_mul_left (2*C) (Nat.mul_le_mul hlo (dM.trans ds))
  have sqcost := Nat.mul_le_mul_left s (twice_slots k).symm.le
  apply (far_budget hB).trans
  change C*d^2 ≤ s*slotsN k
  nlinarith only [big,mult,sqcost,Nat.zero_le (s*k)]
end OrbitUp.Moment
end

/- FixedInput -/
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

/- Stratify -/
section
namespace OrbitUp
noncomputable abbrev rankChange {d : ℕ} (a : L d) := Module.finrank K (LinearMap.range (a.toLinearMap - LinearMap.id))
end OrbitUp
end

/- MoveRank -/
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

/- TensorMomentFixed -/
section
namespace OrbitUp
theorem fixed_inputs_output_rank {d s : ℕ} (a : L d) (b : L s) :
    let f := Module.finrank K (fixedSubspace a)
    Nat.card (mixedFix a b) * 2^(rankChange b*(f+f*(f-1)/2)) ≤ Nat.card (Q d s) := by
  classical
  let f := Module.finrank K (fixedSubspace a)
  let e : fixedSubspace a ≃ₗ[K] V f := (Module.finBasis K _).equivFun
  let u := (fixedSubspace a).subtype.comp e.symm.toLinearMap
  have au (x : V f) : a (u x) = u x := (mem_fixedSubspace a _).mp (e.symm x).property
  obtain ⟨c,cinv⟩ := u.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr ((fixedSubspace a).subtype_injective.comp e.symm.injective))
  have cu (x : V f) : c (u x) = x := LinearMap.congr_fun cinv x
  let D := b.toLinearMap - LinearMap.id
  let r := rankChange b
  let w : D.range ≃ₗ[K] V r := (Module.finBasis K _).equivFun
  obtain ⟨j,hj⟩ := D.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr D.surjective_rangeRestrict)
  let t := j.comp w.symm.toLinearMap
  have decode (x : V r) : D (t x)=(w.symm x).val := congrArg Subtype.val (LinearMap.congr_fun hj (w.symm x))
  let enc (p : mixedFix a b × Q f r) : Q d s := p.1.val+t.compQuadraticMap (p.2.comp c)
  have delta (q : mixedFix a b) (z : Q f r) (x : V f) : D (enc (q,z) (u x))=(w.symm (z x)).val := by
    change D (q.val (u x)+t (z (c (u x))))=_
    rw [cu,map_add,decode]
    change (b (q.val (u x))-q.val (u x))+_=_
    rw [q.property,au,sub_self,zero_add]
  have inj : Function.Injective enc := by
    rintro ⟨q,z⟩ ⟨g,y⟩ h
    have he : z=y := by
      apply QuadraticMap.ext
      intro x
      apply w.symm.injective
      apply Subtype.ext
      rw [←delta q z x,h,delta g y x]
    subst y
    refine Prod.ext (Subtype.ext (QuadraticMap.ext fun x => ?_)) rfl
    exact add_right_cancel (by exact congrArg (fun v : Q d s=>v x) h : q.val x+t (z (c x))=g.val x+t (z (c x)))
  simpa only [Nat.card_prod,card_forms_exact] using Nat.card_le_card_of_injective enc inj
end OrbitUp
end

/- TensorMomentPolar -/
section
namespace OrbitUp
theorem nontrivial_input_polar_saving {d s : ℕ} (a : L d) (ha : a≠1) :
    Nat.card (mixedFix a (1 : L s)) * 2^(s*(Module.finrank K (fixedSubspace a)-1)) ≤ Nat.card (Q d s) := by
  classical
  obtain ⟨x,hx⟩ : ∃ x : V d,a x≠x := by
    by_contra! h;exact ha (LinearEquiv.ext h)
  obtain ⟨i,hi⟩ : ∃ i : Fin d,a x i≠x i := by by_contra! h;exact hx (funext h)
  let l : V d →ₗ[K] K := LinearMap.proj i
  have diff : l (a x)-l x=1 := (show ∀ z : K,z≠0 → z=1 by decide) _
    (sub_ne_zero.mpr hi)
  let F := fixedSubspace a
  let coord :=  l.comp F.subtype
  let W := coord.ker
  let k := Module.finrank K W
  have hw : Module.finrank K F-1 ≤ k := by
    have eqn := coord.finrank_range_add_finrank_ker
    have up : Module.finrank K coord.range ≤ 1 := coord.range.finrank_le.trans_eq (Module.finrank_self K)
    dsimp [k,W]
    omega
  let e : W ≃ₗ[K] V k := (Module.finBasis K _).equivFun
  let u := F.subtype.comp (W.subtype.comp e.symm.toLinearMap)
  have au (y : V k) : a (u y)=u y := (mem_fixedSubspace a _).mp (e.symm y).val.property
  have lu (y : V k) : l (u y)=0 := (e.symm y).property
  obtain ⟨c,cinv⟩ := u.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr
    (F.subtype_injective.comp (W.subtype_injective.comp e.symm.injective)))
  have cu (y : V k) : c (u y)=y := LinearMap.congr_fun cinv y
  let M := V k →ₗ[K] V s
  let B (t : M) := (LinearMap.lsmul K (V s)).compl₁₂ l (t.comp c)
  let noise (t : M) := LinearMap.BilinMap.toQuadraticMap (B t)
  let enc (p : mixedFix a (1 : L s) × M) : Q d s := p.1.val+noise p.2
  let D (q : Q d s) (y : V k) := QuadraticMap.polar q (a x) (u y) - QuadraticMap.polar q x (u y)
  have addD (q t : Q d s) (y : V k) : D (q+t) y=D q y+D t y := by
    simp only [D,QuadraticMap.polar,QuadraticMap.add_apply]
    abel
  have invD (q : mixedFix a (1 : L s)) (y : V k) : D q.val y=0 := by
    have inv (v : V d) : q.val (a v)=q.val v := (q.property v).symm
    apply sub_eq_zero.mpr
    change q.val (a x+u y)-q.val (a x)-q.val (u y)=_
    rw [←au y,←map_add,inv,inv,au]
    rfl
  have decode (t : M) (y : V k) : D (noise t) y=t y := by
    dsimp only [D,noise]
    rw [LinearMap.BilinMap.polar_toQuadraticMap,LinearMap.BilinMap.polar_toQuadraticMap]
    change (l (a x) • t (c (u y)) + l (u y) • t (c (a x))) -
      (l x • t (c (u y)) + l (u y) • t (c x))=_
    rw [lu,zero_smul,zero_smul,add_zero,add_zero,cu,←sub_smul,diff,one_smul]
  have recover (q : mixedFix a (1 : L s)) (t : M) (y : V k) : D (enc (q,t)) y=t y := by
    change D (q.val+noise t) y=_
    rw [addD,invD,decode,zero_add]
  have inj : Function.Injective enc := by
    rintro ⟨q,t⟩ ⟨p,r⟩ h
    have he : t=r := LinearMap.ext (fun y => (recover q t y).symm.trans
      (h ▸ recover p r y))
    subst r
    exact Prod.ext (Subtype.ext (add_right_cancel (show q.val+noise t=p.val+noise t from h))) rfl
  have hcard : Nat.card M=2^(s*k) := by
    rw [Module.natCard_eq_pow_finrank (K := K),Nat.card_zmod,Module.finrank_linearMap]
    simp [V,Nat.mul_comm]
  have hcard' := Nat.card_le_card_of_injective enc inj
  rw [Nat.card_prod,hcard] at hcard'
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left s hw))).trans hcard'
end OrbitUp
end

/- CompleteStabilizerMoment81 -/
section
namespace OrbitUp.Moment
open Erdos1160.Paper85
open scoped Classical
private theorem fixes_card {d s : ℕ} (g : Change d s) (F : Finset (Q d s))
    (hF : ∀ q : Q d s, q ∈ F ↔ g • q = q) : F.card = Nat.card (mixedFix g.1 g.2) := by
  let e : F ≃ mixedFix g.1 g.2 := Equiv.subtypeEquivRight (fun q => by
    rw [hF]
    constructor
    · intro he x
      have h := congrArg (fun z : Q d s => z (g.1 x)) he
      change g.2 (q (g.1.symm (g.1 x))) = q (g.1 x) at h
      rwa [g.1.symm_apply_apply] at h
    · intro h
      apply QuadraticMap.ext
      intro x
      exact (h (g.1.symm x)).trans (congrArg q (g.1.apply_symm_apply x)))
  simpa using Nat.card_congr e
private theorem equiv_ball_card {d s R : ℕ} [Fintype (Change d s)] :
    (Finset.univ.filter (fun g : Change d s=>rankChange g.1 ≤ R ∧ rankChange g.2 ≤ R)).card ≤ 2^(2*d*R+2*s*R) := by
  classical
  let B := Finset.univ.filter (fun g : Change d s=>rankChange g.1 ≤ R ∧ rankChange g.2 ≤ R)
  let I := {a : L d // rankChange a ≤ R}
  let J := {b : L s // rankChange b ≤ R}
  let f (g : B) : I×J :=
    (⟨g.val.1,(Finset.mem_filter.mp g.property).2.1⟩,⟨g.val.2,(Finset.mem_filter.mp g.property).2.2⟩)
  have hi : Function.Injective f := fun _ _ eq => Subtype.ext
    (Prod.ext (congrArg (fun z : I×J=>z.1.val) eq) (congrArg (fun z : I×J=>z.2.val) eq))
  have h := Nat.card_le_card_of_injective f hi
  rw [Nat.card_prod] at h
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,Nat.pow_add] using
    h.trans (Nat.mul_le_mul (count_small_rank_changes d R) (count_small_rank_changes s R))
theorem complete_form_stabilizer_moment {d s A B h : ℕ} (hA : 0 < A) (hlo : d ≤ A*s) (hhi : s ≤ B*d)
    (hd : threshold A B h ≤ d) [Fintype (Q d s)] :
    Fintype.card (Q d s) ≤ ∑ q : Q d s, Nat.card (MulAction.stabilizer (Change d s) q)^h ∧
      (∑ q : Q d s,Nat.card (MulAction.stabilizer (Change d s) q)^h)*2^(saving d A) ≤
        Fintype.card (Q d s)*(2^(saving d A)+2) := by
  classical
  let := Fintype.ofFinite (Change d s)
  let R := cut d A B h
  let ball := Finset.univ.filter (fun g : Change d s=>rankChange g.1 ≤ R ∧ rankChange g.2 ≤ R)
  have minimum : 4 ≤ d := by
    have m : 8 ≤ divisor A B h := Nat.le_add_left ..
    have bound : 1 ≤ 16*A*divisor A B h*mass h B+8*mass h B+8 := by omega
    have hd' := Nat.mul_le_mul m bound
    change divisor A B h*(16*A*divisor A B h*mass h B+8*mass h B+8) ≤ d at hd
    omega
  have allCard : Fintype.card (Change d s)^h ≤ 2^(farExponent d s h) := by
    have hle := Nat.mul_le_mul (gl_upper d) (gl_upper s)
    rw [←Nat.card_prod,←Nat.pow_add] at hle
    change Nat.card (Change d s)≤_ at hle
    rw [←Nat.card_eq_fintype_card,show farExponent d s h = (d*d+s*s)*h by dsimp [farExponent];ring,Nat.pow_mul]
    exact Nat.pow_le_pow_left hle _
  have ballCard : ball.card^h ≤ 2^(nearExponent d s A B h) := by
    change ball.card^h ≤ 2^(h*(2*d*R+2*s*R))
    rw [Nat.mul_comm h,Nat.pow_mul]
    exact Nat.pow_le_pow_left equiv_ball_card _
  refine ⟨?_,action_moment_scaled (G:=Change d s) (X:=Q d s) h _ (Nat.two_pow_pos _) ball ?_ ?_⟩
  · calc
      _ = ∑ _q : Q d s,1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun q _=>Nat.succ_le_of_lt (Nat.pow_pos Nat.card_pos))
  · intro g hg
    conv_lhs =>
      arg 1
      arg 1
      equals Nat.card (mixedFix g.1 g.2) =>
        apply fixes_card g
        intro q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [←Nat.card_eq_fintype_card (α:=Q d s)]
    apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ allCard)).trans
    rw [Nat.mul_assoc,←Nat.pow_add]
    by_cases ha : rankChange g.1 ≤ R
    · have hb : R < rankChange g.2 := lt_of_not_ge (fun h => hg (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,h⟩))
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
        (far_nontrivial_output hhi hd ha (rank_add_fixed g.1) hb))).trans (fixed_inputs_output_rank g.1 g.2)
    · obtain ⟨k,hk,move⟩ := exists_moves_rank g.1
      rw [card_forms_exact]
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
        (far_nontrivial_input hlo hhi hd (lt_of_not_ge ha) hk))).trans (moved_fixed_card g.2 move)
  · intro g hg gn
    conv_lhs =>
      arg 1
      arg 1
      equals Nat.card (mixedFix g.1 g.2) =>
        apply fixes_card g
        intro q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [←Nat.card_eq_fintype_card (α:=Q d s)]
    apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ballCard)).trans
    rw [Nat.mul_assoc,←Nat.pow_add]
    have hr := (Finset.mem_filter.mp hg).2.1
    by_cases hb : g.2=1
    · have ha : g.1≠1 := fun ha => gn (Prod.ext ha hb)
      rw [hb]
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
        (near_nontrivial_input hA hlo hhi minimum hr (rank_add_fixed g.1)))).trans (nontrivial_input_polar_saving g.1 ha)
    · rw [card_forms_exact]
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
        (near_nontrivial_output hA hhi minimum hr (rank_add_fixed g.1)))).trans (fixed_input_card g.1 g.2 hb)
theorem complete_form_moment_le_two {d s A B h : ℕ} (hA : 0 < A) (hlo : d ≤ A*s) (hhi : s ≤ B*d)
    (hd : max (threshold A B h) (32*A) ≤ d) [Fintype (Q d s)] :
    (∑ q : Q d s,Nat.card (MulAction.stabilizer (Change d s) q)^h) ≤ 2*Fintype.card (Q d s) := by
  have h := (complete_form_stabilizer_moment (h:=h) hA hlo hhi ((le_max_left ..).trans hd)).2
  have hD : 32*A ≤ d := (le_max_right ..).trans hd
  have hs : 1 ≤ saving d A := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    rw [one_mul]
    exact hD.trans (by have := Nat.mul_le_mul_left d (show 1 ≤ d by omega);nlinarith only [this])
  have hu : 2 ≤ 2^(saving d A) := (Nat.pow_le_pow_right (by decide : 0 < 2) hs)
  have hp := Nat.mul_le_mul_left (Fintype.card (Q d s)) (show 2^(saving d A)+2 ≤ 2*2^(saving d A) by omega)
  apply Nat.le_of_mul_le_mul_right _ (Nat.two_pow_pos (saving d A))
  exact h.trans (hp.trans_eq (by ring))
end OrbitUp.Moment
end

/- CoreRange89 -/
section
namespace Erdos1160.OuterExtensions
open CategoryTheory
abbrev ClassOf (n : ℕ) := Tables.orderClasses n
noncomputable def orderRep {n : ℕ} (c : ClassOf n) : FiniteGrp.{0} := c.property.choose
theorem rep_size {n : ℕ} (c : ClassOf n) : Nat.card (orderRep c) = n := c.property.choose_spec.1
end Erdos1160.OuterExtensions
end

/- CoreMoment29 -/
section
namespace Erdos1160.OuterExtensions
open CategoryTheory SylowActions
open scoped BigOperators
noncomputable instance classFintype (n : ℕ) : Fintype (ClassOf n) := (Tables.orderClasses_finite n).fintype
end Erdos1160.OuterExtensions
end

/- MomentAsymptotics89 -/
section
namespace Erdos1160.Paper89
open Filter

def envelope (k : ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ᶠ a : ℕ in atTop, f a ^ 27 * 2^(12*a^2) ≤ 2^(2*a^3+6*k*a^2+C*a)
end Erdos1160.Paper89
end

/- NonrootProfiles85 -/
section
namespace Erdos1160.Paper85
open OuterExtensions DescendantTree DescendantTree.Actual
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160Growth.LowerTriangularUpper
open scoped Classical
def inCentralStrip (m d : ℕ) : Prop :=
  1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d
noncomputable def generatorRank {m : ℕ} (c : ClassOf (2^m)) :=
  Nat.log 2 (frattini (orderRep c)).index
def ProfileClasses (m d s : ℕ) := {c : ClassOf (2^m) //
  (frattini (orderRep c)).index=2^d ∧
  Nat.card (frattini (orderRep c ⧸ binaryThird (orderRep c)))=2^s}
noncomputable instance (m d s : ℕ) : Fintype (ProfileClasses m d s) := by
  unfold ProfileClasses
  exact Fintype.ofFinite _
noncomputable def profileMoment (m d s k : ℕ) : ℕ :=
  ∑ x : ProfileClasses m d s, Nat.card (MulAut (orderRep x.val))^k
end Erdos1160.Paper85
end

/- WeightedRanks -/
section
namespace Erdos1160.DescendantTree
theorem thousandth_moment {X : Type*} (T : Finset X) (weight : X→ℕ) (k : ℕ) {A U : ℝ}
    (hcard : (T.card:ℝ) ≤ 2^A)
    (hm : ∑x∈T,(weight x:ℝ)^(k*1000) ≤ 2^U) :
    ∑x∈T,(weight x:ℝ)^k ≤ 2^(A+(U-A)/1000) := by
  let w (x:X) := (weight x:ℝ)^k
  have h := pow_sum_le_card_mul_sum_pow (s:=T) (f:=w) (fun x _=>by dsimp [w];positivity) 999
  change (∑ x ∈ T,w x)^1000≤(T.card:ℝ)^999*(∑x∈T,w x^1000) at h
  have h₁ := pow_le_pow_left₀ (by positivity : 0 ≤ (T.card:ℝ)) hcard 999
  have h₂ : ∑x∈T,w x^1000 ≤ 2^U := by simpa only [w,←pow_mul] using hm
  apply le_of_pow_le_pow_left₀ (n:=1000) (by decide) (by positivity)
  have hn : 0≤∑x∈T,w x^1000 := Finset.sum_nonneg (fun x _=>pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)
  apply (h.trans (mul_le_mul h₁ h₂ hn (pow_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le _))).trans_eq
  rw [←Real.rpow_mul_natCast (by norm_num : 0≤(2:ℝ)),←Real.rpow_add (by norm_num : (0:ℝ) < 2),
    ←Real.rpow_mul_natCast (by norm_num : 0≤(2:ℝ))]
  congr 1
  push_cast
  ring
end Erdos1160.DescendantTree
end

/- ThirdChart -/
section
namespace Erdos1160.DeepJacobi
open CentralKernelCount
open scoped commutatorElement
variable {G : Type*} [Group G] {q n s : ℕ}
def coreMark (i : Fin q) : Fin (n+q) := Fin.natAdd n i
def outMark (i : Fin n) : Fin (n+q) := Fin.castAdd q i
end Erdos1160.DeepJacobi
end

/- JacobiCoordinates -/
section
namespace OrbitUp
open Erdos1160.DeepJacobi (W coreMark outMark)
open scoped Matrix
def jacobiPair {d t : ℕ} (M : Matrix (Fin d) (Fin t) K) (x : V d) (w : V t) : K :=
  x ⬝ᵥ M.mulVec w
def JacobiCompatible {d t : ℕ} (M : Matrix (Fin d) (Fin t) K) (F : Q d t) : Prop :=
  ∀ x y z : V d, jacobiPair M x (QuadraticMap.polar F y z) =
    jacobiPair M y (QuadraticMap.polar F x z) - jacobiPair M z (QuadraticMap.polar F x y)
theorem jacobiPair_basis {d t : ℕ} (M : Matrix (Fin d) (Fin t) K) (i : Fin d) (w : V t) :
    jacobiPair M (basis i) w = M.mulVec w i := by
  simp [jacobiPair,basis,dotProduct,Pi.single_apply]
def chartSplit {q s : ℕ} (v : Equiv.Perm (Fin (q+s))) (w : V (q+s)) : W q s :=
  (fun i => w (v (finSumFinEquiv (.inl i))), fun j => w (v (finSumFinEquiv (.inr j))))
def chartJoin {q s : ℕ} (v : Equiv.Perm (Fin (q+s))) : W q s →ₗ[K] V (q+s) where
  toFun p := fun j => Sum.elim p.1 p.2 (finSumFinEquiv.symm (v.symm j))
  map_add' x y := by funext j; simp only [Pi.add_apply, Pi.smul_apply]; cases finSumFinEquiv.symm (v.symm j) <;> rfl
  map_smul' c x := by funext j; simp only [Pi.add_apply, Pi.smul_apply]; cases finSumFinEquiv.symm (v.symm j) <;> rfl
theorem join_split {q s : ℕ} (v : Equiv.Perm (Fin (q+s))) (w : V (q+s)) :
    chartJoin v (chartSplit v w) = w := by
  funext j
  have he (z : Fin q ⊕ Fin s) :
      Sum.elim (chartSplit v w).1 (chartSplit v w).2 z = w (v (finSumFinEquiv z)) := by
    cases z <;> rfl
  change Sum.elim _ _ _ = w j
  rw [he]
  simp
theorem split_inj {q s : ℕ} (v : Equiv.Perm (Fin (q+s))) : Function.Injective (chartSplit v) :=
  fun _ _ h => (join_split v _).symm.trans ((congrArg (chartJoin v) h).trans (join_split v _))
private def selectRows {n k : ℕ} (r : Fin k → Fin n) : V n →ₗ[K] V k where
  toFun x := x ∘ r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def jacobiCore {n q s : ℕ} (M : Matrix (Fin (n+q)) (Fin (q+s)) K)
    (u : Equiv.Perm (Fin (n+q))) (v : Equiv.Perm (Fin (q+s))) : W q s →+ V q :=
  ((selectRows (u ∘ coreMark)).comp (M.mulVecLin.comp (chartJoin v))).toAddMonoidHom
def jacobiOutside {n q s : ℕ} (M : Matrix (Fin (n+q)) (Fin (q+s)) K)
    (u : Equiv.Perm (Fin (n+q))) (v : Equiv.Perm (Fin (q+s))) (i : Fin n) : W q s →+ K :=
  ((LinearMap.proj (u (outMark i))).comp (M.mulVecLin.comp (chartJoin v))).toAddMonoidHom
theorem core_split {n q s : ℕ} (M : Matrix (Fin (n+q)) (Fin (q+s)) K)
    (u : Equiv.Perm (Fin (n+q))) (v : Equiv.Perm (Fin (q+s))) (w : V (q+s)) (i : Fin q) :
    jacobiCore M u v (chartSplit v w) i = jacobiPair M (basis (u (coreMark i))) w := by
  rw [jacobiPair_basis]
  change M.mulVec (chartJoin v (chartSplit v w)) _ = _
  rw [join_split]
  rfl
theorem outside_split {n q s : ℕ} (M : Matrix (Fin (n+q)) (Fin (q+s)) K)
    (u : Equiv.Perm (Fin (n+q))) (v : Equiv.Perm (Fin (q+s))) (w : V (q+s)) (i : Fin n) :
    jacobiOutside M u v i (chartSplit v w) = jacobiPair M (basis (u (outMark i))) w := by
  rw [jacobiPair_basis]
  change M.mulVec (chartJoin v (chartSplit v w)) _ = _
  rw [join_split]
lemma coordPivot {n q s : ℕ} (M : Matrix (Fin (n+q)) (Fin (q+s)) K)
    (u : Equiv.Perm (Fin (n+q))) (v : Equiv.Perm (Fin (q+s))) (x : V q) :
    jacobiCore M u v (x,0) = (M.submatrix (u ∘ coreMark) (fun i : Fin q => v (finSumFinEquiv (.inl i)))).mulVec x := by
  funext i
  change ∑ j, M (u (coreMark i)) j * chartJoin v (x,0) j = _
  let f (j : Fin (q+s)) := M (u (coreMark i)) j * chartJoin v (x,0) j
  change ∑ j, f j = _
  rw [← Equiv.sum_comp v f, ← Equiv.sum_comp finSumFinEquiv (fun j => f (v j)), Fintype.sum_sum_type]
  simp [f,chartJoin,Matrix.mulVec,dotProduct,Matrix.submatrix]
theorem exists_chart_perms {n q s : ℕ} (M : Matrix (Fin (n+q)) (Fin (q+s)) K) (h : q ≤ M.rank) :
    ∃ u : Equiv.Perm (Fin (n+q)), ∃ v : Equiv.Perm (Fin (q+s)),
      Function.Injective (fun x : V q => jacobiCore M u v (x,0)) := by
  classical
  obtain ⟨rows,cols,hunit⟩ := exists_unit_minor M h
  let col (i : Fin q) : Fin (q+s) := finSumFinEquiv (.inl i)
  have hi : Function.Injective (@coreMark q n) := by
    intro i j h
    exact Fin.ext (Nat.add_left_cancel (show n+i.val = n+j.val from congrArg Fin.val h))
  obtain ⟨u,hu⟩ := Equiv.Perm.exists_extending_pair (@coreMark q n) rows hi rows.injective
  obtain ⟨v,hv⟩ := Equiv.Perm.exists_extending_pair col cols
    (finSumFinEquiv.injective.comp Sum.inl_injective) cols.injective
  have hr : u ∘ coreMark = rows := funext hu
  have hc : (fun i : Fin q => v (finSumFinEquiv (.inl i))) = cols := funext hv
  refine ⟨u,v,fun x y e => ?_⟩
  simp only [coordPivot,hr,hc] at e
  exact Matrix.mulVec_injective_iff_isUnit.mpr hunit e
end OrbitUp
end

/- PolarChart -/
section
namespace OrbitUp
open Erdos1160.DeepJacobi (W Array Pair Old low coreMark outMark)
def chartPol {q n t : ℕ} (u : Equiv.Perm (Fin (n+q))) (F : Q (n+q) t) (i j : Fin (n+q)) :=
  QuadraticMap.polar F (basis (u i)) (basis (u j))
def polarChart {q n s t : ℕ} (u : Equiv.Perm (Fin (n+q))) (f : V t → W q s)
    (F : Q (n+q) t) : Array q n s :=
  (Sum.elim
    (fun z => f (chartPol (q:=q) (n:=n) u F (coreMark z.1) (coreMark (low z))))
    (fun z => f (chartPol (q:=q) (n:=n) u F (coreMark z.1) (outMark z.2))),
    fun z => f (chartPol (q:=q) (n:=n) u F (outMark z.1) (outMark (low z))))
private theorem symmetric_split {X : Type} {k : ℕ} {f g : Fin k → Fin k → X}
    (sf : ∀ i j, f i j = f j i) (sg : ∀ i j, g i j = g j i) (hd : ∀ i, f i i = g i i)
    (lowers : ∀ a : Pair k, f a.1 (low a) = g a.1 (low a)) :
    ∀ i j, f i j = g i j := by
  have lo (i j : Fin k) (h : j < i) : f i j = g i j := lowers ⟨i,⟨j.val,h⟩⟩
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · exact (sf i j).trans ((lo j i h).trans (sg j i))
  · exact hd i
  · exact lo i j h
set_option maxHeartbeats 1400000 in
theorem polarChart_separates {q n s t : ℕ} (u : Equiv.Perm (Fin (n+q))) (f : V t → W q s)
    (hf : Function.Injective f) {F G : Q (n+q) t} (diag : ∀ i, F (basis i) = G (basis i))
    (h : polarChart (q:=q) (n:=n) (s:=s) u f F = polarChart (q:=q) (n:=n) (s:=s) u f G) : F=G := by
  let P := chartPol (q:=q) (n:=n) u F
  let T := chartPol (q:=q) (n:=n) u G
  have hp (i j) : P i j=P j i := QuadraticMap.polar_comm F _ _
  have ht (i j) : T i j=T j i := QuadraticMap.polar_comm G _ _
  have hd (i) : P i i=T i i := by simp only [P,T,chartPol,QuadraticMap.polar_self,diag]
  have cc (ij : Pair q) : P (coreMark ij.1) (coreMark (low ij)) = T (coreMark ij.1) (coreMark (low ij)) :=
    hf (congrArg (fun z : Array q n s => z.1 (.inl ij)) h)
  have oo (ij : Pair n) : P (outMark ij.1) (outMark (low ij)) = T (outMark ij.1) (outMark (low ij)) :=
    hf (congrArg (fun z : Array q n s => z.2 ij) h)
  have co (i : Fin q) (j : Fin n) : P (coreMark i) (outMark j)= T (coreMark i) (outMark j) :=
    hf (congrArg (fun z : Array q n s => z.1 (.inr (i,j))) h)
  have ccall (i j : Fin q) : P (coreMark i) (coreMark j)=T (coreMark i) (coreMark j) :=
    symmetric_split (f:=fun i j => P (coreMark i) (coreMark j)) (g:=fun i j => T (coreMark i) (coreMark j))
      (fun _ _ => hp _ _) (fun _ _ => ht _ _) (fun _ => hd _) cc i j
  have ooall (i j : Fin n) : P (outMark i) (outMark j)=T (outMark i) (outMark j) :=
    symmetric_split (f:=fun i j => P (outMark i) (outMark j)) (g:=fun i j => T (outMark i) (outMark j))
      (fun _ _ => hp _ _) (fun _ _ => ht _ _) (fun _ => hd _) oo i j
  have all (i j : Fin (n+q)) : P i j = T i j := by
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j => exact ooall i j
      | right j => exact (hp _ _).trans ((co j i).trans (ht _ _))
    | right i =>
      induction j using Fin.addCases with
      | left j => exact co i j
      | right j => exact ccall i j
  apply coefficients_injective
  funext z
  rcases z with i | z
  · exact diag i
  · change QuadraticMap.polar F (basis z.1) (basis (low z)) = QuadraticMap.polar G (basis z.1) (basis (low z))
    obtain ⟨i,hi⟩ := u.surjective z.1
    obtain ⟨j,hj⟩ := u.surjective (low z)
    simpa only [P,T,chartPol,hi,hj] using all i j
end OrbitUp
end

/- FixedJacobi -/
section
namespace OrbitUp
open Erdos1160.DeepJacobi (W Array compatible coreMark outMark low)
private theorem compatible_chart {q n s : ℕ} (M : Matrix (Fin (n+q)) (Fin (q+s)) K)
    (u : Equiv.Perm (Fin (n+q))) (v : Equiv.Perm (Fin (q+s))) (F : Q (n+q) (q+s))
    (h : JacobiCompatible M F) : compatible (jacobiCore M u v) (jacobiOutside M u v)
      (polarChart (q:=q) (n:=n) (s:=s) u (chartSplit v) F) := by
  intro ij c
  change jacobiCore M u v (chartSplit v (chartPol (q:=q) u F (outMark ij.1) (outMark (low ij)))) c =
    jacobiOutside M u v ij.1 (chartSplit v (chartPol (q:=q) u F (coreMark c) (outMark (low ij)))) -
    jacobiOutside M u v (low ij) (chartSplit v (chartPol (q:=q) u F (coreMark c) (outMark ij.1)))
  rw [core_split,outside_split,outside_split]
  exact h _ _ _
private theorem fixed_split {q n s : ℕ} (M : Matrix (Fin (n+q)) (Fin (q+s)) K) (hr : q ≤ M.rank) :
    Nat.card {F : Q (n+q) (q+s) // JacobiCompatible M F} * 2^(q*(n*(n-1)/2)) ≤
      2^((q+s)*slotsN (n+q)) := by
  classical
  obtain ⟨u,v,hpivot⟩ := exists_chart_perms M hr
  let D := Fin (n+q) → V (q+s)
  let C := {z : Array q n s // compatible (jacobiCore M u v) (jacobiOutside M u v) z}
  let f (x : {F : Q (n+q) (q+s) // JacobiCompatible M F}) : D × C :=
    (fun i => x.val (basis i), ⟨polarChart (q:=q) (n:=n) (s:=s) u (chartSplit v) x.val,
      compatible_chart M u v x.val x.property⟩)
  have hf : Function.Injective f := by
    intro x y e
    apply Subtype.ext
    apply polarChart_separates u (chartSplit v) (split_inj v)
    · exact congrFun (congrArg Prod.fst e)
    · exact congrArg (fun z : D × C => z.2.val) e
  have hc := Erdos1160.DeepJacobi.fixed_tensor_count (jacobiCore M u v) (jacobiOutside M u v) hpivot
  calc
    _ ≤ Nat.card (D × C) * 2^(q*(n*(n-1)/2)) := Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective f hf)
    _ = Nat.card D * (Nat.card C * 2^(q*(n*(n-1)/2))) := by rw [Nat.card_prod,Nat.mul_assoc]
    _ ≤ Nat.card D * Nat.card (Array q n s) := Nat.mul_le_mul_left _ hc
    _ = _ := by
      simp only [D,V,Nat.card_fun,Nat.card_fin,Nat.card_zmod,Erdos1160.DeepJacobi.array_card,
        ←pow_mul,← pow_add,slotsN,Nat.mul_add]
theorem fixed_jacobi_count {d t q : ℕ} (M : Matrix (Fin d) (Fin t) K) (hr : q ≤ M.rank) :
    Nat.card {F : Q d t // JacobiCompatible M F} * 2^(q*((d-q)*(d-q-1)/2)) ≤ 2^(t*slotsN d) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (hr.trans M.rank_le_height)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (hr.trans M.rank_le_width)
  simpa using fixed_split M hr
end OrbitUp
end

/- RareJacobiBudget -/
section
namespace OrbitUp
abbrev ProbeMat (d t : ℕ) := Matrix (Fin d) (Fin t) K
end OrbitUp
end

/- WeightedOrbits19 -/
section
namespace Erdos1160.Paper85
open MulAction
variable (G X : Type*) [Group G] [Fintype G] [Fintype X] [MulAction G X]
variable [Fintype (orbitRel.Quotient G X)]
theorem weighted_orbit_sum (l : ℕ) :
    (∑ o : orbitRel.Quotient G X,Nat.card (stabilizer G o.out)^l)*Fintype.card G =
        ∑ x : X,Nat.card (stabilizer G x)^(l+1) := by
  classical
  let e := selfEquivSigmaOrbits G X
  let F (x : X) := Nat.card (stabilizer G x)^(l+1)
  change _=∑ x : X,F x
  rw [←e.symm.sum_comp F,Fintype.sum_sigma,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro o _
  have st (x : orbit G o.out) : Nat.card (stabilizer G x.val)=Nat.card (stabilizer G o.out) :=
    Nat.card_congr (stabilizerEquivStabilizerOfOrbitRel x.property).toEquiv
  have orbitSize := card_orbit_mul_card_stabilizer_eq_card_group G o.out
  rw [←orbitSize]
  change _=∑ y : orbit G o.out,Nat.card (stabilizer G y.val)^(l+1)
  simp only [st,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,pow_succ]
  rw [←Nat.card_eq_fintype_card (α:=stabilizer G o.out)]
  ac_rfl
theorem weighted_admissible_orbits (l : ℕ) (S : Finset (orbitRel.Quotient G X)) :
    (∑ o∈S,Nat.card (stabilizer G o.out)^l)*Fintype.card G ≤
        ∑ x : X,Nat.card (stabilizer G x)^(l+1) := by
  rw [←weighted_orbit_sum G X]
  exact Nat.mul_le_mul_right _ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (by simp))
end Erdos1160.Paper85
end

/- LabelledRanks -/
section
namespace Erdos1160.DescendantTree
open OrbitUp MulAction
open scoped Classical
theorem orbit_weighted_filter (G X : Type*) [Group G] [Fintype G] [Fintype X] [MulAction G X]
    [Fintype (orbitRel.Quotient G X)] (S : Finset (orbitRel.Quotient G X)) (k : ℕ) :
    (∑o∈S,Nat.card (stabilizer G o.out)^k)*Fintype.card G =
      ∑x : X,if Quotient.mk'' x∈S then Nat.card (stabilizer G x)^(k+1) else 0 := by
  classical
  let e := selfEquivSigmaOrbits G X
  let F (x:X) := if Quotient.mk'' x∈S then Nat.card (stabilizer G x)^(k+1) else 0
  change _=∑x:X,F x
  rw [←e.symm.sum_comp F,Fintype.sum_sigma,Finset.sum_mul]
  have hU : Finset.univ.filter (fun o=>o∈S)=S := by ext;simp
  conv_lhs => rw [←hU,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o _
  have same (x : orbit G o.out) : Quotient.mk'' x.val=o :=
    (Quotient.sound x.property).trans (Quotient.out_eq' o)
  have term (x : orbit G o.out) : F x.val=
      if o∈S then Nat.card (stabilizer G o.out)^(k+1) else 0 := by
    simp only [F,same]
    rw [Nat.card_congr (stabilizerEquivStabilizerOfOrbitRel x.property).toEquiv]
  change _=∑x:orbit G o.out,F x.val
  simp only [term,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  by_cases ho : o∈S
  · simp only [ho,if_pos]
    rw [←card_orbit_mul_card_stabilizer_eq_card_group G o.out,pow_succ,
      ←Nat.card_eq_fintype_card (α:=stabilizer G o.out)]
    ac_rfl
  · simp [ho]
theorem rank_labeled_count (d s r : ℕ) :
    Nat.card {F : Q d s // ∃ M : ProbeMat d s, M.rank=r ∧ JacobiCompatible M F} *
       2^(r*((d-r)*(d-r-1)/2)) ≤ 2^(s*slotsN d+r*(d+s)) := by
  classical
  letI : Finite (Q d s) := Finite.of_injective _ (@coefficients_injective d s)
  let E := {M : ProbeMat d s // M.rank=r}
  letI := Fintype.ofFinite E
  let P (a:E) := {F : Q d s // JacobiCompatible a.val F}
  let T := {F : Q d s // ∃ M : ProbeMat d s,M.rank=r ∧ JacobiCompatible M F}
  let f (x:T) : (a:E) × P a := ⟨⟨x.property.choose,x.property.choose_spec.1⟩,⟨x.val,x.property.choose_spec.2⟩⟩
  have hi : Function.Injective f := fun _ _ e=>Subtype.ext (congrArg (fun t : (a:E) × P a=>t.2.val) e)
  have ca := (Nat.card_le_card_of_injective
    (fun e : E=>(⟨e.val,e.property.le⟩:{M : ProbeMat d s // M.rank ≤ r}))
    (fun _ _ h=>Subtype.ext (congrArg (fun z : {M : ProbeMat d s // M.rank ≤ r}=>z.val) h))).trans (count_small_rank_matrices d s r)
  have h := Nat.mul_le_mul_right (2^(r*((d-r)*(d-r-1)/2))) (Nat.card_le_card_of_injective f hi)
  rw [Nat.card_sigma,Finset.sum_mul] at h
  have bp (a:E) : Nat.card (P a)*2^(r*((d-r)*(d-r-1)/2)) ≤ 2^(s*slotsN d) := fixed_jacobi_count a.val a.property.ge
  apply (h.trans (Finset.sum_le_sum (fun a _=>bp a))).trans
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,smul_eq_mul,pow_add,Nat.mul_comm (2^(s*slotsN d))]
  exact Nat.mul_le_mul_right _ ca
end Erdos1160.DescendantTree
end

/- LabelledMargin -/
section
namespace Erdos1160.DescendantTree
theorem triangular_real (n : ℕ) : ((n*(n-1)/2:ℕ):ℝ)=((n:ℝ)^2-n)/2 := by
  have hn := OrbitUp.twice_slots n
  dsimp only [OrbitUp.slotsN] at hn
  have hh : 2*((n:ℝ)+((n*(n-1)/2:ℕ):ℝ))=(n:ℝ)^2+n := by exact_mod_cast hn
  linarith
private theorem labelled_numeric {d s t r : ℝ} (hd : 10000 ≤ d) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hz : s+t ≤ 51*d/100) (hr : 1 ≤ r) (hrs : r ≤ s) (range : r ≤ 7 ∨ 8 ≤ r) :
    let C := r*((d-r)^2-(d-r))/2
    (-999*C+999*r*(d+s)+d^2)/1000 + t*(s+1)*r + t*(s+t)+(d+s) ≤ -21*d^2/400 := by
  dsimp only
  have hd0 : 0 ≤ d := by linarith
  have hz0 : 0 ≤ s+t := by positivity
  have hs0 : 0 ≤ r := by linarith
  have dz := mul_self_le_mul_self hz0 hz
  have ts : t*(s+1) ≤ 0.067*d^2 := by
    have hm := mul_le_mul_of_nonneg_right hd hd0
    have hts := sq_nonneg (t-s)
    nlinarith only [hm,dz,hts,ht,hs,hz]
  have tz : t*(s+t) ≤ 0.261*d^2 := by
    have h := mul_le_mul_of_nonneg_right (show t ≤ s+t by linarith) hz0
    nlinarith only [h,dz,sq_nonneg d]
  have linear : d+s ≤ 0.001*d^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hd hd0,hz,ht]
  have control := mul_le_mul_of_nonneg_right ts hs0
  have lin := mul_le_mul_of_nonneg_left linear hs0
  by_cases hl : r ≤ 7
  · have hnr : 0.99*d ≤ d-r := by linarith
    have hns := mul_self_le_mul_self (show 0 ≤ 0.99*d by positivity) hnr
    have sc : 0.45*d^2 ≤ ((d-r)^2-(d-r))/2 := by
      nlinarith only [hns,mul_le_mul_of_nonneg_right hd hd0,hr]
    have loss := mul_le_mul_of_nonneg_left sc hs0
    nlinarith only [loss,control,lin,linear,tz,mul_le_mul_of_nonneg_right hr (sq_nonneg d),sq_nonneg d]
  · have h8 : 8 ≤ r := range.resolve_left hl
    have hnr : 0.49*d ≤ d-r := by linarith
    have hns := mul_self_le_mul_self (show 0 ≤ 0.49*d by positivity) hnr
    have sc : 0.115*d^2≤((d-r)^2-(d-r))/2 := by
      nlinarith only [hns,mul_le_mul_of_nonneg_right hd hd0,hr]
    have loss := mul_le_mul_of_nonneg_left sc hs0
    nlinarith only [loss,control,lin,linear,tz,mul_le_mul_of_nonneg_right h8 (sq_nonneg d),sq_nonneg d]
theorem labelled_margin (d s t r : ℕ) (D : ℝ) (hd : 10000 ≤ d) (hr : 1 ≤ r) (hrs : r ≤ s)
    (hz : (s:ℝ)+t ≤ 51*(d:ℝ)/100) :
    let C : ℝ := (r*((d-r)*(d-r-1)/2):ℕ)
    let A : ℝ := s*D+r*(d+s)-C
    let U : ℝ := s*D+d^2
    A+(U-A)/1000+t*(D-s+(s+1)*r)-(d^2+s^2-d-s) ≤
      (s+t)*D-d^2-(s+t)^2-21*d^2/400 := by
  dsimp only
  have hds : s ≤ d := by
    exact_mod_cast (show (s:ℝ) ≤ d by linarith [show (0:ℝ) ≤ t by positivity,show (0:ℝ) ≤ d by positivity])
  have hco : ((r*((d-r)*(d-r-1)/2):ℕ):ℝ)=(r:ℝ)*(((d:ℝ)-r)^2-((d:ℝ)-r))/2 := by
    rw [Nat.cast_mul,triangular_real,Nat.cast_sub (hrs.trans hds)]
    ring
  rw [hco]
  have h := labelled_numeric (d:=(d:ℝ)) (s:=(s:ℝ)) (t:=(t:ℝ)) (r:=(r:ℝ))
    (by exact_mod_cast hd) (by positivity) (by positivity) hz (by exact_mod_cast hr)
    (by exact_mod_cast hrs) (by exact_mod_cast (show r ≤ 7 ∨ 8 ≤ r by omega))
  dsimp only at h
  nlinarith only [h]
end Erdos1160.DescendantTree
end

/- RankSensitivePolar -/
section
namespace OrbitUp
theorem input_rank_polar_saving {d s : ℕ} (a : L d) :
    let r := Module.finrank K (LinearMap.range (a.toLinearMap-LinearMap.id))
    Nat.card (mixedFix a (1 : L s))*2^(s*r*(d-2*r)) ≤ Nat.card (Q d s) := by
  classical
  let Δ := a.toLinearMap-LinearMap.id
  let B := Δ.range
  let F := Δ.ker
  let r := Module.finrank K B
  obtain ⟨l,li⟩ := B.subtype.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr B.subtype_injective)
  let v := l.comp F.subtype
  let W := v.ker
  let u : W →ₗ[K] V d := F.subtype.comp W.subtype
  obtain ⟨c,ci⟩ := u.exists_leftInverse_of_injective (LinearMap.ker_eq_bot (f:=u) |>.mpr
    (F.subtype_injective.comp W.subtype_injective))
  have lu (w : W) : l (u w)=0 := w.property
  have cu (w : W) : c (u w)=w := LinearMap.congr_fun ci w
  have lb (b : B) : l b.val=b := LinearMap.congr_fun li b
  have au (w : W) : a (u w)=u w := sub_eq_zero.mp (show a (u w)-u w=0 from w.val.property)
  have space : d-2*r ≤ Module.finrank K W := by
    have h₁ := Δ.finrank_range_add_finrank_ker
    have h₂ := v.finrank_range_add_finrank_ker
    have h₃ := Submodule.finrank_le v.range
    rw [Module.finrank_fin_fun] at h₁
    change r+Module.finrank K F=d at h₁
    change Module.finrank K v.range+Module.finrank K W=Module.finrank K F at h₂
    change Module.finrank K v.range ≤ r at h₃
    omega
  let M := B →ₗ[K] W →ₗ[K] V s
  let noise (t : M) := LinearMap.BilinMap.toQuadraticMap (t.compl₁₂ l c)
  let enc (p : mixedFix a (1 : L s) × M) : Q d s := p.1.val+noise p.2
  have vanish (q : mixedFix a (1 : L s)) (b : B) (w : W) :
      QuadraticMap.polar q.val b.val (u w)=0 := by
    obtain ⟨x,hx⟩ := b.property
    have iv (y : V d) : q.val (a y)=q.val y := (q.property y).symm
    have equal : QuadraticMap.polar q.val (a x) (u w)=QuadraticMap.polar q.val x (u w) := by
      change q.val (a x+u w)-q.val (a x)-q.val (u w)=_
      rw [←au w,←map_add,iv,iv,au];rfl
    rw [←hx]
    change ((QuadraticMap.polarBilin q.val) (a x-x)) (u w)=0
    rw [map_sub]
    exact sub_eq_zero.mpr equal
  have recover (q : mixedFix a (1 : L s)) (t : M) (b : B) (w : W) :
      QuadraticMap.polar (enc (q,t)) b.val (u w)=t b w := by
    have add (q z : Q d s) (x y : V d) : QuadraticMap.polar (q+z) x y=
        QuadraticMap.polar q x y+QuadraticMap.polar z x y := by
      simp only [QuadraticMap.polar,QuadraticMap.add_apply];abel
    dsimp only [enc]
    rw [add,vanish,zero_add]
    dsimp only [noise]
    rw [LinearMap.BilinMap.polar_toQuadraticMap]
    change t (l b.val) (c (u w))+t (l (u w)) (c b.val)=_
    rw [lb,cu,lu,map_zero,LinearMap.zero_apply,add_zero]
  have inj : Function.Injective enc := by
    rintro ⟨q,t⟩ ⟨p,z⟩ he
    have eq : t=z := LinearMap.ext (fun b=>LinearMap.ext (fun w=>
      (recover q t b w).symm.trans (he ▸ recover p z b w)))
    subst z
    exact Prod.ext (Subtype.ext (add_right_cancel (show q.val+noise t=p.val+noise t from he))) rfl
  have size : Nat.card M=2^(s*r*Module.finrank K W) := by
    rw [Module.natCard_eq_pow_finrank (K:=K),Nat.card_zmod,Module.finrank_linearMap,Module.finrank_linearMap,
      Module.finrank_fin_fun]
    congr 1;dsimp only [r];ring
  have h := Nat.card_le_card_of_injective enc inj
  rw [Nat.card_prod,size] at h
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left (s*r) space))).trans h
end OrbitUp
end

/- UniformPolarLoss -/
section
namespace OrbitUp
theorem uniform_polar_loss {d s z : ℕ} (hd : 64 ≤ d) (a : L d)
    (hz : 64*z ≤ s*d*rankChange a) :
    Nat.card (mixedFix a (1 : L s))*2^z ≤ Nat.card (Q d s) := by
  let r := rankChange a
  change 64*z ≤ s*d*r at hz
  by_cases h : 4*r ≤ d
  · have h₁ : d ≤ 64*(d-2*r) := by omega
    have h₂ := Nat.mul_le_mul_left (s*r) h₁
    have he : z ≤ s*r*(d-2*r) := by nlinarith only [h₂,hz]
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) he)).trans (input_rank_polar_saving a)
  · obtain ⟨k,hk,hm⟩ := exists_moves_rank a
    change r ≤ 2*k+2 at hk
    have bound : 2*r ≤ 5*k := by omega
    have sq := Nat.mul_le_mul bound bound
    have dsmall : d ≤ 4*r := by omega
    have rd := Nat.mul_le_mul_right r dsmall
    have hk1 : 1 ≤ k := by omega
    have eq := congrArg (k*·) (show k-1+1=k by omega)
    have div : k*(k-1) ≤ 2*(k*(k-1)/2)+1 := by omega
    have cost : d*r ≤ 64*(k+k*(k-1)/2) := by nlinarith only [sq,rd,eq,div,hk1]
    have c := Nat.mul_le_mul_left s cost
    have he : z ≤ s*(k+k*(k-1)/2) := by nlinarith only [hz,c]
    rw [card_forms_exact]
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) he)).trans (moved_fixed_card 1 hm)
end OrbitUp
end

/- SmallInputMoment -/
section
namespace OrbitUp.Moment
open Erdos1160.Paper85 Finset
open scoped Classical
noncomputable def inputStabilizer {d s : ℕ} (q : Q d s) : Subgroup (L d) :=
  (MulAction.stabilizer (Change d s) q).comap (MonoidHom.inl (L d) (L s))
theorem mem_inputStabilizer {d s : ℕ} (q : Q d s) (a : L d) :
    a∈inputStabilizer q ↔ ∀x,q x=q (a x) := by
  change ((a,1) : Change d s) • q=q ↔ _
  constructor
  · intro h x
    have eq := congrArg (fun z : Q d s=>z (a x)) h
    change q (a.symm (a x))=q (a x) at eq
    rwa [a.symm_apply_apply] at eq
  · intro h;apply QuadraticMap.ext;intro x
    exact (h (a.symm x)).trans (congrArg q (a.apply_symm_apply x))
theorem input_stabilizer_moment {d s h : ℕ} (hd : 64 ≤ d) (hh : 0 < h) (hs : 192*h ≤ s)
    [Fintype (Q d s)] :
    (∑q : Q d s,Nat.card (inputStabilizer q)^h) ≤ 2*Fintype.card (Q d s) := by
  classical
  letI := Fintype.ofFinite (L d)
  let fix (a : L d) := univ.filter (fun q : Q d s=>∀x,q x=q (a x))
  let cost (t : Fin h→L d) := (commonFix fix t).card
  let R (t : Fin h→L d) := univ.sup (fun i=>rankChange (t i))
  let S (r : ℕ) := univ.filter (fun t : Fin h→L d => R t=r)
  let Z := Fintype.card (Q d s)
  have card_fix (a : L d) : (fix a).card=Nat.card (mixedFix a (1:L s)) := by
    let e : fix a ≃ mixedFix a (1:L s) := Equiv.subtypeEquivRight (fun q=>by
      change q∈univ.filter _ ↔ _
      simp only [mem_filter,mem_univ,true_and];rfl)
    simpa using Nat.card_congr e
  have bound (t : Fin h→L d) : R t ≤ d := by
    apply Finset.sup_le;intro i _
    have h' := (LinearMap.range ((t i).toLinearMap-LinearMap.id)).finrank_le
    simpa only [Module.finrank_fin_fun] using h'
  have ball (r : ℕ) : (S r).card ≤ 2^(2*d*r*h) := by
    let T := univ.filter (fun a : L d=>rankChange a ≤ r)
    have ht : T.card ≤ 2^(2*d*r) := by
      let e : T ≃ {a : L d // rankChange a ≤ r} := Equiv.subtypeEquivRight (fun _=>by simp [T])
      rw [←Nat.card_eq_finsetCard,Nat.card_congr e]
      exact count_small_rank_changes d r
    have sub : S r⊆Fintype.piFinset (fun _ : Fin h=>T) := by
      intro t ht
      rw [Fintype.mem_piFinset]
      intro i
      refine mem_filter.mpr ⟨mem_univ _,?_⟩
      have e : R t=r := (mem_filter.mp ht).2
      exact (Finset.le_sup (f:=fun j=>rankChange (t j)) (mem_univ i)).trans_eq e
    have c := card_le_card sub
    rw [Fintype.card_piFinset_const] at c
    rw [Nat.pow_mul]
    exact c.trans (Nat.pow_le_pow_left ht _)
  have zero_cost (t : Fin h→L d) : cost t ≤ Z := card_le_univ _
  have pos_cost (r : ℕ) (hr : 0 < r) (t : Fin h→L d) (ht : t∈S r) :
      cost t*2^(2*d*r*h+d) ≤ Z := by
    have pos : Nonempty (Fin h) := Fin.pos_iff_nonempty.mp hh
    obtain ⟨i,_,ei⟩ := Finset.exists_mem_eq_sup univ Finset.univ_nonempty (fun i=>rankChange (t i))
    have eq : rankChange (t i)=r := ei.symm.trans ((mem_filter.mp ht).2)
    have loss : 64*(2*d*r*h+d) ≤ s*d*rankChange (t i) := by
      rw [eq]
      have a := Nat.mul_le_mul_right (d*r) hs
      have rd : d ≤ d*r := (Nat.le_mul_of_pos_right d hr)
      have rd' : d*r ≤ d*r*h := Nat.le_mul_of_pos_right _ hh
      nlinarith only [a,rd,rd']
    have sub : commonFix fix t⊆fix (t i) := by
      intro q hq
      simp only [commonFix, mem_filter, mem_univ, true_and] at hq
      exact hq i
    have small := (card_le_card sub).trans_eq (card_fix (t i))
    exact (Nat.mul_le_mul_right _ small).trans ((uniform_polar_loss hd _ loss).trans_eq Nat.card_eq_fintype_card)
  have pos_budget (r : ℕ) (hr : 0 < r) : (∑t∈S r,cost t)*2^d ≤ Z := by
    let B := 2^(2*d*r*h)
    have each (t) (ht : t∈S r) : cost t*2^d*B ≤ Z := by
      simpa only [B,Nat.mul_assoc,←Nat.pow_add,Nat.add_comm d] using pos_cost r hr t ht
    have sum := (S r).sum_le_card_nsmul _ _ each
    rw [←sum_mul,←sum_mul,nsmul_eq_mul,Nat.cast_id] at sum
    exact Nat.le_of_mul_le_mul_right (sum.trans ((Nat.mul_le_mul_right Z (ball r)).trans_eq (Nat.mul_comm ..))) (Nat.two_pow_pos _)
  have zero_budget : (∑t∈S 0,cost t) ≤ Z := by
    have sum := (S 0).sum_le_card_nsmul _ _ (fun t _=>zero_cost t)
    have se : (S 0).card ≤ 1 := by simpa using ball 0
    simpa only [nsmul_eq_mul,Nat.cast_id,one_mul] using sum.trans (Nat.mul_le_mul_right Z se)
  have remaining := (range d).sum_le_card_nsmul _ _ (fun i _=>pos_budget (i+1) (Nat.succ_pos _))
  rw [←sum_mul,card_range,nsmul_eq_mul,Nat.cast_id] at remaining
  have pay : (∑i∈range d,∑t∈S (i+1),cost t) ≤ Z := Nat.le_of_mul_le_mul_right
    (remaining.trans ((Nat.mul_le_mul_right Z (Nat.lt_two_pow_self.le)).trans_eq (Nat.mul_comm ..))) (Nat.two_pow_pos _)
  have split := Finset.sum_fiberwise_of_maps_to (s:=(univ : Finset (Fin h→L d))) (t:=range (d+1))
    (g:=R) (fun t _=>mem_range.mpr (Nat.lt_succ_of_le (bound t))) cost
  change (∑j∈range (d+1),∑t∈S j,cost t)=∑t,cost t at split
  rw [sum_range_succ'] at split
  have rows (q : Q d s) : (stabilizing fix q).card=Nat.card (inputStabilizer q) := by
    let e : stabilizing fix q ≃ inputStabilizer q := Equiv.subtypeEquivRight (fun a=>by simp [stabilizing,fix,mem_inputStabilizer])
    simpa using Nat.card_congr e
  simp_rw [←rows]
  rw [stabilizer_moment_expand]
  change (∑t,cost t) ≤ 2*Z
  omega
end OrbitUp.Moment
end

/- SmallJointMoment -/
section
namespace OrbitUp.Moment
theorem joint_stabilizer_card {d s : ℕ} (q : Q d s) :
    Nat.card (MulAction.stabilizer (Change d s) q) ≤ 2^(s*s)*Nat.card (inputStabilizer q) := by
  let S := MulAction.stabilizer (Change d s) q
  let p := (MonoidHom.snd (L d) (L s)).comp S.subtype
  let f (x : p.ker) : inputStabilizer q :=
    ⟨x.val.val.1,by
      have hb : x.val.val.2=1 := x.property
      change (x.val.val.1,1)∈S
      rw [←hb];exact x.val.property⟩
  have hi : Function.Injective f := by
    intro x y e
    apply Subtype.ext;apply Subtype.ext
    exact Prod.ext (congrArg (fun t : inputStabilizer q => t.val) e)
      ((show x.val.val.2=1 from x.property).trans (show y.val.val.2=1 from y.property).symm)
  have bound := Nat.mul_le_mul (p.range.card_le_card_group.trans (gl_upper s)) (Nat.card_le_card_of_injective f hi)
  rwa [←Subgroup.index_ker,p.ker.index_mul_card] at bound
theorem small_joint_moment {d s h : ℕ} (hd : 64 ≤ d) (hh : 0 < h) (hs : 192*h ≤ s)
    [Fintype (Q d s)] :
    (∑q : Q d s,Nat.card (MulAction.stabilizer (Change d s) q)^h) ≤
      2*Fintype.card (Q d s)*2^(s*s*h) := by
  have h₁ := Finset.sum_le_sum (s:=Finset.univ) (fun (q : Q d s) _=>Nat.pow_le_pow_left (joint_stabilizer_card q) h)
  simp_rw [Nat.mul_pow,←Nat.pow_mul] at h₁
  rw [←Finset.mul_sum] at h₁
  exact h₁.trans ((Nat.mul_le_mul_left _ (input_stabilizer_moment hd hh hs)).trans_eq (Nat.mul_comm ..))
end OrbitUp.Moment
end

/- SmallOutput83 -/
section
namespace OrbitUp.Moment
open Erdos1160.Paper85
private lemma pred_mul_balance (x : ℕ) : x*(x-1)+x=x*x := by
  cases x with
  | zero => rfl
  | succ n => simp only [Nat.add_one_sub_one];ring
private lemma exchange {M N L K s : ℕ} (h : M*2^L ≤ N*2^K) (hk : K+s*s ≤ L) :
    M*2^(s*s) ≤ N := by
  apply Nat.le_of_mul_le_mul_right (c:=2^K) _ (Nat.two_pow_pos _)
  rw [Nat.mul_assoc,←pow_add,Nat.add_comm (s*s)]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)).trans h
theorem weighted_small_output_orbits {d s l : ℕ} (hd : 64 ≤ d) (hs : 192*(l+1) ≤ s)
    (hsd : s ≤ d) (h81 : max (threshold (2*(l+1)) 1 (l+1)) (32*(2*(l+1))) ≤ d)
    (S : Finset (Classes d s)) :
    (∑o∈S,Nat.card (MulAction.stabilizer (Change d s) o.out)^l)*2^(s*s)≤
      2^(s*(d+d*(d-1)/2)) := by
  classical
  letI := Fintype.ofFinite (Q d s)
  letI := Fintype.ofFinite (Change d s)
  letI := Fintype.ofFinite (Classes d s)
  let M := ∑o∈S,Nat.card (MulAction.stabilizer (Change d s) o.out)^l
  let Z := Nat.card (Q d s)
  let L := d*(d-1)+s*(s-1)
  have lower : 2^L ≤ Fintype.card (Change d s) := by
    rw [←Nat.card_eq_fintype_card];change 2^(d*(d-1)+s*(s-1)) ≤ Nat.card (OrbitUp.L d × OrbitUp.L s)
    rw [Nat.pow_add,Nat.card_prod]
    exact Nat.mul_le_mul (gl_lower d) (gl_lower s)
  have upper := (Nat.mul_le_mul_left M lower).trans
    (weighted_admissible_orbits (Change d s) (Q d s) l S)
  have exactCard : Z=2^(s*(d+d*(d-1)/2)) := card_forms_exact _ _
  change M*2^(s*s)≤_
  rw [←exactCard]
  have pd := pred_mul_balance d
  have ps := pred_mul_balance s
  have dd := Nat.mul_le_mul_left d hd
  by_cases large : d ≤ 2*(l+1)*s
  · have hlarge := complete_form_moment_le_two (h:=l+1) (A:=2*(l+1)) (B:=1)
        (by omega) large (by simpa using hsd) h81
    have h := upper.trans hlarge
    have upper' : M*2^L ≤ Z*2^1 := by
      simpa only [Z,Nat.card_eq_fintype_card,pow_one,Nat.mul_comm 2] using h
    exact exchange upper' (by dsimp [L];nlinarith only [pd,ps,dd,hsd,hd])
  · have hsmall := upper.trans (small_joint_moment hd (Nat.succ_pos l) hs)
    have upper' : M*2^L ≤ Z*2^(1+s*s*(l+1)) := by
      apply hsmall.trans_eq
      rw [pow_add 2 1,pow_one]
      dsimp only [Z];rw [Nat.card_eq_fintype_card];ac_rfl
    have area := Nat.mul_le_mul_right s (Nat.le_of_lt (lt_of_not_ge large))
    have ss := Nat.mul_le_mul_left d hsd
    apply exchange upper'
    dsimp [L]
    nlinarith only [area,ss,pd,ps,dd,hd,hsd]
end OrbitUp.Moment
end

/- JacobiNaturality -/
section
namespace OrbitUp
open scoped Matrix
noncomputable def transformJacobiMatrix {d t : ℕ} (M : Matrix (Fin d) (Fin t) K)
    (a : L d) (b : L t) :=
  (LinearMap.toMatrix' a.symm.toLinearMap)ᵀ * (M * LinearMap.toMatrix' b.symm.toLinearMap)
theorem transformJacobiPair {d t : ℕ} (M : Matrix (Fin d) (Fin t) K) (a : L d) (b : L t)
    (x : V d) (w : V t) :
    jacobiPair (transformJacobiMatrix M a b) x w = jacobiPair M (a.symm x) (b.symm w) := by
  simp only [jacobiPair,transformJacobiMatrix,←Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,LinearMap.toMatrix'_mulVec,LinearMap.toMatrix'_mulVec]
  rfl
private theorem changed_polar {d t : ℕ} (a : L d) (b : L t) (F : Q d t) (x y : V d) :
    QuadraticMap.polar ((a,b) • F) x y = b (QuadraticMap.polar F (a.symm x) (a.symm y)) := by
  change b (F (a.symm (x+y))) - b (F (a.symm x)) - b (F (a.symm y)) = _
  simp only [QuadraticMap.polar,map_add,map_sub]
theorem JacobiCompatible.change {d t : ℕ} {M : Matrix (Fin d) (Fin t) K} {F : Q d t}
    (h : JacobiCompatible M F) (a : L d) (b : L t) :
    JacobiCompatible (transformJacobiMatrix M a b) ((a,b) • F) := by
  intro x y z
  simp only [changed_polar,transformJacobiPair,b.symm_apply_apply]
  exact h _ _ _
end OrbitUp
end

/- RootPairing -/
section
namespace OrbitUp
open scoped Matrix
open Erdos1160.DeepJacobi (C₂)
variable {d t : ℕ}
private theorem bitExt {k : ℕ} (f g : V k → K) (h0 : f 0=g 0)
    (hadd : ∀u v,f (u+v)=f u+f v) (gadd : ∀u v,g (u+v)=g u+g v)
    (hb : ∀i,f (basis i)=g (basis i)) (x : V k) : f x=g x := by
  induction x using Pi.single_induction with
  | zero => exact h0
  | add u v hu hv => rw [hadd,gadd,hu,hv]
  | single i b =>
    rcases (show ∀ b : K,b=0 ∨ b=1 by decide) b with rfl|rfl
    · simpa only [Pi.single_zero] using h0
    · exact hb i
def pairingMatrix (b : Multiplicative (V t) →* (Multiplicative (V d) →* C₂)) :
    Matrix (Fin d) (Fin t) K := fun i j => (b (.ofAdd (basis j)) (.ofAdd (basis i))).toAdd
lemma pairingMatrix_apply (b : Multiplicative (V t) →* (Multiplicative (V d) →* C₂)) (x : V d) (w : V t) :
    jacobiPair (pairingMatrix b) x w = (b (.ofAdd w) (.ofAdd x)).toAdd := by
  let M := pairingMatrix b
  apply bitExt (fun x => jacobiPair M x w) (fun x => (b (.ofAdd w) (.ofAdd x)).toAdd) _ _ _ _ x
  · simp [jacobiPair]
  · intro u v
    exact add_dotProduct u v _
  · intro u v
    exact congrArg Multiplicative.toAdd ((b (.ofAdd w)).map_mul (.ofAdd u) (.ofAdd v))
  · intro i
    apply bitExt (fun w => jacobiPair M (basis i) w) (fun w => (b (.ofAdd w) (.ofAdd (basis i))).toAdd) _ _ _ _ w
    · simp [jacobiPair]
    · intro u v
      simp only [jacobiPair_basis,Matrix.mulVec_add,Pi.add_apply]
    · intro u v
      exact congrArg (fun h : Multiplicative (V d) →* C₂ => (h (.ofAdd (basis i))).toAdd)
        (b.map_mul (.ofAdd u) (.ofAdd v))
    · intro j
      rw [jacobiPair_basis]
      change (∑ k,M i k * (Pi.single j 1 : V t) k)=M i j
      simp [Pi.single_apply]
def polarSpan (F : Q d t) : Submodule K (V t) :=
  Submodule.span K (Set.range (fun p : V d × V d => QuadraticMap.polar F p.1 p.2))
end OrbitUp
end

/- RootDetection -/
section
namespace OrbitUp
open Erdos1160Growth Erdos1160Growth.LowerTriangularUpper
open Erdos1160.DeepJacobi
open scoped commutatorElement
variable {d t : ℕ} (B : V d →+ V d →+ V t)
def liftW (w : V t) : BilinearExtension B := ⟨0,w⟩
def liftV (x : V d) : BilinearExtension B := ⟨x,0⟩
lemma liftW_add (w v : V t) : liftW B (w+v) = liftW B w * liftW B v := by
  apply BilinearExtension.ext <;> simp [liftW]
def fiberSub (H : Subgroup (BilinearExtension B)) : Submodule K (V t) where
  carrier := {w | liftW B w ∈ H}
  zero_mem' := H.one_mem
  add_mem' hu hv := by rw [Set.mem_ofPred_eq,liftW_add];exact H.mul_mem hu hv
  smul_mem' k w hw := by
    rcases (show ∀ z : K,z=0 ∨ z=1 by decide) k with rfl|rfl
    · rw [zero_smul];exact H.one_mem
    · rwa [one_smul]
theorem bracket_polar (x y : V d) :
    ⁅liftV B x,liftV B y⁆ = liftW B (QuadraticMap.polar (diagonalQ B) x y) := by
  rw [BilinearExtension.commutator_formula]
  apply BilinearExtension.ext
  · rfl
  · change B x y - B y x = B (x+y) (x+y) - B x x - B y y
    simp only [map_add,AddMonoidHom.add_apply]
    have h (w : V t) : -w=w := by funext i; exact (show ∀b : K,-b=b by decide) (w i)
    rw [sub_eq_add_neg,h]
    abel
lemma base_surj : Function.Surjective (BilinearExtension.projection B) :=
  fun x => ⟨liftV B x.toAdd,rfl⟩
end OrbitUp
end

/- JacobiRankDimension -/
section
namespace OrbitUp
open Erdos1160Growth Erdos1160Growth.LowerTriangularUpper Erdos1160.DeepJacobi
open scoped Matrix
def jacobiMatrixSpace {d t : ℕ} (F : Q d t) : Submodule K (Matrix (Fin d) (Fin t) K) where
  carrier := {M | JacobiCompatible M F}
  zero_mem' := by intro x y z; simp [jacobiPair]
  add_mem' := by
    intro M N hM hN x y z
    have addP (x : V d) (w : V t) : jacobiPair (M+N) x w=jacobiPair M x w+jacobiPair N x w := by
      simp only [jacobiPair,Matrix.add_mulVec,dotProduct_add]
    rw [addP,addP,addP,hM x y z,hN x y z]
    abel
  smul_mem' := by
    intro a M hM
    rcases (show ∀b:K,b=0 ∨ b=1 by decide) a with rfl|rfl
    · rw [zero_smul]; intro x y z; simp [jacobiPair]
    · rwa [one_smul]
end OrbitUp
end

/- PeakRank -/
section
namespace OrbitUp
open scoped Matrix
variable {d s : ℕ}
noncomputable def peakRank (F : Q d s) : ℕ := by
  classical
  exact Finset.univ.sup (fun M : jacobiMatrixSpace F => M.val.rank)
theorem JacobiCompatible.rank_le_peak {M : Matrix (Fin d) (Fin s) K} {F : Q d s} (h : JacobiCompatible M F) :
    M.rank ≤ peakRank F := by
  classical
  let x : jacobiMatrixSpace F := ⟨M,h⟩
  let f (N : jacobiMatrixSpace F) := N.val.rank
  have bound : f x ≤ Finset.univ.sup f := Finset.le_sup (s:=Finset.univ) (b:=x) (f:=f) (Finset.mem_univ x)
  exact bound
theorem peakRank_mem (F : Q d s) :
    ∃M : Matrix (Fin d) (Fin s) K,JacobiCompatible M F ∧ M.rank=peakRank F := by
  classical
  obtain ⟨M,_,h⟩ := Finset.exists_mem_eq_sup Finset.univ (Finset.univ_nonempty (α:=jacobiMatrixSpace F))
    (fun M : jacobiMatrixSpace F=>M.val.rank)
  exact ⟨M.val,M.property,h.symm⟩
lemma transformJacobiMatrix_rank (M : Matrix (Fin d) (Fin s) K) (a : L d) (b : L s) :
    (transformJacobiMatrix M a b).rank=M.rank := by
  have unit {k : ℕ} (e : L k) : IsUnit (LinearMap.toMatrix' e.toLinearMap).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr e.bijective))
  have tr := unit a.symm
  rw [←Matrix.det_transpose] at tr
  rw [transformJacobiMatrix,Matrix.rank_mul_eq_right_of_isUnit_det _ _ tr,Matrix.rank_mul_eq_left_of_isUnit_det _ _ (unit b.symm)]
theorem peakRank_smul (g : Change d s) (F : Q d s) : peakRank (g•F)=peakRank F := by
  have step (v : Change d s) (G : Q d s) : peakRank G ≤ peakRank (v•G) := by
    obtain ⟨M,hM,hr⟩ := peakRank_mem G
    rw [←hr,←transformJacobiMatrix_rank M v.1 v.2]
    exact (hM.change v.1 v.2).rank_le_peak
  exact le_antisymm (by simpa using step g⁻¹ (g•F)) (step g F)
end OrbitUp
end

/- Actual84 -/
section
namespace Erdos1160.DescendantTree
open OrbitUp MulAction Erdos1160.Paper85
open scoped Classical
private theorem real_pow_cut {N M L : ℕ} (h : N*2^L ≤ 2^M) :
    (N:ℝ)≤(2:ℝ)^((M:ℝ)-L) := by
  rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_natCast,Real.rpow_natCast,le_div_iff₀ (by positivity)]
  exact_mod_cast h
abbrev exponentH (k : ℕ) := (k+1)*1000
abbrev threshold84 (k : ℕ) := max 10000 (max (Moment.threshold (2*exponentH k) 1 (exponentH k)) (32*(2*exponentH k)))
private theorem labelled_high_moment {d s k : ℕ} [Fintype (Q d s)] [Fintype (Change d s)]
    [Fintype (Classes d s)] (hd : threshold84 k ≤ d) (hs : 192*exponentH k ≤ s) (hsd : s ≤ d) :
    ∑q : Q d s,Nat.card (stabilizer (Change d s) q)^(exponentH k) ≤ 2^(s*slotsN d+d^2) := by
  let h := exponentH k
  have he : h-1+1=h := Nat.sub_add_cancel (by dsimp [h,exponentH];omega)
  have h81 : max (Moment.threshold (2*(h-1+1)) 1 (h-1+1)) (32*(2*(h-1+1))) ≤ d := by
    rw [he];exact (le_max_right ..).trans hd
  have h' := Moment.weighted_small_output_orbits (l:=h-1) ((show 64 ≤ 10000 by decide).trans ((le_max_left ..).trans hd))
    (by rwa [he]) hsd h81 (Finset.univ : Finset (Classes d s))
  have rel := weighted_orbit_sum (Change d s) (Q d s) (h-1)
  rw [he] at rel
  have cap : Fintype.card (Change d s) ≤ 2^(d^2+s^2) := by
    rw [←Nat.card_eq_fintype_card,pow_add,sq,sq,Nat.card_prod]
    exact Nat.mul_le_mul (gl_upper d) (gl_upper s)
  apply Nat.le_of_mul_le_mul_right (c:=2^(s*s)) _ (Nat.two_pow_pos _)
  change (∑q : Q d s,_) * _≤_
  rw [←rel,Nat.mul_right_comm]
  apply (Nat.mul_le_mul h' cap).trans_eq
  rw [←pow_add,←pow_add,sq s]
  congr 1 <;> unfold slotsN <;> omega
private theorem peak_respects {d s : ℕ} (q : Q d s) :
    peakRank ((Quotient.mk'' q : Classes d s).out)=peakRank q := by
  have h : (Quotient.mk'' ((Quotient.mk'' q : Classes d s).out) : Classes d s)=Quotient.mk'' q :=
    Quotient.out_eq' _
  obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  rw [←hg,peakRank_smul]
noncomputable abbrev stabilizerSize {d s : ℕ} (q : Q d s) := Nat.card (stabilizer (Change d s) q)
private theorem rank_slice {d s t k r : ℕ} [Fintype (Q d s)] [Fintype (Change d s)] [Fintype (Classes d s)]
    (S : Finset (Classes d s)) (ranked : ∀o∈S, peakRank o.out=r) (hr : 1 ≤ r) (hrs : r ≤ s)
    (hd : threshold84 k ≤ d) (hs : 192*exponentH k ≤ s) (hz : (s:ℝ)+t ≤ 51*(d:ℝ)/100) :
    (∑o∈S,(stabilizerSize o.out:ℝ)^k) *
        2^((t:ℝ)*(slotsN d-s+(s+1)*r)) ≤
      2^(((s:ℝ)+t)*slotsN d-d^2-((s:ℝ)+t)^2-21*(d:ℝ)^2/400) := by
  classical
  let T := Finset.univ.filter (fun q : Q d s=>(Quotient.mk'' q : Classes d s)∈S)
  let C := r*((d-r)*(d-r-1)/2)
  let A : ℝ := (s:ℝ)*slotsN d+r*(d+s)-(C:ℝ)
  let U : ℝ := (s:ℝ)*slotsN d+(d:ℝ)^2
  let W := ∑o∈S,(stabilizerSize o.out:ℝ)^k
  let Z : ℝ := 2^((t:ℝ)*(slotsN d-s+(s+1)*r))
  let L : ℝ := (d:ℝ)^2+(s:ℝ)^2-d-s
  let F : ℝ := ((s:ℝ)+t)*slotsN d-d^2-((s:ℝ)+t)^2-21*(d:ℝ)^2/400
  have cardT : (T.card:ℝ) ≤ 2^A := by
    have w (q : T) : ∃M : ProbeMat d s,M.rank=r ∧ JacobiCompatible M q.val := by
      obtain ⟨M,h,hM⟩ := peakRank_mem q.val
      exact ⟨M,hM.trans ((peak_respects q.val).symm.trans (ranked _ (Finset.mem_filter.mp q.property).2)),h⟩
    have le := Nat.card_le_card_of_injective
      (fun q : T=>(⟨q.val,w q⟩ : {F : Q d s // ∃M : ProbeMat d s,M.rank=r ∧ JacobiCompatible M F}))
      (fun _ _ he=>Subtype.ext (congrArg (fun z : {F : Q d s // ∃M : ProbeMat d s,M.rank=r ∧ JacobiCompatible M F}=>z.val) he))
    rw [Nat.card_eq_finsetCard] at le
    have cut := real_pow_cut ((Nat.mul_le_mul_right (2^C) le).trans (rank_labeled_count d s r))
    simpa only [A,C,Nat.cast_add,Nat.cast_mul] using cut
  have hsd : s ≤ d := by exact_mod_cast (show (s:ℝ) ≤ d by linarith [show (0:ℝ) ≤ t by positivity,show (0:ℝ) ≤ d by positivity])
  have hm : ∑q∈T,(stabilizerSize q:ℝ)^((k+1)*1000) ≤ 2^U := by
    have h := ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun x _ _=>Nat.zero_le _)).trans
      (labelled_high_moment (k:=k) hd hs hsd))
    dsimp only [U]
    rw [←Nat.cast_mul,←Nat.cast_pow,←Nat.cast_add,Real.rpow_natCast]
    exact_mod_cast h
  have price := thousandth_moment T stabilizerSize (k+1) cardT hm
  have balance : W*(Fintype.card (Change d s):ℝ)=∑q∈T,(stabilizerSize q:ℝ)^(k+1) := by
    have h := orbit_weighted_filter (Change d s) (Q d s) S k
    rw [←Finset.sum_filter] at h
    dsimp only [W,T,stabilizerSize]
    exact_mod_cast h
  have hG : (2:ℝ)^L≤(Fintype.card (Change d s):ℝ) := by
    have h := Nat.mul_le_mul (gl_lower d) (gl_lower s)
    rw [←Nat.pow_add,←Nat.card_prod] at h
    change _ ≤ Nat.card (Change d s) at h
    rw [Nat.card_eq_fintype_card] at h
    have pred (n:ℕ) : ((n*(n-1):ℕ):ℝ)=(n:ℝ)^2-n := by cases n <;> simp <;> ring
    have eq : L=((d*(d-1)+s*(s-1):ℕ):ℝ) := by dsimp [L];rw [Nat.cast_add,pred,pred];ring
    rw [eq,Real.rpow_natCast]
    exact_mod_cast h
  have hd0 : 10000 ≤ d := (le_max_left ..).trans hd
  have cap := labelled_margin d s t r (slotsN d) hd0 hr hrs hz
  change A+(U-A)/1000+_ - L ≤ F at cap
  have e : W*2^L ≤ 2^(A+(U-A)/1000) :=
    ((mul_le_mul_of_nonneg_left hG (Finset.sum_nonneg fun _ _=>by positivity)).trans_eq balance).trans price
  change W*Z≤(2:ℝ)^F
  apply le_of_mul_le_mul_right (a:=(2:ℝ)^L) _ (by positivity)
  rw [mul_right_comm]
  apply (mul_le_mul_of_nonneg_right e (show 0 ≤ Z by dsimp [Z];positivity)).trans
  dsimp only [Z]
  rw [←Real.rpow_add (by norm_num : (0:ℝ) < 2),←Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith only [cap])
theorem su_xia_8_4_orbits {d s t k : ℕ} (S : Finset (Classes d s))
    (positive : ∀o∈S,0 < peakRank o.out)
    (hd : threshold84 k ≤ d) (hs : 192*exponentH k ≤ s) (hz : (s:ℝ)+t ≤ 51*(d:ℝ)/100) :
    ∑o∈S,(stabilizerSize o.out:ℝ)^k*2^((t:ℝ)*(slotsN d-s+(s+1)*peakRank o.out)) ≤
      2^(((s:ℝ)+t)*slotsN d-d^2-((s:ℝ)+t)^2-(d:ℝ)^2/25) := by
  classical
  letI := Fintype.ofFinite (Q d s)
  letI := Fintype.ofFinite (Change d s)
  letI := Fintype.ofFinite (Classes d s)
  let ranks := Finset.Icc 1 s
  let rank (o : Classes d s) := peakRank o.out
  have maps (o) (ho:o∈S) : rank o∈ranks := by
    obtain ⟨M,h,eq⟩ := peakRank_mem o.out
    exact Finset.mem_Icc.mpr ⟨positive o ho,eq.ge.trans M.rank_le_width⟩
  let weight (o : Classes d s) := (stabilizerSize o.out:ℝ)^k*2^((t:ℝ)*(slotsN d-s+(s+1)*rank o))
  let F : ℝ := ((s:ℝ)+t)*slotsN d-d^2-((s:ℝ)+t)^2
  have each (r) (hr:r∈ranks) :
      ∑o∈S.filter (fun o=>rank o=r),weight o ≤ 2^(F-21*(d:ℝ)^2/400) := by
    let T := S.filter (fun o=>rank o=r)
    let Z : ℝ := 2^((t:ℝ)*(slotsN d-s+(s+1)*r))
    have eq (o) (ho:o∈T) : weight o=(stabilizerSize o.out:ℝ)^k*Z := by
      dsimp only [weight,Z];rw [(Finset.mem_filter.mp ho).2]
    have hslice := rank_slice T (fun o ho=>(Finset.mem_filter.mp ho).2) (Finset.mem_Icc.mp hr).1
      (Finset.mem_Icc.mp hr).2 hd hs hz
    exact ((Finset.sum_congr rfl eq).trans (Finset.sum_mul ..).symm).le.trans hslice
  have sum := Finset.sum_le_sum each
  rw [Finset.sum_fiberwise_of_maps_to maps,Finset.sum_const,nsmul_eq_mul] at sum
  have dr : (10000:ℝ) ≤ d := by exact_mod_cast (show 10000 ≤ d from (le_max_left ..).trans hd)
  have cnt : (ranks.card:ℝ) ≤(2:ℝ)^((d:ℝ)^2/80) := by
    have hc : ranks.card=s := by simp [ranks]
    rw [hc]
    have ls : (s:ℝ) ≤ d := by linarith [show (0:ℝ) ≤ t by positivity]
    have h : (d:ℝ) ≤ 2^(d:ℝ) := by rw [Real.rpow_natCast];exact_mod_cast (Nat.lt_two_pow_self (n:=d)).le
    exact (ls.trans h).trans (Real.rpow_le_rpow_of_exponent_le one_le_two (by
      nlinarith only [mul_le_mul_of_nonneg_right dr (show (0:ℝ) ≤ d by positivity)]))
  apply (sum.trans (mul_le_mul_of_nonneg_right cnt (by positivity))).trans_eq
  rw [←Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  dsimp only [F];ring
end Erdos1160.DescendantTree
end

/- NonrootOrbitFibers -/
section
namespace Erdos1160.Paper85
open OuterExtensions DescendantTree DescendantTree.Actual CategoryTheory
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160.CentralLifts.Survival (binaryThird_map_eq)
open Erdos1160Growth Erdos1160Growth.LowerTriangularUpper
open OrbitUp (Q Classes peakRank)
open scoped Classical
private abbrev Bilin (d s : ℕ) := OrbitUp.V d →+ OrbitUp.V d →+ OrbitUp.V s
structure RootModel {m d s : ℕ} (x : ProfileClasses m d s) where
  root : Root d s
  form : Bilin d s
  model : BilinearExtension form ≃* root.group
  toRoot : orderRep x.val →* root.group
  onto : Function.Surjective toRoot
  deep : toRoot.ker ≤ binaryThird (orderRep x.val)
  weight : ∀ k, Nat.card (MulAut (orderRep x.val))^k ≤
    2^(k*d*(m-d)) * stabilizerSize (diagonalQ form)^k
theorem exists_root_model {m d s : ℕ} (x : ProfileClasses m d s) : Nonempty (RootModel x) := by
  classical
  let P := orderRep x.val
  let K := binaryThird P
  let Y := P ⧸ K
  let p := QuotientGroup.mk' K
  have hp := QuotientGroup.mk'_surjective K
  have mP : Nat.card P=2^m := rep_size x.val
  obtain ⟨_,_,_,_,aut,B,rfl,⟨e⟩⟩ := root_form_automorphism_model mP x.property.1 x.property.2
  have cardY : Nat.card Y=2^(d+s) := by
    rw [←Nat.card_congr e.toEquiv,BilinearExtension.card,pow_add,Nat.card_fun,Nat.card_fin,
      Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  have width : Nat.card (squareCore Y)=2^s := by
    rw [←frattini_eq_squareCore cardY]
    exact x.property.2
  have cardV : Nat.card (Y ⧸ squareCore Y)=2^d := by
    have h := (squareCore Y).card_eq_card_quotient_mul_card_subgroup
    rw [cardY,width,pow_add] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h.symm
  have elem (z : Y ⧸ squareCore Y) : z*z=1 := by
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (squareCore Y) z
    rw [←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨y,rfl⟩)
  obtain ⟨j⟩ := exist_elementary_coords elem cardV
  let f := j.toMonoidHom.comp (QuotientGroup.mk' (squareCore Y))
  have ker : f.ker=squareCore Y := by
    rw [←QuotientGroup.ker_mk' (squareCore Y)]
    ext y
    exact j.map_eq_one_iff
  have bot : binaryThird Y=⊥ :=
    (binaryThird_map_eq p hp).symm.trans ((Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' K).ge)
  let R : Root d s := ⟨FiniteGrp.of Y,cardY,f,j.surjective.comp (QuotientGroup.mk'_surjective (squareCore Y)),ker,bot,width⟩
  exact ⟨⟨R,B,e,p,hp,(QuotientGroup.ker_mk' K).le,aut⟩⟩
noncomputable def rootModel {m d s : ℕ} (x : ProfileClasses m d s) : RootModel x :=
  (exists_root_model x).some
noncomputable def rootOrbit {m d s : ℕ} (x : ProfileClasses m d s) : Classes d s :=
  Quotient.mk'' (diagonalQ (rootModel x).form)
private theorem same_orbit {d s : ℕ} (B C : Bilin d s)
    (h : (Quotient.mk'' (diagonalQ B) : Classes d s)=Quotient.mk'' (diagonalQ C)) :
    Nonempty (BilinearExtension B ≃* BilinearExtension C) := by
  obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  have eq (v : OrbitUp.V d) : pushB g C v v=B v v := congrArg (fun q : Q d s=>q v) hg
  exact ⟨((pushIso g C).trans (diagonalIso eq)).symm⟩
theorem root_orbit_invariants {m d s : ℕ} (x : ProfileClasses m d s) :
    stabilizerSize (rootOrbit x).out=stabilizerSize (diagonalQ (rootModel x).form) ∧
    peakRank (rootOrbit x).out=peakRank (diagonalQ (rootModel x).form) := by
  have h : (Quotient.mk'' (rootOrbit x).out : Classes d s)=Quotient.mk'' (diagonalQ (rootModel x).form) :=
    Quotient.out_eq' (rootOrbit x)
  obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  exact ⟨(Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv).symm,
    by rw [←hg,OrbitUp.peakRank_smul]⟩
theorem orbit_weight {m d s : ℕ} (x : ProfileClasses m d s) (k : ℕ) :
    Nat.card (MulAut (orderRep x.val))^k ≤ 2^(k*d*(m-d)) * stabilizerSize (rootOrbit x).out^k := by
  rw [(root_orbit_invariants x).1]
  exact (rootModel x).weight k
theorem fiber_in_tree {m d s t : ℕ} (hm : d+s+t=m) (x y : ProfileClasses m d s)
    (h : rootOrbit y=rootOrbit x) :
    y.val.val ∈ descendants (rootModel x).root.group (d+s) t := by
  obtain ⟨j⟩ := same_orbit _ _ h
  let a := (rootModel y).model.symm.trans (j.trans (rootModel x).model)
  let f := a.toMonoidHom.comp (rootModel y).toRoot
  have deep : f.ker ≤ binaryThird (orderRep y.val) := by
    intro z hz
    exact (rootModel y).deep (a.map_eq_one_iff.mp hz)
  exact ⟨orderRep y.val,hm ▸ rep_size y.val,⟨f,a.surjective.comp (rootModel y).onto,deep⟩,y.val.property.choose_spec.2⟩
theorem orbit_fiber_count {m d s t : ℕ} (hm : d+s+t=m) (x : ProfileClasses m d s) :
    (Finset.univ.filter (fun y : ProfileClasses m d s=>rootOrbit y=rootOrbit x)).card ≤
       (descendants (rootModel x).root.group (d+s) t).ncard := by
  classical
  let T := Finset.univ.filter (fun y : ProfileClasses m d s=>rootOrbit y=rootOrbit x)
  let U := descendants (rootModel x).root.group (d+s) t
  letI := (descendants_finite _ (rootModel x).root.size t).fintype
  let f : ↑T → U := fun y=>⟨y.val.val.val,fiber_in_tree hm x y.val (Finset.mem_filter.mp y.property).2⟩
  have hi : Function.Injective f := by
    intro a b eq
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : U=>z.val) eq
  have := Nat.card_le_card_of_injective f hi
  rwa [Nat.card_coe_set_eq,Nat.card_eq_fintype_card,Fintype.card_coe] at this
end Erdos1160.Paper85
end

/- LinearizedRank -/
section
namespace OrbitUp.BoundedMatrices
open Polynomial
open scoped Polynomial
variable {E : Type} [Field E] [Algebra K E] [CharP E 2]
noncomputable def linearized {n : ℕ} (c : Fin n→E) : E[X] :=
  ∑i : Fin n,monomial (2^i.val) (c i)
lemma linearized_coeff {n : ℕ} (c : Fin n→E) (i : Fin n) : (linearized c).coeff (2^i.val)=c i := by
  classical
  simp only [linearized,finsetSum_coeff,coeff_monomial]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hj
    exact if_neg (fun eq=>hj (Fin.ext ((Nat.pow_right_injective (by decide : 1 < 2)) eq)))
lemma linearized_degree {n : ℕ} (c : Fin n→E) : (linearized c).natDegree ≤ 2^(n-1) := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans (Nat.pow_le_pow_right (by decide) (by omega))
noncomputable def linearizedEval {n : ℕ} : (Fin n→E) →ₗ[K] E →ₗ[K] E where
  toFun c := (show E→+E from {
    toFun := fun x=>∑i,(c i)*(iterateFrobenius E 2 i.val x)
    map_zero' := by simp
    map_add' := by intro x y;simp [mul_add,Finset.sum_add_distrib] }).toZModLinearMap 2
  map_add' c w := by ext x;change (∑i,(c i+w i)*_) = _;simp [add_mul,Finset.sum_add_distrib]
  map_smul' k c := by
    rcases (show ∀x:K,x=0 ∨ x=1 by decide) k with rfl|rfl
    · simp only [map_zero,zero_smul];ext x;change (∑i,(0 : Fin n→E) i*_)=(0 : E);simp
    · simp
theorem linearized_eval {n : ℕ} (c : Fin n→E) (x : E) :
    linearizedEval c x=(linearized c).eval x := by
  simp only [linearized,eval_finsetSum,eval_monomial]
  rfl
theorem linearized_ker {U : Type} [AddCommGroup U] [Module K U] [Finite U] {n : ℕ}
    (f : U→ₗ[K] E) (hf : Function.Injective f) (c : Fin n→E) (hc : c≠0) :
    Module.finrank K (LinearMap.ker ((linearizedEval c).comp f)) ≤ n-1 := by
  classical
  have nz : linearized c≠0 := fun eq=>hc (funext fun i=>
    (linearized_coeff c i).symm.trans (by rw [eq,coeff_zero];rfl))
  let h := (linearizedEval c).comp f
  let roots := (linearized c).roots.toFinset
  let g (x : LinearMap.ker h) : roots := ⟨f x.val,by
    rw [Multiset.mem_toFinset,Polynomial.mem_roots nz]
    exact (linearized_eval c (f x.val)).symm.trans x.property⟩
  have bd := Nat.card_le_card_of_injective g (fun x y he=>Subtype.ext (hf (congrArg Subtype.val he)))
  rw [Module.natCard_eq_pow_finrank (K:=K),Nat.card_zmod,Nat.card_eq_finsetCard] at bd
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (bd.trans ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans (linearized_degree c))))
end OrbitUp.BoundedMatrices
end

/- BoundedMatrices -/
section
namespace OrbitUp.BoundedMatrices
theorem flanders_linear {U W : Type} [AddCommGroup U] [Module K U] [Finite U]
    [AddCommGroup W] [Module K W] [Finite W] (S : Submodule K (U→ₗ[K] W)) (R : ℕ)
    (sizes : Module.finrank K U ≤ Module.finrank K W) (ranks : ∀f:S,Module.finrank K (LinearMap.range f.val) ≤ R) :
    Module.finrank K S ≤ Module.finrank K W*R := by
  classical
  let b := Module.finrank K U
  let a := Module.finrank K W
  have total : Module.finrank K (U→ₗ[K] W)=b*a := Module.finrank_linearMap _ _ _ _
  by_cases large : b ≤ R
  · exact (Submodule.finrank_le S).trans (total.le.trans (by change b*a ≤ a*R;simpa [Nat.mul_comm] using Nat.mul_le_mul_right a large))
  have aPos : a≠0 := by change b ≤ a at sizes;omega
  let E := GaloisField 2 a
  have dimE : Module.finrank K E=a := GaloisField.finrank 2 aPos
  obtain ⟨f,hf⟩ : ∃f:U→ₗ[K] E,Function.Injective f := (finrank_le_iff_exists_linearMap).mp (by rw [dimE];exact sizes)
  let q : E≃ₗ[K] W := Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq dimE)
  let n := b-R
  let C : (Fin n→E) →ₗ[K] (U→ₗ[K] W) := {
    toFun c := q.toLinearMap.comp ((linearizedEval c).comp f)
    map_add' c z := by ext x;change q (linearizedEval (c+z) (f x))=_;rw [map_add];simp
    map_smul' c z := by ext x;change q (linearizedEval (c • z) (f x))=_;rw [map_smul];simp }
  have avoid (c : Fin n→E) (hc : c≠0) (hS : C c∈S) : False := by
    have kr := linearized_ker f hf c hc
    have hr : Module.finrank K (LinearMap.range (C c)) ≤ R := ranks ⟨_,hS⟩
    have nu := LinearMap.finrank_range_add_finrank_ker (C c)
    have eq : LinearMap.ker (C c)=LinearMap.ker ((linearizedEval c).comp f) := by
      change LinearMap.ker (q.toLinearMap.comp _)=_
      rw [LinearMap.ker_comp,q.ker,Submodule.comap_bot]
    rw [eq] at nu
    change _+_ = b at nu
    dsimp [n] at kr
    omega
  have inj : Function.Injective (S.mkQ.comp C) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro c hc
    by_contra nc
    exact avoid c nc ((Submodule.Quotient.mk_eq_zero S).mp (show S.mkQ (C c)=0 from hc))
  have bd := LinearMap.finrank_le_finrank_of_injective inj
  have dimC : Module.finrank K (Fin n→E)=n*a := by rw [Module.finrank_pi_fintype];simp [dimE]
  rw [dimC] at bd
  have sum := Submodule.finrank_quotient_add_finrank S
  rw [total] at sum
  have h := Nat.sub_add_cancel (le_of_lt (lt_of_not_ge large))
  change Module.finrank K S ≤ a*R
  have e : n*a+R*a=b*a := by rw [←Nat.add_mul,h]
  rw [Nat.mul_comm a R]
  omega
end OrbitUp.BoundedMatrices
end

/- Flanders -/
section
namespace OrbitUp.BoundedMatrices
private theorem matrix_oriented {a b : ℕ} (h : b ≤ a) (S : Submodule K (Matrix (Fin a) (Fin b) K))
    (R : ℕ) (hR : ∀ A:S,A.val.rank ≤ R) : Module.finrank K S ≤ a*R := by
  let e : Matrix (Fin a) (Fin b) K ≃ₗ[K] ((Fin b→K)→ₗ[K] Fin a→K) := Matrix.toLin'
  let P := S.map e.toLinearMap
  have hr (f:P) : Module.finrank K (LinearMap.range f.val) ≤ R := by
    obtain ⟨z,hz,eq⟩ := f.property
    rw [←eq]
    exact hR ⟨z,hz⟩
  have bound := flanders_linear P R (by simpa only [Module.finrank_fin_fun] using h) hr
  rw [Module.finrank_fin_fun,←(e.submoduleMap S).finrank_eq] at bound
  exact bound
theorem binary_flanders {a b : ℕ} (S : Submodule K (Matrix (Fin a) (Fin b) K))
    (R : ℕ) (hR : ∀ A:S,A.val.rank ≤ R) : Module.finrank K S ≤ max a b*R := by
  classical
  rcases le_total b a with h|h
  · rw [max_eq_left h];exact matrix_oriented h S R hR
  · rw [max_eq_right h]
    let e := Matrix.transposeLinearEquiv (Fin a) (Fin b) K K
    let P := S.map e.toLinearMap
    have ranks (A:P) : A.val.rank ≤ R := by
      obtain ⟨z,hz,eq⟩ := A.property
      rw [←eq]
      exact (Matrix.rank_transpose z).le.trans (hR ⟨z,hz⟩)
    exact (e.submoduleMap S).finrank_eq.le.trans (matrix_oriented h P R ranks)
end OrbitUp.BoundedMatrices
end

/- HyperplaneForms -/
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

/- MinimalPolar -/
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

/- PowerJacobiPair -/
section
namespace OrbitUp
open scoped Matrix
def powerJacobiPairs {d s : ℕ} (F : Q d s) :
    Submodule K ((Matrix (Fin d) (Fin s) K) × Module.Dual K (V s)) where
  carrier := {p | JacobiCompatible p.1 F ∧
    ∀ x y, jacobiPair p.1 x (F y)=p.2 (QuadraticMap.polar F x y)+jacobiPair p.1 y (QuadraticMap.polar F x y)}
  zero_mem' := ⟨(jacobiMatrixSpace F).zero_mem,by intro x y; simp [jacobiPair]⟩
  add_mem' := by
    rintro u v ⟨hu,h⟩ ⟨hv,k⟩
    refine ⟨(jacobiMatrixSpace F).add_mem hu hv,?_⟩
    intro x y
    have addP (x : V d) (w : V s) : jacobiPair (u.1+v.1) x w=jacobiPair u.1 x w+jacobiPair v.1 x w := by
      simp only [jacobiPair,Matrix.add_mulVec,dotProduct_add]
    change jacobiPair (u.1+v.1) _ _=(u.2 _+v.2 _)+jacobiPair (u.1+v.1) _ _
    rw [addP,addP,h,k];abel
  smul_mem' := by
    rintro k ⟨u,v⟩ h
    rcases (show ∀x:K,x=0 ∨ x=1 by decide) k with rfl|rfl
    · rw [zero_smul]; exact ⟨(jacobiMatrixSpace F).zero_mem,by intro x y; simp [jacobiPair]⟩
    · rwa [one_smul]
end OrbitUp
end

/- PowerDefect -/
section
namespace OrbitUp
open scoped Matrix
variable {d s : ℕ} (F : Q d s)
def jacobiRow (M : Matrix (Fin d) (Fin s) K) (x : V d) : Module.Dual K (V s) :=
  (dotProductBilin K K x).comp M.mulVecLin
lemma polar_member (x y : V d) : QuadraticMap.polar F x y∈polarSpan F :=
  Submodule.subset_span ⟨(x,y),rfl⟩
def polarRestriction : powerJacobiPairs F →ₗ[K] (V d → polarSpan F → K) where
  toFun p x y := jacobiPair p.val.1 x y.val
  map_add' a b := by funext x y;change jacobiPair (a.val.1+b.val.1) x y.val=_; simp only [jacobiPair,Matrix.add_mulVec,dotProduct_add];rfl
  map_smul' c a := by
    rcases (show ∀ c:K,c=0 ∨ c=1 by decide) c with rfl|rfl
    · simp only [zero_smul,RingHom.id_apply];funext x y;simp [jacobiPair]
    · simp
def modPolar : V d →ₗ[K] (V s ⧸ polarSpan F) where
  toFun x := (polarSpan F).mkQ (F x)
  map_add' x y := by
    rw [←map_add]
    apply (Submodule.Quotient.eq _).mpr
    have h : F (x+y)-(F x+F y)=QuadraticMap.polar F x y := by dsimp only [QuadraticMap.polar];abel
    rw [h];exact polar_member F x y
  map_smul' c x := by
    rcases (show ∀ c:K,c=0 ∨ c=1 by decide) c with rfl|rfl <;> simp
lemma modPolar_onto (hs : Submodule.span K (Set.range (F : V d → V s))=⊤) :
    Function.Surjective (modPolar F) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro v _
  obtain ⟨w,rfl⟩ := (polarSpan F).mkQ_surjective v
  have le : Submodule.span K (Set.range (F : V d → V s)) ≤ (modPolar F).range.comap (polarSpan F).mkQ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact ⟨x,rfl⟩
  exact le (hs.symm ▸ (show w∈(⊤ : Submodule K (V s)) from trivial))
private lemma quotient_basis_ext {W : Type} [AddCommGroup W] [Module K W] (B : Submodule K W)
    {k : ℕ} (b : Module.Basis (Fin k) K (W ⧸ B)) (w : Fin k→W) (hw : ∀ i,B.mkQ (w i)=b i)
    (h : W→ₗ[K]K) (hB : B ≤ h.ker) (hb : ∀i,h (w i)=0) : h=0 := by
  let L := B.liftQ h hB
  have he : L=0 := by
    apply b.ext
    intro i
    rw [←hw]
    exact hb i
  apply LinearMap.ext
  intro y
  exact DFunLike.congr_fun he (B.mkQ y)
private abbrev DualSlots (k : ℕ) := (((i : Fin k) × Fin i.val) ⊕ Fin k)
private def record {k : ℕ} (x : Fin k → V d) : LinearMap.ker (polarRestriction F) →ₗ[K] (DualSlots k → K) where
  toFun a := Sum.elim (fun z=>jacobiPair a.val.val.1 (x z.1) (F (x ⟨z.2.val,lt_trans z.2.isLt z.1.isLt⟩)))
    (fun i=>a.val.val.2 (F (x i)))
  map_add' u v := by
    funext z;cases z with
    | inl i => change jacobiPair (u.val.val.1+v.val.val.1) _ _=_; simp only [jacobiPair,Matrix.add_mulVec,dotProduct_add]; rfl
    | inr i => rfl
  map_smul' c a := by
    rcases (show ∀ c:K,c=0 ∨ c=1 by decide) c with rfl|rfl
    · simp only [zero_smul,RingHom.id_apply];funext z;cases z with
      | inl i => simp [jacobiPair]
      | inr i => rfl
    · simp
lemma power_restriction_kernel (hs : Submodule.span K (Set.range (F : V d → V s))=⊤) :
    let k := Module.finrank K (V s ⧸ polarSpan F)
    Module.finrank K (LinearMap.ker (polarRestriction F)) ≤ k*(k+1)/2 := by
  let B := polarSpan F
  let k := Module.finrank K (V s ⧸ B)
  let b := Module.finBasis K (V s ⧸ B)
  choose x hx using fun i : Fin k => modPolar_onto F hs (b i)
  let q (i : Fin k) := F (x i)
  have hq (i : Fin k) : B.mkQ (q i)=b i := hx i
  have hrec : Function.Injective (record F x) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro u hu
    let M := u.val.val.1
    let δ := u.val.val.2
    have van (y : V d) (w : V s) (hw:w∈B) : jacobiPair M y w=0 :=
      congrFun (congrFun (show polarRestriction F u.val=0 from u.property) y) ⟨w,hw⟩
    have compat (y z : V d) : jacobiPair M y (F z)=δ (QuadraticMap.polar F y z) := by
      have h := u.val.property.2 y z
      change jacobiPair M y (F z)=δ _+jacobiPair M z _ at h
      rw [van z _ (polar_member F y z),add_zero] at h
      exact h
    have sym (y z : V d) : jacobiPair M y (F z)=jacobiPair M z (F y) := by
      rw [compat,compat,QuadraticMap.polar_comm F y z]
    have diag (y : V d) : jacobiPair M y (F y)=0 := by
      rw [compat,F.polar_self]
      have h : 2 • F y=0 := by
        funext i;change 2 • F y i=0;rw [two_nsmul];exact (show ∀a:K,a+a=0 by decide) _
      rw [h,map_zero]
    have low (i j : Fin k) (hj : j < i) : jacobiPair M (x i) (q j)=0 :=
      congrFun hu (.inl ⟨i,⟨j.val,hj⟩⟩)
    have allp (i j : Fin k) : jacobiPair M (x i) (q j)=0 := by
      rcases lt_trichotomy j i with l|rfl|l
      · exact low i j l
      · exact diag (x j)
      · exact (sym (x i) (x j)).trans (low j i l)
    have onbasis (i : Fin k) : jacobiRow M (x i)=0 :=
      quotient_basis_ext B b q hq _ (fun w hw=>van _ w hw) (allp i)
    have allrow (y : V d) : jacobiRow M y=0 := by
      apply quotient_basis_ext B b q hq (jacobiRow M y) (fun w hw=>van y w hw)
      intro i
      exact (sym y (x i)).trans (DFunLike.congr_fun (onbasis i) (F y))
    have zeroM : M=0 := by
      ext i j
      have h := DFunLike.congr_fun (allrow (basis i)) (basis j)
      change jacobiPair M (basis i) (basis j)=0 at h
      rw [jacobiPair_basis] at h
      simpa [Matrix.mulVec,dotProduct,basis,Pi.single_apply,mul_ite] using h
    have le : B ≤ δ.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨y,z⟩,rfl⟩
      exact (compat y z).symm.trans (DFunLike.congr_fun (allrow y) (F z))
    have zeroδ := quotient_basis_ext B b q hq δ le (fun i=>congrFun hu (.inr i))
    exact Subtype.ext (Subtype.ext (Prod.ext zeroM zeroδ))
  have hdim := LinearMap.finrank_le_finrank_of_injective hrec
  rw [Module.finrank_fintype_fun_eq_card,←Nat.card_eq_fintype_card] at hdim
  change _ ≤ Nat.card ((((i : Fin k) × Fin i.val) ⊕ Fin k)) at hdim
  rw [Nat.card_sum,Erdos1160Growth.SharpFamily.triangular_card,Nat.card_fin] at hdim
  have e := twice_slots k
  dsimp only [slotsN] at e
  change _ ≤ k*(k+1)/2
  have he : k*(k+1)=k^2+k := by ring
  rw [he,←e];omega
end OrbitUp
end

/- PowerDefectRank -/
section
namespace OrbitUp
open scoped Matrix
variable {d s : ℕ} (F : Q d s)
lemma jacobi_of_annihilating {M : Matrix (Fin d) (Fin s) K}
    (h : polarSpan F ≤ M.mulVecLin.ker) : JacobiCompatible M F := by
  intro x y z
  have e (u v : V d) : M.mulVec (QuadraticMap.polar F u v)=0 := h (polar_member F u v)
  simp only [jacobiPair,e,dotProduct_zero,sub_zero]
theorem jacobi_rank_of_defect (hs : Submodule.span K (Set.range (F : V d → V s))=⊤) :
    ∃ M : Matrix (Fin d) (Fin s) K,JacobiCompatible M F ∧ M.rank=Module.finrank K (V s ⧸ polarSpan F) := by
  let B := polarSpan F
  obtain ⟨g,hg⟩ := (modPolar F).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (modPolar_onto F hs))
  have hinj : Function.Injective g := (show Function.LeftInverse (modPolar F) g from fun x=>DFunLike.congr_fun hg x).injective
  let h := g.comp B.mkQ
  let M := LinearMap.toMatrix' h
  have atM : M.mulVecLin=h := LinearMap.ext (fun w=>LinearMap.toMatrix'_mulVec h w)
  refine ⟨M,jacobi_of_annihilating F (fun w hw=>?_),?_⟩
  · change M.mulVecLin w=0
    rw [atM]
    change g (B.mkQ w)=0
    rw [show B.mkQ w=0 from (Submodule.Quotient.mk_eq_zero B).mpr hw,map_zero]
  · change Module.finrank K M.mulVecLin.range=_
    rw [atM,LinearMap.range_comp_of_range_eq_top g (LinearMap.range_eq_top.mpr B.mkQ_surjective),LinearMap.finrank_range_of_inj hinj]
end OrbitUp
end

/- PolarCompression -/
section
namespace OrbitUp
open scoped Matrix
variable {d s : ℕ} (F : Q d s)
def polarOntoB : V d→ₗ[K] V d→ₗ[K] polarSpan F where
  toFun x := (F.polarBilin x).codRestrict _ (fun y=>polar_member F x y)
  map_add' x y := LinearMap.ext (fun w=>Subtype.ext (DFunLike.congr_fun (F.polarBilin.map_add x y) w))
  map_smul' c x := LinearMap.ext (fun w=>Subtype.ext (DFunLike.congr_fun (F.polarBilin.map_smul c x) w))
theorem polarOntoB_span : BoundedMatrices.valuesOn (polarOntoB F) ⊤=⊤ := by
  classical
  let B := polarSpan F
  let U := BoundedMatrices.valuesOn (polarOntoB F) ⊤
  have core : B ≤ U.map B.subtype := Submodule.span_le.mpr (by
    rintro _ ⟨⟨x,y⟩,rfl⟩
    refine ⟨polarOntoB F x y,Submodule.subset_span ⟨(⟨x,Submodule.mem_top⟩,⟨y,Submodule.mem_top⟩),rfl⟩,rfl⟩)
  apply top_unique
  intro w _
  obtain ⟨v,hv,e⟩ := core w.property
  exact Subtype.ext e ▸ hv
theorem compressed_polar {D : Submodule K (V d)} (spanD : BoundedMatrices.valuesOn (polarOntoB F) D=⊤)
    (M : Matrix (Fin d) (Fin s) K) (hJ : JacobiCompatible M F)
    (hz : ∀x:D,∀w:polarSpan F,jacobiPair M x.val w.val=0) :
    ∀x : V d,∀w:polarSpan F,jacobiPair M x w.val=0 := by
  intro x
  let L := (jacobiRow M x).comp (polarSpan F).subtype
  have ke : BoundedMatrices.valuesOn (polarOntoB F) D ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨y,z⟩,rfl⟩
    change jacobiPair M x (QuadraticMap.polar F y.val z.val)=0
    have hy : jacobiPair M y.val (QuadraticMap.polar F x z.val)=0 := hz y (polarOntoB F x z.val)
    have hz' : jacobiPair M z.val (QuadraticMap.polar F x y.val)=0 := hz z (polarOntoB F x y.val)
    rw [hJ x y.val z.val,hy,hz',sub_zero]
  rw [spanD] at ke
  exact fun w=>ke (Submodule.mem_top)
private theorem tested_on_bases {D : Submodule K (V d)}
    (M : Matrix (Fin d) (Fin s) K) {ι κ : Type} (A : Module.Basis ι K D) (B : Module.Basis κ K (polarSpan F))
    (hz : ∀i j,jacobiPair M (A i).val (B j).val=0) :
    ∀x:D,∀w:polarSpan F,jacobiPair M x.val w.val=0 := by
  have on (i : ι) : (jacobiRow M (A i).val).comp (polarSpan F).subtype=0 :=
    B.ext (fun j=>hz i j)
  intro x w
  let L := ((dotProductBilin K K).flip (M.mulVec w.val)).comp D.subtype
  have e : L = 0 := A.ext (fun i=>DFunLike.congr_fun (on i) w)
  exact DFunLike.congr_fun e x
theorem polar_image_rank (R : ℕ) (hr : ∀M : Matrix (Fin d) (Fin s) K,JacobiCompatible M F→M.rank ≤ R) :
    Module.finrank K (LinearMap.range (polarRestriction F))≤(Module.finrank K (polarSpan F)+1)*R := by
  classical
  let B := polarSpan F
  obtain ⟨D,sp,size⟩ := BoundedMatrices.minimal_commutator_span (polarOntoB F) (fun x=>by
    apply Subtype.ext;change QuadraticMap.polar F x x=0
    have hx : x+x=0 := by funext i;exact (show ∀t:K,t+t=0 by decide) _
    simp only [QuadraticMap.polar,hx,F.map_zero,zero_sub]
    ext i;change -(F x i)-F x i=0;exact (show ∀t:K,-t-t=0 by decide) _)
    (polarOntoB_span F)
  let a := Module.finrank K D
  let b := Module.finrank K B
  let A := Module.finBasis K D
  let Z := Module.finBasis K B
  let V₀ := LinearMap.range (polarRestriction F)
  let read : V₀→ₗ[K] Matrix (Fin a) (Fin b) K := {
    toFun := fun f i j=>f.val (A i).val (Z j)
    map_add' _ _ := rfl,map_smul' _ _ := rfl }
  have inj : Function.Injective read := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    rintro ⟨_,p,rfl⟩ hp
    apply Subtype.ext;funext x w
    exact compressed_polar F sp p.val.1 p.property.1 (tested_on_bases F _ A Z (fun i j=>
      congrArg (fun m:Matrix (Fin a) (Fin b) K=>m i j) (show read _=0 from hp))) x w
  let X : Matrix (Fin a) (Fin d) K := fun i=>(A i).val
  let Z' : Matrix (Fin s) (Fin b) K := fun i j=>(Z j).val i
  have rank (T : LinearMap.range read) : T.val.rank ≤ R := by
    obtain ⟨⟨_,p,rfl⟩,e⟩ := T.property
    have he : read ⟨polarRestriction F p,⟨p,rfl⟩⟩ = X*(p.val.1*Z') := by
      ext i j
      change jacobiPair p.val.1 (A i).val (Z j).val=_
      rfl
    rw [←e,he]
    exact ((Matrix.rank_mul_le_right ..).trans (Matrix.rank_mul_le_left ..)).trans (hr _ p.property.1)
  have bound := BoundedMatrices.binary_flanders (LinearMap.range read) R rank
  rw [LinearMap.finrank_range_of_inj inj] at bound
  exact bound.trans (Nat.mul_le_mul_right R (max_le size (Nat.le_succ _)))
end OrbitUp
end

/- PeakPowerPairs -/
section
namespace OrbitUp
theorem power_pairs_peak {d s : ℕ} (F : Q d s)
    (hs : Submodule.span K (Set.range (F : V d→V s))=⊤)
    (R : ℕ) (hr : ∀M : Matrix (Fin d) (Fin s) K,JacobiCompatible M F→M.rank ≤ R) :
    Module.finrank K (powerJacobiPairs F)≤(s+1)*R := by
  let b := Module.finrank K (polarSpan F)
  let k := Module.finrank K (V s ⧸ polarSpan F)
  have sum : k+b=s := (Submodule.finrank_quotient_add_finrank (polarSpan F)).trans (Module.finrank_fin_fun K)
  have range := polar_image_rank F R hr
  have ker := power_restriction_kernel F hs
  obtain ⟨M,hM,hk⟩ := jacobi_rank_of_defect F hs
  have kr : k ≤ R := hk.ge.trans (hr M hM)
  have eq := LinearMap.finrank_range_add_finrank_ker (polarRestriction F)
  change _≤(b+1)*R at range
  change _ ≤ k*(k+1)/2 at ker
  have square : k*(k+1)/2 ≤ k*R := by
    by_cases z : k=0
    · simp [z]
    have a := Nat.mul_le_mul_left k (show k+1 ≤ 2*R by omega)
    apply (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)).mpr
    nlinarith only [a]
  calc _ = _ := eq.symm
       _ ≤ (b+1)*R+k*R := Nat.add_le_add range (ker.trans square)
       _ = (s+1)*R := by rw [←Nat.add_mul];congr 1;omega
end OrbitUp
end

/- SquareNucleusOperations -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
variable {E : Type*} [Group E]
def squareElement (x : E) : squareCore E := ⟨x*x, Subgroup.subset_closure ⟨x,rfl⟩⟩
def derivedElement (x y : E) : squareCore E := ⟨⁅x,y⁆,derived_le_squares E (secondBracket x y).property⟩
def nSquare (w : squareCore E) : binaryThird E := ⟨w.val*w.val,Subgroup.subset_closure (.inl ⟨w,rfl⟩)⟩
def nBracket (w : squareCore E) (x : E) : binaryThird E := ⟨⁅w.val,x⁆,Subgroup.subset_closure (.inr ⟨(w,x),rfl⟩)⟩
variable (hc : binaryThird E ≤ Subgroup.center E) (hb : ∀ z : binaryThird E, z*z=1)
include hc in
lemma nBracket_right (w : squareCore E) (x y : E) : nBracket w (x*y)=nBracket w x*nBracket w y := by
  apply Subtype.ext
  change ⁅w.val,x*y⁆=⁅w.val,x⁆*⁅w.val,y⁆
  have hz := Subgroup.mem_center_iff.mp (hc (nBracket w y).property) x
  rw [commutatorElement_mul_right_eq_mul_conj]
  change x*⁅w.val,y⁆=⁅w.val,y⁆*x at hz
  calc ⁅w.val,x⁆*x*⁅w.val,y⁆*x⁻¹ = ⁅w.val,x⁆*(x*⁅w.val,y⁆)*x⁻¹ := by group
       _ = _ := by rw [hz];group
include hc in
lemma nBracket_left (w v : squareCore E) (x : E) : nBracket (w*v) x=nBracket w x*nBracket v x := by
  apply Subtype.ext
  change ⁅w.val*v.val,x⁆=⁅w.val,x⁆*⁅v.val,x⁆
  have hz := Subgroup.mem_center_iff.mp (hc (nBracket v x).property) w.val
  have hz' := Subgroup.mem_center_iff.mp (hc (nBracket v x).property) ⁅w.val,x⁆
  change w.val*⁅v.val,x⁆=⁅v.val,x⁆*w.val at hz
  rw [commutatorElement_mul_left_eq_conj_mul,hz,mul_inv_cancel_right]
  exact hz'.symm
include hc hb in
lemma squareCore_commutes (w v : squareCore E) : Commute w.val v.val := by
  have h : squareCore E ≤ Subgroup.centralizer {w.val} := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g,rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have e : nBracket w (g*g)=1 := (nBracket_right hc w g g).trans (hb _)
    exact congrArg Subtype.val e
  exact Subgroup.mem_centralizer_iff.mp (h v.property) w.val (Set.mem_singleton _)
def nPowerChar (μ : binaryThird E →* C₂) : squareCore E →* C₂ where
  toFun w := μ (nSquare w)
  map_one' := by rw [show nSquare (1:squareCore E)=1 from Subtype.ext (one_mul _),map_one]
  map_mul' w v := by
    rw [←map_mul]
    apply congrArg μ
    apply Subtype.ext
    exact (pow_two _).symm.trans (((squareCore_commutes hc hb w v).mul_pow 2).trans (by rw [pow_two,pow_two];rfl))
def nBilinear (μ : binaryThird E →* C₂) : squareCore E →* (E →* C₂) where
  toFun w := {
    toFun x := μ (nBracket w x)
    map_one' := by rw [show nBracket w 1=1 from Subtype.ext (by simp [nBracket]),map_one]
    map_mul' x y := by rw [nBracket_right hc,map_mul] }
  map_one' := by ext x;change μ (nBracket 1 x)=1;rw [show nBracket (1:squareCore E) x=1 from Subtype.ext (by simp [nBracket]),map_one]
  map_mul' w v := by ext x;change μ (nBracket (w*v) x)=_;rw [nBracket_left hc,map_mul];rfl
include hc hb in

lemma char_square_rule (μ : binaryThird E →* C₂) (x y : E) :
    μ (nBracket (squareElement y) x)=μ (nSquare (derivedElement x y))*μ (nBracket (derivedElement x y) y) := by
  let c := ⁅x,y⁆
  let h := ⁅c,y⁆
  have hh : h∈Subgroup.center E := hc (nBracket (derivedElement x y) y).property
  have invh : h⁻¹=h := inv_eq_of_mul_eq_one_left (congrArg Subtype.val (hb (nBracket (derivedElement x y) y)))
  have swap : y*c*y⁻¹=h*c := by
    rw [←invh,commutatorElement_inv,commutatorElement_def];group
  have e : ⁅x,y*y⁆=(c*c)*h := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    change c*y*c*y⁻¹=(c*c)*h
    calc c*y*c*y⁻¹=c*(y*c*y⁻¹) := by group
         _ = _ := by rw [swap,←Subgroup.mem_center_iff.mp hh c];group
  have ei : ⁅y*y,x⁆=⁅x,y*y⁆ := by
    exact ((inv_eq_of_mul_eq_one_left (congrArg Subtype.val (hb (nBracket (squareElement y) x)))).symm).trans (commutatorElement_inv ..)
  rw [←map_mul]
  exact congrArg μ (Subtype.ext (ei.trans e))
end Erdos1160.CentralLifts.Survival
end

/- NucleusCharacters -/
section
namespace OrbitUp
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper Erdos1160.CentralLifts.Survival
open scoped Matrix commutatorElement
variable {E : Type*} [Group E] {d s : ℕ}
structure NucleusFrame (E : Type*) [Group E] {d s : ℕ} (F : Q d s) where
  base : E →* Multiplicative (V d)
  fiber : squareCore E →* Multiplicative (V s)
  base_onto : Function.Surjective base
  fiber_onto : Function.Surjective fiber
  central : binaryThird E ≤ Subgroup.center E
  binary : ∀ z : binaryThird E,z*z=1
  fiber_ker : ∀ w : squareCore E,w ∈ fiber.ker → w.val∈Subgroup.center E ∧ w.val*w.val=1
  base_ker : ∀ (w : squareCore E) (x : E), x∈base.ker → Commute w.val x
  diag : ∀ y,(fiber (squareElement y)).toAdd=F (base y).toAdd
  polar : ∀ x y,(fiber (derivedElement x y)).toAdd=QuadraticMap.polar F (base x).toAdd (base y).toAdd
structure PairReads {F : Q d s} (A : NucleusFrame E F) (μ : binaryThird E →* C₂)
    (p : Matrix (Fin d) (Fin s) K × Module.Dual K (V s)) : Prop where
  bracket : ∀ w x, jacobiPair p.1 (A.base x).toAdd (A.fiber w).toAdd=(μ (nBracket w x)).toAdd
  square : ∀ w, p.2 (A.fiber w).toAdd=(μ (nSquare w)).toAdd
theorem pair_exists {F : Q d s} (A : NucleusFrame E F) (μ : binaryThird E →* C₂) :
    ∃ p : powerJacobiPairs F,PairReads A μ p.val := by
  let T := nBilinear A.central μ
  let S := nPowerChar A.central A.binary μ
  have hk (w : squareCore E) (hw : w∈A.fiber.ker) : nSquare w=1 := Subtype.ext (A.fiber_ker w hw).2
  have hkS : A.fiber.ker ≤ S.ker := by
    intro w hw
    change μ (nSquare w)=1
    rw [hk w hw,map_one]
  let δ := A.fiber.liftOfSurjective A.fiber_onto (⟨S,hkS⟩ : {h : squareCore E→*C₂ // A.fiber.ker ≤ h.ker})
  let l : V s →ₗ[K] K := (show V s →+ K from {
    toFun x := (δ (.ofAdd x)).toAdd
    map_zero' := congrArg Multiplicative.toAdd δ.map_one
    map_add' x y := congrArg Multiplicative.toAdd (δ.map_mul (.ofAdd x) (.ofAdd y)) }).toZModLinearMap 2
  have hl (w : squareCore E) : l (A.fiber w).toAdd=(μ (nSquare w)).toAdd :=
    congrArg (fun h : {h : squareCore E→*C₂ // A.fiber.ker ≤ h.ker} => (h.val w).toAdd)
       ((A.fiber.liftOfSurjective A.fiber_onto).left_inv ⟨S,hkS⟩)
  have hkT : A.fiber.ker ≤ T.ker := by
    intro w hw
    apply MonoidHom.ext
    intro x
    change μ (nBracket w x)=1
    rw [show nBracket w x=1 from Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (A.fiber_ker w hw).1 x).symm),map_one]
  have hkB (w : squareCore E) : A.base.ker≤(T w).ker := by
    intro x hx
    change μ (nBracket w x)=1
    rw [show nBracket w x=1 from Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr (A.base_ker w x hx).eq),map_one]
  obtain ⟨t,ht⟩ := descend_pair A.fiber A.fiber_onto A.base A.base_onto T hkT hkB
  let M := pairingMatrix t
  have read (w : squareCore E) (x : E) : jacobiPair M (A.base x).toAdd (A.fiber w).toAdd=(μ (nBracket w x)).toAdd :=
    (pairingMatrix_apply t ..).trans (congrArg Multiplicative.toAdd (ht w x))
  have hj : JacobiCompatible M F := by
    intro x y z
    obtain ⟨u,hu⟩ := A.base_onto (.ofAdd x)
    obtain ⟨v,hv⟩ := A.base_onto (.ofAdd y)
    obtain ⟨w,hw⟩ := A.base_onto (.ofAdd z)
    change (A.base u).toAdd=x at hu;change (A.base v).toAdd=y at hv;change (A.base w).toAdd=z at hw
    rw [←hu,←hv,←hw,←A.polar,←A.polar,←A.polar,read,read,read]
    have tri (a b c : E) : ⁅⁅a,b⁆,c⁆∈Subgroup.center E := A.central (nBracket (derivedElement a b) c).property
    have h : nBracket (derivedElement v w) u=nBracket (derivedElement u w) v*(nBracket (derivedElement u v) w)⁻¹ :=
      Subtype.ext (triple_rearranged tri u v w)
    rw [h,map_mul,map_inv,sub_eq_add_neg];rfl
  refine ⟨⟨(M,l),hj,?_⟩,⟨read,hl⟩⟩
  intro x y
  obtain ⟨u,hu⟩ := A.base_onto (.ofAdd x)
  obtain ⟨v,hv⟩ := A.base_onto (.ofAdd y)
  change (A.base u).toAdd=x at hu;change (A.base v).toAdd=y at hv
  change jacobiPair M x (F y)=l (QuadraticMap.polar F x y)+jacobiPair M y (QuadraticMap.polar F x y)
  rw [←hu,←hv,←A.polar,←A.diag,read,read,hl]
  exact congrArg Multiplicative.toAdd (char_square_rule A.central A.binary μ u v)
theorem reads_separate {F : Q d s} (A : NucleusFrame E F) {μ η : binaryThird E →* C₂}
    {p : Matrix (Fin d) (Fin s) K × Module.Dual K (V s)}
    (hr : PairReads A μ p) (hs : PairReads A η p) : μ=η := by
  let L := (μ.eqLocus η).map (binaryThird E).subtype
  have sub : binaryThird E ≤ L := by
    apply (Subgroup.closure_le _).mpr
    rintro _ (⟨w,rfl⟩|⟨⟨w,x⟩,rfl⟩)
    · exact ⟨nSquare w,Multiplicative.toAdd.injective ((hr.square w).symm.trans (hs.square w)),rfl⟩
    · exact ⟨nBracket w x,Multiplicative.toAdd.injective ((hr.bracket w x).symm.trans (hs.bracket w x)),rfl⟩
  apply MonoidHom.ext
  intro z
  obtain ⟨w,hw,eq⟩ := sub z.property
  exact (Subtype.ext eq : w=z) ▸ hw
noncomputable def nucleusPair {F : Q d s} (A : NucleusFrame E F) (μ : binaryThird E →* C₂) : powerJacobiPairs F :=
  (pair_exists A μ).choose
theorem nucleusPair_inj {F : Q d s} (A : NucleusFrame E F) : Function.Injective (nucleusPair A) := by
  intro μ η he
  have h : PairReads A η (nucleusPair A μ).val := by
    rw [he]
    exact (pair_exists A η).choose_spec
  exact reads_separate A ((pair_exists A μ).choose_spec) h
end OrbitUp
end

/- QuadraticNucleusFrame -/
section
namespace OrbitUp
open Erdos1160Growth Erdos1160Growth.LowerTriangularUpper Erdos1160.DeepJacobi
open Erdos1160.CentralLifts.Survival
open scoped Matrix commutatorElement
variable {d s : ℕ} (B : V d →+ V d →+ V s)
private lemma bits_cancel {j : ℕ} (x : V j) : x+x=0 := by
  funext i
  exact (show ∀ a : K,a+a=0 by decide) (x i)
lemma square_as_fiber (x : BilinearExtension B) :
    x*x=liftW B (diagonalQ B x.base) := by
  apply BilinearExtension.ext
  · exact bits_cancel _
  · change x.fiber+x.fiber+B x.base x.base=B x.base x.base
    rw [bits_cancel,zero_add]
lemma bracket_as_fiber (x y : BilinearExtension B) :
    ⁅x,y⁆=liftW B (QuadraticMap.polar (diagonalQ B) x.base y.base) := by
  rw [←bracket_polar,BilinearExtension.commutator_formula,BilinearExtension.commutator_formula]
  rfl
lemma squareCore_full (hs : Submodule.span K (Set.range (diagonalQ B : V d → V s))=⊤) :
    squareCore (BilinearExtension B)=(BilinearExtension.projection B).ker := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨v,rfl⟩
    exact bits_cancel _
  have h : Submodule.span K (Set.range (diagonalQ B : V d → V s)) ≤ fiberSub B (squareCore (BilinearExtension B)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    change liftW B (diagonalQ B x)∈squareCore (BilinearExtension B)
    exact (square_as_fiber B (liftV B x)) ▸ (squareElement (liftV B x)).property
  rw [hs] at h
  rintro ⟨x,w⟩ (hx:x=0)
  subst x
  exact h (Submodule.mem_top : w ∈ (⊤ : Submodule K (V s)))
variable {E : Type*} [Group E] (f : E →* BilinearExtension B) (hf : Function.Surjective f)
variable (hs : Submodule.span K (Set.range (diagonalQ B : V d → V s))=⊤)
include hf hs in
lemma square_image_base (w : squareCore E) : (f w.val).base=0 :=
  (squareCore_full B hs ▸ (CentralKernelCount.squareCore_map f hf).le ⟨w.val,w.property,rfl⟩ :
    f w.val ∈ (BilinearExtension.projection B).ker)
def squareCoordinate : squareCore E →* Multiplicative (V s) where
  toFun w := .ofAdd (f w.val).fiber
  map_one' := by change (f 1).fiber=0; rw [f.map_one];rfl
  map_mul' u v := by
    change (f (u.val*v.val)).fiber= (f u.val).fiber+(f v.val).fiber
    rw [f.map_mul,BilinearExtension.mul_fiber,square_image_base B f hf hs u,B.map_zero]
    simp
lemma squareCoordinate_onto : Function.Surjective (squareCoordinate B f hf hs) := by
  intro w
  have h : liftW B w.toAdd∈(squareCore E).map f := by
    rw [CentralKernelCount.squareCore_map f hf,squareCore_full B hs]
    rfl
  obtain ⟨u,hu,eq⟩ := h
  exact ⟨⟨u,hu⟩,congrArg BilinearExtension.fiber eq⟩
noncomputable def quadraticNucleusFrame (hc : f.ker ≤ Subgroup.center E)
    (hb : ∀ z : f.ker,z*z=1) : NucleusFrame E (diagonalQ B) := by
  let base := (BilinearExtension.projection B).comp f
  let fiber := squareCoordinate B f hf hs
  have kill : binaryThird E ≤ f.ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ (⟨w,rfl⟩|⟨⟨w,x⟩,rfl⟩)
    · change f (w.val*w.val)=1
      rw [f.map_mul,square_as_fiber,square_image_base B f hf hs w]
      have h : diagonalQ B 0=0 := (diagonalQ B).map_zero
      rw [h];rfl
    · change f ⁅w.val,x⁆=1
      rw [map_commutatorElement]
      have c : f w.val∈Subgroup.center (BilinearExtension B) := by
        have e : f w.val=liftW B (f w.val).fiber :=
          BilinearExtension.ext (square_image_base B f hf hs w) rfl
        rw [e];exact BilinearExtension.central_fiber _
      exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp c _).symm
  have binary (z : binaryThird E) : z*z=1 := Subtype.ext (congrArg (fun v : f.ker => (v : E)) (hb ⟨z.val,kill z.property⟩))
  refine ⟨base,fiber,(base_surj B).comp hf,squareCoordinate_onto B f hf hs,kill.trans hc,binary,?_,?_,?_,?_⟩
  · intro w hw
    have eq : f w.val=1 := BilinearExtension.ext (square_image_base B f hf hs w) (show (f w.val).fiber=0 from hw)
    exact ⟨hc eq,congrArg Subtype.val (hb ⟨w.val,eq⟩)⟩
  · intro w x hx
    have mem : liftW B (f x).fiber∈(squareCore E).map f := by
      rw [CentralKernelCount.squareCore_map f hf,squareCore_full B hs];rfl
    obtain ⟨v,hv,eq⟩ := mem
    have eq' : f v=f x := eq.trans (BilinearExtension.ext (show 0=(f x).base from Eq.symm hx) rfl)
    have cent : v⁻¹*x∈Subgroup.center E := hc (show f (v⁻¹*x)=1 by rw [f.map_mul,f.map_inv,eq',inv_mul_cancel])
    have h1 := squareCore_commutes (kill.trans hc) binary w ⟨v,hv⟩
    have h2 : Commute w.val (v⁻¹*x) := Subgroup.mem_center_iff.mp cent _
    simpa using h1.mul_right h2
  · intro x
    change (f (x*x)).fiber=diagonalQ B (f x).base
    rw [f.map_mul,square_as_fiber];rfl
  · intro x y
    change (f ⁅x,y⁆).fiber=QuadraticMap.polar (diagonalQ B) (f x).base (f y).base
    rw [map_commutatorElement,bracket_as_fiber];rfl
end OrbitUp
end

/- NucleusPairBound -/
section
namespace OrbitUp
open Erdos1160Growth Erdos1160Growth.LowerTriangularUpper Erdos1160.DeepJacobi
open Erdos1160.CentralLifts.Survival
open scoped BigOperators
private lemma binary_character_count {S : Type*} [Group S] [Finite S] {k : ℕ}
    (hs : ∀x:S,x*x=1) (hsize : Nat.card S=2^k) : 2^k ≤ Nat.card (S→*C₂) := by
  obtain ⟨i⟩ := exist_elementary_coords hs hsize
  let dot (v : Fin k → ZMod 2) : Multiplicative (Fin k → ZMod 2) →* C₂ := {
    toFun := fun x => Multiplicative.ofAdd (∑j,v j*x.toAdd j)
    map_one' := by change (∑j,v j*0)=0; simp
    map_mul' := fun x y=>by
      change (∑j,v j*(x.toAdd j+y.toAdd j))=(∑j,v j*x.toAdd j)+(∑j,v j*y.toAdd j)
      simp [mul_add,Finset.sum_add_distrib] }
  let embed (v : Fin k → ZMod 2) : S →* C₂ := (dot v).comp i.toMonoidHom
  have ev (v : Fin k→ZMod 2) (j : Fin k) : embed v (i.symm (Multiplicative.ofAdd (Pi.single j 1))) =
      Multiplicative.ofAdd (v j) := by
    change (∑l : Fin k,v l * ((i (i.symm (Multiplicative.ofAdd (Pi.single j 1)))).toAdd l)) = _
    rw [i.apply_symm_apply]
    simp [Pi.single_apply, mul_ite]
    rfl
  have inj : Function.Injective embed := by
    intro v w h
    funext j
    have h' := congrArg (fun g : S →* C₂ => g (i.symm (Multiplicative.ofAdd (Pi.single j 1)))) h
    exact (ev v j).symm.trans (h'.trans (ev w j))
  let _ : Finite (S→*C₂) := Finite.of_injective (fun g : S→*C₂ => (g : S→C₂)) DFunLike.coe_injective
  simpa only [Nat.card_fun,Nat.card_zmod,Nat.card_fin] using Nat.card_le_card_of_injective _ inj
theorem nucleus_le_power_pairs {d s t : ℕ} (B : V d →+ V d →+ V s)
    (hs : Submodule.span K (Set.range (diagonalQ B : V d → V s))=⊤)
    (π : FreeGroup (Fin t) →* BilinearExtension B) (hπ : Function.Surjective π) :
    nucleusRank π ≤ Module.finrank K (powerJacobiPairs (diagonalQ B)) := by
  let _ : Finite (BilinearExtension B) := Finite.of_equiv _ (BilinearExtension.coordinateEquiv B).symm
  have hsize : Nat.card (BilinearExtension B)=2^(d+s) := by simp [BilinearExtension.card,V,←Nat.pow_add]
  have he := cover_card π hπ
  rw [hsize,←pow_add] at he
  let _ : Finite (Cover π) := Nat.finite_of_card_ne_zero (he ▸ Nat.ne_of_gt (Nat.two_pow_pos _))
  let A := quadraticNucleusFrame B (coverProjection π) (cover_onto π hπ) hs (cover_central π) (cover_binary π)
  let _ : Finite (Module.Dual K (V s)) := Finite.of_injective (fun l : Module.Dual K (V s) => (l : V s→K)) DFunLike.coe_injective
  have h := (binary_character_count A.binary (nucleus_card π hπ hsize)).trans
    (Nat.card_le_card_of_injective (nucleusPair A) (nucleusPair_inj A))
  let _ : Fintype (powerJacobiPairs (diagonalQ B)) := Fintype.ofFinite _
  have hd := Module.card_eq_pow_finrank (K := K) (V := powerJacobiPairs (diagonalQ B))
  rw [←Nat.card_eq_fintype_card,ZMod.card] at hd
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  exact h.trans_eq hd
end OrbitUp
end

/- NucleusPeak -/
section
namespace OrbitUp
open Erdos1160.CentralLifts.Survival Erdos1160Growth Erdos1160Growth.LowerTriangularUpper
theorem nucleus_peak {d s t : ℕ} (B : V d →+ V d →+ V s)
    (hs : Submodule.span K (Set.range (diagonalQ B : V d→V s))=⊤)
    (π : FreeGroup (Fin t)→* BilinearExtension B) (hπ : Function.Surjective π)
    (R : ℕ) (hr : ∀M : Matrix (Fin d) (Fin s) K,JacobiCompatible M (diagonalQ B)→M.rank ≤ R) :
    nucleusRank π≤(s+1)*R :=
  (nucleus_le_power_pairs B hs π hπ).trans (power_pairs_peak (diagonalQ B) hs R hr)
end OrbitUp
end

/- RootFiberCount -/
section
namespace Erdos1160.CentralLifts.Survival
variable {d r s : ℕ} {Q V : Type} [Group Q] [Group V] [Finite Q] [Finite V]
noncomputable def initialPresentation {m : ℕ} (c : Codes 2 m) : Fin (m*(m+1)/2) → FreeGroup (Fin m) := by
  classical
  let _ := Fintype.ofFinite (Gen m)
  let _ := Fintype.ofFinite (Rel m)
  let eg : Gen m ≃ Fin m := Fintype.equivFinOfCardEq (by rw [←Nat.card_eq_fintype_card,card_gen])
  let er : Rel m ≃ Fin (m*(m+1)/2) := Fintype.equivFinOfCardEq (by rw [←Nat.card_eq_fintype_card,← twice_card_rel];simp)
  exact fun j => FreeGroup.freeGroupCongr eg (relations c (er.symm j))
noncomputable def initialIso {m : ℕ} (c : Codes 2 m) : Model c ≃* Grp (initialPresentation c) := by
  classical
  let _ := Fintype.ofFinite (Gen m)
  let _ := Fintype.ofFinite (Rel m)
  let eg : Gen m ≃ Fin m := Fintype.equivFinOfCardEq (by rw [←Nat.card_eq_fintype_card,card_gen])
  let er : Rel m ≃ Fin (m*(m+1)/2) := Fintype.equivFinOfCardEq (by rw [←Nat.card_eq_fintype_card,← twice_card_rel];simp)
  have he : Set.range (initialPresentation c) = (FreeGroup.freeGroupCongr eg) '' Set.range (relations c) := by
    ext x
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨_,⟨er.symm j,rfl⟩,rfl⟩
    · rintro ⟨_,⟨j,rfl⟩,rfl⟩
      exact ⟨er j,by change (FreeGroup.freeGroupCongr eg) (relations c (er.symm (er j)))=_; rw [er.symm_apply_apply]⟩
  change _ ≃* PresentedGroup (Set.range _)
  rw [he]
  exact PresentedGroup.equivPresentedGroup _ eg
theorem prescribed_presentation (hV : Nat.card V=2^d) (hQ : Nat.card Q=2^(d+s))
    (f : Q →* V) (hf : Function.Surjective f) (hΦ : f.ker ≤ frattini Q) :
    ∃ R : Fin (d*(d+1)/2+s*d) → FreeGroup (Fin d), Nonempty (Grp R ≃* Q) := by
  obtain ⟨c,g,hg⟩ := covered Nat.prime_two d V hV
  let _ := finite_model (p := 2) (by decide) d c
  let R := initialPresentation c
  let equiv := initialIso c
  let _ : Finite (Grp R) := Finite.of_equiv (Model c) equiv.toEquiv
  have hc : Nat.card (Model c)=2^d :=
    le_antisymm (card_model (by decide) d c) (hV ▸ Nat.card_le_card_of_surjective g hg)
  have hR : Nat.card (Grp R)=2^d := (Nat.card_congr equiv.symm.toEquiv).trans hc
  obtain ⟨a,v,hv⟩ := frattini_cover R hR (g.comp equiv.symm.toMonoidHom) (hg.comp equiv.symm.surjective) hV s hQ f hf hΦ
  let _ := run_finite R s a
  have H : Nat.card (Grp (run R a))=Nat.card Q := by
    apply le_antisymm _ (Nat.card_le_card_of_surjective v hv)
    simpa only [hR,hQ,pow_add] using run_card R s a
  let iso := MulEquiv.ofBijective v ((Nat.bijective_iff_surjective_and_card v).2 ⟨hv,H⟩)
  have h : ∃ R' : Fin (RelDim d (d*(d+1)/2) s) → FreeGroup (Fin d), Nonempty (Grp R' ≃* Q) := ⟨run R a,⟨iso⟩⟩
  rw [← rel_dim d (d*(d+1)/2) s]
  exact h
end Erdos1160.CentralLifts.Survival
end

/- ActualModelFiber -/
section
namespace Erdos1160.DescendantTree.Actual
open BinaryFactor.Elementary OrbitUp Erdos1160Growth
open Erdos1160Growth.LowerTriangularUpper (squareCore diagonalQ squares_le_frattini)
open Erdos1160.DeepJacobi (binaryThird binaryThird_map)
open Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival
variable {d s : ℕ} (R : Root d s) (B : V d →+ V d →+ V s)
theorem model_spans (hw : Nat.card (squareCore (BilinearExtension B))=2^s) :
    Submodule.span K (Set.range (diagonalQ B : V d→V s))=⊤ := by
  let _ : Finite (BilinearExtension B) := Finite.of_equiv _ (BilinearExtension.coordinateEquiv B).symm
  let W := Submodule.span K (Set.range (diagonalQ B : V d→V s))
  let incl : Multiplicative (V s) →* BilinearExtension B :=
    { toFun := fun u=>liftW B u.toAdd, map_one' := rfl, map_mul' := fun u v=>liftW_add B _ _ }
  let H := W.toAddSubgroup.toSubgroup.map incl
  have hsq : squareCore (BilinearExtension B) ≤ H := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    exact ⟨Multiplicative.ofAdd (diagonalQ B x.base),
      (Submodule.subset_span ⟨x.base,rfl⟩ : diagonalQ B x.base∈W), (square_as_fiber B x).symm⟩
  let p := BilinearExtension.projection B
  have hk : H ≤ p.ker := by rintro _ ⟨w,hw,rfl⟩;rfl
  have hc : Nat.card (BilinearExtension B)=2^(d+s) := by simp [BilinearExtension.card,V,←Nat.pow_add]
  have hc' := ker_card_of_epi Nat.prime_two hc (vectors_card d) p (base_surj B)
  have eq : squareCore (BilinearExtension B)=p.ker := Subgroup.eq_of_le_of_card_ge (hsq.trans hk) (by omega)
  apply eq_top_iff.mpr
  intro w _
  have hm : liftW B w∈H := hsq (eq.ge (show liftW B w∈p.ker from rfl))
  obtain ⟨u,hu,he⟩ := hm
  have e : u.toAdd=w := congrArg BilinearExtension.fiber he
  exact e ▸ hu
theorem descendants_congr {P Q : Type} [Group P] [Group Q] (e : P≃*Q) (m t : ℕ) :
    descendants P m t=descendants Q m t := by
  have sub {A C : Type} [Group A] [Group C] (e : A≃*C) :
      descendants A m t⊆descendants C m t := by
    rintro v ⟨G,h,⟨f,hf,hk⟩,he⟩
    refine ⟨G,h,⟨e.toMonoidHom.comp f,e.surjective.comp hf,?_⟩,he⟩
    exact fun x hx=>hk (e.injective ((show e (f x)=1 from hx).trans e.map_one.symm))
  exact Set.Subset.antisymm (sub e) (sub e.symm)
theorem root_mark (R : Root d s) : ∃π : FreeGroup (Fin d)→*R.group, Function.Surjective π := by
  obtain ⟨S,⟨e⟩⟩ := prescribed_presentation (vectors_card d) R.size R.elementary R.onto
    (R.ker_eq ▸ squares_le_frattini R.size)
  exact ⟨e.toMonoidHom.comp (PresentedGroup.mk (Set.range S)),e.surjective.comp (PresentedGroup.mk_surjective _)⟩
theorem descendants_over_model (e : BilinearExtension B≃*R.group) :
    (∀t,0 < t→(descendants R.group (d+s) t).Nonempty→0 < peakRank (diagonalQ B)) ∧
    ∀ {t Δ : ℕ}, 10000 ≤ d → s ≤ d → 1000*Δ ≤ d+1000 → 2*(s+t) ≤ d+2*Δ+1 →
      let w := t-(d/2-1000)
      let U := 2*Δ+12
      (descendants R.group (d+s) t).ncard ≤
        (d+3)^t*2^(t*(b₀ d s+(s+1)*peakRank (diagonalQ B))+(2*s+1)*w*(s+w)+50*U*(U+1)) := by
  let _ : Finite (BilinearExtension B) := Finite.of_equiv R.group e.symm.toEquiv
  have hc := (Nat.card_congr e.toEquiv).trans R.size
  have hw := Nat.card_congr (e.subgroupMap (squareCore _)).toEquiv
  change Nat.card (squareCore (BilinearExtension B))=Nat.card ((squareCore _).map e.toMonoidHom) at hw
  rw [CentralKernelCount.squareCore_map e.toMonoidHom e.surjective,R.width] at hw
  have span := model_spans B hw
  have hz : binaryThird (BilinearExtension B)=⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have h := binaryThird_map e.toMonoidHom e.surjective ⟨x,hx,rfl⟩
    rw [R.deep_trivial] at h
    exact Subgroup.mem_bot.mpr (e.injective ((Subgroup.mem_bot.mp h).trans e.map_one.symm))
  let M : Root d s := ⟨FiniteGrp.of (BilinearExtension B),hc,BilinearExtension.projection B,base_surj B,
    (squareCore_full B span).symm,hz,hw⟩
  obtain ⟨π,hπ⟩ := root_mark M
  have hbound := nucleus_peak B span π hπ (peakRank (diagonalQ B)) (fun _ h=>h.rank_le_peak)
  have heq (t : ℕ) : descendants M.group (d+s) t=descendants R.group (d+s) t := descendants_congr e _ _
  constructor
  · rintro (_|j) ht hn
    · omega
    · by_contra! h
      have h0 : nucleusRank π=0 := by rw [Nat.eq_zero_of_le_zero h,Nat.mul_zero] at hbound;exact Nat.eq_zero_of_le_zero hbound
      rw [←heq,zero_nucleus_empty M π hπ h0] at hn
      exact Set.not_nonempty_empty hn
  · intro t Δ hd hs hΔ ht
    dsimp only
    rw [←heq]
    apply (su_xia_5_6 M π hπ hd hs hΔ ht).trans
    gcongr <;> first | exact hbound | decide
end Erdos1160.DescendantTree.Actual
end

/- NonrootWideProfile -/
section
namespace Erdos1160.Paper85
open OuterExtensions DescendantTree DescendantTree.Actual
open Erdos1160Growth.LowerTriangularUpper
open OrbitUp (Classes peakRank slotsN)
open scoped Classical
private theorem strip_nat {d s t : ℕ} (h : inCentralStrip (d+s+t) d) :
    1000*roundedDelta d s t ≤ d+1000 ∧ 2*(s+t) ≤ d+2*roundedDelta d s t+1 ∧ s ≤ d := by
  unfold inCentralStrip at h
  rcases h with ⟨a,b⟩
  unfold roundedDelta
  omega
theorem strip_real {d s t : ℕ} (h : inCentralStrip (d+s+t) d) :
    -(d:ℝ)/1000≤(s:ℝ)+t-d/2 ∧ (s:ℝ)+t-d/2 ≤ d/1000 := by
  unfold inCentralStrip at h
  have lo : 1000*(3*d) ≤ 1000*(2*(d+s+t))+2*d := by omega
  have hi : 1000*(2*(d+s+t)) ≤ 1000*(3*d)+2*d := by omega
  have l : 1000*(3*(d:ℝ)) ≤ 1000*(2*(d+s+t))+2*d := by exact_mod_cast lo
  have u : 1000*(2*((d:ℝ)+s+t)) ≤ 1000*(3*d)+2*d := by exact_mod_cast hi
  constructor <;> linarith
private theorem per_orbit {d s t k : ℕ} (hd : 10000 ≤ d) (hh : inCentralStrip (d+s+t) d)
    (x : ProfileClasses (d+s+t) d s) :
    ∑ y ∈ Finset.univ.filter (fun y : ProfileClasses (d+s+t) d s=>rootOrbit y=rootOrbit x),
      Nat.card (MulAut (orderRep y.val))^k ≤
    (2^(k*d*(s+t))*(d+3)^t*2^(clippingCharge d s t)) *
      (stabilizerSize (rootOrbit x).out ^ k * 2^(t*(b₀ d s+(s+1)*peakRank (rootOrbit x).out))) := by
  let T := Finset.univ.filter (fun y : ProfileClasses (d+s+t) d s=>rootOrbit y=rootOrbit x)
  let w (y : ProfileClasses (d+s+t) d s) := Nat.card (MulAut (orderRep y.val))^k
  have weight (y) (hy : y ∈ T) : w y ≤ 2^(k*d*(s+t))*stabilizerSize (rootOrbit x).out^k := by
    simpa only [(Finset.mem_filter.mp hy).2,show d+s+t-d=s+t by omega] using orbit_weight y k
  obtain ⟨ha,hb,hc⟩ := strip_nat hh
  let M := rootModel x
  have h := (descendants_over_model M.root M.form M.model).2 hd hc ha hb
  dsimp only at h
  have fibers : T.card ≤ (d+3)^t * (2^(t*(b₀ d s+(s+1)*peakRank (rootOrbit x).out)) * 2^(clippingCharge d s t)) := by
    rw [(root_orbit_invariants x).2,←pow_add]
    apply (orbit_fiber_count (t:=t) rfl x).trans
    simpa only [clippingCharge,Nat.add_assoc,M] using h
  have total := Finset.sum_le_card_nsmul T w _ weight
  rw [nsmul_eq_mul] at total
  apply total.trans
  apply (Nat.mul_le_mul_right _ fibers).trans_eq
  ring
theorem wide_profile_real {d s t k : ℕ} (hd : threshold84 k ≤ d) (hs : 192*exponentH k ≤ s)
    (ht : 0 < t) (hh : inCentralStrip (d+s+t) d) :
    (profileMoment (d+s+t) d s k:ℝ) ≤ (2:ℝ)^(k*d*(s+t))*(d+3)^t*2^(clippingCharge d s t)*
      2^(((s:ℝ)+t)*slotsN d-d^2-((s:ℝ)+t)^2-(d:ℝ)^2/25) := by
  classical
  let T := (Finset.univ : Finset (ProfileClasses (d+s+t) d s)).image rootOrbit
  let price (o : Classes d s) := stabilizerSize o.out^k * 2^(t*(b₀ d s+(s+1)*peakRank o.out))
  let A := 2^(k*d*(s+t))*(d+3)^t*2^(clippingCharge d s t)
  have d0 : 10000 ≤ d := (le_max_left ..).trans hd
  have per (o : Classes d s) (ho : o∈T) :
      ∑y∈Finset.univ.filter (fun y : ProfileClasses (d+s+t) d s=>rootOrbit y=o),
        Nat.card (MulAut (orderRep y.val))^k ≤ A*price o := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp ho
    exact per_orbit d0 hh x
  have sum := Finset.sum_le_sum per
  rw [Finset.sum_fiberwise_of_maps_to (fun x hx=>Finset.mem_image_of_mem rootOrbit hx),←Finset.mul_sum] at sum
  change profileMoment (d+s+t) d s k ≤ A*∑o∈T,price o at sum
  have positive (o) (ho:o∈T) : 0 < peakRank o.out := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp ho
    rw [(root_orbit_invariants x).2]
    let M := rootModel x
    exact (descendants_over_model M.root M.form M.model).1 t ht ⟨x.val.val,fiber_in_tree rfl x x rfl⟩
  have z : (s:ℝ)+t ≤ 51*(d:ℝ)/100 := by linarith [(strip_real hh).2,show (0:ℝ) ≤ d by positivity]
  have orbits := su_xia_8_4_orbits T positive hd hs z
  have sd := (strip_nat hh).2.2
  have b : (b₀ d s:ℝ)=(slotsN d:ℝ)-s := by
    have ge : s ≤ d*(d+1)/2 := sd.trans (by rw [←coeff_identity];omega)
    rw [b₀,Nat.cast_sub ge,←coeff_identity]
    unfold slotsN
    push_cast
    ring
  have each (o : Classes d s) : (price o:ℝ) =
      (stabilizerSize o.out:ℝ)^k*2^((t:ℝ)*(slotsN d-s+(s+1)*peakRank o.out)) := by
    dsimp only [price]
    rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat,
      ←Real.rpow_natCast (2:ℝ) (t*_),Nat.cast_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_add,Nat.cast_one,b]
  have charge : (A:ℝ)=(2:ℝ)^(k*d*(s+t))*(d+3)^t*2^(clippingCharge d s t) := by
    dsimp only [A]
    push_cast
    rfl
  have total : (profileMoment (d+s+t) d s k:ℝ) ≤ (A:ℝ)*(∑o∈T,(price o:ℝ)) := by exact_mod_cast sum
  rw [charge] at total
  apply total.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [each] using orbits
end Erdos1160.Paper85
end

/- NonrootProfileCover -/
section
namespace Erdos1160.Paper85
open OuterExtensions DescendantTree DescendantTree.Actual
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160Growth Erdos1160Growth.LowerTriangularUpper
open scoped Classical
theorem positive_profile {m : ℕ} (c : ClassOf (2^m)) (pos : binaryThird (orderRep c)≠⊥) :
    ∃d s t, d=generatorRank c ∧ 0 < t ∧ d+s+t=m ∧
    (frattini (orderRep c)).index=2^d ∧
    Nat.card (frattini (orderRep c ⧸ binaryThird (orderRep c)))=2^s := by
  let P := orderRep c
  let K := binaryThird P
  let Y := P ⧸ K
  have hp := IsPGroup.of_card (rep_size c)
  obtain ⟨d,hd⟩ := (hp.to_quotient (frattini P)).exists_card_eq
  change (frattini P).index=2^d at hd
  obtain ⟨s,hs⟩ := ((hp.to_quotient K).to_subgroup (frattini Y)).exists_card_eq
  obtain ⟨t,ht⟩ := (hp.to_subgroup K).exists_card_eq
  obtain ⟨_,_,_,_,_,B,rfl,⟨e⟩⟩ := root_form_automorphism_model (rep_size c) hd hs
  have cardY : Nat.card Y=2^(d+s) := by
    rw [←Nat.card_congr e.toEquiv,BilinearExtension.card,pow_add,Nat.card_fun,Nat.card_fin,
      Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  change Nat.card K=2^t at ht
  have nK := K.one_lt_card_iff_ne_bot.mpr pos
  have sum := K.card_eq_card_quotient_mul_card_subgroup
  change Nat.card P=Nat.card Y*Nat.card K at sum
  rw [rep_size c,cardY,ht,←pow_add] at sum
  exact ⟨d,s,t,by unfold generatorRank;rw [hd,Nat.log_pow (by decide : 1 < 2)],
    Nat.pos_of_ne_zero (by rintro rfl;rw [ht] at nK;norm_num at nK),
    (Nat.pow_right_injective (by decide : 1 < 2) sum).symm,hd,hs⟩
private def memberAt {m : ℕ} (d s : ℕ) (c : ClassOf (2^m)) : Prop :=
  (frattini (orderRep c)).index=2^d ∧ Nat.card (frattini (orderRep c ⧸ binaryThird (orderRep c)))=2^s
private theorem moment_eq_raw (m d s k : ℕ) :
    profileMoment m d s k = ∑ c : ClassOf (2^m),if memberAt d s c then Nat.card (MulAut (orderRep c))^k else 0 := by
  classical
  let w (c : ClassOf (2^m)) := Nat.card (MulAut (orderRep c))^k
  let e : ProfileClasses m d s ≃ ↑(Finset.univ.filter (memberAt d s)) :=
    Equiv.subtypeEquivRight (fun c=>by simp [memberAt])
  have eq := Equiv.sum_comp e (fun z : ↑(Finset.univ.filter (memberAt d s))=>w z.val)
  change profileMoment m d s k=_ at eq
  rw [eq,Finset.sum_coe_sort,Finset.sum_filter]
private def active (m d s S : ℕ) : Prop := S ≤ s ∧ d+s < m ∧ inCentralStrip m d
noncomputable def wideCell (m d s S k : ℕ) : ℕ :=
  if active m d s S then profileMoment m d s k else 0
noncomputable def wideMoment (m S k : ℕ) : ℕ :=
  ∑i : Fin (m+1)×Fin (m+1), wideCell m i.1.val i.2.val S k
private theorem wideCell_eq (m d s S k : ℕ) :
    wideCell m d s S k = ∑c : ClassOf (2^m),
    if active m d s S ∧ memberAt d s c then Nat.card (MulAut (orderRep c))^k else 0 := by
  classical
  by_cases h : active m d s S
  · simp [wideCell,h,moment_eq_raw]
  · simp [wideCell,h]
theorem cells_upper {m S k : ℕ} (bound : ∀d s, active m d s S →
    (profileMoment m d s k)^27*2^(12*m^2) ≤ 2^(2*m^3+6*k*m^2)) :
    (wideMoment m S k)^27*2^(12*m^2) ≤ 2^(2*m^3+6*k*m^2+54*m) := by
  classical
  let f (i : Fin (m+1) × Fin (m+1)) := wideCell m i.1.val i.2.val S k
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ f (Finset.univ_nonempty)
  have cap : (f i)^27*2^(12*m^2) ≤ 2^(2*m^3+6*k*m^2) := by
    unfold f wideCell
    split_ifs with h
    · exact bound _ _ h
    · simp
  have s := Finset.sum_le_card_nsmul Finset.univ f (f i) hi
  rw [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul] at s
  have n : m+1 ≤ 2^m := Nat.lt_two_pow_self
  have total : wideMoment m S k ≤ 2^(m+m)*f i :=
    s.trans (Nat.mul_le_mul_right _ (by rw [pow_add];exact Nat.mul_le_mul n n))
  apply (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left total 27)).trans
  rw [mul_pow,←pow_mul,Nat.mul_assoc]
  apply (Nat.mul_le_mul_left _ cap).trans_eq
  rw [←pow_add]
  congr 1
  ring
end Erdos1160.Paper85
namespace Erdos1160.Paper85
open OuterExtensions DescendantTree DescendantTree.Actual
open Erdos1160.DeepJacobi (binaryThird)
open scoped Classical
theorem wide_subset_le {m S : ℕ} (C : Set (ClassOf (2^m)))
    (hc : ∀c∈C, binaryThird (orderRep c)≠⊥ ∧ inCentralStrip m (generatorRank c) ∧
      2^S ≤ Nat.card (frattini (orderRep c ⧸ binaryThird (orderRep c)))) :
    C.ncard ≤ wideMoment m S 0 := by
  classical
  have sum : C.ncard=∑c : ClassOf (2^m),if c∈C then 1 else 0 := by
    rw [Finset.sum_boole,Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp
  rw [sum,wideMoment]
  simp_rw [wideCell_eq,pow_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c _
  split_ifs with h
  · obtain ⟨root,strip,large⟩ := hc c h
    obtain ⟨d,s,t,hd,ht,eq,idx,width⟩ := positive_profile c root
    have hs := (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp (large.trans_eq width)
    let i : Fin (m+1)×Fin (m+1) := (⟨d,by omega⟩,⟨s,by omega⟩)
    have hi : active m d s S ∧ memberAt d s c := ⟨⟨hs,by omega,hd ▸ strip⟩,idx,width⟩
    have hh := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j : Fin (m+1)×Fin (m+1)=>if active m j.1.val j.2.val S ∧ memberAt j.1.val j.2.val c
        then (1:ℕ) else 0) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    change (if active m d s S ∧ memberAt d s c then _ else _)≤_ at hh
    rwa [if_pos hi] at hh
  · exact Nat.zero_le _
end Erdos1160.Paper85
end

/- StripMargin -/
section
namespace Erdos1160.DescendantTree
private theorem sq_le_two_pow {n : ℕ} (h : 4 ≤ n) : n^2 ≤ 2^n := by
  induction n,h using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ 2]
    nlinarith only [ih,mul_nonneg (show 0 ≤ n-4 from Nat.zero_le _) (show 0 ≤ n from Nat.zero_le _),
      show n=4+(n-4) from by omega, sq_nonneg (n-4),hn]
theorem log_charge_small (Q d : ℕ) (hd : 2^(4*Q+4) ≤ d) :
    Q*(Nat.log 2 (d+3)+1) ≤ d := by
  let k := Nat.log 2 (d+3)
  have hk : 4*Q+4 ≤ k := Nat.le_log_of_pow_le (by decide) (hd.trans (Nat.le_add_right ..))
  have hpow : 2^k ≤ d+3 := Nat.pow_log_le_self _ (by omega)
  have hsq := sq_le_two_pow (show 4 ≤ k by omega)
  have hmul := Nat.mul_le_mul_right k hk
  have d4 : 4 ≤ d := (show 4 ≤ 2^(4*Q+4) from (show 4 ≤ 2^4 by decide).trans
    (Nat.pow_le_pow_right (by decide) (by omega))).trans hd
  nlinarith only [hpow,hsq,hmul,hk,d4]
theorem strip_margin (q k : ℕ) (hq : 0 < q) :
    ∃D : ℕ, ∀d s t : ℕ,D ≤ d →
      -(d:ℝ)/1000 ≤ (s:ℝ)+t-d/2 → (s:ℝ)+t-d/2 ≤ d/1000 →
      rootExponent d ((s:ℝ)+t)+(clippingCharge d s t:ℝ)+k*d*((s:ℝ)+t)
        +(t:ℝ)*(Nat.log 2 (d+3)+1:ℕ) ≤
      leadingExponent ((d:ℝ)+s+t)+(2*(k:ℝ)/9)*((d:ℝ)+s+t)^2 + (d:ℝ)^2/q := by
  let H := 1000000000000+4*q*(k+2)^2+4*q*10000000000
  refine ⟨max H (2^(4*(4*q)+4)),?_⟩
  intro d s t hd hl hu
  have hH : H ≤ d := (le_max_left ..).trans hd
  have hD : 1000000000000 ≤ d := by dsimp [H] at hH;omega
  have hk : 4*q*(k+2)^2 ≤ d := by dsimp [H] at hH;omega
  have hc : 4*q*10000000000 ≤ d := by dsimp [H] at hH;omega
  have ht : (t:ℝ) ≤ d := by linarith [show (0:ℝ) ≤ s by positivity]
  have logBd := log_charge_small (4*q) d ((le_max_right ..).trans hd)
  have hlog : (4*(q:ℝ))*(Nat.log 2 (d+3)+1:ℕ) ≤ d := by exact_mod_cast logBd
  have hkr : 4*(q:ℝ)*(k+2)^2 ≤ d := by exact_mod_cast hk
  have hcr : 4*(q:ℝ)*10000000000 ≤ d := by exact_mod_cast hc
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hlin := strip_optimization d s t k hD hl hu
  have hk2 : (1+(k:ℝ)/3)^2 ≤ (k+2)^2 := by
    have hn : (0:ℝ) ≤ k := by positivity
    nlinarith [sq_nonneg (k:ℝ)]
  have hrem : (1+(k:ℝ)/3)^2*d+10000000000+(t:ℝ)*(Nat.log 2 (d+3)+1:ℕ) ≤ (d:ℝ)^2/q := by
    apply (le_div_iff₀ hq').mpr
    have hd0 : (0:ℝ) ≤ d := by positivity
    have ht0 : (0:ℝ) ≤ t := by positivity
    have h₁ := mul_le_mul_of_nonneg_right hkr hd0
    have h₂ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk2 hd0) hq'.le
    have h₃ := mul_le_mul_of_nonneg_right hlog ht0
    have h₄ := mul_le_mul_of_nonneg_left ht hd0
    have h₅ := mul_le_mul_of_nonneg_left hdr hd0
    nlinarith only [h₁,h₂,h₃,h₄,h₅,hcr,sq_nonneg (d:ℝ)]
  linarith only [hlin,hrem]
end Erdos1160.DescendantTree
end

/- ProfileScalar85 -/
section
namespace Erdos1160.DescendantTree
open OrbitUp
theorem central_profile_scalar (k : ℕ) : ∃D, ∀d s t N : ℕ, D ≤ d →
    -(d:ℝ)/1000≤(s:ℝ)+t-d/2 → (s:ℝ)+t-d/2 ≤ d/1000 →
    (N:ℝ) ≤ (2:ℝ)^(k*d*(s+t))*(d+3:ℝ)^t*2^(clippingCharge d s t)*
      2^(((s:ℝ)+t)*slotsN d-d^2-((s:ℝ)+t)^2-(d:ℝ)^2/25) →
    N^27*2^(12*(d+s+t)^2) ≤ 2^(2*(d+s+t)^3+6*k*(d+s+t)^2) := by
  obtain ⟨D,hD⟩ := strip_margin 25 k (by decide)
  refine ⟨D,fun d s t N hd hl hu hN=>?_⟩
  let L := Nat.log 2 (d+3)+1
  let z : ℝ := s+t
  let m : ℝ := d+s+t
  have hdL : (d+3:ℝ) ≤ (2:ℝ)^L := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (d+3)).le
  have htree := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ d+3) hdL t
  have h0 := hN.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htree (by positivity : (0:ℝ) ≤ 2^(k*d*(s+t)))) (by positivity)) (by positivity))
  have hslots : (slotsN d : ℝ)=(d:ℝ)*(d+1)/2 := by
    have h : 2*(slotsN d:ℝ)=(d:ℝ)^2+d := by exact_mod_cast twice_slots d
    linarith
  have hM := hD d s t hd hl hu
  change rootExponent d z + _ + (k:ℝ)*d*z + (t:ℝ)*L ≤ leadingExponent m + _ + _ at hM
  let A : ℝ := (2*m^3+6*k*m^2-12*m^2)/27
  have hA : (k:ℝ)*d*z+(L:ℝ)*t+(clippingCharge d s t:ℝ)+(z*slotsN d-d^2-z^2-(d:ℝ)^2/25) ≤ A := by
    rw [hslots]
    unfold rootExponent leadingExponent at hM
    dsimp only [A,m] at *
    linear_combination (norm := (ring_nf <;> norm_num)) hM
  have hexp : (N:ℝ)≤(2:ℝ)^A := by
    apply h0.trans
    rw [←pow_mul,←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_natCast,
      ←Real.rpow_add (by norm_num : (0:ℝ) < 2),←Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ←Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    push_cast
    simpa only [z,slotsN,Nat.cast_add] using hA
  have cub : (N:ℝ)^27*(2:ℝ)^(12*(d+s+t)^2) ≤ (2:ℝ)^(2*(d+s+t)^3+6*k*(d+s+t)^2) := by
    apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hexp 27) (by positivity)).trans
    rw [← Real.rpow_natCast (2^A),← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ) < 2),← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    push_cast
    dsimp [A,m]
    linarith
  exact_mod_cast cub
end Erdos1160.DescendantTree
end

/- CentralNonrootMoment85 -/
section
namespace Erdos1160.Paper85
open OuterExtensions DescendantTree Filter Paper89
theorem wide_moment_envelope (k : ℕ) : envelope k (fun m=>wideMoment m (192*exponentH k) k) := by
  obtain ⟨D,scalar⟩ := central_profile_scalar k
  let H := max D (threshold84 k)
  refine ⟨54,eventually_atTop.mpr ⟨2*H,fun m hm=>?_⟩⟩
  apply cells_upper
  intro d s cell
  rcases cell with ⟨hs,hpos,hstrip⟩
  let t := m-(d+s)
  have eq : d+s+t=m := by dsimp [t];omega
  have hd : H ≤ d := by
    have hi := hstrip.1
    omega
  have scalar' := scalar d s t (profileMoment (d+s+t) d s k) ((le_max_left ..).trans hd)
  have st : inCentralStrip (d+s+t) d := eq ▸ hstrip
  have loc := wide_profile_real ((le_max_right ..).trans hd) hs (show 0 < t by dsimp [t];omega) st
  simpa only [eq] using scalar' (strip_real st).1 (strip_real st).2 loc
end Erdos1160.Paper85
end

/- MomentWideLeaf -/
section
namespace Erdos1160.Paper85
open Filter OuterExtensions DescendantTree.Actual
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
theorem sigma_card_sum {X : Type*} [Fintype X] (B : X → Type*) [∀ x, Finite (B x)] (P : X → Prop)
    [DecidablePred P] (k : ℕ) : Nat.card {u : (x : X) × (Fin k → B x) // P u.1} =
      ∑ x, if P x then Nat.card (B x)^k else 0 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeSigmaEquiv _ _),Nat.card_sigma]
  simp only [Nat.card_fun,Nat.card_fin]
  rw [Finset.sum_ite,Finset.sum_const_zero,add_zero]
  exact (Finset.sum_subtype (Finset.univ.filter P) (fun x=>by simp) (fun x=>Nat.card (B x)^k)).symm
open scoped Classical in
theorem moment_subset_le {m S k : ℕ} (P : ClassOf (2^m) → Prop)
    (hc : ∀c, P c → binaryThird (orderRep c)≠⊥ ∧ inCentralStrip m (generatorRank c) ∧
      2^S ≤ Nat.card (frattini (orderRep c ⧸ binaryThird (orderRep c)))) :
    Nat.card {u : (c : ClassOf (2^m)) × (Fin k → MulAut (orderRep c)) // P u.1} ≤ wideMoment m S k := by
  have _ (c : ClassOf (2^m)) : Finite (MulAut (orderRep c)) :=
    Finite.of_injective (fun f : MulAut (orderRep c)=>(f : orderRep c → orderRep c)) DFunLike.coe_injective
  rw [sigma_card_sum (fun c=>MulAut (orderRep c)) P k,wideMoment]
  simp_rw [wideCell_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c _
  split_ifs with h
  · obtain ⟨root,strip,large⟩ := hc c h
    obtain ⟨d,s,t,hd,ht,eq,idx,width⟩ := positive_profile c root
    have hs := (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp (large.trans_eq width)
    let i : Fin (m+1)×Fin (m+1) := (⟨d,by omega⟩,⟨s,by omega⟩)
    have hi : active m d s S ∧ memberAt d s c := ⟨⟨hs,by omega,hd ▸ strip⟩,idx,width⟩
    have hh := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j : Fin (m+1)×Fin (m+1)=>if active m j.1.val j.2.val S ∧ memberAt j.1.val j.2.val c
        then Nat.card (MulAut (orderRep c))^k else 0) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    change (if active m d s S ∧ memberAt d s c then _ else _)≤_ at hh
    rwa [if_pos hi] at hh
  · exact Nat.zero_le _
theorem moment_large_leaf : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1_H2_R2.H2 := by
  classical
  intro t
  obtain ⟨B,cap⟩ := wide_moment_envelope t
  obtain ⟨M,hM⟩ := eventually_atTop.mp cap
  let S : ℕ := 192*((t+1)*1000)
  let W (b : ℕ) : ℕ := wideMoment b S t
  let C : ℕ := B+∑b ∈ Finset.range M,(27*W b+8*b^2)
  refine ⟨C,fun b=>?_⟩
  let P (c : ClassOf (2^b)) : Prop :=
    let G : FiniteGrp.{0} := orderRep c
    let d := Nat.log 2 (frattini G).index
    let strip := 1000*(2*b-3*d) ≤ 2*d ∧ 1000*(3*d-2*b) ≤ 2*d
    let F := Subgroup.closure (Set.range fun x : G => x*x)
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    strip ∧ K≠⊥ ∧ 2^(192*((t+1)*1000)) * Nat.card K ≤ Nat.card F
  have cnt : Nat.card {u : (c : ClassOf (2^b)) × (Fin t → MulAut (orderRep c)) // P u.1} ≤ W b := by
    apply moment_subset_le
    intro c hc
    obtain ⟨strip,root,width⟩ := hc
    obtain ⟨r,hr⟩ := ((IsPGroup.of_card (rep_size c)).to_quotient (binaryThird (orderRep c))).exists_card_eq
    refine ⟨root,strip,?_⟩
    rw [frattini_eq_squareCore hr]
    change 2^S*Nat.card (binaryThird (orderRep c)) ≤ Nat.card (squareCore (orderRep c)) at width
    rw [squareCore_card_product] at width
    exact Nat.le_of_mul_le_mul_right width Nat.card_pos
  change Nat.card {u : (c : ClassOf (2^b)) × (Fin t → MulAut (orderRep c)) // P u.1}^27*2^(8*b^2) ≤
    2^(2*b^3+6*t*b^2+C*(b+1))
  by_cases hb : M ≤ b
  · have bound := hM b hb
    calc _ ≤ (W b)^27*2^(12*b^2) := Nat.mul_le_mul (Nat.pow_le_pow_left cnt 27)
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide)))
      _ ≤ 2^(2*b^3+6*t*b^2+B*b) := bound
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left
          (Nat.mul_le_mul (Nat.le_add_right B _) (Nat.le_succ b)) _)
  · have hW : (W b)^27 ≤ 2^(27*W b) := by
      rw [pow_mul']
      exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 27
    have hs : 27*W b+8*b^2 ≤ C := (Finset.single_le_sum (f:=fun b=>27*W b+8*b^2)
      (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr (by omega))).trans (Nat.le_add_left _ _)
    calc _ ≤ 2^(27*W b)*2^(8*b^2) := Nat.mul_le_mul_right _ ((Nat.pow_le_pow_left cnt 27).trans hW)
      _ = 2^(27*W b+8*b^2) := (pow_add ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (hs.trans ((Nat.le_mul_of_pos_right C
          (Nat.succ_pos b)).trans (Nat.le_add_left _ _)))
end Erdos1160.Paper85
end

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1_H2_R2.H2 :=
  Erdos1160.Paper85.moment_large_leaf
