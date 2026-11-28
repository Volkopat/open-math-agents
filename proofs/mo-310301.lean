import OMAStatements.S_mo_310301

open scoped BigOperators

namespace OMA.MO310301

variable {F : Type*} [Field F]

private def hyperbolaEquiv (h₂ : (2 : F) ≠ 0) :
    Fˣ ≃ (x : F) × {y : F // y ^ 2 = 1 + x ^ 2} where
  toFun t := by
    refine ⟨((↑t : F)⁻¹ - ↑t) / 2, ((↑t : F)⁻¹ + ↑t) / 2, ?_⟩
    have hunit : (↑t : F)⁻¹ * ↑t = 1 := inv_mul_cancel₀ t.ne_zero
    calc
      (((↑t : F)⁻¹ + ↑t) / 2) ^ 2 =
          ((↑t : F)⁻¹ * ↑t) + (((↑t : F)⁻¹ - ↑t) / 2) ^ 2 := by
        field_simp
        ring
      _ = _ := by rw [hunit]
  invFun xy := by
    have h : (xy.2.val - xy.1) * (xy.2.val + xy.1) = 1 := by
      linear_combination xy.2.property
    exact Units.mk0 _ (left_ne_zero_of_mul (h ▸ one_ne_zero))
  left_inv t := by
    apply Units.ext
    change (((↑t : F)⁻¹ + ↑t) / 2) - (((↑t : F)⁻¹ - ↑t) / 2) = ↑t
    field_simp
    ring
  right_inv xy := by
    rcases xy with ⟨x, y, hy⟩
    have h : (y - x) * (y + x) = 1 := by linear_combination hy
    have hinv : (y - x)⁻¹ = y + x := (eq_inv_of_mul_eq_one_right h).symm
    have hx : (((y - x)⁻¹ - (y - x)) / 2) = x := by
      rw [hinv]
      field_simp
      ring
    have hy' : (((y - x)⁻¹ + (y - x)) / 2) = y := by
      rw [hinv]
      field_simp
      ring
    exact Sigma.subtype_ext hx hy'

/-- Counting the hyperbola using the nonzero parameter y - x gives the character sum. -/
theorem quadraticChar_sum_one_add_sq [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2) :
    (∑ x : F, quadraticChar F (1 + x ^ 2)) = -1 := by
  classical
  have h₂ : (2 : F) ≠ 0 := by
    intro h
    exact hF (CharP.ringChar_of_prime_eq_zero (by decide : Nat.Prime 2) h)
  have hc := Fintype.card_congr (hyperbolaEquiv (F := F) h₂)
  rw [Fintype.card_units, Fintype.card_sigma] at hc
  have hcast : ((Fintype.card F - 1 : ℕ) : ℤ) =
      ∑ x : F, (quadraticChar F (1 + x ^ 2) + 1) := by
    rw [hc, Nat.cast_sum]
    congr 1
    ext x
    rw [Fintype.card_of_subtype {y : F | y ^ 2 = 1 + x ^ 2}.toFinset (by simp)]
    exact quadraticChar_card_sqrts hF (1 + x ^ 2)
  rw [Nat.cast_sub (Fintype.card_pos : 1 ≤ Fintype.card F),
    Finset.sum_add_distrib] at hcast
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.cast_one] at hcast
  omega

end OMA.MO310301

open scoped BigOperators

namespace OMA.MO310301

/-- Modulo two the unreplaced matrix is the difference between the all-ones matrix and an
involutive permutation. Its square is the identity, and its rows sum to the replacement row. -/
theorem odd_det_updateRow {G : Type*} [Fintype G] [DecidableEq G]
    (M : Matrix G G ℤ) (hG : Even (Fintype.card G)) (P : Equiv.Perm G)
    (hP : Function.Involutive P) (i₀ : G) (ψ : G → ℤ)
    (hM : ∀ i j, (M i j : ZMod 2) = if i = P j then 0 else 1)
    (hψ : ∀ j, (ψ j : ZMod 2) = 1) :
    Odd (M.updateRow i₀ ψ).det := by
  let J : Matrix G G (ZMod 2) := fun _ _ => 1
  let W : Matrix G G (ZMod 2) := fun i j => if i = P j then 1 else 0
  let C := Int.castRingHom (ZMod 2)
  have hCW : C.mapMatrix M = J - W := by
    ext i j
    change (M i j : ZMod 2) = 1 - (if i = P j then 1 else 0)
    by_cases hij : i = P j <;> simp [hM, hij]
  have hJJ : J * J = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    simpa [J] using hG.natCast_zmod_two
  have hJW : J * W = J := by
    ext i j
    rw [Matrix.mul_apply]
    simp [J, W]
  have hWP (i j : G) : (i = P j) ↔ j = P i := by
    constructor
    · intro h
      rw [h, hP j]
    · intro h
      rw [h, hP i]
  have hWJ : W * J = J := by
    ext i j
    rw [Matrix.mul_apply]
    simp [J, W, hWP i]
  have hWW : W * W = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp [W, mul_ite, hP j, Matrix.one_apply]
  have hsq : C.mapMatrix M * C.mapMatrix M = 1 := by
    rw [hCW, sub_mul, mul_sub, mul_sub, hJJ, hJW, hWJ, hWW]
    ext i j
    change (0 : ZMod 2) - 1 - (1 - (1 : Matrix G G (ZMod 2)) i j) = (1 : Matrix G G (ZMod 2)) i j
    rw [Matrix.one_apply]
    split <;> decide
  have hdet : (C.mapMatrix M).det ≠ 0 := by
    intro hz
    have hdetOfSq := congr_arg Matrix.det hsq
    rw [Matrix.det_mul, Matrix.det_one, hz, zero_mul] at hdetOfSq
    exact zero_ne_one hdetOfSq
  have hsum : (∑ k : G, (1 : ZMod 2) • (C.mapMatrix M) k) = fun _ => (1 : ZMod 2) := by
    funext j
    rw [hCW, Finset.sum_apply]
    simp_rw [one_smul, Matrix.sub_apply]
    simp [J, W, Finset.sum_sub_distrib, hG.natCast_zmod_two, show -(1 : ZMod 2) = 1 by decide]
  have hmap : C.mapMatrix (M.updateRow i₀ ψ) =
      (C.mapMatrix M).updateRow i₀ (fun _ => 1) := by
    ext i j
    by_cases hi : i = i₀ <;> simp [C, Matrix.updateRow_apply, hi, hψ]
  apply Int.not_even_iff_odd.mp
  intro he
  have hCast := he.intCast_zmod_two
  change C (M.updateRow i₀ ψ).det = 0 at hCast
  rw [C.map_det, hmap, ← hsum, Matrix.det_updateRow_sum, one_smul] at hCast
  exact hdet hCast

end OMA.MO310301

namespace SunHalfReps

open Finset

lemma sum_zmod_half {p : ℕ} [NeZero p] (hodd : p % 2 = 1)
    (f : ZMod p → ℤ) (hf : ∀ x, f (-x) = f x) :
    (∑ x : ZMod p, f x) = f 0 + 2 * ∑ i : Fin ((p-1)/2), f ((i.val : ZMod p)+1) := by
  let m := (p-1)/2
  have hp : p = (1+m)+m := by dsimp [m]; omega
  have eqCast (i : Fin p) : ZMod.finEquiv p i = (i.val : ZMod p) := by
    rw [← ZMod.natCast_zmod_val (ZMod.finEquiv p i)]
    congr 1
    cases p with
    | zero => exact i.elim0
    | succ p => rfl
  have hsum : (∑ x : ZMod p, f x) = ∑ j ∈ range p, f (j : ZMod p) := by
    calc
      _ = ∑ i : Fin p, f (ZMod.finEquiv p i) := ((ZMod.finEquiv p).toEquiv.sum_comp f).symm
      _ = ∑ i : Fin p, f (i.val : ZMod p) := by simp only [eqCast]
      _ = _ := Fin.sum_univ_eq_sum_range (fun j : ℕ => f (j : ZMod p)) p
  have hupper :
      (∑ j ∈ range m, f (((1+m)+j : ℕ) : ZMod p)) =
        ∑ j ∈ range m, f ((j+1 : ℕ) : ZMod p) := by
    calc
      _ = ∑ j ∈ range m, f ((m-1-j+1 : ℕ) : ZMod p) := by
        apply sum_congr rfl
        intro j hj
        have hj' : j < m := mem_range.mp hj
        have e : (((1+m)+j : ℕ) : ZMod p) = -((m-1-j+1 : ℕ) : ZMod p) := by
          apply eq_neg_iff_add_eq_zero.mpr
          rw [←Nat.cast_add, show (1+m)+j+(m-1-j+1)=p by omega, ZMod.natCast_self]
        rw [e,hf]
      _ = _ := sum_range_reflect (fun j : ℕ => f ((j+1 : ℕ) : ZMod p)) m
  have rangeEq : range p = range ((1+m)+m) := by rw [←hp]
  have hlower :
      (∑ j ∈ range (1+m), f (j : ZMod p)) =
        (∑ j ∈ range m, f ((j+1 : ℕ) : ZMod p)) + f 0 := by
    rw [add_comm 1 m, sum_range_succ']
    simp [add_comm]
  rw [hsum,rangeEq,sum_range_add,hupper,hlower]
  have he :
      (∑ i : Fin m, f ((i.val : ZMod p)+1)) =
        ∑ j ∈ range m, f ((j+1 : ℕ) : ZMod p) := by
    simpa using Fin.sum_univ_eq_sum_range (fun j : ℕ => f ((j+1 : ℕ) : ZMod p)) m
  rw [←he]
  change (_ + f 0) + _ = f 0 + 2 * (∑ i : Fin m, f ((i.val : ZMod p)+1))
  ring

/-- The least positive representatives on one side of the negation pairing. -/
def halfRep {p : ℕ} (i : Fin ((p-1)/2)) : ZMod p := (i.val : ZMod p)+1

private lemma halfRep_val {p : ℕ} (hodd : p % 2 = 1)
    (i : Fin ((p-1)/2)) : (halfRep i).val = i.val+1 := by
  rw [halfRep,←Nat.cast_succ]
  exact ZMod.val_natCast_of_lt (by have := i.isLt; omega)

lemma halfRep_ne_zero {p : ℕ} (hodd : p % 2 = 1) (i : Fin ((p-1)/2)) :
    halfRep i ≠ 0 := by
  intro h
  have e := congrArg ZMod.val h
  rw [halfRep_val hodd,ZMod.val_zero] at e
  omega

lemma halfSq_injective {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1) :
    Function.Injective (fun i : Fin ((p-1)/2) => (halfRep i)^2) := by
  intro i j h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with hpos | hneg
  · apply Fin.ext
    have he := congrArg ZMod.val hpos
    rw [halfRep_val hodd,halfRep_val hodd] at he
    omega
  · exfalso
    have hn : halfRep i + halfRep j = (0 : ZMod p) := eq_neg_iff_add_eq_zero.mp hneg
    rw [halfRep,halfRep,←Nat.cast_succ,←Nat.cast_succ,←Nat.cast_add] at hn
    have hlt : i.val+1+(j.val+1) < p := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    have he := congrArg ZMod.val hn
    rw [ZMod.val_natCast_of_lt hlt,ZMod.val_zero] at he
    omega

private lemma exists_halfRep_or_neg {p : ℕ} [NeZero p] (hodd : p % 2 = 1)
    {x : ZMod p} (hx : x ≠ 0) :
    ∃ i : Fin ((p-1)/2), halfRep i = x ∨ halfRep i = -x := by
  have hlt := ZMod.val_lt x
  have hpos : 0 < x.val := by
    by_contra! h
    have e : x.val=0 := by omega
    exact hx (by rw [← ZMod.natCast_zmod_val x,e,Nat.cast_zero])
  by_cases h : x.val ≤ (p-1)/2
  · refine ⟨⟨x.val-1,by omega⟩,Or.inl ?_⟩
    change (((x.val-1 : ℕ) : ZMod p)+1) = x
    rw [←Nat.cast_succ,show (x.val-1).succ=x.val by omega,ZMod.natCast_zmod_val]
  · have : NeZero x := ⟨hx⟩
    have e := ZMod.val_neg_of_ne_zero x
    refine ⟨⟨p-x.val-1,by omega⟩,Or.inr ?_⟩
    change (((p-x.val-1 : ℕ) : ZMod p)+1) = -x
    rw [←Nat.cast_succ,show (p-x.val-1).succ=(-x).val by omega,ZMod.natCast_zmod_val]

/-- Squaring the half representatives parametrizes the nonzero square residues. -/
noncomputable def halfSqEquiv {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1) :
    Fin ((p-1)/2) ≃ {z : ZMod p // z ≠ 0 ∧ IsSquare z} :=
  Equiv.ofBijective
    (fun i => ⟨(halfRep i)^2,pow_ne_zero _ (halfRep_ne_zero hodd i),
      (isSquare_iff_exists_sq _).mpr ⟨halfRep i,rfl⟩⟩)
    ⟨fun _ _ he => halfSq_injective hodd (congrArg Subtype.val he),by
      rintro ⟨z,hz,hs⟩
      obtain ⟨x,hx⟩ := hs.exists_sq
      have hx0 : x ≠ 0 := by
        intro h
        exact hz (by rw [hx,h]; simp)
      obtain ⟨i,hi|hi⟩ := exists_halfRep_or_neg hodd hx0
      · refine ⟨i,Subtype.ext ?_⟩
        change (halfRep i)^2 = z
        rw [hi,←hx]
      · refine ⟨i,Subtype.ext ?_⟩
        change (halfRep i)^2 = z
        rw [hi,neg_sq,←hx]⟩

end SunHalfReps

namespace SunHalfReps

/-- The multiplicative subgroup of nonzero squares. -/
def squareUnits (p : ℕ) [Fact p.Prime] : Subgroup (ZMod p)ˣ :=
  (powMonoidHom (α := (ZMod p)ˣ) 2).range

noncomputable instance squareUnitsFintype (p : ℕ) [Fact p.Prime] : Fintype (squareUnits p) :=
  Fintype.ofFinite _

private def toSquare {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) : squareUnits p :=
  ⟨u^2,⟨u,rfl⟩⟩

private def squareRep {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1)
    (i : Fin ((p-1)/2)) : squareUnits p :=
  toSquare (Units.mk0 (halfRep i) (halfRep_ne_zero hodd i))

private lemma squareRep_val {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1)
    (i : Fin ((p-1)/2)) : ((squareRep hodd i).val : ZMod p) = (halfRep i)^2 := by
  simp [squareRep,toSquare]

private lemma squareRep_bijective {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1) :
    Function.Bijective (squareRep hodd) := by
  constructor
  · intro i j hij
    apply halfSq_injective hodd
    simpa [squareRep_val] using
      congrArg (fun u : squareUnits p => (u.val : ZMod p)) hij
  · intro u
    obtain ⟨a,ha⟩ := u.property
    obtain ⟨i,hi|hi⟩ := exists_halfRep_or_neg hodd a.ne_zero
    · refine ⟨i,Subtype.ext (Units.ext ?_)⟩
      rw [squareRep_val,hi,←ha]
      simp
    · refine ⟨i,Subtype.ext (Units.ext ?_)⟩
      rw [squareRep_val,hi,neg_sq,←ha]
      simp

noncomputable def squareEquiv {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1) :
    Fin ((p-1)/2) ≃ squareUnits p :=
  Equiv.ofBijective (squareRep hodd) (squareRep_bijective hodd)

@[simp] lemma squareEquiv_val {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1)
    (i : Fin ((p-1)/2)) : ((squareEquiv hodd i).val : ZMod p) = (halfRep i)^2 :=
  squareRep_val hodd i

@[simp] lemma squareEquiv_zero {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1)
    (h : 0 < (p-1)/2) : squareEquiv hodd ⟨0,h⟩ = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [squareEquiv_val]
  simp [halfRep]

private noncomputable def squareRoot {p : ℕ} [Fact p.Prime] (u : squareUnits p) :
    (ZMod p)ˣ :=
  Classical.choose u.property

private lemma squareRoot_sq {p : ℕ} [Fact p.Prime] (u : squareUnits p) :
    squareRoot u ^ 2 = u.val :=
  Classical.choose_spec u.property

private lemma squareRoot_sq_val {p : ℕ} [Fact p.Prime] (u : squareUnits p) :
    (↑(squareRoot u) : ZMod p)^2 = (u.val : ZMod p) := by
  simpa using congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) (squareRoot_sq u)

private lemma char_eq_of_sq_eq {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1)
    {x y : ZMod p} (h : x^2=y^2) :
    quadraticChar (ZMod p) x = quadraticChar (ZMod p) y := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with hxy|hxy
  · rw [hxy]
  · have hsign : quadraticChar (ZMod p) (-1) = 1 := by
      apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      rw [FiniteField.isSquare_neg_one_iff,ZMod.card]
      omega
    rw [hxy,show -y=(-1)*y by ring,map_mul,hsign,one_mul]

private lemma psi_compare_root {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1)
    (u : squareUnits p) {x : ZMod p} (hx : x^2 = (u.val : ZMod p)) :
    quadraticChar (ZMod p) (squareRoot u : ZMod p) = quadraticChar (ZMod p) x := by
  exact char_eq_of_sq_eq hp4 ((squareRoot_sq_val u).trans hx.symm)

/-- The sign of the quadratic character of a square root of a nonzero square.
It is independent of the root choice when the field order is one modulo four. -/
noncomputable def psi {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1) :
    squareUnits p →* ℚ where
  toFun u := (quadraticChar (ZMod p) (squareRoot u : ZMod p) : ℚ)
  map_one' := by
    rw [psi_compare_root hp4 (1 : squareUnits p) (x:=1) (by simp),map_one,Int.cast_one]
  map_mul' u v := by
    rw [psi_compare_root hp4 (u*v)
      (x:=(squareRoot u : ZMod p)*(squareRoot v : ZMod p))
      (by rw [mul_pow,squareRoot_sq_val,squareRoot_sq_val]; rfl)]
    rw [map_mul,Int.cast_mul]

@[simp] lemma psi_squareEquiv {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1)
    (hodd : p % 2 = 1) (i : Fin ((p-1)/2)) :
    psi hp4 (squareEquiv hodd i) = (quadraticChar (ZMod p) (halfRep i) : ℚ) := by
  change (quadraticChar (ZMod p) (squareRoot (squareEquiv hodd i) : ZMod p) : ℚ) = _
  rw [psi_compare_root hp4 _ (squareEquiv_val hodd i).symm]

lemma psi_mul_self {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1)
    (u : squareUnits p) : psi hp4 u * psi hp4 u = 1 := by
  change (quadraticChar (ZMod p) (squareRoot u : ZMod p) : ℚ) *
    (quadraticChar (ZMod p) (squareRoot u : ZMod p) : ℚ) = 1
  rw [←Int.cast_mul,←pow_two,quadraticChar_sq_one (squareRoot u).ne_zero,Int.cast_one]

lemma exists_square_generator {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1) :
    ∃ g : squareUnits p, (∀ u : squareUnits p, ∃ n : ℕ, g^n=u) ∧ psi hp4 g = -1 := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_monoid_generator (α := squareUnits p)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  obtain ⟨a,ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) hchar
  have hpsi : psi hp4 (toSquare a) = -1 := by
    change (quadraticChar (ZMod p) (squareRoot (toSquare a) : ZMod p) : ℚ) = -1
    rw [psi_compare_root hp4 _ (x:=(a:ZMod p)) (by simp [toSquare]),ha,Int.cast_neg,Int.cast_one]
  refine ⟨g,hg,?_⟩
  have hpm : psi hp4 g = 1 ∨ psi hp4 g = -1 := sq_eq_one_iff.mp (by
    rw [pow_two,psi_mul_self])
  refine hpm.resolve_left ?_
  intro h
  obtain ⟨n,hn⟩ := hg (toSquare a)
  rw [←hn,map_pow,h,one_pow] at hpsi
  norm_num at hpsi

end SunHalfReps

open BigOperators


namespace SunCirculant

section Structure

variable {G : Type*} [CommGroup G] [Fintype G]

abbrev V (G : Type*) := G → ℚ

private def reflect : V G →ₗ[ℚ] V G where
  toFun v i := v i⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def drift (g : G) : V G →ₗ[ℚ] V G where
  toFun v i := v (g * i) - v (g⁻¹ * i)
  map_add' v w := by ext i; simp; ring
  map_smul' a v := by ext i; simp; ring

private def moment (ψ : V G) : V G →ₗ[ℚ] ℚ where
  toFun v := ∑ i, ψ i * v i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_left_comm]

omit [Fintype G] in
@[simp] private theorem reflect_app (v : V G) (i : G) : reflect v i = v i⁻¹ := rfl
omit [Fintype G] in
@[simp] private theorem drift_app (g : G) (v : V G) (i : G) :
    drift g v i = v (g * i) - v (g⁻¹ * i) := rfl
omit [CommGroup G] in
@[simp] private theorem moment_app (ψ v : V G) : moment ψ v = ∑ i, ψ i * v i := rfl

private def silent (ψ : V G) (s : ℚ) : Submodule ℚ (V G) :=
  (moment 1).ker ⊓ (moment ψ).ker ⊓ (reflect - s • LinearMap.id).ker

private theorem mem_silent (ψ : V G) (s : ℚ) (v : V G) :
    v ∈ silent ψ s ↔ moment 1 v = 0 ∧ moment ψ v = 0 ∧ (∀ i, v i⁻¹ = s * v i) := by
  simp only [silent, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  rw [funext_iff]
  simp [and_assoc]

private theorem shift_moment (ψ : G →* ℚ) (v : V G) (g : G) :
    (∑ i, ψ i * v (g * i)) = ψ g⁻¹ * moment (ψ : V G) v := by
  rw [moment_app, Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft g)
  intro i
  change ψ i * v (g * i) = ψ g⁻¹ * (ψ (g * i) * v (g * i))
  rw [map_mul, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem drift_mem_silent (ψ : G →* ℚ) (g : G) (s : ℚ) {v : V G}
    (hv : v ∈ silent ψ s) : drift g v ∈ silent ψ (-s) := by
  rw [mem_silent] at hv ⊢
  refine ⟨?_, ?_, fun i => ?_⟩
  · let χ : G →* ℚ := 1
    change (∑ i, χ i * (v (g * i) - v (g⁻¹ * i))) = 0
    rw [show (∑ i, χ i * (v (g * i) - v (g⁻¹ * i))) =
        (∑ i, χ i * v (g * i)) - ∑ i, χ i * v (g⁻¹ * i) by
          simp_rw [mul_sub, Finset.sum_sub_distrib], shift_moment, shift_moment]
    change χ g⁻¹ * moment 1 v - χ (g⁻¹)⁻¹ * moment 1 v = 0
    simp [hv.1]
  · simp only [moment_app, drift_app, mul_sub, Finset.sum_sub_distrib]
    rw [shift_moment, shift_moment]
    simp [hv.2.1]
  · simp only [drift_app]
    rw [show g * i⁻¹ = (g⁻¹ * i)⁻¹ by simp [mul_comm],
      show g⁻¹ * i⁻¹ = (g * i)⁻¹ by simp [mul_comm], hv.2.2, hv.2.2]
    ring

omit [Fintype G] in
private theorem drift_zero_imp_parity (ψ : G →* ℚ) (g : G)
    (hg : ∀ i : G, ∃ n : ℕ, g ^ n = i) (hψ : ψ g = -1)
    (v : V G) (hv : drift g v = 0) :
    v = ((v 1 + v g) / 2) • (1 : V G) + ((v 1 - v g) / 2) • (ψ : V G) := by
  have hp (i : G) : v (g ^ 2 * i) = v i := by
    have h := congr_fun hv (g * i)
    change v (g * (g * i)) - v (g⁻¹ * (g * i)) = 0 at h
    simpa [pow_two, mul_assoc] using sub_eq_zero.mp h
  have he (n : ℕ) : v (g ^ n) = (v 1 + v g) / 2 + (v 1 - v g) / 2 * ψ (g ^ n) := by
    induction n using Nat.twoStepInduction with
    | zero => simp; ring
    | one => simp [hψ]; ring
    | more n ih _ =>
      rw [show n + 2 = 2 + n by omega, pow_add, hp, map_mul, map_pow, hψ, ih]
      ring
  ext i
  obtain ⟨n, rfl⟩ := hg i
  simpa using he n

private theorem moment_character_zero (ψ : G →* ℚ) (g : G) (hψ : ψ g = -1) :
    moment 1 (ψ : V G) = 0 := by
  have he : ∑ i, ψ (g * i) = ∑ i : G, ψ i := by
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)
  simp_rw [map_mul, hψ, ← Finset.mul_sum] at he
  simpa only [moment_app, Pi.one_apply, one_mul] using (show ∑ i : G, ψ i = 0 by linarith)

private theorem moment_two (ψ : G →* ℚ) (hψ₂ : ∀ i, ψ i * ψ i = 1) :
    moment (ψ : V G) (ψ : V G) = (Fintype.card G : ℚ) := by
  simp [hψ₂]

private theorem moment_one (ψ : G →* ℚ) : moment (ψ : V G) 1 = moment 1 (ψ : V G) := by
  simp

omit [Fintype G] in
private theorem character_inv (ψ : G →* ℚ) (hψ₂ : ∀ i, ψ i * ψ i = 1) (i : G) :
    ψ i⁻¹ = ψ i := by
  have h := hψ₂ i
  rw [map_inv]
  apply inv_eq_of_mul_eq_one_left
  exact h

private theorem silent_drift_injective (ψ : G →* ℚ) (g : G)
    (hg : ∀ i : G, ∃ n : ℕ, g ^ n = i) (hψ : ψ g = -1) (hψ₂ : ∀ i, ψ i * ψ i = 1)
    (s : ℚ) {v : V G} (hv : v ∈ silent ψ s) (hd : drift g v = 0) : v = 0 := by
  have hv₀ := (mem_silent ψ s v).1 hv
  let a := (v 1 + v g) / 2
  let b := (v 1 - v g) / 2
  have he : v = a • (1 : V G) + b • (ψ : V G) := drift_zero_imp_parity ψ g hg hψ v hd
  rw [he, map_add, map_smul, map_smul, moment_character_zero ψ g hψ] at hv₀
  have hc : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h₁ : moment (1 : V G) 1 = (Fintype.card G : ℚ) := by simp
  have ha : a = 0 := by
    have h := hv₀.1
    simp [h₁, smul_eq_mul] at h
    exact h
  have hb : b = 0 := by
    have h := hv₀.2.1
    rw [map_add, map_smul, map_smul, moment_one ψ, moment_character_zero ψ g hψ,
      moment_two ψ hψ₂] at h
    simp [smul_eq_mul] at h
    exact h
  simp [he, ha, hb]

private theorem moment_reflect (ψ : G →* ℚ) (hψ₂ : ∀ i, ψ i * ψ i = 1) (v : V G) :
    moment (⇑ψ) (reflect v) = moment (⇑ψ) v := by
  simp only [moment_app, reflect_app]
  apply Fintype.sum_equiv (Equiv.inv G)
  intro i
  change ψ i * v i⁻¹ = ψ i⁻¹ * v i⁻¹
  rw [character_inv ψ hψ₂]

private theorem moment_reflect_one (v : V G) : moment 1 (reflect v) = moment 1 v := by
  exact moment_reflect (1 : G →* ℚ) (by simp) v

private abbrev Pieces (ψ : V G) := ℚ × ℚ × (silent ψ 1 × silent ψ (-1))

private def combine (ψ : V G) : Pieces ψ →ₗ[ℚ] V G where
  toFun x := x.1 • 1 + x.2.1 • ψ + (x.2.2.1 : V G) + (x.2.2.2 : V G)
  map_add' x y := by
    ext i
    change (x.1 + y.1) * 1 + (x.2.1 + y.2.1) * ψ i +
      (x.2.2.1.val i + y.2.2.1.val i) + (x.2.2.2.val i + y.2.2.2.val i) = _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
    ring
  map_smul' a x := by
    ext i
    change (a * x.1) * 1 + (a * x.2.1) * ψ i + a * x.2.2.1.val i + a * x.2.2.2.val i = _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, RingHom.id_apply]
    ring

omit [CommGroup G] in
private theorem moment_one_one : moment (1 : V G) 1 = (Fintype.card G : ℚ) := by simp

private theorem combine_bijective (ψ : G →* ℚ) (g : G) (hψ : ψ g = -1)
    (hψ₂ : ∀ i, ψ i * ψ i = 1) : Function.Bijective (combine (⇑ψ)) := by
  have hc : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm := moment_character_zero ψ g hψ
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    rintro ⟨a, b, u, v⟩ h
    change a • (1 : V G) + b • (ψ : V G) + (u : V G) + (v : V G) = 0 at h
    have hu := (mem_silent _ _ _).mp u.property
    have hv := (mem_silent _ _ _).mp v.property
    have ha := congr_arg (moment (1 : V G)) h
    have hb := congr_arg (moment (ψ : V G)) h
    simp only [map_add, map_smul, map_zero, moment_one_one, hm, hu.1, hv.1, smul_eq_mul,
      mul_zero, add_zero, mul_eq_zero, hc, or_false] at ha
    simp only [map_add, map_smul, map_zero, moment_one, moment_two ψ hψ₂,
      hm, hu.2.1, hv.2.1, smul_eq_mul, mul_zero, zero_add, add_zero, mul_eq_zero, hc, or_false] at hb
    simp [ha, hb] at h
    rw [Prod.mk_eq_zero, Prod.mk_eq_zero, Prod.mk_eq_zero]
    refine ⟨ha, hb, ?_, ?_⟩
    · apply Subtype.ext
      funext i
      have h₁ := congr_fun h i
      have h₂ := congr_fun h i⁻¹
      change u.val i + v.val i = 0 at h₁
      change u.val i⁻¹ + v.val i⁻¹ = 0 at h₂
      rw [hu.2.2, hv.2.2] at h₂
      change u.val i = 0
      linarith
    · apply Subtype.ext
      funext i
      have h₁ := congr_fun h i
      have h₂ := congr_fun h i⁻¹
      change u.val i + v.val i = 0 at h₁
      change u.val i⁻¹ + v.val i⁻¹ = 0 at h₂
      rw [hu.2.2, hv.2.2] at h₂
      change v.val i = 0
      linarith
  · intro x
    let a := moment (1 : V G) x / (Fintype.card G : ℚ)
    let b := moment (ψ : V G) x / (Fintype.card G : ℚ)
    let y := x - a • (1 : V G) - b • (ψ : V G)
    have hy₁ : moment 1 y = 0 := by
      simp only [y, map_sub, map_smul, moment_one_one, hm, smul_eq_mul, mul_zero, sub_zero]
      rw [div_mul_cancel₀ _ hc, sub_self]
    have hy₂ : moment (ψ : V G) y = 0 := by
      simp only [y, map_sub, map_smul, moment_one, hm, moment_two ψ hψ₂,
        smul_eq_mul, mul_zero, sub_zero]
      rw [div_mul_cancel₀ _ hc, sub_self]
    let u : V G := (1 / 2 : ℚ) • (y + reflect y)
    let v : V G := (1 / 2 : ℚ) • (y - reflect y)
    have hu : u ∈ silent (⇑ψ) 1 := by
      rw [mem_silent]
      refine ⟨?_, ?_, fun i => ?_⟩
      · simp only [u, map_smul, map_add, moment_reflect_one, hy₁, add_zero, smul_zero]
      · simp only [u, map_smul, map_add, moment_reflect ψ hψ₂, hy₂, add_zero, smul_zero]
      · simp only [u, Pi.smul_apply, Pi.add_apply, reflect_app, inv_inv, one_mul]
        ring
    have hv : v ∈ silent (⇑ψ) (-1) := by
      rw [mem_silent]
      refine ⟨?_, ?_, fun i => ?_⟩
      · simp only [v, map_smul, map_sub, moment_reflect_one, sub_self, smul_zero]
      · simp only [v, map_smul, map_sub, moment_reflect ψ hψ₂, sub_self, smul_zero]
      · simp only [v, Pi.smul_apply, Pi.sub_apply, reflect_app, inv_inv]
        ring
    refine ⟨(a, b, ⟨u, hu⟩, ⟨v, hv⟩), ?_⟩
    ext i
    change (a • (1 : V G) + b • (ψ : V G) + u + v) i = x i
    simp only [u, v, y, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, reflect_app, Pi.one_apply,
      smul_eq_mul]
    ring

private theorem drift_restrict_injective (ψ : G →* ℚ) (g : G)
    (hg : ∀ i : G, ∃ n : ℕ, g ^ n = i) (hψ : ψ g = -1) (hψ₂ : ∀ i, ψ i * ψ i = 1) (s : ℚ) :
    Function.Injective (LinearMap.restrict (f := drift g) (p := silent (⇑ψ) s)
      (q := silent (⇑ψ) (-s)) (fun _v hv => drift_mem_silent ψ g s hv)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  apply Subtype.ext
  have h := congr_arg Subtype.val hv
  exact silent_drift_injective ψ g hg hψ hψ₂ s v.property h

private theorem equal_silent_determinants (ψ : G →* ℚ) (g : G)
    (hg : ∀ i : G, ∃ n : ℕ, g ^ n = i) (hψ : ψ g = -1) (hψ₂ : ∀ i, ψ i * ψ i = 1)
    (T : V G →ₗ[ℚ] V G) (hT : ∀ s v, v ∈ silent (⇑ψ) s → T v ∈ silent (⇑ψ) s)
    (hcomm : ∀ v, drift g (T v) = T (drift g v)) :
    (T.restrict (hT 1)).det = (T.restrict (hT (-1))).det := by
  let f : silent (⇑ψ) 1 →ₗ[ℚ] silent (⇑ψ) (-1) :=
    (drift g).restrict (fun _v hv => drift_mem_silent ψ g 1 hv)
  let h : silent (⇑ψ) (-1) →ₗ[ℚ] silent (⇑ψ) 1 :=
    (drift g).restrict (fun _v hv => by simpa using drift_mem_silent ψ g (-1) hv)
  have hf : Function.Injective f := drift_restrict_injective ψ g hg hψ hψ₂ 1
  have hh : Function.Injective h := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    exact silent_drift_injective ψ g hg hψ hψ₂ (-1) x.property (congr_arg Subtype.val hx)
  have hd := le_antisymm (LinearMap.finrank_le_finrank_of_injective hf)
    (LinearMap.finrank_le_finrank_of_injective hh)
  let e := LinearEquiv.ofBijective f ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hf⟩
  have he : (e : _ →ₗ[ℚ] _) ∘ₗ T.restrict (hT 1) ∘ₗ
      (e.symm : _ →ₗ[ℚ] _) = T.restrict (hT (-1)) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change drift g (T (e.symm x : V G)) = T (x : V G)
    rw [hcomm]
    congr 1
    exact congr_arg Subtype.val (e.apply_symm_apply x)
  rw [← he, LinearMap.det_conj]

private theorem det_from_silent (ψ : G →* ℚ) (g : G)
    (hg : ∀ i : G, ∃ n : ℕ, g ^ n = i) (hψ : ψ g = -1) (hψ₂ : ∀ i, ψ i * ψ i = 1)
    (T : V G →ₗ[ℚ] V G) (h₁ : T 1 = -1) (h₂ : T (ψ : V G) = (ψ : V G))
    (hT : ∀ s v, v ∈ silent (⇑ψ) s → T v ∈ silent (⇑ψ) s)
    (hcomm : ∀ v, drift g (T v) = T (drift g v)) : IsSquare (-T.det) := by
  let e := LinearEquiv.ofBijective (combine (⇑ψ)) (combine_bijective ψ g hψ hψ₂)
  let T₁ := T.restrict (hT 1)
  let T₂ := T.restrict (hT (-1))
  let D := (LinearMap.mulLeft ℚ (-1 : ℚ)).prodMap
    ((LinearMap.id : ℚ →ₗ[ℚ] ℚ).prodMap (T₁.prodMap T₂))
  have he : (e : _ →ₗ[ℚ] _) ∘ₗ D ∘ₗ (e.symm : _ →ₗ[ℚ] _) = T := by
    apply LinearMap.ext
    intro x
    let y := e.symm x
    have hy : combine (⇑ψ) y = x := e.apply_symm_apply x
    have hye : T (combine (⇑ψ) y) = combine (⇑ψ) (D y) := by
      change T (y.1 • (1 : V G) + y.2.1 • (ψ : V G) + (y.2.2.1 : V G) + (y.2.2.2 : V G)) =
        ((-1 : ℚ) * y.1) • (1 : V G) + y.2.1 • (ψ : V G) + T (y.2.2.1 : V G) + T (y.2.2.2 : V G)
      rw [map_add, map_add, map_add, map_smul, map_smul, h₁, h₂]
      simp [smul_neg, neg_smul]
    change combine (⇑ψ) (D y) = T x
    rw [← hye, hy]
  have hdet : T.det = -(T₁.det * T₂.det) := by
    rw [← he, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_mulLeft,
      LinearMap.det_prodMap, LinearMap.det_id, LinearMap.det_prodMap, one_mul, neg_one_mul]
  rw [hdet, neg_neg, ← equal_silent_determinants ψ g hg hψ hψ₂ T hT hcomm]
  exact ⟨T₁.det, rfl⟩

private def conv (c : V G) : V G →ₗ[ℚ] V G where
  toFun v i := ∑ j, c j * v (j * i)
  map_add' v w := by
    ext i
    change (∑ j, c j * (v (j * i) + w (j * i))) = _
    simp_rw [mul_add, Finset.sum_add_distrib]; rfl
  map_smul' a v := by
    ext i
    change (∑ j, c j * (a * v (j * i))) = a * ∑ j, c j * v (j * i)
    simp_rw [Finset.mul_sum, mul_left_comm a]

@[simp] private theorem conv_app (c v : V G) (i : G) :
    conv c v i = ∑ j, c j * v (j * i) := rfl

private theorem conv_drift (c : V G) (g : G) (v : V G) :
    drift g (conv c v) = conv c (drift g v) := by
  ext i
  simp only [drift_app, conv_app, mul_sub, Finset.sum_sub_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> rw [mul_left_comm]

private theorem conv_reflect (c : V G) (hc : ∀ i, c i⁻¹ = c i) (v : V G) :
    reflect (conv c v) = conv c (reflect v) := by
  ext i
  simp only [reflect_app, conv_app]
  apply Fintype.sum_equiv (Equiv.inv G)
  intro j
  change c j * v (j * i⁻¹) = c j⁻¹ * v ((j⁻¹ * i)⁻¹)
  rw [hc]
  congr 2
  simp [mul_comm]

private theorem conv_character (c : V G) (ψ : G →* ℚ) :
    conv c (ψ : V G) = (∑ i, c i * ψ i) • (ψ : V G) := by
  ext i
  simp only [conv_app, map_mul, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]

private theorem conv_moment (c : V G) (ψ : G →* ℚ) (v : V G) :
    moment (ψ : V G) (conv c v) = (∑ i, c i * ψ i⁻¹) * moment (ψ : V G) v := by
  rw [moment_app]
  simp only [conv_app, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (∑ x, ψ x * (c i * v (i * x))) = c i * ∑ x, ψ x * v (i * x) by
    simp_rw [Finset.mul_sum, mul_left_comm (c i)], shift_moment, mul_assoc]

private def transform (c : V G) (ψ : G →* ℚ) : V G →ₗ[ℚ] V G :=
  conv c + (((1 - ∑ i, c i * ψ i) / (Fintype.card G : ℚ)) •
    (moment (ψ : V G)).smulRight (ψ : V G))

private theorem transform_apply (c : V G) (ψ : G →* ℚ) (v : V G) :
    transform c ψ v = conv c v +
      (((1 - ∑ i, c i * ψ i) / (Fintype.card G : ℚ)) * moment (ψ : V G) v) • (ψ : V G) := by
  simp [transform, LinearMap.smulRight_apply, smul_smul]

private theorem transform_comm (c : V G) (ψ : G →* ℚ) (g : G)
    (hψ₂ : ∀ i, ψ i * ψ i = 1) (v : V G) :
    drift g (transform c ψ v) = transform c ψ (drift g v) := by
  have hh : drift g (ψ : V G) = 0 := by
    ext i
    simp [map_mul, character_inv ψ hψ₂]
  have hm : moment (ψ : V G) (drift g v) = 0 := by
    simp only [moment_app, drift_app, mul_sub, Finset.sum_sub_distrib]
    rw [shift_moment, shift_moment, inv_inv, character_inv ψ hψ₂, sub_self]
  simp only [transform_apply, map_add, map_smul, hh, hm, smul_zero, mul_zero, zero_smul,
    add_zero, conv_drift]

private theorem transform_silent (c : V G) (hc : ∀ i, c i⁻¹ = c i) (ψ : G →* ℚ)
    (s : ℚ) (v : V G) (hv : v ∈ silent (⇑ψ) s) :
    transform c ψ v ∈ silent (⇑ψ) s := by
  rw [mem_silent] at hv ⊢
  simp only [transform_apply, hv.2.1, mul_zero, zero_smul, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · let χ : G →* ℚ := 1
    change moment (χ : V G) (conv c v) = 0
    rw [conv_moment, show moment (χ : V G) v = 0 from hv.1, mul_zero]
  · rw [conv_moment, hv.2.1, mul_zero]
  · intro i
    change reflect (conv c v) i = _
    rw [conv_reflect c hc]
    have h : reflect v = s • v := funext hv.2.2
    rw [h, map_smul]
    rfl

private theorem transform_square (c : V G) (hc : ∀ i, c i⁻¹ = c i) (ψ : G →* ℚ)
    (g : G) (hg : ∀ i : G, ∃ n : ℕ, g ^ n = i) (hψ : ψ g = -1)
    (hψ₂ : ∀ i, ψ i * ψ i = 1) (hc₁ : ∑ i, c i = -1) :
    IsSquare (-(transform c ψ).det) := by
  have hcard : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine det_from_silent ψ g hg hψ hψ₂ (transform c ψ) ?_ ?_
    (transform_silent c hc ψ) (transform_comm c ψ g hψ₂)
  · have hh : conv c 1 = -1 := by
      ext i
      simp [hc₁]
    rw [transform_apply, hh, moment_one ψ, moment_character_zero ψ g hψ]
    simp
  · rw [transform_apply, conv_character, moment_two ψ hψ₂, div_mul_cancel₀ _ hcard,
      ← add_smul]
    simp

private theorem transform_character (c : V G) (ψ : G →* ℚ) (hψ₂ : ∀ i, ψ i * ψ i = 1) :
    transform c ψ (ψ : V G) = (ψ : V G) := by
  have hcard : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [transform_apply, conv_character, moment_two ψ hψ₂, div_mul_cancel₀ _ hcard, ← add_smul]
  simp

private def adjusted (c : V G) (ψ : G →* ℚ) : Matrix G G ℚ := fun i j =>
  c (j * i⁻¹) + ((1 - ∑ x, c x * ψ x) / (Fintype.card G : ℚ)) * ψ i * ψ j

private theorem adjusted_toLin [DecidableEq G] (c : V G) (ψ : G →* ℚ) :
    (adjusted c ψ).toLin' = transform c ψ := by
  apply LinearMap.ext
  intro v
  funext i
  rw [Matrix.toLin'_apply, transform_apply]
  let k := (1 - ∑ x, c x * ψ x) / (Fintype.card G : ℚ)
  change (∑ j, (c (j * i⁻¹) + k * ψ i * ψ j) * v j) =
    (∑ j, c j * v (j * i)) + (k * (∑ j, ψ j * v j)) * ψ i
  simp_rw [add_mul, Finset.sum_add_distrib]
  have he : (∑ j, c (j * i⁻¹) * v j) = ∑ j, c j * v (j * i) := by
    symm
    apply Fintype.sum_equiv (Equiv.mulRight i)
    intro j
    change c j * v (j * i) = c (j * i * i⁻¹) * v (j * i)
    rw [mul_inv_cancel_right]
  rw [he]
  congr 1
  rw [mul_right_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

private theorem adjusted_symm (c : V G) (ψ : G →* ℚ) (hc : ∀ i, c i⁻¹ = c i) (i j : G) :
    adjusted c ψ i j = adjusted c ψ j i := by
  unfold adjusted
  rw [← hc (j * i⁻¹), mul_inv_rev, inv_inv]
  ring

variable [DecidableEq G]

/-- Replacing the identity row of a symmetric circulant by its order-two character
leaves only the determinant on the complementary character spaces.  The constant
mode contributes `-1`, and the remaining two real reflection blocks have equal determinant. -/
theorem square_det_replace (c : V G) (hc : ∀ i, c i⁻¹ = c i) (ψ : G →* ℚ)
    (g : G) (hg : ∀ i : G, ∃ n : ℕ, g ^ n = i) (hψ : ψ g = -1)
    (hψ₂ : ∀ i, ψ i * ψ i = 1) (hc₁ : ∑ i, c i = -1) :
    IsSquare (-(Matrix.updateRow (fun i j : G => c (j * i⁻¹)) 1 (⇑ψ)).det) := by
  let B : Matrix G G ℚ := fun i j => c (j * i⁻¹)
  let C := adjusted c ψ
  let A := B.updateRow 1 (⇑ψ)
  have hleft : (∑ i, ψ i • C i) = (ψ : V G) := by
    funext j
    have hr := congr_fun (transform_character c ψ hψ₂) j
    rw [← adjusted_toLin, Matrix.toLin'_apply] at hr
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      adjusted_symm c ψ hc j, mul_comm] using hr
  have h₁ : (C.updateRow 1 (⇑ψ)).det = C.det := by
    rw [← hleft, Matrix.det_updateRow_sum, map_one, one_smul]
  have h₂ : (C.updateRow 1 (⇑ψ)).det = A.det := by
    let k := (1 - ∑ x, c x * ψ x) / (Fintype.card G : ℚ)
    refine Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => if i = 1 then 0 else k * ψ i) 1 (if_pos rfl) (fun i j => ?_)
    by_cases hi : i = 1
    · subst i
      simp [A, Matrix.updateRow_self]
    · change C.updateRow 1 (⇑ψ) i j = B.updateRow 1 (⇑ψ) i j +
        (if i = 1 then 0 else k * ψ i) * B.updateRow 1 (⇑ψ) 1 j
      rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi, Matrix.updateRow_self, if_neg hi]
      rfl
  have hdet : C.det = A.det := h₁.symm.trans h₂
  have hs := transform_square c hc ψ g hg hψ hψ₂ hc₁
  rw [← adjusted_toLin, LinearMap.det_toLin'] at hs
  change IsSquare (-C.det) at hs
  rw [hdet] at hs
  exact hs

end Structure

end SunCirculant

namespace SunDeterminant

open BigOperators SunHalfReps

private abbrev value {p : ℕ} [Fact p.Prime] (x : squareUnits p) : ZMod p := (x.val : ZMod p)

private theorem square_value {p : ℕ} [Fact p.Prime] (x : squareUnits p) :
    quadraticChar (ZMod p) (value x) = 1 := by
  apply (quadraticChar_one_iff_isSquare x.val.ne_zero).2
  obtain ⟨t, ht⟩ := x.property
  refine ⟨(t : ZMod p), ?_⟩
  have he := congr_arg (fun u : (ZMod p)ˣ => (u : ZMod p)) ht.symm
  simpa [pow_two] using he

private theorem char_cast_two {p : ℕ} [Fact p.Prime] {x : ZMod p} (hx : x ≠ 0) :
    (quadraticChar (ZMod p) x : ZMod 2) = 1 := by
  rcases quadraticChar_dichotomy hx with h | h
  · simp [h]
  · rw [h]
    decide

private theorem coefficient_symm {p : ℕ} [Fact p.Prime] (x : squareUnits p) :
    quadraticChar (ZMod p) (1 + value x⁻¹) = quadraticChar (ZMod p) (1 + value x) := by
  have he : 1 + value x⁻¹ = value x⁻¹ * (1 + value x) := by
    change 1 + (↑(x.val⁻¹) : ZMod p) = ↑(x.val⁻¹) * (1 + ↑(x.val) : ZMod p)
    rw [mul_add, mul_one, ← Units.val_mul, inv_mul_cancel]
    rw [Units.val_one]
    exact add_comm _ _
  rw [he, map_mul, square_value, one_mul]

private theorem coeff_row {p : ℕ} [Fact p.Prime] (x y : squareUnits p) :
    quadraticChar (ZMod p) (value x + value y) =
      quadraticChar (ZMod p) (1 + value (y * x⁻¹)) := by
  have he : value x + value y = value x * (1 + value (y * x⁻¹)) := by
    change (↑x.val : ZMod p) + ↑y.val = ↑x.val * (1 + ↑(y.val * x.val⁻¹))
    simp only [Units.val_mul, mul_add, mul_one, mul_left_comm (↑x.val : ZMod p) (↑y.val : ZMod p)]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [he, map_mul, square_value, one_mul]

private theorem jacobi_char (p : ℕ) [Fact p.Prime] (i : ℤ) :
    jacobiSym i p = quadraticChar (ZMod p) (i : ZMod p) :=
  (jacobiSym.legendreSym.to_jacobiSym p i).symm

private theorem row_sum {p : ℕ} [Fact p.Prime] (ho : p % 2 = 1) :
    ∑ x : squareUnits p, quadraticChar (ZMod p) (1 + value x) = -1 := by
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hsum := SunHalfReps.sum_zmod_half ho
    (fun a : ZMod p => quadraticChar (ZMod p) (1 + a^2)) (fun a => by rw [neg_sq])
  rw [OMA.MO310301.quadraticChar_sum_one_add_sq hc] at hsum
  norm_num at hsum
  have heq : ∑ i : Fin ((p-1)/2), quadraticChar (ZMod p) (1 + (halfRep i)^2) =
      ∑ x : squareUnits p, quadraticChar (ZMod p) (1 + value x) := by
    apply Fintype.sum_equiv (squareEquiv ho)
    intro i
    rw [show value (squareEquiv ho i) = (halfRep i)^2 from squareEquiv_val ho i]
  change (-1 : ℤ) = 1 + 2 * ∑ i : Fin ((p-1)/2),
    quadraticChar (ZMod p) (1 + (halfRep i)^2) at hsum
  rw [heq] at hsum
  omega

private def negUnit {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1) : squareUnits p := by
  refine ⟨-1, ?_⟩
  obtain ⟨z,hz⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 (by omega)
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
  simpa [pow_two] using hz.symm

private theorem negUnit_value {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1) :
    value (negUnit hp4) = (-1 : ZMod p) := rfl

private theorem negUnit_sq {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1) :
    negUnit hp4 * negUnit hp4 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change value (negUnit hp4) * value (negUnit hp4) = 1
  rw [negUnit_value]
  ring

private theorem value_inj {p : ℕ} [Fact p.Prime] :
    Function.Injective (value (p := p)) := by
  intro x y h
  exact Subtype.ext (Units.ext h)

private theorem solution (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) :
    ∃ m : ℤ, Odd m ∧ -(OMA.S_mo_310301.A p).det = m ^ 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hpl := hp.two_le
  have ho : p % 2 = 1 := by omega
  have hmid : 0 < (p-1)/2 := by omega
  let G := squareUnits p
  let e := squareEquiv (p := p) ho
  let i₀ : Fin ((p-1)/2) := ⟨0, hmid⟩
  have he₀ : e i₀ = 1 := squareEquiv_zero ho hmid
  let M : Matrix G G ℤ := fun x y => quadraticChar (ZMod p) (value x + value y)
  let q : G → ℤ := fun y => quadraticChar (ZMod p) (halfRep (e.symm y))
  have mq (y : G) : (q y : ℚ) = psi hp4 y := by
    change (quadraticChar (ZMod p) (halfRep (e.symm y)) : ℚ) = psi hp4 y
    rw [← psi_squareEquiv hp4 ho, show squareEquiv ho (e.symm y) = y from e.apply_symm_apply y]
  have hA : (OMA.S_mo_310301.A p).submatrix e.symm e.symm = M.updateRow 1 q := by
    ext x y
    rw [Matrix.submatrix_apply]
    have h : (↑(e.symm x) : ℕ) = 0 ↔ x = 1 := by
      constructor
      · intro hz
        have hz' : e.symm x = i₀ := Fin.ext hz
        calc
          x = e (e.symm x) := (e.apply_symm_apply x).symm
          _ = e i₀ := congrArg e hz'
          _ = 1 := he₀
      · intro hx
        subst x
        rw [← he₀, e.symm_apply_apply]
    unfold OMA.S_mo_310301.A
    by_cases hx : x = 1
    · rw [if_pos (h.mpr hx), hx, Matrix.updateRow_self, jacobi_char]
      simp [q, halfRep]
    · rw [if_neg (fun hz => hx (h.mp hz)), Matrix.updateRow_ne hx, jacobi_char]
      change quadraticChar (ZMod p) ((((↑(e.symm x).val : ℤ) + 1) ^ 2 +
        ((↑(e.symm y).val : ℤ) + 1) ^ 2 : ℤ) : ZMod p) =
        quadraticChar (ZMod p) (value x + value y)
      simp only [Int.cast_add, Int.cast_pow, Int.cast_natCast, Int.cast_one]
      change quadraticChar (ZMod p) ((halfRep (e.symm x)) ^ 2 + (halfRep (e.symm y)) ^ 2) = _
      rw [← squareEquiv_val ho, ← squareEquiv_val ho,
        show squareEquiv ho (e.symm x) = x from e.apply_symm_apply x,
        show squareEquiv ho (e.symm y) = y from e.apply_symm_apply y]
  have hdet : (OMA.S_mo_310301.A p).det = (M.updateRow 1 q).det := by
    rw [← hA, Matrix.det_submatrix_equiv_self]
  have hGcard : Fintype.card G = (p-1)/2 := (Fintype.card_congr e).symm.trans (Fintype.card_fin _)
  have hG : Even (Fintype.card G) := by rw [hGcard, Nat.even_iff]; omega
  let P : Equiv.Perm G := Equiv.mulLeft (negUnit hp4)
  have hP : Function.Involutive P := by
    intro x
    change negUnit hp4 * (negUnit hp4 * x) = x
    rw [← mul_assoc, negUnit_sq, one_mul]
  have hM (x y : G) : (M x y : ZMod 2) = if x = P y then 0 else 1 := by
    have hxy : value x + value y = 0 ↔ x = P y := by
      change value x + value y = 0 ↔ x = negUnit hp4 * y
      rw [add_eq_zero_iff_eq_neg]
      constructor
      · intro hv
        apply value_inj
        change value x = value (negUnit hp4) * value y
        rw [negUnit_value, neg_one_mul, hv]
      · intro hv
        rw [hv]
        change value (negUnit hp4) * value y = -value y
        rw [negUnit_value, neg_one_mul]
    by_cases h : x = P y
    · change (quadraticChar (ZMod p) (value x + value y) : ZMod 2) = _
      rw [hxy.mpr h, quadraticChar_zero, Int.cast_zero, if_pos h]
    · exact (if_neg h).symm ▸ char_cast_two (fun hv => h (hxy.mp hv))
  have hq (y : G) : (q y : ZMod 2) = 1 := char_cast_two (halfRep_ne_zero ho (e.symm y))
  have hodd := OMA.MO310301.odd_det_updateRow M hG P hP 1 q hM hq
  let c : G → ℚ := fun x => (quadraticChar (ZMod p) (1 + value x) : ℚ)
  have hc_symm (x : G) : c x⁻¹ = c x :=
    congr_arg (fun n : ℤ => (n : ℚ)) (coefficient_symm x)
  have hcsum : ∑ i : G, c i = -1 := by
    change (∑ i : G, (quadraticChar (ZMod p) (1 + value i) : ℚ)) = -1
    exact_mod_cast row_sum (p := p) ho
  obtain ⟨g, hg, hψ⟩ := exists_square_generator hp4
  have hsq := SunCirculant.square_det_replace c hc_symm (psi hp4) g hg hψ (psi_mul_self hp4) hcsum
  let C := Int.castRingHom ℚ
  let B : Matrix G G ℚ := fun x y => c (y * x⁻¹)
  have hcast : C.mapMatrix (M.updateRow 1 q) =
      B.updateRow 1 (psi hp4 : G → ℚ) := by
    ext x y
    change ((M.updateRow 1 q x y : ℤ) : ℚ) = B.updateRow 1 (psi hp4 : G → ℚ) x y
    simp only [Matrix.updateRow_apply]
    by_cases hx : x = 1
    · simpa only [if_pos hx] using mq y
    · simp only [if_neg hx]
      change (quadraticChar (ZMod p) (value x + value y) : ℚ) = c (y * x⁻¹)
      rw [coeff_row]
  change IsSquare (-(B.updateRow 1 (psi hp4 : G → ℚ)).det) at hsq
  rw [← hcast, ← C.map_det, ← map_neg C] at hsq
  change IsSquare ((-(M.updateRow 1 q).det : ℤ) : ℚ) at hsq
  obtain ⟨m, hm⟩ := Rat.isSquare_intCast_iff.mp hsq
  have hmOdd : Odd m := by
    have hh : Odd (m * m) := by
      rw [← hm]
      exact hodd.neg
    exact (Int.odd_mul.mp hh).1
  exact ⟨m, hmOdd, by rw [hdet, hm, pow_two]⟩

end SunDeterminant

-- The square assertion is Hai-Liang Wu, Corollary 5 (C. R. Math. 359, 2021, 651–655),
-- https://doi.org/10.5802/crmath.205. We pair rational reflection blocks by a difference
-- of shift operators, and obtain oddness from the rank structure modulo two.
theorem OMA.solution : type_of% @OMA.S_mo_310301.main := SunDeterminant.solution
