import FormalConjectures.ErdosProblems.«211»
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Analysis.Real.Pi.Bounds

section
-- Lattice211
open scoped BigOperators Matrix
open Finset

namespace E211Counter

abbrev Z3 := Fin 3 → ℤ
abbrev R3 := Fin 3 → ℝ
abbrev E3 := EuclideanSpace ℝ (Fin 3)

def height (x : Z3) : ℕ := (x 0).natAbs + (x 1).natAbs + (x 2).natAbs

def content (x : Z3) : ℕ := Nat.gcd (Nat.gcd (x 0).natAbs (x 1).natAbs) (x 2).natAbs

def realVec (x : Z3) : R3 := fun i => x i

def eVec (x : Z3) : E3 := WithLp.toLp 2 (realVec x)

theorem coord_le_norm {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) (i : ι) :
    |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i

theorem int_coord_le_norm (x : Z3) (i : Fin 3) : ((x i).natAbs : ℝ) ≤ ‖eVec x‖ := by
  have he : ((x i).natAbs : ℝ) = |(x i : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [he]
  exact coord_le_norm (eVec x) i

theorem content_dvd (d : ℕ) (x : Z3) : d ∣ content x ↔ ∀ i, (d : ℤ) ∣ x i := by
  simp [content, Nat.dvd_gcd_iff, Int.natCast_dvd, Fin.forall_fin_succ, and_assoc]

theorem content_pos {x : Z3} (h : x ≠ 0) : 0 < content x := by
  by_contra! hn
  have he : content x = 0 := by omega
  have hd := (content_dvd 0 x).mp (by simp [he])
  exact h (funext fun i => by simpa using hd i)

theorem content_smul (d : ℕ) (x : Z3) : content ((d : ℤ) • x) = d * content x := by
  simp [content, Pi.smul_apply, smul_eq_mul, Int.natAbs_mul, Nat.gcd_mul_left]

theorem height_smul (d : ℕ) (x : Z3) : height ((d : ℤ) • x) = d * height x := by
  simp [height, Pi.smul_apply, smul_eq_mul, Int.natAbs_mul, Nat.mul_add]

theorem content_neg (x : Z3) : content (-x) = content x := by
  simp [content]

theorem height_neg (x : Z3) : height (-x) = height x := by
  simp [height]

theorem coord_le_height (x : Z3) (i : Fin 3) : (x i).natAbs ≤ height x := by
  fin_cases i <;> simp [height] <;> omega

theorem height_pos {x : Z3} (h : x ≠ 0) : 0 < height x := by
  by_contra! hn
  apply h
  ext i
  have := coord_le_height x i
  simpa using (show (x i).natAbs = 0 by omega)

def normalize (x : Z3) : Z3 := fun i => x i / (content x : ℤ)

theorem smul_normalize (x : Z3) : (content x : ℤ) • normalize x = x := by
  ext i
  have hd := (content_dvd (content x) x).mp dvd_rfl i
  simpa [normalize, Pi.smul_apply, smul_eq_mul, mul_comm] using Int.ediv_mul_cancel hd

theorem content_normalize {x : Z3} (h : x ≠ 0) : content (normalize x) = 1 := by
  have he := congrArg content (smul_normalize x)
  rw [content_smul, ← mul_one (content x)] at he
  exact Nat.eq_of_mul_eq_mul_left (content_pos h) (by simpa using he)

theorem primitive_coeff {x y : Z3} (hx : content x = 1) {t : ℝ}
    (h : realVec y = t • realVec x) : ∃ d : ℤ, (d : ℝ) = t := by
  let a := Int.gcdA (x 0) (x 1)
  let b := Int.gcdB (x 0) (x 1)
  let g := Int.gcd (x 0) (x 1)
  let c := Int.gcdA (g : ℤ) (x 2)
  let e := Int.gcdB (g : ℤ) (x 2)
  have hg : (g : ℤ) = x 0 * a + x 1 * b := Int.gcd_eq_gcd_ab ..
  have h1 : (1 : ℤ) = (g : ℤ) * c + x 2 * e := by
    have hh := Int.gcd_eq_gcd_ab (g : ℤ) (x 2)
    change ((Int.gcd (g : ℤ) (x 2) : ℕ) : ℤ) = (g : ℤ) * c + x 2 * e at hh
    have he : Int.gcd (g : ℤ) (x 2) = 1 := by simpa [g, Int.gcd, content] using hx
    simpa [he] using hh
  have h2 : (1 : ℤ) = (x 0 * a + x 1 * b) * c + x 2 * e := by rw [← hg, ← h1]
  have hr : (1 : ℝ) = ((x 0 : ℝ) * (a : ℝ) + (x 1 : ℝ) * (b : ℝ)) * (c : ℝ) +
      (x 2 : ℝ) * (e : ℝ) := by exact_mod_cast h2
  refine ⟨(y 0 * a + y 1 * b) * c + y 2 * e, ?_⟩
  have hh (i : Fin 3) : (y i : ℝ) = t * (x i : ℝ) := congrFun h i
  push_cast
  rw [hh, hh, hh]
  linear_combination -t * hr

theorem content_int_smul (d : ℤ) (x : Z3) : content (d • x) = d.natAbs * content x := by
  simp [content, Pi.smul_apply, smul_eq_mul, Int.natAbs_mul, Nat.gcd_mul_left]

theorem primitive_prop {x y : Z3} (hx : content x = 1) (hy : content y = 1) {t : ℝ}
    (h : realVec y = t • realVec x) : y = x ∨ y = -x := by
  obtain ⟨d, hd⟩ := primitive_coeff hx h
  have he : y = d • x := by
    ext i
    have hh : (y i : ℝ) = (d : ℝ) * (x i : ℝ) := by simpa [← hd, realVec, Pi.smul_apply, smul_eq_mul] using congrFun h i
    exact_mod_cast hh
  have ha : d.natAbs = 1 := by rw [he, content_int_smul, hx, mul_one] at hy; exact hy
  have hd' : d = 1 ∨ d = -1 := by omega
  rcases hd' with rfl | rfl <;> simp [he]

def positive (x : Z3) : Prop := 0 < x 0 ∨ x 0 = 0 ∧ (0 < x 1 ∨ x 1 = 0 ∧ 0 < x 2)

theorem positive_or_neg {x : Z3} (hx : x ≠ 0) : positive x ∨ positive (-x) := by
  simp [positive]
  have hn : ¬ (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0) := by
    rintro ⟨h0,h1,h2⟩
    apply hx
    ext i
    fin_cases i <;> assumption
  omega

theorem not_positive_neg {x : Z3} (h : positive x) : ¬ positive (-x) := by
  simp [positive] at h ⊢
  omega

noncomputable def cube (m : ℕ) : Finset Z3 :=
  Fintype.piFinset fun _ : Fin 3 => Icc (-(m : ℤ)) (m : ℤ)

theorem mem_cube {m : ℕ} {x : Z3} : x ∈ cube m ↔ ∀ i, (x i).natAbs ≤ m := by
  simp only [cube, Fintype.mem_piFinset, mem_Icc]
  exact forall_congr' (fun i => by omega)

theorem card_cube (m : ℕ) : (cube m).card = (2 * m + 1)^3 := by
  rw [cube, Fintype.card_piFinset]
  have h : (Icc (-(m : ℤ)) (m : ℤ)).card = 2 * m + 1 := by
    rw [Int.card_Icc]
    omega
  simp [h]

noncomputable def ballInts (r : ℝ) : Finset Z3 := by
  classical
  exact (cube ⌈r⌉₊).filter fun x => ‖eVec x‖ ≤ r

theorem mem_ballInts {r : ℝ} {x : Z3} : x ∈ ballInts r ↔ ‖eVec x‖ ≤ r := by
  simp only [ballInts, mem_filter, mem_cube]
  refine and_iff_right_of_imp fun h i => ?_
  exact_mod_cast (int_coord_le_norm x i).trans (h.trans (Nat.le_ceil r))

noncomputable def prim (m : ℕ) : Finset Z3 := (ballInts m).filter fun x => content x = 1

theorem eVec_neg (x : Z3) : eVec (-x) = -eVec x := by
  ext i
  simp [eVec, realVec]

noncomputable def points (m : ℕ) : Finset Z3 := by
  classical
  exact (prim m).filter positive

theorem twice_points (m : ℕ) : 2 * (points m).card = (prim m).card := by
  classical
  let Q := (prim m).filter fun x => ¬ positive x
  have hsum := card_filter_add_card_filter_not (s := prim m) (p := positive)
  change (points m).card + Q.card = (prim m).card at hsum
  have he : Q = (points m).image Neg.neg := by
    ext x
    simp only [Q, points, mem_filter, mem_image, prim, mem_ballInts]
    constructor
    · rintro ⟨⟨hh,hc⟩,hp⟩
      have hn : x ≠ 0 := by rintro rfl; simp [content] at hc
      exact ⟨-x, ⟨⟨by simpa [eVec_neg], by simpa [content_neg]⟩,
        (positive_or_neg hn).resolve_left hp⟩, neg_neg x⟩
    · rintro ⟨y,⟨⟨hh,hc⟩,hp⟩, rfl⟩
      exact ⟨⟨by simpa [eVec_neg], by simpa [content_neg]⟩, not_positive_neg hp⟩
  rw [he, card_image_of_injective _ neg_injective] at hsum
  omega

theorem mem_points {m : ℕ} {x : Z3} :
    x ∈ points m ↔ ‖eVec x‖ ≤ m ∧ content x = 1 ∧ positive x := by
  simp [points, prim, mem_ballInts, and_assoc]

theorem realVec_inj : Function.Injective realVec := by
  intro x y he
  ext i
  exact_mod_cast (show (x i : ℝ) = (y i : ℝ) from congrFun he i)

theorem realVec_cross (x y : Z3) : realVec (x ⨯₃ y) = realVec x ⨯₃ realVec y := by
  ext i
  fin_cases i <;> simp [cross_apply, realVec]

theorem realVec_smul (d : ℤ) (x : Z3) : realVec (d • x) = (d : ℝ) • realVec x := by
  ext i
  simp [realVec, Pi.smul_apply, smul_eq_mul]

theorem realVec_neg (x : Z3) : realVec (-x) = -realVec x := by
  ext i
  simp [realVec]

theorem realVec_zero : realVec 0 = 0 := by ext i; simp [realVec]

theorem eVec_inj : Function.Injective eVec := fun _ _ h => realVec_inj (WithLp.toLp_injective 2 h)

theorem eVec_zero : eVec 0 = 0 := by simp [eVec, realVec_zero]

theorem eVec_smul (d : ℤ) (x : Z3) : eVec (d • x) = (d : ℝ) • eVec x := by
  rw [eVec, realVec_smul]
  rfl

theorem eVec_add (x y : Z3) : eVec (x+y) = eVec x + eVec y := by
  ext i
  simp [eVec, realVec]

theorem eVec_sub (x y : Z3) : eVec (x-y) = eVec x - eVec y := by
  ext i
  simp [eVec, realVec]

theorem cross_ne_of_points {m : ℕ} {x y : Z3} (hx : x ∈ points m) (hy : y ∈ points m)
    (hne : x ≠ y) : realVec x ⨯₃ realVec y ≠ 0 := by
  have hcx := (mem_points.mp hx).2.1
  have hx0 : realVec x ≠ 0 := by
    intro h
    have : x = 0 := realVec_inj (h.trans realVec_zero.symm)
    simp [this, content] at hcx
  rw [crossProduct_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff' hx0]
  intro t ht
  rcases primitive_prop hcx (mem_points.mp hy).2.1 ht.symm with h | h
  · exact hne h.symm
  · exact not_positive_neg (mem_points.mp hx).2.2 (h ▸ (mem_points.mp hy).2.2)

theorem height_cross (x y : Z3) : height (x ⨯₃ y) ≤ height x * height y := by
  have h (a b c d : ℤ) : (a*b-c*d).natAbs ≤ a.natAbs*b.natAbs+c.natAbs*d.natAbs := by
    simpa [Int.natAbs_mul, sub_eq_add_neg] using Int.natAbs_add_le (a*b) (-(c*d))
  change (x 1 * y 2 - x 2 * y 1).natAbs + (x 2 * y 0 - x 0 * y 2).natAbs +
    (x 0 * y 1 - x 1 * y 0).natAbs ≤ height x * height y
  unfold height
  have h0 := h (x 1) (y 2) (x 2) (y 1)
  have h1 := h (x 2) (y 0) (x 0) (y 2)
  have h2 := h (x 0) (y 1) (x 1) (y 0)
  nlinarith only [h0, h1, h2, Nat.zero_le ((x 0).natAbs * (y 0).natAbs),
    Nat.zero_le ((x 1).natAbs * (y 1).natAbs), Nat.zero_le ((x 2).natAbs * (y 2).natAbs)]

end E211Counter
end

section
-- Residues211
noncomputable section
open scoped BigOperators Matrix
open Finset

namespace E211Counter

def residue {ι : Type*} (d : ℕ) (x : ι → ℤ) : ι → ZMod d := fun i => x i

def Plocal {F : Type*} [Ring F] (x : Fin 3 → F) : Prop := x ≠ 0

def Qlocal {F : Type*} [CommRing F] (x y : Fin 3 → F) : Prop := x ⨯₃ y ≠ 0

theorem residue_cross (d : ℕ) (x y : Z3) : residue d (x ⨯₃ y) = residue d x ⨯₃ residue d y := by
  ext i
  fin_cases i <;> simp [residue, cross_apply]

theorem residue_eq_zero_iff (d : ℕ) (x : Z3) : residue d x = 0 ↔ d ∣ content x := by
  rw [content_dvd, funext_iff]
  exact forall_congr' fun i => ZMod.intCast_zmod_eq_zero_iff_dvd (x i) d

abbrev V (d : ℕ) := Fin 3 → ZMod d

def crt (a b : ℕ) (h : a.Coprime b) : V (a * b) ≃ V a × V b :=
  (Equiv.piCongrRight fun _ : Fin 3 => (ZMod.chineseRemainder h).toEquiv).trans
    (Equiv.arrowProdEquivProdArrow (Fin 3) (fun _ => ZMod a) (fun _ => ZMod b))

theorem crt_residue (a b : ℕ) (h : a.Coprime b) (x : Z3) :
    crt a b h (residue (a*b) x) = (residue a x, residue b x) := by
  apply Prod.ext <;> ext i
  · change (ZMod.chineseRemainder h ((x i : ℤ) : ZMod (a*b))).1 = _
    rw [map_intCast]
    rfl
  · change (ZMod.chineseRemainder h ((x i : ℤ) : ZMod (a*b))).2 = _
    rw [map_intCast]
    rfl

def ok6 (x : V 6) : Prop :=
  let p := crt 2 3 (by decide) x
  Plocal p.1 ∧ Plocal p.2

abbrev pairV (d : ℕ) := V d × V d

def pairCRT (a b : ℕ) (h : Nat.Coprime a b) : pairV (a*b) ≃ pairV a × pairV b :=
  ((crt a b h).prodCongr (crt a b h)).trans (Equiv.prodProdProdComm _ _ _ _)

def crt30 : pairV 30 ≃ (pairV 2 × pairV 3) × pairV 5 :=
  (pairCRT 6 5 (by decide)).trans ((pairCRT 2 3 (by decide)).prodCongr (Equiv.refl _))

def ok30 (x y : V 30) : Prop :=
  let p := crt30 (x,y)
  Qlocal p.1.1.1 p.1.1.2 ∧ Qlocal p.1.2.1 p.1.2.2 ∧ Qlocal p.2.1 p.2.2

theorem ok6_res (x : Z3) : ok6 (residue 6 x) ↔ ¬ 2 ∣ content x ∧ ¬ 3 ∣ content x := by
  unfold ok6
  change (let p := crt 2 3 (by decide) (residue (2*3) x); Plocal p.1 ∧ Plocal p.2) ↔ _
  rw [crt_residue]
  simp [Plocal, residue_eq_zero_iff]

theorem ok30_res {x y : Z3} (h : content (x ⨯₃ y) = 1) : ok30 (residue 30 x) (residue 30 y) := by
  unfold ok30
  change (let p := crt 6 5 (by decide) (residue (6*5) x)
          let q := crt 6 5 (by decide) (residue (6*5) y)
          let a := crt 2 3 (by decide) p.1
          let b := crt 2 3 (by decide) q.1
          Qlocal a.1 b.1 ∧ Qlocal a.2 b.2 ∧ Qlocal p.2 q.2)
  rw [crt_residue, crt_residue]
  change Qlocal (crt 2 3 (by decide) (residue (2*3) x)).1 (crt 2 3 (by decide) (residue (2*3) y)).1 ∧
    Qlocal (crt 2 3 (by decide) (residue (2*3) x)).2 (crt 2 3 (by decide) (residue (2*3) y)).2 ∧
    Qlocal (residue 5 x) (residue 5 y)
  rw [crt_residue, crt_residue]
  norm_num [Qlocal, ← residue_cross, residue_eq_zero_iff, h]

theorem card_local_pts (d : ℕ) [NeZero d] :
    Nat.card {x : V d // Plocal x} = d^3 - 1 := by
  classical
  unfold Plocal
  rw [Nat.card_eq_fintype_card]
  have h := Fintype.card_subtype_compl (fun x : V d => x = 0)
  have h1 : Fintype.card {x : V d // x = 0} = 1 := Fintype.card_unique
  rw [h, h1]
  simp [ZMod.card]

theorem card_local_pairs (d : ℕ) [Fact d.Prime] [NeZero d] :
    Nat.card {p : V d × V d // Qlocal p.1 p.2} = (d^3 - 1) * (d^3 - d) := by
  classical
  let f : V d × V d → V d := Prod.fst
  let s := (univ : Finset (V d × V d)).filter fun p => Qlocal p.1 p.2
  let t := (univ : Finset (V d)).erase 0
  have ht : t.card = d^3 - 1 := by simp [t, Fintype.card_fun, ZMod.card]
  have hmaps : ∀ p ∈ s, f p ∈ t := by
    intro p hp
    have hc := (mem_filter.mp hp).2
    simp only [t, f, mem_erase, mem_univ, and_true]
    intro hz
    simp [Qlocal, hz] at hc
  have hcard (x : V d) (hx : x ∈ t) : (s.filter fun p => f p = x).card = d^3 - d := by
    have hx0 : x ≠ 0 := (mem_erase.mp hx).1
    let r : Finset (V d) := univ.image (fun c : ZMod d => c • x)
    have hri : Function.Injective (fun c : ZMod d => c • x) := smul_left_injective (ZMod d) hx0
    have hr : r.card = d := by rw [card_image_of_injective _ hri]; exact ZMod.card d
    have he : s.filter (fun p => f p = x) = (univ \ r).image (fun y => (x,y)) := by
      ext p
      rcases p with ⟨u,v⟩
      simp only [s, f, mem_filter, mem_univ, true_and, mem_image, mem_sdiff, r, Prod.mk.injEq]
      by_cases hu : u = x
      · subst u
        simp only [true_and, and_true]
        rw [Qlocal, crossProduct_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff' hx0]
        simp
      · simp [hu, Ne.symm hu]
    rw [he, card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), card_sdiff_of_subset (subset_univ _), hr]
    simp [Fintype.card_fun, ZMod.card]
  have h := card_eq_sum_card_fiberwise hmaps
  rw [sum_congr rfl hcard, sum_const, smul_eq_mul, ht] at h
  simpa [s, Nat.card_eq_fintype_card, Fintype.card_subtype] using h

theorem card_ok6 : Nat.card {x : V 6 // ok6 x} = 182 := by
  classical
  let e := (crt 2 3 (by decide)).subtypeEquiv
    (p := ok6) (q := fun p : V 2 × V 3 => Plocal p.1 ∧ Plocal p.2) (fun _ => Iff.rfl)
  let e' : {p : V 2 × V 3 // Plocal p.1 ∧ Plocal p.2} ≃
      {x : V 2 // Plocal x} × {x : V 3 // Plocal x} :=
    { toFun := fun p => (⟨p.1.1,p.2.1⟩, ⟨p.1.2,p.2.2⟩)
      invFun := fun p => ⟨(p.1.1,p.2.1),p.1.2,p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e.trans e'), Nat.card_prod, card_local_pts, card_local_pts]
  norm_num

theorem card_ok30 : Nat.card {p : pairV 30 // ok30 p.1 p.2} = 389975040 := by
  classical
  let P : (pairV 2 × pairV 3) × pairV 5 → Prop := fun p =>
    Qlocal p.1.1.1 p.1.1.2 ∧ Qlocal p.1.2.1 p.1.2.2 ∧ Qlocal p.2.1 p.2.2
  let e' : {p : pairV 30 // ok30 p.1 p.2} ≃ {p // P p} :=
    crt30.subtypeEquiv (fun ⟨_,_⟩ => Iff.rfl)
  let e'' : {p // P p} ≃ {p : pairV 2 // Qlocal p.1 p.2} × {p : pairV 3 // Qlocal p.1 p.2} ×
      {p : pairV 5 // Qlocal p.1 p.2} :=
    { toFun := fun p => (⟨p.1.1.1,p.2.1⟩,⟨p.1.1.2,p.2.2.1⟩,⟨p.1.2,p.2.2.2⟩)
      invFun := fun p => ⟨((p.1.1,p.2.1.1),p.2.2.1),p.1.2,p.2.1.2,p.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [Nat.card_congr (e'.trans e''), Nat.card_prod, Nat.card_prod,
    card_local_pairs, card_local_pairs, card_local_pairs]
  norm_num

end E211Counter
end

section
-- Reduction211
open scoped BigOperators Matrix InnerProductSpace
open Finset

namespace E211Counter

theorem realVec_sub (x y : Z3) : realVec (x-y) = realVec x - realVec y := by
  ext i; simp [realVec]

def inPlane (c : R3) (x : Z3) : Prop := c ⬝ᵥ realVec x = 0

theorem inPlane_smul {c : R3} {x : Z3} (d : ℤ) (h : inPlane c x) : inPlane c (d • x) := by
  unfold inPlane at *
  rw [realVec_smul, dotProduct_smul, h, smul_zero]

theorem inPlane_of_smul {c : R3} {x : Z3} {d : ℤ} (hd : d ≠ 0) (h : inPlane c (d • x)) :
    inPlane c x := by
  unfold inPlane at *
  rw [realVec_smul, dotProduct_smul, smul_eq_mul, mul_eq_zero] at h
  exact h.resolve_left (by exact_mod_cast hd)

theorem inPlane_sub {c : R3} {x y : Z3} (hx : inPlane c x) (hy : inPlane c y) : inPlane c (x-y) := by
  unfold inPlane at *
  simp [realVec_sub, dotProduct_sub, hx, hy]

theorem cross_sub_smul (a b : Z3) (j : ℤ) :
    realVec a ⨯₃ realVec (b - j • a) = realVec a ⨯₃ realVec b := by
  rw [realVec_sub, realVec_smul, map_sub, map_smul, cross_self, smul_zero, sub_zero]

theorem divideVec {d : ℕ} {x : Z3} (h : residue d x = 0) : ∃ q : Z3, (d : ℤ) • q = x := by
  have hdiv := (content_dvd d x).mp ((residue_eq_zero_iff d x).mp h)
  refine ⟨fun i => x i / (d : ℤ), ?_⟩
  ext i
  simpa [Pi.smul_apply, mul_comm] using Int.ediv_mul_cancel (hdiv i)

/-- The two successive shortest independent integral vectors of a plane are reduced.
Their cross product is primitive: dependent reductions modulo a prime would give
a still shorter vector by division, possibly after subtracting a multiple of the first. -/
theorem exists_reduced {m : ℕ} {c : R3} {x y : Z3}
    (hx : x ∈ ballInts m) (hy : y ∈ ballInts m) (hx' : inPlane c x) (hy' : inPlane c y)
    (hxy : realVec x ⨯₃ realVec y ≠ 0) :
    ∃ a b : Z3, a ∈ ballInts m ∧ b ∈ ballInts m ∧ inPlane c a ∧ inPlane c b ∧
      ‖eVec a‖ ≤ ‖eVec b‖ ∧ |⟪eVec a, eVec b⟫_ℝ| ≤ ‖eVec a‖^2 / 2 ∧
      content (a ⨯₃ b) = 1 := by
  classical
  let T := (ballInts m).filter fun z => inPlane c z ∧ z ≠ 0
  have hx0 : x ≠ 0 := by rintro rfl; simp [realVec_zero] at hxy
  obtain ⟨a, ha, hamin⟩ := T.exists_min_image (fun z => ‖eVec z‖) ⟨x,mem_filter.mpr ⟨hx,hx',hx0⟩⟩
  have hap := (mem_filter.mp ha).2.1
  have ha0 := (mem_filter.mp ha).2.2
  have haR : realVec a ≠ 0 := fun h => ha0 (realVec_inj (h.trans realVec_zero.symm))
  have haE : eVec a ≠ 0 := fun h => ha0 (eVec_inj (h.trans eVec_zero.symm))
  have haN : 0 < ‖eVec a‖ := norm_pos_iff.mpr haE
  let U := (ballInts m).filter fun z => inPlane c z ∧ realVec a ⨯₃ realVec z ≠ 0
  have hU : U.Nonempty := by
    by_cases h : realVec a ⨯₃ realVec x = 0
    · refine ⟨y,mem_filter.mpr ⟨hy,hy',?_⟩⟩
      intro hy0
      have dep (z : Z3) (hz : realVec a ⨯₃ realVec z = 0) : ∃ t : ℝ, t • realVec a = realVec z := by
        by_contra! hdep
        exact (crossProduct_ne_zero_iff_linearIndependent.mpr (LinearIndependent.pair_iff' haR |>.mpr hdep)) hz
      obtain ⟨s, hs⟩ := dep x h
      obtain ⟨t, ht⟩ := dep y hy0
      apply hxy
      rw [← hs, ← ht, map_smul, map_smul, LinearMap.smul_apply, cross_self, smul_zero, smul_zero]
    · exact ⟨x,mem_filter.mpr ⟨hx,hx',h⟩⟩
  obtain ⟨b,hb,hbmin⟩ := U.exists_min_image (fun z => ‖eVec z‖) hU
  have hbp := (mem_filter.mp hb).2.1
  have hab := (mem_filter.mp hb).2.2
  have hb0 : b ≠ 0 := by rintro rfl; simp [realVec_zero] at hab
  have haB := (mem_filter.mp ha).1
  have hbB := (mem_filter.mp hb).1
  have hnorm := hamin b (mem_filter.mpr ⟨hbB, hbp, hb0⟩)
  have hbN := haN.trans_le hnorm
  have hn (z : Z3) (hz : inPlane c z) (hz' : realVec a ⨯₃ realVec z ≠ 0) : ‖eVec b‖ ≤ ‖eVec z‖ := by
    by_cases hzr : ‖eVec z‖ ≤ (m : ℝ)
    · exact hbmin z (mem_filter.mpr ⟨mem_ballInts.mpr hzr,hz,hz'⟩)
    · exact (mem_ballInts.mp hbB).trans (le_of_not_ge hzr)
  have hdprod : |⟪eVec a, eVec b⟫_ℝ| ≤ ‖eVec a‖^2 / 2 := by
    have h₁ := hn (b - (1 : ℤ) • a) (inPlane_sub hbp (inPlane_smul _ hap)) (by rwa [cross_sub_smul])
    have h₂ := hn (b - (-1 : ℤ) • a) (inPlane_sub hbp (inPlane_smul _ hap)) (by rwa [cross_sub_smul])
    simp only [eVec_sub, one_smul] at h₁
    simp only [neg_smul, one_smul, sub_neg_eq_add, eVec_add] at h₂
    have he₁ := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    have he₂ := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
    rw [norm_sub_sq_real, real_inner_comm] at he₁
    rw [norm_add_sq_real, real_inner_comm] at he₂
    rw [abs_le]
    constructor <;> linarith
  refine ⟨a,b,haB,hbB,hap,hbp,hnorm,hdprod,?_⟩
  by_contra hc
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
  have : Fact p.Prime := ⟨hp⟩
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : NeZero p := ⟨hp.ne_zero⟩
  have hra : residue p a ≠ 0 := by
    intro hzero
    obtain ⟨q,hq⟩ := divideVec hzero
    have hq0 : q ≠ 0 := by rintro rfl; simp at hq; exact ha0 hq.symm
    have hqn : ‖eVec q‖ < ‖eVec a‖ := by
      have h := congrArg (fun z => ‖eVec z‖) hq
      simp only [eVec_smul, norm_smul, Int.cast_natCast, Real.norm_eq_abs, abs_of_nonneg hp0] at h
      have hqN : 0 < ‖eVec q‖ := norm_pos_iff.mpr fun he => hq0 (eVec_inj (he.trans eVec_zero.symm))
      rw [← h]
      nlinarith only [mul_pos (sub_pos.mpr hp') hqN]
    have hqt : q ∈ T := mem_filter.mpr ⟨mem_ballInts.mpr (hqn.le.trans (mem_ballInts.mp haB)),
      inPlane_of_smul hpZ (hq ▸ hap), hq0⟩
    exact hqn.not_ge (hamin q hqt)
  have hrs : residue p a ⨯₃ residue p b = 0 := by
    rw [← residue_cross, residue_eq_zero_iff]; exact hpd
  obtain ⟨t, ht⟩ : ∃ t : ZMod p, t • residue p a = residue p b := by
    by_contra! h
    exact (crossProduct_ne_zero_iff_linearIndependent.mpr (LinearIndependent.pair_iff' hra |>.mpr h)) hrs
  let j := t.val
  have hj : (j : ℝ) + 1 ≤ p := by exact_mod_cast t.val_lt
  have hzero : residue p (b - (j : ℤ) • a) = 0 := by
    ext i
    have hi : (t : ZMod p) * (a i : ZMod p) = (b i : ZMod p) := congrFun ht i
    change ((b i - (j : ℤ) * a i : ℤ) : ZMod p) = 0
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, show (j : ZMod p) = t from ZMod.natCast_zmod_val t, hi, sub_self]
  obtain ⟨q, hq⟩ := divideVec hzero
  have hqp : inPlane c q := inPlane_of_smul hpZ (hq ▸ inPlane_sub hbp (inPlane_smul _ hap))
  have hqa : realVec a ⨯₃ realVec q ≠ 0 := by
    intro hn0
    apply hab
    rw [← cross_sub_smul a b (j : ℤ), ← hq, realVec_smul, map_smul, hn0, smul_zero]
  have hqn := hn q hqp hqa
  have hlen : (p : ℝ) * ‖eVec q‖ = ‖eVec b - (j : ℝ) • eVec a‖ := by
    have h := congrArg (fun z => ‖eVec z‖) hq
    simpa only [eVec_smul, norm_smul, Int.cast_natCast, Real.norm_eq_abs, abs_of_nonneg hp0,
      eVec_sub] using h
  have hsq : ‖eVec b - (j : ℝ) • eVec a‖ ^ 2 ≤ (1 + (j : ℝ)^2 + j) * ‖eVec b‖^2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg j), mul_pow]
    have h₂ : -(‖eVec a‖^2 / 2) ≤ ⟪eVec a,eVec b⟫_ℝ := (abs_le.mp hdprod).1
    have hh := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α := ℝ) j)
    have hpos : 0 ≤ (j : ℝ)^2 + j := by positivity
    have hh' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hpos
    nlinarith only [hh,hh']
  have hcoef : 1 + (j : ℝ)^2 + j < (p : ℝ)^2 := by
    have h₁ := mul_nonneg (show 0 ≤ (j : ℝ) by positivity) (show 0 ≤ (p : ℝ) - 1 - j by linarith)
    have h₂ := mul_nonneg (show 0 ≤ (p : ℝ) by positivity) (show 0 ≤ (p : ℝ) - 1 - j by linarith)
    nlinarith only [h₁,h₂,hp']
  have hm := pow_le_pow_left₀ (by positivity : 0 ≤ (p : ℝ) * ‖eVec b‖)
    (mul_le_mul_of_nonneg_left hqn (Nat.cast_nonneg p)) 2
  rw [hlen, mul_pow] at hm
  exact (not_lt_of_ge (hm.trans hsq)) (mul_lt_mul_of_pos_right hcoef (by positivity))

noncomputable def reduced (m : ℕ) : Finset (Z3 × Z3) := by
  classical
  exact ((ballInts m) ×ˢ (ballInts m)).filter (fun p => ‖eVec p.1‖ ≤ ‖eVec p.2‖ ∧
    |⟪eVec p.1,eVec p.2⟫_ℝ| ≤ ‖eVec p.1‖^2/2 ∧ content (p.1 ⨯₃ p.2) = 1)

theorem mem_reduced {m : ℕ} {a b : Z3} : (a,b) ∈ reduced m ↔
    ‖eVec b‖ ≤ m ∧ ‖eVec a‖ ≤ ‖eVec b‖ ∧
    |⟪eVec a,eVec b⟫_ℝ| ≤ ‖eVec a‖^2/2 ∧ content (a ⨯₃ b) = 1 := by
  classical
  simp only [reduced, mem_filter, mem_product, mem_ballInts]
  constructor
  · tauto
  · rintro ⟨hb,hab,hh,hc⟩
    exact ⟨⟨hab.trans hb,hb⟩,hab,hh,hc⟩

end E211Counter
end

section
-- Projective211
noncomputable section
open scoped Matrix Classical
open Finset

namespace E211Counter

abbrev PlanePoint := EuclideanSpace ℝ (Fin 2)
abbrev PlaneLine := AffineSubspace ℝ PlanePoint

def denominator (t : ℝ) (x : Z3) : ℝ := (x 0 : ℝ) + t * (x 1 : ℝ) + t^2 * (x 2 : ℝ)

def project (t : ℝ) (x : Z3) : PlanePoint :=
  WithLp.toLp 2 ![(x 1 : ℝ) / denominator t x, (x 2 : ℝ) / denominator t x]

def liftPoint (t : ℝ) (p : PlanePoint) : R3 := ![1-t*p 0-t^2*p 1, p 0, p 1]

lemma exists_chart (m : ℕ) : ∃ t : ℝ, ∀ x ∈ ballInts m, x ≠ 0 → denominator t x ≠ 0 := by
  classical
  let P := (ballInts m).erase (0 : Z3)
  let f (x : Z3) : Polynomial ℝ :=
    Polynomial.C (x 0 : ℝ) + Polynomial.C (x 1 : ℝ) * Polynomial.X +
      Polynomial.C (x 2 : ℝ) * Polynomial.X ^ 2
  have hf (x : Z3) (hx : x ∈ P) : f x ≠ 0 := by
    intro h
    apply (mem_erase.mp hx).1
    have h0 := congrArg (fun p : Polynomial ℝ => p.coeff 0) h
    have h1 := congrArg (fun p : Polynomial ℝ => p.coeff 1) h
    have h2 := congrArg (fun p : Polynomial ℝ => p.coeff 2) h
    simp only [f, Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_zero] at h0 h1 h2
    norm_num at h0 h1 h2
    ext i
    fin_cases i
    · exact_mod_cast h0
    · exact_mod_cast h1
    · exact_mod_cast h2
  let bad := P.biUnion (fun x => (f x).roots.toFinset)
  obtain ⟨t,ht⟩ := Infinite.exists_notMem_finset bad
  refine ⟨t, fun x hx hx0 h => ht (mem_biUnion.mpr ⟨x,mem_erase.mpr ⟨hx0,hx⟩,?_⟩)⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hf x (mem_erase.mpr ⟨hx0,hx⟩))]
  simpa [f, Polynomial.IsRoot, denominator, mul_comm] using h

lemma lift_project {t : ℝ} {x : Z3} (h : denominator t x ≠ 0) :
    liftPoint t (project t x) = (denominator t x)⁻¹ • realVec x := by
  ext i
  fin_cases i
  · change 1-t*((x 1 : ℝ)/denominator t x)-t^2*((x 2 : ℝ)/denominator t x) = _
    change _ = (denominator t x)⁻¹ * (x 0 : ℝ)
    field_simp
    unfold denominator
    ring
  · change (x 1 : ℝ)/denominator t x = (denominator t x)⁻¹ * (x 1 : ℝ)
    ring
  · change (x 2 : ℝ)/denominator t x = (denominator t x)⁻¹ * (x 2 : ℝ)
    ring

lemma project_injOn {T : Finset Z3} {t : ℝ}
    (ht : ∀ x ∈ T, denominator t x ≠ 0) (hprim : ∀ x ∈ T, content x = 1 ∧ positive x) :
    Set.InjOn (project t) T := by
  intro x hx y hy he
  have h := congrArg (liftPoint t) he
  rw [lift_project (ht x hx), lift_project (ht y hy)] at h
  have hprop : realVec y = (denominator t y * (denominator t x)⁻¹) • realVec x := by
    rw [← smul_smul, h, smul_smul, mul_inv_cancel₀ (ht y hy), one_smul]
  rcases primitive_prop (hprim x hx).1 (hprim y hy).1 hprop with h | h
  · exact h.symm
  · exact (not_positive_neg (hprim x hx).2 (h ▸ (hprim y hy).2)).elim

lemma lift_lineMap (t r : ℝ) (p q : PlanePoint) :
    liftPoint t (AffineMap.lineMap p q r) = (1-r) • liftPoint t p + r • liftPoint t q := by
  rw [AffineMap.lineMap_apply_module]
  ext i
  fin_cases i <;> simp [liftPoint, PiLp.add_apply, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul] <;> ring

lemma inPlane_of_project_mem {t : ℝ} {c : R3} {a b x : Z3}
    (ha : denominator t a ≠ 0) (hb : denominator t b ≠ 0) (hx : denominator t x ≠ 0)
    (hap : inPlane c a) (hbp : inPlane c b)
    (hm : project t x ∈ line[ℝ, project t a, project t b]) : inPlane c x := by
  rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hm with ⟨r, hr⟩
  have he := congrArg (liftPoint t) hr
  rw [lift_lineMap, lift_project ha, lift_project hb, lift_project hx] at he
  unfold inPlane at *
  have hh := congrArg (fun z : R3 => c ⬝ᵥ z) he
  simp only [dotProduct_add, dotProduct_smul, hap, hbp, smul_eq_mul, mul_zero, add_zero] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left (inv_ne_zero hx)

lemma mem_of_inPlane {t : ℝ} {c : R3} {a b x : Z3}
    (hc : c ≠ 0) (ha : denominator t a ≠ 0) (hb : denominator t b ≠ 0) (hx : denominator t x ≠ 0)
    (hn : project t a ≠ project t b) (hap : inPlane c a) (hbp : inPlane c b)
    (hxp : inPlane c x) : project t x ∈ line[ℝ, project t a, project t b] := by
  let f : PlanePoint → ℝ := fun p => c ⬝ᵥ liftPoint t p
  have hz (y : Z3) (hy : denominator t y ≠ 0) (h : inPlane c y) : f (project t y) = 0 := by
    dsimp only [f]
    rw [lift_project hy, dotProduct_smul, h, smul_zero]
  let p := project t a
  let q := project t b
  let v := project t x
  have hp : f p = 0 := hz a ha hap
  have hq : f q = 0 := hz b hb hbp
  have hv : f v = 0 := hz x hx hxp
  let A := c 1 - t * c 0
  let B := c 2 - t^2 * c 0
  have he (y : PlanePoint) : f y = c 0 + A*y 0 + B*y 1 := by
    unfold f liftPoint A B
    rw [Matrix.vec3_dotProduct]
    simp
    ring
  rw [he] at hp hq hv
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_contra! h
    have h0 : c 0 = 0 := by simpa [h.1,h.2] using hp
    apply hc
    ext i
    have h1 : c 1 = 0 := by simpa [A,h0] using h.1
    have h2 : c 2 = 0 := by simpa [B,h0] using h.2
    fin_cases i <;> assumption
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  rcases hAB with hA | hB
  · have hd : q 1 - p 1 ≠ 0 := by
      intro hn1
      have hn0 : p 0 = q 0 := by
        apply mul_left_cancel₀ hA
        rw [sub_eq_zero.mp hn1] at hq
        linear_combination hp - hq
      apply hn
      ext i
      fin_cases i
      · exact hn0
      · exact (sub_eq_zero.mp hn1).symm
    let r := (v 1 - p 1)/(q 1 - p 1)
    have h1 : r*(q 1 - p 1) = v 1 - p 1 := div_mul_cancel₀ _ hd
    have h0 : r*(q 0 - p 0) = v 0 - p 0 := by
      apply mul_left_cancel₀ hA
      linear_combination r * (hq - hp) - (hv - hp) - B * h1
    refine ⟨r,?_⟩
    rw [AffineMap.lineMap_apply_module']
    ext i
    fin_cases i
    · change r*(q 0 - p 0)+p 0 = v 0
      linarith [h0]
    · change r*(q 1 - p 1)+p 1 = v 1
      linarith [h1]
  · have hd : q 0 - p 0 ≠ 0 := by
      intro hn0
      have hn1 : p 1 = q 1 := by
        apply mul_left_cancel₀ hB
        rw [sub_eq_zero.mp hn0] at hq
        linear_combination hp - hq
      apply hn
      ext i
      fin_cases i
      · exact (sub_eq_zero.mp hn0).symm
      · exact hn1
    let r := (v 0 - p 0)/(q 0 - p 0)
    have h0 : r*(q 0 - p 0) = v 0 - p 0 := div_mul_cancel₀ _ hd
    have h1 : r*(q 1 - p 1) = v 1 - p 1 := by
      apply mul_left_cancel₀ hB
      linear_combination r * (hq - hp) - (hv - hp) - A * h0
    refine ⟨r,?_⟩
    rw [AffineMap.lineMap_apply_module']
    ext i
    fin_cases i
    · change r*(q 0 - p 0)+p 0 = v 0
      linarith [h0]
    · change r*(q 1 - p 1)+p 1 = v 1
      linarith [h1]

lemma plane_slice_card {m : ℕ} {c : R3} (hc : c ≠ 0) (T : Finset Z3)
    (hT : ∀ x ∈ T, x ∈ ballInts m ∧ inPlane c x) : T.card ≤ (2*m+1)^2 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i : Fin 3, c i ≠ 0 := by
    by_contra! h
    exact hc (funext h)
  let target := Fintype.piFinset fun _ : Fin 2 => Icc (-(m : ℤ)) (m : ℤ)
  have htarget : target.card = (2*m+1)^2 := by
    rw [Fintype.card_piFinset]
    have he : (Icc (-(m : ℤ)) (m : ℤ)).card = 2*m+1 := by rw [Int.card_Icc]; omega
    simp [he]
  rw [← htarget]
  apply card_le_card_of_injOn (fun (x : Z3) (j : Fin 2) => x (i.succAbove j))
  · intro x hx
    change (fun j : Fin 2 => x (i.succAbove j)) ∈ target
    simp only [target, Fintype.mem_piFinset, mem_Icc]
    intro j
    have h : ((x (i.succAbove j)).natAbs : ℝ) ≤ m := (int_coord_le_norm x _).trans (mem_ballInts.mp (hT x hx).1)
    have h' : (x (i.succAbove j)).natAbs ≤ m := by exact_mod_cast h
    omega
  · intro x hx y hy he
    have hxy (j : Fin 3) (hj : j ≠ i) : x j = y j := by
      obtain ⟨a,rfl⟩ : j ∈ Set.range i.succAbove := by simpa [Fin.range_succAbove] using hj
      exact congrFun he a
    have hv : realVec x - realVec y = Pi.single i ((x i : ℝ) - (y i : ℝ)) := by
      ext j
      by_cases hj : j = i
      · subst j; simp [realVec]
      · simp [realVec, hxy j hj, Pi.single_eq_of_ne hj]
    have hsub : c ⬝ᵥ (realVec x - realVec y) = 0 := by rw [dotProduct_sub, (hT x hx).2, (hT y hy).2, sub_self]
    rw [hv, dotProduct_single] at hsub
    have hi' := sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left hi)
    ext j
    by_cases hj : j = i
    · subst j; exact_mod_cast hi'
    · exact hxy j hj

lemma line_eq_of_pair {L : PlaneLine} (hL : EuclideanGeometry.IsLine L)
    {p q : PlanePoint} (hp : p ∈ L) (hq : q ∈ L) (hn : p ≠ q) : L = line[ℝ,p,q] := by
  have hd : (line[ℝ,p,q]).direction = Submodule.span ℝ {q-p} := by
    rw [direction_affineSpan, vectorSpan_pair_rev]
    rfl
  have hqp : q - p ∈ L.direction := L.vsub_mem_direction hq hp
  have he := eq_span_singleton_of_mem_of_finrank_eq_one hL hqp (sub_ne_zero.mpr hn.symm)
  exact (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le (hd.trans he.symm)
    ⟨p,left_mem_affineSpan_pair _ _ _⟩ (affineSpan_pair_le_of_mem_of_mem hp hq)).symm

lemma line_cap {m : ℕ} {t : ℝ} (hchart : ∀ x ∈ ballInts m, x ≠ 0 → denominator t x ≠ 0)
    (L : PlaneLine) (hL : EuclideanGeometry.IsLine L) :
    (((points m).image (project t)).filter fun p => p ∈ L).card ≤ (2*m+1)^2 := by
  classical
  let T := (points m).filter fun x => project t x ∈ L
  have hmap (x : Z3) (hx : x ∈ points m) : denominator t x ≠ 0 := by
    obtain ⟨hh,hc,_⟩ := mem_points.mp hx
    exact hchart x (mem_ballInts.mpr hh) (by rintro rfl; simp [content] at hc)
  have hpi : Set.InjOn (project t) (points m) := project_injOn hmap
    (fun _ hx => (mem_points.mp hx).2)
  have hsur : Set.SurjOn (project t) T (((points m).image (project t)).filter fun p => p ∈ L) := by
    intro p hp
    obtain ⟨⟨x,hx,rfl⟩,hp⟩ := (mem_filter.mp hp : p ∈ (points m).image (project t) ∧ p ∈ L)
      |>.imp_left mem_image.mp
    exact ⟨x,mem_filter.mpr ⟨hx,hp⟩,rfl⟩
  apply (card_le_card_of_surjOn _ hsur).trans
  by_cases hcard : T.card ≤ 1
  · exact hcard.trans (one_le_pow₀ (by omega))
  obtain ⟨x,y,hx,hy,hxy⟩ := one_lt_card_iff.mp (lt_of_not_ge hcard)
  have hx' := (mem_filter.mp hx).1
  have hy' := (mem_filter.mp hy).1
  have hd : L = line[ℝ, project t x, project t y] :=
    line_eq_of_pair hL (mem_filter.mp hx).2 (mem_filter.mp hy).2 (fun h => hxy (hpi hx' hy' h))
  let c := realVec x ⨯₃ realVec y
  refine plane_slice_card (cross_ne_of_points hx' hy' hxy) T fun z hz => ?_
  have hz' := (mem_filter.mp hz).1
  refine ⟨mem_ballInts.mpr (mem_points.mp hz').1, inPlane_of_project_mem (hmap x hx') (hmap y hy') (hmap z hz') ?_ ?_ ?_⟩
  · simp [inPlane, c, dotProduct_comm]
  · simp [inPlane, c, dotProduct_comm]
  · rw [← hd]; exact (mem_filter.mp hz).2

def reducedLine (t : ℝ) (p : Z3 × Z3) : PlaneLine := line[ℝ, project t p.1, project t p.2]

lemma lines_le_reduced {m : ℕ} {t : ℝ} (hchart : ∀ x ∈ ballInts m, x ≠ 0 → denominator t x ≠ 0) :
    (Erdos211.determinedLines ((points m).image (project t))).card * 4 ≤ (reduced m).card := by
  classical
  let s := (points m).image (project t)
  let T := Erdos211.determinedLines s
  have hxB (x : Z3) (hx : x ∈ points m) : x ∈ ballInts m := mem_ballInts.mpr (mem_points.mp hx).1
  have hxD (x : Z3) (hx : x ∈ points m) : denominator t x ≠ 0 :=
    hchart x (hxB x hx) (by rintro rfl; simpa [content] using (mem_points.mp hx).2.1)
  have hs (L : PlaneLine) (hL : L ∈ T) : ∃ a b : Z3, (a,b) ∈ reduced m ∧
      (a,-b) ∈ reduced m ∧ (-a,b) ∈ reduced m ∧ (-a,-b) ∈ reduced m ∧
      a ≠ -a ∧ b ≠ -b ∧ reducedLine t (a,b) = L ∧ reducedLine t (a,-b) = L ∧
      reducedLine t (-a,b) = L ∧ reducedLine t (-a,-b) = L := by
    obtain ⟨⟨p,q⟩,hpq,rfl⟩ := mem_image.mp hL
    obtain ⟨hp,hq,hn⟩ := mem_offDiag.mp hpq
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hq
    change project t x ≠ project t y at hn
    have hxy : x ≠ y := fun h => hn (congrArg (project t) h)
    let c := realVec x ⨯₃ realVec y
    have hc : c ≠ 0 := cross_ne_of_points hx hy hxy
    obtain ⟨a,b,ha,hb,hap,hbp,hab,hd,hcont⟩ := exists_reduced (hxB x hx) (hxB y hy)
      (c := c) (by simp [inPlane,c,dotProduct_comm]) (by simp [inPlane,c,dotProduct_comm]) hc
    have hcr : realVec a ⨯₃ realVec b ≠ 0 := by
      intro he
      rw [← realVec_cross] at he
      have hh := realVec_inj (he.trans realVec_zero.symm)
      simp [hh,content] at hcont
    have hna : a ≠ 0 := by rintro rfl; simp [realVec_zero] at hcr
    have hnb : b ≠ 0 := by rintro rfl; simp [realVec_zero] at hcr
    have hda := hchart a ha hna
    have hdb := hchart b hb hnb
    have hproj : project t a ≠ project t b := by
      intro he
      have hh := congrArg (liftPoint t) he
      rw [lift_project hda, lift_project hdb] at hh
      have he' : realVec b = (denominator t b * (denominator t a)⁻¹) • realVec a := by
        rw [← smul_smul, hh, smul_smul, mul_inv_cancel₀ hdb, one_smul]
      exact hcr (by rw [he',map_smul,cross_self,smul_zero])
    have hma := mem_of_inPlane (t := t) hc (hxD x hx) (hxD y hy) hda hn
      (by simp [inPlane,c,dotProduct_comm]) (by simp [inPlane,c,dotProduct_comm]) hap
    have hmb := mem_of_inPlane (t := t) hc (hxD x hx) (hxD y hy) hdb hn
      (by simp [inPlane,c,dotProduct_comm]) (by simp [inPlane,c,dotProduct_comm]) hbp
    have he := affineSpan_pair_eq_of_mem_of_mem_of_ne hma hmb hproj
    have hsign (z : Z3) (hz : denominator t z ≠ 0) : project t (-z) = project t z := by
      have hh : denominator t (-z) = -denominator t z := by simp [denominator]; ring
      ext i
      fin_cases i <;> simp [project,hh]
    have hneq (z : Z3) (hz : z ≠ 0) : z ≠ -z := by
      intro hh; apply hz; ext i
      have hh' : z i = -(z i) := congrFun hh i
      change z i = 0
      omega
    have hcont' : content (b ⨯₃ a) = 1 := by rw [← cross_anticomm, content_neg, hcont]
    refine ⟨a,b,?_,?_,?_,?_,hneq a hna,hneq b hnb,he,?_,?_,?_⟩
    · exact mem_reduced.mpr ⟨mem_ballInts.mp hb,hab,hd,hcont⟩
    · simp [mem_reduced, eVec_neg, map_neg, mem_ballInts.mp hb,hab,hd,hcont']
    · simp [mem_reduced, eVec_neg, map_neg, LinearMap.neg_apply, mem_ballInts.mp hb,hab,hd,hcont']
    · simp [mem_reduced, eVec_neg, map_neg, LinearMap.neg_apply, content_neg, mem_ballInts.mp hb,hab,hd,hcont]
    · simpa [reducedLine, hsign b hdb] using he
    · simpa [reducedLine, hsign a hda] using he
    · simpa [reducedLine, hsign a hda, hsign b hdb] using he
  let D (L : PlaneLine) := (reduced m).filter fun p => reducedLine t p = L
  have hD (L : PlaneLine) (hL : L ∈ T) : 4 ≤ (D L).card := by
    obtain ⟨a,b,h1,h2,h3,h4,ha,hb,e1,e2,e3,e4⟩ := hs L hL
    let A : Finset Z3 := {a, -a}
    let B : Finset Z3 := {b, -b}
    have hAB : A ×ˢ B ⊆ D L := by
      intro p hp
      obtain ⟨ha',hb'⟩ := mem_product.mp hp
      have hh : p.1 = a ∨ p.1 = -a := by simpa [A] using ha'
      have hk : p.2 = b ∨ p.2 = -b := by simpa [B] using hb'
      rcases p with ⟨u,v⟩
      rcases hh with hu|hu <;> rcases hk with hv|hv <;> cases hu <;> cases hv <;>
        exact mem_filter.mpr ⟨by assumption,by assumption⟩
    have he : (A ×ˢ B).card = 4 := by simp [A,B,card_product,ha,hb,Finset.card_pair]
    exact he ▸ card_le_card hAB
  have hsum := sum_card_fiberwise_eq_card_filter (reduced m) T (reducedLine t)
  calc
    T.card * 4 = ∑ L ∈ T, (4 : ℕ) := by simp
    _ ≤ ∑ L ∈ T, (D L).card := sum_le_sum hD
    _ ≤ (reduced m).card := hsum.trans_le (card_filter_le _ _)

end E211Counter
end

section
-- CountBoxes211
noncomputable section
open scoped BigOperators Topology ENNReal Pointwise
open Filter MeasureTheory Metric

namespace E211Counter

section Cubes
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Half-open boxes on a grid. The lattice points of a fixed residue class index
disjoint boxes of side `d`; the whole boxes are within that distance of their centers. -/
def cell (h : ℝ) (x : ι → ℤ) : Set (ι → ℝ) :=
  Set.univ.pi fun i => Set.Ioc (x i : ℝ) ((x i : ℝ) + h)

lemma mem_cell {h : ℝ} {x : ι → ℤ} {y : ι → ℝ} : y ∈ cell h x ↔
    ∀ i, (x i : ℝ) < y i ∧ y i ≤ (x i : ℝ) + h := by simp [cell]

lemma measurable_cell (h : ℝ) (x : ι → ℤ) : MeasurableSet (cell h x) := by
  apply MeasurableSet.pi (Set.toFinite _).countable
  simp

lemma volume_cell {h : ℝ} (hh : 0 ≤ h) (x : ι → ℤ) :
    volume.real (cell h x) = h ^ Fintype.card ι := by
  rw [measureReal_def, cell, Real.volume_pi_Ioc_toReal (by intro i; dsimp; linarith)]
  simp

lemma cell_dist {h : ℝ} (hh : 0 ≤ h) {x : ι → ℤ} {y : ι → ℝ}
    (hy : y ∈ cell h x) : ‖y - (fun i => (x i : ℝ))‖ ≤ h := by
  rw [pi_norm_le_iff_of_nonneg hh]
  intro i
  have hi := mem_cell.mp hy i
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hi.1, hi.2]

lemma cell_disjoint {d : ℕ} (hd : 0 < d) {x y : ι → ℤ}
    (hxy : x ≠ y) (hmod : ∀ i, (x i : ZMod d) = (y i : ZMod d)) :
    Disjoint (cell (d : ℝ) x) (cell (d : ℝ) y) := by
  rw [Set.disjoint_left]
  intro p hp hq
  apply hxy
  ext i
  have he : ((x i - y i : ℤ) : ZMod d) = 0 := by simp [hmod]
  obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
  have h1 := mem_cell.mp hp i
  have h2 := mem_cell.mp hq i
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hbr : (x i : ℝ) - (y i : ℝ) = (d : ℝ) * (b : ℝ) := by exact_mod_cast hb
  have hb0 : b = 0 := by
    by_contra h
    have hh : b ≤ -1 ∨ 1 ≤ b := by omega
    rcases hh with h | h
    · have h' : (b : ℝ) ≤ -1 := by exact_mod_cast h
      have hm := mul_le_mul_of_nonneg_left h' hd'.le
      linarith [h1.1,h1.2,h2.1,h2.2]
    · have h' : (1 : ℝ) ≤ b := by exact_mod_cast h
      have hm := mul_le_mul_of_nonneg_left h' hd'.le
      linarith [h1.1,h1.2,h2.1,h2.2]
  rw [hb0, mul_zero] at hb
  exact sub_eq_zero.mp hb

lemma volume_cells {d : ℕ} (hd : 0 < d) (T : Finset (ι → ℤ))
    (he : ∀ x ∈ T, ∀ y ∈ T, ∀ i, (x i : ZMod d) = (y i : ZMod d)) :
    volume.real (⋃ x ∈ T, cell (d : ℝ) x) = (T.card : ℝ) * (d : ℝ)^Fintype.card ι := by
  have hfin : ∀ x ∈ T, volume (cell (d : ℝ) x) ≠ ∞ := by
    intro x _
    rw [cell, Real.volume_pi_Ioc]
    exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  rw [measureReal_biUnion_finset (fun x hx y hy hne => cell_disjoint hd hne (he x hx y hy))
    (fun x _ => measurable_cell _ _) hfin]
  simp [volume_cell]

def ri (x : ι → ℤ) : ι → ℝ := fun i => x i

lemma scaled_volume {K : Set (ι → ℝ)} (r : ℝ) (hr : 0 ≤ r) :
    volume.real (r • K) = r ^ Fintype.card ι * volume.real K := by
  rw [measureReal_def, measureReal_def, Measure.addHaar_smul_of_nonneg _ hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr _), Module.finrank_pi_fintype]
  simp

open scoped Pointwise in
lemma count_le_thickening {d : ℕ} (hd : 0 < d) {m : ℝ} (hm : 0 < m)
    (T : Finset (ι → ℤ)) (K : Set (ι → ℝ)) (hK : Bornology.IsBounded K)
    (he : ∀ x ∈ T, ∀ y ∈ T, ∀ i, (x i : ZMod d) = (y i : ZMod d))
    (hT : ∀ x ∈ T, m⁻¹ • ri x ∈ K) :
    (T.card : ℝ) * (d : ℝ)^Fintype.card ι ≤
      m ^ Fintype.card ι * volume.real (cthickening ((d : ℝ)/m) K) := by
  rw [← scaled_volume m hm.le, ← volume_cells hd T he]
  apply measureReal_mono
  · intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hy⟩ := hy
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hm.ne']
    apply mem_cthickening_of_dist_le _ _ _ _ (hT x hx)
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hm, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (cell_dist (Nat.cast_nonneg _) hy) (inv_nonneg.mpr hm.le)
  · have hc : Bornology.IsBounded (cthickening ((d : ℝ)/m) K) := hK.cthickening
    exact (hc.smul₀ m).measure_lt_top.ne

lemma eventual_thickening_lt (K : Set (ι → ℝ)) (hK : IsCompact K) (d : ℕ)
    {B : ℝ} (hB : volume.real K < B) :
    ∀ᶠ m : ℕ in atTop, volume.real (cthickening ((d : ℝ)/(m : ℝ)) K) < B := by
  have hh := tendsto_measure_cthickening_of_isCompact (μ := volume) hK
  have hh' := (ENNReal.tendsto_toReal hK.measure_lt_top.ne).comp hh
  have hm : Tendsto (fun m : ℕ => (d : ℝ)/(m : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (d : ℝ)
  exact (hh'.comp hm).eventually_lt_const hB

end Cubes

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def volUnit : ℝ := 4 * Real.pi / 3

lemma volUnit_pos : 0 < volUnit := by unfold volUnit; positivity

lemma real_volume_ball3 (r : ℝ) (hr : 0 ≤ r) :
    volume.real (Metric.closedBall (0 : E3) r) = volUnit * r^3 := by
  rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (by positivity)]
  unfold volUnit
  ring

def realBall (r : ℝ) : Set R3 := WithLp.toLp 2 ⁻¹' Metric.closedBall (0 : E3) r

lemma mem_realBall {r : ℝ} {x : R3} : x ∈ realBall r ↔ ‖(WithLp.toLp 2 x : E3)‖ ≤ r := by
  simp [realBall]

lemma realBall_compact (r : ℝ) : IsCompact (realBall r) := by
  have h : realBall r = WithLp.ofLp '' Metric.closedBall (0 : E3) r := by
    ext x
    constructor
    · intro hx
      exact ⟨WithLp.toLp 2 x,hx,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact hy
  rw [h]
  exact (isCompact_closedBall _ _).image (PiLp.continuous_ofLp 2 _)

lemma realBall_volume (r : ℝ) (hr : 0 ≤ r) : volume.real (realBall r) = volUnit * r^3 := by
  rw [realBall, (PiLp.volume_preserving_toLp (Fin 3)).measureReal_preimage
    measurableSet_closedBall.nullMeasurableSet, real_volume_ball3 r hr]

lemma eVec_norm_le_coord (x : E3) (c : ℝ) (hc : 0 ≤ c) (h : ∀ i, |x i| ≤ c) :
    ‖x‖ ≤ 2*c := by
  have hi (i : Fin 3) : x i ^ 2 ≤ c^2 := by
    rw [← sq_abs (x i)]
    exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  have he : ‖x‖^2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
  nlinarith only [he, hi 0, hi 1, hi 2, sq_nonneg c]

lemma ballInts_upper {r : ℝ} (hr : 0 ≤ r) :
    ((ballInts r).card : ℝ) ≤ volUnit * (r+2)^3 := by
  classical
  rw [← realBall_volume (r+2) (by linarith)]
  have he : ∀ x ∈ ballInts r, ∀ y ∈ ballInts r, ∀ i : Fin 3, (x i : ZMod 1) = (y i : ZMod 1) :=
    fun _ _ _ _ _ => Subsingleton.elim _ _
  have hu := volume_cells (by norm_num : 0 < (1 : ℕ)) (ballInts r) he
  simp only [Nat.cast_one, one_pow, mul_one] at hu
  rw [← hu]
  apply measureReal_mono _ (realBall_compact _).measure_lt_top.ne
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x,hx,hy⟩ := hy
  rw [mem_realBall]
  have he' : ‖(WithLp.toLp 2 y : E3) - eVec x‖ ≤ 2*1 := by
    apply eVec_norm_le_coord _ 1 (by norm_num)
    intro i
    change |y i - (x i : ℝ)| ≤ 1
    have hi := mem_cell.mp hy i
    rw [abs_le]; constructor <;> linarith [hi.1,hi.2]
  linarith [norm_le_insert' (WithLp.toLp 2 y : E3) (eVec x), mem_ballInts.mp hx]

lemma ballInts_res_lower {d : ℕ} [NeZero d] (hd : 0 < d) (a : Fin 3 → ZMod d)
    {r : ℝ} (hr : 2*(d : ℝ) ≤ r) :
    volUnit * (r-2*d)^3 ≤
      (((ballInts r).filter (fun x => ∀ i, (x i : ZMod d) = a i)).card : ℝ) * (d : ℝ)^3 := by
  classical
  let T := (ballInts r).filter (fun x => ∀ i, (x i : ZMod d) = a i)
  have hT : ∀ x ∈ T, ∀ y ∈ T, ∀ i : Fin 3, (x i : ZMod d) = (y i : ZMod d) :=
    fun x hx y hy i => ((Finset.mem_filter.mp hx).2 i).trans ((Finset.mem_filter.mp hy).2 i).symm
  have hu := volume_cells hd T hT
  rw [Fintype.card_fin] at hu
  change volUnit * (r-2*d)^3 ≤ (T.card : ℝ) * (d : ℝ)^3
  rw [← hu, ← realBall_volume _ (by linarith)]
  have hb : Bornology.IsBounded (⋃ x ∈ T, cell (d : ℝ) x) := by
    refine (realBall_compact (r+2*d)).isBounded.subset ?_
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x,hx,hy⟩ := hy
    rw [mem_realBall]
    have he : ‖(WithLp.toLp 2 y : E3) - eVec x‖ ≤ 2*d := by
      apply eVec_norm_le_coord _ (d : ℝ) (by positivity)
      intro i
      change |y i - (x i : ℝ)| ≤ (d : ℝ)
      have hi := mem_cell.mp hy i
      rw [abs_le]; constructor <;> linarith [hi.1,hi.2]
    linarith [norm_le_insert' (WithLp.toLp 2 y : E3) (eVec x),
      mem_ballInts.mp (Finset.mem_filter.mp hx).1]
  apply measureReal_mono _ hb.measure_lt_top.ne
  intro y hy
  simp only [Set.mem_iUnion]
  let k : Fin 3 → ℤ := fun i => ⌈(y i - ((a i).val : ℝ)) / (d : ℝ)⌉ - 1
  let x : Z3 := fun i => ((a i).val : ℤ) + (d : ℤ) * k i
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hxy : y ∈ cell (d : ℝ) x := by
    rw [mem_cell]
    intro i
    have h₁ : (k i : ℝ) < (y i - ((a i).val : ℝ)) / (d : ℝ) := by
      apply Int.lt_ceil.mp
      simp [k]
    have h₂ : (y i - ((a i).val : ℝ)) / (d : ℝ) ≤ (k i : ℝ) + 1 := by
      simpa [k] using Int.le_ceil ((y i - ((a i).val : ℝ)) / (d : ℝ))
    have h₁' := (lt_div_iff₀ hd').mp h₁
    have h₂' := (div_le_iff₀ hd').mp h₂
    constructor <;> simp only [x, Int.cast_add, Int.cast_mul, Int.cast_natCast] <;> linarith
  have he : ‖eVec x - (WithLp.toLp 2 y : E3)‖ ≤ 2*d := by
    apply eVec_norm_le_coord _ (d : ℝ) (by positivity)
    intro i
    change |(x i : ℝ) - y i| ≤ (d : ℝ)
    have hi := mem_cell.mp hxy i
    rw [abs_le]; constructor <;> linarith [hi.1,hi.2]
  refine ⟨x, Finset.mem_filter.mpr ⟨mem_ballInts.mpr ?_, ?_⟩, hxy⟩
  · linarith [norm_le_insert' (eVec x) (WithLp.toLp 2 y : E3), mem_realBall.mp hy]
  · intro i
    simp [x, ZMod.natCast_zmod_val]

end E211Counter
end

section
-- PointCount211
noncomputable section
open scoped BigOperators
open Finset

namespace E211Counter

lemma divisor_sum (m : ℕ) (hm : 4 ≤ m) :
    (∑ d ∈ Icc 5 m, ((d : ℝ)⁻¹)^2) ≤ 1/4 - (m : ℝ)⁻¹ ∧
    (∑ d ∈ Icc 5 m, ((d : ℝ)⁻¹)^3) ≤ 1/32 - 1/(2*(m : ℝ)^2) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ j hj IH =>
    have he : Icc 5 (j+1) = insert (j+1) (Icc 5 j) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    have hn : j+1 ∉ Icc 5 j := by simp
    simp only [he, sum_insert hn, Nat.cast_succ]
    have h0 : (0 : ℝ) < j := by positivity
    have h1 : (0 : ℝ) < (j : ℝ)+1 := by positivity
    have hs : ((j : ℝ)+1)⁻¹^2 ≤ (j : ℝ)⁻¹ - ((j : ℝ)+1)⁻¹ := by
      field_simp [h0.ne', h1.ne']
      nlinarith only [h0]
    have hc : ((j : ℝ)+1)⁻¹^3 ≤ 1/(2*(j : ℝ)^2) - 1/(2*((j : ℝ)+1)^2) := by
      field_simp [h0.ne', h1.ne']
      nlinarith only [h0]
    constructor <;> linarith only [hs,hc,IH.1,IH.2]

lemma sum_scaled_balls (m : ℕ) (hm : 12 ≤ m) :
    ∑ d ∈ Icc 5 m, ((ballInts ((m : ℝ)/d)).card : ℝ) ≤
      volUnit * ((m : ℝ)^3/32 + 26*(m : ℝ)^2) := by
  have hm' : (12 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : ((Icc 5 m).card : ℝ) ≤ m := by
    have h : (Icc 5 m).card ≤ m := by rw [Nat.card_Icc]; omega
    exact_mod_cast h
  have hinv : ∑ d ∈ Icc 5 m, (d : ℝ)⁻¹ ≤ m := by
    calc
      _ ≤ ∑ _d ∈ Icc 5 m, (1 : ℝ) := by
        apply sum_le_sum; intro d hd
        have h : 1 ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by have := (mem_Icc.mp hd).1; omega)
        exact inv_le_one_of_one_le₀ h
      _ ≤ _ := by simpa using hc
  have h₂ : ∑ d ∈ Icc 5 m, ((d : ℝ)⁻¹)^2 ≤ 1 :=
    (divisor_sum m (by omega)).1.trans (by linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) m)])
  have h₃ : ∑ d ∈ Icc 5 m, ((d : ℝ)⁻¹)^3 ≤ 1/32 :=
    (divisor_sum m (by omega)).2.trans (by linarith [show 0 ≤ (1 : ℝ)/(2*(m : ℝ)^2) by positivity])
  calc
    _ ≤ ∑ d ∈ Icc 5 m, volUnit * ((m : ℝ)/d+2)^3 :=
      sum_le_sum fun d _ => ballInts_upper (by positivity)
    _ = volUnit * ((m : ℝ)^3 * (∑ d ∈ Icc 5 m, ((d : ℝ)⁻¹)^3) +
        6*(m : ℝ)^2 * (∑ d ∈ Icc 5 m, ((d : ℝ)⁻¹)^2) +
        12*(m : ℝ) * (∑ d ∈ Icc 5 m, (d : ℝ)⁻¹) + 8*((Icc 5 m).card : ℝ)) := by
      rw [← mul_sum]
      congr 1
      have h8 : (8 : ℝ) * ((Icc 5 m).card : ℝ) = ∑ _d ∈ Icc 5 m, (8 : ℝ) := by simp [mul_comm]
      rw [h8]
      simp only [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      rw [div_eq_mul_inv]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ volUnit_pos.le
      have h1 := mul_le_mul_of_nonneg_left h₃ (by positivity : 0 ≤ (m : ℝ)^3)
      have h2 := mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ 6*(m : ℝ)^2)
      have h3 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 12*(m : ℝ))
      nlinarith only [h1,h2,h3,hc,hm',mul_nonneg (show (0 : ℝ) ≤ m by positivity) (show (0 : ℝ) ≤ m-1 by linarith)]

/-- A lower estimate for the primitive vectors, by excluding the nonprimitive
vectors first modulo 2 and 3, then bounding the number of remaining multiples. -/
lemma points_lower (m : ℕ) (hm : 10000 ≤ m) :
    (2/5 : ℝ) * volUnit * (m : ℝ)^3 ≤ ((points m).card : ℝ) := by
  classical
  let good := (ballInts m).filter fun x => ok6 (residue 6 x)
  let valid := (univ : Finset (V 6)).filter ok6
  have hv : valid.card = 182 := by
    have h := card_ok6
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  have hm' : (10000 : ℝ) ≤ m := by exact_mod_cast hm
  have hG : (182/216 : ℝ) * (volUnit * ((m : ℝ)-12)^3) ≤ (good.card : ℝ) := by
    have hmaps : Set.MapsTo (residue (ι := Fin 3) 6) (↑good) (↑valid) := by
      intro x hx
      change x ∈ good at hx
      change residue 6 x ∈ valid
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
    rw [card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
    have hlocal (a : V 6) (ha : a ∈ valid) : volUnit * ((m : ℝ)-12)^3 / 216 ≤
        ((good.filter fun x => residue 6 x = a).card : ℝ) := by
      have he : good.filter (fun x => residue 6 x = a) = (ballInts m).filter (fun x => ∀ i, (x i : ZMod 6) = a i) := by
        ext x
        simp only [good, mem_filter]
        have h := (mem_filter.mp ha).2
        have hr : (∀ i, (x i : ZMod 6) = a i) ↔ residue 6 x = a :=
          ⟨fun hh => funext hh, fun hh => congrFun hh⟩
        rw [hr]
        constructor
        · tauto
        · rintro ⟨hx, he⟩
          exact ⟨⟨hx, he ▸ h⟩,he⟩
      rw [he, div_le_iff₀ (by norm_num : (0 : ℝ) < 216)]
      have h := ballInts_res_lower (by decide : 0 < (6 : ℕ)) a (r := (m : ℝ)) (by norm_num; linarith)
      norm_num at h
      exact h
    have hsum := sum_le_sum hlocal
    simp only [sum_const,nsmul_eq_mul,hv,Nat.cast_ofNat] at hsum
    linarith only [hsum]
  have hsub : prim m ⊆ good := by
    intro x hx
    have hh := mem_filter.mp hx
    refine mem_filter.mpr ⟨hh.1,?_⟩
    rw [ok6_res, hh.2]; decide
  have hbad : (good \ prim m).card ≤ ∑ d ∈ Icc 5 m, (ballInts ((m : ℝ)/d)).card := by
    let U := (Icc 5 m).biUnion (fun d => (ballInts ((m : ℝ)/d)).image (fun x => (d : ℤ) • x))
    have hU : good \ prim m ⊆ U := by
      intro x hx
      have hg := mem_filter.mp (mem_sdiff.mp hx).1
      have hb := (ok6_res x).mp hg.2
      have hx0 : x ≠ 0 := by rintro rfl; exact hb.1 (by simp [content])
      have hh : content x ≠ 1 := fun h => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨hg.1,h⟩)
      let d := content x
      have hd0 : 0 < d := content_pos hx0
      have hd5 : 5 ≤ d := by
        by_contra! hd
        have he : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
        rcases he with he | he | he | he
        · exact hh he
        · exact hb.1 (by change 2 ∣ d; simp [he])
        · exact hb.2 (by change 3 ∣ d; simp [he])
        · exact hb.1 (by change 2 ∣ d; simp [he])
      obtain ⟨i, hi⟩ : ∃ i : Fin 3, x i ≠ 0 := by
        by_contra! h; exact hx0 (funext h)
      have hd' : d ≤ m := by
        have h1 := Int.natAbs_le_of_dvd_ne_zero ((content_dvd d x).mp dvd_rfl i) hi
        have h2 : (x i).natAbs ≤ m := by
          exact_mod_cast (int_coord_le_norm x i).trans (mem_ballInts.mp hg.1)
        simpa using h1.trans h2
      refine mem_biUnion.mpr ⟨d, mem_Icc.mpr ⟨hd5,hd'⟩,
        mem_image.mpr ⟨normalize x, mem_ballInts.mpr ?_, smul_normalize x⟩⟩
      have hn := congrArg (fun z => ‖eVec z‖) (smul_normalize x)
      have hpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd0
      change ‖eVec ((d : ℤ) • normalize x)‖ = ‖eVec x‖ at hn
      rw [eVec_smul, norm_smul, Int.cast_natCast, Real.norm_eq_abs, abs_of_pos hpos] at hn
      apply (le_div_iff₀ hpos).2
      rw [mul_comm,hn]
      exact mem_ballInts.mp hg.1
    exact (card_le_card hU).trans (card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le))
  have hb : ((good \ prim m).card : ℝ) ≤ _ :=
    (show ((good \ prim m).card : ℝ) ≤ ∑ d ∈ Icc 5 m, ((ballInts ((m : ℝ)/d)).card : ℝ) by exact_mod_cast hbad).trans
      (sum_scaled_balls m (by omega))
  have hcard : ((good \ prim m).card : ℝ) + 2 * ((points m).card : ℝ) = (good.card : ℝ) := by
    exact_mod_cast (twice_points m ▸ card_sdiff_add_card_eq_card hsub)
  have hr : (4/5 : ℝ) * (m : ℝ)^3 ≤ (182/216 : ℝ) * ((m : ℝ)-12)^3 - ((m : ℝ)^3/32+26*(m : ℝ)^2) := by
    nlinarith only [mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hm'),hm']
  have hh := mul_le_mul_of_nonneg_left hr volUnit_pos.le
  linarith only [hG,hb,hcard,show (4/5 : ℝ)*volUnit*(m : ℝ)^3 ≤
    (182/216 : ℝ) * (volUnit * ((m : ℝ)-12)^3) - volUnit * ((m : ℝ)^3/32+26*(m : ℝ)^2) by
      linear_combination hh]

end E211Counter
end

section
-- ReducedVolume211
noncomputable section
open scoped ENNReal InnerProductSpace Topology
open MeasureTheory Metric Set

namespace E211Counter

def reducedRegion : Set (E3 × E3) :=
  {p | ‖p.2‖ ≤ 1 ∧ ‖p.1‖ ≤ ‖p.2‖ ∧ |⟪p.1,p.2⟫_ℝ| ≤ ‖p.1‖^2/2}

lemma reducedRegion_closed : IsClosed reducedRegion := by
  unfold reducedRegion
  exact (isClosed_le (f := fun p : E3 × E3 => ‖p.2‖) (g := fun _ => 1)
    (by fun_prop) (by fun_prop)).inter <|
    (isClosed_le (f := fun p : E3 × E3 => ‖p.1‖) (g := fun p => ‖p.2‖)
      (by fun_prop) (by fun_prop)).inter <|
    isClosed_le (f := fun p : E3 × E3 => |⟪p.1,p.2⟫_ℝ|) (g := fun p => ‖p.1‖^2/2)
      (by fun_prop) (by fun_prop)

lemma reducedRegion_compact : IsCompact reducedRegion := by
  refine ((isCompact_closedBall (0 : E3) 1).prod (isCompact_closedBall (0 : E3) 1)).of_isClosed_subset
    reducedRegion_closed ?_
  intro p hp
  change ‖p.2‖ ≤ 1 ∧ ‖p.1‖ ≤ ‖p.2‖ ∧ _ at hp
  exact ⟨by simpa using hp.2.1.trans hp.1, by simpa using hp.1⟩

lemma orthSplit (u : E3) (hu : ‖u‖ = 1) :
    ∃ F : WithLp 2 (ℝ × E2) ≃ₗᵢ[ℝ] E3,
      ∀ t : ℝ, ∀ v : E2, ⟪u, F (WithLp.toLp 2 (t,v))⟫_ℝ = t := by
  let K := Submodule.span ℝ {u}
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have fdim : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩
  let M := OrthonormalBasis.fromOrthogonalSpanSingleton (n := 2) (𝕜 := ℝ) hu0
  let F := (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.toSpanUnitSingleton u hu)
      M.repr.symm).trans K.orthogonalDecomposition.symm
  refine ⟨F, fun t v => ?_⟩
  have ho : ⟪u, ((M.repr.symm v : Kᗮ) : E3)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (M.repr.symm v).property
  change ⟪u, t • u + ((M.repr.symm v : Kᗮ) : E3)⟫_ℝ = t
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ho, hu]
  ring

lemma shellBand_volume {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    volume {p : ℝ × E2 | |p.1| ≤ r/2 ∧ r^2 ≤ p.1^2 + ‖p.2‖^2 ∧ p.1^2 + ‖p.2‖^2 ≤ 1} =
      ENNReal.ofReal (Real.pi * r * (1-r^2)) := by
  let D : Set (ℝ × E2) := {p | |p.1| ≤ r/2 ∧ r^2 ≤ p.1^2 + ‖p.2‖^2 ∧ p.1^2 + ‖p.2‖^2 ≤ 1}
  have hD : MeasurableSet D := by
    apply IsClosed.measurableSet
    exact (isClosed_le (f := fun p : ℝ × E2 => |p.1|) (g := fun _ => r/2)
      (by fun_prop) (by fun_prop)).inter <|
      (isClosed_le (f := fun _ : ℝ × E2 => r^2) (g := fun p => p.1^2 + ‖p.2‖^2)
        (by fun_prop) (by fun_prop)).inter <|
      isClosed_le (f := fun p : ℝ × E2 => p.1^2 + ‖p.2‖^2) (g := fun _ => 1)
        (by fun_prop) (by fun_prop)
  change (volume.prod volume) D = _
  rw [Measure.prod_apply hD]
  have hh (t : ℝ) :
      (volume : Measure E2) (Prod.mk t ⁻¹' D) =
        (Icc (-r/2) (r/2)).indicator (fun _ => ENNReal.ofReal (Real.pi * (1-r^2))) t := by
    by_cases ht : |t| ≤ r/2
    · have ht0 : t^2 ≤ r^2 := by
        rw [← sq_abs]
        apply pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
      have ht1 : t^2 ≤ 1 := ht0.trans (by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr'), hr'])
      have h0 := sub_nonneg.mpr ht0
      have h1 := sub_nonneg.mpr ht1
      have hset : Prod.mk t ⁻¹' D =
          closedBall (0 : E2) (Real.sqrt (1-t^2)) \ ball (0 : E2) (Real.sqrt (r^2-t^2)) := by
        ext v
        simp only [D, mem_preimage, mem_ofPred_eq, ht, true_and, mem_sdiff, mem_closedBall,
          mem_ball, dist_zero_right, not_lt, Real.sqrt_le_iff, Real.le_sqrt (norm_nonneg _) h1]
        constructor
        · rintro ⟨h₂,h₃⟩
          exact ⟨by linarith, norm_nonneg _, by linarith⟩
        · rintro ⟨h₂,_,h₃⟩
          constructor <;> linarith
      have hsubset : ball (0 : E2) (Real.sqrt (r^2-t^2)) ⊆ closedBall 0 (Real.sqrt (1-t^2)) := by
        apply ball_subset_closedBall.trans (closedBall_subset_closedBall _)
        apply Real.sqrt_le_sqrt
        nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr'), hr']
      have htI : t ∈ Icc (-r/2) (r/2) := by
        rw [abs_le] at ht
        constructor <;> linarith [ht.1,ht.2]
      rw [indicator_of_mem htI, hset, measure_sdiff hsubset measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne,
        EuclideanSpace.volume_closedBall_fin_two, EuclideanSpace.volume_ball_fin_two,
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
        Real.sq_sqrt h0, Real.sq_sqrt h1,
        ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h0,
        ← ENNReal.ofReal_sub _ (mul_nonneg h0 Real.pi_nonneg)]
      congr 1
      ring
    · have htI : t ∉ Icc (-r/2) (r/2) := by
        intro h
        apply ht
        rw [abs_le]
        exact ⟨by linarith [h.1],h.2⟩
      rw [indicator_of_notMem htI]
      simp [D, Set.preimage, ht]
  simp_rw [hh]
  rw [lintegral_indicator measurableSet_Icc, lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
    ← ENNReal.ofReal_mul (mul_nonneg Real.pi_nonneg (by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr'), hr']))]
  congr 1
  ring

lemma reduced_slice {a : E3} (ha : a ≠ 0) (hr : ‖a‖ ≤ 1) :
    (volume : Measure E3) (Prod.mk a ⁻¹' reducedRegion) =
      ENNReal.ofReal (Real.pi * ‖a‖ * (1-‖a‖^2)) := by
  let u := ‖a‖⁻¹ • a
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hp.ne']
  have hau : a = ‖a‖ • u := by simp [u, smul_smul, hp.ne']
  obtain ⟨F,hF⟩ := orthSplit u hu
  have hmp := F.measurePreserving.comp (WithLp.volume_preserving_toLp (U := ℝ) (V := E2))
  rw [← hmp.measure_preimage (reducedRegion_closed.measurableSet.preimage measurable_prodMk_left).nullMeasurableSet]
  convert shellBand_volume (norm_nonneg a) hr using 2
  ext p
  rcases p with ⟨t,v⟩
  let w := F (WithLp.toLp 2 (t,v))
  have hn : ‖w‖^2 = t^2 + ‖v‖^2 := by
    rw [show w = F (WithLp.toLp 2 (t,v)) from rfl, F.norm_map, WithLp.prod_norm_sq_eq_of_L2]
    simp [Real.norm_eq_abs]
  have hi : ⟪a,w⟫_ℝ = ‖a‖ * t := by rw [← hF t v, ← real_inner_smul_left, ← hau]
  change (‖w‖ ≤ 1 ∧ ‖a‖ ≤ ‖w‖ ∧ |⟪a,w⟫_ℝ| ≤ ‖a‖^2/2) ↔
    |t| ≤ ‖a‖/2 ∧ ‖a‖^2 ≤ t^2 + ‖v‖^2 ∧ t^2 + ‖v‖^2 ≤ 1
  have he1 : ‖w‖ ≤ 1 ↔ ‖w‖^2 ≤ 1 := by
    simpa using (pow_le_pow_iff_left₀ (norm_nonneg w) zero_le_one (by decide : (2 : ℕ) ≠ 0)).symm
  have he2 : ‖a‖ ≤ ‖w‖ ↔ ‖a‖^2 ≤ ‖w‖^2 :=
    (pow_le_pow_iff_left₀ (norm_nonneg a) (norm_nonneg w) (by decide : (2 : ℕ) ≠ 0)).symm
  have he3 : |‖a‖ * t| ≤ ‖a‖^2/2 ↔ |t| ≤ ‖a‖/2 := by
    rw [abs_mul, abs_of_nonneg hp.le, pow_two, mul_div_assoc, mul_le_mul_iff_right₀ hp]
  rw [he1,he2,hi,he3,hn]
  tauto

lemma reducedRegion_volume : volume.real reducedRegion = Real.pi^2 / 3 := by
  let f : ℝ → ℝ := fun r => Real.pi * r * (1-r^2)
  let g := (Icc (0 : ℝ) 1).indicator f
  have hf : Continuous f := by fun_prop
  have hg (a : E3) : g ‖a‖ = (closedBall (0 : E3) 1).indicator (fun x : E3 => f ‖x‖) a := by
    simp [g, indicator, norm_nonneg]
  have hg' : Integrable (fun a : E3 => g ‖a‖) (volume : Measure E3) := by
    simp_rw [hg]
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (hf.comp (continuous_norm : Continuous (norm : E3 → ℝ))).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  have hgpos : ∀ a : E3, 0 ≤ g ‖a‖ := by
    intro a
    by_cases ha : ‖a‖ ≤ 1
    · have hae : ‖a‖ ∈ Icc (0 : ℝ) 1 := ⟨norm_nonneg _,ha⟩
      dsimp only [g]
      rw [indicator_of_mem hae]
      exact mul_nonneg (by positivity : 0 ≤ Real.pi * ‖a‖)
        (by nlinarith only [mul_nonneg (norm_nonneg a) (sub_nonneg.mpr ha),ha])
    · have hae : ‖a‖ ∉ Icc (0 : ℝ) 1 := fun h => ha h.2
      simp [g, indicator_of_notMem hae]
  have hslice : (fun a : E3 => (volume : Measure E3) (Prod.mk a ⁻¹' reducedRegion)) =ᵐ[volume]
      (fun a : E3 => ENNReal.ofReal (g ‖a‖)) := by
    have hae : ∀ᵐ a : E3 ∂volume, a ≠ 0 := by simp [ae_iff, measure_singleton]
    filter_upwards [hae] with a ha
    by_cases hr : ‖a‖ ≤ 1
    · dsimp only [g]
      rw [reduced_slice ha hr, indicator_of_mem (show ‖a‖ ∈ Icc (0 : ℝ) 1 from ⟨norm_nonneg _,hr⟩)]
    · have he : Prod.mk a ⁻¹' reducedRegion = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro b hb
        exact hr (hb.2.1.trans hb.1)
      dsimp only [g]
      rw [he, measure_empty, indicator_of_notMem (show ‖a‖ ∉ Icc (0 : ℝ) 1 from fun h => hr h.2), ENNReal.ofReal_zero]
  rw [measureReal_def, show (volume : Measure (E3 × E3)) = volume.prod volume from rfl,
    Measure.prod_apply reducedRegion_closed.measurableSet, lintegral_congr_ae hslice,
    ← ofReal_integral_eq_lintegral_ofReal hg' (.of_forall hgpos),
    ENNReal.toReal_ofReal (integral_nonneg hgpos), integral_fun_norm_addHaar (μ := volume) g]
  have hball : (volume : Measure E3).real (ball 0 1) = volUnit := by
    rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball, real_volume_ball3 _ (by positivity), one_pow, mul_one]
  have hi : (∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ E3 - 1) • g y) = Real.pi / 12 := by
    simp only [finrank_euclideanSpace_fin, Nat.reduceSub, smul_eq_mul]
    have he (y : ℝ) : y^2 * g y = (Icc (0 : ℝ) 1).indicator (fun z => z^2 * f z) y := by
      by_cases hh : y ∈ Icc (0 : ℝ) 1 <;> simp [g, indicator, hh]
    simp_rw [he]
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have hs : Icc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 := by ext; simp; grind
    rw [hs, ← intervalIntegral.integral_of_le zero_le_one]
    have heq (y : ℝ) : y^2 * f y = Real.pi * (y^3-y^5) := by unfold f; ring
    simp_rw [heq]
    have hpow (n : ℕ) : IntervalIntegrable (fun x : ℝ => x^n) volume 0 1 :=
      (continuous_id.pow n).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hpow 3) (hpow 5)]
    norm_num [integral_pow]
    ring
  rw [hball, hi]
  simp [volUnit, nsmul_eq_mul, smul_eq_mul]
  ring

end E211Counter
end

section
-- PairCount211
noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open MeasureTheory Metric Filter Finset

namespace E211Counter

abbrev PairIndex := Fin 3 ⊕ Fin 3

def pairSplit (x : PairIndex → ℝ) : E3 × E3 :=
  (WithLp.toLp 2 (x ∘ Sum.inl), WithLp.toLp 2 (x ∘ Sum.inr))

lemma pairSplit_preserving : MeasurePreserving pairSplit := by
  exact ((PiLp.volume_preserving_toLp (Fin 3)).prod (PiLp.volume_preserving_toLp (Fin 3))).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : PairIndex => ℝ))

def pairRegion : Set (PairIndex → ℝ) := pairSplit ⁻¹' reducedRegion

lemma pairRegion_compact : IsCompact pairRegion := by
  have hcont : Continuous pairSplit := by
    unfold pairSplit
    exact ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_apply _)).prodMk
      ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_apply _))
  refine (isCompact_Icc (α := PairIndex → ℝ) (a := fun _ => -1) (b := fun _ => 1)).of_isClosed_subset
    (reducedRegion_closed.preimage hcont) ?_
  intro x hx
  have hx' : ‖(pairSplit x).2‖ ≤ 1 ∧ ‖(pairSplit x).1‖ ≤ ‖(pairSplit x).2‖ ∧ _ := hx
  have hh (i : PairIndex) : |x i| ≤ 1 := by
    rcases i with i | i
    · exact (coord_le_norm (pairSplit x).1 i).trans (hx'.2.1.trans hx'.1)
    · exact (coord_le_norm (pairSplit x).2 i).trans hx'.1
  exact ⟨fun i => (abs_le.mp (hh i)).1, fun i => (abs_le.mp (hh i)).2⟩

lemma pairRegion_volume : volume.real pairRegion = (3/16 : ℝ) * volUnit^2 := by
  rw [pairRegion, pairSplit_preserving.measureReal_preimage reducedRegion_closed.measurableSet.nullMeasurableSet,
    reducedRegion_volume, volUnit]
  ring

def pairJoin : (Z3 × Z3) ↪ (PairIndex → ℤ) :=
  ⟨fun p => Sum.elim p.1 p.2, fun _ _ h => Prod.ext
    (funext fun i => congrFun h (Sum.inl i)) (funext fun i => congrFun h (Sum.inr i))⟩

def pairResidue (d : ℕ) (x : PairIndex → ℤ) : pairV d :=
  (residue d (x ∘ Sum.inl), residue d (x ∘ Sum.inr))

lemma forall_pairJoin {U : Finset (Z3 × Z3)} {P : (PairIndex → ℤ) → Prop}
    (h : ∀ p ∈ U, P (pairJoin p)) : ∀ x ∈ U.map pairJoin, P x :=
  fun _ hx => (mem_map.mp hx).elim fun p hp => hp.2 ▸ h p hp.1

lemma card_mul_le_of_fibers {α β : Type*} [Fintype β] [DecidableEq β]
    (U : Finset α) (f : α → β) (ok : β → Prop) [DecidablePred ok] (b C : ℝ)
    (hmaps : ∀ x ∈ U, ok (f x))
    (hcount : ∀ r : β, ok r → (↑((U.filter fun x => f x = r).card) : ℝ) * b ≤ C) :
    (U.card : ℝ) * b ≤ (Nat.card {r // ok r} : ℝ) * C := by
  let A : Finset β := univ.filter ok
  have hM : Set.MapsTo f ↑U ↑A := fun x hx => mem_filter.mpr ⟨mem_univ _, hmaps x hx⟩
  have h := sum_le_sum (s := A) (fun r hr => hcount r (mem_filter.mp hr).2)
  rw [← sum_mul, ← Nat.cast_sum, ← card_eq_sum_card_fiberwise hM, sum_const, nsmul_eq_mul] at h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

/-- The modular sieve keeps exactly `389975040` classes modulo 30 among
the `30^6` classes of lattice pairs. On each class use the box-volume upper bound. -/
lemma reduced_upper : ∀ᶠ m : ℕ in atTop,
    ((reduced m).card : ℝ) ≤ 4 * (51/2000 : ℝ) * volUnit^2 * (m : ℝ)^6 := by
  have hV : volume.real pairRegion < (19/100 : ℝ) * volUnit^2 := by
    rw [pairRegion_volume]
    exact mul_lt_mul_of_pos_right (by norm_num) (by positivity [volUnit_pos])
  filter_upwards [eventual_thickening_lt pairRegion pairRegion_compact 30 hV, eventually_gt_atTop 0] with m hm hm0
  classical
  let U := (reduced m).map pairJoin
  have hmaps : ∀ x ∈ U, ok30 (pairResidue 30 x).1 (pairResidue 30 x).2 :=
    forall_pairJoin (P := fun x => ok30 (pairResidue 30 x).1 (pairResidue 30 x).2)
      (fun ⟨_,_⟩ hp => ok30_res (mem_reduced.mp hp).2.2.2)
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hT : ∀ x ∈ U, (m : ℝ)⁻¹ • ri x ∈ pairRegion := by
    refine forall_pairJoin (P := fun x => (m : ℝ)⁻¹ • ri x ∈ pairRegion) ?_
    rintro ⟨a,b⟩ hp
    obtain ⟨hb,hab,hi,_⟩ := mem_reduced.mp hp
    change ‖(m : ℝ)⁻¹ • eVec b‖ ≤ 1 ∧ ‖(m : ℝ)⁻¹ • eVec a‖ ≤ ‖(m : ℝ)⁻¹ • eVec b‖ ∧
      |⟪(m : ℝ)⁻¹ • eVec a, (m : ℝ)⁻¹ • eVec b⟫_ℝ| ≤ ‖(m : ℝ)⁻¹ • eVec a‖^2/2
    have hpos := (inv_pos.mpr hm').le
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos, real_inner_smul_left,
      real_inner_smul_right, abs_mul, mul_pow]
    refine ⟨?_, mul_le_mul_of_nonneg_left hab hpos, ?_⟩
    · simpa [hm'.ne'] using mul_le_mul_of_nonneg_left hb hpos
    · rw [← mul_assoc, ← pow_two, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hi (sq_nonneg _)
  have hcount (c : pairV 30) (_ : ok30 c.1 c.2) :
      (((U.filter fun x => pairResidue 30 x = c).card : ℕ) : ℝ) * (30 : ℝ)^6 ≤
        (m : ℝ)^6 * volume.real (cthickening ((30 : ℝ)/(m : ℝ)) pairRegion) := by
    let T := U.filter fun x => pairResidue 30 x = c
    have he : ∀ x ∈ T, ∀ y ∈ T, ∀ i, (x i : ZMod 30) = (y i : ZMod 30) := by
      intro x hx y hy i
      have hx' : pairResidue 30 x = c := (mem_filter.mp hx).2
      have hy' : pairResidue 30 y = c := (mem_filter.mp hy).2
      have h := hx'.trans hy'.symm
      rcases i with i | i
      · exact congrFun (congrArg Prod.fst h) i
      · exact congrFun (congrArg Prod.snd h) i
    simpa using count_le_thickening (by norm_num : 0 < (30 : ℕ)) hm' T pairRegion
      pairRegion_compact.isBounded he (fun x hx => hT x (mem_filter.mp hx).1)
  have hsum := card_mul_le_of_fibers U (pairResidue 30) (fun p => ok30 p.1 p.2)
    ((30 : ℝ)^6) _ hmaps hcount
  rw [card_ok30,
    show U.card = (reduced m).card from card_map _] at hsum
  have hre := mul_le_mul_of_nonneg_left hm.le (show 0 ≤ (389975040 : ℝ) * (m : ℝ)^6 by positivity)
  calc
    ((reduced m).card : ℝ) ≤
        (389975040 : ℝ) * ((m : ℝ)^6 * volume.real (cthickening (30/(m : ℝ)) pairRegion)) / 30^6 :=
      (le_div_iff₀ (by positivity)).2 hsum
    _ ≤ _ := by
      apply (div_le_iff₀ (by positivity)).2
      have hcoef : (389975040 : ℝ) * (19/100) ≤ 4 * (51/2000) * 30^6 := by norm_num
      have h := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ volUnit^2 * (m : ℝ)^6 by positivity)
      nlinarith only [hre, h]

end E211Counter
end

section
-- Main
open scoped Classical

open E211Counter Filter in
theorem OMA.disproof : ¬ (type_of% @Erdos211.erdos_211.variants.one_sixth) := by
  intro h
  obtain ⟨N,hN⟩ := h (1/100 : ℝ) (by norm_num)
  have hall := eventually_atTop.mp reduced_upper
  obtain ⟨M,hM⟩ := hall
  let m := max (max M N) 10000
  have hmM : M ≤ m := by dsimp [m]; omega
  have hmN : N ≤ m := by dsimp [m]; omega
  have hm : 10000 ≤ m := by dsimp [m]; omega
  have hm' : (10000 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨t,ht⟩ := exists_chart m
  let s := (points m).image (project t)
  let n := s.card
  let q := (2*m+1)^2
  let k := n-q
  let X : ℝ := volUnit * (m : ℝ)^3
  have hmpos : (0 : ℝ) < m := by linarith
  have hX : 0 < X := mul_pos volUnit_pos (pow_pos hmpos 3)
  have hvol : 4 ≤ volUnit := by unfold volUnit; linarith [Real.pi_gt_three]
  have hpts : (2/5 : ℝ)*X ≤ (n : ℝ) := by
    have hi : Set.InjOn (project t) (points m) := project_injOn
      (fun x hx => ht x (mem_ballInts.mpr (mem_points.mp hx).1) (by
        rintro rfl; have hh := (mem_points.mp hx).2.1; simp [content] at hh))
      (fun _ hx => (mem_points.mp hx).2)
    have he : n = (points m).card := Finset.card_image_of_injOn hi
    rw [he]
    simpa only [X, mul_assoc] using points_lower m hm
  have hX4 : 4*(m : ℝ)^3 ≤ X := mul_le_mul_of_nonneg_right hvol (by positivity)
  have hq : (q : ℝ) ≤ (1/1000 : ℝ)*X := by
    have h0 : (2*(m : ℝ)+1)^2 ≤ (3*(m : ℝ))^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h1 := mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hm')
    simp only [q, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    nlinarith only [h0,h1,hX4,sq_nonneg (m : ℝ)]
  have hqn : q < n := by
    exact_mod_cast (show (q : ℝ) < n by linarith only [hpts,hq,hX])
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hk2 : k < n := by
    have hq0 : 0 < q := by dsimp [q]; positivity
    dsimp [k]; omega
  have hk : (399/1000 : ℝ)*X ≤ (k : ℝ) := by
    rw [show (k : ℝ) = (n : ℝ) - q from Nat.cast_sub hqn.le]
    linarith only [hpts,hq]
  have hmn : m ≤ n := by
    have hp : (m : ℝ) ≤ (m : ℝ)^3 := le_self_pow₀ (by linarith) (by decide)
    exact_mod_cast (show (m : ℝ) ≤ n by nlinarith only [hp,hpts,hX4,show 0 ≤ (m : ℝ) by positivity])
  have hcap (L : PlaneLine) (hL : EuclideanGeometry.IsLine L) :
      (s.filter fun p => p ∈ L).card ≤ n-k := by
    have he : n-k = q := by dsimp [k]; omega
    rw [he]
    exact line_cap ht L hL
  have hu : ((Erdos211.determinedLines s).card : ℝ) ≤ (51/2000 : ℝ)*X^2 := by
    have h₁ : ((Erdos211.determinedLines s).card : ℝ)*4 ≤ ((reduced m).card : ℝ) :=
      by exact_mod_cast lines_le_reduced ht
    have h₂ := hM m hmM
    unfold X
    nlinarith only [h₁,h₂]
  have hh := hN n k (hmN.trans hmn) hk1 hk2 s rfl hcap
  have hl := mul_le_mul hk hpts (by positivity : 0 ≤ (2/5 : ℝ)*X) (Nat.cast_nonneg (α := ℝ) k)
  have hc := mul_le_mul_of_nonneg_left hl (by norm_num : 0 ≤ (1-(1/100 : ℝ))/6)
  have hxp : 0 < X^2 := sq_pos_of_pos hX
  nlinarith only [hh,hu,hc,hxp]
end
