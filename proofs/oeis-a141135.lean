import OMAStatements.S_oeis_a141135
import Mathlib.Tactic

/-!
Barker's rational function predicts 91 edges for 24 pentagons. Wang's OEIS
extension in 2019 gives 90. This file independently certifies the upper bound
from an exact packing, without taking a sequence term as an assumption.
The layout uses the six-cycle packing in R. H. Buchholz and W. de Launey,
"An edge minimization problem for regular polygons", EJC 16 (2009), R90,
Figure 22. Take the pentagons at the vertices of seven adjacent honeycomb
faces (one face and the six around it). The 24 pentagons share 30 edges.

Coordinates are represented by pairs of integers a,b denoting a+b*t,
where t²=1−t. The finite certificates check support lines and count edges;
only the final map from these coordinates to the real plane uses analysis.
-/

namespace Pentagon24
open OMA.S_oeis_a141135

abbrev Coeff := ℤ × ℤ
abbrev Vec := Coeff × Coeff
def plus (a b : Coeff) : Coeff := (a.1+b.1, a.2+b.2)
def minus (a b : Coeff) : Coeff := (a.1-b.1, a.2-b.2)
def neg (a : Coeff) : Coeff := (-a.1,-a.2)
def times (a b : Coeff) : Coeff :=
  (a.1*b.1+a.2*b.2, a.1*b.2+a.2*b.1-a.2*b.2)
def addVec (p q : Vec) : Vec := (plus p.1 q.1, plus p.2 q.2)
def negVec (p : Vec) : Vec := (neg p.1, neg p.2)
def project (p q : Vec) : Coeff := plus (times p.1 q.1) (times p.2 q.2)
noncomputable def val (z : Coeff) : ℝ := z.1 + z.2*t
noncomputable def realVec (p : Vec) : Point := (val p.1,val p.2)

lemma eqT : t^2 + t = 1 := by
  unfold t
  nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 5)]

lemma boundsT : (61803 : ℝ)/100000 ≤ t ∧ t ≤ (61804 : ℝ)/100000 := by
  have sq := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 5)
  have hpos := Real.sqrt_nonneg (5:ℝ)
  unfold t
  constructor
  · by_contra! h
    have p : Real.sqrt 5 < (223606:ℝ)/100000 := by linarith
    have q := mul_self_lt_mul_self hpos p
    nlinarith
  · by_contra! h
    have p : (223608:ℝ)/100000 < Real.sqrt 5 := by linarith
    have q := mul_self_lt_mul_self (by norm_num : (0:ℝ) ≤ 223608/100000) p
    nlinarith

lemma valPlus (a b : Coeff) : val (plus a b) = val a + val b := by
  simp [val,plus]; ring
lemma valMinus (a b : Coeff) : val (minus a b) = val a - val b := by
  simp [val,minus]; ring
lemma valNeg (a : Coeff) : val (neg a) = -val a := by
  simp [val,neg]; ring
lemma valTimes (a b : Coeff) : val (times a b) = val a * val b := by
  simp [val,times]
  linear_combination -(a.2 : ℝ) * (b.2 : ℝ) * eqT
lemma valProject (p q : Vec) : val (project p q) = dot (realVec p) (realVec q) := by
  simp [project,valPlus,valTimes,dot,realVec]

abbrev Nonnegative (z : Coeff) : Prop :=
  0 ≤ 100000*z.1 + 61803*z.2 ∧ 0 ≤ 100000*z.1 + 61804*z.2
abbrev Positive (z : Coeff) : Prop :=
  0 < 100000*z.1 + 61803*z.2 ∧ 0 < 100000*z.1 + 61804*z.2

lemma nonnegSound (z : Coeff) (h : Nonnegative z) : 0 ≤ val z := by
  rcases z with ⟨a,b⟩
  obtain ⟨l,u⟩ := h
  have L : (0 : ℝ) ≤ 100000 * (a : ℝ) + 61803 * (b : ℝ) := by exact_mod_cast l
  have U : (0 : ℝ) ≤ 100000 * (a : ℝ) + 61804 * (b : ℝ) := by exact_mod_cast u
  change 0 ≤ (a : ℝ) + (b : ℝ) * t
  by_cases hb : (0 : ℝ) ≤ b
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr boundsT.1)]
  · nlinarith [mul_nonneg (show 0 ≤ -(b : ℝ) by linarith) (sub_nonneg.mpr boundsT.2)]

lemma positiveSound (z : Coeff) (h : Positive z) : 0 < val z := by
  rcases z with ⟨a,b⟩
  obtain ⟨l,u⟩ := h
  have L : (0 : ℝ) < 100000 * (a : ℝ) + 61803 * (b : ℝ) := by exact_mod_cast l
  have U : (0 : ℝ) < 100000 * (a : ℝ) + 61804 * (b : ℝ) := by exact_mod_cast u
  change 0 < (a : ℝ) + (b : ℝ) * t
  by_cases hb : (0 : ℝ) ≤ b
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr boundsT.1)]
  · nlinarith [mul_nonneg (show 0 ≤ -(b : ℝ) by linarith) (sub_nonneg.mpr boundsT.2)]

def base (i : Fin 5) : Vec :=
  [((1,0),(0,0)), ((0,0),(1,0)), ((-1,0),(0,1)), ((0,-1),(0,-1)), ((0,1),(-1,0))].getD i.val ((0,0),(0,0))

def center (i : Fin 24) : Vec :=
  [((0,0),(0,0)), ((1,0),(1,0)), ((2,1),(1,0)), ((2,1),(0,-1)), ((1,1),(-1,-1)), ((0,0),(-1,-1)), ((3,1),(2,0)), ((4,2),(2,0)), ((4,2),(1,-1)), ((3,2),(0,-1)), ((-2,-1),(-1,0)), ((-1,-1),(0,0)), ((-1,0),(-2,-1)), ((-2,-1),(-2,-1)), ((1,0),(2,1)), ((2,0),(3,1)), ((3,1),(3,1)), ((1,1),(-2,-2)), ((0,1),(-3,-2)), ((-1,0),(-3,-2)), ((3,2),(-1,-2)), ((2,2),(-2,-2)), ((-1,-1),(1,1)), ((0,-1),(2,1))].getD i.val ((0,0),(0,0))

def flipped (i : Fin 24) : Bool :=
  [false, true, false, true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, false, true, true, false, false, true].getD i.val false

def normal (i : Fin 10) : Vec :=
  [((1,0),(1,0)), ((-1,1),(1,0)), ((0,-2),(-1,1)), ((-1,1),(0,-2)), ((1,0),(-1,1)), ((-1,0),(-1,0)), ((1,-1),(-1,0)), ((0,2),(1,-1)), ((1,-1),(0,2)), ((-1,0),(1,-1))].getD i.val ((0,0),(0,0))

def axis (i j : Fin 24) : Fin 10 :=
  let table : List (List (Fin 10)) := [
    [0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 3, 3, 2, 0, 3, 1, 0],
    [5, 0, 7, 4, 3, 2, 0, 0, 0, 4, 2, 2, 2, 2, 8, 0, 0, 3, 2, 2, 3, 3, 2, 1],
    [2, 2, 0, 3, 2, 2, 0, 0, 0, 4, 2, 2, 2, 2, 1, 0, 0, 2, 2, 2, 3, 3, 1, 1],
    [2, 1, 8, 0, 5, 2, 0, 0, 0, 7, 2, 1, 2, 2, 1, 0, 0, 2, 2, 2, 4, 3, 1, 1],
    [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 2, 2, 0, 0, 0, 3, 2, 2, 0, 4, 1, 0],
    [8, 0, 0, 0, 7, 0, 0, 0, 0, 0, 2, 1, 5, 2, 0, 0, 0, 4, 3, 2, 0, 4, 1, 0],
    [2, 2, 5, 2, 2, 2, 0, 7, 4, 3, 2, 2, 2, 2, 2, 1, 8, 2, 2, 2, 3, 2, 2, 1],
    [2, 2, 2, 2, 2, 2, 2, 0, 3, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1],
    [2, 1, 2, 2, 2, 2, 1, 8, 0, 5, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1],
    [1, 1, 1, 2, 2, 2, 0, 0, 0, 0, 1, 1, 2, 2, 1, 0, 0, 2, 2, 2, 3, 2, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0],
    [7, 0, 0, 0, 4, 4, 0, 0, 0, 0, 5, 0, 3, 2, 0, 0, 0, 3, 3, 3, 0, 4, 8, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 7, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0],
    [2, 3, 4, 3, 3, 2, 0, 0, 0, 3, 2, 2, 2, 2, 0, 0, 0, 3, 2, 2, 3, 3, 2, 2],
    [2, 2, 3, 3, 2, 2, 4, 4, 3, 3, 2, 2, 2, 2, 5, 0, 7, 2, 2, 2, 3, 3, 2, 2],
    [2, 2, 2, 2, 2, 2, 3, 4, 3, 3, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 3, 2, 2, 2],
    [1, 0, 0, 0, 8, 1, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 5, 2, 0, 7, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 8, 1, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 2, 1, 0, 0, 0, 8, 1, 1, 2, 1, 1, 0, 0, 2, 2, 2, 0, 5, 1, 1],
    [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 2, 2, 2, 0, 0, 1, 0],
    [4, 0, 0, 0, 3, 3, 0, 0, 0, 0, 2, 3, 3, 2, 0, 0, 0, 3, 3, 3, 0, 3, 0, 0],
    [3, 4, 4, 3, 3, 3, 0, 0, 0, 4, 2, 2, 2, 2, 7, 0, 0, 3, 3, 2, 3, 3, 5, 0]]
  (table.getD i.val []).getD j.val 0

def offset (b : Bool) (k : Fin 5) : Vec := if b then negVec (base k) else base k
def pos (i : Fin 24) (k : Fin 5) : Vec := addVec (center i) (offset (flipped i) k)
noncomputable def tile (i : Fin 24) (k : Fin 5) : Point := realVec (pos i k)

def lower (b : Bool) (d : Fin 10) : Coeff :=
  let cs : List Coeff := if b
    then [(-1,0), (-1,0), (-1,0), (-1,0), (-1,0), (0,-2), (0,-2), (0,-2), (0,-2), (0,-2)]
    else [(0,-2), (0,-2), (0,-2), (0,-2), (0,-2), (-1,0), (-1,0), (-1,0), (-1,0), (-1,0)]
  cs.getD d.val (0,0)

def upper (b : Bool) (d : Fin 10) : Coeff :=
  let cs : List Coeff := if b
    then [(0,2), (0,2), (0,2), (0,2), (0,2), (1,0), (1,0), (1,0), (1,0), (1,0)]
    else [(1,0), (1,0), (1,0), (1,0), (1,0), (0,2), (0,2), (0,2), (0,2), (0,2)]
  cs.getD d.val (0,0)

lemma baseReal (k : Fin 5) : realVec (base k) = vertex k := by
  fin_cases k <;> norm_num [realVec,base,vertex,val,List.getD]

lemma tileRegular (i : Fin 24) : regular (tile i) := by
  cases h : flipped i
  · refine ⟨realVec (center i),1,0,by ring,?_⟩
    intro j
    rw [← baseReal j]
    simp [tile,pos,h,offset,realVec,addVec,valPlus]
  · refine ⟨realVec (center i),-1,0,by ring,?_⟩
    intro j
    rw [← baseReal j]
    simp [tile,pos,h,offset,realVec,addVec,negVec,valPlus,valNeg,sub_eq_add_neg]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
lemma supportCertificate : ∀ (b : Bool) (d : Fin 10) (k : Fin 5),
    Nonnegative (minus (project (normal d) (offset b k)) (lower b d)) ∧
    Nonnegative (minus (upper b d) (project (normal d) (offset b k))) := by
  decide +kernel

lemma nonzeroCertificate : ∀ d : Fin 10,
    Positive (normal d).1 ∨ Positive (neg (normal d).1) := by decide +kernel

def gap (i j : Fin 24) : Coeff :=
  let d := axis i j
  minus (plus (project (normal d) (center j)) (lower (flipped j) d))
        (plus (project (normal d) (center i)) (upper (flipped i) d))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
lemma gapCertificate : ∀ i j : Fin 24, i ≠ j → Nonnegative (gap i j) := by
  decide +kernel

lemma projection (n : Vec) (i : Fin 24) (k : Fin 5) :
    dot (realVec n) (tile i k) =
      val (project n (center i)) + val (project n (offset (flipped i) k)) := by
  simp [tile,pos,valProject,dot,realVec,addVec,valPlus]
  ring

lemma tilesPacked : packing tile := by
  refine ⟨tileRegular, ?_⟩
  intro i j hij
  let d := axis i j
  refine ⟨realVec (normal d), ?_, ?_⟩
  · intro heq
    have hx : val (normal d).1 = 0 := congrArg Prod.fst heq
    rcases nonzeroCertificate d with h | h
    · linarith [positiveSound _ h]
    · have H := positiveSound _ h
      rw [valNeg] at H
      linarith
  · intro k l
    have hu := nonnegSound _ (supportCertificate (flipped i) d k).2
    have hl := nonnegSound _ (supportCertificate (flipped j) d l).1
    have hg := nonnegSound _ (gapCertificate i j hij)
    change 0 ≤ val (minus (plus (project (normal d) (center j)) (lower (flipped j) d))
        (plus (project (normal d) (center i)) (upper (flipped i) d))) at hg
    simp only [valMinus,valPlus] at hu hl hg
    rw [projection,projection]
    linarith

def symbolEdges : Finset (Finset Vec) :=
  Finset.univ.biUnion fun i : Fin 24 =>
    Finset.univ.image fun j : Fin 5 => {pos i j, pos i (j+1)}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
lemma symbolCount : symbolEdges.card = 90 := by decide +kernel

lemma edgeBound : (edges tile).card ≤ 90 := by
  classical
  calc
    (edges tile).card ≤ (symbolEdges.image (fun e => e.image realVec)).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨i, hi, ie⟩ := Finset.mem_biUnion.mp (show e ∈
        Finset.univ.biUnion (fun i : Fin 24 => Finset.univ.image
          (fun j : Fin 5 => ({tile i j, tile i (j+1)} : Finset Point))) from he)
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ie
      apply Finset.mem_image.mpr
      refine ⟨{pos i j,pos i (j+1)}, Finset.mem_biUnion.mpr
        ⟨i,hi,Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩,?_⟩
      simp [tile]
    _ ≤ symbolEdges.card := Finset.card_image_le
    _ = 90 := symbolCount

lemma minimumBound : minimum 24 ≤ 90 := by
  have h : (edges tile).card ∈ {e : ℕ | ∃ f : Fin 24 → Fin 5 → Point,
      packing f ∧ (edges f).card = e} := ⟨tile, tilesPacked, rfl⟩
  exact (Nat.sInf_le h).trans edgeBound
end Pentagon24

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a141135.main) := by
  rintro ⟨formula, _⟩
  have H := formula 24 (by decide)
  have computed : OMA.S_oeis_a141135.barker 24 = 91 := by decide +kernel
  rw [computed] at H
  have h := Pentagon24.minimumBound
  omega
