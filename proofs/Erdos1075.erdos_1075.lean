import FormalConjectures.ErdosProblems.«1075»
import Mathlib

/- The mathematical counterexample is due to Anonymous (2026), Zenodo record 22667633.
This formalization uses the oscillation of a potential directly on the cycle. -/
namespace E1075
open Finset
open scoped BigOperators

open Fin.NatCast

noncomputable def pot (x : ℝ) : ℝ := if x ≤ 1 then x-x^2/2 else 1/2

lemma pot_le (x : ℝ) : pot x ≤ 1/2 := by
  unfold pot
  split <;> nlinarith [sq_nonneg (x-1)]

lemma pot_le_self {x : ℝ} (_hx : 0 ≤ x) : pot x ≤ x := by
  unfold pot
  split <;> nlinarith [sq_nonneg x]

lemma pot_high {x : ℝ} (hx : 1/3 ≤ x) : 5/18 ≤ pot x := by
  unfold pot
  split <;> rename_i h
  · nlinarith [mul_nonneg (show 0 ≤ x-1/3 by linarith) (show 0 ≤ 5/3-x by linarith)]
  · norm_num

lemma pot_step {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pot x-pot y ≤ x*(1-y)^2 := by
  by_cases h : y ≤ 1
  · rw [pot, pot, if_pos h]
    split <;> rename_i hx'
    · nlinarith [sq_nonneg (x-2*y+y^2),
        mul_nonneg (mul_nonneg hy (sq_nonneg (1-y))) (show 0 ≤ 2-y by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ x-1/2 by linarith) (sq_nonneg (1-y))]
  · rw [show pot y = 1/2 by simp [pot,h]]
    linarith [pot_le x, mul_nonneg hx (sq_nonneg (1-y))]

/- Sum the drops along the oriented arc from i to j, then extend the sum
   to the whole cycle using the nonnegativity of the edge costs. -/
lemma cyclic_diff {n : ℕ} [NeZero n] (f g : Fin n → ℝ) (hg : ∀ i, 0 ≤ g i)
    (h : ∀ i, f i - f (i+1) ≤ g i) (i j : Fin n) :
    f i - f j ≤ ∑ k, g k := by
  let t := (j-i).val
  have aux (k : ℕ) : f i - f (i+(k : Fin n)) ≤ ∑ l ∈ range k, g (i+(l : Fin n)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, Nat.cast_succ, ← add_assoc]
      linarith [h (i+(k : Fin n))]
  have hj : i + (t : Fin n) = j := by simp [t]
  have hh := aux t
  rw [hj] at hh
  refine hh.trans ?_
  calc
    _ ≤ ∑ l ∈ range n, g (i+(l : Fin n)) :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_of_lt (j-i).isLt))
        (fun _ _ _ => hg _)
    _ = ∑ l : Fin n, g (i+l) := by simp [← Fin.sum_univ_eq_sum_range]
    _ = _ := Equiv.sum_comp (Equiv.addLeft i) g

def en (x y : ℝ) := x*(1-y)^2

lemma circle_energy {n : ℕ} [NeZero n] (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (ma : ∃ i, a i ≤ 1/18) (mb : ∃ i, b i ≤ 1/18)
    (hm : 1/2 ≤ ∑ i, a i + ∑ i, b i) :
    2/9 ≤ ∑ i, (en (a i) (b i) + en (b i) (a (i+1))) := by
  have ep {x y : ℝ} (h : 0 ≤ x) : 0 ≤ en x y := mul_nonneg h (sq_nonneg _)
  by_cases ah : ∃ i, 1/3 ≤ a i
  · obtain ⟨i, hi⟩ := ah
    obtain ⟨j, hj⟩ := ma
    have hh := cyclic_diff (fun k => pot (a k)) _ (fun k => add_nonneg (ep (ha k) (y := b k)) (ep (hb k) (y := a (k+1))))
      (fun k => by dsimp [en]; linarith [pot_step (ha k) (hb k), pot_step (hb k) (ha (k+1))]) i j
    linarith [pot_high hi, pot_le_self (ha j)]
  by_cases bh : ∃ i, 1/3 ≤ b i
  · obtain ⟨i, hi⟩ := bh
    obtain ⟨j, hj⟩ := mb
    have hh := cyclic_diff (fun k => pot (b k)) _
      (fun k => add_nonneg (ep (hb k) (y := a (k+1))) (ep (ha (k+1)) (y := b (k+1))))
      (fun k => by dsimp [en]; linarith [pot_step (hb k) (ha (k+1)), pot_step (ha (k+1)) (hb (k+1))]) i j
    rw [sum_add_distrib] at hh ⊢
    have sh : (∑ k, en (a (k+1)) (b (k+1))) = ∑ k, en (a k) (b k) :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin n)) (fun k => en (a k) (b k))
    rw [sh] at hh
    linarith [pot_high hi, pot_le_self (hb j)]
  push Not at ah bh
  have low {x y : ℝ} (hx : 0 ≤ x) (hy : y < 1/3) : 4/9*x ≤ en x y := by
    unfold en
    nlinarith [mul_nonneg (mul_nonneg hx (show 0 ≤ 1/3-y by linarith))
      (show 0 ≤ 5/3-y by linarith)]
  have hh := sum_le_sum (s := (univ : Finset (Fin n))) (fun k _ =>
    add_le_add (low (ha k) (bh k)) (low (hb k) (ah (k+1))))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hh
  linarith


noncomputable def row {n : ℕ} (a b : Fin n → ℝ) (k B D : ℝ) :=
  ∑ i, a i * (b i + k) * (B - b i + D)

noncomputable def err {n : ℕ} (a b : Fin n → ℝ) (d : ℝ) :=
  ∑ i, a i * (b i-d)^2

lemma complete_row {n : ℕ} (a b : Fin n → ℝ) (A B k D : ℝ)
    (hA : ∑ i, a i = A) (hm : A+B+k+D=1) :
    1/27 - row a b k B D = err a b ((B+D-k)/2) + (A-1/3)^2*(4/3-A)/4 := by
  have h : row a b k B D + err a b ((B+D-k)/2) = A*((1-A)/2)^2 := by
    unfold row err
    rw [← sum_add_distrib, ← hA, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [hA]
    linear_combination (a i * (B+D+k+1-A)/4) * hm
  linarith only [show 1/27-A*((1-A)/2)^2=(A-1/3)^2*(4/3-A)/4 by ring, h]

lemma tiny_entry {n : ℕ} [NeZero n] (a : Fin n → ℝ) (h : ∑ i, a i ≤ 1) :
    ∃ i, a i ≤ 1/n := by
  by_contra! bad
  have hh := sum_lt_sum_of_nonempty (s := (univ : Finset (Fin n))) univ_nonempty
    (fun i _ => bad i)
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp [hn] at hh
  linarith

lemma weighted_en (s a b u v t : ℝ) (hs : 0 ≤ s) (_hs' : s ≤ 1)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hu : 0 < u) (hv : 0 < v) (htu : t ≤ u) (htv : t ≤ v) :
    s*(1-s)*t^3 * en (a/u) (b/v) ≤ s*(a*(b-v)^2) := by
  have eqn : u*v^2*en (a/u) (b/v) = a*(b-v)^2 := by
    unfold en
    field_simp
    ring
  rw [← eqn, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (div_nonneg ha hu.le) (sq_nonneg _))
  calc
    s*(1-s)*t^3 ≤ s*t^3 := by nlinarith [mul_nonneg (sq_nonneg s) (pow_nonneg ht 3)]
    _ ≤ s*(u*v^2) := by
      apply mul_le_mul_of_nonneg_left _ hs
      rw [pow_succ]
      simpa [mul_comm] using mul_le_mul htu (pow_le_pow_left₀ ht htv 2) (sq_nonneg t) hu.le

set_option maxHeartbeats 1500000 in
lemma cubic {n : ℕ} [NeZero n] (a b : Fin n → ℝ) (A B k D s : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hA : ∑ i, a i = A) (hB : ∑ i, b i = B)
    (hk : 0 ≤ k) (hD : 0 ≤ D) (hm : A+B+k+D=1) (hs : 0 ≤ s) (hs' : s ≤ 1) :
    s*row a b k B D + (1-s)*row b (fun i => a (i+1)) k A D ≤
      1/27 - s*(1-s)*D^3/10 + 1/n := by
  let α := (A+D-k)/2
  let β := (B+D-k)/2
  let p := A-1/3
  let q := B-1/3
  let T := |p|+|q|
  let E := s*err a b β + (1-s)*err b (fun i => a (i+1)) α
  let v := s*(1-s)
  have hA0 : 0 ≤ A := hA ▸ sum_nonneg fun i _ => ha i
  have hB0 : 0 ≤ B := hB ▸ sum_nonneg fun i _ => hb i
  have hs0 : 0 ≤ 1-s := by linarith
  have hv : 0 ≤ v := mul_nonneg hs hs0
  have hv' : v ≤ 1/4 := by dsimp [v]; nlinarith [sq_nonneg (s-1/2)]
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have he : 0 ≤ E := add_nonneg (mul_nonneg hs (sum_nonneg fun i _ => mul_nonneg (ha i) (sq_nonneg _)))
    (mul_nonneg hs0 (sum_nonneg fun i _ => mul_nonneg (hb i) (sq_nonneg _)))
  have hp : D/3 ≤ (4/3-A)/4 := by linarith
  have hq : D/3 ≤ (4/3-B)/4 := by linarith
  have hsq : v*T^2 ≤ s*p^2+(1-s)*q^2 := by
    dsimp [v,T]
    nlinarith [sq_nonneg (s*|p|-(1-s)*|q|), sq_abs p, sq_abs q,
      congrArg (fun x : ℝ => s*x) (sq_abs p), congrArg (fun x : ℝ => s^2*x) (sq_abs p),
      congrArg (fun x : ℝ => s*x) (sq_abs q), congrArg (fun x : ℝ => s^2*x) (sq_abs q)]
  have loss : E + v*D*T^2/3 ≤ 1/27 -
      (s*row a b k B D + (1-s)*row b (fun i => a (i+1)) k A D) := by
    have e1 := complete_row a b A B k D hA hm
    have e2 := complete_row b (fun i => a (i+1)) B A k D hB (by linarith)
    change 1/27 - _ = err a b β + p^2*(4/3-A)/4 at e1
    change 1/27 - _ = err b _ α + q^2*(4/3-B)/4 at e2
    dsimp only [E]
    nlinarith only [mul_le_mul_of_nonneg_left hsq (div_nonneg hD (by norm_num : (0:ℝ) ≤ 3)),
      mul_le_mul_of_nonneg_left hp (mul_nonneg hs (sq_nonneg p)),
      mul_le_mul_of_nonneg_left hq (mul_nonneg hs0 (sq_nonneg q)),
      congrArg (s*·) e1, congrArg ((1-s)*·) e2]
  change _ ≤ 1/27-v*D^3/10+1/n
  have hT : 0 ≤ T := add_nonneg (abs_nonneg _) (abs_nonneg _)
  by_cases big : 11*D/20 ≤ T
  · have ht2 := pow_le_pow_left₀ (show 0 ≤ 11*D/20 by positivity) big 2
    nlinarith only [loss, he, mul_le_mul_of_nonneg_left ht2 (mul_nonneg hv hD),
      mul_nonneg hv (pow_nonneg hD 3), show (0:ℝ) ≤ 1/n by positivity]
  have hTp : |p| ≤ T := le_add_of_nonneg_right (abs_nonneg _)
  have hTq : |q| ≤ T := le_add_of_nonneg_left (abs_nonneg _)
  have bounds : D-T ≤ α ∧ D-T ≤ β ∧ α ≤ 1/2 ∧ β ≤ 1/2 := by
    dsimp [α,β,T,p,q] at *
    constructor
    · linarith [neg_abs_le (A-1/3), neg_abs_le (B-1/3), abs_nonneg (B-1/3)]
    constructor
    · linarith [neg_abs_le (A-1/3), neg_abs_le (B-1/3), abs_nonneg (A-1/3)]
    constructor <;> linarith
  obtain ⟨hα,hβ,hα',hβ'⟩ := bounds
  have ht : 0 < D-T := by linarith
  /- In a short cycle the allowed error absorbs the loss. Otherwise each
     alternating class contains an entry small enough to anchor its potential. -/
  by_cases small : D-T < 18*(1/n)
  · have hd : D ≤ 40*(1/n) := by linarith
    have hcube : D^3 ≤ D := by
      have h := pow_le_pow_left₀ hD (show D ≤ 1 by linarith) 2
      nlinarith [mul_le_mul_of_nonneg_left h hD]
    nlinarith only [loss, he, mul_nonneg (mul_nonneg hv hD) (sq_nonneg T),
      mul_le_mul_of_nonneg_right hv' (pow_nonneg hD 3),hd,hcube]
  have hu := ht.trans_le hα
  have hw := ht.trans_le hβ
  have find (x : Fin n → ℝ) (z : ℝ) (hz : 0 < z) (hz' : D-T ≤ z) (hx : ∑ i, x i ≤ 1) :
      ∃ i, x i/z ≤ 1/18 := by
    obtain ⟨i,hi⟩ := tiny_entry x hx
    exact ⟨i, (div_le_iff₀ hz).2 (by linarith)⟩
  have htotal : 1/2 ≤ ∑ i, a i/α + ∑ i, b i/β := by
    have h (x z : ℝ) (hx : 0 ≤ x) (hz : 0 < z) (hz' : z ≤ 1/2) : 2*x ≤ x/z :=
      (le_div_iff₀ hz).2 (by nlinarith [mul_le_mul_of_nonneg_left hz' hx])
    rw [← sum_div, ← sum_div,hA,hB]
    have dd : D ≤ 1/3+T := by
      dsimp [T,p,q]; linarith [neg_abs_le (A-1/3), neg_abs_le (B-1/3)]
    have ab : 2/3-T ≤ A+B := by
      dsimp [T,p,q]; linarith [neg_abs_le (A-1/3), neg_abs_le (B-1/3)]
    linarith [h A α hA0 hu hα',h B β hB0 hw hβ']
  have ec := circle_energy (fun i => a i/α) (fun i => b i/β)
    (fun i => div_nonneg (ha i) hu.le) (fun i => div_nonneg (hb i) hw.le)
    (find a α hu hα (by linarith)) (find b β hw hβ (by linarith)) htotal
  have energy : v*(D-T)^3*(2/9) ≤ E := by
    apply (mul_le_mul_of_nonneg_left ec (mul_nonneg hv (pow_nonneg ht.le 3))).trans
    dsimp only [E,err]
    rw [mul_sum,mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro i _
    rw [mul_add]
    apply add_le_add
    · exact weighted_en s _ _ _ _ _ hs hs' (ha i) ht.le hu hw hα hβ
    · have hh := weighted_en (1-s) _ (a (i+1)) _ _ _ hs0 (by linarith) (hb i) ht.le hw hu hβ hα
      simpa only [sub_sub_cancel, mul_comm (1-s) s] using hh
  have poly (t : ℝ) (ht' : 0 ≤ t) :
      (T+t)*T^2/3 + 2*t^3/9 ≥ (T+t)^3/10 := by
    nlinarith only [mul_nonneg (sq_nonneg (T-3*t/5)) (show 0 ≤ T+6*t/5 by positivity),
      mul_nonneg ht' (sq_nonneg (T-18*t/25)),pow_nonneg ht' 3]
  have pp := poly (D-T) ht.le
  nlinarith only [loss,energy,mul_le_mul_of_nonneg_left pp hv,
    show (0:ℝ) ≤ 1/n by positivity]

lemma avg13 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^1*y^3 ≤ ((1*x+3*y)/4)^4 := by
  apply sub_nonneg.mp
  rcases le_total x y with h | h
  · obtain ⟨d,hd,rfl⟩ := le_iff_exists_nonneg_add.mp h
    ring_nf
    positivity
  · obtain ⟨d,hd,rfl⟩ := le_iff_exists_nonneg_add.mp h
    ring_nf
    positivity

lemma avg23 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^2*y^3 ≤ ((2*x+3*y)/5)^5 := by
  apply sub_nonneg.mp
  rcases le_total x y with h | h
  · obtain ⟨d,hd,rfl⟩ := le_iff_exists_nonneg_add.mp h
    ring_nf
    positivity
  · obtain ⟨d,hd,rfl⟩ := le_iff_exists_nonneg_add.mp h
    ring_nf
    positivity

lemma avg14 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^1*y^4 ≤ ((1*x+4*y)/5)^5 := by
  apply sub_nonneg.mp
  rcases le_total x y with h | h
  · obtain ⟨d,hd,rfl⟩ := le_iff_exists_nonneg_add.mp h
    ring_nf
    positivity
  · obtain ⟨d,hd,rfl⟩ := le_iff_exists_nonneg_add.mp h
    ring_nf
    positivity

lemma avg12 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^1*y^2 ≤ ((1*x+2*y)/3)^3 := by
  apply sub_nonneg.mp
  rcases le_total x y with h | h
  · obtain ⟨d,hd,rfl⟩ := le_iff_exists_nonneg_add.mp h
    ring_nf
    positivity
  · obtain ⟨d,hd,rfl⟩ := le_iff_exists_nonneg_add.mp h
    ring_nf
    positivity

lemma threeprod (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x*y*z ≤ ((x+y+z)/3)^3 := by
  nlinarith only [mul_nonneg hz (sq_nonneg (x-y)), avg12 z ((x+y)/2) hz (by positivity)]

/- The scalar expression is affine in z. Bound its two endpoint values
   with the weighted arithmetic-geometric mean inequalities above. -/
lemma scalar (h Q t z : ℝ) (hh : 0 ≤ h) (hq : 0 ≤ Q) (ht : 0 ≤ t)
    (hz : 0 ≤ z) (hz' : z ≤ 1/4) :
    h*Q*t^3*(1/27-z/10) + Q^2*t^3*z/27 ≤ (h+Q+t)^5/3125 ∧
    h*Q*t^3 ≤ (h+Q+t)^5/24 := by
  let R := Q+t
  have hr : 0 ≤ R := add_nonneg hq ht
  have e1 : Q*t^3/27 ≤ R^4/256 := by
    dsimp [R]; nlinarith only [avg13 Q (t/3) hq (by positivity)]
  have e2 : Q^2*t^3/108 ≤ R^5/3125 := by
    dsimp [R]; nlinarith only [avg23 (Q/2) (t/3) (by positivity) (by positivity)]
  have e3 : h*(R^4/256) ≤ (h+R)^5/3125 := by
    nlinarith only [avg14 h (R/4) hh (by positivity)]
  have base : h*Q*t^3/27 ≤ (h+R)^5/3125 := by
    nlinarith only [mul_le_mul_of_nonneg_left e1 hh,e3]
  have edge : (13/40)*(h*Q*t^3/27) + Q^2*t^3/108 ≤ (h+R)^5/3125 := by
    have b : 5*h*R^4+R^5 ≤ (h+R)^5 := by
      apply sub_nonneg.mp
      ring_nf
      positivity
    nlinarith only [mul_le_mul_of_nonneg_left e1 hh,e2,b,mul_nonneg hh (pow_nonneg hr 4)]
  rw [add_assoc]
  change _ ≤ (h+R)^5/3125 ∧ _ ≤ (h+R)^5/24
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left base (show 0 ≤ 1-4*z by linarith),
      mul_le_mul_of_nonneg_left edge (show 0 ≤ 4*z by positivity)]
  · nlinarith only [base,pow_nonneg (add_nonneg hh hr) 5]

abbrev Col (n : ℕ) := (Bool × Fin n) ⊕ Fin 7
abbrev Kind (n : ℕ) := Option (Bool × Fin n)

def partner {n : ℕ} [NeZero n] (b : Bool) (i : Fin n) := if b then i+1 else i

/- A row assigns each admissible vertex to a unique position in its edge.
   The extra edge uses the row indexed by none. -/
def lane {n : ℕ} [NeZero n] : Kind n → Col n → Option (Fin 5)
  | none, .inl _ => none
  | none, .inr c => ![none, some 2, some 3, some 4, some 0, some 1, none] c
  | some (b,i), .inl (a,j) =>
    if a=b then (if j=i then some 2 else none)
    else (if j=partner b i then some 3 else some 4)
  | some (b,_), .inr c =>
    ![some 3, some 4, some 4, some 4, if b then none else some 1,
      if b then some 1 else none, some 0] c

lemma key_lane {n : ℕ} [NeZero n] (b : Bool) (i : Fin n) (c : Col n)
    (h : lane (some (b,i)) c = some 2) : c = .inl (b,i) := by
  rcases c with ⟨a,j⟩ | k
  · by_cases ab : a=b <;> by_cases ji : j=i <;> simp_all [lane,apply_ite]
    all_goals split at h <;> contradiction
  · fin_cases k <;> cases b <;> simp [lane] at h

lemma top_lane {n : ℕ} [NeZero n] (b : Bool) (i : Fin n) (c : Col n)
    (h : lane (some (b,i)) c = some 1) : c = .inr (if b then 5 else 4) := by
  rcases c with ⟨a,j⟩ | k
  · simp only [lane] at h
    split at h <;> all_goals split at h <;> contradiction
  · fin_cases k <;> cases b <;> simp_all [lane]

lemma w_lane {n : ℕ} [NeZero n] (b : Bool) (i : Fin n) (c : Col n)
    (h : lane (some (b,i)) c = some 0) : c = .inr 6 := by
  rcases c with ⟨a,j⟩ | k
  · simp only [lane] at h
    split at h <;> all_goals split at h <;> contradiction
  · fin_cases k <;> cases b <;> simp_all [lane]

def edgeOf {V : Type*} [DecidableEq V] (f : Fin 5 → V) := univ.image f

noncomputable def tuples {n : ℕ} [NeZero n] {V : Type*} (L : V → Col n)
    (S : Finset V) (r : Kind n) :=
  Fintype.piFinset fun j => S.filter (fun x => lane r (L x) = some j)

lemma fits {n : ℕ} [NeZero n] {V : Type*} {L : V → Col n} {S : Finset V}
    {r : Kind n} {f : Fin 5 → V} (hf : f ∈ tuples L S r) (j : Fin 5) :
    lane r (L (f j)) = some j := (mem_filter.mp (Fintype.mem_piFinset.mp hf j)).2

lemma transfer {V : Type*} [DecidableEq V] {f g : Fin 5 → V} (h : edgeOf f = edgeOf g)
    (i : Fin 5) : ∃ j, g j = f i := by
  have hm : f i ∈ edgeOf g := h ▸ mem_image_of_mem f (mem_univ i)
  simpa [edgeOf] using hm

lemma kind_unique {n : ℕ} [NeZero n] {V : Type*} [DecidableEq V] {L : V → Col n}
    {S : Finset V} {r t : Kind n} {f g : Fin 5 → V}
    (hf : f ∈ tuples L S r) (hg : g ∈ tuples L S t) (h : edgeOf f = edgeOf g) : r=t := by
  have sep {b : Bool} {i : Fin n} {x y : Fin 5 → V} (hx : x ∈ tuples L S (some (b,i)))
      (hy : y ∈ tuples L S none) (eq : edgeOf x = edgeOf y) : False := by
    obtain ⟨j,hj⟩ := transfer eq 0
    have hh := fits hy j
    rw [hj, w_lane b i _ (fits hx 0)] at hh
    simp [lane] at hh
  rcases r with _|⟨b,i⟩ <;> rcases t with _|⟨a,k⟩
  · rfl
  · exact (sep hg hf h.symm).elim
  · exact (sep hf hg h).elim
  · obtain ⟨j,hj⟩ := transfer h 1
    have ht := fits hg j
    rw [hj,top_lane b i _ (fits hf 1)] at ht
    have hab : a=b := by cases a <;> cases b <;> simp_all [lane]
    subst a
    obtain ⟨l,hl⟩ := transfer h 2
    have hk := fits hg l
    rw [hl,key_lane b i _ (fits hf 2)] at hk
    by_cases hi : i=k
    · simp [hi]
    · simp [lane, hi] at hk

noncomputable def graph {n : ℕ} [NeZero n] {V : Type*} [DecidableEq V] (L : V → Col n)
    (S : Finset V) := univ.biUnion fun r => (tuples L S r).image edgeOf

lemma graph_card {n : ℕ} [NeZero n] {V : Type*} [DecidableEq V] (L : V → Col n)
    (S : Finset V) :
    (graph L S).card = ∑ r : Kind n, ∏ j : Fin 5, (S.filter (fun x => lane r (L x) = some j)).card := by
  rw [graph, card_biUnion]
  · apply sum_congr rfl
    intro r _
    rw [card_image_of_injOn]
    · exact Fintype.card_piFinset _
    intro f hf g hg he
    funext i
    obtain ⟨j,hj⟩ := transfer he i
    have hh := fits hg j
    rw [hj,fits hf i] at hh
    cases Option.some.inj hh
    exact hj.symm
  · intro r _ t _ hrt
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨g,hg,hg'⟩ := mem_image.mp he'
    exact hrt (kind_unique hf hg hg'.symm)

lemma graph_five {n : ℕ} [NeZero n] {V : Type*} [DecidableEq V] (L : V → Col n)
    (S : Finset V) {e : Finset V} (h : e ∈ graph L S) : e.card = 5 := by
  obtain ⟨r,_,f,hf,rfl⟩ := (by simpa [graph,mem_biUnion,mem_image] using h :
    ∃ r ∈ (univ : Finset (Kind n)), ∃ f ∈ tuples L S r, edgeOf f=e)
  rw [edgeOf,card_image_of_injective]
  · simp
  · intro i j eq
    have hh := fits hf i
    rw [eq,fits hf j] at hh
    exact (Option.some.inj hh).symm

lemma graph_induced {n : ℕ} [NeZero n] {V : Type*} [Fintype V] [DecidableEq V]
    (L : V → Col n) (S : Finset V) : (graph L univ).filter (· ⊆ S) = graph L S := by
  ext e
  simp only [graph,mem_filter,mem_biUnion, mem_univ,true_and,mem_image]
  constructor
  · rintro ⟨⟨r,f,hf,rfl⟩,hs⟩
    exact ⟨r,f,Fintype.mem_piFinset.mpr fun j => mem_filter.mpr
      ⟨hs (mem_image_of_mem f (mem_univ j)), fits hf j⟩, rfl⟩
  · rintro ⟨r,f,hf,rfl⟩
    refine ⟨⟨r,f,Fintype.mem_piFinset.mpr fun j => mem_filter.mpr ⟨mem_univ _, fits hf j⟩,rfl⟩,?_⟩
    intro x hx
    obtain ⟨j,_,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp (Fintype.mem_piFinset.mp hf j)).1


abbrev side {n : ℕ} (w : Col n → ℝ) (b : Bool) (i : Fin n) := w (.inl (b,i))
abbrev cap {n : ℕ} (w : Col n → ℝ) (j : Fin 7) := w (.inr j)
abbrev dots {n : ℕ} (w : Col n → ℝ) := cap w 1 + cap w 2 + cap w 3

noncomputable def amount {n : ℕ} [NeZero n] (w : Col n → ℝ) (r : Kind n) (j : Fin 5) :=
  ∑ c, if lane r c = some j then w c else 0

lemma branch {q : Prop} [Decidable q] (x y j : Option (Fin 5)) (m : ℝ) :
    (if (if q then x else y) = j then m else 0) =
      (if q then (if x=j then m else 0) else (if y=j then m else 0)) := by split <;> split_ifs <;> simp_all

lemma except {n : ℕ} (k : Fin n) (f : Fin n → ℝ) :
    (∑ j, if j=k then 0 else f j) = ∑ j, f j - f k := by
  have eq (j) : (if j=k then 0 else f j) = f j - (if j=k then f j else 0) := by split <;> simp_all
  simp [eq,sum_sub_distrib]

lemma amounts_index {n : ℕ} [NeZero n] (w : Col n → ℝ) (b : Bool) (i : Fin n) (j : Fin 5) :
    amount w (some (b,i)) j = ![cap w 6,cap w (if b then 5 else 4),side w b i,
      side w (!b) (partner b i) + cap w 0,
      (∑ k, side w (!b) k) - side w (!b) (partner b i) + dots w] j := by
  cases b <;> fin_cases j <;>
    simp [amount,Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_succ,
      lane, branch, except,side,cap,dots,partner] <;> ring

lemma amounts_extra {n : ℕ} [NeZero n] (w : Col n → ℝ) (j : Fin 5) :
    amount w none j = ![cap w 4,cap w 5,cap w 1,cap w 2,cap w 3] j := by
  fin_cases j <;> simp [amount,Fintype.sum_sum_type,Fin.sum_univ_succ,lane,cap]


noncomputable def mass {n : ℕ} {V : Type*} (L : V → Col n) (S : Finset V) (c : Col n) : ℝ :=
  (S.filter (fun v => L v = c)).card

lemma integrate {n : ℕ} {V : Type*} (L : V → Col n) (S : Finset V) (f : Col n → ℝ) :
    ∑ c, mass L S c * f c = ∑ x ∈ S, f (L x) := by
  simpa [mass] using sum_fiberwise_of_maps_to' (s := S) (g := L) (fun x _ => mem_univ (L x)) f

lemma mass_sum {n : ℕ} {V : Type*} (L : V → Col n) (S : Finset V) :
    ∑ c, mass L S c = S.card := by simpa using integrate L S (fun _ => 1)

lemma amount_mass {n : ℕ} [NeZero n] {V : Type*} (L : V → Col n) (S : Finset V) (r : Kind n) (j : Fin 5) :
    amount (mass L S) r j = (S.filter (fun x => lane r (L x) = some j)).card := by
  simpa [amount,mul_ite] using integrate L S (fun c => if lane r c=some j then 1 else 0)

noncomputable def value {n : ℕ} [NeZero n] (w : Col n → ℝ) :=
  cap w 6 * (cap w 4 * row (side w false) (side w true) (cap w 0) (∑ i, side w true i) (dots w) +
    cap w 5 * row (side w true) (fun i => side w false (i+1)) (cap w 0) (∑ i, side w false i) (dots w)) +
    cap w 4 * cap w 5 * cap w 1 * cap w 2 * cap w 3

lemma value_count {n : ℕ} [NeZero n] {V : Type*} [DecidableEq V] (L : V → Col n) (S : Finset V) :
    ((graph L S).card : ℝ) = value (mass L S) := by
  let w := mass L S
  rw [graph_card,Nat.cast_sum]
  simp only [Nat.cast_prod, ← amount_mass]
  change (∑ r, ∏ j, amount w r j) = value w
  rw [Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool]
  have indexed (b : Bool) (i : Fin n) : (∏ j, amount w (some (b,i)) j) =
      cap w 6 * cap w (if b then 5 else 4) * (side w b i *
      (side w (!b) (partner b i) + cap w 0) *
      ((∑ k, side w (!b) k) - side w (!b) (partner b i) + dots w)) := by
    simp [amounts_index, Fin.prod_univ_succ]
    ring
  simp [indexed,amounts_extra,Fin.prod_univ_succ,partner,value,row,← mul_sum]
  ring


def size {n : ℕ} (M : ℕ) : Col n → ℕ
  | .inl _ => 6*M
  | .inr c => ![6*(n-1)*M,2*M,2*M,2*M,3*n*M,3*n*M,6*n*M] c

lemma total_size (n M : ℕ) [NeZero n] : ∑ c : Col n, size M c = 30*n*M := by
  simp [Fintype.sum_sum_type,Fin.sum_univ_succ,size]
  have hn := Nat.sub_add_cancel (show 1 ≤ n from Nat.pos_of_ne_zero (NeZero.ne n))
  nlinarith [congrArg (·*M) hn]

noncomputable def label {n : ℕ} [NeZero n] (M : ℕ) : Fin (30*n*M) → Col n :=
  fun x => ((Fintype.equivFinOfCardEq (α := Σ c : Col n, Fin (size M c))
    (by rw [Fintype.card_sigma]; simpa using total_size n M)).symm x).1

lemma label_mass {n : ℕ} [NeZero n] (M : ℕ) (c : Col n) :
    mass (label (n := n) M) univ c = size M c := by
  let eqv := Fintype.equivFinOfCardEq (α := Σ c : Col n, Fin (size M c))
    (by rw [Fintype.card_sigma]; simpa using total_size n M : Fintype.card _ = 30*n*M)
  have eq : ∑ x : Fin (30*n*M), (if label M x = c then (1:ℝ) else 0) =
      ∑ v : Σ k : Col n, Fin (size M k), if v.1=c then (1:ℝ) else 0 :=
    Equiv.sum_comp eqv.symm (fun v => if v.1=c then (1:ℝ) else 0)
  rw [sum_boole] at eq
  rw [mass, eq, Fintype.sum_sigma]
  calc
    _ = ∑ x : Col n, if x=c then (size M x : ℝ) else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases hx : x=c <;> simp [hx]
    _ = _ := by rw [sum_ite_eq']; simp

lemma witness_value (n M : ℕ) [NeZero n] :
    value (fun c : Col n => (size M c : ℝ)) = ((6*(n:ℝ))^5 + 72*n^2)*M^5 := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  simp [value,row,side,cap,dots,size,Nat.cast_sub hn]
  ring

lemma row_div {n : ℕ} (a b : Fin n → ℝ) (k B D t : ℝ) (ht : t ≠ 0) :
    row (fun i => a i/t) (fun i => b i/t) (k/t) (B/t) (D/t) = row a b k B D / t^3 := by
  unfold row
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  field_simp <;> ring

lemma combine_error (X k : ℝ) : X/3125 + X/24*(1/k) = (1/3125+1/(24*k))*X := by ring

lemma spread_error (h Q t e k : ℝ) :
    h*(Q*t^3*(1/27-e/10+1/k)) + Q^2*t^3*e/27 =
    (h*Q*t^3*(1/27-e/10)+Q^2*t^3*e/27) + h*Q*t^3*(1/k) := by ring

lemma unscale (Q t x R : ℝ) (hQ : Q ≠ 0) (ht : t ≠ 0) :
    Q*t^3*(x/Q*(R/t^3)) = x*R := by field_simp <;> ring

lemma unscale_extra (Q t u v D : ℝ) (hQ : Q ≠ 0) (ht : t ≠ 0) :
    Q^2*t^3*(u/Q*(v/Q)*(D/t)^3)/27 = u*v*(D/3)^3 := by
  field_simp
  <;> ring

set_option maxHeartbeats 350000 in
lemma raw_bound {n : ℕ} [NeZero n] (a b : Fin n → ℝ) (h u v k x y z : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hh : 0 ≤ h) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hk : 0 ≤ k) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    let A := ∑ i, a i
    let B := ∑ i, b i
    let D := x+y+z
    let Q := u+v
    let t := A+B+k+D
    h*(u*row a b k B D + v*row b (fun i => a (i+1)) k A D) + u*v*x*y*z ≤
      (1/3125+1/(24*(n:ℝ)))*(h+Q+t)^5 := by
  intro A B D Q t
  have hA : 0 ≤ A := sum_nonneg fun i _ => ha i
  have hB : 0 ≤ B := sum_nonneg fun i _ => hb i
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hQ : 0 ≤ Q := add_nonneg hu hv
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have rhs : 0 ≤ (1/3125+1/(24*(n:ℝ)))*(h+Q+t)^5 := by positivity
  rcases hQ.eq_or_lt with hQ0 | hQp
  · have h1 : u=0 := by dsimp only [Q] at hQ0; linarith only [hQ0,hu,hv]
    have h2 : v=0 := by dsimp only [Q] at hQ0; linarith only [hQ0,hu,hv]
    simpa only [h1,h2,zero_mul,add_zero,mul_zero] using rhs
  rcases ht.eq_or_lt with ht0 | htp
  · have A0 : A=0 := by dsimp only [t] at ht0; linarith only [ht0,hA,hB,hD,hk]
    have B0 : B=0 := by dsimp only [t] at ht0; linarith only [ht0,hA,hB,hD,hk]
    have X0 : x=0 := by dsimp only [t,D] at ht0; linarith only [ht0,hA,hB,hk,hx,hy,hz]
    have az (i) : a i=0 := le_antisymm ((single_le_sum (fun j _ => ha j) (mem_univ i)).trans A0.le) (ha i)
    have bz (i) : b i=0 := le_antisymm ((single_le_sum (fun j _ => hb j) (mem_univ i)).trans B0.le) (hb i)
    simpa only [row,az,bz,zero_mul,sum_const_zero,mul_zero,add_zero,X0] using rhs
  let s := u/Q
  let d := D/t
  let e := s*(1-s)*d^3
  have hs : 0 ≤ s := div_nonneg hu hQ
  have hs' : s ≤ 1 := (div_le_one hQp).2 (le_add_of_nonneg_right hv)
  have hd : 0 ≤ d := div_nonneg hD ht
  have hd' : d ≤ 1 := (div_le_one htp).2 (by dsimp only [t]; linarith only [hA,hB,hk])
  have he0 : 0 ≤ e := by dsimp [e]; exact mul_nonneg (mul_nonneg hs (sub_nonneg.mpr hs')) (pow_nonneg hd 3)
  have he1 : e ≤ 1/4 := by
    dsimp [e]
    have hd3 := pow_le_pow_left₀ hd hd' 3
    nlinarith only [mul_le_mul_of_nonneg_left hd3 (mul_nonneg hs (sub_nonneg.mpr hs')),
      sq_nonneg (s-1/2)]
  have h1s : 1-s=v/Q := by
    calc
      1-s = Q/Q-u/Q := by rw [div_self hQp.ne']
      _ = v/Q := by rw [← sub_div]; dsimp only [Q]; rw [add_sub_cancel_left]
  have cc := cubic (fun i => a i/t) (fun i => b i/t) (A/t) (B/t) (k/t) (D/t) s
    (fun i => div_nonneg (ha i) ht) (fun i => div_nonneg (hb i) ht)
    (sum_div ..).symm (sum_div ..).symm (div_nonneg hk ht) hd
    (by rw [← add_div, ← add_div, ← add_div]; exact div_self htp.ne') hs hs'
  rw [row_div a b k B D t htp.ne', row_div b (fun i => a (i+1)) k A D t htp.ne'] at cc
  change s*(_/t^3)+(1-s)*(_/t^3) ≤ 1/27-e/10+1/n at cc
  have ch := mul_le_mul_of_nonneg_left cc (show 0 ≤ Q*t^3 by positivity)
  rw [h1s] at ch
  dsimp only [s] at ch
  have cb : u*row a b k B D + v*row b (fun i => a (i+1)) k A D ≤ Q*t^3*(1/27-e/10+1/n) := by
    rwa [mul_add,unscale _ _ _ _ hQp.ne' htp.ne',unscale _ _ _ _ hQp.ne' htp.ne'] at ch
  have surplus : u*v*x*y*z ≤ Q^2*t^3*e/27 := by
    have eq : Q^2*t^3*e/27 = u*v*(D/3)^3 := by
      dsimp only [e]; rw [h1s]; exact unscale_extra _ _ _ _ _ hQp.ne' htp.ne'
    rw [eq]
    dsimp only [D]
    nlinarith only [mul_le_mul_of_nonneg_left (threeprod x y z hx hy hz) (mul_nonneg hu hv)]
  obtain ⟨s1,s2⟩ := scalar h Q t e hh hQ ht he0 he1
  have rem := mul_le_mul_of_nonneg_right s2 (show (0:ℝ) ≤ 1/n by positivity)
  calc
    _ ≤ h*(Q*t^3*(1/27-e/10+1/n)) + Q^2*t^3*e/27 :=
      add_le_add (mul_le_mul_of_nonneg_left cb hh) surplus
    _ = (h*Q*t^3*(1/27-e/10) + Q^2*t^3*e/27) + (h*Q*t^3)*(1/n) := spread_error _ _ _ _ _
    _ ≤ _ := (add_le_add s1 rem).trans_eq (combine_error _ _)

lemma value_bound {n : ℕ} [NeZero n] (w : Col n → ℝ) (hw : ∀ c, 0 ≤ w c) :
    value w ≤ (1/3125+1/(24*(n:ℝ)))*(∑ c, w c)^5 := by
  have h := raw_bound (side w false) (side w true) (cap w 6) (cap w 4) (cap w 5)
    (cap w 0) (cap w 1) (cap w 2) (cap w 3) (fun _ => hw _) (fun _ => hw _)
    (hw _) (hw _) (hw _) (hw _) (hw _) (hw _) (hw _)
  change value w ≤ _ at h
  apply h.trans_eq
  congr 2
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_succ,side,cap,dots]
  ring

end E1075

open E1075 Filter Finset

theorem OMA.disproof : ¬ (type_of% @Erdos1075.erdos_1075) := by
  classical
  intro claim
  obtain ⟨c,hc,hdense⟩ := claim 5 (by decide)
  norm_num at hc
  let δ := c-1/3125
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let n := max 2 (⌊1/(24*δ)⌋₊+1)
  have hn2 : 2 ≤ n := le_max_left .. 
  haveI : NeZero n := ⟨by omega⟩
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : 1/(24*δ) < (n : ℝ) := by
    apply (Nat.lt_floor_add_one _).trans_le
    exact_mod_cast le_max_right 2 (⌊1/(24*δ)⌋₊+1)
  have gap : 1/3125 + 1/(24*(n:ℝ)) < c := by
    have h := (div_lt_iff₀ (show 0 < 24*δ by positivity)).mp hn'
    have g : 1/(24*(n:ℝ)) < δ := (div_lt_iff₀ (by positivity)).mpr (by linarith only [h])
    dsimp [δ] at g
    linarith
  let ε := 1/(4*(3*(n:ℝ))^3)
  obtain ⟨m,hm,hev⟩ := hdense ε (by dsimp [ε]; positivity)
  have hm' : ∀ᶠ N in atTop, 1 ≤ m N := hm.eventually (eventually_ge_atTop 1)
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hev.and hm')
  let M := T+1
  let N := 30*n*M
  have hN : T ≤ N := (Nat.le_succ T).trans (Nat.le_mul_of_pos_left M (by positivity))
  obtain ⟨allH,hmN⟩ := hT N hN
  let L : Fin N → Col n := label M
  let H := graph L univ
  have hcount : ((H.card : ℝ)) = ((6*(n:ℝ))^5+72*n^2)*M^5 := by
    rw [show H=graph L univ from rfl, value_count]
    have eq : mass L univ = fun c => (size M c : ℝ) := funext (label_mass M)
    rw [eq,witness_value]
  have enough : (1+ε)*((N:ℝ)/5)^5 ≤ H.card := by
    rw [hcount]
    apply le_of_eq
    dsimp only [N,ε]
    push_cast
    field_simp [hn.ne']
    <;> ring
  obtain ⟨S,hS,lower⟩ := allH H (fun e he => graph_five L univ he) enough
  have positive : 0 < (S.card : ℝ) := by exact_mod_cast (show 0 < S.card by omega)
  have upper := value_bound (mass L S) (fun c => Nat.cast_nonneg _)
  rw [mass_sum, ← value_count] at upper
  change c * (S.card : ℝ)^5 ≤ (((graph L univ).filter (· ⊆ S)).card : ℝ) at lower
  rw [graph_induced] at lower
  exact (not_lt_of_ge (lower.trans upper)) (mul_lt_mul_of_pos_right gap (pow_pos positive 5))

