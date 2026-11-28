import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R2
import Mathlib

/-! The divisor-sum gap for all positive exponents on the supports {3,5,7}, {3,5,11}, and {3,5,13}. Rational interval bounds cover the infinite exponent ranges. The boundary rectangles use exact prime-power divisibility and kernel-checked finite arithmetic. The multiplicativity argument follows the earlier merged A245212 reduction. -/
open Finset
namespace A245212Local

def geom (p e : ℕ) : ℕ := ∑ j ∈ range (e+1), p^j
def moment (p e : ℕ) : ℕ := ∑ j ∈ range (e+1), p^j*(j+1)
def top (p e : ℕ) := p^e*(e+1)

lemma power_id (p e : ℕ) (hp : 1 ≤ p) :
    (p-1)*geom p e+1=p^(e+1) ∧ (p-1)*moment p e+geom p e=p*top p e := by
  rw [show p*top p e = (e+1)*p^(e+1) by unfold top; rw [pow_succ]; ring]
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p≠0)
  unfold geom moment
  simp only [Nat.add_one_sub_one]
  induction e with
  | zero => simp
  | succ e ih =>
    obtain ⟨h₁,h₂⟩ := ih
    rw [sum_range_succ (fun j => (p+1)^j) (e+1),
      sum_range_succ (fun j => (p+1)^j*(j+1)) (e+1),pow_succ (p+1) (e+1)]
    constructor <;> nlinarith only [h₁,h₂]

lemma remainder_dvd (p e W S T : ℕ) (hp : 1 ≤ p)
    (balance : W*moment p e+S*geom p e = 2*T*top p e) :
    (p^e : ℤ) ∣ (W : ℤ)-((p:ℤ)-1)*S := by
  obtain ⟨hg,hw⟩ := power_id p e hp
  zify [hp] at hg hw balance
  simp only [top, Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] at hw balance
  rw [pow_succ] at hg
  use -((p:ℤ)*((p:ℤ)-1)*(e+1)*W - (p:ℤ)*(W-((p:ℤ)-1)*S) - 2*T*(e+1)*((p:ℤ)-1)^2)
  linear_combination (norm := ring_nf) -(W : ℤ)*((p:ℤ)-1)*hw -
    (((p:ℤ)-1)*(S:ℤ)-(W:ℤ))*hg + ((p:ℤ)-1)^2*balance

def geomRatio (p e : ℕ) : ℚ := (geom p e : ℚ)/(top p e)
def momentRatio (p e : ℕ) : ℚ := (moment p e : ℚ)/(top p e)

lemma geomRatio_avg (p e : ℕ) (hp : 1 ≤ p) :
    geomRatio p e = (∑ j ∈ range (e+1), ((p:ℚ)⁻¹)^j)/(e+1 : ℕ) := by
  have h : (p:ℚ)≠0 := by positivity
  rw [geomRatio,top,Nat.cast_mul,Nat.cast_pow,div_mul_eq_div_div,geom,Nat.cast_sum]
  congr 1
  rw [Finset.sum_div]
  rw [← Finset.sum_range_reflect (fun j => ((p:ℚ)⁻¹)^j) (e+1)]
  apply sum_congr rfl
  intro j hj
  have hje : j ≤ e := by simpa using Finset.mem_range.mp hj
  push_cast
  rw [inv_pow, div_eq_iff (pow_ne_zero e h)]
  rw [inv_mul_eq_div, eq_div_iff (pow_ne_zero _ h), ← pow_add, Nat.add_sub_of_le hje]

lemma geomRatio_anti (p : ℕ) (hp : 1≤p) : Antitone (geomRatio p) := by
  apply antitone_nat_of_succ_le
  intro e
  rw [geomRatio_avg p _ hp,geomRatio_avg p _ hp,sum_range_succ]
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hx : (0 : ℚ) ≤ (p:ℚ)⁻¹ := by positivity
  have hx' : (p:ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp)
  have H : ∑ _j ∈ range (e+1), ((p:ℚ)⁻¹)^(e+1) ≤ ∑ j ∈ range (e+1), ((p:ℚ)⁻¹)^j :=
    sum_le_sum (fun j hj => pow_le_pow_of_le_one hx hx' (Finset.mem_range.mp hj).le)
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at H
  linarith

lemma top_pos {p : ℕ} (hp : 1 ≤ p) (e : ℕ) : 0 < top p e := by unfold top; positivity

lemma affine {p : ℕ} (hp : 1 ≤ p) (e : ℕ) :
    ((p:ℚ)-1)*momentRatio p e + geomRatio p e = p := by
  have hn : (top p e : ℚ) ≠ 0 := by exact_mod_cast (top_pos hp e).ne'
  have h := (power_id p e hp).2
  qify [hp] at h
  unfold momentRatio geomRatio
  field_simp
  linarith

def low (p e : ℕ) : ℚ :=
  if e=0 then 0 else geomRatio p (min e 8) * ((min e 8:ℕ)+1) / ((e:ℚ)+1)
def high (p e : ℕ) : ℚ :=
  if e≤8 then geomRatio p e else (p:ℚ) / (((p:ℚ)-1)*(e+1))

lemma low_le {p e : ℕ} (hp : 1 ≤ p) : low p e ≤ geomRatio p e := by
  unfold low
  split_ifs with h
  · unfold geomRatio; positivity
  rw [geomRatio_avg p _ hp,geomRatio_avg p _ hp]
  push_cast
  rw [div_mul_cancel₀ _ (by positivity)]
  gcongr
  exact min_le_left _ _

lemma le_high {p e : ℕ} (hp : 2≤p) : geomRatio p e ≤ high p e := by
  unfold high
  split_ifs with h
  · rfl
  have pos : (0:ℚ) < p-1 := by
    have h2 : (2:ℚ)≤p := by exact_mod_cast hp
    linarith
  have H := (power_id p e (by omega)).1
  qify [show 1≤p by omega] at H
  unfold geomRatio top
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [pow_succ] at H
  have A : (geom p e:ℚ)*((p:ℚ)-1) ≤ p*p^e := by linarith
  nlinarith only [mul_le_mul_of_nonneg_right A (show 0≤(e:ℚ)+1 by positivity)]

structure Box where
  lo : ℕ
  hi : ℕ
  deriving DecidableEq,Repr

def Fits (B : Box) (e : ℕ) : Prop := B.lo ≤ e ∧ (B.hi=0 ∨ e≤B.hi)

lemma ratio_bounds {p e : ℕ} (hp : 2 ≤ p) {B : Box} (h : Fits B e) :
    low p B.hi ≤ geomRatio p e ∧ geomRatio p e ≤ high p B.lo := by
  constructor
  · rcases h.2 with hz|he
    · simp only [low,hz,if_pos rfl]
      unfold geomRatio
      positivity
    · exact (low_le (by omega)).trans ((geomRatio_anti p (by omega)) he)
  · exact ((geomRatio_anti p (by omega)) h.1).trans (le_high hp)

def weightLo (p : ℕ) (B : Box) := ((p:ℚ)-high p B.lo)/((p:ℚ)-1)
def weightHi (p : ℕ) (B : Box) := ((p:ℚ)-low p B.hi)/((p:ℚ)-1)

lemma weight_bounds {p e : ℕ} (hp : 2 ≤ p) {B : Box} (h : Fits B e) :
    weightLo p B ≤ momentRatio p e ∧ momentRatio p e ≤ weightHi p B := by
  obtain ⟨l,u⟩ := ratio_bounds hp h
  have pos : 0 < (p:ℚ)-1 := by
    have h2 : (2:ℚ)≤p := by exact_mod_cast hp
    linarith
  have eq := affine (show 1≤p by omega) e
  constructor
  · rw [weightLo,div_le_iff₀ pos]; linarith
  · rw [weightHi,le_div_iff₀ pos]; linarith

def Safe (p q r a b c : ℕ) : Prop :=
  moment p a * moment q b * moment r c + geom p a * geom q b * geom r c ≠
    2 * (top p a * top q b * top r c)

def Valid (p q r : ℕ) (A B C : Box) : Prop :=
  ∀ a b c, Fits A a → Fits B b → Fits C c → Safe p q r a b c

def cutLow (A : Box) (k : ℕ) : Box := ⟨A.lo,k⟩
def cutHigh (A : Box) (k : ℕ) : Box := ⟨k+1,A.hi⟩

lemma splitA {p q r k : ℕ} {A B C : Box}
    (l : Valid p q r (cutLow A k) B C) (h : Valid p q r (cutHigh A k) B C) : Valid p q r A B C := by
  intro a b c ha hb hc
  by_cases H : a≤k
  · exact l _ _ _ ⟨ha.1,Or.inr H⟩ hb hc
  · exact h _ _ _ ⟨by change k+1≤a; omega,ha.2⟩ hb hc

lemma rotate {p q r a b c : ℕ} : Safe q r p b c a → Safe p q r a b c := by
  unfold Safe
  convert id using 1 <;> ring_nf

lemma cycle {p q r : ℕ} {A B C : Box} (h : Valid q r p B C A) : Valid p q r A B C := by
  intro a b c ha hb hc
  exact rotate (h _ _ _ hb hc ha)

lemma normalized {p q r a b c : ℕ} (hp : 1≤p) (hq : 1≤q) (hr : 1≤r)
    (h : ¬ Safe p q r a b c) :
    momentRatio p a * momentRatio q b * momentRatio r c +
      geomRatio p a * geomRatio q b * geomRatio r c = 2 := by
  classical
  obtain eq := not_not.mp h
  have hp' : (top p a : ℚ) ≠ 0 := by exact_mod_cast (top_pos hp a).ne'
  have hq' : (top q b : ℚ) ≠ 0 := by exact_mod_cast (top_pos hq b).ne'
  have hr' : (top r c : ℚ) ≠ 0 := by exact_mod_cast (top_pos hr c).ne'
  unfold momentRatio geomRatio
  field_simp
  qify at eq
  linarith

def upper (p q r : ℕ) (A B C : Box) :=
  weightHi p A * weightHi q B * weightHi r C + high p A.lo * high q B.lo * high r C.lo

def lower (p q r : ℕ) (A B C : Box) :=
  weightLo p A * weightLo q B * weightLo r C + low p A.hi * low q B.hi * low r C.hi

lemma mul3_le {a b c A B C : ℚ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hA : a≤A) (hB : b≤B) (hC : c≤C) : a*b*c ≤ A*B*C :=
  mul_le_mul (mul_le_mul hA hB hb (ha.trans hA)) hC hc
    (mul_nonneg (ha.trans hA) (hb.trans hB))

lemma validUpper {p q r : ℕ} {A B C : Box} (hp : 2≤p) (hq : 2≤q) (hr : 2≤r)
    (test : upper p q r A B C < 2) : Valid p q r A B C := by
  intro a b c ha hb hc
  by_contra h
  have H := normalized (by omega : 1≤p) (by omega : 1≤q) (by omega : 1≤r) h
  have gn (s t : ℕ) : 0 ≤ geomRatio s t := by unfold geomRatio; positivity
  have wn (s t : ℕ) : 0 ≤ momentRatio s t := by unfold momentRatio; positivity
  apply (not_le_of_gt test)
  rw [← H]
  unfold upper
  exact add_le_add
    (mul3_le (wn _ _) (wn _ _) (wn _ _) (weight_bounds hp ha).2 (weight_bounds hq hb).2 (weight_bounds hr hc).2)
    (mul3_le (gn _ _) (gn _ _) (gn _ _) (ratio_bounds hp ha).2 (ratio_bounds hq hb).2 (ratio_bounds hr hc).2)

lemma validLower {p q r : ℕ} {A B C : Box} (hp : 2≤p) (hq : 2≤q) (hr : 2≤r)
    (hn : 0 ≤ weightLo p A ∧ 0 ≤ weightLo q B ∧ 0 ≤ weightLo r C ∧
      0 ≤ low p A.hi ∧ 0 ≤ low q B.hi ∧ 0 ≤ low r C.hi)
    (test : 2 < lower p q r A B C) : Valid p q r A B C := by
  intro a b c ha hb hc
  by_contra h
  have H := normalized (by omega : 1≤p) (by omega : 1≤q) (by omega : 1≤r) h
  obtain ⟨w1,w2,w3,g1,g2,g3⟩ := hn
  apply (not_le_of_gt test)
  rw [← H]
  unfold lower
  exact add_le_add
    (mul3_le w1 w2 w3 (weight_bounds hp ha).1 (weight_bounds hq hb).1 (weight_bounds hr hc).1)
    (mul3_le g1 g2 g3 (ratio_bounds hp ha).1 (ratio_bounds hq hb).1 (ratio_bounds hr hc).1)

def fastGeom (p e : ℕ) := (p^(e+1)-1)/(p-1)
def fastMoment (p e : ℕ) := (p*top p e-fastGeom p e)/(p-1)

lemma fast_eq (p e : ℕ) (hp : 2 ≤ p) :
    fastGeom p e = geom p e ∧ fastMoment p e = moment p e := by
  obtain ⟨h₁,h₂⟩ := power_id p e (by omega)
  have h : fastGeom p e = geom p e := by
    rw [fastGeom,←h₁,Nat.add_sub_cancel,Nat.mul_div_cancel_left _ (by omega)]
  refine ⟨h,?_⟩
  rw [fastMoment,h,←h₂,Nat.add_sub_cancel,Nat.mul_div_cancel_left _ (by omega)]

def singleCheck (p lo k W S T : ℕ) : Bool :=
  decide (¬ (p^k : ℤ) ∣ (W:ℤ)-((p:ℤ)-1)*S) &&
  (List.range k).all fun e => decide (e < lo ∨ W*fastMoment p e+S*fastGeom p e ≠ 2*T*top p e)

def rectangle (p q r : ℕ) (A B C : Box) (k : ℕ) : Bool :=
  (List.range (B.hi+1-B.lo)).all fun j =>
    (List.range (C.hi+1-C.lo)).all fun i =>
      let b := j+B.lo
      let c := i+C.lo
      singleCheck p A.lo k (fastMoment q b*fastMoment r c) (fastGeom q b*fastGeom r c)
        (top q b*top r c)

lemma validRect {p q r k : ℕ} {A B C : Box} (hp : 2≤p) (hq : 2≤q) (hr : 2≤r)
    (hbnd : B.hi ≠ 0 ∧ C.hi ≠ 0) (test : rectangle p q r A B C k = true) :
    Valid p q r A B C := by
  intro a b c ha hb hc
  obtain ⟨hB,hC⟩ := hbnd
  obtain ⟨hbl,hbu⟩ := hb
  obtain ⟨hcl,hcu⟩ := hc
  simp only [hB,hC,false_or] at hbu hcu
  simp only [rectangle,List.all_eq_true,List.mem_range] at test
  have H := test (b-B.lo) (by omega) (c-C.lo) (by omega)
  rw [Nat.sub_add_cancel hbl,Nat.sub_add_cancel hcl] at H
  simp only [singleCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,
    (fast_eq q b hq).1,(fast_eq q b hq).2,(fast_eq r c hr).1,(fast_eq r c hr).2] at H
  intro eq
  let W := moment q b*moment r c
  let S := geom q b*geom r c
  let T := top q b*top r c
  have heq : W*moment p a+S*geom p a=2*T*top p a := by
    dsimp [W,S,T]
    convert eq using 1 <;> ring
  by_cases h : a<k
  · obtain bad := (H.2 a h).resolve_left (Nat.not_lt.mpr ha.1)
    rw [(fast_eq p a hp).1,(fast_eq p a hp).2] at bad
    exact bad heq
  · apply H.1
    exact (pow_dvd_pow (p:ℤ) (by omega : k≤a)).trans (remainder_dvd p a W S T (by omega) heq)

lemma splitB {p q r k : ℕ} {A B C : Box}
    (l : Valid p q r A (cutLow B k) C) (h : Valid p q r A (cutHigh B k) C) : Valid p q r A B C := by
  intro a b c ha hb hc
  by_cases H : b≤k
  · exact l _ _ _ ha ⟨hb.1,Or.inr H⟩ hc
  · exact h _ _ _ ha ⟨by change k+1≤b; omega,hb.2⟩ hc

lemma splitC {p q r k : ℕ} {A B C : Box}
    (l : Valid p q r A B (cutLow C k)) (h : Valid p q r A B (cutHigh C k)) : Valid p q r A B C := by
  intro a b c ha hb hc
  by_cases H : c≤k
  · exact l _ _ _ ha hb ⟨hc.1,Or.inr H⟩
  · exact h _ _ _ ha hb ⟨by change k+1≤c; omega,hc.2⟩

end A245212Local

namespace A245212Local
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_0 : Valid 3 5 7 ⟨1,1⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_1 : Valid 3 5 7 ⟨2,3⟩ ⟨1,1⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_2 : Valid 3 5 7 ⟨2,3⟩ ⟨2,3⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_3 : Valid 3 5 7 ⟨2,3⟩ ⟨4,0⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_4 : Valid 3 5 7 ⟨2,3⟩ ⟨2,0⟩ ⟨1,0⟩ :=
  splitB (k := 3) box7_2 box7_3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_5 : Valid 3 5 7 ⟨2,3⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  splitB (k := 1) box7_1 box7_4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_6 : Valid 3 5 7 ⟨4,7⟩ ⟨1,1⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_7 : Valid 3 5 7 ⟨8,0⟩ ⟨1,1⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_8 : Valid 3 5 7 ⟨4,0⟩ ⟨1,1⟩ ⟨1,0⟩ :=
  splitA (k := 7) box7_6 box7_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_9 : Valid 3 5 7 ⟨4,7⟩ ⟨2,3⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_10 : Valid 3 5 7 ⟨4,7⟩ ⟨4,0⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_11 : Valid 3 5 7 ⟨4,7⟩ ⟨4,0⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_12 : Valid 3 5 7 ⟨4,7⟩ ⟨4,7⟩ ⟨4,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_13 : Valid 3 5 7 ⟨4,5⟩ ⟨8,0⟩ ⟨4,7⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_14 : Valid 3 5 7 ⟨4,5⟩ ⟨8,15⟩ ⟨8,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_15 : Valid 3 5 7 ⟨4,4⟩ ⟨16,0⟩ ⟨8,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_16 : Valid 3 5 7 ⟨5,5⟩ ⟨16,0⟩ ⟨8,15⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_17 : Valid 3 5 7 ⟨5,5⟩ ⟨16,31⟩ ⟨16,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_18 : Valid 3 5 7 ⟨5,5⟩ ⟨32,0⟩ ⟨16,31⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_19 : Valid 3 5 7 ⟨5,5⟩ ⟨32,63⟩ ⟨32,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_20 : Valid 3 5 7 ⟨5,5⟩ ⟨64,0⟩ ⟨32,63⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_21 : Valid 3 5 7 ⟨5,5⟩ ⟨64,127⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_22 : Valid 3 5 7 ⟨5,5⟩ ⟨128,0⟩ ⟨64,127⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_23 : Valid 3 5 7 ⟨5,5⟩ ⟨128,255⟩ ⟨128,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_24 : Valid 3 5 7 ⟨5,5⟩ ⟨256,0⟩ ⟨128,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_25 : Valid 3 5 7 ⟨5,5⟩ ⟨128,0⟩ ⟨128,0⟩ :=
  splitB (k := 255) box7_23 box7_24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_26 : Valid 3 5 7 ⟨5,5⟩ ⟨128,0⟩ ⟨64,0⟩ :=
  splitC (k := 127) box7_22 box7_25

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_27 : Valid 3 5 7 ⟨5,5⟩ ⟨64,0⟩ ⟨64,0⟩ :=
  splitB (k := 127) box7_21 box7_26

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_28 : Valid 3 5 7 ⟨5,5⟩ ⟨64,0⟩ ⟨32,0⟩ :=
  splitC (k := 63) box7_20 box7_27

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_29 : Valid 3 5 7 ⟨5,5⟩ ⟨32,0⟩ ⟨32,0⟩ :=
  splitB (k := 63) box7_19 box7_28

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_30 : Valid 3 5 7 ⟨5,5⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  splitC (k := 31) box7_18 box7_29

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_31 : Valid 3 5 7 ⟨5,5⟩ ⟨16,0⟩ ⟨16,0⟩ :=
  splitB (k := 31) box7_17 box7_30

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_32 : Valid 3 5 7 ⟨5,5⟩ ⟨16,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box7_16 box7_31

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_33 : Valid 3 5 7 ⟨4,5⟩ ⟨16,0⟩ ⟨8,0⟩ :=
  splitA (k := 4) box7_15 box7_32

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_34 : Valid 3 5 7 ⟨4,5⟩ ⟨8,0⟩ ⟨8,0⟩ :=
  splitB (k := 15) box7_14 box7_33

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_35 : Valid 3 5 7 ⟨4,5⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  splitC (k := 7) box7_13 box7_34

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_36 : Valid 3 5 7 ⟨6,7⟩ ⟨8,0⟩ ⟨4,7⟩ :=
  cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_37 : Valid 3 5 7 ⟨6,7⟩ ⟨8,15⟩ ⟨8,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_38 : Valid 3 5 7 ⟨6,7⟩ ⟨16,0⟩ ⟨8,15⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_39 : Valid 3 5 7 ⟨6,7⟩ ⟨16,31⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_40 : Valid 3 5 7 ⟨6,6⟩ ⟨32,0⟩ ⟨16,31⟩ :=
  cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_41 : Valid 3 5 7 ⟨6,6⟩ ⟨32,0⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_42 : Valid 3 5 7 ⟨6,6⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  splitC (k := 31) box7_40 box7_41

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_43 : Valid 3 5 7 ⟨7,7⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_44 : Valid 3 5 7 ⟨6,7⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  splitA (k := 6) box7_42 box7_43

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_45 : Valid 3 5 7 ⟨6,7⟩ ⟨16,0⟩ ⟨16,0⟩ :=
  splitB (k := 31) box7_39 box7_44

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_46 : Valid 3 5 7 ⟨6,7⟩ ⟨16,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box7_38 box7_45

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_47 : Valid 3 5 7 ⟨6,7⟩ ⟨8,0⟩ ⟨8,0⟩ :=
  splitB (k := 15) box7_37 box7_46

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_48 : Valid 3 5 7 ⟨6,7⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  splitC (k := 7) box7_36 box7_47

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_49 : Valid 3 5 7 ⟨4,7⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  splitA (k := 5) box7_35 box7_48

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_50 : Valid 3 5 7 ⟨4,7⟩ ⟨4,0⟩ ⟨4,0⟩ :=
  splitB (k := 7) box7_12 box7_49

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_51 : Valid 3 5 7 ⟨4,7⟩ ⟨4,0⟩ ⟨2,0⟩ :=
  splitC (k := 3) box7_11 box7_50

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_52 : Valid 3 5 7 ⟨4,7⟩ ⟨4,0⟩ ⟨1,0⟩ :=
  splitC (k := 1) box7_10 box7_51

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_53 : Valid 3 5 7 ⟨4,7⟩ ⟨2,0⟩ ⟨1,0⟩ :=
  splitB (k := 3) box7_9 box7_52

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_54 : Valid 3 5 7 ⟨8,0⟩ ⟨2,3⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_55 : Valid 3 5 7 ⟨8,15⟩ ⟨2,3⟩ ⟨2,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_56 : Valid 3 5 7 ⟨16,0⟩ ⟨2,3⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_57 : Valid 3 5 7 ⟨16,31⟩ ⟨2,3⟩ ⟨4,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_58 : Valid 3 5 7 ⟨32,0⟩ ⟨2,3⟩ ⟨4,7⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_59 : Valid 3 5 7 ⟨32,63⟩ ⟨2,2⟩ ⟨8,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_60 : Valid 3 5 7 ⟨64,0⟩ ⟨2,2⟩ ⟨8,15⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_61 : Valid 3 5 7 ⟨64,127⟩ ⟨2,2⟩ ⟨16,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_62 : Valid 3 5 7 ⟨128,0⟩ ⟨2,2⟩ ⟨16,31⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_63 : Valid 3 5 7 ⟨128,0⟩ ⟨2,2⟩ ⟨32,63⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_64 : Valid 3 5 7 ⟨128,255⟩ ⟨2,2⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_65 : Valid 3 5 7 ⟨256,0⟩ ⟨2,2⟩ ⟨64,127⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_66 : Valid 3 5 7 ⟨256,0⟩ ⟨2,2⟩ ⟨128,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_67 : Valid 3 5 7 ⟨256,0⟩ ⟨2,2⟩ ⟨64,0⟩ :=
  splitC (k := 127) box7_65 box7_66

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_68 : Valid 3 5 7 ⟨128,0⟩ ⟨2,2⟩ ⟨64,0⟩ :=
  splitA (k := 255) box7_64 box7_67

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_69 : Valid 3 5 7 ⟨128,0⟩ ⟨2,2⟩ ⟨32,0⟩ :=
  splitC (k := 63) box7_63 box7_68

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_70 : Valid 3 5 7 ⟨128,0⟩ ⟨2,2⟩ ⟨16,0⟩ :=
  splitC (k := 31) box7_62 box7_69

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_71 : Valid 3 5 7 ⟨64,0⟩ ⟨2,2⟩ ⟨16,0⟩ :=
  splitA (k := 127) box7_61 box7_70

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_72 : Valid 3 5 7 ⟨64,0⟩ ⟨2,2⟩ ⟨8,0⟩ :=
  splitC (k := 15) box7_60 box7_71

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_73 : Valid 3 5 7 ⟨32,0⟩ ⟨2,2⟩ ⟨8,0⟩ :=
  splitA (k := 63) box7_59 box7_72

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_74 : Valid 3 5 7 ⟨32,63⟩ ⟨3,3⟩ ⟨8,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_75 : Valid 3 5 7 ⟨64,0⟩ ⟨3,3⟩ ⟨8,15⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_76 : Valid 3 5 7 ⟨64,0⟩ ⟨3,3⟩ ⟨16,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_77 : Valid 3 5 7 ⟨64,0⟩ ⟨3,3⟩ ⟨8,0⟩ :=
  splitC (k := 15) box7_75 box7_76

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_78 : Valid 3 5 7 ⟨32,0⟩ ⟨3,3⟩ ⟨8,0⟩ :=
  splitA (k := 63) box7_74 box7_77

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_79 : Valid 3 5 7 ⟨32,0⟩ ⟨2,3⟩ ⟨8,0⟩ :=
  splitB (k := 2) box7_73 box7_78

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_80 : Valid 3 5 7 ⟨32,0⟩ ⟨2,3⟩ ⟨4,0⟩ :=
  splitC (k := 7) box7_58 box7_79

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_81 : Valid 3 5 7 ⟨16,0⟩ ⟨2,3⟩ ⟨4,0⟩ :=
  splitA (k := 31) box7_57 box7_80

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_82 : Valid 3 5 7 ⟨16,0⟩ ⟨2,3⟩ ⟨2,0⟩ :=
  splitC (k := 3) box7_56 box7_81

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_83 : Valid 3 5 7 ⟨8,0⟩ ⟨2,3⟩ ⟨2,0⟩ :=
  splitA (k := 15) box7_55 box7_82

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_84 : Valid 3 5 7 ⟨8,0⟩ ⟨2,3⟩ ⟨1,0⟩ :=
  splitC (k := 1) box7_54 box7_83

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_85 : Valid 3 5 7 ⟨8,15⟩ ⟨4,0⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_86 : Valid 3 5 7 ⟨16,0⟩ ⟨4,7⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_87 : Valid 3 5 7 ⟨16,31⟩ ⟨8,0⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_88 : Valid 3 5 7 ⟨32,0⟩ ⟨8,15⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_89 : Valid 3 5 7 ⟨32,63⟩ ⟨16,0⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_90 : Valid 3 5 7 ⟨64,0⟩ ⟨16,31⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_91 : Valid 3 5 7 ⟨64,127⟩ ⟨32,0⟩ ⟨1,1⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_92 : Valid 3 5 7 ⟨128,0⟩ ⟨32,63⟩ ⟨1,1⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_93 : Valid 3 5 7 ⟨128,255⟩ ⟨64,0⟩ ⟨1,1⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_94 : Valid 3 5 7 ⟨256,0⟩ ⟨64,127⟩ ⟨1,1⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_95 : Valid 3 5 7 ⟨256,0⟩ ⟨128,0⟩ ⟨1,1⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_96 : Valid 3 5 7 ⟨256,0⟩ ⟨64,0⟩ ⟨1,1⟩ :=
  splitB (k := 127) box7_94 box7_95

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_97 : Valid 3 5 7 ⟨128,0⟩ ⟨64,0⟩ ⟨1,1⟩ :=
  splitA (k := 255) box7_93 box7_96

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_98 : Valid 3 5 7 ⟨128,0⟩ ⟨32,0⟩ ⟨1,1⟩ :=
  splitB (k := 63) box7_92 box7_97

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_99 : Valid 3 5 7 ⟨64,0⟩ ⟨32,0⟩ ⟨1,1⟩ :=
  splitA (k := 127) box7_91 box7_98

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_100 : Valid 3 5 7 ⟨64,0⟩ ⟨16,0⟩ ⟨1,1⟩ :=
  splitB (k := 31) box7_90 box7_99

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_101 : Valid 3 5 7 ⟨32,0⟩ ⟨16,0⟩ ⟨1,1⟩ :=
  splitA (k := 63) box7_89 box7_100

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_102 : Valid 3 5 7 ⟨32,0⟩ ⟨8,0⟩ ⟨1,1⟩ :=
  splitB (k := 15) box7_88 box7_101

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_103 : Valid 3 5 7 ⟨16,0⟩ ⟨8,0⟩ ⟨1,1⟩ :=
  splitA (k := 31) box7_87 box7_102

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_104 : Valid 3 5 7 ⟨16,0⟩ ⟨4,0⟩ ⟨1,1⟩ :=
  splitB (k := 7) box7_86 box7_103

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_105 : Valid 3 5 7 ⟨8,0⟩ ⟨4,0⟩ ⟨1,1⟩ :=
  splitA (k := 15) box7_85 box7_104

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_106 : Valid 3 5 7 ⟨8,15⟩ ⟨4,0⟩ ⟨2,3⟩ :=
  cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_107 : Valid 3 5 7 ⟨8,15⟩ ⟨4,7⟩ ⟨4,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_108 : Valid 3 5 7 ⟨8,15⟩ ⟨8,0⟩ ⟨4,7⟩ :=
  cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_109 : Valid 3 5 7 ⟨8,11⟩ ⟨8,15⟩ ⟨8,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_110 : Valid 3 5 7 ⟨8,11⟩ ⟨16,0⟩ ⟨8,15⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_111 : Valid 3 5 7 ⟨8,11⟩ ⟨16,0⟩ ⟨16,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_112 : Valid 3 5 7 ⟨8,11⟩ ⟨16,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box7_110 box7_111

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_113 : Valid 3 5 7 ⟨8,11⟩ ⟨8,0⟩ ⟨8,0⟩ :=
  splitB (k := 15) box7_109 box7_112

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_114 : Valid 3 5 7 ⟨12,15⟩ ⟨8,0⟩ ⟨8,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_115 : Valid 3 5 7 ⟨8,15⟩ ⟨8,0⟩ ⟨8,0⟩ :=
  splitA (k := 11) box7_113 box7_114

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_116 : Valid 3 5 7 ⟨8,15⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  splitC (k := 7) box7_108 box7_115

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_117 : Valid 3 5 7 ⟨8,15⟩ ⟨4,0⟩ ⟨4,0⟩ :=
  splitB (k := 7) box7_107 box7_116

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_118 : Valid 3 5 7 ⟨8,15⟩ ⟨4,0⟩ ⟨2,0⟩ :=
  splitC (k := 3) box7_106 box7_117

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_119 : Valid 3 5 7 ⟨16,0⟩ ⟨4,7⟩ ⟨2,3⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_120 : Valid 3 5 7 ⟨16,31⟩ ⟨8,0⟩ ⟨2,3⟩ :=
  cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_121 : Valid 3 5 7 ⟨32,0⟩ ⟨8,15⟩ ⟨2,3⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_122 : Valid 3 5 7 ⟨32,0⟩ ⟨16,0⟩ ⟨2,3⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_123 : Valid 3 5 7 ⟨32,0⟩ ⟨8,0⟩ ⟨2,3⟩ :=
  splitB (k := 15) box7_121 box7_122

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_124 : Valid 3 5 7 ⟨16,0⟩ ⟨8,0⟩ ⟨2,3⟩ :=
  splitA (k := 31) box7_120 box7_123

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_125 : Valid 3 5 7 ⟨16,0⟩ ⟨4,0⟩ ⟨2,3⟩ :=
  splitB (k := 7) box7_119 box7_124

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_126 : Valid 3 5 7 ⟨16,31⟩ ⟨4,7⟩ ⟨4,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_127 : Valid 3 5 7 ⟨32,0⟩ ⟨4,7⟩ ⟨4,7⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_128 : Valid 3 5 7 ⟨32,0⟩ ⟨4,7⟩ ⟨8,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_129 : Valid 3 5 7 ⟨32,0⟩ ⟨4,7⟩ ⟨4,0⟩ :=
  splitC (k := 7) box7_127 box7_128

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_130 : Valid 3 5 7 ⟨16,0⟩ ⟨4,7⟩ ⟨4,0⟩ :=
  splitA (k := 31) box7_126 box7_129

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_131 : Valid 3 5 7 ⟨16,31⟩ ⟨8,0⟩ ⟨4,7⟩ :=
  cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_132 : Valid 3 5 7 ⟨16,31⟩ ⟨8,0⟩ ⟨8,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_133 : Valid 3 5 7 ⟨16,31⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  splitC (k := 7) box7_131 box7_132

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_134 : Valid 3 5 7 ⟨32,0⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_135 : Valid 3 5 7 ⟨16,0⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  splitA (k := 31) box7_133 box7_134

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_136 : Valid 3 5 7 ⟨16,0⟩ ⟨4,0⟩ ⟨4,0⟩ :=
  splitB (k := 7) box7_130 box7_135

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_137 : Valid 3 5 7 ⟨16,0⟩ ⟨4,0⟩ ⟨2,0⟩ :=
  splitC (k := 3) box7_125 box7_136

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_138 : Valid 3 5 7 ⟨8,0⟩ ⟨4,0⟩ ⟨2,0⟩ :=
  splitA (k := 15) box7_118 box7_137

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_139 : Valid 3 5 7 ⟨8,0⟩ ⟨4,0⟩ ⟨1,0⟩ :=
  splitC (k := 1) box7_105 box7_138

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_140 : Valid 3 5 7 ⟨8,0⟩ ⟨2,0⟩ ⟨1,0⟩ :=
  splitB (k := 3) box7_84 box7_139

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_141 : Valid 3 5 7 ⟨4,0⟩ ⟨2,0⟩ ⟨1,0⟩ :=
  splitA (k := 7) box7_53 box7_140

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_142 : Valid 3 5 7 ⟨4,0⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  splitB (k := 1) box7_8 box7_141

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_143 : Valid 3 5 7 ⟨2,0⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  splitA (k := 3) box7_5 box7_142

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box7_144 : Valid 3 5 7 ⟨1,0⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  splitA (k := 1) box7_0 box7_143

theorem triples7 : Valid 3 5 7 ⟨1,0⟩ ⟨1,0⟩ ⟨1,0⟩ := box7_144
end A245212Local

namespace A245212Local
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_0 : Valid 3 5 11 ⟨1,1⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_1 : Valid 3 5 11 ⟨2,3⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_2 : Valid 3 5 11 ⟨4,0⟩ ⟨1,1⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_3 : Valid 3 5 11 ⟨4,7⟩ ⟨2,3⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_4 : Valid 3 5 11 ⟨4,7⟩ ⟨4,0⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_5 : Valid 3 5 11 ⟨4,7⟩ ⟨2,0⟩ ⟨1,0⟩ :=
  splitB (k := 3) box11_3 box11_4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_6 : Valid 3 5 11 ⟨8,0⟩ ⟨2,3⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_7 : Valid 3 5 11 ⟨8,15⟩ ⟨4,7⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_8 : Valid 3 5 11 ⟨8,15⟩ ⟨8,0⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_9 : Valid 3 5 11 ⟨8,15⟩ ⟨8,0⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_10 : Valid 3 5 11 ⟨8,11⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_11 : Valid 3 5 11 ⟨12,15⟩ ⟨8,15⟩ ⟨4,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_12 : Valid 3 5 11 ⟨12,15⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_13 : Valid 3 5 11 ⟨12,15⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  splitB (k := 15) box11_11 box11_12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_14 : Valid 3 5 11 ⟨8,15⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  splitA (k := 11) box11_10 box11_13

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_15 : Valid 3 5 11 ⟨8,15⟩ ⟨8,0⟩ ⟨2,0⟩ :=
  splitC (k := 3) box11_9 box11_14

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_16 : Valid 3 5 11 ⟨8,15⟩ ⟨8,0⟩ ⟨1,0⟩ :=
  splitC (k := 1) box11_8 box11_15

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_17 : Valid 3 5 11 ⟨8,15⟩ ⟨4,0⟩ ⟨1,0⟩ :=
  splitB (k := 7) box11_7 box11_16

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_18 : Valid 3 5 11 ⟨16,0⟩ ⟨4,7⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_19 : Valid 3 5 11 ⟨16,31⟩ ⟨4,7⟩ ⟨2,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_20 : Valid 3 5 11 ⟨32,0⟩ ⟨4,7⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_21 : Valid 3 5 11 ⟨32,0⟩ ⟨4,5⟩ ⟨4,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_22 : Valid 3 5 11 ⟨32,0⟩ ⟨6,7⟩ ⟨4,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_23 : Valid 3 5 11 ⟨32,0⟩ ⟨4,7⟩ ⟨4,0⟩ :=
  splitB (k := 5) box11_21 box11_22

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_24 : Valid 3 5 11 ⟨32,0⟩ ⟨4,7⟩ ⟨2,0⟩ :=
  splitC (k := 3) box11_20 box11_23

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_25 : Valid 3 5 11 ⟨16,0⟩ ⟨4,7⟩ ⟨2,0⟩ :=
  splitA (k := 31) box11_19 box11_24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_26 : Valid 3 5 11 ⟨16,0⟩ ⟨4,7⟩ ⟨1,0⟩ :=
  splitC (k := 1) box11_18 box11_25

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_27 : Valid 3 5 11 ⟨16,0⟩ ⟨8,0⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_28 : Valid 3 5 11 ⟨16,31⟩ ⟨8,0⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_29 : Valid 3 5 11 ⟨16,31⟩ ⟨8,15⟩ ⟨4,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_30 : Valid 3 5 11 ⟨16,31⟩ ⟨16,0⟩ ⟨4,7⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_31 : Valid 3 5 11 ⟨16,23⟩ ⟨16,31⟩ ⟨8,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_32 : Valid 3 5 11 ⟨16,19⟩ ⟨32,0⟩ ⟨8,15⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_33 : Valid 3 5 11 ⟨16,19⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_34 : Valid 3 5 11 ⟨16,17⟩ ⟨64,0⟩ ⟨16,31⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_35 : Valid 3 5 11 ⟨16,17⟩ ⟨64,127⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_36 : Valid 3 5 11 ⟨16,17⟩ ⟨128,0⟩ ⟨32,63⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_37 : Valid 3 5 11 ⟨16,16⟩ ⟨128,255⟩ ⟨64,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_38 : Valid 3 5 11 ⟨16,16⟩ ⟨256,0⟩ ⟨64,127⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_39 : Valid 3 5 11 ⟨16,16⟩ ⟨256,511⟩ ⟨128,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_40 : Valid 3 5 11 ⟨16,16⟩ ⟨512,0⟩ ⟨128,255⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_41 : Valid 3 5 11 ⟨16,16⟩ ⟨512,0⟩ ⟨256,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_42 : Valid 3 5 11 ⟨16,16⟩ ⟨512,0⟩ ⟨128,0⟩ :=
  splitC (k := 255) box11_40 box11_41

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_43 : Valid 3 5 11 ⟨16,16⟩ ⟨256,0⟩ ⟨128,0⟩ :=
  splitB (k := 511) box11_39 box11_42

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_44 : Valid 3 5 11 ⟨16,16⟩ ⟨256,0⟩ ⟨64,0⟩ :=
  splitC (k := 127) box11_38 box11_43

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_45 : Valid 3 5 11 ⟨16,16⟩ ⟨128,0⟩ ⟨64,0⟩ :=
  splitB (k := 255) box11_37 box11_44

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_46 : Valid 3 5 11 ⟨17,17⟩ ⟨128,255⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_47 : Valid 3 5 11 ⟨17,17⟩ ⟨256,0⟩ ⟨64,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_48 : Valid 3 5 11 ⟨17,17⟩ ⟨128,0⟩ ⟨64,0⟩ :=
  splitB (k := 255) box11_46 box11_47

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_49 : Valid 3 5 11 ⟨16,17⟩ ⟨128,0⟩ ⟨64,0⟩ :=
  splitA (k := 16) box11_45 box11_48

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_50 : Valid 3 5 11 ⟨16,17⟩ ⟨128,0⟩ ⟨32,0⟩ :=
  splitC (k := 63) box11_36 box11_49

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_51 : Valid 3 5 11 ⟨16,17⟩ ⟨64,0⟩ ⟨32,0⟩ :=
  splitB (k := 127) box11_35 box11_50

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_52 : Valid 3 5 11 ⟨16,17⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  splitC (k := 31) box11_34 box11_51

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_53 : Valid 3 5 11 ⟨18,19⟩ ⟨64,0⟩ ⟨16,31⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_54 : Valid 3 5 11 ⟨18,19⟩ ⟨64,127⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_55 : Valid 3 5 11 ⟨18,19⟩ ⟨128,0⟩ ⟨32,63⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_56 : Valid 3 5 11 ⟨18,19⟩ ⟨128,0⟩ ⟨64,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_57 : Valid 3 5 11 ⟨18,19⟩ ⟨128,0⟩ ⟨32,0⟩ :=
  splitC (k := 63) box11_55 box11_56

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_58 : Valid 3 5 11 ⟨18,19⟩ ⟨64,0⟩ ⟨32,0⟩ :=
  splitB (k := 127) box11_54 box11_57

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_59 : Valid 3 5 11 ⟨18,19⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  splitC (k := 31) box11_53 box11_58

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_60 : Valid 3 5 11 ⟨16,19⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  splitA (k := 17) box11_52 box11_59

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_61 : Valid 3 5 11 ⟨16,19⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  splitB (k := 63) box11_33 box11_60

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_62 : Valid 3 5 11 ⟨16,19⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box11_32 box11_61

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_63 : Valid 3 5 11 ⟨20,23⟩ ⟨32,0⟩ ⟨8,15⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_64 : Valid 3 5 11 ⟨20,23⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_65 : Valid 3 5 11 ⟨20,23⟩ ⟨64,0⟩ ⟨16,31⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_66 : Valid 3 5 11 ⟨20,23⟩ ⟨64,127⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_67 : Valid 3 5 11 ⟨20,23⟩ ⟨128,0⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_68 : Valid 3 5 11 ⟨20,23⟩ ⟨64,0⟩ ⟨32,0⟩ :=
  splitB (k := 127) box11_66 box11_67

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_69 : Valid 3 5 11 ⟨20,23⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  splitC (k := 31) box11_65 box11_68

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_70 : Valid 3 5 11 ⟨20,23⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  splitB (k := 63) box11_64 box11_69

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_71 : Valid 3 5 11 ⟨20,23⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box11_63 box11_70

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_72 : Valid 3 5 11 ⟨16,23⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitA (k := 19) box11_62 box11_71

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_73 : Valid 3 5 11 ⟨16,23⟩ ⟨16,0⟩ ⟨8,0⟩ :=
  splitB (k := 31) box11_31 box11_72

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_74 : Valid 3 5 11 ⟨24,31⟩ ⟨16,31⟩ ⟨8,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_75 : Valid 3 5 11 ⟨24,31⟩ ⟨32,0⟩ ⟨8,15⟩ :=
  cycle (validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_76 : Valid 3 5 11 ⟨24,31⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_77 : Valid 3 5 11 ⟨24,31⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_78 : Valid 3 5 11 ⟨24,31⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  splitB (k := 63) box11_76 box11_77

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_79 : Valid 3 5 11 ⟨24,31⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box11_75 box11_78

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_80 : Valid 3 5 11 ⟨24,31⟩ ⟨16,0⟩ ⟨8,0⟩ :=
  splitB (k := 31) box11_74 box11_79

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_81 : Valid 3 5 11 ⟨16,31⟩ ⟨16,0⟩ ⟨8,0⟩ :=
  splitA (k := 23) box11_73 box11_80

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_82 : Valid 3 5 11 ⟨16,31⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  splitC (k := 7) box11_30 box11_81

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_83 : Valid 3 5 11 ⟨16,31⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  splitB (k := 15) box11_29 box11_82

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_84 : Valid 3 5 11 ⟨16,31⟩ ⟨8,0⟩ ⟨2,0⟩ :=
  splitC (k := 3) box11_28 box11_83

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_85 : Valid 3 5 11 ⟨32,0⟩ ⟨8,15⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_86 : Valid 3 5 11 ⟨32,63⟩ ⟨16,0⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_87 : Valid 3 5 11 ⟨64,0⟩ ⟨16,31⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_88 : Valid 3 5 11 ⟨64,127⟩ ⟨32,0⟩ ⟨2,3⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_89 : Valid 3 5 11 ⟨128,0⟩ ⟨32,63⟩ ⟨2,3⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_90 : Valid 3 5 11 ⟨128,0⟩ ⟨64,0⟩ ⟨2,2⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_91 : Valid 3 5 11 ⟨128,255⟩ ⟨64,0⟩ ⟨3,3⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_92 : Valid 3 5 11 ⟨256,0⟩ ⟨64,127⟩ ⟨3,3⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_93 : Valid 3 5 11 ⟨256,0⟩ ⟨128,0⟩ ⟨3,3⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_94 : Valid 3 5 11 ⟨256,0⟩ ⟨64,0⟩ ⟨3,3⟩ :=
  splitB (k := 127) box11_92 box11_93

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_95 : Valid 3 5 11 ⟨128,0⟩ ⟨64,0⟩ ⟨3,3⟩ :=
  splitA (k := 255) box11_91 box11_94

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_96 : Valid 3 5 11 ⟨128,0⟩ ⟨64,0⟩ ⟨2,3⟩ :=
  splitC (k := 2) box11_90 box11_95

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_97 : Valid 3 5 11 ⟨128,0⟩ ⟨32,0⟩ ⟨2,3⟩ :=
  splitB (k := 63) box11_89 box11_96

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_98 : Valid 3 5 11 ⟨64,0⟩ ⟨32,0⟩ ⟨2,3⟩ :=
  splitA (k := 127) box11_88 box11_97

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_99 : Valid 3 5 11 ⟨64,0⟩ ⟨16,0⟩ ⟨2,3⟩ :=
  splitB (k := 31) box11_87 box11_98

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_100 : Valid 3 5 11 ⟨32,0⟩ ⟨16,0⟩ ⟨2,3⟩ :=
  splitA (k := 63) box11_86 box11_99

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_101 : Valid 3 5 11 ⟨32,0⟩ ⟨8,0⟩ ⟨2,3⟩ :=
  splitB (k := 15) box11_85 box11_100

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_102 : Valid 3 5 11 ⟨32,63⟩ ⟨8,15⟩ ⟨4,0⟩ :=
  cycle (cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_103 : Valid 3 5 11 ⟨64,0⟩ ⟨8,15⟩ ⟨4,7⟩ :=
  validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_104 : Valid 3 5 11 ⟨64,0⟩ ⟨8,11⟩ ⟨8,15⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_105 : Valid 3 5 11 ⟨64,127⟩ ⟨8,11⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_106 : Valid 3 5 11 ⟨128,0⟩ ⟨8,9⟩ ⟨16,31⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_107 : Valid 3 5 11 ⟨128,255⟩ ⟨8,9⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_108 : Valid 3 5 11 ⟨256,0⟩ ⟨8,8⟩ ⟨32,63⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_109 : Valid 3 5 11 ⟨256,511⟩ ⟨8,8⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_110 : Valid 3 5 11 ⟨512,0⟩ ⟨8,8⟩ ⟨64,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_111 : Valid 3 5 11 ⟨256,0⟩ ⟨8,8⟩ ⟨64,0⟩ :=
  splitA (k := 511) box11_109 box11_110

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_112 : Valid 3 5 11 ⟨256,0⟩ ⟨8,8⟩ ⟨32,0⟩ :=
  splitC (k := 63) box11_108 box11_111

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_113 : Valid 3 5 11 ⟨256,0⟩ ⟨9,9⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_114 : Valid 3 5 11 ⟨256,0⟩ ⟨8,9⟩ ⟨32,0⟩ :=
  splitB (k := 8) box11_112 box11_113

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_115 : Valid 3 5 11 ⟨128,0⟩ ⟨8,9⟩ ⟨32,0⟩ :=
  splitA (k := 255) box11_107 box11_114

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_116 : Valid 3 5 11 ⟨128,0⟩ ⟨8,9⟩ ⟨16,0⟩ :=
  splitC (k := 31) box11_106 box11_115

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_117 : Valid 3 5 11 ⟨128,0⟩ ⟨10,11⟩ ⟨16,31⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_118 : Valid 3 5 11 ⟨128,0⟩ ⟨10,11⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_119 : Valid 3 5 11 ⟨128,0⟩ ⟨10,11⟩ ⟨16,0⟩ :=
  splitC (k := 31) box11_117 box11_118

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_120 : Valid 3 5 11 ⟨128,0⟩ ⟨8,11⟩ ⟨16,0⟩ :=
  splitB (k := 9) box11_116 box11_119

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_121 : Valid 3 5 11 ⟨64,0⟩ ⟨8,11⟩ ⟨16,0⟩ :=
  splitA (k := 127) box11_105 box11_120

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_122 : Valid 3 5 11 ⟨64,0⟩ ⟨8,11⟩ ⟨8,0⟩ :=
  splitC (k := 15) box11_104 box11_121

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_123 : Valid 3 5 11 ⟨64,0⟩ ⟨12,15⟩ ⟨8,15⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_124 : Valid 3 5 11 ⟨64,127⟩ ⟨12,15⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_125 : Valid 3 5 11 ⟨128,0⟩ ⟨12,15⟩ ⟨16,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_126 : Valid 3 5 11 ⟨64,0⟩ ⟨12,15⟩ ⟨16,0⟩ :=
  splitA (k := 127) box11_124 box11_125

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_127 : Valid 3 5 11 ⟨64,0⟩ ⟨12,15⟩ ⟨8,0⟩ :=
  splitC (k := 15) box11_123 box11_126

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_128 : Valid 3 5 11 ⟨64,0⟩ ⟨8,15⟩ ⟨8,0⟩ :=
  splitB (k := 11) box11_122 box11_127

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_129 : Valid 3 5 11 ⟨64,0⟩ ⟨8,15⟩ ⟨4,0⟩ :=
  splitC (k := 7) box11_103 box11_128

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_130 : Valid 3 5 11 ⟨32,0⟩ ⟨8,15⟩ ⟨4,0⟩ :=
  splitA (k := 63) box11_102 box11_129

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_131 : Valid 3 5 11 ⟨32,63⟩ ⟨16,0⟩ ⟨4,7⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_132 : Valid 3 5 11 ⟨32,63⟩ ⟨16,31⟩ ⟨8,15⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_133 : Valid 3 5 11 ⟨32,47⟩ ⟨16,31⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_134 : Valid 3 5 11 ⟨48,63⟩ ⟨16,31⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_135 : Valid 3 5 11 ⟨32,63⟩ ⟨16,31⟩ ⟨16,0⟩ :=
  splitA (k := 47) box11_133 box11_134

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_136 : Valid 3 5 11 ⟨32,63⟩ ⟨16,31⟩ ⟨8,0⟩ :=
  splitC (k := 15) box11_132 box11_135

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_137 : Valid 3 5 11 ⟨32,63⟩ ⟨32,0⟩ ⟨8,15⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_138 : Valid 3 5 11 ⟨32,63⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_139 : Valid 3 5 11 ⟨32,63⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box11_137 box11_138

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_140 : Valid 3 5 11 ⟨32,63⟩ ⟨16,0⟩ ⟨8,0⟩ :=
  splitB (k := 31) box11_136 box11_139

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_141 : Valid 3 5 11 ⟨32,63⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  splitC (k := 7) box11_131 box11_140

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_142 : Valid 3 5 11 ⟨64,0⟩ ⟨16,31⟩ ⟨4,7⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_143 : Valid 3 5 11 ⟨64,127⟩ ⟨32,0⟩ ⟨4,7⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_144 : Valid 3 5 11 ⟨128,0⟩ ⟨32,63⟩ ⟨4,7⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_145 : Valid 3 5 11 ⟨128,0⟩ ⟨64,0⟩ ⟨4,7⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_146 : Valid 3 5 11 ⟨128,0⟩ ⟨32,0⟩ ⟨4,7⟩ :=
  splitB (k := 63) box11_144 box11_145

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_147 : Valid 3 5 11 ⟨64,0⟩ ⟨32,0⟩ ⟨4,7⟩ :=
  splitA (k := 127) box11_143 box11_146

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_148 : Valid 3 5 11 ⟨64,0⟩ ⟨16,0⟩ ⟨4,7⟩ :=
  splitB (k := 31) box11_142 box11_147

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_149 : Valid 3 5 11 ⟨64,0⟩ ⟨16,31⟩ ⟨8,15⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_150 : Valid 3 5 11 ⟨64,0⟩ ⟨16,31⟩ ⟨16,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_151 : Valid 3 5 11 ⟨64,0⟩ ⟨16,31⟩ ⟨8,0⟩ :=
  splitC (k := 15) box11_149 box11_150

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_152 : Valid 3 5 11 ⟨64,0⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_153 : Valid 3 5 11 ⟨64,0⟩ ⟨16,0⟩ ⟨8,0⟩ :=
  splitB (k := 31) box11_151 box11_152

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_154 : Valid 3 5 11 ⟨64,0⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  splitC (k := 7) box11_148 box11_153

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_155 : Valid 3 5 11 ⟨32,0⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  splitA (k := 63) box11_141 box11_154

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_156 : Valid 3 5 11 ⟨32,0⟩ ⟨8,0⟩ ⟨4,0⟩ :=
  splitB (k := 15) box11_130 box11_155

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_157 : Valid 3 5 11 ⟨32,0⟩ ⟨8,0⟩ ⟨2,0⟩ :=
  splitC (k := 3) box11_101 box11_156

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_158 : Valid 3 5 11 ⟨16,0⟩ ⟨8,0⟩ ⟨2,0⟩ :=
  splitA (k := 31) box11_84 box11_157

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_159 : Valid 3 5 11 ⟨16,0⟩ ⟨8,0⟩ ⟨1,0⟩ :=
  splitC (k := 1) box11_27 box11_158

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_160 : Valid 3 5 11 ⟨16,0⟩ ⟨4,0⟩ ⟨1,0⟩ :=
  splitB (k := 7) box11_26 box11_159

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_161 : Valid 3 5 11 ⟨8,0⟩ ⟨4,0⟩ ⟨1,0⟩ :=
  splitA (k := 15) box11_17 box11_160

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_162 : Valid 3 5 11 ⟨8,0⟩ ⟨2,0⟩ ⟨1,0⟩ :=
  splitB (k := 3) box11_6 box11_161

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_163 : Valid 3 5 11 ⟨4,0⟩ ⟨2,0⟩ ⟨1,0⟩ :=
  splitA (k := 7) box11_5 box11_162

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_164 : Valid 3 5 11 ⟨4,0⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  splitB (k := 1) box11_2 box11_163

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_165 : Valid 3 5 11 ⟨2,0⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  splitA (k := 3) box11_1 box11_164

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box11_166 : Valid 3 5 11 ⟨1,0⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  splitA (k := 1) box11_0 box11_165

theorem triples11 : Valid 3 5 11 ⟨1,0⟩ ⟨1,0⟩ ⟨1,0⟩ := box11_166
end A245212Local

namespace A245212Local
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_0 : Valid 3 5 13 ⟨1,1⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_1 : Valid 3 5 13 ⟨2,3⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_2 : Valid 3 5 13 ⟨4,0⟩ ⟨1,1⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_3 : Valid 3 5 13 ⟨4,7⟩ ⟨2,0⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_4 : Valid 3 5 13 ⟨8,0⟩ ⟨2,3⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_5 : Valid 3 5 13 ⟨8,15⟩ ⟨4,0⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_6 : Valid 3 5 13 ⟨16,0⟩ ⟨4,7⟩ ⟨1,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_7 : Valid 3 5 13 ⟨16,0⟩ ⟨8,0⟩ ⟨1,1⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_8 : Valid 3 5 13 ⟨16,31⟩ ⟨8,15⟩ ⟨2,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_9 : Valid 3 5 13 ⟨16,31⟩ ⟨16,0⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_10 : Valid 3 5 13 ⟨16,23⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_11 : Valid 3 5 13 ⟨24,31⟩ ⟨16,31⟩ ⟨4,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_12 : Valid 3 5 13 ⟨24,31⟩ ⟨32,0⟩ ⟨4,7⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_13 : Valid 3 5 13 ⟨24,31⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_14 : Valid 3 5 13 ⟨24,31⟩ ⟨32,0⟩ ⟨4,0⟩ :=
  splitC (k := 7) box13_12 box13_13

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_15 : Valid 3 5 13 ⟨24,31⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  splitB (k := 31) box13_11 box13_14

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_16 : Valid 3 5 13 ⟨16,31⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  splitA (k := 23) box13_10 box13_15

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_17 : Valid 3 5 13 ⟨16,31⟩ ⟨16,0⟩ ⟨2,0⟩ :=
  splitC (k := 3) box13_9 box13_16

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_18 : Valid 3 5 13 ⟨16,31⟩ ⟨8,0⟩ ⟨2,0⟩ :=
  splitB (k := 15) box13_8 box13_17

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_19 : Valid 3 5 13 ⟨32,0⟩ ⟨8,15⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_20 : Valid 3 5 13 ⟨32,63⟩ ⟨8,15⟩ ⟨4,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_21 : Valid 3 5 13 ⟨64,0⟩ ⟨8,15⟩ ⟨4,7⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_22 : Valid 3 5 13 ⟨64,0⟩ ⟨8,15⟩ ⟨8,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_23 : Valid 3 5 13 ⟨64,0⟩ ⟨8,15⟩ ⟨4,0⟩ :=
  splitC (k := 7) box13_21 box13_22

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_24 : Valid 3 5 13 ⟨32,0⟩ ⟨8,15⟩ ⟨4,0⟩ :=
  splitA (k := 63) box13_20 box13_23

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_25 : Valid 3 5 13 ⟨32,0⟩ ⟨8,15⟩ ⟨2,0⟩ :=
  splitC (k := 3) box13_19 box13_24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_26 : Valid 3 5 13 ⟨32,0⟩ ⟨16,0⟩ ⟨2,3⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_27 : Valid 3 5 13 ⟨32,63⟩ ⟨16,31⟩ ⟨4,7⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_28 : Valid 3 5 13 ⟨32,47⟩ ⟨16,31⟩ ⟨8,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_29 : Valid 3 5 13 ⟨48,63⟩ ⟨16,31⟩ ⟨8,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_30 : Valid 3 5 13 ⟨32,63⟩ ⟨16,31⟩ ⟨8,0⟩ :=
  splitA (k := 47) box13_28 box13_29

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_31 : Valid 3 5 13 ⟨32,63⟩ ⟨16,31⟩ ⟨4,0⟩ :=
  splitC (k := 7) box13_27 box13_30

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_32 : Valid 3 5 13 ⟨32,63⟩ ⟨32,0⟩ ⟨4,7⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_33 : Valid 3 5 13 ⟨32,47⟩ ⟨32,0⟩ ⟨8,15⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_34 : Valid 3 5 13 ⟨32,39⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_35 : Valid 3 5 13 ⟨40,47⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_36 : Valid 3 5 13 ⟨32,47⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  splitA (k := 39) box13_34 box13_35

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_37 : Valid 3 5 13 ⟨32,39⟩ ⟨64,0⟩ ⟨16,31⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_38 : Valid 3 5 13 ⟨32,35⟩ ⟨64,127⟩ ⟨32,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_39 : Valid 3 5 13 ⟨36,39⟩ ⟨64,127⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_40 : Valid 3 5 13 ⟨32,39⟩ ⟨64,127⟩ ⟨32,0⟩ :=
  splitA (k := 35) box13_38 box13_39

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_41 : Valid 3 5 13 ⟨32,35⟩ ⟨128,0⟩ ⟨32,63⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_42 : Valid 3 5 13 ⟨32,33⟩ ⟨128,255⟩ ⟨64,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_43 : Valid 3 5 13 ⟨34,35⟩ ⟨128,255⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_44 : Valid 3 5 13 ⟨32,35⟩ ⟨128,255⟩ ⟨64,0⟩ :=
  splitA (k := 33) box13_42 box13_43

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_45 : Valid 3 5 13 ⟨32,33⟩ ⟨256,0⟩ ⟨64,127⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_46 : Valid 3 5 13 ⟨32,33⟩ ⟨256,511⟩ ⟨128,255⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_47 : Valid 3 5 13 ⟨32,32⟩ ⟨256,511⟩ ⟨256,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_48 : Valid 3 5 13 ⟨33,33⟩ ⟨256,511⟩ ⟨256,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_49 : Valid 3 5 13 ⟨32,33⟩ ⟨256,511⟩ ⟨256,0⟩ :=
  splitA (k := 32) box13_47 box13_48

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_50 : Valid 3 5 13 ⟨32,33⟩ ⟨256,511⟩ ⟨128,0⟩ :=
  splitC (k := 255) box13_46 box13_49

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_51 : Valid 3 5 13 ⟨32,33⟩ ⟨512,0⟩ ⟨128,255⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_52 : Valid 3 5 13 ⟨32,32⟩ ⟨512,1023⟩ ⟨256,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_53 : Valid 3 5 13 ⟨32,32⟩ ⟨1024,0⟩ ⟨256,511⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_54 : Valid 3 5 13 ⟨32,32⟩ ⟨1024,1535⟩ ⟨512,1023⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_55 : Valid 3 5 13 ⟨32,32⟩ ⟨1536,2047⟩ ⟨512,767⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_56 : Valid 3 5 13 ⟨32,32⟩ ⟨1536,2047⟩ ⟨768,1023⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_57 : Valid 3 5 13 ⟨32,32⟩ ⟨1536,2047⟩ ⟨512,1023⟩ :=
  splitC (k := 767) box13_55 box13_56

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_58 : Valid 3 5 13 ⟨32,32⟩ ⟨1024,2047⟩ ⟨512,1023⟩ :=
  splitB (k := 1535) box13_54 box13_57

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_59 : Valid 3 5 13 ⟨32,32⟩ ⟨1024,1279⟩ ⟨1024,0⟩ :=
  cycle (cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_60 : Valid 3 5 13 ⟨32,32⟩ ⟨1280,1535⟩ ⟨1024,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_61 : Valid 3 5 13 ⟨32,32⟩ ⟨1024,1535⟩ ⟨1024,0⟩ :=
  splitB (k := 1279) box13_59 box13_60

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_62 : Valid 3 5 13 ⟨32,32⟩ ⟨1536,1791⟩ ⟨1024,2047⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_63 : Valid 3 5 13 ⟨32,32⟩ ⟨1792,2047⟩ ⟨1024,2047⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_64 : Valid 3 5 13 ⟨32,32⟩ ⟨1536,2047⟩ ⟨1024,2047⟩ :=
  splitB (k := 1791) box13_62 box13_63

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_65 : Valid 3 5 13 ⟨32,32⟩ ⟨1536,2047⟩ ⟨2048,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_66 : Valid 3 5 13 ⟨32,32⟩ ⟨1536,2047⟩ ⟨1024,0⟩ :=
  splitC (k := 2047) box13_64 box13_65

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_67 : Valid 3 5 13 ⟨32,32⟩ ⟨1024,2047⟩ ⟨1024,0⟩ :=
  splitB (k := 1535) box13_61 box13_66

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_68 : Valid 3 5 13 ⟨32,32⟩ ⟨1024,2047⟩ ⟨512,0⟩ :=
  splitC (k := 1023) box13_58 box13_67

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_69 : Valid 3 5 13 ⟨32,32⟩ ⟨2048,4095⟩ ⟨512,767⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_70 : Valid 3 5 13 ⟨32,32⟩ ⟨2048,4095⟩ ⟨768,1023⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_71 : Valid 3 5 13 ⟨32,32⟩ ⟨2048,4095⟩ ⟨512,1023⟩ :=
  splitC (k := 767) box13_69 box13_70

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_72 : Valid 3 5 13 ⟨32,32⟩ ⟨4096,0⟩ ⟨512,1023⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_73 : Valid 3 5 13 ⟨32,32⟩ ⟨2048,0⟩ ⟨512,1023⟩ :=
  splitB (k := 4095) box13_71 box13_72

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_74 : Valid 3 5 13 ⟨32,32⟩ ⟨2048,0⟩ ⟨1024,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_75 : Valid 3 5 13 ⟨32,32⟩ ⟨2048,0⟩ ⟨512,0⟩ :=
  splitC (k := 1023) box13_73 box13_74

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_76 : Valid 3 5 13 ⟨32,32⟩ ⟨1024,0⟩ ⟨512,0⟩ :=
  splitB (k := 2047) box13_68 box13_75

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_77 : Valid 3 5 13 ⟨32,32⟩ ⟨1024,0⟩ ⟨256,0⟩ :=
  splitC (k := 511) box13_53 box13_76

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_78 : Valid 3 5 13 ⟨32,32⟩ ⟨512,0⟩ ⟨256,0⟩ :=
  splitB (k := 1023) box13_52 box13_77

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_79 : Valid 3 5 13 ⟨33,33⟩ ⟨512,1023⟩ ⟨256,511⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_80 : Valid 3 5 13 ⟨33,33⟩ ⟨512,1023⟩ ⟨512,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_81 : Valid 3 5 13 ⟨33,33⟩ ⟨512,1023⟩ ⟨256,0⟩ :=
  splitC (k := 511) box13_79 box13_80

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_82 : Valid 3 5 13 ⟨33,33⟩ ⟨1024,0⟩ ⟨256,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_83 : Valid 3 5 13 ⟨33,33⟩ ⟨512,0⟩ ⟨256,0⟩ :=
  splitB (k := 1023) box13_81 box13_82

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_84 : Valid 3 5 13 ⟨32,33⟩ ⟨512,0⟩ ⟨256,0⟩ :=
  splitA (k := 32) box13_78 box13_83

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_85 : Valid 3 5 13 ⟨32,33⟩ ⟨512,0⟩ ⟨128,0⟩ :=
  splitC (k := 255) box13_51 box13_84

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_86 : Valid 3 5 13 ⟨32,33⟩ ⟨256,0⟩ ⟨128,0⟩ :=
  splitB (k := 511) box13_50 box13_85

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_87 : Valid 3 5 13 ⟨32,33⟩ ⟨256,0⟩ ⟨64,0⟩ :=
  splitC (k := 127) box13_45 box13_86

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_88 : Valid 3 5 13 ⟨34,35⟩ ⟨256,0⟩ ⟨64,127⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_89 : Valid 3 5 13 ⟨34,35⟩ ⟨256,511⟩ ⟨128,255⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_90 : Valid 3 5 13 ⟨34,35⟩ ⟨256,383⟩ ⟨256,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_91 : Valid 3 5 13 ⟨34,35⟩ ⟨384,511⟩ ⟨256,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_92 : Valid 3 5 13 ⟨34,35⟩ ⟨256,511⟩ ⟨256,0⟩ :=
  splitB (k := 383) box13_90 box13_91

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_93 : Valid 3 5 13 ⟨34,35⟩ ⟨256,511⟩ ⟨128,0⟩ :=
  splitC (k := 255) box13_89 box13_92

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_94 : Valid 3 5 13 ⟨34,35⟩ ⟨512,0⟩ ⟨128,255⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_95 : Valid 3 5 13 ⟨34,35⟩ ⟨512,0⟩ ⟨256,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_96 : Valid 3 5 13 ⟨34,35⟩ ⟨512,0⟩ ⟨128,0⟩ :=
  splitC (k := 255) box13_94 box13_95

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_97 : Valid 3 5 13 ⟨34,35⟩ ⟨256,0⟩ ⟨128,0⟩ :=
  splitB (k := 511) box13_93 box13_96

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_98 : Valid 3 5 13 ⟨34,35⟩ ⟨256,0⟩ ⟨64,0⟩ :=
  splitC (k := 127) box13_88 box13_97

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_99 : Valid 3 5 13 ⟨32,35⟩ ⟨256,0⟩ ⟨64,0⟩ :=
  splitA (k := 33) box13_87 box13_98

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_100 : Valid 3 5 13 ⟨32,35⟩ ⟨128,0⟩ ⟨64,0⟩ :=
  splitB (k := 255) box13_44 box13_99

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_101 : Valid 3 5 13 ⟨32,35⟩ ⟨128,0⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_41 box13_100

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_102 : Valid 3 5 13 ⟨36,39⟩ ⟨128,0⟩ ⟨32,63⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_103 : Valid 3 5 13 ⟨36,37⟩ ⟨128,255⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_104 : Valid 3 5 13 ⟨38,39⟩ ⟨128,255⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_105 : Valid 3 5 13 ⟨36,39⟩ ⟨128,255⟩ ⟨64,0⟩ :=
  splitA (k := 37) box13_103 box13_104

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_106 : Valid 3 5 13 ⟨36,37⟩ ⟨256,0⟩ ⟨64,127⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_107 : Valid 3 5 13 ⟨36,37⟩ ⟨256,0⟩ ⟨128,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_108 : Valid 3 5 13 ⟨36,37⟩ ⟨256,0⟩ ⟨64,0⟩ :=
  splitC (k := 127) box13_106 box13_107

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_109 : Valid 3 5 13 ⟨38,39⟩ ⟨256,0⟩ ⟨64,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_110 : Valid 3 5 13 ⟨36,39⟩ ⟨256,0⟩ ⟨64,0⟩ :=
  splitA (k := 37) box13_108 box13_109

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_111 : Valid 3 5 13 ⟨36,39⟩ ⟨128,0⟩ ⟨64,0⟩ :=
  splitB (k := 255) box13_105 box13_110

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_112 : Valid 3 5 13 ⟨36,39⟩ ⟨128,0⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_102 box13_111

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_113 : Valid 3 5 13 ⟨32,39⟩ ⟨128,0⟩ ⟨32,0⟩ :=
  splitA (k := 35) box13_101 box13_112

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_114 : Valid 3 5 13 ⟨32,39⟩ ⟨64,0⟩ ⟨32,0⟩ :=
  splitB (k := 127) box13_40 box13_113

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_115 : Valid 3 5 13 ⟨32,39⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_37 box13_114

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_116 : Valid 3 5 13 ⟨40,47⟩ ⟨64,0⟩ ⟨16,31⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_117 : Valid 3 5 13 ⟨40,47⟩ ⟨64,127⟩ ⟨32,63⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_118 : Valid 3 5 13 ⟨40,43⟩ ⟨64,127⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_119 : Valid 3 5 13 ⟨44,47⟩ ⟨64,127⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_120 : Valid 3 5 13 ⟨40,47⟩ ⟨64,127⟩ ⟨64,0⟩ :=
  splitA (k := 43) box13_118 box13_119

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_121 : Valid 3 5 13 ⟨40,47⟩ ⟨64,127⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_117 box13_120

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_122 : Valid 3 5 13 ⟨40,47⟩ ⟨128,0⟩ ⟨32,63⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_123 : Valid 3 5 13 ⟨40,47⟩ ⟨128,0⟩ ⟨64,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_124 : Valid 3 5 13 ⟨40,47⟩ ⟨128,0⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_122 box13_123

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_125 : Valid 3 5 13 ⟨40,47⟩ ⟨64,0⟩ ⟨32,0⟩ :=
  splitB (k := 127) box13_121 box13_124

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_126 : Valid 3 5 13 ⟨40,47⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_116 box13_125

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_127 : Valid 3 5 13 ⟨32,47⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  splitA (k := 39) box13_115 box13_126

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_128 : Valid 3 5 13 ⟨32,47⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  splitB (k := 63) box13_36 box13_127

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_129 : Valid 3 5 13 ⟨32,47⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box13_33 box13_128

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_130 : Valid 3 5 13 ⟨48,63⟩ ⟨32,0⟩ ⟨8,15⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_131 : Valid 3 5 13 ⟨48,63⟩ ⟨32,63⟩ ⟨16,31⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_132 : Valid 3 5 13 ⟨48,63⟩ ⟨32,47⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_133 : Valid 3 5 13 ⟨48,63⟩ ⟨48,63⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_134 : Valid 3 5 13 ⟨48,63⟩ ⟨32,63⟩ ⟨32,0⟩ :=
  splitB (k := 47) box13_132 box13_133

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_135 : Valid 3 5 13 ⟨48,63⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_131 box13_134

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_136 : Valid 3 5 13 ⟨48,63⟩ ⟨64,0⟩ ⟨16,31⟩ :=
  cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_137 : Valid 3 5 13 ⟨48,55⟩ ⟨64,127⟩ ⟨32,63⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_138 : Valid 3 5 13 ⟨48,55⟩ ⟨64,127⟩ ⟨64,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_139 : Valid 3 5 13 ⟨48,55⟩ ⟨64,127⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_137 box13_138

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_140 : Valid 3 5 13 ⟨56,63⟩ ⟨64,127⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_141 : Valid 3 5 13 ⟨48,63⟩ ⟨64,127⟩ ⟨32,0⟩ :=
  splitA (k := 55) box13_139 box13_140

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_142 : Valid 3 5 13 ⟨48,63⟩ ⟨128,0⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_143 : Valid 3 5 13 ⟨48,63⟩ ⟨64,0⟩ ⟨32,0⟩ :=
  splitB (k := 127) box13_141 box13_142

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_144 : Valid 3 5 13 ⟨48,63⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_136 box13_143

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_145 : Valid 3 5 13 ⟨48,63⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  splitB (k := 63) box13_135 box13_144

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_146 : Valid 3 5 13 ⟨48,63⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box13_130 box13_145

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_147 : Valid 3 5 13 ⟨32,63⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitA (k := 47) box13_129 box13_146

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_148 : Valid 3 5 13 ⟨32,63⟩ ⟨32,0⟩ ⟨4,0⟩ :=
  splitC (k := 7) box13_32 box13_147

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_149 : Valid 3 5 13 ⟨32,63⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  splitB (k := 31) box13_31 box13_148

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_150 : Valid 3 5 13 ⟨64,0⟩ ⟨16,31⟩ ⟨4,7⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_151 : Valid 3 5 13 ⟨64,127⟩ ⟨16,31⟩ ⟨8,15⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_152 : Valid 3 5 13 ⟨64,95⟩ ⟨16,23⟩ ⟨16,0⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_153 : Valid 3 5 13 ⟨96,127⟩ ⟨16,23⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_154 : Valid 3 5 13 ⟨64,127⟩ ⟨16,23⟩ ⟨16,0⟩ :=
  splitA (k := 95) box13_152 box13_153

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_155 : Valid 3 5 13 ⟨64,95⟩ ⟨24,31⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_156 : Valid 3 5 13 ⟨96,127⟩ ⟨24,31⟩ ⟨16,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_157 : Valid 3 5 13 ⟨64,127⟩ ⟨24,31⟩ ⟨16,0⟩ :=
  splitA (k := 95) box13_155 box13_156

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_158 : Valid 3 5 13 ⟨64,127⟩ ⟨16,31⟩ ⟨16,0⟩ :=
  splitB (k := 23) box13_154 box13_157

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_159 : Valid 3 5 13 ⟨64,127⟩ ⟨16,31⟩ ⟨8,0⟩ :=
  splitC (k := 15) box13_151 box13_158

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_160 : Valid 3 5 13 ⟨128,0⟩ ⟨16,31⟩ ⟨8,15⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_161 : Valid 3 5 13 ⟨128,255⟩ ⟨16,19⟩ ⟨16,31⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_162 : Valid 3 5 13 ⟨128,191⟩ ⟨16,19⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_163 : Valid 3 5 13 ⟨192,255⟩ ⟨16,19⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_164 : Valid 3 5 13 ⟨128,255⟩ ⟨16,19⟩ ⟨32,0⟩ :=
  splitA (k := 191) box13_162 box13_163

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_165 : Valid 3 5 13 ⟨128,255⟩ ⟨16,19⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_161 box13_164

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_166 : Valid 3 5 13 ⟨128,255⟩ ⟨20,23⟩ ⟨16,31⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_167 : Valid 3 5 13 ⟨128,191⟩ ⟨20,23⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_168 : Valid 3 5 13 ⟨192,255⟩ ⟨20,23⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_169 : Valid 3 5 13 ⟨128,255⟩ ⟨20,23⟩ ⟨32,0⟩ :=
  splitA (k := 191) box13_167 box13_168

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_170 : Valid 3 5 13 ⟨128,255⟩ ⟨20,23⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_166 box13_169

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_171 : Valid 3 5 13 ⟨128,255⟩ ⟨16,23⟩ ⟨16,0⟩ :=
  splitB (k := 19) box13_165 box13_170

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_172 : Valid 3 5 13 ⟨256,0⟩ ⟨16,19⟩ ⟨16,31⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_173 : Valid 3 5 13 ⟨256,511⟩ ⟨16,17⟩ ⟨32,63⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_174 : Valid 3 5 13 ⟨256,383⟩ ⟨16,17⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_175 : Valid 3 5 13 ⟨384,511⟩ ⟨16,17⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_176 : Valid 3 5 13 ⟨256,511⟩ ⟨16,17⟩ ⟨64,0⟩ :=
  splitA (k := 383) box13_174 box13_175

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_177 : Valid 3 5 13 ⟨256,511⟩ ⟨16,17⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_173 box13_176

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_178 : Valid 3 5 13 ⟨256,511⟩ ⟨18,19⟩ ⟨32,63⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_179 : Valid 3 5 13 ⟨256,383⟩ ⟨18,19⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_180 : Valid 3 5 13 ⟨384,511⟩ ⟨18,19⟩ ⟨64,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_181 : Valid 3 5 13 ⟨256,511⟩ ⟨18,19⟩ ⟨64,0⟩ :=
  splitA (k := 383) box13_179 box13_180

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_182 : Valid 3 5 13 ⟨256,511⟩ ⟨18,19⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_178 box13_181

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_183 : Valid 3 5 13 ⟨256,511⟩ ⟨16,19⟩ ⟨32,0⟩ :=
  splitB (k := 17) box13_177 box13_182

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_184 : Valid 3 5 13 ⟨512,0⟩ ⟨16,17⟩ ⟨32,63⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_185 : Valid 3 5 13 ⟨512,1023⟩ ⟨16,17⟩ ⟨64,127⟩ :=
  validRect (k := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_186 : Valid 3 5 13 ⟨512,767⟩ ⟨16,16⟩ ⟨128,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_187 : Valid 3 5 13 ⟨768,1023⟩ ⟨16,16⟩ ⟨128,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_188 : Valid 3 5 13 ⟨512,1023⟩ ⟨16,16⟩ ⟨128,0⟩ :=
  splitA (k := 767) box13_186 box13_187

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_189 : Valid 3 5 13 ⟨512,767⟩ ⟨17,17⟩ ⟨128,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_190 : Valid 3 5 13 ⟨768,1023⟩ ⟨17,17⟩ ⟨128,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_191 : Valid 3 5 13 ⟨512,1023⟩ ⟨17,17⟩ ⟨128,0⟩ :=
  splitA (k := 767) box13_189 box13_190

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_192 : Valid 3 5 13 ⟨512,1023⟩ ⟨16,17⟩ ⟨128,0⟩ :=
  splitB (k := 16) box13_188 box13_191

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_193 : Valid 3 5 13 ⟨512,1023⟩ ⟨16,17⟩ ⟨64,0⟩ :=
  splitC (k := 127) box13_185 box13_192

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_194 : Valid 3 5 13 ⟨1024,0⟩ ⟨16,17⟩ ⟨64,127⟩ :=
  validRect (k := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_195 : Valid 3 5 13 ⟨1024,2047⟩ ⟨16,16⟩ ⟨128,255⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_196 : Valid 3 5 13 ⟨1024,1535⟩ ⟨16,16⟩ ⟨256,511⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_197 : Valid 3 5 13 ⟨1024,1535⟩ ⟨16,16⟩ ⟨512,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_198 : Valid 3 5 13 ⟨1024,1535⟩ ⟨16,16⟩ ⟨256,0⟩ :=
  splitC (k := 511) box13_196 box13_197

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_199 : Valid 3 5 13 ⟨1536,2047⟩ ⟨16,16⟩ ⟨256,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_200 : Valid 3 5 13 ⟨1024,2047⟩ ⟨16,16⟩ ⟨256,0⟩ :=
  splitA (k := 1535) box13_198 box13_199

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_201 : Valid 3 5 13 ⟨1024,2047⟩ ⟨16,16⟩ ⟨128,0⟩ :=
  splitC (k := 255) box13_195 box13_200

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_202 : Valid 3 5 13 ⟨2048,0⟩ ⟨16,16⟩ ⟨128,255⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_203 : Valid 3 5 13 ⟨2048,0⟩ ⟨16,16⟩ ⟨256,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_204 : Valid 3 5 13 ⟨2048,0⟩ ⟨16,16⟩ ⟨128,0⟩ :=
  splitC (k := 255) box13_202 box13_203

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_205 : Valid 3 5 13 ⟨1024,0⟩ ⟨16,16⟩ ⟨128,0⟩ :=
  splitA (k := 2047) box13_201 box13_204

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_206 : Valid 3 5 13 ⟨1024,0⟩ ⟨17,17⟩ ⟨128,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_207 : Valid 3 5 13 ⟨1024,0⟩ ⟨16,17⟩ ⟨128,0⟩ :=
  splitB (k := 16) box13_205 box13_206

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_208 : Valid 3 5 13 ⟨1024,0⟩ ⟨16,17⟩ ⟨64,0⟩ :=
  splitC (k := 127) box13_194 box13_207

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_209 : Valid 3 5 13 ⟨512,0⟩ ⟨16,17⟩ ⟨64,0⟩ :=
  splitA (k := 1023) box13_193 box13_208

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_210 : Valid 3 5 13 ⟨512,0⟩ ⟨16,17⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_184 box13_209

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_211 : Valid 3 5 13 ⟨512,0⟩ ⟨18,19⟩ ⟨32,63⟩ :=
  validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_212 : Valid 3 5 13 ⟨512,0⟩ ⟨18,19⟩ ⟨64,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_213 : Valid 3 5 13 ⟨512,0⟩ ⟨18,19⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_211 box13_212

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_214 : Valid 3 5 13 ⟨512,0⟩ ⟨16,19⟩ ⟨32,0⟩ :=
  splitB (k := 17) box13_210 box13_213

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_215 : Valid 3 5 13 ⟨256,0⟩ ⟨16,19⟩ ⟨32,0⟩ :=
  splitA (k := 511) box13_183 box13_214

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_216 : Valid 3 5 13 ⟨256,0⟩ ⟨16,19⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_172 box13_215

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_217 : Valid 3 5 13 ⟨256,0⟩ ⟨20,23⟩ ⟨16,31⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_218 : Valid 3 5 13 ⟨256,511⟩ ⟨20,23⟩ ⟨32,63⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_219 : Valid 3 5 13 ⟨256,511⟩ ⟨20,23⟩ ⟨64,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_220 : Valid 3 5 13 ⟨256,511⟩ ⟨20,23⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_218 box13_219

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_221 : Valid 3 5 13 ⟨512,0⟩ ⟨20,23⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_222 : Valid 3 5 13 ⟨256,0⟩ ⟨20,23⟩ ⟨32,0⟩ :=
  splitA (k := 511) box13_220 box13_221

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_223 : Valid 3 5 13 ⟨256,0⟩ ⟨20,23⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_217 box13_222

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_224 : Valid 3 5 13 ⟨256,0⟩ ⟨16,23⟩ ⟨16,0⟩ :=
  splitB (k := 19) box13_216 box13_223

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_225 : Valid 3 5 13 ⟨128,0⟩ ⟨16,23⟩ ⟨16,0⟩ :=
  splitA (k := 255) box13_171 box13_224

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_226 : Valid 3 5 13 ⟨128,255⟩ ⟨24,31⟩ ⟨16,31⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_227 : Valid 3 5 13 ⟨128,191⟩ ⟨24,31⟩ ⟨32,63⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_228 : Valid 3 5 13 ⟨128,191⟩ ⟨24,31⟩ ⟨64,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_229 : Valid 3 5 13 ⟨128,191⟩ ⟨24,31⟩ ⟨32,0⟩ :=
  splitC (k := 63) box13_227 box13_228

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_230 : Valid 3 5 13 ⟨192,255⟩ ⟨24,31⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_231 : Valid 3 5 13 ⟨128,255⟩ ⟨24,31⟩ ⟨32,0⟩ :=
  splitA (k := 191) box13_229 box13_230

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_232 : Valid 3 5 13 ⟨128,255⟩ ⟨24,31⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_226 box13_231

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_233 : Valid 3 5 13 ⟨256,0⟩ ⟨24,31⟩ ⟨16,31⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_234 : Valid 3 5 13 ⟨256,0⟩ ⟨24,31⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_235 : Valid 3 5 13 ⟨256,0⟩ ⟨24,31⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_233 box13_234

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_236 : Valid 3 5 13 ⟨128,0⟩ ⟨24,31⟩ ⟨16,0⟩ :=
  splitA (k := 255) box13_232 box13_235

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_237 : Valid 3 5 13 ⟨128,0⟩ ⟨16,31⟩ ⟨16,0⟩ :=
  splitB (k := 23) box13_225 box13_236

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_238 : Valid 3 5 13 ⟨128,0⟩ ⟨16,31⟩ ⟨8,0⟩ :=
  splitC (k := 15) box13_160 box13_237

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_239 : Valid 3 5 13 ⟨64,0⟩ ⟨16,31⟩ ⟨8,0⟩ :=
  splitA (k := 127) box13_159 box13_238

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_240 : Valid 3 5 13 ⟨64,0⟩ ⟨16,31⟩ ⟨4,0⟩ :=
  splitC (k := 7) box13_150 box13_239

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_241 : Valid 3 5 13 ⟨64,127⟩ ⟨32,0⟩ ⟨4,7⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_242 : Valid 3 5 13 ⟨128,0⟩ ⟨32,63⟩ ⟨4,7⟩ :=
  validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_243 : Valid 3 5 13 ⟨128,255⟩ ⟨64,0⟩ ⟨4,5⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_244 : Valid 3 5 13 ⟨256,0⟩ ⟨64,127⟩ ⟨4,5⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_245 : Valid 3 5 13 ⟨256,0⟩ ⟨128,0⟩ ⟨4,4⟩ :=
  validUpper (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_246 : Valid 3 5 13 ⟨256,511⟩ ⟨128,0⟩ ⟨5,5⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_247 : Valid 3 5 13 ⟨512,0⟩ ⟨128,255⟩ ⟨5,5⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_248 : Valid 3 5 13 ⟨512,1023⟩ ⟨256,511⟩ ⟨5,5⟩ :=
  validRect (k := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_249 : Valid 3 5 13 ⟨512,1023⟩ ⟨512,0⟩ ⟨5,5⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_250 : Valid 3 5 13 ⟨512,1023⟩ ⟨256,0⟩ ⟨5,5⟩ :=
  splitB (k := 511) box13_248 box13_249

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_251 : Valid 3 5 13 ⟨1024,0⟩ ⟨256,0⟩ ⟨5,5⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_252 : Valid 3 5 13 ⟨512,0⟩ ⟨256,0⟩ ⟨5,5⟩ :=
  splitA (k := 1023) box13_250 box13_251

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_253 : Valid 3 5 13 ⟨512,0⟩ ⟨128,0⟩ ⟨5,5⟩ :=
  splitB (k := 255) box13_247 box13_252

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_254 : Valid 3 5 13 ⟨256,0⟩ ⟨128,0⟩ ⟨5,5⟩ :=
  splitA (k := 511) box13_246 box13_253

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_255 : Valid 3 5 13 ⟨256,0⟩ ⟨128,0⟩ ⟨4,5⟩ :=
  splitC (k := 4) box13_245 box13_254

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_256 : Valid 3 5 13 ⟨256,0⟩ ⟨64,0⟩ ⟨4,5⟩ :=
  splitB (k := 127) box13_244 box13_255

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_257 : Valid 3 5 13 ⟨128,0⟩ ⟨64,0⟩ ⟨4,5⟩ :=
  splitA (k := 255) box13_243 box13_256

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_258 : Valid 3 5 13 ⟨128,255⟩ ⟨64,0⟩ ⟨6,7⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_259 : Valid 3 5 13 ⟨256,0⟩ ⟨64,127⟩ ⟨6,7⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_260 : Valid 3 5 13 ⟨256,511⟩ ⟨128,255⟩ ⟨6,7⟩ :=
  validRect (k := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_261 : Valid 3 5 13 ⟨256,511⟩ ⟨256,0⟩ ⟨6,7⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_262 : Valid 3 5 13 ⟨256,511⟩ ⟨128,0⟩ ⟨6,7⟩ :=
  splitB (k := 255) box13_260 box13_261

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_263 : Valid 3 5 13 ⟨512,0⟩ ⟨128,0⟩ ⟨6,7⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_264 : Valid 3 5 13 ⟨256,0⟩ ⟨128,0⟩ ⟨6,7⟩ :=
  splitA (k := 511) box13_262 box13_263

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_265 : Valid 3 5 13 ⟨256,0⟩ ⟨64,0⟩ ⟨6,7⟩ :=
  splitB (k := 127) box13_259 box13_264

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_266 : Valid 3 5 13 ⟨128,0⟩ ⟨64,0⟩ ⟨6,7⟩ :=
  splitA (k := 255) box13_258 box13_265

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_267 : Valid 3 5 13 ⟨128,0⟩ ⟨64,0⟩ ⟨4,7⟩ :=
  splitC (k := 5) box13_257 box13_266

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_268 : Valid 3 5 13 ⟨128,0⟩ ⟨32,0⟩ ⟨4,7⟩ :=
  splitB (k := 63) box13_242 box13_267

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_269 : Valid 3 5 13 ⟨64,0⟩ ⟨32,0⟩ ⟨4,7⟩ :=
  splitA (k := 127) box13_241 box13_268

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_270 : Valid 3 5 13 ⟨64,127⟩ ⟨32,63⟩ ⟨8,15⟩ :=
  validRect (k := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_271 : Valid 3 5 13 ⟨64,95⟩ ⟨64,0⟩ ⟨8,15⟩ :=
  cycle (validRect (k := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_272 : Valid 3 5 13 ⟨96,127⟩ ⟨64,0⟩ ⟨8,15⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_273 : Valid 3 5 13 ⟨64,127⟩ ⟨64,0⟩ ⟨8,15⟩ :=
  splitA (k := 95) box13_271 box13_272

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_274 : Valid 3 5 13 ⟨64,127⟩ ⟨32,0⟩ ⟨8,15⟩ :=
  splitB (k := 63) box13_270 box13_273

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_275 : Valid 3 5 13 ⟨64,95⟩ ⟨32,47⟩ ⟨16,31⟩ :=
  validRect (k := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_276 : Valid 3 5 13 ⟨64,95⟩ ⟨48,63⟩ ⟨16,31⟩ :=
  validRect (k := 8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_277 : Valid 3 5 13 ⟨64,95⟩ ⟨32,63⟩ ⟨16,31⟩ :=
  splitB (k := 47) box13_275 box13_276

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_278 : Valid 3 5 13 ⟨64,79⟩ ⟨32,47⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_279 : Valid 3 5 13 ⟨80,95⟩ ⟨32,47⟩ ⟨32,0⟩ :=
  cycle (cycle (validRect (k := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_280 : Valid 3 5 13 ⟨64,95⟩ ⟨32,47⟩ ⟨32,0⟩ :=
  splitA (k := 79) box13_278 box13_279

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_281 : Valid 3 5 13 ⟨64,95⟩ ⟨48,63⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_282 : Valid 3 5 13 ⟨64,95⟩ ⟨32,63⟩ ⟨32,0⟩ :=
  splitB (k := 47) box13_280 box13_281

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_283 : Valid 3 5 13 ⟨64,95⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_277 box13_282

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_284 : Valid 3 5 13 ⟨96,127⟩ ⟨32,47⟩ ⟨16,31⟩ :=
  validRect (k := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_285 : Valid 3 5 13 ⟨96,127⟩ ⟨48,63⟩ ⟨16,31⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_286 : Valid 3 5 13 ⟨96,127⟩ ⟨32,63⟩ ⟨16,31⟩ :=
  splitB (k := 47) box13_284 box13_285

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_287 : Valid 3 5 13 ⟨96,127⟩ ⟨32,63⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_288 : Valid 3 5 13 ⟨96,127⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_286 box13_287

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_289 : Valid 3 5 13 ⟨64,127⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  splitA (k := 95) box13_283 box13_288

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_290 : Valid 3 5 13 ⟨64,79⟩ ⟨64,127⟩ ⟨16,31⟩ :=
  cycle (validRect (k := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_291 : Valid 3 5 13 ⟨80,95⟩ ⟨64,127⟩ ⟨16,31⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_292 : Valid 3 5 13 ⟨64,95⟩ ⟨64,127⟩ ⟨16,31⟩ :=
  splitA (k := 79) box13_290 box13_291

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_293 : Valid 3 5 13 ⟨64,95⟩ ⟨128,0⟩ ⟨16,31⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_294 : Valid 3 5 13 ⟨64,95⟩ ⟨64,0⟩ ⟨16,31⟩ :=
  splitB (k := 127) box13_292 box13_293

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_295 : Valid 3 5 13 ⟨64,95⟩ ⟨64,0⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_296 : Valid 3 5 13 ⟨64,95⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_294 box13_295

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_297 : Valid 3 5 13 ⟨96,127⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_298 : Valid 3 5 13 ⟨64,127⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  splitA (k := 95) box13_296 box13_297

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_299 : Valid 3 5 13 ⟨64,127⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  splitB (k := 63) box13_289 box13_298

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_300 : Valid 3 5 13 ⟨64,127⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box13_274 box13_299

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_301 : Valid 3 5 13 ⟨128,0⟩ ⟨32,63⟩ ⟨8,15⟩ :=
  validRect (k := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_302 : Valid 3 5 13 ⟨128,255⟩ ⟨64,127⟩ ⟨8,11⟩ :=
  validRect (k := 8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_303 : Valid 3 5 13 ⟨128,255⟩ ⟨64,127⟩ ⟨12,15⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_304 : Valid 3 5 13 ⟨128,255⟩ ⟨64,127⟩ ⟨8,15⟩ :=
  splitC (k := 11) box13_302 box13_303

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_305 : Valid 3 5 13 ⟨128,255⟩ ⟨128,0⟩ ⟨8,15⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_306 : Valid 3 5 13 ⟨128,255⟩ ⟨64,0⟩ ⟨8,15⟩ :=
  splitB (k := 127) box13_304 box13_305

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_307 : Valid 3 5 13 ⟨256,0⟩ ⟨64,0⟩ ⟨8,15⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_308 : Valid 3 5 13 ⟨128,0⟩ ⟨64,0⟩ ⟨8,15⟩ :=
  splitA (k := 255) box13_306 box13_307

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_309 : Valid 3 5 13 ⟨128,0⟩ ⟨32,0⟩ ⟨8,15⟩ :=
  splitB (k := 63) box13_301 box13_308

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_310 : Valid 3 5 13 ⟨128,255⟩ ⟨32,47⟩ ⟨16,31⟩ :=
  validRect (k := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_311 : Valid 3 5 13 ⟨128,255⟩ ⟨48,63⟩ ⟨16,31⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_312 : Valid 3 5 13 ⟨128,255⟩ ⟨32,63⟩ ⟨16,31⟩ :=
  splitB (k := 47) box13_310 box13_311

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_313 : Valid 3 5 13 ⟨128,255⟩ ⟨32,63⟩ ⟨32,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_314 : Valid 3 5 13 ⟨128,255⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  splitC (k := 31) box13_312 box13_313

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_315 : Valid 3 5 13 ⟨256,0⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_316 : Valid 3 5 13 ⟨128,0⟩ ⟨32,63⟩ ⟨16,0⟩ :=
  splitA (k := 255) box13_314 box13_315

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_317 : Valid 3 5 13 ⟨128,0⟩ ⟨64,0⟩ ⟨16,0⟩ :=
  validLower (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_318 : Valid 3 5 13 ⟨128,0⟩ ⟨32,0⟩ ⟨16,0⟩ :=
  splitB (k := 63) box13_316 box13_317

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_319 : Valid 3 5 13 ⟨128,0⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitC (k := 15) box13_309 box13_318

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_320 : Valid 3 5 13 ⟨64,0⟩ ⟨32,0⟩ ⟨8,0⟩ :=
  splitA (k := 127) box13_300 box13_319

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_321 : Valid 3 5 13 ⟨64,0⟩ ⟨32,0⟩ ⟨4,0⟩ :=
  splitC (k := 7) box13_269 box13_320

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_322 : Valid 3 5 13 ⟨64,0⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  splitB (k := 31) box13_240 box13_321

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_323 : Valid 3 5 13 ⟨32,0⟩ ⟨16,0⟩ ⟨4,0⟩ :=
  splitA (k := 63) box13_149 box13_322

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_324 : Valid 3 5 13 ⟨32,0⟩ ⟨16,0⟩ ⟨2,0⟩ :=
  splitC (k := 3) box13_26 box13_323

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_325 : Valid 3 5 13 ⟨32,0⟩ ⟨8,0⟩ ⟨2,0⟩ :=
  splitB (k := 15) box13_25 box13_324

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_326 : Valid 3 5 13 ⟨16,0⟩ ⟨8,0⟩ ⟨2,0⟩ :=
  splitA (k := 31) box13_18 box13_325

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_327 : Valid 3 5 13 ⟨16,0⟩ ⟨8,0⟩ ⟨1,0⟩ :=
  splitC (k := 1) box13_7 box13_326

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_328 : Valid 3 5 13 ⟨16,0⟩ ⟨4,0⟩ ⟨1,0⟩ :=
  splitB (k := 7) box13_6 box13_327

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_329 : Valid 3 5 13 ⟨8,0⟩ ⟨4,0⟩ ⟨1,0⟩ :=
  splitA (k := 15) box13_5 box13_328

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_330 : Valid 3 5 13 ⟨8,0⟩ ⟨2,0⟩ ⟨1,0⟩ :=
  splitB (k := 3) box13_4 box13_329

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_331 : Valid 3 5 13 ⟨4,0⟩ ⟨2,0⟩ ⟨1,0⟩ :=
  splitA (k := 7) box13_3 box13_330

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_332 : Valid 3 5 13 ⟨4,0⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  splitB (k := 1) box13_2 box13_331

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_333 : Valid 3 5 13 ⟨2,0⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  splitA (k := 3) box13_1 box13_332

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem box13_334 : Valid 3 5 13 ⟨1,0⟩ ⟨1,0⟩ ⟨1,0⟩ :=
  splitA (k := 1) box13_0 box13_333

theorem triples13 : Valid 3 5 13 ⟨1,0⟩ ⟨1,0⟩ ⟨1,0⟩ := box13_334
end A245212Local
namespace A245212Local
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Multiplicativity of the weighted sum, as in the earlier A245212 reduction. -/
private lemma weighted_mul (u v : ℕ) (hc : u.Coprime v) :
    (∑ d ∈ (u*v).divisors, d * d.divisors.card) =
    (∑ d ∈ u.divisors, d * d.divisors.card) * (∑ d ∈ v.divisors, d * d.divisors.card) := by
  let F : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta
  have hf : F.IsMultiplicative :=
    (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
  have he (n : ℕ) : F n = ∑ d ∈ n.divisors, d * d.divisors.card := by
    change ((ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta) n = _
    rw [ArithmeticFunction.mul_zeta_apply]
    simp only [pmul_apply, id_apply, sigma_zero_apply]
  simpa only [he] using hf.map_mul_of_coprime hc

private lemma weighted_at (p e : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^e).divisors, d*d.divisors.card) = moment p e := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp [moment,Nat.divisors_prime_pow hp]
private lemma sigma_at (p e : ℕ) (hp : p.Prime) : σ 1 (p^e)=geom p e := by
  simp [sigma_apply_prime_pow hp,geom]

theorem safe_gap {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p<q) (hqr : q<r) (safe : Safe p q r a b c) :
    let n := p^a*q^b*r^c
    OeisA245212.a n ≠ (σ 1 n : ℤ) := by
  intro n eq
  have hn : n ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)) (pow_ne_zero _ hr.ne_zero)
  have hs : (∑ d ∈ n.divisors,d*d.divisors.card) =
      n*n.divisors.card + ∑ d ∈ n.properDivisors,d*d.divisors.card := by
    conv_lhs => rw [← Nat.insert_self_properDivisors hn, sum_insert Nat.self_notMem_properDivisors]
  have balance : (∑ d ∈ n.divisors,d*d.divisors.card) + σ 1 n = 2*n*n.divisors.card := by
    rw [hs]
    unfold OeisA245212.a at eq
    zify
    linarith
  have hc1 := ((Nat.coprime_primes hp hq).mpr hpq.ne).pow_left a |>.pow_right b
  have hc2 := ((((Nat.coprime_primes hp hr).mpr (hpq.trans hqr).ne).pow_left a).mul_left
    (((Nat.coprime_primes hq hr).mpr hqr.ne).pow_left b)).pow_right c
  dsimp only [n] at balance
  rw [weighted_mul _ _ hc2,weighted_mul _ _ hc1,weighted_at p a hp,weighted_at q b hq,weighted_at r c hr,
    isMultiplicative_sigma.map_mul_of_coprime hc2,isMultiplicative_sigma.map_mul_of_coprime hc1,
    sigma_at p a hp,sigma_at q b hq,sigma_at r c hr,hc2.card_divisors_mul,hc1.card_divisors_mul,
    Nat.divisors_prime_pow hp,Nat.divisors_prime_pow hq,Nat.divisors_prime_pow hr] at balance
  simp only [card_map,card_range] at balance
  apply safe
  exact balance.trans (by unfold top; ring)

end A245212Local
open A245212Local
open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R2.H1 := by
  intro r a b c hr ha hb hc
  have fa : Fits ⟨1,0⟩ a := ⟨ha,Or.inl rfl⟩
  have fb : Fits ⟨1,0⟩ b := ⟨hb,Or.inl rfl⟩
  have fc : Fits ⟨1,0⟩ c := ⟨hc,Or.inl rfl⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at hr
  rcases hr with rfl|rfl|rfl
  · exact safe_gap (by decide) (by decide) (by decide) (by decide) (by decide) (triples7 a b c fa fb fc)
  · exact safe_gap (by decide) (by decide) (by decide) (by decide) (by decide) (triples11 a b c fa fb fc)
  · exact safe_gap (by decide) (by decide) (by decide) (by decide) (by decide) (triples13 a b c fa fb fc)
