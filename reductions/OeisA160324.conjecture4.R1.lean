import FormalConjectures.OEIS.«160324»
import Mathlib

/-!
# Sun's three consecutive polygonal numbers

Credit: @yuka30240

Write d = m - 1 and T(x) = x.choose 2. The sum of a triple is d times
its triangular level q = T(x) + T(y) + T(z), plus an offset independent of d.
Ordering a triple in opposite directions gives low and high offsets.
We prove that adjacent triangular levels overlap after adding the allowed
remainder whenever d ≥ 3 * (n / d). This leaves finitely many orders per level.
-/

namespace OMA.R_OeisA160324_conjecture4_R1

open OeisA160324

/-- At order four the remainder vanishes. The signs of the pentagonal and
hexagonal square roots enforce nonnegative polygonal indices. -/
def H1 : Prop := ∀ n : ℕ, ∃ (x : ℕ) (u v : ℤ),
  -1 ≤ u ∧ u % 6 = 5 ∧ -1 ≤ v ∧ v % 4 = 3 ∧
  24 * (n : ℤ) + 4 = 24 * (x : ℤ)^2 + u^2 + 3*v^2

/-- A finite covering problem at each quotient q. The parameter d, the
residue t, and all three indices have explicit bounds in terms of q. -/
def H2 : Prop := ∀ q : ℕ, ∀ d : Fin (3*q), 3 ≤ d.val → ∀ t : Fin d.val,
  ∃ x y z : Fin (q + 2),
    let s := polygonalNumber (d.val+2) x.val + polygonalNumber (d.val+3) y.val +
      polygonalNumber (d.val+4) z.val
    s ≤ d.val*q+t.val ∧ d.val*q+t.val ≤ s+(d.val-2)

section

variable (gauss : ∀ q : ℕ, ∃ a b c : ℕ, q = a.choose 2 + b.choose 2 + c.choose 2)

include gauss in
private lemma sorted_level (q : ℕ) :
    ∃ a b c : ℕ, a ≤ b ∧ b ≤ c ∧ q = a.choose 2 + b.choose 2 + c.choose 2 := by
  obtain ⟨a,b,c,h⟩ := gauss q
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact ⟨a,b,c,hab,hbc,h⟩
    · rcases le_total a c with hac | hca
      · exact ⟨a,c,b,hac,hcb,by omega⟩
      · exact ⟨c,a,b,hca,hab,by omega⟩
  · rcases le_total a c with hac | hca
    · exact ⟨b,a,c,hba,hac,by omega⟩
    · rcases le_total b c with hbc | hcb
      · exact ⟨b,c,a,hbc,hca,by omega⟩
      · exact ⟨c,b,a,hcb,hba,by omega⟩

private lemma spread {a c : ℕ} (hc : 6 ≤ c) (hac : a < c) :
    a.choose 2 + 2*c + 2 ≤ c.choose 2 + 2*a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hc
  clear hc
  induction k generalizing a with
  | zero => interval_cases a <;> decide
  | succ k ih =>
    change a.choose 2 + 2*(6+k+1) + 2 ≤ (6+k+1).choose 2 + 2*a
    rw [Nat.choose_succ_succ' (6+k) 1, Nat.choose_one_right]
    change a.choose 2 + 2*(6+k+1) + 2 ≤ 6+k+(6+k).choose 2+2*a
    by_cases h : a = 6+k
    · subst a; omega
    · have := ih (by omega : a < 6+k)
      omega

private lemma top_at_least_six {q a b c : ℕ} (hq : 31 ≤ q) (hab : a ≤ b) (hbc : b ≤ c)
    (h : q = a.choose 2 + b.choose 2 + c.choose 2) : 6 ≤ c := by
  by_contra! hc
  have hc' := Nat.choose_le_choose 2 (show c ≤ 5 by omega)
  have hb' := Nat.choose_le_choose 2 hbc
  have ha' := Nat.choose_le_choose 2 hab
  change c.choose 2 ≤ 10 at hc'
  omega

include gauss in
/-- The large offset at level q exceeds the small offset at level q+1.
Swapping the extreme indices changes the sign of their triangular difference. -/
private lemma adjacent_offsets (q : ℕ) :
    ∃ a b c i j k : ℕ,
      q = a.choose 2 + b.choose 2 + c.choose 2 ∧
      q+1 = i.choose 2 + j.choose 2 + k.choose 2 ∧
      k+j+i+j.choose 2+2*i.choose 2 < a+b+c+b.choose 2+2*c.choose 2 := by
  by_cases small : q < 31
  · interval_cases q
    · exact ⟨1, 1, 1, 0, 0, 2, by decide⟩
    · exact ⟨1, 1, 2, 0, 2, 2, by decide⟩
    · exact ⟨1, 2, 2, 0, 0, 3, by decide⟩
    · exact ⟨1, 1, 3, 0, 2, 3, by decide⟩
    · exact ⟨1, 2, 3, 2, 2, 3, by decide⟩
    · exact ⟨2, 2, 3, 0, 0, 4, by decide⟩
    · exact ⟨1, 1, 4, 0, 2, 4, by decide⟩
    · exact ⟨1, 2, 4, 2, 2, 4, by decide⟩
    · exact ⟨2, 2, 4, 0, 3, 4, by decide⟩
    · exact ⟨1, 3, 4, 0, 0, 5, by decide⟩
    · exact ⟨1, 1, 5, 0, 2, 5, by decide⟩
    · exact ⟨1, 2, 5, 2, 2, 5, by decide⟩
    · exact ⟨2, 2, 5, 0, 3, 5, by decide⟩
    · exact ⟨1, 3, 5, 2, 3, 5, by decide⟩
    · exact ⟨2, 3, 5, 0, 0, 6, by decide⟩
    · exact ⟨1, 1, 6, 0, 2, 6, by decide⟩
    · exact ⟨1, 2, 6, 2, 2, 6, by decide⟩
    · exact ⟨2, 2, 6, 0, 3, 6, by decide⟩
    · exact ⟨1, 3, 6, 2, 3, 6, by decide⟩
    · exact ⟨2, 3, 6, 0, 5, 5, by decide⟩
    · exact ⟨1, 5, 5, 0, 0, 7, by decide⟩
    · exact ⟨1, 1, 7, 0, 2, 7, by decide⟩
    · exact ⟨1, 2, 7, 2, 2, 7, by decide⟩
    · exact ⟨2, 2, 7, 0, 3, 7, by decide⟩
    · exact ⟨1, 3, 7, 2, 3, 7, by decide⟩
    · exact ⟨2, 3, 7, 2, 5, 6, by decide⟩
    · exact ⟨2, 5, 6, 0, 4, 7, by decide⟩
    · exact ⟨1, 4, 7, 0, 0, 8, by decide⟩
    · exact ⟨1, 1, 8, 0, 2, 8, by decide⟩
    · exact ⟨1, 2, 8, 2, 2, 8, by decide⟩
    · exact ⟨2, 2, 8, 0, 3, 8, by decide⟩
  · obtain ⟨a,b,c,hab,hbc,hq⟩ := sorted_level gauss q
    obtain ⟨i,j,k,hij,hjk,hq'⟩ := sorted_level gauss (q+1)
    have hc := top_at_least_six (by omega) hab hbc hq
    have hk := top_at_least_six (by omega) hij hjk hq'
    have hac := hab.trans hbc
    have hik := hij.trans hjk
    have hic : i ≤ c := by
      by_contra! h
      have inc := Nat.choose_le_choose 2 (show c+1 ≤ i by omega)
      rw [Nat.choose_succ_succ' c 1, Nat.choose_one_right] at inc
      change c + c.choose 2 ≤ i.choose 2 at inc
      have ba := Nat.choose_le_choose 2 hac
      have bb := Nat.choose_le_choose 2 hbc
      have bj := Nat.choose_le_choose 2 hij
      have bk := Nat.choose_le_choose 2 hik
      omega
    refine ⟨a,b,c,i,j,k,hq,hq',?_⟩
    by_cases h : a = c
    · have h' : i < k := by
        by_contra! he
        have : b = a := by omega
        have : j = i := by omega
        have : k = i := by omega
        simp_all only
        omega
      have := spread hk h'
      have : b = c := by omega
      subst a; subst b
      omega
    · have h₁ := spread hc (show a < c by omega)
      by_cases h' : i = k
      · have : j = k := by omega
        subst i; subst j
        omega
      · have h₂ := spread hk (show i < k by omega)
        omega

private lemma index_le (x : ℕ) : x ≤ x.choose 2 + 1 := by
  induction x with
  | zero => decide
  | succ x ih =>
    rw [Nat.choose_succ_succ x 1, Nat.choose_one_right]
    omega

private lemma triple_value (d x y z : ℕ) :
    polygonalNumber (d+2) x + polygonalNumber (d+3) y + polygonalNumber (d+4) z =
      d*(x.choose 2 + y.choose 2 + z.choose 2) + (x+y+z+y.choose 2+2*z.choose 2) := by
  simp only [polygonalNumber, ← Nat.choose_two_right]
  rw [show d+2-2 = d by omega, show d+3-2 = d+1 by omega, show d+4-2 = d+2 by omega]
  ring

include gauss in
/-- Gauss's theorem alone covers the entire range d ≥ 3q. -/
theorem large_order {d q t : ℕ} (hd : 2 ≤ d) (large : 3*q ≤ d) (ht : t < d) :
    ∃ x y z r : ℕ, r ≤ d-2 ∧ d*q+t =
      polygonalNumber (d+2) x + polygonalNumber (d+3) y + polygonalNumber (d+4) z + r := by
  cases q with
  | zero =>
    by_cases h : t = 0
    · exact ⟨0,0,0,0,by omega,by simp [polygonalNumber,h]⟩
    · exact ⟨1,0,0,t-1,by omega,by simp [polygonalNumber]; omega⟩
  | succ q =>
    obtain ⟨a,b,c,i,j,k,prev,curr,overlap⟩ := adjacent_offsets gauss q
    let low := k+j+i+j.choose 2+2*i.choose 2
    let high := a+b+c+b.choose 2+2*c.choose 2
    change low < high at overlap
    have pos : 0 < low := by
      by_contra! h
      have hi : i = 0 := by dsimp [low] at h; omega
      have hj : j = 0 := by dsimp [low] at h; omega
      have hk : k = 0 := by dsimp [low] at h; omega
      simp [hi,hj,hk] at curr
    by_cases above : low ≤ t
    · refine ⟨k,j,i,t-low,by omega,?_⟩
      rw [triple_value, show k.choose 2+j.choose 2+i.choose 2 = q+1 by omega]
      change d*(q+1)+t = d*(q+1)+low+(t-low)
      omega
    · have bound : high ≤ d := by
        dsimp [high]
        have := index_le a
        have := index_le b
        have := index_le c
        omega
      refine ⟨a,b,c,d+t-high,by omega,?_⟩
      rw [triple_value, ← prev, Nat.mul_succ]
      change d*q+d+t = d*q+high+(d+t-high)
      omega

end

private lemma twice_choose (x : ℕ) : 2*x.choose 2 + x = x^2 := by
  induction x with
  | zero => decide
  | succ x ih =>
    rw [Nat.choose_succ_succ x 1, Nat.choose_one_right]
    change 2*(x+x.choose 2)+(x+1) = (x+1)^2
    nlinarith only [ih]

private lemma order_four (roots : H1) (n : ℕ) :
    ∃ x y z r : ℕ, r ≤ 0 ∧ n =
      polygonalNumber 4 x + polygonalNumber 5 y + polygonalNumber 6 z + r := by
  obtain ⟨x,u,v,hu,hu6,hv,hv4,h⟩ := roots n
  let y := ((u+1)/6).toNat
  let z := ((v+1)/4).toNat
  have uy : u = 6*(y : ℤ)-1 := by dsimp [y]; omega
  have vz : v = 4*(z : ℤ)-1 := by dsimp [z]; omega
  rw [uy,vz] at h
  refine ⟨x,y,z,0,by decide,?_⟩
  simp only [polygonalNumber, ← Nat.choose_two_right, Nat.reduceSub, add_zero]
  have hx := twice_choose x
  have hy := twice_choose y
  have hz := twice_choose z
  zify at hx hy hz ⊢
  nlinarith only [h,hx,hy,hz]

/-- At level Q ≥ 2 the bound 3Q+3 on an offset is strict. Equality would
force the first two indices to have triangular value zero and the last
index to be at most two. -/
private lemma offset_bound {x y z : ℕ} (hq : 2 ≤ x.choose 2 + y.choose 2 + z.choose 2) :
    x+y+z+y.choose 2+2*z.choose 2 ≤ 3*(x.choose 2+y.choose 2+z.choose 2)+2 := by
  have hx := index_le x
  have hy := index_le y
  have hz := index_le z
  by_contra! bad
  have hz' : z.choose 2 + 1 = z := by omega
  have hz2 : 3 ≤ z := by
    by_contra! h
    interval_cases z <;> simp_all <;> omega
  have hz3 := twice_choose z
  nlinarith only [hz3,hz',Nat.mul_le_mul_right z hz2]

/-- The top residue at d = 3q-1 in the finite family forces an exact
triangular representation of q. Thus the reduction needs no extra hypothesis
for Gauss's theorem. -/
private lemma triangular_of_finite_windows (windows : H2) (q : ℕ) :
    ∃ x y z : ℕ, q = x.choose 2 + y.choose 2 + z.choose 2 := by
  by_cases small : q ≤ 2
  · interval_cases q
    · exact ⟨0,0,0,rfl⟩
    · exact ⟨2,0,0,rfl⟩
    · exact ⟨2,2,0,rfl⟩
  let d := 3*q-1
  have hd : 3 ≤ d := by dsimp [d]; omega
  have hdq : d+1 = 3*q := by dsimp [d]; omega
  obtain ⟨x,y,z,h⟩ := windows q ⟨d,by omega⟩ hd ⟨d-1,show d-1 < d by omega⟩
  dsimp only at h
  rw [triple_value] at h
  let level := x.val.choose 2 + y.val.choose 2 + z.val.choose 2
  let offset := x.val+y.val+z.val+y.val.choose 2+2*z.val.choose 2
  change d*level+offset ≤ d*q+(d-1) ∧ d*q+(d-1) ≤ d*level+offset+(d-2) at h
  refine ⟨x.val,y.val,z.val,?_⟩
  change q = level
  rcases lt_trichotomy q level with lt | eq | gt
  · have := Nat.mul_le_mul_left d (show q+1 ≤ level by omega)
    rw [Nat.mul_succ] at this
    omega
  · exact eq
  · have le := Nat.mul_le_mul_left d (show level+1 ≤ q by omega)
    rw [Nat.mul_succ] at le
    have full : offset ≤ 3*level+3 := by
      dsimp [offset,level]
      have := index_le x.val
      have := index_le y.val
      have := index_le z.val
      omega
    have strict := offset_bound (x := x.val) (y := y.val) (z := z.val)
      (show 2 ≤ level by omega)
    change offset ≤ 3*level+2 at strict
    omega

theorem main : H1 → H2 → type_of% @OeisA160324.conjecture4 := by
  intro roots windows m hm n
  by_cases base : m = 3
  · subst m; exact order_four roots n
  let d := m-1
  let q := n/d
  let t := n%d
  have hd : 3 ≤ d := by dsimp [d]; omega
  have ht : t < d := Nat.mod_lt _ (by omega)
  have split : n = d*q+t := (Nat.div_add_mod n d).symm
  have hm' : m = d+1 := by dsimp [d]; omega
  rw [hm']
  change ∃ x y z r : ℕ, r ≤ d+1-3 ∧ n =
    polygonalNumber (d+2) x + polygonalNumber (d+3) y + polygonalNumber (d+4) z + r
  rw [show d+1-3 = d-2 by omega,split]
  by_cases large : 3*q ≤ d
  · exact large_order (triangular_of_finite_windows windows) (by omega) large ht
  · obtain ⟨x,y,z,h⟩ := windows q ⟨d,by omega⟩ hd ⟨t,ht⟩
    let s := polygonalNumber (d+2) x.val + polygonalNumber (d+3) y.val +
      polygonalNumber (d+4) z.val
    change s ≤ d*q+t ∧ d*q+t ≤ s+(d-2) at h
    exact ⟨x.val,y.val,z.val,d*q+t-s,by omega,by change d*q+t = s+(d*q+t-s); omega⟩

end OMA.R_OeisA160324_conjecture4_R1
