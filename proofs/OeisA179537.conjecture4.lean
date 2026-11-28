import FormalConjectures.OEIS.«179537»
import Mathlib

/-!
# Sun's weighted alternating congruence for A179537

Reorder the defining finite sum by its inner binomial index. Two telescoping
identities evaluate the alternating columns modulo the square of the prime.
A third finite identity evaluates the weighted sum of cubed central binomial
coefficients. The remaining sum reduces by the binomial theorem and quadratic
reciprocity to the Legendre symbol modulo seven.
-/

namespace SunAlternating

theorem reorder (R : Type*) [CommRing R] (p : ℕ) (hp : 0 < p) (w : ℕ → R) :
    ∑ n ∈ Finset.range p, w n * (OeisA179537.a n : R) =
      ∑ j ∈ Finset.range ((p-1)/2+1), ((-16:R)^j * ((2*j).choose j : R)^2) *
        ∑ n ∈ Finset.range p, w n * (n.choose (2*j) : R)^2 := by
  let f (j : ℕ) : R := (-16:R)^j * ((2*j).choose j : R)^2
  have row (n : ℕ) (hn : n < p) : (OeisA179537.a n : R) =
      ∑ j ∈ Finset.range p, f j * (n.choose (2*j) : R)^2 := by
    unfold OeisA179537.a
    push_cast
    calc
      _ = ∑ j ∈ Finset.range (n+1), f j * (n.choose (2*j) : R)^2 := by
        apply Finset.sum_congr rfl
        intro j _
        have h := Nat.choose_mul (n:=n) (k:=2*j) (s:=j) (by omega)
        rw [show 2*j-j=j by omega] at h
        have e := congrArg (fun t : ℕ => (t:R)) h
        push_cast at e
        dsimp only [f]
        linear_combination -(-16:R)^j * congrArg (fun t : R => t^2) e
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j _ hj
        simp only [Finset.mem_range] at hj
        simp [Nat.choose_eq_zero_of_lt (show n < 2*j by omega)]
  calc
    _ = ∑ n ∈ Finset.range p, ∑ j ∈ Finset.range p,
        w n * (f j * (n.choose (2*j) : R)^2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [row n (Finset.mem_range.mp hn), Finset.mul_sum]
    _ = ∑ j ∈ Finset.range p, ∑ n ∈ Finset.range p,
        w n * (f j * (n.choose (2*j) : R)^2) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range ((p-1)/2+1), ∑ n ∈ Finset.range p,
        w n * (f j * (n.choose (2*j) : R)^2) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      simp only [Finset.mem_range] at hj
      apply Finset.sum_eq_zero
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [Nat.choose_eq_zero_of_lt (show n < 2*j by omega)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      dsimp only [f]
      ring

end SunAlternating

namespace SunAlternating

variable {R : Type*} [CommRing R]

theorem chooseAcross (n m : ℕ) :
    ((m:R)+1) * (n.choose (m+1) : R) = ((n:R)-m)*(n.choose m : R) := by
  by_cases h : m ≤ n
  · have e := congrArg (fun t : ℕ => (t:R)) (Nat.choose_succ_right_eq n m)
    push_cast [h] at e
    linear_combination e
  · have a : n < m := by omega
    simp [Nat.choose_eq_zero_of_lt a, Nat.choose_eq_zero_of_lt (show n < m+1 by omega)]

theorem chooseUp (n m : ℕ) :
    ((n:R)+1-m)*( (n+1).choose m : R) = ((n:R)+1)*(n.choose m : R) := by
  by_cases h : m ≤ n+1
  · have e := congrArg (fun t : ℕ => (t:R)) (Nat.choose_mul_succ_eq n m)
    push_cast [h] at e
    linear_combination -e
  · simp [Nat.choose_eq_zero_of_lt (show n < m by omega),
      Nat.choose_eq_zero_of_lt (show n+1 < m by omega)]

private def cert (n m : R) := 2*n^2-(6*m+8)*n+(5*m+8)*(m+1)

private def boundary (R : Type*) [CommRing R] (n m : ℕ) : R :=
  -(-1:R)^n * (((n:R)-m)*(n.choose m : R))^2 * cert (n:R) (m:R)

/-- The alternating sum of squared binomial coefficients in a fixed column. -/
def altColumn (R : Type*) [CommRing R] (N m : ℕ) : R :=
  ∑ n ∈ Finset.range N, (-1:R)^n * (n.choose m : R)^2

private theorem step (n m : ℕ) :
    ((m:R)+1)^2*((m:R)+2) *
        (4*((m:R)+2)*((-1:R)^n*(n.choose (m+2) : R)^2)
        + ((m:R)+1)*((-1:R)^n*(n.choose m : R)^2)) =
      boundary R (n+1) m - boundary R n m := by
  have c₁ := chooseAcross (R:=R) n m
  have c₂ := chooseAcross (R:=R) n (m+1)
  push_cast at c₂
  have c : ((m:R)+1)*((m:R)+2)*(n.choose (m+2):R) =
      ((n:R)-m-1)*((n:R)-m)*(n.choose m:R) := by
    linear_combination ((m:R)+1)*c₂ + ((n:R)-m-1)*c₁
  unfold boundary
  push_cast
  rw [chooseUp, pow_succ]
  unfold cert
  linear_combination 4*(-1:R)^n * congrArg (fun t : R => t^2) c

private theorem telescope (N m : ℕ) :
    ((m:R)+1)^2*((m:R)+2) *
      (4*((m:R)+2)*altColumn R N (m+2) + ((m:R)+1)*altColumn R N m) =
      boundary R N m := by
  induction N with
  | zero => cases m <;> simp [altColumn,boundary,Nat.choose]
  | succ N IH =>
    simp only [altColumn,Finset.sum_range_succ] at *
    linear_combination IH + step (R:=R) N m

theorem unitBelow {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : 0 < i) (h : i < p) :
    IsUnit (i : ZMod (p^2)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0<2)).2 fun hd =>
    (Nat.not_le_of_gt h) (Nat.le_of_dvd hi hd)

theorem columnRecurrence {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : m+2 < p) :
    4*((m:ZMod (p^2))+2)*altColumn (ZMod (p^2)) p (m+2) +
      ((m:ZMod (p^2))+1)*altColumn (ZMod (p^2)) p m = 0 := by
  have u₁ := unitBelow hp (m+1) (by omega) (by omega)
  have u₂ := unitBelow hp (m+2) (by omega) hm
  push_cast at u₁ u₂
  apply ((u₁.pow 2).mul u₂).mul_left_cancel
  rw [mul_zero, telescope]
  have hN : p-1+1=p := by have := hp.pos; omega
  have he := chooseUp (R:=ZMod (p^2)) (p-1) m
  rw [← Nat.cast_add_one, hN] at he
  unfold boundary
  rw [he, mul_pow]
  have hz : (p : ZMod (p^2))^2 = 0 :=
    (Nat.cast_pow (α := ZMod (p^2)) p 2).symm.trans (ZMod.natCast_self (p^2))
  rw [hz]
  ring

theorem alternating_transform {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (j : ℕ) (hj : 2*j < p) :
    (-16 : ZMod (p^2))^j * altColumn (ZMod (p^2)) p (2*j) =
      ((2*j).choose j : ZMod (p^2)) := by
  induction j with
  | zero =>
    have ho := hp.odd_of_ne_two hp2
    simp [altColumn,neg_one_geom_sum,Nat.not_even_iff_odd.mpr ho]
  | succ j IH =>
    have h := columnRecurrence hp (2*j) (by omega)
    have ih := IH (by omega)
    have hc := congrArg (fun t : ℕ => (t : ZMod (p^2))) (Nat.succ_mul_centralBinom_succ j)
    simp only [Nat.centralBinom] at hc
    have hu := unitBelow hp (j+1) (by omega) (by omega)
    push_cast at hu hc h
    apply hu.mul_left_cancel
    rw [show 2*(j+1) = 2*j+2 by omega] at hc ⊢
    rw [pow_succ (-16:ZMod (p^2)) j]
    linear_combination -2*(-16 : ZMod (p^2))^j*h + 2*(2*(j:ZMod (p^2))+1)*ih - hc

end SunAlternating

namespace SunWeightedColumn

open SunAlternating

def column (R : Type*) [CommRing R] (N m : ℕ) : R :=
  ∑ n ∈ Finset.range N, (-1:R)^n * (2*(n:R)-m+1) * (n.choose m : R)^2

private def cert {R : Type*} [CommRing R] (n m : R) : R :=
  4*n^3 - (14*m+20)*n^2 + (16*m^2+44*m+28)*n - (5*m^3+18*m^2+18*m+4)

private def boundary (R : Type*) [CommRing R] (n m : ℕ) : R :=
  -(-1:R)^n * (((n:R)-m)*(n.choose m : R))^2 * cert (n:R) (m:R)

variable {R : Type*} [CommRing R]

private theorem step (n m : ℕ) :
    ((m:R)+1)*((m:R)+2)^2 *
      (4*((m:R)+1)*((-1:R)^n*(2*(n:R)-((m:R)+2)+1)*(n.choose (m+2):R)^2)
        + ((m:R)+2)*((-1:R)^n*(2*(n:R)-m+1)*(n.choose m:R)^2)) =
      boundary R (n+1) m - boundary R n m := by
  have c₁ := chooseAcross (R:=R) n m
  have c₂ := chooseAcross (R:=R) n (m+1)
  push_cast at c₂
  have c : ((m:R)+1)*((m:R)+2)*(n.choose (m+2):R) =
      ((n:R)-m-1)*((n:R)-m)*(n.choose m:R) := by
    linear_combination ((m:R)+1)*c₂ + ((n:R)-m-1)*c₁
  unfold boundary
  push_cast
  rw [chooseUp, pow_succ (a := (-1:R))]
  unfold cert
  linear_combination 4*(-1:R)^n*(2*(n:R)-m-1)*congrArg (fun t : R => t^2) c

private theorem telescope (N m : ℕ) :
    ((m:R)+1)*((m:R)+2)^2 *
      (4*((m:R)+1)*column R N (m+2) + ((m:R)+2)*column R N m) =
      boundary R N m := by
  induction N with
  | zero => cases m <;> simp [column,boundary,Nat.choose]
  | succ N ih =>
    simp only [column,Finset.sum_range_succ] at *
    have h := step (R:=R) N m
    push_cast at ih ⊢
    linear_combination ih + h

theorem recurrence {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : m+2 < p) :
    4*((m:ZMod (p^2))+1)*column (ZMod (p^2)) p (m+2) +
      ((m:ZMod (p^2))+2)*column (ZMod (p^2)) p m = 0 := by
  have u₁ := unitBelow hp (m+1) (by omega) (by omega)
  have u₂ := unitBelow hp (m+2) (by omega) hm
  push_cast at u₁ u₂
  apply (u₁.mul (u₂.pow 2)).mul_left_cancel
  rw [mul_zero, telescope]
  have hN : p-1+1=p := by have := hp.pos; omega
  have he := chooseUp (R:=ZMod (p^2)) (p-1) m
  rw [← Nat.cast_add_one, hN] at he
  unfold boundary
  rw [he, mul_pow]
  have hz : (p : ZMod (p^2))^2 = 0 :=
    (Nat.cast_pow (α := ZMod (p^2)) p 2).symm.trans (ZMod.natCast_self (p^2))
  rw [hz]
  ring

private theorem column_zero (N : ℕ) :
    column R N 0 = -(-1:R)^N * N := by
  induction N with
  | zero => simp [column]
  | succ k ih =>
    unfold column at *
    rw [Finset.sum_range_succ,ih]
    simp only [Nat.cast_succ, pow_succ, Nat.cast_zero, sub_zero, Nat.choose_zero_right,
      Nat.cast_one, one_pow, mul_one]
    ring

theorem transform {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (j : ℕ) (hj : 2*j < p) :
    ((2*j).choose j : ZMod (p^2))*column (ZMod (p^2)) p (2*j) =
      (p:ZMod (p^2))*(-1)^j := by
  induction j with
  | zero => simp [column_zero,(hp.odd_of_ne_two hp2).neg_one_pow]
  | succ j ih =>
    have h := recurrence hp (2*j) (by omega)
    have prev := ih (by omega)
    have hc := congrArg (fun t : ℕ => (t : ZMod (p^2))) (Nat.succ_mul_centralBinom_succ j)
    simp only [Nat.centralBinom] at hc
    have hu := unitBelow hp (j+1) (by omega) (by omega)
    have htwo := unitBelow hp 2 (by omega) (by have := hp.two_le; omega)
    push_cast at hu htwo hc h
    apply (htwo.mul hu).mul_left_cancel
    rw [show 2*(j+1)=2*j+2 by omega] at *
    rw [pow_succ (-1 : ZMod (p^2))]
    linear_combination ((2*j).choose j : ZMod (p^2))*h +
      2*column (ZMod (p^2)) p (2*j+2)*hc - 2*((j:ZMod (p^2))+1)*prev

end SunWeightedColumn

open Finset

namespace SunWeighted

private def c (n k : ℕ) : ℤ := (n+k).choose n

private theorem c_sym (n k : ℕ) : c n k = c k n := by
  unfold c
  rw [Nat.choose_symm_add, Nat.add_comm n k]

private theorem c_pascal (n k : ℕ) :
    c (n+1) (k+1) = c n (k+1) + c (n+1) k := by
  unfold c
  rw [show n+1+(k+1) = (n+k+1)+1 by omega, Nat.choose_succ_succ]
  simp only [Nat.cast_add, show n+(k+1) = n+k+1 by omega, show n+1+k = n+k+1 by omega]

private theorem c_ratio (n k : ℕ) :
    (n+k+1 : ℤ) * c n k = (n+1 : ℤ) * c (n+1) k := by
  unfold c
  rw [show n+1+k = n+k+1 by omega]
  exact_mod_cast (Nat.add_one_mul_choose_eq (n+k) n).trans (Nat.mul_comm _ _)

private theorem c_twice (n : ℕ) : c (n+1) (n+1) = 2 * c n (n+1) := by
  rw [c_pascal, c_sym (n+1) n]
  ring

private theorem c_central_ratio (n : ℕ) :
    ((n:ℤ)+1) * c (n+1) (n+1) = 2*(2*n+1) * c n n := by
  rw [c_twice, c_sym n (n+1)]
  linear_combination -2 * c_ratio n n

private theorem telescope (n k : ℕ) :
    8*(2*((n:ℤ)+1)+1)*(∑ i ∈ range k, c (n+1) i ^ 2) -
      4*((n:ℤ)+1)*(∑ i ∈ range k, c n i ^ 2) =
    4*(2*(k:ℤ)+3*((n:ℤ)+1))*(c (n+1) k - c n k)^2 := by
  induction k with
  | zero => simp [c]
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ, c_pascal]
    push_cast
    linear_combination ih + (8*c n k-16*c (n+1) k) * c_ratio n k

private theorem c_sum_step (n : ℕ) :
    8*(2*((n:ℤ)+1)+1)*(∑ i ∈ range (n+1+1), c (n+1) i ^ 2) -
      4*((n:ℤ)+1)*(∑ i ∈ range (n+1), c n i ^ 2) =
    (21*((n:ℤ)+1)+8)*c (n+1) (n+1)^2 := by
  rw [sum_range_succ]
  have h := telescope n (n+1)
  push_cast at h
  rw [c_twice] at h ⊢
  linear_combination h

/-- Sun's finite identity for the cubic central-binomial sum. -/
theorem central_identity (n : ℕ) :
    (∑ k ∈ range (n+1), (21*(k:ℤ)+8)*c k k ^ 3) =
      4*((n:ℤ)+1)*c (n+1) (n+1)*(∑ k ∈ range (n+1), c n k^2) := by
  induction n with
  | zero => norm_num [c, Finset.sum_range_succ]
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    have e := c_sum_step n
    have q := c_central_ratio (n+1)
    push_cast at q
    linear_combination -c (n+1) (n+1) * e -
      4*(∑ k ∈ range (n+1+1), c (n+1) k^2) * q

theorem full_congr (p : ℕ) [Fact p.Prime] :
    (∑ k ∈ range p, (21*(k:ℤ)+8)*((2*k).choose k : ℤ)^3) ≡ 8*(p:ℤ) [ZMOD (p:ℤ)^2] := by
  have hp := Fact.out (p := p.Prime)
  have hp0 := hp.pos
  have hb : c p p ≡ 2 [ZMOD (p:ℤ)] := by
    simpa [c, Nat.mul_two] using Choose.choose_mul_mul_modEq_choose (p:=p) (a:=2) (b:=1)
  have ht : (∑ k ∈ range p, c (p-1) k ^ 2) ≡ 1 [ZMOD (p:ℤ)] := by
    have h := Int.sum_modEq_single (n:=(p:ℤ)) (s:=range p) (a:=0)
      (f:=fun k => c (p-1) k ^ 2) (by simp [hp.pos]) (by
        intro k hk hk0
        rw [mem_range] at hk
        have hD := hp.dvd_choose (a:=p-1) (b:=p-1+k) (by omega) (by omega) (by omega)
        have hi : (p:ℤ) ∣ c (p-1) k := by unfold c; exact_mod_cast hD
        exact Int.modEq_zero_iff_dvd.mpr (dvd_pow hi (by decide)))
    simpa [c] using h
  have h := (hb.mul ht).mul_left 4
  have h' : (p:ℤ) * (4 * (c p p * ∑ k ∈ range p, c (p-1) k^2)) ≡
      (p:ℤ) * (4 * ((2:ℤ)*1)) [ZMOD (p:ℤ)*(p:ℤ)] := h.mul_left'
  have he := central_identity (p-1)
  rw [show p-1+1=p by omega] at he
  rw [show ((p-1:ℕ):ℤ)+1=(p:ℤ) by omega] at he
  simpa only [← Nat.two_mul, c, mul_left_comm, mul_assoc, mul_one, pow_two] using
    (show (∑ k ∈ range p, (21*(k:ℤ)+8)*c k k^3) ≡ 8*(p:ℤ) [ZMOD (p:ℤ)^2] by
      rw [he]
      convert h' using 1 <;> ring)

theorem half_congr (p : ℕ) [Fact p.Prime] :
    (∑ k ∈ range ((p-1)/2+1), (21*(k:ℤ)+8)*((2*k).choose k : ℤ)^3) ≡
      8*(p:ℤ) [ZMOD (p:ℤ)^2] := by
  have hp := Fact.out (p := p.Prime)
  have hp0 := hp.pos
  let f (k : ℕ) : ℤ := (21*(k:ℤ)+8)*((2*k).choose k : ℤ)^3
  have ht : (∑ k ∈ Ico ((p-1)/2+1) p, f k) ≡ 0 [ZMOD (p:ℤ)^2] := by
    apply Int.ModEq.sum_zero
    intro k hk
    obtain ⟨hk₁,hk₂⟩ := mem_Ico.mp hk
    have hd := hp.dvd_choose (a:=k) (b:=2*k) hk₂ (by omega) (by omega)
    obtain ⟨q,hq⟩ := hd
    apply Int.modEq_zero_iff_dvd.mpr
    refine ⟨(21*(k:ℤ)+8)*(p:ℤ)*(q:ℤ)^3, ?_⟩
    simp only [f, hq, Nat.cast_mul]
    ring
  have hf : (∑ k ∈ range p, f k) ≡ 8*(p:ℤ) [ZMOD (p:ℤ)^2] := full_congr p
  rw [← sum_range_add_sum_Ico f (show (p-1)/2+1 ≤ p by omega)] at hf
  exact (by simpa using ht.add_left (∑ k ∈ range ((p-1)/2+1), f k) :
    (∑ k ∈ range ((p-1)/2+1), f k) + ∑ k ∈ Ico ((p-1)/2+1) p, f k ≡
      (∑ k ∈ range ((p-1)/2+1), f k) [ZMOD (p:ℤ)^2]).symm.trans hf

end SunWeighted

namespace SunSplit

/-- The central binomial coefficient reduced at the midpoint of an odd prime. -/
theorem centralBinom_mod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {j : ℕ} (hj : j ≤ p / 2) :
    (Nat.centralBinom j : ZMod p) = (-4 : ZMod p)^j * ((p/2).choose j : ZMod p) := by
  have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two (p := p) Fact.out).2 hp
  have hhalf : 2 * (p/2 : ℕ) + 1 = p := by omega
  have hzero : 2 * ((p / 2 : ℕ) : ZMod p) + 1 = 0 := by
    have h : ((2 * (p/2) + 1 : ℕ) : ZMod p) = (p : ZMod p) := congrArg Nat.cast hhalf
    simpa using h
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j ≤ p/2 := by omega
    have hjp : j+1 < p := by have := (Fact.out : p.Prime).two_le; omega
    have hj0 : ((j : ZMod p) + 1) ≠ 0 := by
      change ¬ ((j : ZMod p) + 1) = 0
      rw [← Nat.cast_one (R := ZMod p), ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) hjp
    have hc := congrArg (fun t : ℕ => (t : ZMod p)) (Nat.succ_mul_centralBinom_succ j)
    have hb := congrArg (fun t : ℕ => (t : ZMod p)) (Nat.choose_succ_right_eq (p/2) j)
    push_cast [Nat.cast_sub hj'] at hc hb
    rw [ih hj'] at hc
    apply mul_left_cancel₀ hj0
    rw [pow_succ]
    linear_combination hc + (4 * (-4)^j) * hb +
      (2 * (-4)^j * ((p/2).choose j : ZMod p)) * hzero

private theorem legendre_neg_seven {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    legendreSym p (-7) = legendreSym 7 p := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two (p := p) Fact.out).2 hp
  rw [legendreSym.at_neg hp 7, ZMod.χ₄_eq_neg_one_pow hodd,
    legendreSym.quadratic_reciprocity' (p := p) (q := 7) hp (by decide)]
  rw [mul_comm (p / 2) (7 / 2), pow_mul]
  norm_num

/-- The unweighted central-binomial term appearing in Sun's weighted congruence. -/
theorem centralBinom_sixteen (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    (∑ j ∈ Finset.range ((p - 1)/2 + 1), (16 : ℤ)^j * ((2*j).choose j : ℤ)) ≡
      legendreSym 7 p [ZMOD (p : ℤ)] := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp2 : p ≠ 2 := by omega
  have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two (p := p) Fact.out).2 hp2
  rw [show (p - 1)/2 = p/2 by omega, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  have hthree : ((3 : ℤ) : ZMod p) ≠ 0 := by
    have hn := (ZMod.natCast_eq_zero_iff 3 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega) : ¬ p ∣ 3)
    simpa only [Nat.cast_ofNat, Int.cast_ofNat] using hn
  calc
    ∑ j ∈ Finset.range (p/2+1), (16 : ZMod p)^j * ((2*j).choose j : ZMod p)
        = ∑ j ∈ Finset.range (p/2+1), (-64 : ZMod p)^j * ((p/2).choose j : ZMod p) := by
          apply Finset.sum_congr rfl
          intro j hj
          have h := centralBinom_mod (p := p) hp2 (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
          rw [← Nat.centralBinom_eq_two_mul_choose, h, ← mul_assoc, ← mul_pow]
          norm_num
    _ = (-63 : ZMod p)^(p/2) := by
      simpa [show (-64 : ZMod p) + 1 = -63 by norm_num] using (add_pow (-64 : ZMod p) 1 (p/2)).symm
    _ = legendreSym p (-63) := by simpa using (legendreSym.eq_pow p (-63)).symm
    _ = (legendreSym 7 p : ZMod p) := by
      rw [show (-63 : ℤ) = -7 * 3^2 by norm_num, legendreSym.mul,
        legendreSym.sq_one' p hthree, mul_one, legendre_neg_seven hp2]

end SunSplit

namespace SunSmall

theorem weighted_small (p : ℕ) (h : p = 2 ∨ p = 3) :
    letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    (∑ k ∈ Finset.range p, (42*(k:ℤ)+37)*(-1:ℤ)^k*OeisA179537.a k) ≡
      (p:ℤ)*(21*legendreSym 7 p + 16) [ZMOD (p:ℤ)^2] := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  rcases h with rfl | rfl <;>
    norm_num [Finset.sum_range_succ, OeisA179537.a_0, OeisA179537.a_1, OeisA179537.a_2, Int.ModEq]

end SunSmall

namespace SunCombination

open Finset SunAlternating SunWeightedColumn

private theorem at_column {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (j : ℕ) (hj : 2*j < p) :
    ((-16:ZMod (p^2))^j * ((2*j).choose j : ZMod (p^2))^2) *
      (∑ n ∈ range p, ((42*(n:ZMod (p^2))+37)*(-1)^n)*(n.choose (2*j):ZMod (p^2))^2) =
    2*((21*(j:ZMod (p^2))+8)*((2*j).choose j:ZMod (p^2))^3) +
      (21*(p:ZMod (p^2)))*((16:ZMod (p^2))^j * ((2*j).choose j:ZMod (p^2))) := by
  let B : ZMod (p^2) := (2*j).choose j
  let S := altColumn (ZMod (p^2)) p (2*j)
  let U := column (ZMod (p^2)) p (2*j)
  have he :
      (∑ n ∈ range p, ((42*(n:ZMod (p^2))+37)*(-1)^n)*(n.choose (2*j):ZMod (p^2))^2) =
        21*U + (42*(j:ZMod (p^2))+16)*S := by
    simp only [U,S,column,altColumn,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  rw [he]
  have hs : (-16:ZMod (p^2))^j * S = B := alternating_transform hp hp2 j hj
  have hu : B*U = (p:ZMod (p^2))*(-1)^j := transform hp hp2 j hj
  have hsign : (-16:ZMod (p^2))^j*(-1)^j = 16^j := by rw [← mul_pow]; norm_num
  change ((-16:ZMod (p^2))^j*B^2)*(21*U+(42*j+16)*S) =
    2*((21*(j:ZMod (p^2))+8)*B^3)+(21*(p:ZMod (p^2)))*(16^j*B)
  calc
    _ = 21*B*(-16:ZMod (p^2))^j*(B*U)+(42*j+16)*B^2*((-16:ZMod (p^2))^j*S) := by ring
    _ = _ := by
      rw [hu,hs]
      linear_combination 21*B*(p:ZMod (p^2))*hsign

theorem weighted_reduction {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (∑ n ∈ range p, (42*(n:ℤ)+37)*(-1)^n*OeisA179537.a n) ≡
    2*(∑ j ∈ range ((p-1)/2+1), (21*(j:ℤ)+8)*((2*j).choose j : ℤ)^3) +
    (21*(p:ℤ))*(∑ j ∈ range ((p-1)/2+1), (16:ℤ)^j*((2*j).choose j : ℤ))
      [ZMOD (p:ℤ)^2] := by
  rw [← Nat.cast_pow, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [reorder (ZMod (p^2)) p hp.pos (fun n => (42*(n:ZMod (p^2))+37)*(-1)^n)]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  apply at_column hp hp2 j
  rw [mem_range] at hj
  have := hp.pos
  omega

theorem weighted_large (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    (∑ n ∈ range p, (42*(n:ℤ)+37)*(-1)^n*OeisA179537.a n) ≡
      (p:ℤ)*(21*legendreSym 7 p+16) [ZMOD (p:ℤ)^2] := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have left := (SunWeighted.half_congr p).mul_left 2
  have right := ((SunSplit.centralBinom_sixteen p hp).mul_left' (c := (p:ℤ))).mul_left 21
  rw [← sq] at right
  have right' := right
  simp only [← mul_assoc] at right'
  have h := (weighted_reduction (Fact.out : p.Prime) (by omega)).trans (left.add right')
  convert h using 1 <;> ring

end SunCombination

theorem OMA.solution : type_of% @OeisA179537.conjecture4 := by
  intro p inst _hp7
  by_cases h : 5 ≤ p
  · exact SunCombination.weighted_large p h
  · apply SunSmall.weighted_small
    have hp : p.Prime := Fact.out
    have hp2 := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
    omega
