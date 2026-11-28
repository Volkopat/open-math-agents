import OMAStatements.S_mo_165884

-- uses note #92566
-- Complete companion disproof by @Gh0stBlock, published in statement PR #20704.
-- Source commit b5f5cfe1de1420da9586fbdc363a1af59661b86b, 2026-11-28.
-- Rechecked and assembled for the registered statement, with no novelty claim.
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Speyer

def norm (u v : ℤ) : ℤ := u ^ 2 + v ^ 2

/-- Coordinates of an integer point after multiplication by the conjugate of u + vi. -/
def inTriangle (u v : ℤ) (p : ℤ × ℤ) : Prop :=
  0 ≤ u * p.1 + v * p.2 ∧ 0 ≤ u * p.2 - v * p.1 ∧
    2 * ((u * p.1 + v * p.2) + (u * p.2 - v * p.1)) ≤ norm u v

/-- The closed image of the triangle with vertices (0,0), (1/2,0), (0,1/2). -/
def inClosedDilation (u v : ℤ) (p : ℤ × ℤ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 / 2 ∧
    (p.1 : ℝ) = (u : ℝ) * a - (v : ℝ) * b ∧
    (p.2 : ℝ) = (v : ℝ) * a + (u : ℝ) * b

theorem inTriangle_iff_closed {u v : ℤ} (hz : u ≠ 0 ∨ v ≠ 0) (p : ℤ × ℤ) :
    inTriangle u v p ↔ inClosedDilation u v p := by
  have hn : 0 < norm u v := by
    rcases hz with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg v)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg u) (sq_pos_of_ne_zero h)
  have hnr : (0 : ℝ) < (norm u v : ℝ) := by exact_mod_cast hn
  constructor
  · rintro ⟨hS, hT, hsum⟩
    let a : ℝ := ((u * p.1 + v * p.2 : ℤ) : ℝ) / (norm u v : ℝ)
    let b : ℝ := ((u * p.2 - v * p.1 : ℤ) : ℝ) / (norm u v : ℝ)
    refine ⟨a, b, div_nonneg (by exact_mod_cast hS) hnr.le,
      div_nonneg (by exact_mod_cast hT) hnr.le, ?_, ?_, ?_⟩
    · dsimp [a, b]
      rw [← add_div, div_le_iff₀ hnr]
      have h := Int.cast_le (R := ℝ).2 hsum
      push_cast at h ⊢
      linarith only [h]
    · dsimp [a, b]
      field_simp [hnr.ne']
      push_cast
      unfold norm
      push_cast
      ring
    · dsimp [a, b]
      field_simp [hnr.ne']
      push_cast
      unfold norm
      push_cast
      ring
  · rintro ⟨a, b, ha, hb, hab, hx, hy⟩
    have hS : ((u * p.1 + v * p.2 : ℤ) : ℝ) = (norm u v : ℝ) * a := by
      push_cast [norm]
      rw [hx, hy]
      ring
    have hT : ((u * p.2 - v * p.1 : ℤ) : ℝ) = (norm u v : ℝ) * b := by
      push_cast [norm]
      rw [hx, hy]
      ring
    refine ⟨?_, ?_, ?_⟩
    · exact_mod_cast (show (0 : ℝ) ≤ ((u * p.1 + v * p.2 : ℤ) : ℝ) by
        rw [hS]; exact mul_nonneg hnr.le ha)
    · exact_mod_cast (show (0 : ℝ) ≤ ((u * p.2 - v * p.1 : ℤ) : ℝ) by
        rw [hT]; exact mul_nonneg hnr.le hb)
    · have h := mul_le_mul_of_nonneg_left hab hnr.le
      exact_mod_cast (show ((2 * ((u * p.1 + v * p.2) +
        (u * p.2 - v * p.1)) : ℤ) : ℝ) ≤ (norm u v : ℝ) by
          push_cast only [Int.cast_mul, Int.cast_add, Int.cast_ofNat] at *
          nlinarith only [h, hS, hT])

noncomputable def count (u v : ℤ) : ℕ := Nat.card {p : ℤ × ℤ // inTriangle u v p}

/-- A finite row encoding for an integer lattice region with closed row intervals. -/
private theorem count_by_rows {u v : ℤ} (n : ℕ) (lo hi : ℕ → ℤ)
    (h : ∀ x y : ℤ, inTriangle u v (x, y) ↔
      0 ≤ y ∧ y ≤ n ∧ lo y.toNat ≤ x ∧ x ≤ hi y.toNat) :
    count u v = ∑ j ∈ Finset.range (n + 1), (hi j - lo j + 1).toNat := by
  let width (j : ℕ) := (hi j - lo j + 1).toNat
  let encode (q : Σ j : Fin (n + 1), Fin (width j.val)) :
      {p : ℤ × ℤ // inTriangle u v p} :=
    ⟨(lo q.1.val + q.2.val, q.1.val), (h _ _).2 (by
      have hy := q.1.isLt
      have hx := q.2.isLt
      dsimp [width] at hx
      simp only [Int.toNat_natCast]
      omega)⟩
  have he : Function.Bijective encode := by
    constructor
    · rintro ⟨j, r⟩ ⟨l, s⟩ hEq
      have hy := congrArg (fun p : {p // inTriangle u v p} => p.val.2) hEq
      change (j.val : ℤ) = (l.val : ℤ) at hy
      have hj : j = l := Fin.ext (by omega)
      subst l
      have hx := congrArg (fun p : {p // inTriangle u v p} => p.val.1) hEq
      change lo j.val + (r.val : ℤ) = lo j.val + (s.val : ℤ) at hx
      have hr : r = s := Fin.ext (by omega)
      subst s
      rfl
    · rintro ⟨⟨x, y⟩, hp⟩
      obtain ⟨hy0, hy1, hlo, hhi⟩ := (h x y).1 hp
      let j : Fin (n + 1) := ⟨y.toNat, by omega⟩
      let r : Fin (width j.val) := ⟨(x - lo y.toNat).toNat, by dsimp [width, j]; omega⟩
      refine ⟨⟨j, r⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
      · change lo y.toNat + ((x - lo y.toNat).toNat : ℤ) = x
        omega
      · exact Int.toNat_of_nonneg hy0
  rw [count, ← Nat.card_congr (Equiv.ofBijective encode he), Nat.card_sigma]
  simp only [Nat.card_fin, width]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (hi j - lo j + 1).toNat) (n + 1)

private theorem y_bounds {u v x y : ℤ} (hu : 0 < u) (hv : 0 ≤ v) (hvu : v ≤ u)
    (h : inTriangle u v (x,y)) : 0 ≤ y ∧ 2 * y ≤ u := by
  obtain ⟨hS, hT, hsum⟩ := h
  let S := u*x + v*y
  let T := u*y - v*x
  change 0 ≤ S at hS
  change 0 ≤ T at hT
  change 2 * (S + T) ≤ norm u v at hsum
  have hn : 0 < norm u v := add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hu.ne') (sq_nonneg v)
  have hlow : 0 ≤ norm u v * y := calc
    0 ≤ v*S + u*T := add_nonneg (mul_nonneg hv hS) (mul_nonneg hu.le hT)
    _ = _ := by dsimp [norm, S, T]; ring
  have hhigh : 0 ≤ norm u v * (u - 2*y) := calc
    0 ≤ u * (norm u v - 2 * (S + T)) + 2 * (u-v) * S :=
      add_nonneg (mul_nonneg hu.le (sub_nonneg.mpr hsum))
        (mul_nonneg (by omega) hS)
    _ = _ := by dsimp [norm, S, T]; ring
  exact ⟨nonneg_of_mul_nonneg_right hlow hn,
    sub_nonneg.mp (nonneg_of_mul_nonneg_right hhigh hn)⟩

private def diagLo (y : ℕ) : ℤ := if y = 0 then 0 else 1 - y

private theorem diagonal_rows (k : ℕ) (hk : 0 < k) (x y : ℤ) :
    inTriangle (2 * (k : ℤ) + 1) (2 * (k : ℤ)) (x, y) ↔
      0 ≤ y ∧ y ≤ k ∧ diagLo y.toNat ≤ x ∧ x ≤ y.toNat := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  constructor
  · intro h
    obtain ⟨hy, hy'⟩ := y_bounds (by omega) (by omega) (by omega) h
    have hyk : y ≤ (k : ℤ) := by omega
    obtain ⟨hS, hT, _⟩ := h
    refine ⟨hy, hyk, ?_, ?_⟩
    · by_cases hzero : y = 0
      · subst y
        rw [mul_zero, add_zero] at hS
        have hx : 0 ≤ x := nonneg_of_mul_nonneg_right hS (by omega)
        simpa [diagLo] using hx
      · have hx : 1 - y ≤ x := by
          by_contra! H
          have hp := mul_nonneg (show 0 ≤ 2 * (k : ℤ) + 1 by omega)
            (show 0 ≤ -(x + y) by omega)
          nlinarith only [hS, hp, show 0 < y by omega]
        simpa [diagLo, show y.toNat ≠ 0 by omega, Int.toNat_of_nonneg hy] using hx
    · have hx : x ≤ y := by
        by_contra! H
        have hp := mul_nonneg (show 0 ≤ 2 * (k : ℤ) by omega)
          (show 0 ≤ x - y - 1 by omega)
        nlinarith only [hT, hp, hyk, hk']
      simpa [Int.toNat_of_nonneg hy] using hx
  · rintro ⟨hy, hyk, hlo, hhi⟩
    rw [Int.toNat_of_nonneg hy] at hhi
    by_cases hzero : y = 0
    · subst y
      simp [diagLo] at hlo hhi
      have hx : x = 0 := by omega
      subst x
      simp [inTriangle, norm, add_nonneg, sq_nonneg]
    · have hxy : 1 - y ≤ x := by
        simpa [diagLo, show y.toNat ≠ 0 by omega, Int.toNat_of_nonneg hy] using hlo
      refine ⟨?_, ?_, ?_⟩
      · have hp := mul_nonneg (show 0 ≤ 2 * (k : ℤ) + 1 by omega)
          (show 0 ≤ x + y - 1 by omega)
        change 0 ≤ (2 * (k : ℤ) + 1) * x + 2 * k * y
        nlinarith only [hp, hyk, hk']
      · have hp := mul_nonneg (show 0 ≤ 2 * (k : ℤ) by omega) (show 0 ≤ y - x by omega)
        change 0 ≤ (2 * (k : ℤ) + 1) * y - 2 * k * x
        nlinarith only [hp, hy]
      · have hp := mul_nonneg (show 0 ≤ 8 * (k : ℤ) + 4 by omega) (show 0 ≤ k - y by omega)
        dsimp [norm]
        nlinarith only [hp, hhi, hk']

private theorem integer_cut {a b x t : ℤ} (ha : 0 < a)
    (hlo : a*t ≤ b) (hhi : b < a*(t+1)) : a*x ≤ b ↔ x ≤ t := by
  constructor
  · intro hx
    by_contra! hxt
    have := mul_le_mul_of_nonneg_left (show t + 1 ≤ x by omega) ha.le
    omega
  · intro hx
    exact (mul_le_mul_of_nonneg_left hx ha.le).trans hlo

private def steepLo (y : ℕ) : ℤ := if y = 0 then 0 else 1 - ((y + 1) / 2 : ℕ)

private def steepHi (k y : ℕ) : ℤ :=
  if y ≤ k then 2 * y
  else 2 * (k : ℤ) - 3 * ((y : ℤ) - k) + if 2*k+1 ≤ 4*(y-k) then 1 else 0

private theorem steep_rows (k : ℕ) (hk : 0 < k) (x y : ℤ) :
    inTriangle (4 * (k : ℤ) + 1) (2 * (k : ℤ)) (x, y) ↔
      0 ≤ y ∧ y ≤ 2 * (k : ℤ) ∧ steepLo y.toNat ≤ x ∧ x ≤ steepHi k y.toNat := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hy_bounds (ht : inTriangle (4 * (k : ℤ) + 1) (2 * (k : ℤ)) (x,y)) :
      0 ≤ y ∧ y ≤ 2 * (k : ℤ) := by
    obtain ⟨h₁, h₂⟩ := y_bounds (by omega) (by omega) (by omega) ht
    omega
  have row (hy : 0 ≤ y) (hyk : y ≤ 2 * (k : ℤ)) :
      inTriangle (4 * (k : ℤ) + 1) (2 * (k : ℤ)) (x,y) ↔
        steepLo y.toNat ≤ x ∧ x ≤ steepHi k y.toNat := by
    have hry : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy
    let K : ℤ := k
    have hK : 0 < K := hk'
    change (0 ≤ (4*K+1)*x + 2*K*y ∧ 0 ≤ (4*K+1)*y - 2*K*x ∧
      2*((4*K+1)*x + 2*K*y + ((4*K+1)*y - 2*K*x)) ≤ norm (4*K+1) (2*K)) ↔ _
    have hleft : 0 ≤ (4*K+1)*x + 2*K*y ↔ steepLo y.toNat ≤ x := by
      by_cases h0 : y = 0
      · simp [h0, steepLo, show 0 < 4*K+1 by omega]
      · let l : ℤ := ((y.toNat+1)/2 : ℕ)
        have hl : 0 < l := by dsimp [l]; omega
        have hlk : l ≤ K := by dsimp [l, K]; omega
        have he0 : 0 ≤ 2*l-y := by dsimp [l]; omega
        have he1 : 2*l-y ≤ 1 := by dsimp [l]; omega
        have hgood : (4*K+1)*(l-1) ≤ 2*K*y := by
          have h := mul_nonneg hK.le (show 0 ≤ 1-(2*l-y) by omega)
          nlinarith only [h, hlk, hK]
        have hbad : 2*K*y < (4*K+1)*((l-1)+1) := by
          have h := mul_nonneg hK.le he0
          nlinarith only [h, hl]
        have cut := integer_cut (x := -x) (show 0 < 4*K+1 by omega) hgood hbad
        have hlo : steepLo y.toNat = 1 - l := by
          simp [steepLo, l, show y.toNat ≠ 0 by omega]
        rw [hlo]
        constructor
        · intro hx
          have := cut.mp (by rw [mul_neg]; linarith only [hx])
          omega
        · intro hx
          have := cut.mpr (show -x ≤ l-1 by omega)
          rw [mul_neg] at this
          omega
    rw [hleft, and_congr_right_iff]
    intro hlo
    have third : 2*((4*K+1)*x+2*K*y+((4*K+1)*y-2*K*x)) ≤ norm (4*K+1) (2*K) ↔
        (4*K+2)*x ≤ 20*K^2+8*K+1-(12*K+2)*y := by
      unfold norm
      constructor <;> intro h <;> linarith only [h]
    rw [third]
    by_cases hlow : y ≤ K
    · have hr : steepHi k y.toNat = 2*y := by
        have hc : y.toNat ≤ k := by dsimp [K] at hlow; omega
        simp [steepHi, hc, hry]
      rw [hr]
      have cut := integer_cut (x := x) (show 0 < 2*K by omega)
        (show (2*K)*(2*y) ≤ (4*K+1)*y by nlinarith only [hy])
        (show (4*K+1)*y < (2*K)*(2*y+1) by nlinarith only [hlow, hK])
      constructor
      · intro h
        exact cut.mp (sub_nonneg.mp h.1)
      · intro hx
        refine ⟨sub_nonneg.mpr (cut.mpr hx), ?_⟩
        have h₁ := mul_le_mul_of_nonneg_left hx (show 0 ≤ 4*K+2 by omega)
        have h₂ := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 20*K+6 by omega)
        nlinarith only [h₁, h₂, hK]
    · let r := y-K
      have hr1 : 1 ≤ r := by dsimp [r]; omega
      have hrk : r ≤ K := by dsimp [r, K] at *; omega
      let e : ℤ := if 2*K+1 ≤ 4*r then 1 else 0
      have hhi : steepHi k y.toNat = 2*K-3*r+e := by
        have hp : ¬ y.toNat ≤ k := by dsimp [K] at hlow; omega
        have hc : 2*k+1 ≤ 4*(y.toNat-k) ↔ 2*K+1 ≤ 4*r := by dsimp [K, r]; omega
        simp [steepHi, hp, hry, K, r, e, hc]
      rw [hhi]
      have he : 0 ≤ e ∧ e ≤ 1 := by dsimp [e]; split <;> omega
      have cut := integer_cut (x := x) (show 0 < 4*K+2 by omega)
        (show (4*K+2)*(2*K-3*r+e) ≤ 20*K^2+8*K+1-(12*K+2)*y by
          have hy' : y = K+r := by dsimp [r]; ring
          rw [hy']
          dsimp [e]
          split <;> rename_i hh <;> nlinarith only [hh, hr1, hK])
        (show 20*K^2+8*K+1-(12*K+2)*y < (4*K+2)*(2*K-3*r+e+1) by
          have hy' : y = K+r := by dsimp [r]; ring
          rw [hy']
          dsimp [e]
          split <;> rename_i hh <;> nlinarith only [hh, hrk, hK])
      constructor
      · intro h
        exact cut.mp h.2
      · intro hx
        refine ⟨?_, cut.mpr hx⟩
        have hxy : x ≤ 2*y := by dsimp [r] at *; omega
        have h := mul_nonneg (show 0 ≤ 2*K by omega) (show 0 ≤ 2*y-x by omega)
        nlinarith only [h, hy]
  constructor
  · intro h
    obtain ⟨hy, hyk⟩ := hy_bounds h
    exact ⟨hy, hyk, (row hy hyk).mp h⟩
  · rintro ⟨hy, hyk, hrow⟩
    exact (row hy hyk).mpr hrow

private theorem count_one : count 1 0 = 1 := by
  rw [count_by_rows 0 (fun _ => 0) (fun _ => 0)]
  · decide
  · intro x y
    simp [inTriangle, norm]
    omega

private theorem count_conj (u v : ℤ) : count u (-v) = count u v := by
  have swapIn (x y : ℤ) : inTriangle u (-v) (x,y) ↔ inTriangle u v (y,x) := by
    simp only [inTriangle, norm]
    constructor <;> rintro ⟨h₁,h₂,h₃⟩ <;> refine ⟨?_,?_,?_⟩ <;>
      linarith only [h₁,h₂,h₃]
  exact Nat.card_congr
    { toFun := fun p => ⟨(p.val.2, p.val.1), (swapIn _ _).mp p.property⟩
      invFun := fun p => ⟨(p.val.2, p.val.1), (swapIn _ _).mpr p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem sum_twice (k : ℕ) :
    (∑ j ∈ Finset.range k, 2 * ((j : ℤ) + 1)) = (k : ℤ)*(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem sum_halves (k : ℕ) :
    (∑ j ∈ Finset.range (k+k), (((j+2)/2 : ℕ) : ℤ)) = (k : ℤ)*(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k.succ+k.succ = (k+k)+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih,
      show (k+k+2)/2 = k+1 by omega, show (k+k+1+2)/2 = k+1 by omega]
    push_cast
    ring

private theorem sum_correction (h : ℕ) :
    (∑ j ∈ Finset.range (h+h), (if h ≤ j then (1 : ℤ) else 0)) = h := by
  rw [Finset.sum_range_add]
  have h₀ : (∑ j ∈ Finset.range h, (if h ≤ j then (1 : ℤ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have := Finset.mem_range.mp hj
    simp [show ¬ h ≤ j by omega]
  rw [h₀]
  simp

private theorem sum_high_linear (k : ℕ) :
    2 * (∑ j ∈ Finset.range k, (2*(k : ℤ)-3*((j : ℤ)+1))) =
      4*(k : ℤ)^2 - 3*(k : ℤ)*(k+1) := by
  have h : (∑ j ∈ Finset.range k, (2*(k : ℤ)-3*((j : ℤ)+1))) =
      2*(k : ℤ)^2 - 3 * (∑ j ∈ Finset.range k, ((j : ℤ)+1)) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    simp
    ring
  rw [h]
  have h' := sum_twice k
  rw [← Finset.mul_sum] at h'
  linarith only [h']

theorem diagonal_count (k : ℕ) (hk : 0 < k) :
    (count (2 * (k : ℤ) + 1) (2 * (k : ℤ)) : ℤ) = 1 + (k : ℤ)*(k+1) := by
  rw [count_by_rows k diagLo (fun y => (y : ℤ)) (diagonal_rows k hk),
    Finset.sum_range_succ']
  have hw (j : ℕ) : (((j+1 : ℕ) : ℤ) - diagLo (j+1) + 1).toNat = 2*(j+1) := by
    simp [diagLo]
    omega
  simp_rw [hw]
  have hzero : ((0 : ℤ) - diagLo 0 + 1).toNat = 1 := by simp [diagLo]
  simp only [Nat.cast_zero]
  rw [hzero]
  push_cast
  rw [sum_twice]
  ring

theorem steep_even_count (h : ℕ) (hh : 0 < h) :
    (count (4 * ((h+h : ℕ) : ℤ) + 1) (2 * ((h+h : ℕ) : ℤ)) : ℤ) =
      10*(h : ℤ)^2 + 2*h + 1 := by
  let k := h+h
  have hk : 0 < k := by dsimp [k]; omega
  have hr (x y : ℤ) : inTriangle (4*(k : ℤ)+1) (2*(k : ℤ)) (x,y) ↔
      0 ≤ y ∧ y ≤ (k+k : ℕ) ∧ steepLo y.toNat ≤ x ∧ x ≤ steepHi k y.toNat := by
    simpa [two_mul] using steep_rows k hk x y
  change (count (4*(k : ℤ)+1) (2*(k : ℤ)) : ℤ) = _
  rw [count_by_rows (k+k) steepLo (steepHi k) hr, Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_sum]
  have hwidth (j : ℕ) (hj : j ∈ Finset.range (k+k)) :
      (((steepHi k (j+1) - steepLo (j+1) + 1).toNat : ℕ) : ℤ) =
        (((j+2)/2 : ℕ) : ℤ) + steepHi k (j+1) := by
    have hj' := Finset.mem_range.mp hj
    have hl : steepLo (j+1) = 1 - (((j+2)/2 : ℕ) : ℤ) := by simp [steepLo, Nat.add_assoc]
    have hnonneg : 0 ≤ (((j+2)/2 : ℕ) : ℤ) + steepHi k (j+1) := by
      unfold steepHi
      split
      · positivity
      · have he : 0 ≤ (if 2*k+1 ≤ 4*(j+1-k) then (1 : ℤ) else 0) := by split <;> omega
        omega
    rw [hl, Int.toNat_of_nonneg (by omega)]
    omega
  rw [Finset.sum_congr rfl hwidth, Finset.sum_add_distrib, sum_halves]
  have hzero : (steepHi k 0 - steepLo 0 + 1).toNat = 1 := by simp [steepHi, steepLo]
  rw [hzero]
  have hsplit :
      (∑ j ∈ Finset.range (k+k), steepHi k (j+1)) =
      (∑ j ∈ Finset.range k, 2*((j : ℤ)+1)) +
      (∑ j ∈ Finset.range k, (2*(k : ℤ)-3*((j : ℤ)+1))) +
      (∑ j ∈ Finset.range (h+h), if h ≤ j then (1 : ℤ) else 0) := by
    rw [Finset.sum_range_add, add_assoc]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hle : j+1 ≤ k := by have := Finset.mem_range.mp hj; omega
      simp [steepHi, hle]
    · change _ = (∑ j ∈ Finset.range k, (2*(k : ℤ)-3*((j : ℤ)+1))) +
          (∑ j ∈ Finset.range k, if h ≤ j then (1 : ℤ) else 0)
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have hp : ¬ k+j+1 ≤ k := by omega
      have he : (2*k+1 ≤ 4*(k+j+1-k)) ↔ h ≤ j := by dsimp [k]; omega
      simp [steepHi, hp, he]
      ring
  rw [hsplit, sum_twice, sum_correction]
  have hlinear := sum_high_linear k
  have hcast : (k : ℤ) = 2*(h : ℤ) := by dsimp [k]; ring
  push_cast at *
  rw [hcast] at hlinear ⊢
  linarith only [hlinear]

/-- Number of lattice points in the closed dilated triangle. -/
noncomputable def latticeCount (u v : ℤ) : ℕ :=
  Nat.card {p : ℤ × ℤ // inClosedDilation u v p}

theorem finite_closedDilation (u v : ℤ) : Finite {p : ℤ × ℤ // inClosedDilation u v p} := by
  let B := u.natAbs + v.natAbs
  have bounds (p : {p // inClosedDilation u v p}) :
      |p.val.1| ≤ (B : ℤ) ∧ |p.val.2| ≤ (B : ℤ) := by
    obtain ⟨a,b,ha,hb,hab,hx,hy⟩ := p.property
    have hₐ : a ≤ 1 := by linarith
    have hᵦ : b ≤ 1 := by linarith
    have term (n : ℤ) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
        |(n : ℝ)*t| ≤ (n.natAbs : ℝ) := by
      rw [abs_mul, abs_of_nonneg ht]
      have hc : |(n : ℝ)| = (n.natAbs : ℝ) := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
      rw [hc]
      exact mul_le_of_le_one_right (by positivity) ht'
    have hrx : |(p.val.1 : ℝ)| ≤ ((B : ℤ) : ℝ) := by
      rw [hx]
      have h : |(u : ℝ)*a - (v : ℝ)*b| ≤ (u.natAbs : ℝ) + v.natAbs := calc
        _ ≤ |(u : ℝ)*a| + |(v : ℝ)*b| := by
          simpa only [← sub_eq_add_neg, abs_neg] using abs_add_le ((u : ℝ)*a) (-((v : ℝ)*b))
        _ ≤ _ := add_le_add (term u a ha hₐ) (term v b hb hᵦ)
      simpa [B] using h
    have hry : |(p.val.2 : ℝ)| ≤ ((B : ℤ) : ℝ) := by
      rw [hy]
      have h := (abs_add_le _ _).trans
        (add_le_add (term v a ha hₐ) (term u b hb hᵦ))
      simpa [B, add_comm] using h
    exact ⟨by exact_mod_cast hrx, by exact_mod_cast hry⟩
  let encode (p : {p // inClosedDilation u v p}) : Fin (2*B+1) × Fin (2*B+1) :=
    (⟨(p.val.1+(B : ℤ)).toNat, by have := abs_le.mp (bounds p).1; omega⟩,
     ⟨(p.val.2+(B : ℤ)).toNat, by have := abs_le.mp (bounds p).2; omega⟩)
  refine Finite.of_injective encode fun p q h => Subtype.ext (Prod.ext ?_ ?_)
  · have hh := congrArg (fun t : Fin (2*B+1) × Fin (2*B+1) => t.1.val) h
    change (p.val.1+(B : ℤ)).toNat = (q.val.1+(B : ℤ)).toNat at hh
    have hp := abs_le.mp (bounds p).1
    have hq := abs_le.mp (bounds q).1
    omega
  · have hh := congrArg (fun t : Fin (2*B+1) × Fin (2*B+1) => t.2.val) h
    change (p.val.2+(B : ℤ)).toNat = (q.val.2+(B : ℤ)).toNat at hh
    have hp := abs_le.mp (bounds p).2
    have hq := abs_le.mp (bounds q).2
    omega

private theorem latticeCount_eq_count {u v : ℤ} (hz : u ≠ 0 ∨ v ≠ 0) :
    latticeCount u v = count u v :=
  Nat.card_congr
    { toFun := fun p => ⟨p.val, (inTriangle_iff_closed hz _).mpr p.property⟩
      invFun := fun p => ⟨p.val, (inTriangle_iff_closed hz _).mp p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Bézout coprimality for the Gaussian integers r + si and u + vi. -/
def GaussianCoprime (r s u v : ℤ) : Prop :=
  ∃ a b c d : ℤ,
    r*a - s*b + u*c - v*d = 1 ∧ r*b + s*a + u*d + v*c = 0

/-- The real and imaginary parts have integer gcd one. -/
def Primitive (u v : ℤ) : Prop := ∃ a b : ℤ, u*a+v*b=1

/-- Independent periodicity in both integer inputs. -/
def Periodic₂ (M : ℕ) (f : ℤ → ℤ → ℝ) : Prop :=
  ∀ u v a b : ℤ, f (u+(M : ℤ)*a) (v+(M : ℤ)*b) = f u v

private theorem period_at_multiples (g : ℤ → ℝ) (m : ℤ) (h : ∀ u, g (u+m) = g u)
    (u j : ℤ) : g (u+m*j) = g u := by
  induction j using Int.induction_on with
  | zero => simp
  | succ j ih =>
    rw [show u+m*((j : ℤ)+1) = (u+m*j)+m by ring, h, ih]
  | pred j ih =>
    calc
      _ = g ((u+m*(-(j : ℤ)-1))+m) := (h _).symm
      _ = _ := by
        rw [show (u+m*(-(j : ℤ)-1))+m = u+m*(-(j : ℤ)) by ring]
        exact ih

theorem periodic₂_iff (M : ℕ) (f : ℤ → ℤ → ℝ) :
    Periodic₂ M f ↔
      (∀ u v, f (u+M) v = f u v) ∧ (∀ u v, f u (v+M) = f u v) := by
  constructor
  · intro h
    exact ⟨fun u v => by simpa using h u v 1 0, fun u v => by simpa using h u v 0 1⟩
  · rintro ⟨hu,hv⟩ u v a b
    rw [period_at_multiples (fun x => f x (v+(M : ℤ)*b)) M (fun x => hu x _) u a,
      period_at_multiples (f u) M (hv u) v b]

def GaussianEhrhartFormula (M : ℕ) : Prop :=
  ∃ r s : ℤ, (r ≠ 0 ∨ s ≠ 0) ∧
    ∃ a b c : ℤ → ℤ → ℝ,
      Periodic₂ M a ∧ Periodic₂ M b ∧ Periodic₂ M c ∧
      ∀ u v : ℤ, GaussianCoprime r s u v → Primitive u v →
        (latticeCount u v : ℝ) =
          (norm u v : ℝ) / 8 + a u v * (u : ℝ) + b u v * (v : ℝ) + c u v

private theorem gaussian_coprime_of_congr (r s a b : ℤ) :
    GaussianCoprime r s (1 + a*norm r s) (b*norm r s) := by
  refine ⟨-(a*r+b*s), -(b*r-a*s), 1, 0, ?_, ?_⟩ <;> unfold norm <;> ring

noncomputable def residual (u v : ℤ) : ℝ := (latticeCount u v : ℝ) - (norm u v : ℝ)/8

private theorem residual_one : residual 1 0 = 7/8 := by
  norm_num [residual, latticeCount_eq_count (u := 1) (v := 0) (by omega), count_one, norm]

private theorem residual_diagonal (k : ℕ) (hk : 0 < k) :
    residual (2*(k : ℤ)+1) (2*(k : ℤ)) = 7/8 + (k : ℝ)/2 := by
  unfold residual
  rw [latticeCount_eq_count (Or.inl (by omega))]
  have hc := congrArg (fun t : ℤ => (t : ℝ)) (diagonal_count k hk)
  simp only [norm] at *
  push_cast at hc ⊢
  rw [hc]
  ring

private theorem residual_conj (u v : ℤ) (hu : u ≠ 0) :
    residual u (-v) = residual u v := by
  simp only [residual, latticeCount_eq_count (Or.inl hu), count_conj, norm, neg_sq]

private theorem residual_steep (h : ℕ) (hh : 0 < h) :
    residual (4*((h+h : ℕ) : ℤ)+1) (2*((h+h : ℕ) : ℤ)) = 7/8 := by
  unfold residual
  rw [latticeCount_eq_count (Or.inl (by omega))]
  have hc := congrArg (fun t : ℤ => (t : ℝ)) (steep_even_count h hh)
  simp only [norm] at *
  push_cast at hc ⊢
  rw [hc]
  ring

/-- The same denominator-two triangle refutes a formula of every positive period. -/
theorem no_gaussian_ehrhart_formula (M : ℕ) (hM : 0 < M) :
    ¬ GaussianEhrhartFormula M := by
  rintro ⟨r,s,hD,a,b,c,hpa,hpb,hpc,hformula⟩
  have hn : 0 < norm r s := by
    rcases hD with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg s)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg r) (sq_pos_of_ne_zero h)
  let h := M * (norm r s).toNat
  let k := h+h
  let K : ℤ := k
  have hh : 0 < h := Nat.mul_pos hM (by omega)
  have hk : 0 < k := by dsimp [k]; omega
  have hK : 0 < K := by
    change (0 : ℤ) < (k : ℤ)
    exact_mod_cast hk
  have hcast : K = 2*(M : ℤ)*norm r s := by
    dsimp [K, k, h]
    rw [Int.toNat_of_nonneg hn.le]
    ring
  have haf (i j : ℤ) (hprim : Primitive (1+i*K) (j*K)) :
      residual (1+i*K) (j*K) =
        a 1 0 * ((1+i*K : ℤ) : ℝ) + b 1 0 * ((j*K : ℤ) : ℝ) + c 1 0 := by
    have hcop : GaussianCoprime r s (1+i*K) (j*K) := by
      convert gaussian_coprime_of_congr r s (i*2*M) (j*2*M) using 1 <;>
        rw [hcast] <;> ring
    have per (f : ℤ → ℤ → ℝ) (hf : Periodic₂ M f) : f (1+i*K) (j*K) = f 1 0 := by
      convert hf 1 0 (i*2*norm r s) (j*2*norm r s) using 2 <;> rw [hcast] <;> ring
    unfold residual
    rw [hformula _ _ hcop hprim, per a hpa, per b hpb, per c hpc]
    ring
  have ha0 := haf 0 0 (by exact ⟨1,0,by ring⟩)
  have hap := haf 2 2 (by exact ⟨1,-1,by ring⟩)
  have ham := haf 2 (-2) (by exact ⟨1,1,by ring⟩)
  have has := haf 4 2 (by exact ⟨1,-2,by ring⟩)
  have hrd := residual_diagonal k hk
  have hrs := residual_steep h hh
  change residual (2*K+1) (2*K) = 7/8 + (k : ℝ)/2 at hrd
  change residual (4*K+1) (2*K) = 7/8 at hrs
  simp only [zero_mul, add_zero, residual_one, Int.cast_one, Int.cast_zero, mul_one, mul_zero] at ha0
  rw [show 1+2*K = 2*K+1 by ring, hrd] at hap
  rw [show 1+2*K = 2*K+1 by ring, show -2*K = -(2*K) by ring,
    residual_conj _ _ (by omega), hrd] at ham
  rw [show 1+4*K = 4*K+1 by ring, hrs] at has
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hKR : (K : ℝ) = (k : ℝ) := by simp [K]
  push_cast at ha0 hap ham has
  simp only [hKR] at hap ham has
  nlinarith only [ha0, hap, ham, has, hkR]

/-- Speyer's requested period is the denominator of this triangle, namely two. -/
theorem no_denominator_two_formula : ¬ GaussianEhrhartFormula 2 :=
  no_gaussian_ehrhart_formula 2 (by decide)

end Speyer

namespace SpeyerWitness

open OMA.S_mo_165884

def region : Set Point := fun p => 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 / 2

theorem region_is_polygon : GridPolygon 2 region (1 / 8) := by
  let a : Point := (0, 0)
  let b : Point := (1 / 2, 0)
  let c : Point := (0, 1 / 2)
  have ha : onGrid 2 a := by exact ⟨0, 0, by norm_num [a], by norm_num [a]⟩
  have hb : onGrid 2 b := by exact ⟨1, 0, by norm_num [b], by norm_num [b]⟩
  have hc : onGrid 2 c := by exact ⟨0, 1, by norm_num [c], by norm_num [c]⟩
  have hd : determinant a b c = 1 / 4 := by norm_num [determinant, a, b, c]
  have hr : region = triangle a b c := by
    ext p
    change (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1/2) ↔ _
    constructor
    · rintro ⟨hx, hy, hxy⟩
      refine ⟨2*p.1, 2*p.2, by linarith, by linarith, by linarith, ?_, ?_⟩ <;>
        dsimp [a, b, c] <;> ring
    · rintro ⟨s, t, hs, ht, hst, hx, hy⟩
      dsimp [a, b, c] at hx hy
      exact ⟨by linarith, by linarith, by linarith⟩
  have hg := GridPolygon.base a b c ha hb hc (by rw [hd]; norm_num)
  rw [hd] at hg
  norm_num at hg
  rwa [hr]

theorem count_eq (u v : ℤ) :
    latticeCount region u v = Speyer.latticeCount u v := by
  have hp : inDilation region u v = Speyer.inClosedDilation u v := by
    funext p
    apply propext
    constructor
    · rintro ⟨x, y, ⟨hx, hy, hxy⟩, e, f⟩
      exact ⟨x, y, hx, hy, hxy, e, f⟩
    · rintro ⟨x, y, hx, hy, hxy, e, f⟩
      exact ⟨x, y, ⟨hx, hy, hxy⟩, e, f⟩
  unfold latticeCount Speyer.latticeCount
  rw [hp]

end SpeyerWitness

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_165884.main) := by
  intro h
  obtain ⟨r, s, hrs, a, b, c, ha, hb, hc, hf⟩ :=
    h 2 (by decide) SpeyerWitness.region (1/8) SpeyerWitness.region_is_polygon
  apply Speyer.no_denominator_two_formula
  refine ⟨r, s, hrs, a, b, c, ha, hb, hc, ?_⟩
  intro u v hg hp
  have hcount := hf u v hg hp
  rw [SpeyerWitness.count_eq] at hcount
  simpa only [Speyer.norm, div_eq_mul_inv, one_mul] using hcount
