import OMAStatements.S_oeis_a227017
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat

/-!
# Corrected formulas for OEIS A227017

The midpoint of a block bounds its harmonic mean within half a unit. This
determines the integer floor, the exact starting index of the recurrence, and
the coefficients of the printed generating function at the sequence's offset.
Source: https://oeis.org/A227017
Credit: @ali-hamdan-007
-/

open OMA.S_oeis_a227017

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a227017.main) := by
  intro h
  have actual : a 2 = 3 := by decide +kernel
  have predicted := h.1 2 (by decide)
  rw [actual] at predicted
  exact (by decide : ¬ ((4 : ℤ) * 3 = 1 - (-1 : ℤ)^2 + 4 * 2 + 6 * 2^2)) predicted

namespace A227017Bounds

def midpoint (L : ℕ) : ℚ := ((L : ℚ)^2 + 5)/6
def radius (L : ℕ) : ℚ := ((L : ℚ)-1)/2

private theorem centered_squares_aux (L : ℕ) (h : ℚ) :
    ∑ i ∈ Finset.range L, ((i : ℚ) - h)^2 =
      (L : ℚ)*((L:ℚ)-1)*(2*L-1)/6 - h*L*(L-1) + L*h^2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih, Nat.cast_succ]; ring

private theorem centered_squares (L : ℕ) :
    ∑ i ∈ Finset.range L, ((i : ℚ) - radius L)^2 = L * ((midpoint L-1)/2) := by
  rw [centered_squares_aux, midpoint, radius]
  ring

private theorem double_recip (m t : ℚ) (hp : 0 < m+t) (hn : 0 < m-t) :
    1/(m+t) + 1/(m-t) = 2 * (m/(m^2-t^2)) := by
  rw [div_add_div 1 1 hp.ne' hn.ne', ← mul_div_assoc,
    show m^2-t^2 = (m+t)*(m-t) by ring]
  congr 1
  ring

private theorem paired (L : ℕ) (hL : 2 ≤ L) (m : ℚ) (hm : radius L < m) :
    (∑ i ∈ Finset.range L, (1:ℚ)/(m + ((i:ℚ)-radius L))) =
      ∑ i ∈ Finset.range L, m/(m^2-((i:ℚ)-radius L)^2) := by
  have hl' : 1 ≤ L := by omega
  have hr := Finset.sum_range_reflect (fun i : ℕ => (1:ℚ)/(m + ((i:ℚ)-radius L))) L
  have symm : (∑ i ∈ Finset.range L, (1:ℚ)/(m - ((i:ℚ)-radius L))) =
      ∑ i ∈ Finset.range L, (1:ℚ)/(m + ((i:ℚ)-radius L)) := by
    rw [← hr]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ L-1 := by have := Finset.mem_range.mp hi; omega
    rw [Nat.cast_sub hi', Nat.cast_sub hl']
    unfold radius
    push_cast
    ring
  have term : (∑ i ∈ Finset.range L,
      ((1:ℚ)/(m+((i:ℚ)-radius L)) + 1/(m-((i:ℚ)-radius L)))) =
      2 * ∑ i ∈ Finset.range L, m/(m^2-((i:ℚ)-radius L)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hh : (i:ℚ) ≤ (L:ℚ)-1 := by
      have hb := Finset.mem_range.mp hi
      have hcast : (i:ℚ)+1 ≤ L := by exact_mod_cast hb
      linarith
    apply double_recip
    · have : (0:ℚ) ≤ i := by positivity
      linarith
    · unfold radius at *
      linarith
  rw [Finset.sum_add_distrib, symm] at term
  linarith

/-- For a pentagonal block of length at least two, the harmonic mean
    lies strictly between its midpoint and the preceding half-integer. -/
theorem harmonic_bounds (L : ℕ) (hL : 2 ≤ L) :
    let m := midpoint L
    let S := ∑ i ∈ Finset.range L, (1 : ℚ) / (m + ((i : ℚ) - radius L))
    m - 1/2 < (L : ℚ)/S ∧ (L : ℚ)/S < m := by
  let m := midpoint L
  let h := radius L
  let D := m^2 - h^2
  let t (i : ℕ) : ℚ := (i:ℚ) - h
  let S := ∑ i ∈ Finset.range L, (1:ℚ) / (m + t i)
  let E := ∑ i ∈ Finset.range L, (t i)^2/(m^2-(t i)^2)
  change m - 1/2 < (L:ℚ)/S ∧ (L:ℚ)/S < m
  have hL' : (2:ℚ) ≤ L := by exact_mod_cast hL
  have hLpos : (0:ℚ) < L := by linarith
  have hh : 0 < h := by dsimp [h, radius]; linarith
  have hmh : h < m := by dsimp [m, h, midpoint, radius]; nlinarith [sq_nonneg ((L:ℚ)-2)]
  have hm1 : 1 < m := by dsimp [m, midpoint]; nlinarith [sq_nonneg ((L:ℚ)-2)]
  have hm : 0 < m := by linarith
  have hD : 0 < D := by dsimp [D]; nlinarith [mul_pos (sub_pos.mpr hmh) (show 0 < m+h by linarith)]
  have htsq (i : ℕ) (hi : i ∈ Finset.range L) : (t i)^2 ≤ h^2 := by
    have hi1 : (i:ℚ)+1 ≤ L := by exact_mod_cast (Finset.mem_range.mp hi)
    have hi0 : 0 ≤ (i:ℚ) := by positivity
    have he : -(h) ≤ t i ∧ t i ≤ h := by dsimp [t,h,radius]; constructor <;> linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr he.2) (show 0 ≤ h+t i by linarith [he.1])]
  have den (i : ℕ) (hi : i ∈ Finset.range L) : 0 < m^2-(t i)^2 := by
    dsimp [D] at hD
    linarith [htsq i hi]
  have he : m*S = L+E := by
    change m * (∑ i ∈ Finset.range L, (1:ℚ)/(m+((i:ℚ)-radius L))) = _
    rw [paired L hL m hmh, Finset.mul_sum]
    change _ = (L:ℚ) + ∑ i ∈ Finset.range L, (t i)^2/(m^2-(t i)^2)
    have hc : (L:ℚ) = ∑ _i ∈ Finset.range L, (1:ℚ) := by simp
    rw [hc, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    change m * (m/(m^2-(t i)^2)) = 1+(t i)^2/(m^2-(t i)^2)
    have hd := den i hi
    have hc : 1 + (t i)^2/(m^2-(t i)^2) =
        ((m^2-(t i)^2) + (t i)^2)/(m^2-(t i)^2) := by rw [add_div, div_self hd.ne']
    rw [hc, ← mul_div_assoc]
    congr 1
    ring
  have hepos : 0 < E := by
    apply Finset.sum_pos'
    · intro i hi
      exact div_nonneg (sq_nonneg _) (den i hi).le
    · have h0 : 0 ∈ Finset.range L := Finset.mem_range.mpr (by omega)
      refine ⟨0, h0, div_pos ?_ (den 0 h0)⟩
      dsimp [t]
      simpa using sq_pos_of_pos hh
  have hS : 0 < S := by
    apply (mul_pos_iff_of_pos_left hm).mp
    linarith
  have hupper : E ≤ L * ((m-1)/2) / D := by
    calc E ≤ ∑ i ∈ Finset.range L, (t i)^2/D := by
                apply Finset.sum_le_sum
                intro i hi
                apply div_le_div_of_nonneg_left (sq_nonneg _) hD
                dsimp [D]
                linarith [htsq i hi]
         _ = L * ((m-1)/2) / D := by
                have factor : (∑ i ∈ Finset.range L, (t i)^2 / D) =
                    (∑ i ∈ Finset.range L, (t i)^2) / D := by
                  simp only [div_eq_mul_inv, Finset.sum_mul]
                rw [factor]
                exact congrArg (fun v : ℚ => v / D) (centered_squares L)
  have margin : (2*m-1)*((m-1)/2) < D := by
    dsimp [m, h, D, midpoint, radius]
    nlinarith
  constructor
  · apply (lt_div_iff₀ hS).mpr
    have hu := (le_div_iff₀ hD).mp hupper
    have hcon : E*(2*m-1) < L := by
      apply (mul_lt_mul_iff_left₀ hD).mp
      calc E * (2*m-1) * D = (E*D)*(2*m-1) := by ring
           _ ≤ ((L:ℚ)*((m-1)/2))*(2*m-1) := mul_le_mul_of_nonneg_right hu (by linarith)
           _ < (L:ℚ)*D := by
             have := mul_lt_mul_of_pos_left margin hLpos
             linarith only [this, show ((L:ℚ)*((m-1)/2))*(2*m-1) = L*((2*m-1)*((m-1)/2)) by ring]
    have hc : (2*m) * ((m-1/2)*S) < (2*m)*L := by
      nlinarith only [hcon, congrArg (fun v : ℚ => (2*m-1)*v) he]
    exact (mul_lt_mul_iff_right₀ (show 0 < 2*m by linarith)).mp hc
  · apply (div_lt_iff₀ hS).mpr
    linarith
end A227017Bounds

namespace A227017Corrected

open OMA.S_oeis_a227017 A227017Bounds

private theorem twice_pentagonal (n : ℕ) :
    2 * pentagonal n = n * (3*n-1) := by
  have he : (n * (3*n-1)) % 2 = 0 := by
    rw [Nat.mul_mod]
    rcases (show n%2=0 ∨ n%2=1 by omega) with hh | hh
    · simp [hh]
    · have hz : (3*n-1)%2 = 0 := by omega
      simp [hz]
  unfold pentagonal
  omega

private theorem list_sum_range (f : ℕ → ℚ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- An interval between consecutive half-integers determines the floor. -/
private theorem floor_half (x : ℚ) (z : ℤ)
    (hl : (z : ℚ) / 2 < x) (hu : x < ((z : ℚ) + 1)/2) :
    x.floor = z/2 := by
  let q := z/2
  have hlow : 2*q ≤ z := by dsimp [q]; omega
  have hupp : z ≤ 2*q+1 := by dsimp [q]; omega
  have hlow' : 2*(q : ℚ) ≤ (z : ℚ) := by exact_mod_cast hlow
  have hupp' : (z : ℚ) ≤ 2*(q : ℚ)+1 := by exact_mod_cast hupp
  have L : q ≤ x.floor := Rat.le_floor_iff.mpr (by linarith)
  have U : x.floor < q+1 := Rat.floor_lt_iff.mpr (by push_cast; linarith)
  change x.floor = q
  omega

theorem corrected :
    a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
      a n = (3*(n : ℤ)^2-4*(n : ℤ)+2)/2 := by
  constructor
  · decide +kernel
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+2 := ⟨n-2, by omega⟩
    let L : ℕ := 3*k+4
    let b : ℕ := pentagonal (k+1)
    have hbefore : 2*b = (k+1)*(3*k+2) := by
      change 2*pentagonal (k+1) = _
      rw [twice_pentagonal, show 3*(k+1)-1=3*k+2 by omega]
    have hnow : 2*pentagonal (k+2) = (k+2)*(3*k+5) := by
      rw [twice_pentagonal, show 3*(k+2)-1=3*k+5 by omega]
    have hstep : pentagonal (k+2) - b = L := by
      have h : pentagonal (k+2) = b + L := by
        dsimp [L]
        nlinarith only [hbefore,hnow]
      omega
    have hbQ : 2*(b : ℚ) = ((k : ℚ)+1)*(3*(k : ℚ)+2) := by exact_mod_cast hbefore
    have hLQ : (L : ℚ) = 3*(k : ℚ)+4 := by dsimp [L]; push_cast; ring
    have halign (i : ℕ) :
        ((b+i+1 : ℕ) : ℚ) = midpoint L + ((i : ℚ) - radius L) := by
      unfold midpoint radius
      rw [hLQ]
      push_cast
      nlinarith only [hbQ]
    let S := ∑ i ∈ Finset.range L, (1 : ℚ) / (midpoint L + ((i : ℚ) - radius L))
    have hseq : a (k+2) = ((L : ℚ)/S).floor := by
      unfold a
      simp only [show k+2-1=k+1 by omega]
      change (((pentagonal (k+2)-b : ℕ) : ℚ) /
        ((List.range (pentagonal (k+2)-b)).map
          (fun i => (1 : ℚ) / ((b+i+1 : ℕ) : ℚ))).sum).floor = _
      rw [hstep, list_sum_range]
      simp only [halign, S]
    let z : ℤ := 3*((k+2 : ℕ) : ℤ)^2-4*((k+2 : ℕ) : ℤ)+2
    have hz : midpoint L = ((z : ℚ)+1)/2 := by
      unfold midpoint
      rw [hLQ]
      dsimp [z]
      push_cast
      ring
    have hL : 2 ≤ L := by dsimp [L]; omega
    obtain ⟨hlo, hhi⟩ :
        midpoint L - 1/2 < (L : ℚ)/S ∧ (L : ℚ)/S < midpoint L := harmonic_bounds L hL
    rw [hseq]
    apply floor_half _ z
    · linarith only [hlo,hz]
    · linarith only [hhi,hz]

end A227017Corrected

namespace OMA.S_oeis_a227017

/-- The recurrence already fails at the first index for which all its terms are defined. -/
theorem recurrence_first_fails : a 5 ≠ 2 * a 4 - 2 * a 2 + a 1 := by decide +kernel

/-- The corrected floor gives the printed generating function and the precise recurrence range. -/
theorem consequencesFromFloor
    (floorFormula : ∀ n : ℕ, 2 ≤ n → a n = (3 * (n : ℤ)^2 - 4 * n + 2) / 2) :
    (∀ n : ℕ, 6 ≤ n → a n = 2 * a (n-1) - 2 * a (n-3) + a (n-4)) ∧
    (∀ n : ℕ, seriesCoeff n - 2 * seriesCoeff ((n : ℤ) - 1)
      + 2 * seriesCoeff ((n : ℤ) - 3) - seriesCoeff ((n : ℤ) - 4) = numeratorCoeff n) := by
  have step (k : ℕ) (hk : 2 ≤ k) : a (k+2) = a k + 6 * (k : ℤ) + 2 := by
    rw [floorFormula (k+2) (by omega), floorFormula k hk]
    push_cast
    have h : 3*((k:ℤ)+2)^2 - 4*(k+2) + 2 =
        (3*(k:ℤ)^2 - 4*k + 2) + 2*(6*k + 2) := by ring
    rw [h]
    omega
  have recur (k : ℕ) : a (k+6) = 2 * a (k+5) - 2 * a (k+3) + a (k+2) := by
    have r₄ := step (k+4) (by omega)
    have r₃ := step (k+3) (by omega)
    have r₂ := step (k+2) (by omega)
    change a (k+6) = a (k+4) + 6 * (↑(k+4 : ℕ) : ℤ) + 2 at r₄
    change a (k+5) = a (k+3) + 6 * (↑(k+3 : ℕ) : ℤ) + 2 at r₃
    change a (k+4) = a (k+2) + 6 * (↑(k+2 : ℕ) : ℤ) + 2 at r₂
    push_cast at r₄ r₃ r₂
    omega
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+6 := ⟨n-6, by omega⟩
    simpa using recur k
  · intro n
    match n with
    | 0 | 1 | 2 | 3 | 4 => decide +kernel
    | k+5 =>
      have idx (j : ℕ) : seriesCoeff (j : ℤ) = a (j+1) := by simp [seriesCoeff]
      have h₁ : ((k+5 : ℕ) : ℤ)-1 = (↑(k+4 : ℕ) : ℤ) := by omega
      have h₃ : ((k+5 : ℕ) : ℤ)-3 = (↑(k+2 : ℕ) : ℤ) := by omega
      have h₄ : ((k+5 : ℕ) : ℤ)-4 = (↑(k+1 : ℕ) : ℤ) := by omega
      rw [h₁, h₃, h₄, idx, idx, idx, idx]
      change a (k+6) - 2*a (k+5) + 2*a (k+3) - a (k+2) = 0
      have h := recur k
      omega

end OMA.S_oeis_a227017

namespace A227017Corrected

open OMA.S_oeis_a227017

/-- The corrected formula, valid recurrence range, and published generating function
    (expressed coefficient by coefficient). -/
theorem all_formulas :
    (a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → a n = (3*(n : ℤ)^2 - 4*n + 2)/2) ∧
    (∀ n : ℕ, 6 ≤ n → a n = 2*a (n-1) - 2*a (n-3) + a (n-4)) ∧
    (∀ n : ℕ, seriesCoeff n - 2*seriesCoeff ((n : ℤ)-1)
      + 2*seriesCoeff ((n : ℤ)-3) - seriesCoeff ((n : ℤ)-4) = numeratorCoeff n) :=
  ⟨corrected, consequencesFromFloor corrected.2⟩

end A227017Corrected
