import OMAStatements.S_oeis_a200431
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Linarith

/-!
# Proof of the two conjectures for OEIS A200431

Record the first and third partial sums as u and w. For fixed, distinct
nonzero u and w, the admissible middle partial sums are the intersection
of two integer intervals with zero removed. This gives 2n − |u−w| choices.
The signed endpoint sums yield the cubic, whose fourth difference vanishes.

Source: https://oeis.org/A200431
Credit: @ali-hamdan-007
-/

namespace OMA.S_oeis_a200431

/-- Admissible middle partial sums between the first and third partial sums. -/
def middle (n : ℕ) (u w : ℤ) : Finset ℤ :=
  ((Finset.Icc (u - n) (u + n)) ∩ (Finset.Icc (w - n) (w + n))).erase 0

theorem middle_valid (n : ℕ) (u v w : ℤ) :
    v ∈ middle n u w ↔ v ≠ 0 ∧
      -(n : ℤ) ≤ v - u ∧ v - u ≤ n ∧ -(n : ℤ) ≤ w - v ∧ w - v ≤ n := by
  simp only [middle, Finset.mem_erase, Finset.mem_inter, Finset.mem_Icc]
  omega

theorem middle_card (n : ℕ) (u w : ℤ)
    (hu₁ : -(n : ℤ) ≤ u) (hu₂ : u ≤ n)
    (hw₁ : -(n : ℤ) ≤ w) (hw₂ : w ≤ n) :
    ((middle n u w).card : ℤ) = 2 * (n : ℤ) - |u - w| := by
  have heq : Finset.Icc (u - n) (u + n) ∩ Finset.Icc (w - n) (w + n) =
      Finset.Icc (max u w - n) (min u w + n) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_Icc]
    omega
  have h0 : (0 : ℤ) ∈ Finset.Icc (max u w - n) (min u w + n) := by
    rw [Finset.mem_Icc]
    omega
  have hlen := Int.card_Icc_of_le (max u w - n) (min u w + n) (by omega)
  have herase := Finset.card_erase_add_one h0
  rw [middle, heq]
  rcases le_total u w with huw | hwu
  · rw [abs_of_nonpos (by omega)]
    omega
  · rw [abs_of_nonneg (by omega)]
    omega

/-- A sign and a zero-based magnitude code for a nonzero integer. -/
def signed (i : ℕ) (b : Bool) : ℤ :=
  if b then -((i : ℤ) + 1) else (i : ℤ) + 1

/-- Possible second entries of a quadruple whose first entry is `u` and last
entry is `-w`. The total-zero condition forces its third entry. -/
def seconds (n : ℕ) (u w : ℤ) : Finset ℤ :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter fun b =>
    let c := w - u - b;
    -(n : ℤ) ≤ c ∧ c ≤ n ∧
    u + b ≠ 0 ∧ b + c ≠ 0 ∧ c + (-w) ≠ 0 ∧
    u + b + c ≠ 0 ∧ b + c + (-w) ≠ 0

def weight (n : ℕ) (u w : ℤ) : ℤ :=
  if u = w then 0 else 2 * (n : ℤ) - |u - w|

theorem seconds_weight (n : ℕ) (u w : ℤ) (hu : u ≠ 0) (hw : w ≠ 0)
    (hu₁ : -(n : ℤ) ≤ u) (hu₂ : u ≤ n)
    (hw₁ : -(n : ℤ) ≤ w) (hw₂ : w ≤ n) :
    ((seconds n u w).card : ℤ) = weight n u w := by
  by_cases he : u = w
  · have empty : seconds n u w = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro b hb
      simp only [seconds, Finset.mem_filter, Finset.mem_Icc] at hb
      omega
    rw [empty, weight, if_pos he]
    rfl
  · have hcard : (seconds n u w).card = (middle n u w).card := by
      refine Finset.card_bij' (fun b _ => u + b) (fun v _ => v - u) ?_ ?_ ?_ ?_
      · intro b hb
        rw [middle_valid]
        simp only [seconds, Finset.mem_filter, Finset.mem_Icc] at hb
        omega
      · intro v hv
        rw [middle_valid] at hv
        simp only [seconds, Finset.mem_filter, Finset.mem_Icc]
        omega
      · intro b _
        omega
      · intro v _
        omega
    rw [hcard, middle_card n u w hu₁ hu₂ hw₁ hw₂, weight, if_neg he]

theorem signed_bounds {n i : ℕ} (hi : i < n) (b : Bool) :
    -(n : ℤ) ≤ signed i b ∧ signed i b ≤ n ∧ signed i b ≠ 0 := by
  cases b <;> simp only [signed, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem signed_surj {n : ℕ} {u : ℤ} (hu₁ : -(n : ℤ) ≤ u)
    (hu₂ : u ≤ n) (hu : u ≠ 0) :
    ∃ i : ℕ, i < n ∧ ∃ b : Bool, signed i b = u := by
  by_cases hneg : u < 0
  · refine ⟨(-u - 1).toNat, by omega, true, ?_⟩
    simp only [signed, ↓reduceIte]
    omega
  · refine ⟨(u - 1).toNat, by omega, false, ?_⟩
    simp only [signed, Bool.false_eq_true, ↓reduceIte]
    omega

theorem signed_inj {i j : ℕ} {a b : Bool} (h : signed i a = signed j b) :
    i = j ∧ a = b := by
  cases a <;> cases b <;>
    simp only [signed, Bool.false_eq_true, ↓reduceIte] at h <;> constructor
  all_goals first | rfl | omega

open scoped BigOperators

/-- Four choices of signs and order for unequal magnitudes of the same sign,
    and two choices of signs for magnitudes of opposite signs. -/
def total (n : ℕ) : ℤ :=
  4 * (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j,
    (2 * (n : ℤ) - (j : ℤ) + (i : ℤ))) +
  2 * (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n,
    (2 * (n : ℤ) - (j : ℤ) - (i : ℤ) - 2))

private theorem increasingRow (a : ℤ) (m : ℕ) :
    2 * (∑ i ∈ Finset.range m, (a + (i : ℤ))) =
      (m : ℤ) * (2 * a + m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linear_combination ih

private theorem decreasingRow (a : ℤ) (m : ℕ) :
    2 * (∑ i ∈ Finset.range m, (a - (i : ℤ) - 2)) =
      (m : ℤ) * (2 * a - m - 3) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linear_combination ih

private theorem triangleSum (a : ℤ) (m : ℕ) :
    6 * (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range j, (a - (j : ℤ) + (i : ℤ))) =
      (m : ℤ) * (m - 1) * (3 * a - m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linear_combination ih + 3 * increasingRow (a - m) m

private theorem rectangleSum (a : ℤ) (m n : ℕ) :
    2 * (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n, (a - (j : ℤ) - (i : ℤ) - 2)) =
      (m : ℤ) * n * (2 * a - m - n - 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linear_combination ih + decreasingRow (a - m) n

theorem total_cubic (n : ℕ) :
    3 * total n = 2 * (n : ℤ) * ((n : ℤ) - 1) * (8 * (n : ℤ) - 1) := by
  unfold total
  linear_combination 2 * triangleSum (2 * (n : ℤ)) n +
    3 * rectangleSum (2 * (n : ℤ)) n n

open Finset

/-- Split the sum of a symmetric function with zero diagonal into its two
strict triangles. The proof adds the last row and column together. -/
theorem sum_symmetric (f : ℕ → ℕ → ℤ) (hs : ∀ i j, f i j = f j i)
    (hd : ∀ i, f i i = 0) (m : ℕ) :
    (∑ j ∈ range m, ∑ i ∈ range m, f i j) =
      2 * ∑ j ∈ range m, ∑ i ∈ range j, f i j := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [sum_range_succ, sum_add_distrib, hd, add_zero]
    rw [ih]
    have hrow : (∑ j ∈ range m, f m j) = ∑ i ∈ range m, f i m :=
      sum_congr rfl fun j _ => hs m j
    rw [hrow]
    ring

open Finset

private def sameWeight (n i j : ℕ) : ℤ :=
  if i = j then 0 else 2 * (n : ℤ) - |(i : ℤ) - j|

private def oppositeWeight (n i j : ℕ) : ℤ :=
  2 * (n : ℤ) - j - i - 2

private theorem sign_weights (n i j : ℕ) (hi : i < n) (hj : j < n) :
    ((seconds n (signed i false) (signed j false)).card : ℤ) +
    ((seconds n (signed i true) (signed j true)).card : ℤ) +
    ((seconds n (signed i false) (signed j true)).card : ℤ) +
    ((seconds n (signed i true) (signed j false)).card : ℤ) =
    2 * sameWeight n i j + 2 * oppositeWeight n i j := by
  have h (s t : Bool) :
      ((seconds n (signed i s) (signed j t)).card : ℤ) = weight n (signed i s) (signed j t) :=
    seconds_weight _ _ _ (signed_bounds hi s).2.2 (signed_bounds hj t).2.2
      (signed_bounds hi s).1 (signed_bounds hi s).2.1 (signed_bounds hj t).1 (signed_bounds hj t).2.1
  rw [h false false, h true true, h false true, h true false]
  simp only [weight, signed, sameWeight, oppositeWeight, Bool.false_eq_true,
    ↓reduceIte, abs_eq_max_neg]
  split_ifs <;> omega

theorem count_eq_total (n : ℕ) :
    (∑ j ∈ range n, ∑ i ∈ range n,
      (((seconds n (signed i false) (signed j false)).card : ℤ) +
      ((seconds n (signed i true) (signed j true)).card : ℤ) +
      ((seconds n (signed i false) (signed j true)).card : ℤ) +
      ((seconds n (signed i true) (signed j false)).card : ℤ))) = total n := by
  calc
    _ = ∑ j ∈ range n, ∑ i ∈ range n,
            (2 * sameWeight n i j + 2 * oppositeWeight n i j) := by
      refine sum_congr rfl fun j hj => sum_congr rfl fun i hi => ?_
      exact sign_weights _ _ _ (mem_range.mp hi) (mem_range.mp hj)
    _ = 2 * (∑ j ∈ range n, ∑ i ∈ range n, sameWeight n i j) +
        2 * (∑ j ∈ range n, ∑ i ∈ range n, oppositeWeight n i j) := by
      simp only [sum_add_distrib, mul_sum]
    _ = total n := by
      have hsym (i j : ℕ) : sameWeight n i j = sameWeight n j i := by
        unfold sameWeight
        by_cases hij : i = j
        · subst j
          rfl
        · rw [if_neg hij, if_neg (Ne.symm hij), abs_sub_comm (i : ℤ) (j : ℤ)]
      have hdiag (i : ℕ) : sameWeight n i i = 0 := by simp [sameWeight]
      rw [sum_symmetric _ hsym hdiag n]
      have htriangle :
          (∑ j ∈ range n, ∑ i ∈ range j, sameWeight n i j) =
            ∑ j ∈ range n, ∑ i ∈ range j, (2 * (n : ℤ) - (j : ℤ) + (i : ℤ)) := by
        refine sum_congr rfl fun j _ => sum_congr rfl fun i hi => ?_
        have hij := mem_range.mp hi
        rw [sameWeight, if_neg (Nat.ne_of_lt hij), abs_of_nonpos (by omega)]
        omega
      rw [htriangle]
      unfold total oppositeWeight
      ring

private abbrev EndpointCode := (ℕ × ℕ) × (Bool × Bool)

private def endpointCodes (n : ℕ) : Finset EndpointCode :=
  (Finset.range n ×ˢ Finset.range n) ×ˢ
    ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset Bool))

private def secondChoices (n : ℕ) : Finset (Σ _ : EndpointCode, ℤ) :=
  (endpointCodes n).sigma fun ⟨⟨j, i⟩, e, f⟩ =>
    seconds n (signed i e) (signed j f)

private def recover : (Σ _ : EndpointCode, ℤ) → ℤ × ℤ × ℤ × ℤ
  | ⟨⟨⟨j,i⟩,e,f⟩,b⟩ =>
    (signed i e, b, signed j f - signed i e - b, -signed j f)

private theorem card_secondChoices (n : ℕ) :
    (secondChoices n).card = (quadruples n).card := by
  apply Finset.card_bij (fun p _ => recover p)
  · rintro ⟨⟨⟨j, i⟩, e, f⟩, b⟩ h
    rcases Finset.mem_sigma.mp h with ⟨hcodes, hb⟩
    change ((j,i),(e,f)) ∈ endpointCodes n at hcodes
    simp only [endpointCodes, Finset.mem_product, Finset.mem_range,
      Finset.mem_univ, and_true] at hcodes
    have hu := signed_bounds hcodes.2 e
    have hw := signed_bounds hcodes.1 f
    change b ∈ seconds n (signed i e) (signed j f) at hb
    simp only [seconds, Finset.mem_filter, Finset.mem_Icc] at hb
    simp only [recover, quadruples, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    omega
  · rintro ⟨⟨⟨j, i⟩, e, f⟩, b⟩ _ ⟨⟨⟨k, l⟩, g, h⟩, c⟩ _ heq
    simp only [recover, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := signed_inj heq.1
    obtain ⟨rfl, rfl⟩ := signed_inj (show signed j f = signed k h by omega)
    obtain rfl := heq.2.1
    rfl
  · rintro ⟨a, b, c, d⟩ h
    simp only [quadruples, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
    obtain ⟨i, hi, e, he⟩ := signed_surj (n := n) (u := a) (by omega) (by omega) (by omega)
    obtain ⟨j, hj, f, hf⟩ := signed_surj (n := n) (u := -d) (by omega) (by omega) (by omega)
    refine ⟨⟨((j,i),(e,f)), b⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      constructor
      · change ((j,i),(e,f)) ∈ endpointCodes n
        simp [endpointCodes, hi, hj]
      · change b ∈ seconds n (signed i e) (signed j f)
        rw [he, hf]
        simp only [seconds, Finset.mem_filter, Finset.mem_Icc]
        omega
    · simp only [recover, he, hf, neg_neg, Prod.mk.injEq, true_and, and_true]
      omega

/-- Eliminate the third entry with the total-zero constraint and enumerate
    the signs of the nonzero first and last entries. -/
theorem direct_eq_encoded (n : ℕ) :
    a n = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n,
      (((seconds n (signed i false) (signed j false)).card : ℤ) +
      ((seconds n (signed i true) (signed j true)).card : ℤ) +
      ((seconds n (signed i false) (signed j true)).card : ℤ) +
      ((seconds n (signed i true) (signed j false)).card : ℤ)) := by
  rw [a, ← card_secondChoices]
  simp only [secondChoices, Finset.card_sigma, endpointCodes, Finset.sum_product,
    Fintype.sum_bool, Nat.cast_sum, Nat.cast_add]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

open PowerSeries

/-- The cubic count implies both of Barker's formulas, with zero constant term. -/
theorem of_cubic (a : ℕ → ℤ)
    (hc : ∀ n : ℕ, 3 * a n = 2 * (n : ℤ) * ((n : ℤ) - 1) * (8 * (n : ℤ) - 1)) :
    (mk a * (1 - X)^4 = 4 * X^2 * (5 + 3 * X)) ∧
    (∀ n : ℕ, 4 < n →
      a n = 4 * a (n-1) - 6 * a (n-2) + 4 * a (n-3) - a (n-4)) := by
  have hdiff (i : ℕ) :
      a (i+4) - 4*a (i+3) + 6*a (i+2) - 4*a (i+1) + a i = 0 := by
    have h4 := hc (i+4)
    have h3 := hc (i+3)
    have h2 := hc (i+2)
    have h1 := hc (i+1)
    push_cast at h4 h3 h2 h1
    linarith only [h4, h3, h2, h1, hc i]
  constructor
  · have expandLeft :
        mk a * (1-X)^4 = mk a - C (4:ℤ) * (mk a * X^1) +
          C (6:ℤ) * (mk a * X^2) - C (4:ℤ) * (mk a * X^3) + mk a * X^4 := by
      simp only [map_ofNat]
      ring
    have expandRight :
        4*(X : PowerSeries ℤ)^2*(5+3*X) = C (20:ℤ)*X^2+C (12:ℤ)*X^3 := by
      simp only [map_ofNat]
      ring
    rw [expandLeft, expandRight]
    apply PowerSeries.ext
    intro n
    simp only [map_add, map_sub]
    rw [coeff_C_mul_X_pow (20 : ℤ) 2 n, coeff_C_mul_X_pow (12 : ℤ) 3 n]
    simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have a0 := hc 0
    have a1 := hc 1
    have a2 := hc 2
    have a3 := hc 3
    norm_num at a0 a1 a2 a3
    match n with
    | 0 | 1 | 2 | 3 =>
      norm_num
      omega
    | i+4 =>
      simp (disch := omega) [show i+4-1=i+3 by omega, show i+4-2=i+2 by omega,
        show i+4-3=i+1 by omega, show i+4-4=i by omega]
      exact hdiff i
  · intro n hn
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = i+4 := ⟨n-4, by omega⟩
    simp only [show i+4-1=i+3 by omega, show i+4-2=i+2 by omega,
      show i+4-3=i+1 by omega, show i+4-4=i by omega]
    linarith only [hdiff i]

/-- Closed form with denominators cleared. -/
theorem count_cubic (n : ℕ) :
    3 * a n = 2 * (n : ℤ) * ((n : ℤ) - 1) * (8 * (n : ℤ) - 1) := by
  rw [direct_eq_encoded, count_eq_total, total_cubic]

end OMA.S_oeis_a200431

theorem OMA.solution : type_of% @OMA.S_oeis_a200431.main := by
  exact OMA.S_oeis_a200431.of_cubic _ OMA.S_oeis_a200431.count_cubic
