import OMAStatements.S_oeis_a326247
import Mathlib

/-!
# A326247: proof of Barker's closed form and recurrence

Credit: @ivillar

Group the ordered pairs of edges by their right endpoints b and d. For b < d the edges (x, b),
(y, d) are neither crossing nor nesting exactly when y = x or y >= b, so the pairs with these
right endpoints number b * (1 + d - b); the case d < b is symmetric and for b = d all b^2 pairs
qualify. Hence a(n+1) = a(n) + 2 T(n) + n^2 with T(n) = Σ_{b<n} b (1 + n - b) and
6 T(n) = n (n - 1) (n + 4), which gives 12 a(n) = n (12 - 19 n + 6 n^2 + n^3) by induction; the
recurrence follows because the right side is a polynomial of degree 4.
-/

namespace PA326247
open OMA.S_oeis_a326247

/-- Pairs `(x, y)` with `x < b`, `y < d` such that `(x, b)` and `(y, d)` are neither crossing nor
nesting. -/
def H (b d : ℕ) : ℕ :=
  ∑ x ∈ Finset.range b, ∑ y ∈ Finset.range d,
    if ¬ Crossing x b y d ∧ ¬ Nesting x b y d then 1 else 0

theorem restrict (n b : ℕ) (hb : b ≤ n) (F : ℕ → ℕ) :
    ∑ x ∈ Finset.range n, (if x < b then F x else 0) = ∑ x ∈ Finset.range b, F x := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem a_sum (n : ℕ) : a n = ∑ b ∈ Finset.range n, ∑ d ∈ Finset.range n, H b d := by
  unfold a
  rw [Finset.card_filter]
  simp only [Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_range] at hb
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_range] at hd
  unfold H
  have e1 : ∀ x ∈ Finset.range n, (∑ y ∈ Finset.range n,
      (if x < b ∧ y < d ∧ ¬ Crossing x b y d ∧ ¬ Nesting x b y d then 1 else 0)) =
      if x < b then ∑ y ∈ Finset.range n,
        (if y < d then (if ¬ Crossing x b y d ∧ ¬ Nesting x b y d then 1 else 0) else 0)
      else 0 := by
    intro x _
    split_ifs with hx
    · refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> simp_all
    · simp [hx]
  rw [Finset.sum_congr rfl e1, restrict n b hb.le]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [restrict n d hd.le]

theorem H_lt (b d : ℕ) (h : b < d) : H b d = b * (1 + (d - b)) := by
  unfold H
  have key : ∀ x ∈ Finset.range b, (∑ y ∈ Finset.range d,
      (if ¬ Crossing x b y d ∧ ¬ Nesting x b y d then 1 else 0)) = 1 + (d - b) := by
    intro x hx
    rw [Finset.mem_range] at hx
    rw [← Finset.sum_range_add_sum_Ico _ h.le]
    have h1 : (∑ y ∈ Finset.range b,
        (if ¬ Crossing x b y d ∧ ¬ Nesting x b y d then 1 else 0)) = 1 := by
      rw [Finset.sum_eq_single x]
      · rw [if_pos]
        simp only [Crossing, Nesting]
        omega
      · intro y hy hyx
        rw [Finset.mem_range] at hy
        rw [if_neg]
        simp only [Crossing, Nesting]
        omega
      · intro hx'
        exact absurd (Finset.mem_range.mpr hx) hx'
    have h2 : (∑ y ∈ Finset.Ico b d,
        (if ¬ Crossing x b y d ∧ ¬ Nesting x b y d then 1 else 0)) = d - b := by
      rw [Finset.sum_congr rfl (g := fun _ => 1)]
      · simp
      · intro y hy
        rw [Finset.mem_Ico] at hy
        rw [if_pos]
        simp only [Crossing, Nesting]
        omega
    rw [h1, h2]
  rw [Finset.sum_congr rfl key]
  simp

theorem H_self (b : ℕ) : H b b = b * b := by
  unfold H
  have key : ∀ x ∈ Finset.range b, (∑ y ∈ Finset.range b,
      (if ¬ Crossing x b y b ∧ ¬ Nesting x b y b then 1 else 0)) = b := by
    intro x hx
    rw [Finset.sum_congr rfl (g := fun _ => 1)]
    · simp
    · intro y hy
      rw [Finset.mem_range] at hx hy
      rw [if_pos]
      simp only [Crossing, Nesting]
      omega
  rw [Finset.sum_congr rfl key]
  simp

theorem H_symm (b d : ℕ) : H b d = H d b := by
  unfold H
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  have e : (¬ Crossing x b y d ∧ ¬ Nesting x b y d) ↔ (¬ Crossing y d x b ∧ ¬ Nesting y d x b) := by
    simp only [Crossing, Nesting]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega
  simp only [e]

/-- `Σ_{b < n} b (1 + (n - b))`. -/
def T (n : ℕ) : ℕ := ∑ b ∈ Finset.range n, b * (1 + (n - b))

theorem S_succ (n : ℕ) :
    ∑ b ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1), H b d =
      ∑ b ∈ Finset.range n, ∑ d ∈ Finset.range n, H b d + 2 * T n + n * n := by
  rw [Finset.sum_range_succ, Finset.sum_congr rfl fun b _ => Finset.sum_range_succ _ _,
    Finset.sum_add_distrib, Finset.sum_range_succ, H_self]
  have e1 : ∑ b ∈ Finset.range n, H b n = T n :=
    Finset.sum_congr rfl fun b hb => H_lt b n (Finset.mem_range.mp hb)
  have e2 : ∑ d ∈ Finset.range n, H n d = T n :=
    Finset.sum_congr rfl fun d hd => by rw [H_symm]; exact H_lt d n (Finset.mem_range.mp hd)
  rw [e1, e2]
  ring

theorem gauss (n : ℕ) : 2 * (∑ b ∈ Finset.range n, b) + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; nlinarith [ih]

theorem T_succ (n : ℕ) : T (n + 1) = T n + ∑ b ∈ Finset.range n, b + 2 * n := by
  unfold T
  rw [Finset.sum_range_succ, show n * (1 + (n + 1 - n)) = 2 * n by
    rw [show n + 1 - n = 1 by omega]; ring, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_range] at hb
  rw [show n + 1 - b = (n - b) + 1 by omega]
  ring

theorem T_closed (n : ℕ) : 6 * (T n : ℤ) = n * (n - 1) * (n + 4) := by
  induction n with
  | zero => simp [T]
  | succ n ih =>
    have g := gauss n
    have g' : 2 * ((∑ b ∈ Finset.range n, b : ℕ) : ℤ) + n = n * n := by exact_mod_cast g
    rw [T_succ]
    push_cast at g' ⊢
    linear_combination ih + 3 * g'

theorem a_closed (n : ℕ) : 12 * (a n : ℤ) = n * (12 - 19 * n + 6 * n ^ 2 + n ^ 3) := by
  rw [a_sum]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [S_succ]
    push_cast at ih ⊢
    linear_combination ih + 4 * T_closed n

end PA326247

theorem OMA.solution : type_of% @OMA.S_oeis_a326247.main := by
  refine ⟨PA326247.a_closed, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega]
  have h0 := PA326247.a_closed m
  have h1 := PA326247.a_closed (m + 1)
  have h2 := PA326247.a_closed (m + 2)
  have h3 := PA326247.a_closed (m + 3)
  have h4 := PA326247.a_closed (m + 4)
  have h5 := PA326247.a_closed (m + 5)
  push_cast at h1 h2 h3 h4 h5
  have key : (12 : ℤ) * ((OMA.S_oeis_a326247.a (m + 5) : ℤ) - (5 * OMA.S_oeis_a326247.a (m + 4) -
      10 * OMA.S_oeis_a326247.a (m + 3) + 10 * OMA.S_oeis_a326247.a (m + 2) -
      5 * OMA.S_oeis_a326247.a (m + 1) + OMA.S_oeis_a326247.a m)) = 0 := by
    linear_combination h5 - 5 * h4 + 10 * h3 - 10 * h2 + 5 * h1 - h0
  omega
