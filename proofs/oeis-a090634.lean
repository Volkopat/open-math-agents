import OMAStatements.S_oeis_a090634
import Mathlib

-- Problem: A090634, denominators of iterated averages of 1, 1/2, ..., 1/n.
-- Credit: @jagong-cmu
-- Proof: after m steps the j-th term is 2^(-m) * Sum_i C(m,i)/(j+i+1) (Pascal rule), and
-- Sum_i C(m,i)/(i+1) = (2^(m+1)-1)/(m+1), so F(n) = 2*(1-1/2^n)/n exactly.
namespace OMAa090634

open OMA.S_oeis_a090634 Finset

/-- The terms after `m` averaging steps: `g m j` is the `j`-th entry (from 0). -/
def g : ℕ → ℕ → ℚ
  | 0, j => 1 / ((j : ℚ) + 1)
  | m + 1, j => (g m j + g m (j + 1)) / 2

theorem avg_map (L : ℕ) (h : ℕ → ℚ) :
    avg ((List.range (L + 1)).map h) = (List.range L).map (fun j => (h j + h (j + 1)) / 2) := by
  apply List.ext_getElem
  · simp [avg]
  · intro i h1 h2
    simp [avg, List.getElem_zipWith, List.getElem_tail]

theorem iter (m L : ℕ) :
    (avg^[m]) ((List.range (L + m)).map (g 0)) = (List.range L).map (g m) := by
  induction m generalizing L with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', show L + (m + 1) = (L + 1) + m by ring, ih (L + 1),
      avg_map]
    rfl

theorem pascal_sum (m : ℕ) (f : ℕ → ℚ) :
    ∑ i ∈ range (m + 2), ((m + 1).choose i : ℚ) * f i =
      ∑ i ∈ range (m + 1), (m.choose i : ℚ) * f i +
        ∑ i ∈ range (m + 1), (m.choose i : ℚ) * f (i + 1) := by
  rw [sum_range_succ' _ (m + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, sum_add_distrib]
  rw [sum_range_succ' (fun i => (m.choose i : ℚ) * f i) m,
    sum_range_succ (fun i => (m.choose (i + 1) : ℚ) * f (i + 1)) m]
  simp [Nat.choose_succ_self]
  ring

theorem g_closed (m : ℕ) : ∀ j : ℕ,
    g m j = (∑ i ∈ range (m + 1), (m.choose i : ℚ) * (1 / ((j : ℚ) + i + 1))) / 2 ^ m := by
  induction m with
  | zero =>
    intro j
    simp [g]
  | succ m ih =>
    intro j
    rw [g, ih j, ih (j + 1), pascal_sum m (fun i => 1 / ((j : ℚ) + i + 1))]
    push_cast
    rw [pow_succ]
    have e : ∀ i : ℕ, (1 : ℚ) / ((j : ℚ) + 1 + i + 1) = 1 / ((j : ℚ) + ((i : ℚ) + 1) + 1) := by
      intro i
      ring_nf
    simp only [e]
    field_simp

theorem sum_choose_div (m : ℕ) :
    ∑ i ∈ range (m + 1), (m.choose i : ℚ) * (1 / ((0 : ℕ) + (i : ℚ) + 1)) =
      (2 ^ (m + 1) - 1) / ((m : ℚ) + 1) := by
  have key : ∀ i ∈ range (m + 1),
      (m.choose i : ℚ) * (1 / ((0 : ℕ) + (i : ℚ) + 1)) =
        ((m + 1).choose (i + 1) : ℚ) / ((m : ℚ) + 1) := by
    intro i _
    have h := Nat.add_one_mul_choose_eq m i
    have hq : ((m : ℚ) + 1) * (m.choose i : ℚ) = ((m + 1).choose (i + 1) : ℚ) * ((i : ℚ) + 1) := by
      exact_mod_cast h
    have h1 : (0 : ℚ) < (i : ℚ) + 1 := by positivity
    have h2 : (0 : ℚ) < (m : ℚ) + 1 := by positivity
    field_simp
    push_cast
    linarith [hq]
  rw [sum_congr rfl key, ← sum_div]
  congr 1
  have hs := Nat.sum_range_choose (m + 1)
  rw [sum_range_succ'] at hs
  simp only [Nat.choose_zero_right] at hs
  have hq : (∑ i ∈ range (m + 1), ((m + 1).choose (i + 1) : ℚ)) + 1 = 2 ^ (m + 1) := by
    exact_mod_cast hs
  linarith

theorem F_eq (n : ℕ) (hn : 1 ≤ n) : F n = 2 * (1 - 1 / 2 ^ n) / (n : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hs : start (m + 1) = (List.range (1 + m)).map (g 0) := by
    rw [show 1 + m = m + 1 by ring, start]
    apply List.map_congr_left
    intro k _
    simp [g]
  rw [F, show m + 1 - 1 = m by omega, hs, iter m 1]
  simp only [List.range_one, List.map_cons, List.map_nil, List.headD_cons]
  rw [g_closed, sum_choose_div]
  push_cast
  have h2 : (0 : ℚ) < (m : ℚ) + 1 := by positivity
  field_simp
  ring

theorem sol : ∀ n : ℕ, 1 ≤ n → a n = (2 * (1 - 1 / 2 ^ n) / (n : ℚ)).den := by
  intro n hn
  rw [a, F_eq n hn]

end OMAa090634

theorem OMA.solution : type_of% @OMA.S_oeis_a090634.main :=
  OMAa090634.sol
