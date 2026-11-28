import OMAStatements.S_oeis_a284353
import Mathlib
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Rule 899 turns the background ON. By induction, at odd times the plane is ON except
-- the four cells at distance 1 from the origin; at even times t >= 2 it is ON except the four
-- diagonal cells (+-1, +-1). Hence a n = 2^(n+1) - 2 + (-1)^n, from which the g.f., the
-- recurrence and the binomial sum (via sum of choose and the alternating sum) follow.

namespace OMA.P_oeis_a284353
open OMA.S_oeis_a284353
open PowerSeries

def F1 (x y : ℤ) : Bool :=
  if (x = 1 ∨ x = -1) ∧ y = 0 ∨ x = 0 ∧ (y = 1 ∨ y = -1) then false else true

def F2 (x y : ℤ) : Bool :=
  if (x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1) then false else true

def F0 (x y : ℤ) : Bool := if x = 0 ∧ y = 0 then true else false

lemma state_zero (x y : ℤ) : state 899 0 x y = F0 x y := by
  simp only [state, F0]; split_ifs <;> simp_all

set_option maxHeartbeats 2000000 in
lemma state_zero_one (t : ℕ) (h : ∀ x y, state 899 t x y = F0 x y) (x y : ℤ) :
    state 899 (t+1) x y = F1 x y := by
  simp only [state, h, F0, F1]
  split_ifs <;> first | rfl | decide | (simp; done) | (exfalso; (try simp only [not_and_or, not_or, or_false, false_or, and_true, true_and, and_false, false_and, or_self, not_true, not_false_eq_true] at *); omega)

lemma state_one (x y : ℤ) : state 899 1 x y = F1 x y := state_zero_one 0 state_zero x y

set_option maxHeartbeats 2000000 in
lemma state_odd_even (t : ℕ) (h : ∀ x y, state 899 t x y = F1 x y) (x y : ℤ) :
    state 899 (t+1) x y = F2 x y := by
  simp only [state, h, F1, F2]
  split_ifs <;> first | rfl | decide | (simp; done) | (exfalso; (try simp only [not_and_or, not_or, or_false, false_or, and_true, true_and, and_false, false_and, or_self, not_true, not_false_eq_true] at *); omega)

set_option maxHeartbeats 2000000 in
lemma state_even_odd (t : ℕ) (h : ∀ x y, state 899 t x y = F2 x y) (x y : ℤ) :
    state 899 (t+1) x y = F1 x y := by
  simp only [state, h, F1, F2]
  split_ifs <;> first | rfl | decide | (simp; done) | (exfalso; (try simp only [not_and_or, not_or, or_false, false_or, and_true, true_and, and_false, false_and, or_self, not_true, not_false_eq_true] at *); omega)

lemma state_eq (k : ℕ) : (∀ x y, state 899 (2*k+1) x y = F1 x y) ∧
    (∀ x y, state 899 (2*k+2) x y = F2 x y) := by
  induction k with
  | zero =>
    refine ⟨state_one, fun x y => ?_⟩
    have h := state_odd_even 1 state_one x y
    rw [show 2*0+2 = 1+1 by rfl]
    exact h
  | succ k ih =>
    have h1 : ∀ x y, state 899 (2*(k+1)+1) x y = F1 x y := by
      intro x y
      have h := state_even_odd (2*k+2) ih.2 x y
      rw [show 2*(k+1)+1 = (2*k+2)+1 by ring]
      exact h
    refine ⟨h1, fun x y => ?_⟩
    have h := state_odd_even (2*(k+1)+1) h1 x y
    rw [show 2*(k+1)+2 = (2*(k+1)+1)+1 by ring]
    exact h

lemma geom (n : ℕ) : ∑ i ∈ Finset.range (n+1), (2:ℤ)^(n-i) = 2^(n+1) - 1 := by
  rw [← Finset.sum_range_reflect]
  have : ∀ j ∈ Finset.range (n+1), (2:ℤ)^(n - (n+1-1-j)) = 2^j := by
    intro j hj
    rw [Finset.mem_range] at hj
    congr 1; omega
  rw [Finset.sum_congr rfl this]
  clear this
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

lemma a_even (k : ℕ) : a (2*k+2) = 2^(2*k+3) - 1 := by
  unfold a digits
  rw [← geom (2*k+2)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(state_eq k).2, F2]
  split_ifs <;> first | rfl | decide | (simp; done) | (exfalso; (try simp only [not_and_or, not_or, or_false, false_or, and_true, true_and, and_false, false_and, or_self, not_true, not_false_eq_true] at *); omega)

lemma a_odd (k : ℕ) : a (2*k+1) = 2^(2*k+2) - 3 := by
  unfold a digits
  have e : ∀ i ∈ Finset.range (2*k+1+1),
      ((state 899 (2*k+1) ((i:ℤ) - ↑(2*k+1)) 0).toNat : ℤ) * 2^(2*k+1-i) =
      2^(2*k+1-i) - if i = 2*k then 2^(2*k+1-i) else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [(state_eq k).1, F1]
    push_cast
    split_ifs <;> first | rfl | decide | (simp; done) | (exfalso; (try simp only [not_and_or, not_or, or_false, false_or, and_true, true_and, and_false, false_and, or_self, not_true, not_false_eq_true] at *); omega)
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, geom, Finset.sum_ite_eq']
  rw [if_pos (by simp)]
  have : 2*k+1-2*k = 1 := by omega
  rw [this]; ring

lemma a_zero : a 0 = 1 := by
  simp [a, digits, state]

lemma a_closed (n : ℕ) : a n = 2^(n+1) - 2 + (-1)^n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · simp [a_zero]
    · have := a_even k
      have e : Even (2*k+2) := ⟨k+1, by ring⟩
      rw [show 2*(k+1) = 2*k+2 by ring, this, e.neg_one_pow]; ring
  · have e : Odd (2*k+1) := ⟨k, rfl⟩
    rw [a_odd, e.neg_one_pow]; ring

theorem main_proof :
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X)) =
      1 - X + 4 * X ^ 2) ∧
    (∀ n : ℕ, n % 2 = 0 → a n = 2 ^ (n + 1) - 1) ∧
    (∀ n : ℕ, n % 2 = 1 → a n = 2 ^ (n + 1) - 3) ∧
    (∀ n : ℕ, 2 < n → a n = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) ∧
    (∀ n : ℕ, 0 < n → a n = ∑ k ∈ Finset.range n, (n.choose k : ℤ) * (2 - (-1)^k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hp : ((1 - X) * (1 + X) * (1 - 2 * X) : PowerSeries ℤ) =
        1 - C (2:ℤ) * X^1 - X^2 + C (2:ℤ) * X^3 := by
      simp only [map_ofNat]; ring
    have hq : (1 - X + 4 * X ^ 2 : PowerSeries ℤ) = 1 - X^1 + C (4:ℤ) * X^2 := by
      simp only [map_ofNat]; ring
    rw [hp, hq]
    have hm : PowerSeries.mk a * (1 - C (2:ℤ) * X^1 - X^2 + C (2:ℤ) * X^3) =
        PowerSeries.mk a - C (2:ℤ) * (PowerSeries.mk a * X^1) - PowerSeries.mk a * X^2 +
        C (2:ℤ) * (PowerSeries.mk a * X^3) := by ring
    rw [hm]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one, coeff_X_pow, coeff_C]
    rcases n with _ | _ | _ | n
    · simp [a_zero]
    · simp [a_closed]
    · simp [a_closed]
    · simp only [show ¬ (n+3 = 0) by omega, show ¬ (n+3 = 1) by omega,
        show 1 ≤ n+3 by omega, show 2 ≤ n+3 by omega,
        show 3 ≤ n+3 by omega, if_true, if_false, a_closed]
      rw [show n+3-1 = n+2 by omega, show n+3-2 = n+1 by omega, show n+3-3 = n by omega]
      split_ifs <;> first | contradiction | omega | ring
  · intro n hn
    rw [a_closed, (Nat.even_iff.mpr hn).neg_one_pow]; ring
  · intro n hn
    rw [a_closed, (Nat.odd_iff.mpr hn).neg_one_pow]; ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m+3-1 = m+2 by omega, show m+3-2 = m+1 by omega, show m+3-3 = m by omega]
    simp only [a_closed]; ring
  · intro n hn
    have h1 := Nat.sum_range_choose n
    have h2 := Int.alternating_sum_range_choose (n := n)
    rw [if_neg (by omega)] at h2
    have h1' : ∑ k ∈ Finset.range (n+1), (n.choose k : ℤ) = 2^n := by exact_mod_cast h1
    rw [Finset.sum_range_succ] at h1' h2
    have : ∑ k ∈ Finset.range n, (n.choose k : ℤ) * (2 - (-1)^k) =
        2 * ∑ k ∈ Finset.range n, (n.choose k : ℤ) -
        ∑ k ∈ Finset.range n, (-1)^k * (n.choose k : ℤ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [this, a_closed]
    simp only [Nat.choose_self, Nat.cast_one] at h1' h2
    linear_combination (-2) * h1' + h2

end OMA.P_oeis_a284353

theorem OMA.solution : type_of% @OMA.S_oeis_a284353.main := OMA.P_oeis_a284353.main_proof
