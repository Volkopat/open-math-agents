import OMAStatements.S_oeis_a262005
import Mathlib

-- Problem: A262005: L.g.f.: log( Sum{n>=0} x^n/n! * Product{k=1..n} (k^5 + 1) ).
-- Upstream: formal-conjectures statements/oeis-a262005.lean:0 (declaration OMA.S_oeis_a262005.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)

open OMA.S_oeis_a262005 PowerSeries Finset

namespace OMA.A262005

theorem sixty : ∀ x : ZMod 60, x ^ 2 * (x - 1) * (x + 1) * (x ^ 2 + 1) = 0 := by
  decide

def P (n : ℕ) : ℤ :=
  ∏ k ∈ Finset.range n,
    (((k + 1 : ℕ) : ℤ) ^ 4 - ((k + 1 : ℕ) : ℤ) ^ 3 + ((k + 1 : ℕ) : ℤ) ^ 2 - ((k + 1 : ℕ) : ℤ) + 1)

theorem cF (m : ℕ) : coeffF m = ((m + 1 : ℕ) : ℤ) * P m := rfl

theorem P_succ (m : ℕ) : P (m + 1) = P m *
    (((m + 1 : ℕ) : ℤ) ^ 4 - ((m + 1 : ℕ) : ℤ) ^ 3 + ((m + 1 : ℕ) : ℤ) ^ 2 - ((m + 1 : ℕ) : ℤ) + 1) := by
  unfold P
  exact Finset.prod_range_succ _ m

theorem key (m : ℕ) :
    ((((m : ℤ) + 1) * coeffF (m + 1) : ℤ) : ZMod 60) = ((((m : ℤ) + 2) * coeffF m : ℤ) : ZMod 60) := by
  rw [cF, cF, P_succ]
  push_cast
  have h := sixty ((m : ZMod 60) + 1)
  linear_combination ((P m : ℤ) : ZMod 60) * h

theorem T (n : ℕ) :
    ((((n : ℤ) + 1) * coeffF (n + 1) : ℤ) : ZMod 60) =
      2 * ∑ i ∈ range (n + 1), ((coeffF i : ℤ) : ZMod 60) := by
  induction n with
  | zero =>
    rw [sum_range_one, cF, cF, P_succ]
    simp [P]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ← ih]
    have h := key (n + 1)
    push_cast at h ⊢
    linear_combination h

end OMA.A262005

open OMA.A262005 in
theorem OMA.solution : type_of% @OMA.S_oeis_a262005.main := by
  rintro A ⟨hA0, hA⟩ n hn
  have hcoeff : ∀ m : ℕ, ∑ k ∈ range (m + 1), coeffF k * coeff (m - k) A = (m : ℤ) * coeffF m := by
    intro m
    have h := congrArg (coeff m) hA
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i seriesF * coeff j A)] at h
    simpa [seriesF, xDeriv, coeff_mk] using h
  have hmain : ∀ n : ℕ, 1 ≤ n → ((coeff n A : ℤ) : ZMod 60) = 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h := hcoeff (m + 1)
      rw [sum_range_succ, sum_range_succ', Nat.sub_self, hA0, Nat.sub_zero, mul_zero, add_zero] at h
      have hz := congrArg (Int.cast : ℤ → ZMod 60) h
      push_cast at hz
      have hsum : ∑ k ∈ range m, ((coeffF (k + 1) : ℤ) : ZMod 60) *
          ((coeff (m - k) A : ℤ) : ZMod 60) =
          ∑ k ∈ range m, ((coeffF (k + 1) : ℤ) : ZMod 60) * 2 := by
        apply sum_congr rfl
        intro k hk
        have hk' := mem_range.1 hk
        rw [ih (m - k) (by omega) (by omega)]
      rw [hsum] at hz
      have hT := T m
      rw [sum_range_succ'] at hT
      push_cast at hT
      have h0 : ((coeffF 0 : ℤ) : ZMod 60) = 1 := by simp [coeffF]
      rw [h0] at hz hT
      rw [← sum_mul] at hz
      linear_combination hz + hT
  have h2 := hmain n hn
  have h3 : ((coeff n A : ℤ) : ZMod 60) = ((2 : ℤ) : ZMod 60) := by rw [h2]; norm_num
  exact (ZMod.intCast_eq_intCast_iff _ _ _).1 h3
