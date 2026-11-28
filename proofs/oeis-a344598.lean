import OMAStatements.S_oeis_a344598
import Mathlib

/-!
The summand is phi(k) * (2 * (n / k) - 1) when k divides n and 0 otherwise, so by Pillai's identity
the left side is 2 * P(n) - n with P(m) = sum of gcd(k, m) for k = 1..m. Splitting the right side by
parity gives 2 * A - O, where A sums gcd(j, 2n) for j = 1..n and O sums gcd(2j - 1, n); the same
split gives P(2n) = O + 2 * P(n), and the reflection j -> 2n - j gives P(2n) = 2 * A + n.
-/

namespace R344598
open Finset

theorem icc (f : ℕ → ℤ) (m : ℕ) : ∑ k ∈ Icc 1 m, f k = ∑ k ∈ range m, f (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

theorem pair (f : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (2 * n), f k = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ _ (2 * n + 1),
      sum_range_succ _ (2 * n), ih, sum_range_succ _ n, add_assoc]

theorem pillai (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ range n, Nat.gcd (k + 1) n = ∑ d ∈ n.divisors, Nat.totient d * (n / d) := by
  calc ∑ k ∈ range n, Nat.gcd (k + 1) n
      = ∑ k ∈ range n, ∑ d ∈ n.divisors with d ∣ k + 1, Nat.totient d := by
        refine sum_congr rfl fun k _ => ?_
        rw [← Nat.sum_totient (Nat.gcd (k + 1) n)]
        refine sum_congr ?_ fun _ _ => rfl
        ext d
        simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hn] <;> tauto
    _ = ∑ d ∈ n.divisors, ∑ k ∈ range n with d ∣ k + 1, Nat.totient d :=
        sum_comm' fun k d => by simp only [mem_filter]; tauto
    _ = _ := by
        refine sum_congr rfl fun d _ => ?_
        rw [sum_const, Nat.card_multiples, smul_eq_mul, mul_comm]

theorem lhs (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, (Nat.totient k : ℤ) * (((n / k : ℕ) : ℤ) ^ 2 - (((n - 1) / k : ℕ) : ℤ) ^ 2) =
      ∑ k ∈ n.divisors, (Nat.totient k : ℤ) * (2 * ((n / k : ℕ) : ℤ) - 1) := by
  have hd : n.divisors = (Icc 1 n).filter (· ∣ n) := by
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨h, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h hn, Nat.le_of_dvd hn h⟩, h⟩
    · rintro ⟨-, h⟩
      exact ⟨h, by omega⟩
  rw [hd, sum_filter]
  refine sum_congr rfl fun k _ => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.succ_div]
  split_ifs <;> push_cast <;> ring

theorem rhs (n : ℕ) :
    ∑ k ∈ Icc 1 (2 * n), (-1 : ℤ) ^ k * (Nat.gcd k (4 * n) : ℤ) =
      ∑ j ∈ range n, (2 * (Nat.gcd (j + 1) (2 * n) : ℤ) - Nat.gcd (2 * j + 1) n) := by
  rw [icc, pair]
  refine sum_congr rfl fun j _ => ?_
  have h2 : Nat.Coprime 2 (2 * j + 1) := Nat.coprime_two_left.2 (odd_two_mul_add_one j)
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, show 4 * n = 2 * (2 * n) by ring,
    Nat.gcd_mul_left, h2.gcd_mul_left_cancel_right, h2.gcd_mul_left_cancel_right,
    Odd.neg_one_pow (odd_two_mul_add_one j), Even.neg_one_pow (even_two_mul _)]
  push_cast
  ring

theorem p2 (n : ℕ) :
    ∑ k ∈ range (2 * n), (Nat.gcd (k + 1) (2 * n) : ℤ) =
      ∑ j ∈ range n, ((Nat.gcd (2 * j + 1) n : ℤ) + 2 * Nat.gcd (j + 1) n) := by
  rw [pair]
  refine sum_congr rfl fun j _ => ?_
  have h2 : Nat.Coprime 2 (2 * j + 1) := Nat.coprime_two_left.2 (odd_two_mul_add_one j)
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, Nat.gcd_mul_left,
    h2.gcd_mul_left_cancel_right]
  push_cast
  ring

theorem refl (n : ℕ) :
    ∑ k ∈ range (2 * n), (Nat.gcd (k + 1) (2 * n) : ℤ) =
      2 * ∑ j ∈ range n, (Nat.gcd (j + 1) (2 * n) : ℤ) + n := by
  have e := sum_range_add (fun k => (Nat.gcd (k + 1) (2 * n) : ℤ)) n n
  rw [← two_mul] at e
  have h : ∑ x ∈ range n, (Nat.gcd (n + x + 1) (2 * n) : ℤ) =
      ∑ x ∈ range n, (Nat.gcd x (2 * n) : ℤ) := by
    rw [← sum_range_reflect (fun x => (Nat.gcd (n + x + 1) (2 * n) : ℤ)) n]
    refine sum_congr rfl fun x hx => ?_
    rw [mem_range] at hx
    rw [show n + (n - 1 - x) + 1 = 2 * n - x by omega,
      Nat.gcd_self_sub_left (show x ≤ 2 * n by omega)]
  have e1 := sum_range_succ (fun x => (Nat.gcd x (2 * n) : ℤ)) n
  have e2 := sum_range_succ' (fun x => (Nat.gcd x (2 * n) : ℤ)) n
  simp only [Nat.gcd_zero_left, Nat.gcd_mul_left_right, Nat.cast_mul, Nat.cast_ofNat] at e1 e2
  rw [e, h]
  linarith

end R344598

theorem OMA.solution : type_of% @OMA.S_oeis_a344598.main := by
  intro n hn
  rw [R344598.lhs n hn, R344598.rhs]
  have e1 : ∑ k ∈ Finset.range n, ((Nat.gcd (k + 1) n : ℕ) : ℤ) =
      ∑ d ∈ n.divisors, (Nat.totient d : ℤ) * ((n / d : ℕ) : ℤ) := by
    exact_mod_cast R344598.pillai n (by omega)
  have e2 : ∑ d ∈ n.divisors, (Nat.totient d : ℤ) = n := by exact_mod_cast Nat.sum_totient n
  have e3 := R344598.p2 n
  have e4 := R344598.refl n
  have e5 : ∑ d ∈ n.divisors, (Nat.totient d : ℤ) * (2 * ((n / d : ℕ) : ℤ) - 1) =
      2 * ∑ d ∈ n.divisors, (Nat.totient d : ℤ) * ((n / d : ℕ) : ℤ) - ∑ d ∈ n.divisors, (Nat.totient d : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [e5]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at e3 ⊢
  linarith
