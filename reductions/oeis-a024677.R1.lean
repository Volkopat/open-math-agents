import OMAStatements.S_oeis_a024677

-- Reduction oeis-a024677.R1 of A024677: Smallest prime divisor of n-th terms of sequence A024675 (averages of two consecutive odd primes).
-- Credit: @notswizz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- The case p = 2 is proved here unconditionally (it does NOT need twin primes): a(n) = 2 exactly when
-- prime(n+1) and prime(n+2) lie in different classes mod 4, and by Dirichlet's theorem (in Mathlib)
-- consecutive odd primes cannot stay in one class mod 4 forever. What remains is p = 3 (consecutive
-- primes in classes {1, 5} or {7, 11} mod 12) and p >= 5.

open OMA.S_oeis_a024677

namespace OMA.R_oeis_a024677_R1

def H1 : Prop := {n : ℕ | 1 ≤ n ∧ a n = 3}.Infinite

def H2 : Prop := ∀ p : ℕ, p.Prime → 5 ≤ p → {n : ℕ | 1 ≤ n ∧ a n = p}.Infinite

lemma nth_prime_odd {n : ℕ} (hn : 1 ≤ n) : Nat.nth Nat.Prime n % 2 = 1 := by
  have hsm := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hp := Nat.prime_nth_prime n
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have hgt : 2 < Nat.nth Nat.Prime n := by rw [← h0]; exact hsm (by omega)
  rcases hp.eq_two_or_odd with h | h <;> omega

lemma a_eq_two_of_mod {n : ℕ} (hn : 1 ≤ n)
    (h : Nat.nth Nat.Prime n % 4 ≠ Nat.nth Nat.Prime (n + 1) % 4) : a n = 2 := by
  unfold a
  rw [Nat.minFac_eq_two_iff]
  have h1 := nth_prime_odd hn
  have h2 := nth_prime_odd (n := n + 1) (by omega)
  omega

theorem case_two : {n : ℕ | 1 ≤ n ∧ a n = 2}.Infinite := by
  have hsm := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨B, hB⟩ := hfin.bddAbove
  set N := B + 1 with hN
  have hstep : ∀ n, N ≤ n → Nat.nth Nat.Prime (n + 1) % 4 = Nat.nth Nat.Prime n % 4 := by
    intro n hn
    by_contra hne
    have : n ∈ {n : ℕ | 1 ≤ n ∧ a n = 2} := ⟨by omega, a_eq_two_of_mod (by omega) (Ne.symm hne)⟩
    have := hB this
    omega
  have hall : ∀ k, Nat.nth Nat.Prime (N + k) % 4 = Nat.nth Nat.Prime N % 4 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← Nat.add_assoc, hstep _ (by omega), ih]
  have hodd := nth_prime_odd (n := N) (by omega)
  set r := Nat.nth Nat.Prime N % 4 with hr
  have hr' : r = 1 ∨ r = 3 := by omega
  have hcop : (4 - r).Coprime 4 := by rcases hr' with h | h <;> rw [h] <;> decide
  obtain ⟨q, hqgt, hqp, hqmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (Nat.nth Nat.Prime N) (by norm_num : (4:ℕ) ≠ 0) hcop
  have hq : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hqp
  have hlt : N < Nat.count Nat.Prime q := by
    rw [← hsm.lt_iff_lt, hq]; exact hqgt
  have := hall (Nat.count Nat.Prime q - N)
  rw [Nat.add_sub_cancel' hlt.le, hq] at this
  have hqm : q % 4 = (4 - r) % 4 := hqmod
  rcases hr' with h | h <;> rw [h] at hqm <;> omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a024677.main := by
  intro h1 h2 p hp
  rcases Nat.lt_or_ge p 5 with hlt | hge
  · have h2le := hp.two_le
    interval_cases p
    · exact case_two
    · exact h1
    · exact absurd hp (by decide)
  · exact h2 p hp hge

end OMA.R_oeis_a024677_R1
