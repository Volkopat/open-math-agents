import OMAStatements.S_oeis_a343260
import Mathlib

namespace A343260Proof
open Polynomial

def cc : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n+2 => cc (n+1) - cc n

def ss : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n+2 => ss (n+1) - ss n

lemma cc_ss (n : ℕ) :
    cc (n+1) = ss (n+1) - 2 * ss n ∧ cc (n+2) = ss (n+2) - 2 * ss (n+1) := by
  induction n with
  | zero => refine ⟨by decide, by decide⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h1 : cc (n+3) = cc (n+2) - cc (n+1) := by rw [cc]
    have h2 : ss (n+3) = ss (n+2) - ss (n+1) := by rw [ss]
    have h3 : ss (n+2) = ss (n+1) - ss n := by rw [ss]
    show cc (n+3) = ss (n+3) - 2 * ss (n+2)
    linarith [ih.1, ih.2]

lemma cc3 (n : ℕ) : cc (n+3) = - cc n := by
  have h1 : cc (n+3) = cc (n+2) - cc (n+1) := by rw [cc]
  have h2 : cc (n+2) = cc (n+1) - cc n := by rw [cc]
  linarith

lemma cc6 (n : ℕ) : cc (n+6) = cc n := by
  have h1 : cc (n+6) = - cc (n+3) := cc3 (n+3)
  have h2 := cc3 n
  linarith

lemma cc_mod (q : ℕ) : cc (6*q+1) = 1 ∧ cc (6*q+5) = 1 := by
  induction q with
  | zero => refine ⟨by decide, by decide⟩
  | succ q ih =>
    have e1 : 6*(q+1)+1 = (6*q+1)+6 := by ring
    have e2 : 6*(q+1)+5 = (6*q+5)+6 := by ring
    rw [e1, e2, cc6, cc6]
    exact ih

lemma cc_one (N : ℕ) (h : N % 6 = 1 ∨ N % 6 = 5) : cc N = 1 := by
  rcases h with h | h
  · have e : N = 6 * (N / 6) + 1 := by omega
    rw [e]
    exact (cc_mod _).1
  · have e : N = 6 * (N / 6) + 5 := by omega
    rw [e]
    exact (cc_mod _).2

lemma eval_C (n : ℕ) :
    ((Chebyshev.C ℤ (n : ℤ)).eval 1 = cc n ∧
      (derivative (Chebyshev.C ℤ (n : ℤ))).eval 1 = n * ss n) ∧
    ((Chebyshev.C ℤ ((n : ℤ) + 1)).eval 1 = cc (n+1) ∧
      (derivative (Chebyshev.C ℤ ((n : ℤ) + 1))).eval 1 = ((n : ℤ) + 1) * ss (n+1)) := by
  induction n with
  | zero => simp [cc, ss]
  | succ n ih =>
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ih
    have e : ((n + 1 : ℕ) : ℤ) + 1 = (n : ℤ) + 2 := by push_cast; ring
    have hc : cc (n+2) = cc (n+1) - cc n := by rw [cc]
    have hs : ss (n+2) = ss (n+1) - ss n := by rw [ss]
    have hcs := (cc_ss n).1
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · push_cast
      exact h3
    · push_cast
      exact h4
    · rw [e, Chebyshev.C_add_two]
      simp only [eval_sub, eval_mul, eval_X, one_mul]
      rw [h1, h3]
      exact hc.symm
    · rw [e, Chebyshev.C_add_two]
      simp only [derivative_sub, derivative_mul, derivative_X, eval_sub, eval_add, eval_mul,
        eval_X, one_mul]
      rw [h2, h3, h4]
      show _ = (((n + 1 : ℕ) : ℤ) + 1) * ss (n + 2)
      rw [hs, hcs]
      push_cast
      ring

lemma core (N : ℕ) (h : N % 6 = 1 ∨ N % 6 = 5) :
    ((N : ℤ)^2) ∣ 1 - (Chebyshev.C ℤ (N : ℤ)).eval ((N : ℤ) + 1) := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (Chebyshev.C ℤ (N : ℤ)) 1 (N : ℤ)
  have h1 := (eval_C N).1
  rw [h1.1, h1.2, cc_one N h] at hk
  rw [add_comm (N : ℤ) 1, hk]
  exact ⟨-(ss N + k), by ring⟩

end A343260Proof

open OMA.S_oeis_a343260 A343260Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a343260.main := by
  intro p r hp h5 hr
  have h2 : ¬ 2 ∣ p^r := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)
    omega
  have h3 : ¬ 3 ∣ p^r := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  have hmod : p^r % 6 = 1 ∨ p^r % 6 = 5 := by omega
  have e : (p : ℤ)^(2*r) = (((p^r : ℕ)) : ℤ)^2 := by push_cast; ring
  unfold term
  rw [Int.modEq_iff_dvd, e]
  exact core (p^r) hmod
