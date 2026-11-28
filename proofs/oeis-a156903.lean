import OMAStatements.S_oeis_a156903
import Mathlib

namespace A156903
open Finset

lemma odd_prod (s : Finset ℕ) (f : ℕ → ℕ) : Odd (∏ p ∈ s, f p) ↔ ∀ p ∈ s, Odd (f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.odd_mul, ih]
    constructor
    · rintro ⟨h1, h2⟩ p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact h1
      · exact h2 p hp
    · intro h
      exact ⟨h a (Finset.mem_insert_self a s), fun p hp => h p (Finset.mem_insert_of_mem hp)⟩

lemma geom_mod_odd (p k : ℕ) (hp : p % 2 = 1) :
    (∑ i ∈ range (k + 1), p ^ i) % 2 = (k + 1) % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have h : p ^ (k + 1) % 2 = 1 := by
      rw [Nat.pow_mod, hp, one_pow]
      norm_num
    omega

lemma geom_mod_even (p k : ℕ) (hp : p % 2 = 0) :
    (∑ i ∈ range (k + 1), p ^ i) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have h : p ^ (k + 1) % 2 = 0 := by
      rw [Nat.pow_mod, hp]
      simp
    omega

lemma odd_sigma_iff (n : ℕ) (hn : n ≠ 0) :
    Odd (ArithmeticFunction.sigma 1 n) ↔
      ∀ p ∈ n.primeFactors, Odd p → Even (n.factorization p) := by
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn, odd_prod]
  constructor
  · intro h p hp hodd
    have h1 := h p hp
    simp only [mul_one] at h1
    rw [Nat.odd_iff, geom_mod_odd p _ (Nat.odd_iff.mp hodd)] at h1
    rw [Nat.even_iff]
    omega
  · intro h p hp
    simp only [mul_one]
    rw [Nat.odd_iff]
    rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
    · exact geom_mod_even p _ h0
    · have h2 := h p hp (Nat.odd_iff.mpr h1)
      rw [geom_mod_odd p _ h1]
      rw [Nat.even_iff] at h2
      omega

lemma closure (n s : ℕ) (hn : n ≠ 0) (hs : s ≠ 0)
    (hodd : Odd (ArithmeticFunction.sigma 1 n))
    (hsq : ∀ p : ℕ, p.Prime → Odd p → Even (s.factorization p)) :
    Odd (ArithmeticFunction.sigma 1 (s * n)) := by
  rw [odd_sigma_iff (s * n) (mul_ne_zero hs hn)]
  intro p hp hpodd
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [Nat.factorization_mul hs hn, Finsupp.add_apply]
  apply Even.add (hsq p hpp hpodd)
  by_cases hpn : p ∣ n
  · exact (odd_sigma_iff n hn).mp hodd p (Nat.mem_primeFactors.mpr ⟨hpp, hpn, hn⟩) hpodd
  · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
    exact ⟨0, rfl⟩

lemma sq_fact (t p : ℕ) : Even ((t ^ 2).factorization p) := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  exact even_two_mul _

lemma two_sq_fact (t p : ℕ) (ht : t ≠ 0) (hp : p.Prime) (hodd : Odd p) :
    Even ((2 * t ^ 2).factorization p) := by
  rw [Nat.factorization_mul (by norm_num) (pow_ne_zero 2 ht), Finsupp.add_apply]
  have hnd : ¬ p ∣ 2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
    · exact hp.ne_one h1
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  rw [Nat.factorization_eq_zero_of_not_dvd hnd, zero_add]
  exact sq_fact t p

lemma both (n : ℕ) (h : OMA.S_oeis_a156903.InSequence n) (t : ℕ) (ht : 0 < t) :
    OMA.S_oeis_a156903.InSequence (t ^ 2 * n) ∧
      OMA.S_oeis_a156903.InSequence (2 * t ^ 2 * n) := by
  obtain ⟨hab, hodd⟩ := h
  have hn : n ≠ 0 := hab.pos.ne'
  have ht0 : t ≠ 0 := ht.ne'
  have hs1 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  have hs2 : 2 * t ^ 2 ≠ 0 := mul_ne_zero (by norm_num) hs1
  exact ⟨⟨hab.mul_left hs1, closure n (t ^ 2) hn hs1 hodd (fun p _ _ => sq_fact t p)⟩,
    ⟨hab.mul_left hs2,
      closure n (2 * t ^ 2) hn hs2 hodd (fun p hp ho => two_sq_fact t p ht0 hp ho)⟩⟩

end A156903

theorem OMA.solution : type_of% @OMA.S_oeis_a156903.main := by
  constructor
  · intro n h
    have e : 100 * n = 10 ^ 2 * n := by norm_num
    rw [e]
    exact (A156903.both n h 10 (by norm_num)).1
  · intro n h t ht
    exact A156903.both n h t ht
