import OMAStatements.S_oeis_a253240

-- Reduction oeis-a253240.R1 of A253240: Square array read by antidiagonals: T(m, n) = Phi_m(n), the m-th cyclotomic polynomial at x=n.
-- Credit: @notswizz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Proved here unconditionally: rows 1 and 2 (Phi_1(n) = n - 1 and Phi_2(n) = n + 1 are prime for
-- infinitely many n, by Euclid) and column 1 (Phi_p(1) = p for every prime p). What remains is every
-- row m >= 3 (Bunyakovsky-type, open) and every column n >= 2 (e.g. n = 2 asks for infinitely many
-- prime values Phi_m(2), open).

open Polynomial OMA.S_oeis_a253240

namespace OMA.R_oeis_a253240_R1

def H1 : Prop := ∀ m : ℕ, 3 ≤ m → {n : ℕ | Prime (T m n)}.Infinite

def H2 : Prop := ∀ n : ℕ, 2 ≤ n → {m : ℕ | Prime (T m n)}.Infinite

theorem row_one : {n : ℕ | Prime (T 1 n)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (a + 1)
  refine ⟨p + 1, ?_, by omega⟩
  show Prime (T 1 (p + 1))
  have : T 1 (p + 1) = (p : ℤ) := by simp [T]
  rw [this]
  exact Nat.prime_iff_prime_int.mp hp

theorem row_two : {n : ℕ | Prime (T 2 n)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (a + 2)
  refine ⟨p - 1, ?_, by omega⟩
  show Prime (T 2 (p - 1))
  have h1 : 1 ≤ p := by omega
  have : T 2 (p - 1) = (p : ℤ) := by
    simp only [T, cyclotomic_two, eval_add, eval_X, eval_one]
    push_cast [h1]
    ring
  rw [this]
  exact Nat.prime_iff_prime_int.mp hp

theorem col_one : {m : ℕ | Prime (T m 1)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (a + 1)
  refine ⟨p, ?_, by omega⟩
  show Prime (T p 1)
  haveI : Fact p.Prime := ⟨hp⟩
  have : T p 1 = (p : ℤ) := by simp [T, eval_one_cyclotomic_prime]
  rw [this]
  exact Nat.prime_iff_prime_int.mp hp

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a253240.main := by
  intro h1 h2
  refine ⟨fun m hm => ?_, fun n hn => ?_⟩
  · rcases Nat.lt_or_ge m 3 with hlt | hge
    · interval_cases m
      · exact row_one
      · exact row_two
    · exact h1 m hge
  · rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      exact col_one
    · exact h2 n hge

end OMA.R_oeis_a253240_R1
