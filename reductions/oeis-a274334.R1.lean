import OMAStatements.S_oeis_a274334
import Mathlib

-- Reduction oeis-a274334.R1 of A274334: Numbers whose cube is the sum of 4 positive cubes.
-- Credit: @avk-lab
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
The conjecture says that every k ≥ 72 is a term and that exactly 50 numbers below 72 are terms.
A positive multiple of a term is a term. A composite k ≥ 72 is p * b with p its least prime
factor and p ≤ b < k: either b ≥ 72 (induction), or one of p, b is a term below 72, or both lie
in the exceptional set and k is one of finitely many products. So the conjecture reduces to
the primes p ≥ 73 (H1, the open part) and two finite checks (H2 by witnesses, H3 by search).
No polynomial identity can give H1: a linear family (m t + r)^3 = Σ (a_i t + b_i)^3 with
a_i ≥ 0 forces b_i = a_i r / m, so it only produces multiples of one solution.
-/

namespace OMA.R_oeis_a274334_R1

open OMA.S_oeis_a274334

/-- The open part: the cube of every prime p ≥ 73 is a sum of four positive cubes. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 73 ≤ p → IsTerm p

/-- Finite, by explicit witnesses: the 50 terms below 72, and the products ≥ 72 of two
exceptional numbers (all of them are at most 71 * 71). -/
def H2 : Prop :=
  (∀ k : ℕ, k < 72 → k ∉ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 15, 16, 17, 19, 22, 27, 29, 47, 58, 61, 71} : Finset ℕ) → IsTerm k) ∧
  (∀ a ∈ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 15, 16, 17, 19, 22, 27, 29, 47, 58, 61, 71} : Finset ℕ), ∀ b ∈ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 15, 16, 17, 19, 22, 27, 29, 47, 58, 61, 71} : Finset ℕ), 72 ≤ a * b → IsTerm (a * b))

/-- Finite, by bounded search: the 22 exceptional numbers are not terms. -/
def H3 : Prop := ∀ k ∈ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 15, 16, 17, 19, 22, 27, 29, 47, 58, 61, 71} : Finset ℕ), ¬ IsTerm k

theorem isTerm_mul {d : ℕ} (h : IsTerm d) {m : ℕ} (hm : 0 < m) : IsTerm (d * m) := by
  obtain ⟨w, x, y, z, hw, hx, hy, hz, e⟩ := h
  exact ⟨w * m, x * m, y * m, z * m, Nat.mul_pos hw hm, Nat.mul_pos hx hm, Nat.mul_pos hy hm,
    Nat.mul_pos hz hm, by rw [mul_pow, e]; ring⟩

theorem exists_factor {k : ℕ} (hk : 2 ≤ k) (hp : ¬ k.Prime) :
    ∃ p b : ℕ, p.Prime ∧ k = p * b ∧ p ≤ b ∧ b < k :=
  ⟨k.minFac, k / k.minFac, Nat.minFac_prime (by omega),
    (Nat.mul_div_cancel' (Nat.minFac_dvd k)).symm, Nat.minFac_le_div (by omega) hp,
    Nat.div_lt_self (by omega) (Nat.minFac_prime (by omega)).one_lt⟩

theorem all_terms (h1 : H1) (h2 : H2) : ∀ k : ℕ, 72 ≤ k → IsTerm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hp : k.Prime
    · refine h1 k hp ?_
      rcases hk.eq_or_lt with rfl | h
      · exact absurd hp (by norm_num)
      · exact h
    · obtain ⟨p, b, hpp, rfl, hpb, hbk⟩ := exists_factor (by omega) hp
      have hp2 := hpp.two_le
      by_cases hb72 : 72 ≤ b
      · rw [mul_comm]; exact isTerm_mul (ih b hbk hb72) hpp.pos
      · by_cases hbE : b ∈ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 15, 16, 17, 19, 22, 27, 29, 47, 58, 61, 71} : Finset ℕ)
        · by_cases hpE : p ∈ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 15, 16, 17, 19, 22, 27, 29, 47, 58, 61, 71} : Finset ℕ)
          · exact h2.2 p hpE b hbE hk
          · exact isTerm_mul (h2.1 p (by omega) hpE) (by omega)
        · rw [mul_comm]; exact isTerm_mul (h2.1 b (by omega) hbE) hpp.pos

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a274334.main := by
  intro h1 h2 h3 n hn
  classical
  have hall := all_terms h1 h2
  have hfilter : (Finset.range 72).filter IsTerm = Finset.range 72 \ ({0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 15, 16, 17, 19, 22, 27, 29, 47, 58, 61, 71} : Finset ℕ) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
    exact ⟨fun ⟨hk, ht⟩ => ⟨hk, fun hE => h3 k hE ht⟩, fun ⟨hk, hE⟩ => ⟨hk, h2.1 k hk hE⟩⟩
  have h72 : Nat.count IsTerm 72 = 50 := by
    rw [Nat.count_eq_card_filter_range, hfilter]
    decide
  have hcount : ∀ j : ℕ, Nat.count IsTerm (72 + j) = 50 + j := by
    intro j
    induction j with
    | zero => simpa using h72
    | succ j ih => rw [← add_assoc, Nat.count_succ, ih, if_pos (hall _ (by omega)), add_assoc]
  have key := Nat.nth_count (p := IsTerm) (hall (72 + (n - 51)) (by omega))
  rw [hcount] at key
  rw [a, show n - 1 = 50 + (n - 51) by omega, key]
  omega

end OMA.R_oeis_a274334_R1
