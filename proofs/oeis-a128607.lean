import OMAStatements.S_oeis_a128607
import Mathlib

-- Problem: A128607: Perfect (or pure) powers pp such that sigma(pp) is also a perfect (pure) power.
-- Upstream: formal-conjectures statements/oeis-a128607.lean:0 (declaration OMA.S_oeis_a128607.main)
-- Credit: @Ezekia1 (the owner of the agent is credited as the solver)
-- Witnesses: sigma(751530^3) = 1292054400^2 with 751530 = 2*3*5*13*41*47, and
-- sigma(30519275171^2) = 10773399^3 with 30519275171 = 7*11*29*163*191*439.
-- Each divisor sum is computed by multiplicativity and the prime-power formula.

open scoped ArithmeticFunction.sigma
open ArithmeticFunction

lemma OMA.sig_cube (p : ℕ) (hp : p.Prime) : σ 1 (p ^ 3) = 1 + p + p ^ 2 + p ^ 3 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

lemma OMA.sig_sq (p : ℕ) (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

lemma OMA.sig_mul (a b : ℕ) (h : Nat.Coprime a b) : σ 1 (a * b) = σ 1 a * σ 1 b :=
  isMultiplicative_sigma.map_mul_of_coprime h

lemma OMA.part1 : σ 1 (751530 ^ 3) = 1292054400 ^ 2 := by
  have e : (751530 : ℕ) ^ 3 = 2 ^ 3 * (3 ^ 3 * (5 ^ 3 * (13 ^ 3 * (41 ^ 3 * 47 ^ 3)))) := by
    norm_num
  rw [e,
    OMA.sig_mul (2 ^ 3) (3 ^ 3 * (5 ^ 3 * (13 ^ 3 * (41 ^ 3 * 47 ^ 3)))) (by norm_num),
    OMA.sig_mul (3 ^ 3) (5 ^ 3 * (13 ^ 3 * (41 ^ 3 * 47 ^ 3))) (by norm_num),
    OMA.sig_mul (5 ^ 3) (13 ^ 3 * (41 ^ 3 * 47 ^ 3)) (by norm_num),
    OMA.sig_mul (13 ^ 3) (41 ^ 3 * 47 ^ 3) (by norm_num),
    OMA.sig_mul (41 ^ 3) (47 ^ 3) (by norm_num),
    OMA.sig_cube 2 (by norm_num), OMA.sig_cube 3 (by norm_num), OMA.sig_cube 5 (by norm_num),
    OMA.sig_cube 13 (by norm_num), OMA.sig_cube 41 (by norm_num), OMA.sig_cube 47 (by norm_num)]
  norm_num

lemma OMA.part2 : σ 1 (30519275171 ^ 2) = 10773399 ^ 3 := by
  have e : (30519275171 : ℕ) ^ 2
      = 7 ^ 2 * (11 ^ 2 * (29 ^ 2 * (163 ^ 2 * (191 ^ 2 * 439 ^ 2)))) := by
    norm_num
  rw [e,
    OMA.sig_mul (7 ^ 2) (11 ^ 2 * (29 ^ 2 * (163 ^ 2 * (191 ^ 2 * 439 ^ 2)))) (by norm_num),
    OMA.sig_mul (11 ^ 2) (29 ^ 2 * (163 ^ 2 * (191 ^ 2 * 439 ^ 2))) (by norm_num),
    OMA.sig_mul (29 ^ 2) (163 ^ 2 * (191 ^ 2 * 439 ^ 2)) (by norm_num),
    OMA.sig_mul (163 ^ 2) (191 ^ 2 * 439 ^ 2) (by norm_num),
    OMA.sig_mul (191 ^ 2) (439 ^ 2) (by norm_num),
    OMA.sig_sq 7 (by norm_num), OMA.sig_sq 11 (by norm_num), OMA.sig_sq 29 (by norm_num),
    OMA.sig_sq 163 (by norm_num), OMA.sig_sq 191 (by norm_num), OMA.sig_sq 439 (by norm_num)]
  norm_num

lemma OMA.mkPow (n k b e : ℕ) (hb : 1 < b) (he : k ≤ e) (h : b ^ e = n) :
    OMA.S_oeis_a128607.IsPowerAtLeast n k := by
  unfold OMA.S_oeis_a128607.IsPowerAtLeast
  exact ⟨b, e, hb, he, h⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a128607.main := by
  refine ⟨⟨751530 ^ 3, by norm_num, by norm_num, ?_, ?_⟩, ⟨30519275171 ^ 2, by norm_num, ?_, ?_⟩⟩
  · exact OMA.mkPow _ 3 751530 3 (by norm_num) le_rfl rfl
  · exact OMA.mkPow _ 2 1292054400 2 (by norm_num) le_rfl OMA.part1.symm
  · exact OMA.mkPow _ 2 30519275171 2 (by norm_num) le_rfl rfl
  · exact OMA.mkPow _ 3 10773399 3 (by norm_num) le_rfl OMA.part2.symm
