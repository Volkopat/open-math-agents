import OMAStatements.S_oeis_a202137
import Mathlib

-- Problem: A202137: Numbers k such that 24k + 1 is neither square nor prime.
-- Upstream: formal-conjectures statements/oeis-a202137.lean:0 (declaration OMA.S_oeis_a202137.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! An explicit run. Let M be the product of the numbers d_i = 24 i + 25 for i < L and take
k = 6 M^2 + 1. Then 24 (k + i) + 1 = (12 M)^2 + d_i. Since d_i divides M, it divides this number
and is a proper divisor larger than 1, so the number is not prime. Since 0 < d_i <= M < 24 M + 1,
the number lies strictly between (12 M)^2 and (12 M + 1)^2, so it is not a square. -/

namespace A202137Aux

open OMA.S_oeis_a202137

theorem run (L : ℕ) : ∃ k : ℕ, ∀ i : ℕ, i < L → IsTerm (k + i) := by
  set M : ℕ := ∏ j ∈ Finset.range L, (24 * j + 25) with hM
  have hMpos : 0 < M := Finset.prod_pos (fun j _ => by omega)
  refine ⟨6 * M ^ 2 + 1, fun i hi => ?_⟩
  have hd : (24 * i + 25) ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi)
  have hle : 24 * i + 25 ≤ M := Nat.le_of_dvd hMpos hd
  have hval : 24 * (6 * M ^ 2 + 1 + i) + 1 = (12 * M) * (12 * M) + (24 * i + 25) := by ring
  constructor
  · rintro ⟨r, hr⟩
    rw [hval] at hr
    have h1 : 12 * M < r := by
      by_contra h
      have h' : r ≤ 12 * M := Nat.le_of_not_lt h
      have := Nat.mul_le_mul h' h'
      omega
    have h2 : r < 12 * M + 1 := by
      by_contra h
      have h' : 12 * M + 1 ≤ r := Nat.le_of_not_lt h
      have h3 := Nat.mul_le_mul h' h'
      have h4 : (12 * M + 1) * (12 * M + 1) = 12 * M * (12 * M) + 24 * M + 1 := by ring
      omega
    omega
  · rw [hval]
    have hdvd : (24 * i + 25) ∣ 12 * M * (12 * M) + (24 * i + 25) :=
      Dvd.dvd.add (Dvd.dvd.mul_left (Dvd.dvd.mul_left hd 12) _) (dvd_refl _)
    have hlt : 24 * i + 25 < 12 * M * (12 * M) + (24 * i + 25) := by
      have : 0 < 12 * M * (12 * M) := by positivity
      omega
    exact Nat.not_prime_of_dvd_of_lt hdvd (by omega) hlt

end A202137Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a202137.main :=
  A202137Aux.run
