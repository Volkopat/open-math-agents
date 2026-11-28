import OMAStatements.S_mo_107600
import Mathlib

open OMA.S_mo_107600

private theorem commuteOne (p : ℕ) (A B : Matrix (Fin 1) (Fin 1) (ZMod p)) :
    Commute A B := by
  change A * B = B * A
  ext i j
  rw [Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1)]
  simp only [Matrix.mul_apply, Fin.sum_univ_one, mul_comm]

private theorem bound (p : ℕ) : maxNoncommuting 1 p ≤ 1 := by
  have existsSize : (attainableSizes 1 p).Nonempty := by
    exact ⟨0, ∅, by simp, by simp⟩
  unfold maxNoncommuting
  refine csSup_le existsSize ?_
  intro k hk
  obtain ⟨S, pairwise, rfl⟩ := hk
  refine Finset.card_le_one.mpr ?_
  intro A ha B hb
  by_contra hne
  exact (pairwise ha hb hne) (commuteOne p A B)

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_107600.main) := by
  intro proposed
  obtain ⟨N, approx⟩ := proposed 1 (by decide) (1/2 : ℝ) (by norm_num)
  obtain ⟨p, ge, prime⟩ := Nat.exists_infinite_primes (max N 2)
  have hmin : 2 ≤ p := (le_max_right N 2).trans ge
  have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hmin
  have hcap : (maxNoncommuting 1 p : ℝ) ≤ 1 := by exact_mod_cast (bound p)
  have hr : (maxNoncommuting 1 p : ℝ) / (p : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ (show 0 < (p : ℝ) by linarith)).mpr
    linarith
  have herror := approx p prime ((le_max_left N 2).trans ge)
  norm_num only [one_mul, pow_one] at herror
  have hlow := (abs_lt.mp herror).1
  linarith