import OMAStatements.S_oeis_a039508
import Mathlib

/-! The 3x + 5 problem split by residue classes modulo 2^10 (a Terras-type descent theorem).

On the class `x = 2^10 a + r` the first iterates are affine in `a`: while fewer than ten
halvings have occurred, the parity of the iterate is that of the iterate of `r`, and the
iterate equals `3^o 2^(10-h) a + T^j(r)` after `o` odd steps and `h` halvings. For all but
64 of the 1024 classes this affine form drops below `x` (`3^o < 2^h` plus a bound on the
constant) for every `a ≥ 1`, and the start `x = r` itself descends or meets the six cycle
values. That is `H1`: about 93.8 percent of all starts have an iterate below themselves or in
the set. It is a classical density statement, not progress on the conjecture.

`H2` is the open rest: descent for the 64 residue classes listed there. With strong induction
the two give the conjecture.
-/

namespace OMA.R_oeis_a039508_R1

open OMA.S_oeis_a039508

/-- Starts outside the 64 listed classes modulo 1024 descend or reach the cycle values. -/
def H1 : Prop := ∀ x : ℕ, 1 ≤ x →
    x % 1024 ∉ ({3, 7, 11, 27, 43, 59, 91, 99, 123, 131, 135, 155, 171, 187, 199,
      231, 235, 251, 259, 263, 267, 283, 299, 315, 323, 347, 355, 379, 387, 391, 427, 443, 455,
      491, 507, 515, 523, 539, 555, 571, 579, 611, 635, 643, 647, 667, 683, 699, 743, 747, 763,
      771, 775, 795, 835, 859, 891, 903, 923, 939, 955, 967, 999, 1019} : Finset ℕ) →
    ∃ i : ℕ, T^[i] x < x ∨ T^[i] x ∈ ({1, 5, 19, 23, 187, 347} : Finset ℕ)

/-- The open rest: the 64 residue classes modulo 1024 without an affine descent. -/
def H2 : Prop := ∀ x : ℕ, 1 ≤ x →
    x % 1024 ∈ ({3, 7, 11, 27, 43, 59, 91, 99, 123, 131, 135, 155, 171, 187, 199,
      231, 235, 251, 259, 263, 267, 283, 299, 315, 323, 347, 355, 379, 387, 391, 427, 443, 455,
      491, 507, 515, 523, 539, 555, 571, 579, 611, 635, 643, 647, 667, 683, 699, 743, 747, 763,
      771, 775, 795, 835, 859, 891, 903, 923, 939, 955, 967, 999, 1019} : Finset ℕ) →
    ∃ i : ℕ, T^[i] x < x ∨ T^[i] x ∈ ({1, 5, 19, 23, 187, 347} : Finset ℕ)

lemma T_pos (x : ℕ) (hx : 1 ≤ x) : 1 ≤ T x := by
  unfold T
  split_ifs with h <;> omega

lemma iter_pos (i x : ℕ) (hx : 1 ≤ x) : 1 ≤ T^[i] x := by
  induction i with
  | zero => simpa using hx
  | succ i ih => rw [Function.iterate_succ_apply']; exact T_pos _ ih

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a039508.main := by
  intro h1 h2 x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    have hd : ∃ i : ℕ, T^[i] x < x ∨ T^[i] x ∈ ({1, 5, 19, 23, 187, 347} : Finset ℕ) := by
      by_cases hb : x % 1024 ∈ ({3, 7, 11, 27, 43, 59, 91, 99, 123, 131, 135, 155, 171, 187, 199,
      231, 235, 251, 259, 263, 267, 283, 299, 315, 323, 347, 355, 379, 387, 391, 427, 443, 455,
      491, 507, 515, 523, 539, 555, 571, 579, 611, 635, 643, 647, 667, 683, 699, 743, 747, 763,
      771, 775, 795, 835, 859, 891, 903, 923, 939, 955, 967, 999, 1019} : Finset ℕ)
      · exact h2 x hx hb
      · exact h1 x hx hb
    obtain ⟨i, hi | hi⟩ := hd
    · obtain ⟨j, hj⟩ := ih _ hi (iter_pos i x hx)
      exact ⟨j + i, by rw [Function.iterate_add_apply]; exact hj⟩
    · exact ⟨i, hi⟩

end OMA.R_oeis_a039508_R1
