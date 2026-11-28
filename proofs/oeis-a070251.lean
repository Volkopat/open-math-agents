import OMAStatements.S_oeis_a070251
import Mathlib

/-!
# OEIS A070251: the first conjecture fails at `n = 35`

The numbers `k ≤ 35` sharing a factor with `35` but not dividing it are
`10, 14, 15, 20, 21, 25, 28, 30`, and their product is

  `a(35) = 18522000000 = 2⁷ · 3³ · 5⁶ · 7³`.

Every prime factor occurs at least twice, so `a(35)` is powerful, but it is not `4`.
-/

open OMA.S_oeis_a070251

namespace OMA.A070251

lemma a_35 : a 35 = 2 ^ 7 * 3 ^ 3 * 5 ^ 6 * 7 ^ 3 := by decide

/-- `2⁷ · 3³ · 5⁶ · 7³` is powerful. -/
lemma powerful : IsPowerful (2 ^ 7 * 3 ^ 3 * 5 ^ 6 * 7 ^ 3) := by
  refine ⟨by norm_num, fun p hp hdvd => ?_⟩
  -- `p` is one of `2, 3, 5, 7`
  have hp' : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)))
      · exact Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h))))
    · exact Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp (hp.dvd_of_dvd_pow h))))
  rcases hp' with rfl | rfl | rfl | rfl <;> norm_num

end OMA.A070251

open OMA.A070251 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a070251.main) := by
  rintro ⟨h, -, -⟩
  have h35 := h 35
  rw [a_35] at h35
  have := h35 (by norm_num) powerful
  norm_num at this
