import OMAStatements.S_oeis_a297741
import Mathlib

-- OEIS A297741: the three printed assertions are inconsistent. The g.f. (second conjunct)
-- at n = 13 gives a(13) - 3a(12) + 3a(11) - a(10) = 4 (the numerator coefficient of x^13),
-- while the quadratic 62n^2 + 30n - 55 claimed for n >= 10 (first conjunct) has vanishing
-- third differences: 10813 - 3*9233 + 3*7777 - 6445 = 0. (The entry's data 5233, 6445, 7777,
-- 9233 for n = 10..13 agree with the g.f.; the quadratic is off by one index:
-- it gives a(n+1).)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a297741.main) := by
  rintro ⟨h1, h2, -⟩
  have c : ∀ k : ℕ, OMA.S_oeis_a297741.coefficient (k : ℤ) = (OMA.S_oeis_a297741.a k : ℤ) := by
    intro k
    unfold OMA.S_oeis_a297741.coefficient
    have hk : ¬ ((k : ℤ) < 0) := by omega
    rw [if_neg hk, Int.toNat_natCast]
  have hn : OMA.S_oeis_a297741.numerator 13 = 4 := rfl
  have e12 : ((13 : ℕ) : ℤ) - 1 = ((12 : ℕ) : ℤ) := by norm_num
  have e11 : ((13 : ℕ) : ℤ) - 2 = ((11 : ℕ) : ℤ) := by norm_num
  have e10 : ((13 : ℕ) : ℤ) - 3 = ((10 : ℕ) : ℤ) := by norm_num
  have g := h2 13
  rw [e12, e11, e10, c, c, c, c, hn] at g
  have q10 := h1 10 (by norm_num)
  have q11 := h1 11 (by norm_num)
  have q12 := h1 12 (by norm_num)
  have q13 := h1 13 (by norm_num)
  generalize OMA.S_oeis_a297741.a 10 = x10 at g q10
  generalize OMA.S_oeis_a297741.a 11 = x11 at g q11
  generalize OMA.S_oeis_a297741.a 12 = x12 at g q12
  generalize OMA.S_oeis_a297741.a 13 = x13 at g q13
  push_cast at q10 q11 q12 q13
  linarith
