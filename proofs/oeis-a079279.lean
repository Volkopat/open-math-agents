import OMAStatements.S_oeis_a079279
import Mathlib

/-!
# A079279: the conjectured recurrence a(n) = a(n-1) + a(n-14) - a(n-15) fails at n = 97

The statement is false, so this file proves its negation with an explicit counterexample.

The definition of the sequence uses an infimum, so it is not computed directly. The lemma
`next_eq` says that next x y z = m as soon as z < m, the number m shares a common factor with
1 or 2 of x, y, z, and no k strictly between z and m does. With it the first 97 terms are
proved one by one from the definition, each step being a finite check.

The values found are a(82) = 172, a(83) = 176, a(96) = 202 and a(97) = 203.
The recurrence at n = 97 would give a(97) = a(96) + a(83) - a(82) = 202 + 176 - 172 = 206,
but the true value is 203, because 203 = 7 * 29 shares the factor 7 with a(94) = 196 and
no factor with a(95) = 201 or a(96) = 202. This agrees with the comment in the entry that
the sequence contains all numbers congruent to 203 mod 210.
-/

namespace OMA.P079279

open OMA.S_oeis_a079279

/-- A candidate m is the value of next x y z when it satisfies the rule and nothing between
z and m does. -/
theorem next_eq {x y z m : ℕ} (h1 : z < m) (h2 : shared m x y z = 1 ∨ shared m x y z = 2)
    (h3 : ∀ k, z < k → k < m → ¬ (shared k x y z = 1 ∨ shared k x y z = 2)) :
    next x y z = m := by
  unfold next
  apply le_antisymm
  · exact Nat.sInf_le ⟨h1, h2⟩
  · refine le_csInf (s := {m : ℕ | z < m ∧ (shared m x y z = 1 ∨ shared m x y z = 2)})
      ⟨m, h1, h2⟩ ?_
    rintro b ⟨hb1, hb2⟩
    by_contra hlt
    exact h3 b hb1 (by omega) hb2

/-- The defining step of the sequence, as an equation. -/
theorem step (n : ℕ) : a (n + 4) = next (a (n + 1)) (a (n + 2)) (a (n + 3)) := by rw [a]

theorem t1 : a 1 = 1 := by simp [a]

theorem t2 : a 2 = 2 := by simp [a]

theorem t3 : a 3 = 3 := by simp [a]

theorem t4 : a 4 = 4 := by
  rw [step 0, t1, t2, t3]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t5 : a 5 = 8 := by
  rw [step 1, t2, t3, t4]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t6 : a 6 = 9 := by
  rw [step 2, t3, t4, t5]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t7 : a 7 = 10 := by
  rw [step 3, t4, t5, t6]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t8 : a 8 = 14 := by
  rw [step 4, t5, t6, t7]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t9 : a 9 = 15 := by
  rw [step 5, t6, t7, t8]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t10 : a 10 = 16 := by
  rw [step 6, t7, t8, t9]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t11 : a 11 = 21 := by
  rw [step 7, t8, t9, t10]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t12 : a 12 = 22 := by
  rw [step 8, t9, t10, t11]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t13 : a 13 = 26 := by
  rw [step 9, t10, t11, t12]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t14 : a 14 = 27 := by
  rw [step 10, t11, t12, t13]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t15 : a 15 = 28 := by
  rw [step 11, t12, t13, t14]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t16 : a 16 = 32 := by
  rw [step 12, t13, t14, t15]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t17 : a 17 = 33 := by
  rw [step 13, t14, t15, t16]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t18 : a 18 = 34 := by
  rw [step 14, t15, t16, t17]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t19 : a 19 = 38 := by
  rw [step 15, t16, t17, t18]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t20 : a 20 = 39 := by
  rw [step 16, t17, t18, t19]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t21 : a 21 = 40 := by
  rw [step 17, t18, t19, t20]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t22 : a 22 = 44 := by
  rw [step 18, t19, t20, t21]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t23 : a 23 = 45 := by
  rw [step 19, t20, t21, t22]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t24 : a 24 = 46 := by
  rw [step 20, t21, t22, t23]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t25 : a 25 = 51 := by
  rw [step 21, t22, t23, t24]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t26 : a 26 = 52 := by
  rw [step 22, t23, t24, t25]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t27 : a 27 = 56 := by
  rw [step 23, t24, t25, t26]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t28 : a 28 = 57 := by
  rw [step 24, t25, t26, t27]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t29 : a 29 = 58 := by
  rw [step 25, t26, t27, t28]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t30 : a 30 = 62 := by
  rw [step 26, t27, t28, t29]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t31 : a 31 = 63 := by
  rw [step 27, t28, t29, t30]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t32 : a 32 = 64 := by
  rw [step 28, t29, t30, t31]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t33 : a 33 = 68 := by
  rw [step 29, t30, t31, t32]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t34 : a 34 = 69 := by
  rw [step 30, t31, t32, t33]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t35 : a 35 = 70 := by
  rw [step 31, t32, t33, t34]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t36 : a 36 = 74 := by
  rw [step 32, t33, t34, t35]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t37 : a 37 = 75 := by
  rw [step 33, t34, t35, t36]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t38 : a 38 = 76 := by
  rw [step 34, t35, t36, t37]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t39 : a 39 = 81 := by
  rw [step 35, t36, t37, t38]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t40 : a 40 = 82 := by
  rw [step 36, t37, t38, t39]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t41 : a 41 = 86 := by
  rw [step 37, t38, t39, t40]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t42 : a 42 = 87 := by
  rw [step 38, t39, t40, t41]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t43 : a 43 = 88 := by
  rw [step 39, t40, t41, t42]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t44 : a 44 = 92 := by
  rw [step 40, t41, t42, t43]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t45 : a 45 = 93 := by
  rw [step 41, t42, t43, t44]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t46 : a 46 = 94 := by
  rw [step 42, t43, t44, t45]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t47 : a 47 = 98 := by
  rw [step 43, t44, t45, t46]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t48 : a 48 = 99 := by
  rw [step 44, t45, t46, t47]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t49 : a 49 = 100 := by
  rw [step 45, t46, t47, t48]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t50 : a 50 = 104 := by
  rw [step 46, t47, t48, t49]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t51 : a 51 = 105 := by
  rw [step 47, t48, t49, t50]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t52 : a 52 = 106 := by
  rw [step 48, t49, t50, t51]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t53 : a 53 = 111 := by
  rw [step 49, t50, t51, t52]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t54 : a 54 = 112 := by
  rw [step 50, t51, t52, t53]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t55 : a 55 = 116 := by
  rw [step 51, t52, t53, t54]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t56 : a 56 = 117 := by
  rw [step 52, t53, t54, t55]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t57 : a 57 = 118 := by
  rw [step 53, t54, t55, t56]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t58 : a 58 = 122 := by
  rw [step 54, t55, t56, t57]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t59 : a 59 = 123 := by
  rw [step 55, t56, t57, t58]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t60 : a 60 = 124 := by
  rw [step 56, t57, t58, t59]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t61 : a 61 = 128 := by
  rw [step 57, t58, t59, t60]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t62 : a 62 = 129 := by
  rw [step 58, t59, t60, t61]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t63 : a 63 = 130 := by
  rw [step 59, t60, t61, t62]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t64 : a 64 = 134 := by
  rw [step 60, t61, t62, t63]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t65 : a 65 = 135 := by
  rw [step 61, t62, t63, t64]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t66 : a 66 = 136 := by
  rw [step 62, t63, t64, t65]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t67 : a 67 = 141 := by
  rw [step 63, t64, t65, t66]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t68 : a 68 = 142 := by
  rw [step 64, t65, t66, t67]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t69 : a 69 = 146 := by
  rw [step 65, t66, t67, t68]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t70 : a 70 = 147 := by
  rw [step 66, t67, t68, t69]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t71 : a 71 = 148 := by
  rw [step 67, t68, t69, t70]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t72 : a 72 = 152 := by
  rw [step 68, t69, t70, t71]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t73 : a 73 = 153 := by
  rw [step 69, t70, t71, t72]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t74 : a 74 = 154 := by
  rw [step 70, t71, t72, t73]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t75 : a 75 = 158 := by
  rw [step 71, t72, t73, t74]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t76 : a 76 = 159 := by
  rw [step 72, t73, t74, t75]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t77 : a 77 = 160 := by
  rw [step 73, t74, t75, t76]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t78 : a 78 = 164 := by
  rw [step 74, t75, t76, t77]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t79 : a 79 = 165 := by
  rw [step 75, t76, t77, t78]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t80 : a 80 = 166 := by
  rw [step 76, t77, t78, t79]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t81 : a 81 = 171 := by
  rw [step 77, t78, t79, t80]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t82 : a 82 = 172 := by
  rw [step 78, t79, t80, t81]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t83 : a 83 = 176 := by
  rw [step 79, t80, t81, t82]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t84 : a 84 = 177 := by
  rw [step 80, t81, t82, t83]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t85 : a 85 = 178 := by
  rw [step 81, t82, t83, t84]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t86 : a 86 = 182 := by
  rw [step 82, t83, t84, t85]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t87 : a 87 = 183 := by
  rw [step 83, t84, t85, t86]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t88 : a 88 = 184 := by
  rw [step 84, t85, t86, t87]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t89 : a 89 = 188 := by
  rw [step 85, t86, t87, t88]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t90 : a 90 = 189 := by
  rw [step 86, t87, t88, t89]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t91 : a 91 = 190 := by
  rw [step 87, t88, t89, t90]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t92 : a 92 = 194 := by
  rw [step 88, t89, t90, t91]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t93 : a 93 = 195 := by
  rw [step 89, t90, t91, t92]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t94 : a 94 = 196 := by
  rw [step 90, t91, t92, t93]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t95 : a 95 = 201 := by
  rw [step 91, t92, t93, t94]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  interval_cases k <;> decide

theorem t96 : a 96 = 202 := by
  rw [step 92, t93, t94, t95]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

theorem t97 : a 97 = 203 := by
  rw [step 93, t94, t95, t96]
  refine next_eq (by decide) (by decide) ?_
  intro k hk1 hk2
  omega

end OMA.P079279

/-- The recurrence fails at n = 97: a(97) = 203, while a(96) + a(83) - a(82) = 206. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a079279.main) := by
  intro h
  have h97 := h 97 (by norm_num)
  norm_num [OMA.P079279.t97, OMA.P079279.t96, OMA.P079279.t83, OMA.P079279.t82] at h97
