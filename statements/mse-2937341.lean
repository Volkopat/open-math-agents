import Mathlib

/-!
# Well-behaved finitely additive measure on $\mathbb{Q}$

Source: https://math.stackexchange.com/questions/2937341/is-there-a-well-behaved-finitely-additive-measure-on-mathbbq
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Does there exist a set function $m : \mathcal{P}(\mathbb{Q}) \to [0, \infty]$ satisfying:
1. $m(\emptyset) = 0$,
2. $m(\mathbb{Q}) = \infty$,
3. $m(\{q\}) = 0$ for every $q \in \mathbb{Q}$,
4. $m((a, b) \cap \mathbb{Q}) = b - a$ for all $a, b \in \mathbb{R}$ with $a < b$,
5. $m$ is finitely additive on disjoint sets,
6. $m$ is monotone ($A \subseteq B \implies m(A) \le m(B)$),
7. $m$ is translation-invariant ($m(A + t) = m(A)$ for all $t \in \mathbb{Q}$)?
-/

namespace OMA.S_mse_2937341

theorem main :
    ∃ m : Set ℚ → ENNReal,
      m ∅ = 0 ∧
      m Set.univ = ⊤ ∧
      (∀ q : ℚ, m {q} = 0) ∧
      (∀ a b : ℝ, a < b →
        m {q : ℚ | a < (q : ℝ) ∧ (q : ℝ) < b} = ENNReal.ofReal (b - a)) ∧
      (∀ A B : Set ℚ, Disjoint A B → m (A ∪ B) = m A + m B) ∧
      (∀ A B : Set ℚ, A ⊆ B → m A ≤ m B) ∧
      (∀ (A : Set ℚ) (t : ℚ), m ((· + t) '' A) = m A) := by
  sorry

end OMA.S_mse_2937341
