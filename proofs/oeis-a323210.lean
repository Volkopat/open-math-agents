import OMAStatements.S_oeis_a323210
import Mathlib
-- Credit: @ptc-prover-bot

namespace A323210Proof

open OMA.S_oeis_a323210

/-- Jacobsthal value attached to a pair state: `J (k+1)` for state `2`, `J k` otherwise. -/
def jw (k : ℕ) (a : PairState) : ℕ := if a = 2 then jacobsthal (k + 1) else jacobsthal k

lemma step (m : ℕ) (p : PairState) :
    ∑ a : PairState, (if pairOK p a = true then 3 * jw (m + 1) a else 0)
      = 3 * jw (m + 2) p := by
  fin_cases p <;> simp [Fin.sum_univ_three, pairOK, jw, jacobsthal]
  all_goals ring

lemma closed (m : ℕ) (p : Column) :
    completions (m + 1) p = (3 * jw (m + 1) p.1) * (3 * jw (m + 1) p.2) := by
  induction m generalizing p with
  | zero =>
    obtain ⟨a, b⟩ := p
    fin_cases a <;> fin_cases b <;> simp [completions, jw, jacobsthal]
  | succ m ih =>
    obtain ⟨p1, p2⟩ := p
    have h : completions (m + 1 + 1) (p1, p2) = ∑ a : PairState, ∑ b : PairState,
        (if pairOK p1 a = true then 3 * jw (m + 1) a else 0) *
        (if pairOK p2 b = true then 3 * jw (m + 1) b else 0) := by
      rw [completions]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [ih (a, b)]
      by_cases h1 : pairOK p1 a = true <;> by_cases h2 : pairOK p2 b = true <;> simp [h1, h2]
    rw [h, ← Finset.sum_mul_sum, step, step]

end A323210Proof

open OMA.S_oeis_a323210 in
theorem A323210Proof.main' : ∀ n : ℕ, 1 ≤ n → arrays n = 9*(jacobsthal (n+1))^2 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [arrays, A323210Proof.closed]
  simp [A323210Proof.jw]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a323210.main := A323210Proof.main'

