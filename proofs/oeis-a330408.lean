import OMAStatements.S_oeis_a330408

namespace OMA.S_oeis_a330408


lemma A_one (k : ℕ) : A 1 k = k := by simp [A, lm]


/-- The conjecture: the main diagonal `A(n,n)`, `n ≥ 1`, is A166447. -/
def Conjecture : Prop := ∀ n : ℕ, 1 ≤ n → (A n n : ℤ) = b n

lemma A_19 : A 19 19 = 95 := by decide

lemma b_19 : b 19 = 76 := by
  have hlo : (7 / 2 : ℝ) ≤ Real.sqrt 19 := by
    rw [show (7 / 2 : ℝ) = Real.sqrt ((7 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hhi : Real.sqrt 19 < 9 / 2 := by
    rw [show (9 / 2 : ℝ) = Real.sqrt ((9 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hr : round (Real.sqrt 19) = 4 := by
    rw [round_eq, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  unfold b
  push_cast
  rw [hr]
  norm_num

theorem disproof : ¬ Conjecture := by
  intro h
  have := h 19 (by norm_num)
  rw [A_19, b_19] at this
  norm_num at this

/-- Controls: the table rows of the entry's example, and the diagonal through `n = 6`. -/
example : A 2 2 = 2 ∧ A 3 3 = 6 ∧ A 4 4 = 8 ∧ A 5 5 = 10 ∧ A 6 6 = 12 ∧ A 9 7 = 27 ∧ A 4 13 = 16 ∧
    A 18 18 = 72 ∧ A 20 20 = 100 := by
  decide

end OMA.S_oeis_a330408

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a330408.main) :=
  OMA.S_oeis_a330408.disproof
