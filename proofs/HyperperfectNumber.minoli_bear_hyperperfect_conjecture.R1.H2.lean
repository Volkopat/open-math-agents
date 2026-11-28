import OMAReductions.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1

-- Step HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1.H2: hypothesis H2 of reduction HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1
-- Credit: @Raimo33

/-! Witness n = 21, checked by the upstream lemma `isHyperperfect_small_examples`. -/

theorem OMA.solution : OMA.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1.H2 :=
  ⟨21, HyperperfectNumber.isHyperperfect_small_examples.2.2.1⟩
