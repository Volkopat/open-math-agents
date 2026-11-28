import FormalConjectures.OEIS.«108569»

open OeisA108569

-- Reuse the odd witness from the existing disproof.
set_option maxRecDepth 10000 in
theorem OMA.disproof : ¬ (type_of% @OeisA108569.conjecture) := by
  intro h
  have ht : Nat.totient 5095354107 = 3393612288 := by
    rw [Nat.totient_eq_div_primeFactors_mul]
    decide +kernel
  have ha : A 5095354107 := by
    refine ⟨by decide, ?_⟩
    rw [ht]
    change 3393612288 = Nat.totient 8488966395
    rw [Nat.totient_eq_div_primeFactors_mul]
    decide +kernel
  have hp : 0 < Nat.count A 5095354107 :=
    lt_of_lt_of_le (show 0 < Nat.count A 2 by decide)
      (Nat.count_monotone _ (by decide : 2 ≤ 5095354107))
  have he := h _ hp
  change Even (Nat.nth A (Nat.count A 5095354107)) at he
  rw [Nat.nth_count ha] at he
  exact (by decide : ¬ Even (5095354107 : ℕ)) he
