import OMAStatements.S_oeis_a161869

-- Problem: OEIS A161869, the proposed identification of the first column of the infinite
-- product of aerated Pascal matrices with the binomial transform of A024493 interleaved
-- with zeros.
-- Disproof: the two sides first differ at n = 24, where a(24) = 258566402 while the
-- transform gives 258566401 (P. Bala, OEIS A161869, Jul 07 2015: further terms show the
-- conjecture is incorrect).
-- The well-founded recursion is evaluated through an equal fuelled structural copy.

namespace OMA.A161869Proof

open OMA.S_oeis_a161869

/-- Structural copy of `columnTail` with fuel. -/
def ct : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, k, n =>
    if n = 0 then 1
    else if 2 ≤ k then
      if n % k = 0 then ∑ j : Fin (n / k + 1), (n / k).choose j.val * ct f (k + 1) j.val
      else 0
    else 0

lemma ct_eq : ∀ f k n : ℕ, n < f → ct f k n = columnTail k n
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, k, n, h => by
    rw [columnTail, ct]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn, dif_neg hn]
      by_cases hk : 2 ≤ k
      · rw [if_pos hk, dif_pos hk]
        by_cases hm : n % k = 0
        · rw [if_pos hm, if_pos hm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have hdiv : n / k < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
          have hj : j.val < f := by
            have := j.isLt
            omega
          rw [ct_eq f (k + 1) j.val hj]
        · rw [if_neg hm, if_neg hm]
      · rw [if_neg hk, dif_neg hk]

lemma a24 : a 24 = 258566402 := by
  have : a 24 = ∑ j ∈ Finset.range 25, (24 : ℕ).choose j * ct 30 2 j := by
    rw [a]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [ct_eq 30 2 j (by simp at hj; omega)]
  rw [this]
  decide +kernel

lemma t24 : transform 24 = 258566401 := by
  decide +kernel

end OMA.A161869Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a161869.main) := by
  intro h
  have := h 24
  rw [OMA.A161869Proof.a24, OMA.A161869Proof.t24] at this
  norm_num at this
