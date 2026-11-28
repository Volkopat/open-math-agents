import OMAStatements.S_oeis_a129149

-- Problem: A129149: Permutations with exactly 7 fixed points.
-- Credit: @ricnov (the owner of the agent is credited as the solver)
--
-- Idea: a permutation with fixed-point set exactly S is a derangement of the complement of S, so
-- a(n) = C(n,7) * D(n-7) with D the derangement numbers; Mathar's recurrence then follows from
-- D(m+2) = (m+1) * (D(m) + D(m+1)) and two binomial identities.

/-- Permutations of `Fin n` whose set of fixed points is exactly `S` are counted by the derangement
number of the size of the complement of `S`. -/
lemma OMA.card_fixed_eq (n : ℕ) (S : Finset (Fin n)) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter fun i : Fin n => σ i = i) = S).card = numDerangements (n - S.card) := by
  classical
  have hcard : Fintype.card {a : Fin n // a ∉ S} = n - S.card := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [← hcard, ← card_derangements_eq_numDerangements, ← Fintype.card_subtype]
  refine Fintype.card_congr (Equiv.trans (Equiv.subtypeEquivRight fun σ => ?_)
    (derangements.subtypeEquiv fun a : Fin n => a ∉ S).symm)
  simp only [Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and, not_not,
    Function.mem_fixedPoints, Function.IsFixedPt]
  exact forall_congr' fun a => iff_comm

/-- The terms of A129149 in closed form: choose the seven fixed points, derange the rest. -/
lemma OMA.a_eq (n : ℕ) :
    OMA.S_oeis_a129149.a n = n.choose 7 * numDerangements (n - 7) := by
  classical
  unfold OMA.S_oeis_a129149.a
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm (Fin n) => Finset.univ.filter fun i : Fin n => σ i = i)
    (t := Finset.powersetCard 7 Finset.univ)]
  · rw [Finset.sum_congr rfl (g := fun _ => numDerangements (n - 7))]
    · simp [Finset.card_powersetCard]
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      rw [Finset.filter_filter]
      have h : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
          (Finset.univ.filter fun i : Fin n => σ i = i).card = 7 ∧
            (Finset.univ.filter fun i : Fin n => σ i = i) = S) =
          Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
            (Finset.univ.filter fun i : Fin n => σ i = i) = S := by
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hS.2, h⟩⟩
      rw [h, OMA.card_fixed_eq, hS.2]
  · intro σ hσ
    have hσ' : (Finset.univ.filter fun i : Fin n => σ i = i).card = 7 := by simpa using hσ
    simpa [Finset.mem_powersetCard] using hσ'

theorem OMA.solution : type_of% @OMA.S_oeis_a129149.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  rw [OMA.a_eq, OMA.a_eq, OMA.a_eq]
  have e1 : m + 9 - 1 = m + 8 := by omega
  have e2 : m + 9 - 2 = m + 7 := by omega
  have e3 : m + 9 - 7 = m + 2 := by omega
  have e4 : m + 8 - 7 = m + 1 := by omega
  have e5 : m + 7 - 7 = m := by omega
  rw [e1, e2, e3, e4, e5, numDerangements_add_two]
  have h1 : ((m + 8).choose 7 : ℤ) * ((m : ℤ) + 9) = ((m + 9).choose 7 : ℤ) * ((m : ℤ) + 2) := by
    have h := Nat.choose_mul_succ_eq (m + 8) 7
    have e : m + 8 + 1 - 7 = m + 2 := by omega
    rw [e] at h
    exact_mod_cast h
  have h2 : ((m + 7).choose 7 : ℤ) * ((m : ℤ) + 8) = ((m + 8).choose 7 : ℤ) * ((m : ℤ) + 1) := by
    have h := Nat.choose_mul_succ_eq (m + 7) 7
    have e : m + 7 + 1 - 7 = m + 1 := by omega
    rw [e] at h
    exact_mod_cast h
  push_cast
  linear_combination
    (((m : ℤ) + 1) * ((numDerangements (m + 1) : ℤ) + (numDerangements m : ℤ))) * h1
      + (((m : ℤ) + 9) * (numDerangements m : ℤ)) * h2
