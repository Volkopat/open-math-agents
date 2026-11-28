import OMAStatements.S_oeis_a134558

-- Problem: A134558: Array read by antidiagonals, a(n,k) = gamma(n+1,k)*e^k, where gamma(n,k) is the upper incomplete gamma function and e is the exponential constant 2.71828...
-- Upstream: formal-conjectures statements/oeis-a134558.lean:0 (declaration OMA.S_oeis_a134558.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the entry (sigma i, i) of the matrix is (if sigma i = i then k else 0) + 1, so the
-- product over i expands into the sum, over the subsets t of Fin n fixed pointwise by sigma, of
-- k^|t|. Exchanging the sums, the permutations fixing t pointwise are the permutations of the
-- complement of t, (n - |t|)! of them. Grouping the subsets by size gives
-- Sum_j binomial(n,j) (n-j)! k^j, which is the defining sum read backwards.

namespace S07A134558

open OMA.S_oeis_a134558 Finset

theorem prod_expand (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∏ i, (if σ i = i then k + 1 else 1) =
      ∑ t ∈ (univ : Finset (Fin n)).powerset, (if (∀ i ∈ t, σ i = i) then k ^ t.card else 0) := by
  have h1 : ∏ i, (if σ i = i then k + 1 else 1) =
      ∏ i ∈ (univ : Finset (Fin n)), ((if σ i = i then k else 0) + 1) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : σ i = i
    · simp [h]
    · simp [h]
  rw [h1, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_const_one, mul_one]
  by_cases hc : ∀ i ∈ t, σ i = i
  · rw [if_pos hc, ← Finset.prod_const]
    exact Finset.prod_congr rfl (fun i hi => if_pos (hc i hi))
  · rw [if_neg hc]
    have hex : ∃ i ∈ t, ¬ σ i = i := by
      by_contra hcon
      apply hc
      intro i hi
      by_contra h
      exact hcon ⟨i, hi, h⟩
    obtain ⟨i, hi, hne⟩ := hex
    exact Finset.prod_eq_zero hi (if_neg hne)

theorem card_fix (n : ℕ) (t : Finset (Fin n)) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ t, σ i = i)).card =
      (n - t.card).factorial := by
  have hq : ∀ σ : Equiv.Perm (Fin n), (∀ i ∈ t, σ i = i) ↔ (∀ a, ¬ (a ∉ t) → σ a = a) :=
    fun σ => ⟨fun h a ha => h a (not_not.mp ha), fun h a ha => h a (not_not.mpr ha)⟩
  have e : {σ : Equiv.Perm (Fin n) // ∀ i ∈ t, σ i = i} ≃ Equiv.Perm {i : Fin n // i ∉ t} :=
    (Equiv.subtypeEquivRight hq).trans (Equiv.Perm.subtypeEquivSubtypePerm (fun i => i ∉ t)).symm
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_perm,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]

theorem main_proof (n k : ℕ) : (M n k).permanent = a n k := by
  have h0 : (M n k).permanent =
      ∑ σ : Equiv.Perm (Fin n), ∏ i, (if σ i = i then k + 1 else 1) := rfl
  have h2 : ∑ σ : Equiv.Perm (Fin n), ∏ i, (if σ i = i then k + 1 else 1) =
      ∑ σ : Equiv.Perm (Fin n), ∑ t ∈ (univ : Finset (Fin n)).powerset,
        (if (∀ i ∈ t, σ i = i) then k ^ t.card else 0) :=
    Finset.sum_congr rfl (fun σ _ => prod_expand n k σ)
  have h3 : ∑ σ : Equiv.Perm (Fin n), ∑ t ∈ (univ : Finset (Fin n)).powerset,
        (if (∀ i ∈ t, σ i = i) then k ^ t.card else 0) =
      ∑ t ∈ (univ : Finset (Fin n)).powerset, ∑ σ : Equiv.Perm (Fin n),
        (if (∀ i ∈ t, σ i = i) then k ^ t.card else 0) := Finset.sum_comm
  have h4 : ∑ t ∈ (univ : Finset (Fin n)).powerset, ∑ σ : Equiv.Perm (Fin n),
        (if (∀ i ∈ t, σ i = i) then k ^ t.card else 0) =
      ∑ t ∈ (univ : Finset (Fin n)).powerset, (n - t.card).factorial * k ^ t.card := by
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, card_fix]
  have h5 : ∑ t ∈ (univ : Finset (Fin n)).powerset, (n - t.card).factorial * k ^ t.card =
      ∑ j ∈ range ((univ : Finset (Fin n)).card + 1),
        ((univ : Finset (Fin n)).card).choose j • ((n - j).factorial * k ^ j) :=
    Finset.sum_powerset_apply_card (fun j => (n - j).factorial * k ^ j)
  have h6 : ∑ j ∈ range (n + 1), n.choose j • ((n - j).factorial * k ^ j) =
      ∑ j ∈ range (n + 1), (n + 1 - 1 - j).factorial * n.choose (n + 1 - 1 - j) *
        k ^ (n - (n + 1 - 1 - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ n := by
      rw [Finset.mem_range] at hj
      omega
    rw [show n + 1 - 1 - j = n - j by omega, Nat.choose_symm hj', show n - (n - j) = j by omega,
      smul_eq_mul]
    ring
  rw [h0, h2, h3, h4, h5, Finset.card_univ, Fintype.card_fin, h6]
  exact Finset.sum_range_reflect (fun m => m.factorial * n.choose m * k ^ (n - m)) (n + 1)

end S07A134558

theorem OMA.solution : type_of% @OMA.S_oeis_a134558.main :=
  fun n k => S07A134558.main_proof n k