import FormalConjectures.ErdosProblems.«849»
import Mathlib

/-! Reduce exact multiplicities above the four known cases to two questions
    about finite lists of witnesses. In the second question, the smaller
    coefficient is allowed to have further representations of its own. -/

namespace OMA.R_Erdos849_erdos_849_R1

private theorem column_mono {n i j : ℕ} (hij : i ≤ j) (hj : 2 * j ≤ n) :
    n.choose i ≤ n.choose j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem finite_rows (a : ℕ) :
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.Finite := by
  apply (Set.finite_Iic a).subset
  rintro n ⟨k, hk, hkn, rfl⟩
  simpa using column_mono hk hkn

/-- An exact finite rectangle for each small witness, including its edge. -/
private theorem small_rectangle {a r c : ℕ} (ha : 2 ≤ a)
    (hr : a < r.choose 2) (hc : a < (2 * c).choose c) :
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a} =
      (↑(insert a ((Finset.range r).filter fun n =>
        ∃ k ∈ Finset.range c, 2 ≤ k ∧ 2 * k ≤ n ∧
          n.descFactorial k / k.factorial = a)) : Set ℕ) := by
  ext n
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_filter, Finset.mem_range, ← Nat.choose_eq_descFactorial_div_factorial]
  constructor
  · rintro ⟨k, hk, hkn, heq⟩
    by_cases h : k = 1
    · subst k
      exact Or.inl (by simpa using heq)
    · have hk2 : 2 ≤ k := by omega
      right
      constructor
      · by_contra! hn
        have := (Nat.choose_le_choose 2 hn).trans (column_mono hk2 hkn)
        omega
      · refine ⟨k, ?_, hk2, hkn, heq⟩
        by_contra! hck
        have hnc : 2 * c ≤ n := by omega
        have := (Nat.choose_le_choose c hnc).trans (column_mono hck hkn)
        omega
  · rintro (rfl | ⟨_, k, _, hk, hkn, heq⟩)
    · exact ⟨1, by decide, by omega, by simp⟩
    · exact ⟨k, by omega, hkn, heq⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem first_four (t : ℕ) (h₁ : 1 ≤ t) (h₄ : t ≤ 4) :
    ∃ a : ℕ, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.ncard = t := by
  interval_cases t
  · refine ⟨2, ?_⟩
    rw [small_rectangle (r := 3) (c := 2) (by decide) (by decide) (by decide),
      Set.ncard_coe_finset]
    decide
  · refine ⟨6, ?_⟩
    rw [small_rectangle (r := 5) (c := 3) (by decide) (by decide) (by decide),
      Set.ncard_coe_finset]
    decide
  · refine ⟨120, ?_⟩
    rw [small_rectangle (r := 17) (c := 5) (by decide) (by decide) (by decide),
      Set.ncard_coe_finset]
    decide
  · refine ⟨3003, ?_⟩
    rw [small_rectangle (r := 79) (c := 7) (by decide)
      (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide)
      (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide), Set.ncard_coe_finset]
    decide

/-- Arbitrarily large finite sets of distinct rows share a coefficient. -/
def H1 : Prop := ∀ t : ℕ, 5 ≤ t → ∃ (a : ℕ) (s : Finset ℕ), t ≤ s.card ∧
  ∀ n ∈ s, ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a

/-- From any t+1 witnessed rows, descend in coefficient value while retaining
    at least t witnessed rows. Both sides can be certified by listing rows. -/
def H2 : Prop := ∀ (t a : ℕ) (s : Finset ℕ), 5 ≤ t → t < s.card →
  (∀ n ∈ s, ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a) →
  ∃ (b : ℕ) (u : Finset ℕ), b < a ∧ t ≤ u.card ∧
    ∀ n ∈ u, ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = b

theorem main : H1 → H2 → type_of% @Erdos849.erdos_849 := by
  classical
  intro unbounded descend t ht
  by_cases hsmall : t ≤ 4
  · exact first_four t ht hsmall
  have hlarge : 5 ≤ t := by omega
  let rows (a : ℕ) : Set ℕ := {n | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}
  let witnessed (a : ℕ) : Prop := ∃ s : Finset ℕ, t ≤ s.card ∧ ∀ n ∈ s, n ∈ rows a
  have exists_value : ∃ a, witnessed a := unbounded t hlarge
  let a := Nat.find exists_value
  obtain ⟨s, hcount, hs⟩ := Nat.find_spec exists_value
  have hfin : (rows a).Finite := finite_rows a
  have hlower : t ≤ (rows a).ncard := by
    have hsub : (↑s : Set ℕ) ⊆ rows a := fun n hn => hs n hn
    exact hcount.trans (by simpa using Set.ncard_le_ncard hsub hfin)
  refine ⟨a, le_antisymm ?_ hlower⟩
  change (rows a).ncard ≤ t
  by_contra! hextra
  let u := hfin.toFinset
  have hcard : (rows a).ncard = u.card := Set.ncard_eq_toFinset_card _ hfin
  have hmore : t < u.card := hcard ▸ hextra
  obtain ⟨b, v, hba, hv, hrows⟩ := descend t a u hlarge hmore
    (fun n hn => hfin.mem_toFinset.mp hn)
  exact (Nat.find_min exists_value hba) ⟨v, hv, hrows⟩

end OMA.R_Erdos849_erdos_849_R1
