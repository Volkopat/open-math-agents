import FormalConjectures.ErdosProblems.«338»
import Mathlib.Combinatorics.Additive.Corner.Roth

open Finset Filter Erdos338

theorem OMA.solution : type_of% @Erdos338.erdos_338.variants.kelly_lowerDensity := by
  classical
  intro A hA hd
  have hrep3 {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hab : a ≠ b) (hac : a ≠ c)
      (hbc : b ≠ c) : ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ 3 ∧ ∑ x ∈ S, x = a + b + c := by
    have h : a ∉ ({b, c} : Finset ℕ) := by simp [hab, hac]
    exact ⟨{a, b, c}, by simp [ha, hb, hc], by rw [card_insert_of_notMem h]; simp [hbc],
      by rw [sum_insert h]; simp [hbc, add_assoc]⟩
  have hdens : ∀ᶠ m in atTop, A.lowerDensity / 2 < A.partialDensity Set.univ m :=
    eventually_lt_of_lt_liminf (by change A.lowerDensity / 2 < A.lowerDensity; linarith)
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun _ => by positivity))
  have hroth : ∀ᶠ m in atTop, (rothNumberNat m : ℝ) ≤ A.lowerDensity / 4 * m := by
    simpa only [Real.norm_natCast] using
      rothNumberNat_isLittleO_id.def (by positivity : 0 < A.lowerDensity / 4)
  obtain ⟨m, hm, hdm, hrm⟩ := ((eventually_gt_atTop (0 : ℕ)).and (hdens.and hroth)).exists
  let S := (range m).filter (· ∈ A)
  have hcard : (A ∩ Set.Iio m).ncard = S.card := by
    rw [← show (S : Set ℕ) = A ∩ Set.Iio m by ext a; simp [S, and_comm], Set.ncard_coe_finset]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio, hcard] at hdm
  have hdense : 2 * rothNumberNat m < S.card := by
    have := (lt_div_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm)).mp hdm
    exact_mod_cast (show (2 : ℝ) * rothNumberNat m < S.card by linarith)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hA
  refine eventually_atTop.mpr ⟨3 * m + M + 1, fun n hn => ?_⟩
  by_contra hbad
  let P (a : ℕ) := n - 2 * a ∈ A
  let X := S.filter P
  let Y := S.filter (fun a => ¬ P a)
  have hY (a : ℕ) (ha : a ∈ Y) : a < m ∧ a ∈ A ∧ ∃ b ∈ A, b + b = n - a := by
    obtain ⟨haS, hnP⟩ := mem_filter.mp ha
    have ⟨ham, haA⟩ : a < m ∧ a ∈ A := by simpa [S] using haS
    refine ⟨ham, haA, ?_⟩
    obtain ⟨T, hT, hc, hs⟩ := hM (n - a) (by omega)
    rcases (by omega : T.card = 0 ∨ T.card = 1 ∨ T.card = 2) with h0 | h1 | h2
    · simp [Multiset.card_eq_zero.mp h0] at hs; omega
    · obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp h1; simp at hT hs
      exact (hbad ⟨{a, b}, by simp [haA, hT], by simp [show a ≠ b by omega],
        by simp [show a ≠ b by omega]; omega⟩).elim
    · obtain ⟨b, c, rfl⟩ := Multiset.card_eq_two.mp h2
      have hb := hT b (by simp); have hc' := hT c (by simp)
      have hbc : b + c = n - a := by simpa using hs
      by_cases hab : a = b
      · exact (hnP (by dsimp [P]; rwa [show n - 2 * a = c by omega])).elim
      by_cases hac : a = c
      · exact (hnP (by dsimp [P]; rwa [show n - 2 * a = b by omega])).elim
      by_cases hbc' : b = c
      · exact ⟨b, hb, by omega⟩
      · exact (hbad ((show a + b + c = n by omega) ▸ hrep3 haA hb hc' hab hac hbc')).elim
  have hXfree : ThreeAPFree (X : Set ℕ) := by
    intro a ha b hb c hc habc; by_contra hab
    obtain ⟨haS, _⟩ := mem_filter.mp ha; obtain ⟨hbS, hnb⟩ := mem_filter.mp hb
    obtain ⟨hcS, _⟩ := mem_filter.mp hc
    simp only [S, mem_filter, mem_range] at haS hbS hcS
    exact hbad ((show a + c + (n - 2 * b) = n by omega) ▸
      hrep3 haS.2 hcS.2 hnb (by omega) (by omega) (by omega))
  have hYfree : ThreeAPFree (Y : Set ℕ) := by
    intro a ha b hb c hc habc; by_contra hab
    obtain ⟨_, _, x, hxA, hx⟩ := hY a ha; obtain ⟨_, hbA, _⟩ := hY b hb
    obtain ⟨_, _, y, hyA, hy⟩ := hY c hc
    exact hbad ((show b + x + y = n by omega) ▸
      hrep3 hbA hxA hyA (by omega) (by omega) (by omega))
  have := hXfree.le_rothNumberNat X (fun a ha => mem_range.mp (mem_filter.mp (mem_filter.mp ha).1).1) rfl
  have := hYfree.le_rothNumberNat Y (fun a ha => (hY a ha).1) rfl
  have : X.card + Y.card = S.card := card_filter_add_card_filter_not (s := S) P
  omega
