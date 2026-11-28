import FormalConjectures.Wikipedia.WilfNumericalSemigroupConjecture

/-!
# Wilf's conjecture when the conductor is at most twice the multiplicity
Kaplan (J. Pure Appl. Algebra 216, 2012) proved Wilf's inequality whenever c(S) is at most 2 m(S),
where m(S) is the multiplicity (least positive element). `main` proves this case in full.
H1 is the range 2 m(S) < c(S) at most 3 m(S) (Eliahou, J. Eur. Math. Soc. 2018, known);
H2 is the open range 3 m(S) < c(S).
-/
namespace OMA.R_WilfNumericalSemigroupConjecture_wilf_numerical_semigroup_conjecture_R1

open AddSubmonoid WilfNumericalSemigroupConjecture

/-- Wilf's inequality when the conductor lies strictly above twice and at most three times
the multiplicity (Eliahou 2018). -/
def H1 : Prop :=
  ∀ S : AddSubmonoid ℕ, S.IsNumericalSemigroup →
    2 * sInf {x : ℕ | 0 < x ∧ x ∈ S} < S.conductor →
    S.conductor ≤ 3 * sInf {x : ℕ | 0 < x ∧ x ∈ S} →
    S.conductor ≤ S.embeddingDim * sporadicCount S

/-- Wilf's inequality when the conductor exceeds three times the multiplicity (open). -/
def H2 : Prop :=
  ∀ S : AddSubmonoid ℕ, S.IsNumericalSemigroup →
    3 * sInf {x : ℕ | 0 < x ∧ x ∈ S} < S.conductor →
    S.conductor ≤ S.embeddingDim * sporadicCount S

theorem main : H1 → H2 → type_of% @WilfNumericalSemigroupConjecture.wilf_numerical_semigroup_conjecture := by
  intro h1 h2 S hS
  classical
  set c := S.conductor with hc
  set m := sInf {x : ℕ | 0 < x ∧ x ∈ S} with hm
  by_cases hlarge : 2 * m < c
  · by_cases h3 : 3 * m < c
    · exact h2 S hS h3
    · exact h1 S hS hlarge (by omega)
  push Not at hlarge
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · rw [hc0]; exact Nat.zero_le _
  have hmem : ∀ y, c ≤ y → y ∈ S := fun y hy => hS.mem_of_conductor_le hy
  have hne : {x : ℕ | 0 < x ∧ x ∈ S}.Nonempty := ⟨c, hcpos, hmem c le_rfl⟩
  obtain ⟨hmpos, hmS⟩ : 0 < m ∧ m ∈ S := Nat.sInf_mem hne
  have hmin : ∀ x, 0 < x → x ∈ S → m ≤ x := fun x hx hxS => Nat.sInf_le ⟨hx, hxS⟩
  set A := (Finset.Ico m c).filter (· ∈ S) with hA
  set t := A.card with ht
  -- sporadic count
  have hn : sporadicCount S = t + 1 := by
    unfold sporadicCount
    have : (Finset.range c).filter (· ∈ S) = insert 0 A := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, hA, Finset.mem_Ico]
      constructor
      · rintro ⟨hx, hxS⟩
        rcases Nat.eq_zero_or_pos x with h0 | hpos
        · exact Or.inl h0
        · exact Or.inr ⟨⟨hmin x hpos hxS, hx⟩, hxS⟩
      · rintro (rfl | ⟨⟨_, hx⟩, hxS⟩)
        · exact ⟨hcpos, S.zero_mem⟩
        · exact ⟨hx, hxS⟩
    rw [← hc, this, Finset.card_insert_of_notMem]
    simp only [hA, Finset.mem_filter, Finset.mem_Ico]
    omega
  -- pair sums
  let f : Sym2 ℕ → ℕ := Sym2.lift ⟨fun a b => a + b, fun a b => Nat.add_comm a b⟩
  set B := (A.sym2.image f).filter (· < c + m) with hB
  have hBsub : B ⊆ Finset.Ico (2 * m) (c + m) := by
    intro y hy
    simp only [hB, Finset.mem_filter, Finset.mem_image] at hy
    obtain ⟨⟨z, hz, rfl⟩, hlt⟩ := hy
    induction z using Sym2.ind with
    | _ a b =>
      rw [Finset.mk_mem_sym2_iff] at hz
      simp only [hA, Finset.mem_filter, Finset.mem_Ico] at hz
      have hf : f s(a, b) = a + b := rfl
      rw [hf] at hlt ⊢
      rw [Finset.mem_Ico]
      omega
  have hBc : B.card ≤ c - m := by
    have := Finset.card_le_card hBsub
    simp only [Nat.card_Ico] at this
    omega
  have hBt : 2 * B.card ≤ t * (t + 1) := by
    have h1 : B.card ≤ A.sym2.card :=
      (Finset.card_filter_le _ _).trans Finset.card_image_le
    rw [Finset.card_sym2, Nat.choose_two_right] at h1
    have h2 := Nat.mul_div_le ((t + 1) * (t + 1 - 1)) 2
    simp only [Nat.add_sub_cancel] at h1 h2
    rw [← ht] at h1
    have hcomm : t * (t + 1) = (t + 1) * t := Nat.mul_comm _ _
    omega
  set C := Finset.Ico c (c + m) \ B with hC
  have hCcard : m - B.card ≤ C.card := by
    have := Finset.le_card_sdiff B (Finset.Ico c (c + m))
    simp only [Nat.card_Ico] at this
    rw [hC]; omega
  -- generators
  set G := {x : ℕ | 0 < x ∧ x ∈ S ∧
      ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ∈ S ∧ b ∈ S ∧ x = a + b} with hG
  have hGfin : G.Finite := by
    apply (Set.finite_Iio (c + m)).subset
    rintro x ⟨hx, hxS, hnot⟩
    simp only [Set.mem_Iio]
    by_contra hge
    exact hnot ⟨m, x - m, hmpos, by omega, hmS, hmem _ (by omega), by omega⟩
  have hAG : ∀ x ∈ A, x ∈ G := by
    intro x hx
    simp only [hA, Finset.mem_filter, Finset.mem_Ico] at hx
    refine ⟨by omega, hx.2, ?_⟩
    rintro ⟨a, b, ha, hb, haS, hbS, rfl⟩
    have := hmin a ha haS
    have := hmin b hb hbS
    omega
  have hCG : ∀ y ∈ C, y ∈ G := by
    intro y hy
    simp only [hC, Finset.mem_sdiff, Finset.mem_Ico] at hy
    obtain ⟨⟨hy1, hy2⟩, hyB⟩ := hy
    refine ⟨by omega, hmem y hy1, ?_⟩
    rintro ⟨a, b, ha, hb, haS, hbS, rfl⟩
    have hma := hmin a ha haS
    have hmb := hmin b hb hbS
    apply hyB
    simp only [hB, Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨s(a, b), ?_, rfl⟩, hy2⟩
    rw [Finset.mk_mem_sym2_iff]
    simp only [hA, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨⟨hma, by omega⟩, haS⟩, ⟨⟨hmb, by omega⟩, hbS⟩⟩
  have hdisj : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    simp only [hA, Finset.mem_filter, Finset.mem_Ico] at hxA
    simp only [hC, Finset.mem_sdiff, Finset.mem_Ico] at hxC
    omega
  have he : t + (m - B.card) ≤ S.embeddingDim := by
    have hsub : ((A ∪ C : Finset ℕ) : Set ℕ) ⊆ G := by
      intro x hx
      rw [Finset.coe_union, Set.mem_union] at hx
      rcases hx with hx | hx
      · exact hAG x hx
      · exact hCG x hx
    have := Set.ncard_le_ncard hsub hGfin
    rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj] at this
    unfold embeddingDim
    rw [← hG]
    omega
  rw [hn]
  -- arithmetic
  by_cases hmc : m < c
  · have hmA : m ∈ A := by
      simp only [hA, Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨le_rfl, hmc⟩, hmS⟩
    have ht1 : 1 ≤ t := Finset.card_pos.mpr ⟨m, hmA⟩
    obtain ⟨k, hk⟩ : ∃ k, k + B.card = m := ⟨m - B.card, by omega⟩
    have hke : t + k ≤ S.embeddingDim := by omega
    nlinarith
  · push Not at hmc
    have : m ≤ S.embeddingDim := by
      have : B.card = 0 := by omega
      omega
    nlinarith

end OMA.R_WilfNumericalSemigroupConjecture_wilf_numerical_semigroup_conjecture_R1
