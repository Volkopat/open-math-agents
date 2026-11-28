import OMAStatements.S_mo_464279
import Mathlib
open OMA.S_mo_464279
open Polynomial

/-- Number of ordered pairs `(a, b)` with `a + b = j` and `a, b ∈ S`. -/
def rr (S : Finset ℕ) (j : ℕ) : ℕ :=
  ((Finset.HasAntidiagonal.antidiagonal j).filter fun p => p.1 ∈ S ∧ p.2 ∈ S).card

lemma coeff_poly (S : Finset ℕ) (a : ℕ) : (poly S).coeff a = if a ∈ S then 1 else 0 := by
  simp [poly, Polynomial.coeff_X_pow]

lemma coeff_sq (S : Finset ℕ) (j : ℕ) : ((poly S) ^ 2).coeff j = (rr S j : ℤ) := by
  rw [pow_two, Polynomial.coeff_mul]
  simp only [coeff_poly]
  rw [rr, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  by_cases h1 : x.1 ∈ S <;> by_cases h2 : x.2 ∈ S <;> simp [h1, h2]

lemma thick_iff (S : Finset ℕ) (n : ℕ) (hn : 1 ≤ n) :
    thickness (poly S) = n ↔ (∀ j, rr S j ≤ n) ∧ ∃ j, rr S j = n := by
  have hc : ∀ j, ((poly S ^ 2).coeff j).natAbs = rr S j := by
    intro j; rw [coeff_sq]; simp
  unfold thickness
  simp only [hc]
  constructor
  · intro h
    constructor
    · intro j
      by_cases hj : j ∈ (poly S ^ 2).support
      · rw [← h]; exact Finset.le_sup (f := fun j => rr S j) hj
      · rw [Polynomial.mem_support_iff, not_not, coeff_sq] at hj
        have : rr S j = 0 := by exact_mod_cast hj
        omega
    · have hne : (poly S ^ 2).support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.sup_empty] at h
        simp at h
        omega
      obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup _ hne (fun j => rr S j)
      exact ⟨j, by rw [← hj, h]⟩
  · rintro ⟨h1, j, hj⟩
    apply le_antisymm
    · exact Finset.sup_le fun i _ => h1 i
    · have hmem : j ∈ (poly S ^ 2).support := by
        rw [Polynomial.mem_support_iff, coeff_sq]
        exact_mod_cast (by omega : rr S j ≠ 0)
      rw [← hj]
      exact Finset.le_sup (f := fun j => rr S j) hmem

lemma rr_le_card (S : Finset ℕ) (j : ℕ) : rr S j ≤ S.card := by
  unfold rr
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_filter] at hp
    exact hp.2.1
  · intro p hp q hq hpq
    have hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).1
    have hq' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).1
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp' hq'
    have hpq' : p.1 = q.1 := hpq
    ext
    · exact hpq'
    · omega

lemma rr_eq_card_iff (S : Finset ℕ) (j : ℕ) :
    rr S j = S.card ↔ ∀ a ∈ S, a ≤ j ∧ j - a ∈ S := by
  set F := (Finset.HasAntidiagonal.antidiagonal j).filter fun p => p.1 ∈ S ∧ p.2 ∈ S with hF
  have hinj : Set.InjOn Prod.fst (F : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).1
    have hq' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).1
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp' hq'
    have hpq' : p.1 = q.1 := hpq
    ext
    · exact hpq'
    · omega
  have himg : F.image Prod.fst ⊆ S := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    rw [hF, Finset.mem_filter] at hp
    exact hp.2.1
  have hcard : (F.image Prod.fst).card = rr S j := Finset.card_image_of_injOn hinj
  constructor
  · intro h a ha
    have heq : F.image Prod.fst = S :=
      Finset.eq_of_subset_of_card_le himg (by rw [hcard, h])
    rw [← heq, Finset.mem_image] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    rw [hF, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    refine ⟨by omega, ?_⟩
    rw [show j - p.1 = p.2 by omega]
    exact hp.2.2
  · intro h
    have heq : F.image Prod.fst = S := by
      apply Finset.Subset.antisymm himg
      intro a ha
      obtain ⟨h1, h2⟩ := h a ha
      rw [Finset.mem_image]
      refine ⟨(a, j - a), ?_, rfl⟩
      rw [hF, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
      exact ⟨by simp only; omega, ha, h2⟩
    rw [← hcard, heq]

/-- The admissible missing exponents. -/
def Z (n : ℕ) : Finset ℕ := if Even n then {0, n, n / 2} else {0, n}

lemma memZ (n z : ℕ) : z ∈ Z n ↔ z = 0 ∨ z = n ∨ (Even n ∧ z = n / 2) := by
  unfold Z
  split_ifs with h
  · simp [h]
  · simp [h]

lemma char (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ) (hS : S ⊆ Finset.range (n + 1)) :
    thickness (poly S) = n ↔ ∃ z ∈ Z n, S = (Finset.range (n + 1)).erase z := by
  rw [thick_iff S n hn]
  constructor
  · rintro ⟨h1, j, hj⟩
    have hc1 : n ≤ S.card := hj ▸ rr_le_card S j
    have hc2 : S.card ≤ n + 1 := by
      have := Finset.card_le_card hS
      simpa using this
    have hc3 : S.card ≠ n + 1 := by
      intro hc
      have hSr : S = Finset.range (n + 1) :=
        Finset.eq_of_subset_of_card_le hS (by simp [hc])
      have : rr S n = S.card := by
        rw [rr_eq_card_iff]
        intro a ha
        rw [hSr, Finset.mem_range] at ha ⊢
        omega
      have := h1 n
      omega
    have hcard : S.card = n := by omega
    have hP := (rr_eq_card_iff S j).mp (by rw [hj, hcard])
    have hsd : (Finset.range (n + 1) \ S).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS]
      simp [hcard]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hsd
    have hzmem : z ∈ Finset.range (n + 1) \ S := by rw [hz]; exact Finset.mem_singleton_self z
    rw [Finset.mem_sdiff] at hzmem
    have hSe : S = (Finset.range (n + 1)).erase z := by
      ext a
      rw [Finset.mem_erase]
      constructor
      · intro ha
        exact ⟨fun h => hzmem.2 (h ▸ ha), hS ha⟩
      · rintro ⟨ha1, ha2⟩
        by_contra hna
        have : a ∈ Finset.range (n + 1) \ S := Finset.mem_sdiff.mpr ⟨ha2, hna⟩
        rw [hz, Finset.mem_singleton] at this
        exact ha1 this
    refine ⟨z, ?_, hSe⟩
    rw [memZ]
    have hzn := Finset.mem_range.mp hzmem.1
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    by_cases hzn' : z = n
    · exact Or.inr (Or.inl hzn')
    right; right
    have hmem : ∀ a, a < n + 1 → a ≠ z → a ∈ S := by
      intro a ha1 ha2
      rw [hSe, Finset.mem_erase, Finset.mem_range]
      exact ⟨ha2, ha1⟩
    have h0 := hP 0 (hmem 0 (by omega) (Ne.symm hz0))
    have hjS := Finset.mem_range.mp (hS (by simpa using h0.2))
    have hnS := hP n (hmem n (by omega) (Ne.symm hzn'))
    have hjn : j = n := by omega
    by_cases hnz : n - z = z
    · refine ⟨⟨z, by omega⟩, by omega⟩
    · have h2 := hP (n - z) (hmem (n - z) (by omega) hnz)
      rw [hjn, show n - (n - z) = z by omega] at h2
      exact absurd h2.2 hzmem.2
  · rintro ⟨z, hz, rfl⟩
    have hzr : z ∈ Finset.range (n + 1) := by
      rw [memZ] at hz
      rw [Finset.mem_range]
      rcases hz with h | h | ⟨_, h⟩ <;> omega
    have hcard : ((Finset.range (n + 1)).erase z).card = n := by
      rw [Finset.card_erase_of_mem hzr]; simp
    refine ⟨fun j => by have := rr_le_card ((Finset.range (n + 1)).erase z) j; omega, ?_⟩
    rw [memZ] at hz
    rcases hz with h | h | ⟨⟨k, hk⟩, h⟩
    · refine ⟨n + 1, ?_⟩
      have key := (rr_eq_card_iff ((Finset.range (n + 1)).erase z) (n + 1)).mpr ?_
      · rw [key, hcard]
      · intro a ha
        rw [Finset.mem_erase, Finset.mem_range] at ha ⊢
        omega
    · refine ⟨n - 1, ?_⟩
      have key := (rr_eq_card_iff ((Finset.range (n + 1)).erase z) (n - 1)).mpr ?_
      · rw [key, hcard]
      · intro a ha
        rw [Finset.mem_erase, Finset.mem_range] at ha ⊢
        omega
    · refine ⟨n, ?_⟩
      have key := (rr_eq_card_iff ((Finset.range (n + 1)).erase z) (n)).mpr ?_
      · rw [key, hcard]
      · intro a ha
        rw [Finset.mem_erase, Finset.mem_range] at ha ⊢
        omega

theorem OMA.solution : type_of% @OMA.S_mo_464279.main := by
  intro n hn
  have hset : ((Finset.range (n + 1)).powerset.filter fun S => thickness (poly S) = n) =
      (Z n).image (fun z => (Finset.range (n + 1)).erase z) := by
    ext S
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hS, ht⟩
      obtain ⟨z, hz, rfl⟩ := (char n hn S hS).mp ht
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨Finset.erase_subset _ _, (char n hn _ (Finset.erase_subset _ _)).mpr ⟨z, hz, rfl⟩⟩
  have hinj : Set.InjOn (fun z => (Finset.range (n + 1)).erase z) (Z n : Set ℕ) := by
    intro a ha b hb hab
    simp only at hab
    have ha' : a < n + 1 := by
      have := (memZ n a).mp ha
      rcases this with h | h | ⟨_, h⟩ <;> omega
    have hb' : b < n + 1 := by
      have := (memZ n b).mp hb
      rcases this with h | h | ⟨_, h⟩ <;> omega
    by_contra hne
    have : b ∈ (Finset.range (n + 1)).erase a :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_range.mpr hb'⟩
    rw [hab] at this
    exact (Finset.notMem_erase b _) this
  unfold T
  rw [hset, Finset.card_image_of_injOn hinj]
  unfold Z
  split_ifs with he
  · obtain ⟨k, hk⟩ := he
    have hk1 : 1 ≤ k := by omega
    have h2 : n / 2 = k := by omega
    rw [h2, Finset.card_insert_of_notMem, Finset.card_pair]
    · omega
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; omega
  · rw [Finset.card_pair]; omega
