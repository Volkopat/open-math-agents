import OMAReductions.R_Green91_green_91_variants_fknss_R1_H1_R1

-- Step Green91.green_91.variants.fknss.R1.H1.R1.H4: hypothesis H4 of reduction Green91.green_91.variants.fknss.R1.H1.R1
-- Credit: @yongukpark
-- Proof: union bound over bisections and t-sets of tied vertices; the ties are independent row by row
-- (rows of edges to the outside of the set), each costing at most C(N, N/2) / 2^N <= 1/sqrt(N+1).

namespace OMA.G91H4

theorem centralBinom_sq_mul_le (n : ℕ) :
    n.centralBinom ^ 2 * (2 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key := Nat.succ_mul_centralBinom_succ n
    have h1 : ((n + 1) * (n + 1).centralBinom) ^ 2 * (2 * (n + 1) + 1) =
        4 * (2 * n + 1) * (2 * n + 3) * (n.centralBinom ^ 2 * (2 * n + 1)) := by
      rw [key]; ring
    have h2 : 4 * (2 * n + 1) * (2 * n + 3) * (n.centralBinom ^ 2 * (2 * n + 1)) ≤
        4 * (2 * n + 1) * (2 * n + 3) * 16 ^ n := Nat.mul_le_mul_left _ ih
    have h3 : 4 * (2 * n + 1) * (2 * n + 3) * 16 ^ n ≤ (n + 1) ^ 2 * 16 ^ (n + 1) := by
      have : 4 * (2 * n + 1) * (2 * n + 3) ≤ (n + 1) ^ 2 * 16 := by nlinarith
      calc 4 * (2 * n + 1) * (2 * n + 3) * 16 ^ n ≤ (n + 1) ^ 2 * 16 * 16 ^ n :=
            Nat.mul_le_mul_right _ this
        _ = (n + 1) ^ 2 * 16 ^ (n + 1) := by ring
    have h4 : (n + 1) ^ 2 * ((n + 1).centralBinom ^ 2 * (2 * (n + 1) + 1)) ≤
        (n + 1) ^ 2 * 16 ^ (n + 1) := by
      calc (n + 1) ^ 2 * ((n + 1).centralBinom ^ 2 * (2 * (n + 1) + 1))
          = ((n + 1) * (n + 1).centralBinom) ^ 2 * (2 * (n + 1) + 1) := by ring
        _ ≤ _ := h1 ▸ h2.trans h3
    exact Nat.le_of_mul_le_mul_left h4 (by positivity)

/-- Every binomial coefficient is small compared to `2 ^ N`: `C(N,k)^2 (N+1) ≤ 4^N`. -/
theorem choose_sq_mul_le (N k : ℕ) : N.choose k ^ 2 * (N + 1) ≤ 4 ^ N := by
  rcases Nat.even_or_odd' N with ⟨n, rfl | rfl⟩
  · have hk : (2 * n).choose k ≤ n.centralBinom := Nat.choose_le_centralBinom k n
    have := centralBinom_sq_mul_le n
    calc (2 * n).choose k ^ 2 * (2 * n + 1) ≤ n.centralBinom ^ 2 * (2 * n + 1) := by
          gcongr
      _ ≤ 16 ^ n := this
      _ = 4 ^ (2 * n) := by rw [pow_mul]; norm_num
  · -- C(2n+1, k) ≤ C(2n+2, n+1) / 2
    have hk : (2 * n + 1).choose k ≤ (2 * n + 1).choose n := by
      have := Nat.choose_le_middle k (2 * n + 1)
      have h2 : (2 * n + 1) / 2 = n := by omega
      rwa [h2] at this
    have hc : (n + 1).centralBinom = 2 * (2 * n + 1).choose n := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (n + 1) = (2 * n + 1) + 1 by ring,
        Nat.choose_succ_succ, Nat.choose_symm_half]
      ring
    have := centralBinom_sq_mul_le (n + 1)
    rw [hc] at this
    have h5 : (2 * n + 1).choose n ^ 2 * (2 * n + 2) * 4 ≤ 4 ^ (2 * n + 1) * 4 := by
      calc (2 * n + 1).choose n ^ 2 * (2 * n + 2) * 4
          ≤ (2 * (2 * n + 1).choose n) ^ 2 * (2 * (n + 1) + 1) := by nlinarith
        _ ≤ 16 ^ (n + 1) := this
        _ = 4 ^ (2 * n + 1) * 4 := by rw [show 16 = 4 ^ 2 by norm_num, ← pow_mul]; ring
    have h6 : (2 * n + 1).choose n ^ 2 * (2 * n + 2) ≤ 4 ^ (2 * n + 1) := by omega
    calc (2 * n + 1).choose k ^ 2 * (2 * n + 1 + 1) ≤ (2 * n + 1).choose n ^ 2 * (2 * n + 2) := by
          gcongr
      _ ≤ _ := h6

section split
variable {α : Type*} [DecidableEq α]

/-- Splitting a family of edge sets into its part off `R` and its part on `R`. -/
theorem split_count (D R : Finset α) (hR : R ⊆ D) (P Q : Finset α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hP : ∀ E, P E ↔ P (E \ R)) (M : ℕ)
    (hM : ∀ A ⊆ D \ R, ((R.powerset).filter (fun B => Q (A ∪ B))).card ≤ M) :
    2 ^ R.card * ((D.powerset).filter (fun E => P E ∧ Q E)).card ≤
      M * ((D.powerset).filter P).card := by
  -- fibres over `E \ R`
  have hmaps : ∀ S : Finset (Finset α), S ⊆ D.powerset →
      Set.MapsTo (fun E => E \ R) (S : Set (Finset α)) ((D \ R).powerset : Set (Finset α)) := by
    intro S hS E hE
    have := Finset.mem_powerset.mp (hS hE)
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    exact Finset.sdiff_subset_sdiff this le_rfl
  rw [Finset.card_eq_sum_card_fiberwise (hmaps _ (Finset.filter_subset _ _)),
    Finset.card_eq_sum_card_fiberwise (hmaps _ (Finset.filter_subset _ _)),
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun A hA => ?_
  have hAD : A ⊆ D \ R := Finset.mem_powerset.mp hA
  have hAR : Disjoint A R := Finset.disjoint_of_subset_left hAD Finset.sdiff_disjoint
  -- the fibre of `A` is `{A ∪ B | B ⊆ R}`
  have fib : ∀ E, (E ∈ D.powerset ∧ E \ R = A) ↔ ∃ B ∈ R.powerset, A ∪ B = E := by
    intro E
    constructor
    · rintro ⟨hE, rfl⟩
      refine ⟨E ∩ R, Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
      exact Finset.sdiff_union_inter E R
    · rintro ⟨B, hB, rfl⟩
      have hB' := Finset.mem_powerset.mp hB
      refine ⟨Finset.mem_powerset.mpr (Finset.union_subset (hAD.trans Finset.sdiff_subset)
        (hB'.trans hR)), ?_⟩
      rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hB', Finset.union_empty,
        Finset.sdiff_eq_self_of_disjoint hAR]
  have hinj : Set.InjOn (fun B => A ∪ B) (R.powerset : Set (Finset α)) := by
    intro B₁ h₁ B₂ h₂ h
    have h₁' : B₁ ⊆ R := Finset.mem_powerset.mp h₁
    have h₂' : B₂ ⊆ R := Finset.mem_powerset.mp h₂
    have := congrArg (· ∩ R) h
    simp only [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hAR,
      Finset.empty_union, Finset.inter_eq_left.mpr h₁', Finset.inter_eq_left.mpr h₂'] at this
    exact this
  have hPA : ∀ B ⊆ R, P (A ∪ B) ↔ P A := by
    intro B hB
    rw [hP]
    congr 1
    rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hB, Finset.union_empty,
      Finset.sdiff_eq_self_of_disjoint hAR]
  -- rewrite both fibres as images
  have e1 : ((D.powerset.filter fun E => P E ∧ Q E).filter fun E => E \ R = A) =
      ((R.powerset.filter fun B => P A ∧ Q (A ∪ B)).image fun B => A ∪ B) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨hE, hPE, hQE⟩, hEA⟩
      obtain ⟨B, hB, rfl⟩ := (fib E).mp ⟨hE, hEA⟩
      exact ⟨B, ⟨hB, (hPA B (Finset.mem_powerset.mp hB)).mp hPE, hQE⟩, rfl⟩
    · rintro ⟨B, ⟨hB, hPB, hQB⟩, rfl⟩
      obtain ⟨hE, hEA⟩ := (fib (A ∪ B)).mpr ⟨B, hB, rfl⟩
      exact ⟨⟨hE, (hPA B (Finset.mem_powerset.mp hB)).mpr hPB, hQB⟩, hEA⟩
  have e2 : ((D.powerset.filter P).filter fun E => E \ R = A) =
      ((R.powerset.filter fun _ => P A).image fun B => A ∪ B) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨hE, hPE⟩, hEA⟩
      obtain ⟨B, hB, rfl⟩ := (fib E).mp ⟨hE, hEA⟩
      exact ⟨B, ⟨hB, (hPA B (Finset.mem_powerset.mp hB)).mp hPE⟩, rfl⟩
    · rintro ⟨B, ⟨hB, hPB⟩, rfl⟩
      obtain ⟨hE, hEA⟩ := (fib (A ∪ B)).mpr ⟨B, hB, rfl⟩
      exact ⟨⟨hE, (hPA B (Finset.mem_powerset.mp hB)).mpr hPB⟩, hEA⟩
  rw [e1, e2, Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))),
    Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
  by_cases hPA' : P A
  · simp only [hPA', true_and]
    rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_powerset, mul_comm]
    exact Nat.mul_le_mul_right _ (hM A hAD)
  · simp [hPA']

end split


open Finset

variable {n : ℕ}

/-- Friendliness of `v`, read off an edge set `E`. -/
def fr (s : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) (v : Fin n) : ℤ :=
  ((univ.filter fun w => s(v, w) ∈ E ∧ (w ∈ s ↔ v ∈ s)).card : ℤ) -
    (univ.filter fun w => s(v, w) ∈ E ∧ ¬ (w ∈ s ↔ v ∈ s)).card

/-- The pairs from `u` to the outside of `U`. -/
def row (U : Finset (Fin n)) (u : Fin n) : Finset (Sym2 (Fin n)) :=
  Uᶜ.image fun w => s(u, w)

theorem mem_row {U : Finset (Fin n)} {u : Fin n} {e : Sym2 (Fin n)} :
    e ∈ row U u ↔ ∃ w, w ∉ U ∧ s(u, w) = e := by
  simp [row]

theorem mk_mem_row {U : Finset (Fin n)} {u v w : Fin n} (hv : v ∈ U) :
    s(v, w) ∈ row U u ↔ v = u ∧ w ∉ U := by
  rw [mem_row]
  constructor
  · rintro ⟨w', hw', h⟩
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1.symm, h2 ▸ hw'⟩
    · exact absurd hv (h2 ▸ hw')
  · rintro ⟨rfl, hw⟩
    exact ⟨w, hw, rfl⟩

theorem card_row (U : Finset (Fin n)) (u : Fin n) : (row U u).card = Uᶜ.card := by
  apply card_image_of_injective
  intro a b h
  exact Sym2.congr_right.mp h

/-- The count of one row: whatever happens off the row, the row is determined, up to a
binomial coefficient, by the value of the friendliness of `u`. -/
theorem row_count (s U : Finset (Fin n)) (u : Fin n) (hu : u ∈ U)
    (A : Finset (Sym2 (Fin n))) (hA : Disjoint A (row U u)) (c : ℤ) :
    ((row U u).powerset.filter fun B => fr s (A ∪ B) u = c).card ≤
      Uᶜ.card.choose (Uᶜ.card / 2) := by
  set same : Fin n → Prop := fun w => (w ∈ s ↔ u ∈ s) with hsame
  -- the part of the friendliness carried by a row subset
  let g : Finset (Sym2 (Fin n)) → ℤ := fun B =>
    ((univ.filter fun w => s(u, w) ∈ B ∧ same w).card : ℤ) -
      (univ.filter fun w => s(u, w) ∈ B ∧ ¬ same w).card
  have hsplit : ∀ B ⊆ row U u, fr s (A ∪ B) u = fr s A u + g B := by
    intro B hB
    have hdisj : ∀ (p : Fin n → Prop) [DecidablePred p],
        ((univ.filter fun w => s(u, w) ∈ A ∪ B ∧ p w).card : ℤ) =
          (univ.filter fun w => s(u, w) ∈ A ∧ p w).card +
            (univ.filter fun w => s(u, w) ∈ B ∧ p w).card := by
      intro p _
      rw [← Nat.cast_add, ← card_union_of_disjoint]
      · congr 2
        ext w
        simp only [mem_filter, mem_univ, true_and, mem_union, mem_union]
        tauto
      · rw [disjoint_left]
        intro w h1 h2
        simp only [mem_filter, mem_univ, true_and] at h1 h2
        exact disjoint_left.mp hA h1.1 (hB h2.1)
    simp only [fr, g]
    rw [hdisj (fun w => (w ∈ s ↔ u ∈ s)), hdisj (fun w => ¬ (w ∈ s ↔ u ∈ s))]
    ring
  -- the injective code of a row subset
  let X : Finset (Sym2 (Fin n)) → Finset (Fin n) := fun B =>
    univ.filter fun w => (s(u, w) ∈ B ∧ same w) ∨ (w ∉ U ∧ ¬ same w ∧ s(u, w) ∉ B)
  have hrowmem : ∀ B ⊆ row U u, ∀ w, s(u, w) ∈ B → w ∉ U := by
    intro B hB w hw
    exact ((mk_mem_row hu).mp (hB hw)).2
  have hXsub : ∀ B ⊆ row U u, X B ⊆ Uᶜ := by
    intro B hB w hw
    simp only [X, mem_filter, mem_univ, true_and] at hw
    rw [mem_compl]
    rcases hw with ⟨h, _⟩ | ⟨h, _⟩
    · exact hrowmem B hB w h
    · exact h
  set K : ℕ := (univ.filter fun w => w ∉ U ∧ ¬ same w).card with hK
  have hXcard : ∀ B ⊆ row U u, ((X B).card : ℤ) = g B + K := by
    intro B hB
    have e1 : X B = (univ.filter fun w => s(u, w) ∈ B ∧ same w) ∪
        ((univ.filter fun w => w ∉ U ∧ ¬ same w) \ (univ.filter fun w => s(u, w) ∈ B ∧ ¬ same w)) := by
      ext w
      simp only [X, mem_filter, mem_univ, true_and, mem_union, mem_sdiff]
      constructor
      · rintro (h | ⟨h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨⟨h1, h2⟩, fun h => h3 h.1⟩
      · rintro (h | ⟨⟨h1, h2⟩, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, fun h => h3 ⟨h, h2⟩⟩
    have hsub : (univ.filter fun w => s(u, w) ∈ B ∧ ¬ same w) ⊆
        (univ.filter fun w => w ∉ U ∧ ¬ same w) := by
      intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw ⊢
      exact ⟨hrowmem B hB w hw.1, hw.2⟩
    rw [e1, card_union_of_disjoint, card_sdiff_of_subset hsub]
    · simp only [g]
      rw [Nat.cast_add, Nat.cast_sub (card_le_card hsub)]
      ring
    · rw [disjoint_left]
      intro w h1 h2
      simp only [mem_filter, mem_univ, true_and, mem_sdiff] at h1 h2
      exact h1.2 |> fun hs => h2.1.2 hs
  have hXinj : Set.InjOn X ((row U u).powerset : Set (Finset (Sym2 (Fin n)))) := by
    intro B₁ h₁ B₂ h₂ h
    have h₁' : B₁ ⊆ row U u := mem_powerset.mp h₁
    have h₂' : B₂ ⊆ row U u := mem_powerset.mp h₂
    have key : ∀ w, w ∉ U → (s(u, w) ∈ B₁ ↔ s(u, w) ∈ B₂) := by
      intro w hw
      have hw' : w ∈ X B₁ ↔ w ∈ X B₂ := by rw [h]
      simp only [X, mem_filter, mem_univ, true_and] at hw'
      by_cases hs : same w <;> simp only [hs, and_true, not_true_eq_false, false_and, or_false,
        and_false, false_or, not_false_eq_true, true_and, hw] at hw' <;> tauto
    ext e
    constructor
    · intro he
      obtain ⟨w, hw, rfl⟩ := mem_row.mp (h₁' he)
      exact (key w hw).mp he
    · intro he
      obtain ⟨w, hw, rfl⟩ := mem_row.mp (h₂' he)
      exact (key w hw).mpr he
  -- all codes have the same size
  set k : ℕ := (c - fr s A u + K).toNat with hk
  have hmaps : Set.MapsTo X (((row U u).powerset.filter fun B => fr s (A ∪ B) u = c) :
      Set (Finset (Sym2 (Fin n)))) (Uᶜ.powersetCard k : Set (Finset (Fin n))) := by
    intro B hB
    rw [mem_coe, mem_filter] at hB
    have hB' : B ⊆ row U u := mem_powerset.mp hB.1
    rw [mem_coe, mem_powersetCard]
    refine ⟨hXsub B hB', ?_⟩
    have h1 := hXcard B hB'
    have h2 := hsplit B hB'
    rw [hB.2] at h2
    rw [hk]
    omega
  calc ((row U u).powerset.filter fun B => fr s (A ∪ B) u = c).card
      ≤ (Uᶜ.powersetCard k).card :=
        card_le_card_of_injOn X hmaps (hXinj.mono (coe_subset.mpr (filter_subset _ _)))
    _ = Uᶜ.card.choose k := card_powersetCard _ _
    _ ≤ Uᶜ.card.choose (Uᶜ.card / 2) := Nat.choose_le_middle _ _


/-- All pairs of distinct vertices. -/
def D (n : ℕ) : Finset (Sym2 (Fin n)) := univ.filter fun e => ¬ e.IsDiag

theorem row_subset_D {U : Finset (Fin n)} {u : Fin n} (hu : u ∈ U) : row U u ⊆ D n := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := mem_row.mp he
  simp only [D, mem_filter, mem_univ, true_and, Sym2.mk_isDiag_iff]
  rintro rfl
  exact hw hu

/-- Ties at all vertices of `U'` are rare. -/
theorem all_tie_count (s U : Finset (Fin n)) : ∀ U' ⊆ U,
    2 ^ (Uᶜ.card * U'.card) * ((D n).powerset.filter fun E => ∀ v ∈ U', fr s E v = 1).card ≤
      (Uᶜ.card.choose (Uᶜ.card / 2)) ^ U'.card * 2 ^ (D n).card := by
  intro U' hU'
  induction U' using Finset.induction_on with
  | empty =>
    simp only [card_empty, mul_zero, pow_zero, one_mul]
    calc _ ≤ (D n).powerset.card := card_le_card (filter_subset _ _)
      _ = _ := card_powerset _
  | insert u U' hu ih =>
    have huU : u ∈ U := hU' (mem_insert_self u U')
    have ih := ih ((subset_insert u U').trans hU')
    set N := Uᶜ.card
    set M := N.choose (N / 2)
    have hsplit := split_count (D n) (row U u) (row_subset_D huU)
      (fun E => ∀ v ∈ U', fr s E v = 1) (fun E => fr s E u = 1)
      (by
        intro E
        refine forall₂_congr fun v hv => ?_
        have hvU : v ∈ U := hU' (mem_insert_of_mem hv)
        have hvu : v ≠ u := fun h => hu (h ▸ hv)
        have key : ∀ w, s(v, w) ∈ E ↔ s(v, w) ∈ E \ row U u := by
          intro w
          rw [mem_sdiff, mk_mem_row hvU]
          tauto
        simp only [fr, key])
      M
      (by
        intro A hA
        exact row_count s U u huU A
          (disjoint_of_subset_left hA sdiff_disjoint) 1)
    rw [card_row] at hsplit
    have hfil : ((D n).powerset.filter fun E => ∀ v ∈ insert u U', fr s E v = 1) =
        ((D n).powerset.filter fun E => (∀ v ∈ U', fr s E v = 1) ∧ fr s E u = 1) := by
      apply filter_congr
      intro E _
      rw [forall_mem_insert]
      tauto
    rw [hfil, card_insert_of_notMem hu]
    set X := ((D n).powerset.filter fun E => (∀ v ∈ U', fr s E v = 1) ∧ fr s E u = 1).card
    set Y := ((D n).powerset.filter fun E => ∀ v ∈ U', fr s E v = 1).card
    calc 2 ^ (N * (U'.card + 1)) * X = 2 ^ (N * U'.card) * (2 ^ N * X) := by ring
      _ ≤ 2 ^ (N * U'.card) * (M * Y) := Nat.mul_le_mul_left _ hsplit
      _ = M * (2 ^ (N * U'.card) * Y) := by ring
      _ ≤ M * (M ^ U'.card * 2 ^ (D n).card) := Nat.mul_le_mul_left _ ih
      _ = M ^ (U'.card + 1) * 2 ^ (D n).card := by ring

open Classical in
theorem friendliness_eq_fr (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) (v : Fin n) :
    Green91.friendliness G s v = fr s G.edgeFinset v := by
  unfold Green91.friendliness fr
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

open Classical in
/-- Ties at all vertices of `U`, for graphs. -/
theorem graph_tie_count (s U : Finset (Fin n)) :
    2 ^ (Uᶜ.card * U.card) *
        (univ.filter fun G : SimpleGraph (Fin n) => ∀ v ∈ U, Green91.friendliness G s v = 1).card ≤
      (Uᶜ.card.choose (Uᶜ.card / 2)) ^ U.card * 2 ^ (D n).card := by
  refine le_trans (Nat.mul_le_mul_left _ ?_) (all_tie_count s U U subset_rfl)
  refine card_le_card_of_injOn (fun G => G.edgeFinset) ?_ ?_
  · intro G hG
    rw [mem_coe, mem_filter] at hG ⊢
    refine ⟨mem_powerset.mpr ?_, fun v hv => (friendliness_eq_fr G s v) ▸ hG.2 v hv⟩
    intro e he
    simp only [D, mem_filter, mem_univ, true_and]
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G (SimpleGraph.mem_edgeFinset.mp he)
  · intro G _ H _ h
    exact SimpleGraph.edgeFinset_inj.mp h


theorem card_D (n : ℕ) : (D n).card = n.choose 2 := by
  have := Sym2.card_subtype_not_diag (α := Fin n)
  rw [Fintype.card_fin] at this
  rw [← this, D, Fintype.card_subtype]

open MeasureTheory in
theorem binomialRandom_half_singleton (G : SimpleGraph (Fin n)) :
    SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num, by norm_num⟩ {G} =
      (2⁻¹ : ENNReal) ^ n.choose 2 := by
  classical
  rw [SimpleGraph.binomialRandom_singleton]
  have h1 : ((unitInterval.toNNReal ⟨1 / 2, by norm_num, by norm_num⟩ : NNReal) : ENNReal) = 2⁻¹ := by
    rw [show (unitInterval.toNNReal ⟨1 / 2, by norm_num, by norm_num⟩ : NNReal) = 2⁻¹ by
      ext; simp [unitInterval.toNNReal] <;> rfl]
    simp
  have h2 : ((unitInterval.toNNReal (unitInterval.symm ⟨1 / 2, by norm_num, by norm_num⟩) : NNReal) :
      ENNReal) = 2⁻¹ := by
    rw [show (unitInterval.toNNReal (unitInterval.symm ⟨1 / 2, by norm_num, by norm_num⟩) : NNReal)
      = 2⁻¹ by ext; simp [unitInterval.toNNReal, unitInterval.symm]; norm_num <;> rfl]
    simp
  rw [h1, h2, ← pow_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  congr 1
  have : G.edgeSet.ncard ≤ n.choose 2 := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    simpa using G.card_edgeFinset_le_card_choose_two
  omega

open MeasureTheory Classical in
theorem prob_le_card (P : SimpleGraph (Fin n) → Prop) :
    Green91.prob n P ≤ ((univ.filter P).card : ENNReal) * (2⁻¹ : ENNReal) ^ n.choose 2 := by
  unfold Green91.prob
  have hS : {G | P G} = ⋃ G ∈ univ.filter P, ({G} : Set (SimpleGraph (Fin n))) := by
    ext G; simp
  rw [hS]
  refine (measure_biUnion_finset_le _ _).trans ?_
  simp only [binomialRandom_half_singleton, sum_const, nsmul_eq_mul]
  rfl


open Filter Topology

theorem lim_aux (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 4) :
    Tendsto (fun m : ℕ => (256 : ℝ) ^ m /
      (((2 * m - (⌊ε * ((2 * m : ℕ) : ℝ)⌋₊ + 1) + 1 : ℕ) : ℝ)) ^ (⌊ε * ((2 * m : ℕ) : ℝ)⌋₊ + 1))
      atTop (𝓝 0) := by
  set K : ℕ := ⌈1 / (2 * ε)⌉₊ with hK
  have hK1 : 1 / (2 * ε) ≤ K := Nat.le_ceil _
  have hKε : 1 ≤ (K : ℝ) * (2 * ε) := by
    rw [div_le_iff₀ (by positivity)] at hK1; linarith
  -- the comparison function
  have hlim : Tendsto (fun m : ℕ => (1 / (2 * ε)) / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun m => by positivity
  · filter_upwards [eventually_ge_atTop (max 2 (2 * 256 ^ K))] with m hm
    have hm2 : 2 ≤ m := le_of_max_le_left hm
    have hmK : 2 * 256 ^ K ≤ m := le_of_max_le_right hm
    set t := ⌊ε * ((2 * m : ℕ) : ℝ)⌋₊ + 1 with ht
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hcast : ((2 * m : ℕ) : ℝ) = 2 * m := by push_cast; ring
    have htgt : ε * (2 * m) < t := by
      rw [ht, ← hcast]; push_cast; exact Nat.lt_floor_add_one _
    have htle : (t : ℝ) ≤ ε * (2 * m) + 1 := by
      rw [ht, ← hcast]; push_cast
      have := Nat.floor_le (show 0 ≤ ε * (2 * (m : ℝ)) by positivity)
      linarith
    have htm : t ≤ m := by
      have : (t : ℝ) ≤ m := by nlinarith
      exact_mod_cast this
    have ht1 : 1 ≤ t := by omega
    have hN : m + 1 ≤ 2 * m - t + 1 := by omega
    have hmKt : m ≤ K * t := by
      have : (m : ℝ) < K * t := by
        calc (m : ℝ) ≤ (K * (2 * ε)) * m := by nlinarith
          _ = K * (ε * (2 * m)) := by ring
          _ < K * t := by
            have hK0 : (0 : ℝ) < K := by
              have : (0:ℝ) < 1 / (2 * ε) := by positivity
              linarith
            exact mul_lt_mul_of_pos_left htgt hK0
      exact_mod_cast this.le
    -- the estimate
    have hpos : (0 : ℝ) < ((2 * m - t + 1 : ℕ) : ℝ) := by positivity
    calc (256 : ℝ) ^ m / ((2 * m - t + 1 : ℕ) : ℝ) ^ t
        ≤ (256 : ℝ) ^ (K * t) / ((m : ℝ) + 1) ^ t := by
          apply div_le_div₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hmKt)
            (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          exact_mod_cast hN
      _ = ((256 : ℝ) ^ K / ((m : ℝ) + 1)) ^ t := by rw [div_pow, pow_mul]
      _ ≤ (1 / 2 : ℝ) ^ t := by
          apply pow_le_pow_left₀ (by positivity)
          rw [div_le_iff₀ (by positivity)]
          have : (2 : ℝ) * 256 ^ K ≤ m := by exact_mod_cast hmK
          linarith
      _ ≤ 1 / (t : ℝ) := by
          rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
          exact_mod_cast (Nat.lt_two_pow_self).le
      _ ≤ (1 / (2 * ε)) / (m : ℝ) := by
          rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
          linarith


open Filter Topology in
theorem lim_sqrt (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 4) :
    Tendsto (fun m : ℕ => Real.sqrt ((256 : ℝ) ^ m /
      (((2 * m - (⌊ε * ((2 * m : ℕ) : ℝ)⌋₊ + 1) + 1 : ℕ) : ℝ)) ^ (⌊ε * ((2 * m : ℕ) : ℝ)⌋₊ + 1)))
      atTop (𝓝 0) := by
  simpa using (lim_aux ε hε hε').sqrt

/-- The per-set estimate, squared, in natural numbers. -/
theorem sq_bound (N t T C M : ℕ) (h1 : 2 ^ (N * t) * T ≤ M ^ t * 2 ^ C)
    (h2 : M ^ 2 * (N + 1) ≤ 4 ^ N) : T ^ 2 * (N + 1) ^ t ≤ (2 ^ C) ^ 2 := by
  have h4 : (4 : ℕ) ^ N = 2 ^ (2 * N) := by rw [pow_mul]; norm_num
  have e1 : (2 ^ (N * t) * T) ^ 2 * (N + 1) ^ t ≤ (M ^ t * 2 ^ C) ^ 2 * (N + 1) ^ t :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h1 2)
  have e2 : (M ^ 2 * (N + 1)) ^ t ≤ (4 ^ N) ^ t := Nat.pow_le_pow_left h2 t
  have e3 : (M ^ t * 2 ^ C) ^ 2 * (N + 1) ^ t = (M ^ 2 * (N + 1)) ^ t * (2 ^ C) ^ 2 := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm t 2]; ring
  have e4 : (4 ^ N) ^ t = (2 ^ (N * t)) ^ 2 := by
    rw [h4, ← pow_mul, ← pow_mul]; ring_nf
  have e5 : (2 ^ (N * t) * T) ^ 2 * (N + 1) ^ t = (2 ^ (N * t)) ^ 2 * (T ^ 2 * (N + 1) ^ t) := by
    ring
  have : (2 ^ (N * t)) ^ 2 * (T ^ 2 * (N + 1) ^ t) ≤ (2 ^ (N * t)) ^ 2 * (2 ^ C) ^ 2 := by
    rw [← e5]
    calc _ ≤ (M ^ t * 2 ^ C) ^ 2 * (N + 1) ^ t := e1
      _ = (M ^ 2 * (N + 1)) ^ t * (2 ^ C) ^ 2 := e3
      _ ≤ (4 ^ N) ^ t * (2 ^ C) ^ 2 := Nat.mul_le_mul_right _ e2
      _ = _ := by rw [e4]
  exact Nat.le_of_mul_le_mul_left this (by positivity)

theorem ofReal_div_two_pow (T C : ℕ) :
    ENNReal.ofReal ((T : ℝ) / 2 ^ C) = (T : ENNReal) * (2⁻¹ : ENNReal) ^ C := by
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ← inv_pow,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

open Filter Topology MeasureTheory Classical in
theorem bad_le (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    Green91.prob (2 * m) (fun G => ¬ ∀ s : Finset (Fin (2 * m)), s.card = m →
      (((univ.filter fun v => Green91.friendliness G s v = 1).card : ℕ) : ℝ) ≤ ε * ((2 * m : ℕ) : ℝ))
      ≤ ENNReal.ofReal (Real.sqrt ((256 : ℝ) ^ m /
      (((2 * m - (⌊ε * ((2 * m : ℕ) : ℝ)⌋₊ + 1) + 1 : ℕ) : ℝ)) ^ (⌊ε * ((2 * m : ℕ) : ℝ)⌋₊ + 1))) := by
  set n := 2 * m with hn
  set t := ⌊ε * ((n : ℕ) : ℝ)⌋₊ + 1 with ht
  set C := n.choose 2
  set Tset : Finset (Fin n) → Finset (Fin n) → Set (SimpleGraph (Fin n)) :=
    fun s U => {G | ∀ v ∈ U, Green91.friendliness G s v = 1}
  -- union bound
  have hsub : {G : SimpleGraph (Fin n) | ¬ ∀ s : Finset (Fin n), s.card = m →
      (((univ.filter fun v => Green91.friendliness G s v = 1).card : ℕ) : ℝ) ≤ ε * ((n : ℕ) : ℝ)} ⊆
      ⋃ s ∈ (univ : Finset (Fin n)).powersetCard m, ⋃ U ∈ (univ : Finset (Fin n)).powersetCard t,
        Tset s U := by
    intro G hG
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hG
    obtain ⟨s, hs, hlt⟩ := hG
    have hcard : t ≤ (univ.filter fun v => Green91.friendliness G s v = 1).card := by
      have := (Nat.floor_lt (show (0 : ℝ) ≤ ε * ((n : ℕ) : ℝ) by positivity)).mpr hlt
      omega
    obtain ⟨U, hU, hUc⟩ := exists_subset_card_eq hcard
    simp only [Set.mem_iUnion]
    refine ⟨s, mem_powersetCard.mpr ⟨subset_univ _, hs⟩, U, mem_powersetCard.mpr ⟨subset_univ _, hUc⟩,
      fun v hv => (mem_filter.mp (hU hv)).2⟩
  -- each piece
  have hpiece : ∀ s U : Finset (Fin n), U.card = t →
      SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num, by norm_num⟩ (Tset s U) ≤
        ENNReal.ofReal (Real.sqrt (1 / (((n - t + 1 : ℕ) : ℝ)) ^ t)) := by
    intro s U hU
    have hp := prob_le_card (n := n) (fun G => ∀ v ∈ U, Green91.friendliness G s v = 1)
    unfold Green91.prob at hp
    refine hp.trans ?_
    set T := (univ.filter fun G : SimpleGraph (Fin n) => ∀ v ∈ U, Green91.friendliness G s v = 1).card
    rw [← ofReal_div_two_pow]
    apply ENNReal.ofReal_le_ofReal
    have hgc := graph_tie_count s U
    rw [card_compl, Fintype.card_fin, hU, card_D] at hgc
    have hsq := sq_bound (n - t) t T C _ hgc (choose_sq_mul_le _ _)
    apply Real.le_sqrt_of_sq_le
    have hpos : (0 : ℝ) < ((n - t + 1 : ℕ) : ℝ) ^ t := by positivity
    rw [div_pow, le_div_iff₀ (by positivity), div_mul_eq_mul_div, div_le_one (by positivity)]
    exact_mod_cast hsq
  -- assemble
  unfold Green91.prob
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hU : ∀ s ∈ (univ : Finset (Fin n)).powersetCard m,
      SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num, by norm_num⟩
        (⋃ U ∈ (univ : Finset (Fin n)).powersetCard t, Tset s U) ≤
      ((univ : Finset (Fin n)).powersetCard t).card *
        ENNReal.ofReal (Real.sqrt (1 / (((n - t + 1 : ℕ) : ℝ)) ^ t)) := by
    intro s _
    refine (measure_biUnion_finset_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun U hU => hpiece s U (mem_powersetCard.mp hU).2
  refine (sum_le_sum hU).trans ?_
  rw [sum_const, nsmul_eq_mul, card_powersetCard, card_powersetCard, card_univ, Fintype.card_fin]
  -- numbers
  have hc1 : (n.choose m : ℝ) ≤ 4 ^ m := by
    have := Nat.choose_le_two_pow n m
    have h : (2 : ℕ) ^ n = 4 ^ m := by rw [hn, pow_mul]; norm_num
    rw [h] at this; exact_mod_cast this
  have hc2 : (n.choose t : ℝ) ≤ 4 ^ m := by
    have := Nat.choose_le_two_pow n t
    have h : (2 : ℕ) ^ n = 4 ^ m := by rw [hn, pow_mul]; norm_num
    rw [h] at this; exact_mod_cast this
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hs256 : Real.sqrt ((256 : ℝ) ^ m) = 16 ^ m := by
    rw [show (256 : ℝ) ^ m = (16 ^ m) ^ 2 by rw [← pow_mul, show m * 2 = 2 * m by ring, pow_mul]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have hsplit : Real.sqrt ((256 : ℝ) ^ m / (((n - t + 1 : ℕ) : ℝ)) ^ t) =
      16 ^ m * Real.sqrt (1 / (((n - t + 1 : ℕ) : ℝ)) ^ t) := by
    rw [div_eq_mul_one_div, Real.sqrt_mul (by positivity), hs256]
  rw [hsplit]
  have hsq0 : 0 ≤ Real.sqrt (1 / (((n - t + 1 : ℕ) : ℝ)) ^ t) := Real.sqrt_nonneg _
  calc (n.choose m : ℝ) * ((n.choose t : ℝ) * Real.sqrt (1 / (((n - t + 1 : ℕ) : ℝ)) ^ t))
      ≤ 4 ^ m * (4 ^ m * Real.sqrt (1 / (((n - t + 1 : ℕ) : ℝ)) ^ t)) := by
        gcongr
    _ = 16 ^ m * Real.sqrt (1 / (((n - t + 1 : ℕ) : ℝ)) ^ t) := by
        rw [← mul_assoc, ← mul_pow]; norm_num

open Filter Topology MeasureTheory Classical in
theorem main_small (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 4) :
    Tendsto (fun m : ℕ => Green91.prob (2 * m) fun G => ∀ s : Finset (Fin (2 * m)), s.card = m →
      (((univ.filter fun v => Green91.friendliness G s v = 1).card : ℕ) : ℝ) ≤ ε * ((2 * m : ℕ) : ℝ))
      atTop (𝓝 1) := by
  have hr := ENNReal.tendsto_ofReal (lim_sqrt ε hε hε')
  rw [ENNReal.ofReal_zero] at hr
  have hlow := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal))) hr
    (Or.inl ENNReal.one_ne_top)
  rw [tsub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
  · intro m
    have hb := bad_le ε hε m
    unfold Green91.prob at hb ⊢
    refine (tsub_le_tsub_left hb 1).trans ?_
    rw [tsub_le_iff_right, ← measure_univ (μ := SimpleGraph.binomialRandom (Fin (2 * m))
      ⟨1 / 2, by norm_num, by norm_num⟩)]
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro G _
    by_cases h : G ∈ {G : SimpleGraph (Fin (2 * m)) | ∀ s : Finset (Fin (2 * m)), s.card = m →
      (((univ.filter fun v => Green91.friendliness G s v = 1).card : ℕ) : ℝ) ≤ ε * ((2 * m : ℕ) : ℝ)}
    · exact Or.inl h
    · exact Or.inr h
  · intro m
    unfold Green91.prob
    exact prob_le_one

end OMA.G91H4

open Filter Topology MeasureTheory Classical in
theorem OMA.solution : OMA.R_Green91_green_91_variants_fknss_R1_H1_R1.H4 := by
  have key : ∀ ε : ℝ, 0 < ε → Tendsto (fun m : ℕ => Green91.prob (2 * m) fun G =>
      ∀ s : Finset (Fin (2 * m)), s.card = m →
      (((Finset.univ.filter fun v => Green91.friendliness G s v = 1).card : ℕ) : ℝ) ≤
        ε * ((2 * m : ℕ) : ℝ)) atTop (𝓝 1) := by
    intro ε hε
    have h := OMA.G91H4.main_small (min ε (1 / 4)) (lt_min hε (by norm_num)) (min_le_right _ _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds ?_ ?_
    · intro m
      unfold Green91.prob
      refine measure_mono fun G hG s hs => (hG s hs).trans ?_
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
    · intro m
      unfold Green91.prob
      exact prob_le_one
  exact key
