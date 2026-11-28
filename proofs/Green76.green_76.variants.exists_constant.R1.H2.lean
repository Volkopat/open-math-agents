import OMAReductions.R_Green76_green_76_variants_exists_constant_R1

-- Step Green76.green_76.variants.exists_constant.R1.H2: hypothesis H2 of reduction Green76.green_76.variants.exists_constant.R1
-- Credit: @Raimo33

namespace RaimoG76

open scoped Finset

noncomputable def lo (S : Finset (ℝ × ℝ)) (hS : S.Nonempty) : ℝ × ℝ :=
  (S.inf' hS Prod.fst, S.inf' hS Prod.snd)

noncomputable def hi (S : Finset (ℝ × ℝ)) (hS : S.Nonempty) : ℝ × ℝ :=
  (S.sup' hS Prod.fst, S.sup' hS Prod.snd)

lemma mem_box {S : Finset (ℝ × ℝ)} (hS : S.Nonempty) {s : ℝ × ℝ} (hs : s ∈ S) :
    s ∈ Set.Icc (lo S hS) (hi S hS) :=
  ⟨Prod.le_def.mpr ⟨Finset.inf'_le _ hs, Finset.inf'_le _ hs⟩,
    Prod.le_def.mpr ⟨Finset.le_sup' _ hs, Finset.le_sup' _ hs⟩⟩

lemma box_sub {S : Finset (ℝ × ℝ)} (hS : S.Nonempty) {a b : ℝ × ℝ}
    (hsub : ∀ s ∈ S, s ∈ Set.Icc a b) :
    Set.Icc (lo S hS) (hi S hS) ⊆ Set.Icc a b := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  rw [Prod.le_def] at h1 h2
  refine ⟨Prod.le_def.mpr ⟨?_, ?_⟩, Prod.le_def.mpr ⟨?_, ?_⟩⟩
  · exact le_trans (Finset.le_inf' hS _ fun s hs => (Prod.le_def.mp (hsub s hs).1).1) h1.1
  · exact le_trans (Finset.le_inf' hS _ fun s hs => (Prod.le_def.mp (hsub s hs).1).2) h1.2
  · exact le_trans h2.1 (Finset.sup'_le hS _ fun s hs => (Prod.le_def.mp (hsub s hs).2).1)
  · exact le_trans h2.2 (Finset.sup'_le hS _ fun s hs => (Prod.le_def.mp (hsub s hs).2).2)

end RaimoG76

open scoped Finset in
theorem OMA.solution : OMA.R_Green76_green_76_variants_exists_constant_R1.H2 := by
  intro K A B hhit r
  induction r with
  | zero =>
    intro a b h
    obtain ⟨p, hp, hpab⟩ := hhit a b (by rw [pow_zero, one_mul] at h; omega)
    exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpab⟩⟩
  | succ r ih =>
    intro a b h
    have hpow : 4 ^ (r + 1) * (K + 1) = 4 * (4 ^ r * (K + 1)) := by ring
    have hNpos : 0 < 4 ^ r * (K + 1) := by positivity
    have hKle : K + 1 ≤ 4 ^ r * (K + 1) := Nat.le_mul_of_pos_left _ (by positivity)
    have hK : K ≤ #{p ∈ A | p ∈ Set.Icc a b} := by omega
    obtain ⟨q, hqB, hqab⟩ := hhit a b hK
    set P := {p ∈ A | p ∈ Set.Icc a b} with hPdef
    set Q := {p ∈ B | p ∈ Set.Icc a b} with hQdef
    have hqQ : q ∈ Q := Finset.mem_filter.mpr ⟨hqB, hqab⟩
    have part : ∀ S : Finset (ℝ × ℝ), S ⊆ P → 4 ^ r * (K + 1) ≤ #S →
        (∀ hS : S.Nonempty, q ∉ Set.Icc (RaimoG76.lo S hS) (RaimoG76.hi S hS)) →
        r + 1 + 1 ≤ #Q := by
      intro S hSP hcard hq
      have hS : S.Nonempty := Finset.card_pos.mp (by omega)
      have hsub : ∀ s ∈ S, s ∈ Set.Icc a b := fun s hs => (Finset.mem_filter.mp (hSP hs)).2
      have hA : 4 ^ r * (K + 1) ≤
          #{p ∈ A | p ∈ Set.Icc (RaimoG76.lo S hS) (RaimoG76.hi S hS)} :=
        le_trans hcard (Finset.card_le_card (fun s hs => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp (hSP hs)).1, RaimoG76.mem_box hS hs⟩))
      have h1 := ih _ _ hA
      have hsubQ : {p ∈ B | p ∈ Set.Icc (RaimoG76.lo S hS) (RaimoG76.hi S hS)} ⊆ Q.erase q := by
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_erase, Finset.mem_filter]
        exact ⟨fun h => hq hS (h ▸ hx.2), hx.1, RaimoG76.box_sub hS hsub hx.2⟩
      have h2 := Finset.card_le_card hsubQ
      rw [Finset.card_erase_of_mem hqQ] at h2
      omega
    set L := P.filter (fun p => p.1 < q.1) with hL
    set R := P.filter (fun p => q.1 < p.1) with hR
    set U := P.filter (fun p => p.1 = q.1 ∧ q.2 < p.2) with hU
    set D := P.filter (fun p => p.1 = q.1 ∧ p.2 < q.2) with hD
    have hcover : P.erase q ⊆ L ∪ R ∪ U ∪ D := by
      intro p hp
      rw [Finset.mem_erase] at hp
      obtain ⟨hne, hpP⟩ := hp
      simp only [L, R, U, D, Finset.mem_union, Finset.mem_filter]
      rcases lt_trichotomy p.1 q.1 with h1 | h1 | h1
      · left; left; left; exact ⟨hpP, h1⟩
      · rcases lt_trichotomy p.2 q.2 with h2 | h2 | h2
        · right; exact ⟨hpP, h1, h2⟩
        · exact absurd (Prod.ext h1 h2) hne
        · left; right; exact ⟨hpP, h1, h2⟩
      · left; left; right; exact ⟨hpP, h1⟩
    have hc1 := Finset.card_le_card hcover
    have hc2 := Finset.card_union_le (L ∪ R ∪ U) D
    have hc3 := Finset.card_union_le (L ∪ R) U
    have hc4 := Finset.card_union_le L R
    have hPe : #P - 1 ≤ #(P.erase q) := Finset.pred_card_le_card_erase
    by_cases hLc : 4 ^ r * (K + 1) ≤ #L
    · refine part L (Finset.filter_subset _ _) hLc (fun hS hmem => ?_)
      have h1 : q.1 ≤ L.sup' hS Prod.fst := (Prod.le_def.mp hmem.2).1
      have hlt : L.sup' hS Prod.fst < q.1 :=
        (Finset.sup'_lt_iff _).mpr (fun s hs => (Finset.mem_filter.mp hs).2)
      exact absurd h1 (not_le.mpr hlt)
    by_cases hRc : 4 ^ r * (K + 1) ≤ #R
    · refine part R (Finset.filter_subset _ _) hRc (fun hS hmem => ?_)
      have h1 : R.inf' hS Prod.fst ≤ q.1 := (Prod.le_def.mp hmem.1).1
      have hlt : q.1 < R.inf' hS Prod.fst :=
        (Finset.lt_inf'_iff _).mpr (fun s hs => (Finset.mem_filter.mp hs).2)
      exact absurd h1 (not_le.mpr hlt)
    by_cases hUc : 4 ^ r * (K + 1) ≤ #U
    · refine part U (Finset.filter_subset _ _) hUc (fun hS hmem => ?_)
      have h1 : U.inf' hS Prod.snd ≤ q.2 := (Prod.le_def.mp hmem.1).2
      have hlt : q.2 < U.inf' hS Prod.snd :=
        (Finset.lt_inf'_iff _).mpr (fun s hs => (Finset.mem_filter.mp hs).2.2)
      exact absurd h1 (not_le.mpr hlt)
    by_cases hDc : 4 ^ r * (K + 1) ≤ #D
    · refine part D (Finset.filter_subset _ _) hDc (fun hS hmem => ?_)
      have h1 : q.2 ≤ D.sup' hS Prod.snd := (Prod.le_def.mp hmem.2).2
      have hlt : D.sup' hS Prod.snd < q.2 :=
        (Finset.sup'_lt_iff _).mpr (fun s hs => (Finset.mem_filter.mp hs).2.2)
      exact absurd h1 (not_le.mpr hlt)
    omega
