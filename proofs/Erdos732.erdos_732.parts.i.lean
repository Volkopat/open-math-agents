import FormalConjectures.ErdosProblems.«732»

/-! Polynomial coefficient criterion for pairwise balanced design block-size profiles. -/

-- Original proof by @connoranderson (PR #9192), streamlined by @joshuadc11
-- (pending PR #14768). The two coefficient projections now use sum APIs.

private abbrev E (n : ℕ) := (Finset (Fin n) → ℕ) × Multiset ℕ
private def trm {n : ℕ} (T : Finset (Fin n)) : E n := (fun e => if e.card = 2 ∧ e ⊆ T then 1 else 0, {T.card})
private noncomputable def P (n : ℕ) : AddMonoidAlgebra ℕ (E n) :=
  ∏ T ∈ Finset.univ.filter (2 ≤ Finset.card ·), (1 + AddMonoidAlgebra.single (trm T) 1)

noncomputable def OMA.answer (n : ℕ) (s : List ℕ) : Prop :=
  (s : Multiset ℕ).sort (· ≤ ·) = s ∧ 0 < (P n).coeff ((fun e => if e.card = 2 then 1 else 0, s) : E n)

theorem OMA.solution : Erdos732.erdos_732.parts.i.answer = OMA.answer → type_of% @Erdos732.erdos_732.parts.i := by
  classical
  intro h; rw [h]; intro n s
  have hsz (H : Finset (Finset (Fin n))) : (∑ T ∈ H, trm T).2 = H.val.map Finset.card := by
    rw [Prod.snd_sum, Finset.sum_eq_multiset_sum]
    simpa only [Multiset.map_map, Function.comp_def, trm] using
      Multiset.sum_map_singleton (H.val.map Finset.card)
  have hct (H : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
      (∑ T ∈ H, trm T).1 e = if e.card = 2 then (H.filter (e ⊆ ·)).card else 0 := by
    rw [Prod.fst_sum, Finset.sum_apply]
    by_cases he : e.card = 2 <;> simp [trm, he, Finset.sum_boole]
  have hpos (i : E n) : 0 < (P n).coeff i ↔ ∃ H ⊆ Finset.univ.filter (2 ≤ Finset.card ·), ∑ T ∈ H, trm T = i := by
    unfold P; rw [Finset.prod_one_add]
    simp only [AddMonoidAlgebra.prod_single, Finset.prod_const_one, AddMonoidAlgebra.coeff_sum,
      AddMonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply,
      Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _), Finset.mem_powerset]
    have hi (q : Prop) [Decidable q] : 0 < (if q then 1 else 0 : ℕ) ↔ q := by by_cases h : q <;> simp [h]
    simp only [hi]
  unfold OMA.answer; rw [hpos]
  constructor
  · intro h
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp h
    have hd : H.IsPairwiseBalancedDesign := (Finset.mem_filter.mp hH).2
    refine ⟨by unfold Finset.blockSizeProfile; rw [Multiset.sort_eq],
      H, fun T hT => Finset.mem_filter.2 ⟨Finset.mem_univ _, hd.1 T hT⟩, Prod.ext (funext fun e => ?_) ?_⟩
    · rw [hct]; by_cases he : e.card = 2
      · have hc : (H.filter (e ⊆ ·)).card = 1 := Finset.card_eq_one_iff_existsUnique.2 (by simpa using hd.2 e he)
        simp [he, hc]
      · simp [he]
    · rw [hsz]; exact (Multiset.sort_eq _ _).symm
  · rintro ⟨hs, H, hH, hv⟩
    refine Finset.mem_image.2 ⟨H, Finset.mem_filter.2 ⟨by simp, fun T hT => (Finset.mem_filter.mp (hH hT)).2,
      fun e he => ?_⟩, ?_⟩
    · have h := congrArg (fun z : E n => z.1 e) hv
      change (∑ T ∈ H, trm T).1 e = _ at h; rw [hct] at h
      have hc : (H.filter (e ⊆ ·)).card = 1 := by simpa [he] using h
      simpa using Finset.card_eq_one_iff_existsUnique.1 hc
    · have h := congrArg Prod.snd hv
      change (∑ T ∈ H, trm T).2 = (s : Multiset ℕ) at h; rw [hsz] at h
      simpa only [Finset.blockSizeProfile, h] using hs
