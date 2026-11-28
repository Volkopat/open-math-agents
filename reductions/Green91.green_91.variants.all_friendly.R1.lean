import FormalConjectures.GreensOpenProblems.«91»

/-! The even-size positive-margin result implies the exact all-size
formulation. A chosen last vertex can be deleted after putting it in the
first half. The remaining margins decrease by at most one. -/

namespace OMA.R_Green91_green_91_variants_all_friendly_R1

open Green91 Finset Filter MeasureTheory Topology
open scoped Classical

private theorem filter_drop_last (n : ℕ) (P : Fin (n + 1) → Prop)
    [DecidablePred P] :
    (univ.filter (fun x : Fin n ↦ P x.castSucc)).map Fin.castSuccEmb =
      (univ.filter P).erase (Fin.last n) := by
  classical
  ext y
  induction y using Fin.lastCases with
  | last => simp [Finset.mem_map, Fin.castSuccEmb_apply, Fin.castSucc_ne_last]
  | cast y => simp [Finset.mem_map, Fin.castSuccEmb_apply, Fin.castSucc_ne_last]

private theorem filter_counts (n : ℕ) (P : Fin (n + 1) → Prop)
    [DecidablePred P] :
    (univ.filter (fun x : Fin n ↦ P x.castSucc)).card ≤ (univ.filter P).card ∧
    (univ.filter P).card ≤ (univ.filter (fun x : Fin n ↦ P x.castSucc)).card + 1 := by
  classical
  have h : (univ.filter (fun x : Fin n ↦ P x.castSucc)).card =
      ((univ.filter P).erase (Fin.last n)).card := by
    rw [← filter_drop_last n P, card_map]
  rw [h]
  refine ⟨card_erase_le, ?_⟩
  by_cases hmem : Fin.last n ∈ univ.filter P
  · have hpos : 0 < (univ.filter P).card := card_pos.mpr ⟨_, hmem⟩
    rw [card_erase_of_mem hmem]
    omega
  · rw [erase_eq_of_notMem hmem]
    omega

private theorem friendliness_complement {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) (v : Fin n) : friendliness G sᶜ v = friendliness G s v := by
  classical
  have same (w : Fin n) : ((w ∈ sᶜ ↔ v ∈ sᶜ) ↔ (w ∈ s ↔ v ∈ s)) := by
    simp only [mem_compl]
    tauto
  simp only [friendliness, same]

private theorem delete_friendly {n m : ℕ} (hn : 2 * m = n + 1)
    (G : SimpleGraph (Fin (n + 1))) (s : Finset (Fin (n + 1))) (hs : s.card = m)
    (hf : ∀ v, 2 ≤ friendliness G s v) :
    ∃ t : Finset (Fin n), t.card = n / 2 ∧
      ∀ v, 0 < friendliness (G.comap Fin.castSucc) t v := by
  classical
  have orient : ∃ t : Finset (Fin (n + 1)), t.card = m ∧ Fin.last n ∈ t ∧
      ∀ v, 2 ≤ friendliness G t v := by
    by_cases hl : Fin.last n ∈ s
    · exact ⟨s, hs, hl, hf⟩
    · refine ⟨sᶜ, ?_, mem_compl.mpr hl, fun v ↦ ?_⟩
      · rw [Finset.card_compl, Fintype.card_fin, hs]
        omega
      · rw [friendliness_complement]
        exact hf v
  obtain ⟨s₀, hs₀, hl, hs₀f⟩ := orient
  let t := univ.filter (fun x : Fin n ↦ x.castSucc ∈ s₀)
  have t_mem (x : Fin n) : x ∈ t ↔ x.castSucc ∈ s₀ := by simp [t]
  refine ⟨t, ?_, ?_⟩
  · have hfull : univ.filter (fun x ↦ x ∈ s₀) = s₀ := by ext x; simp
    have hsmall : univ.filter (fun x : Fin n ↦ x.castSucc ∈ s₀) = t := by
      ext x
      simp [t_mem]
    have hmap := filter_drop_last n (fun x ↦ x ∈ s₀)
    rw [hsmall, hfull] at hmap
    calc
      t.card = (t.map Fin.castSuccEmb).card := (card_map _).symm
      _ = n / 2 := by rw [hmap, card_erase_of_mem hl, hs₀]; omega
  · intro v
    let own (w : Fin (n + 1)) := G.Adj v.castSucc w ∧ (w ∈ s₀ ↔ v.castSucc ∈ s₀)
    let other (w : Fin (n + 1)) := G.Adj v.castSucc w ∧ ¬ (w ∈ s₀ ↔ v.castSucc ∈ s₀)
    have cntOwn : ((univ.filter own).card : ℤ) ≤
        (univ.filter (fun x : Fin n ↦ own x.castSucc)).card + 1 := by
      exact_mod_cast (filter_counts n own).2
    have cntOther : ((univ.filter (fun x : Fin n ↦ other x.castSucc)).card : ℤ) ≤
        (univ.filter other).card := by
      exact_mod_cast (filter_counts n other).1
    have eqOld : friendliness G s₀ v.castSucc =
        ((univ.filter own).card : ℤ) - (univ.filter other).card := by
      unfold friendliness
      apply congrArg₂ (· - ·) <;>
        apply congrArg (fun A : Finset (Fin (n + 1)) ↦ (A.card : ℤ)) <;>
        ext w <;> simp [own, other]
    have eqNew : friendliness (G.comap Fin.castSucc) t v =
        ((univ.filter (fun x : Fin n ↦ own x.castSucc)).card : ℤ) -
          (univ.filter (fun x : Fin n ↦ other x.castSucc)).card := by
      unfold friendliness
      apply congrArg₂ (· - ·) <;>
        apply congrArg (fun A : Finset (Fin n) ↦ (A.card : ℤ)) <;>
        ext w <;> simp [own, other, t_mem]
    have old : 2 ≤ ((univ.filter own).card : ℤ) - (univ.filter other).card := by
      rw [← eqOld]
      exact hs₀f v.castSucc
    rw [eqNew]
    linarith only [cntOwn, cntOther, old]

private theorem prob_mono {n : ℕ} {P Q : SimpleGraph (Fin n) → Prop}
    (h : ∀ G, P G → Q G) : prob n P ≤ prob n Q :=
  measure_mono fun G hG ↦ h G hG

/-- The even-size random graph has a bisection whose smallest margin is
at least two, with probability tending to one. -/
def H1 : Prop :=
  Tendsto (fun m : ℕ ↦ prob (2 * m) fun G ↦
    ∃ s : Finset (Fin (2 * m)), s.card = m ∧ ∀ v, 2 ≤ friendliness G s v)
    atTop (𝓝 1)

/-- Deleting a fixed vertex preserves the binomial random graph law on
the remaining labeled vertices. -/
def H2 : Prop :=
  ∀ (n : ℕ) (P : SimpleGraph (Fin n) → Prop),
    prob (n + 1) (fun G ↦ P (G.comap Fin.castSucc)) = prob n P

theorem main : H1 → H2 → type_of% @Green91.green_91.variants.all_friendly := by
  classical
  intro even restriction
  let margin (m : ℕ) (G : SimpleGraph (Fin (2 * m))) :=
    ∃ s : Finset (Fin (2 * m)), s.card = m ∧ ∀ v, 2 ≤ friendliness G s v
  let good (n : ℕ) (G : SimpleGraph (Fin n)) :=
    ∃ s : Finset (Fin n), s.card = n / 2 ∧ ∀ v, 0 < friendliness G s v
  let lower := fun n : ℕ ↦ prob (2 * ((n + 1) / 2)) (margin ((n + 1) / 2))
  have diverges : Tendsto (fun n : ℕ ↦ (n + 1) / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact (eventually_ge_atTop (2 * b)).mono fun n hn ↦ by omega
  have lo : Tendsto lower atTop (𝓝 1) := even.comp diverges
  have le_good (n : ℕ) : lower n ≤ prob n (good n) := by
    let m := (n + 1) / 2
    have hcases : 2 * m = n ∨ 2 * m = n + 1 := by dsimp [m]; omega
    rcases hcases with h | h
    · have upper : prob (2 * m) (margin m) ≤ prob (2 * m) (good (2 * m)) := by
        apply prob_mono
        rintro G ⟨s, hs, hf⟩
        exact ⟨s, by omega, fun v ↦ (by decide : (0 : ℤ) < 2).trans_le (hf v)⟩
      exact upper.trans_eq (by rw [h])
    · let extended (G : SimpleGraph (Fin (n + 1))) :=
        ∃ s : Finset (Fin (n + 1)), s.card = m ∧ ∀ v, 2 ≤ friendliness G s v
      have eq : lower n = prob (n + 1) extended := by
        change prob (2 * m)
          (fun G ↦ ∃ s : Finset (Fin (2 * m)), s.card = m ∧ ∀ v, 2 ≤ friendliness G s v) = _
        rw [h]
      rw [eq, ← restriction n (good n)]
      apply prob_mono
      rintro G ⟨s, hs, hf⟩
      exact delete_friendly h G s hs hf
  have hi (n : ℕ) : prob n (good n) ≤ 1 := by
    unfold prob
    exact prob_le_one
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le lo tendsto_const_nhds le_good hi

end OMA.R_Green91_green_91_variants_all_friendly_R1
