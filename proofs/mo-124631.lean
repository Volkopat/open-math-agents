import OMAStatements.S_mo_124631

open OMA.S_mo_124631

private theorem mem_of_inf_eq {ι α : Type} [LinearOrder α] [OrderTop α]
    {s : Finset ι} {f : ι → α} {a : α} (hs : s.Nonempty) (h : s.inf f = a) :
    ∃ i ∈ s, f i = a := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf s hs f
  exact ⟨i, hi, he.symm.trans h⟩

section

variable {J T : Type} [DecidableEq J] [AddCommMonoid T] [LinearOrder T]
variable (w : J → T)

private theorem session_le {S : Finset J} {qs : List (Finset J)} (h : Packs S qs) :
    oneSession w qs.length S ≤ ↑(duration w qs) := by
  induction qs generalizing S with
  | nil =>
    change S = ∅ at h
    subst S
    simp [oneSession, duration]
  | cons Q qs ih =>
    obtain ⟨hQ, hrest⟩ := h
    rw [List.length_cons, oneSession, duration, WithTop.coe_max]
    exact (Finset.inf_le (Finset.mem_powerset.mpr hQ)).trans
      (max_le_max_left _ (ih hrest))

private theorem session_attains (p : ℕ) (S : Finset J) (t : T)
    (h : oneSession w p S = (t : WithTop T)) :
    ∃ qs, Packs S qs ∧ qs.length = p ∧ duration w qs = t := by
  induction p generalizing S t with
  | zero =>
    rw [oneSession] at h
    split at h
    next hS => exact ⟨[], hS, rfl, WithTop.coe_inj.mp h⟩
    next => simp at h
  | succ p ih =>
    rw [oneSession] at h
    obtain ⟨Q, hQ, he⟩ := mem_of_inf_eq S.powerset_nonempty h
    change max ((∑ j ∈ Q, w j : T) : WithTop T) (oneSession w p (S \ Q)) = ↑t at he
    have hfin : oneSession w p (S \ Q) ≠ ⊤ := by
      intro hinf
      simp [hinf] at he
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hfin
    obtain ⟨qs, hpack, hlen, htime⟩ := ih (S \ Q) u hu.symm
    refine ⟨Q :: qs, ⟨Finset.mem_powerset.mp hQ, hpack⟩, by simp [hlen], ?_⟩
    rw [duration, htime]
    exact WithTop.coe_inj.mp (by simpa only [← hu, ← WithTop.coe_max] using he)

omit [DecidableEq J] in
private theorem duration_nonneg (qs : List (Finset J)) : 0 ≤ duration w qs := by
  induction qs with
  | nil => exact le_rfl
  | cons Q qs ih => exact ih.trans (le_max_right _ _)

variable (p : ℕ) (W : T)

private theorem optimum_le [IsOrderedAddMonoid T] {S : Finset J} {plan : List (List (Finset J))}
    (h : Legal w p W S plan) : optimum w p W S ≤ ↑(elapsed w plan) := by
  induction plan generalizing S with
  | nil =>
    change S = ∅ at h
    subst S
    rw [optimum, if_pos rfl]
    exact le_rfl
  | cons qs rest ih =>
    obtain ⟨R, hRS, hpack, hlen, hcap, hrest⟩ := h
    have htail := ih hrest
    rw [elapsed, WithTop.coe_add]
    by_cases heq : R = S
    · subst R
      exact htail.trans (le_add_of_nonneg_left (WithTop.coe_le_coe.mpr (duration_nonneg w qs)))
    · have hstrict := Finset.ssubset_iff_subset_ne.mpr ⟨hRS, heq⟩
      have hS : S ≠ ∅ := fun h => Finset.not_ssubset_empty R (h ▸ hstrict)
      let r : ↥S.ssubsets := ⟨R, Finset.mem_ssubsets.mpr hstrict⟩
      have hsession := session_le w hpack
      rw [hlen] at hsession
      have hbound := hsession.trans (WithTop.coe_le_coe.mpr hcap)
      rw [optimum, if_neg hS]
      refine (Finset.inf_le (Finset.mem_attach _ r)).trans ?_
      change (if oneSession w p (S \ R) ≤ ↑W then
        oneSession w p (S \ R) + optimum w p W R else ⊤) ≤ _
      rw [if_pos hbound]
      exact add_le_add hsession htail

private theorem optimum_attains (S : Finset J) (t : T) (h : optimum w p W S = (t : WithTop T)) :
    ∃ plan, Legal w p W S plan ∧ elapsed w plan = t := by
  induction S using Finset.strongInductionOn generalizing t with
  | _ S ih =>
    rw [optimum] at h
    split at h
    next hS => exact ⟨[], hS, WithTop.coe_inj.mp h⟩
    next hS =>
      have hempty := Finset.empty_mem_ssubsets (Finset.nonempty_iff_ne_empty.mpr hS)
      have hne : S.ssubsets.attach.Nonempty := ⟨⟨∅, hempty⟩, Finset.mem_attach _ _⟩
      obtain ⟨r, _, he⟩ := mem_of_inf_eq hne h
      change (if oneSession w p (S \ r.val) ≤ ↑W then
        oneSession w p (S \ r.val) + optimum w p W r.val else ⊤) = ↑t at he
      split at he
      next hcap =>
        have hfirst : oneSession w p (S \ r.val) ≠ ⊤ := by
          intro hinf
          simp [hinf] at hcap
        have hlast : optimum w p W r.val ≠ ⊤ := by
          intro hinf
          simp [hinf] at he
        obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hfirst
        obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hlast
        obtain ⟨qs, hpack, hlen, htime⟩ := session_attains w p _ a ha.symm
        have hstrict := Finset.mem_ssubsets.mp r.property
        obtain ⟨rest, hrest, htail⟩ := ih r.val hstrict b hb.symm
        refine ⟨qs :: rest, ⟨r.val, hstrict.le, hpack, hlen, ?_, hrest⟩, ?_⟩
        · rw [htime]
          exact WithTop.coe_le_coe.mp (ha.le.trans hcap)
        · rw [elapsed, htime, htail]
          exact WithTop.coe_inj.mp (by simpa only [← ha, ← hb, ← WithTop.coe_add] using he)
      next => simp at he

end

theorem OMA.solution : type_of% @OMA.S_mo_124631.main := by
  intro J T _ _ _ _ S p _ w W _ _
  constructor
  · constructor
    · rintro hinf ⟨plan, hlegal⟩
      have h := optimum_le w p W hlegal
      simp [hinf] at h
    · intro hnone
      by_contra hfin
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfin
      obtain ⟨plan, hlegal, _⟩ := optimum_attains w p W S t ht.symm
      exact hnone ⟨plan, hlegal⟩
  · intro t ht
    obtain ⟨plan, hlegal, htime⟩ := optimum_attains w p W S t ht
    refine ⟨plan, hlegal, htime, fun other hother => ?_⟩
    exact WithTop.coe_le_coe.mp (ht ▸ optimum_le w p W hother)
