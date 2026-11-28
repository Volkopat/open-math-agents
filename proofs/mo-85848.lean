import OMAStatements.S_mo_85848

open OMA.S_mo_85848

theorem OMA.solution : type_of% @OMA.S_mo_85848.main := by
  intro p d hp V hadd hmod hfinite hdim
  rintro ⟨W, _, _, hjoin, x, hx⟩
  let T := tailIntersection W
  have hmem (k : ℕ) (v : V) :
      v ∈ T k ↔ ∀ j : Fin (d + 1), k ≤ j.val → v ∈ W j := by
    simp [T, tailIntersection]
  have hnext (k : ℕ) (hk : k ≤ d) :
      T k = W ⟨k, by omega⟩ ⊓ T (k + 1) := by
    ext v
    rw [Submodule.mem_inf, hmem, hmem]
    constructor
    · intro hv
      exact ⟨hv ⟨k, by omega⟩ le_rfl, fun j hj => hv j (by omega)⟩
    · rintro ⟨hv, ht⟩ j hj
      by_cases he : j.val = k
      · have hjk : j = ⟨k, by omega⟩ := Fin.ext he
        rwa [hjk]
      · exact ht j (by omega)
  have htop : T (d + 1) = ⊤ := by
    apply top_unique
    intro v _
    exact (hmem _ _).2 (fun j hj => (not_le_of_gt j.isLt hj).elim)
  have hstrict (k : ℕ) (hk : k ≤ d) : T k < T (k + 1) := by
    rw [hnext k hk]
    refine lt_of_le_of_ne inf_le_right ?_
    intro he
    have hle : T (k + 1) ≤ W ⟨k, by omega⟩ := by
      rw [← he]
      exact inf_le_left
    have hfull : W ⟨k, by omega⟩ = ⊤ := by
      rcases lt_or_eq_of_le hk with hkd | rfl
      · exact (sup_eq_left.mpr hle).symm.trans (hjoin ⟨k, hkd⟩)
      · rwa [htop, top_le_iff] at hle
    exact hx ⟨k, by omega⟩ (hfull ▸ Submodule.mem_top)
  have hbound (k : ℕ) : k ≤ d + 1 → k ≤ Module.finrank (ZMod p) (T k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hinc := Submodule.finrank_lt_finrank_of_lt (hstrict k (by omega))
      omega
  have h := hbound (d + 1) le_rfl
  rw [htop, finrank_top, hdim] at h
  omega
