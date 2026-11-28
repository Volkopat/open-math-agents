import OMAStatements.S_opg_upgrading_a_completary_multifuncoid

namespace UpgradeCompletary

open OMA.S_opg_upgrading_a_completary_multifuncoid

def Boxes {ι U : Type} (R : Set (ι → U)) : Set (ι → Set U) :=
  {Y | ∃ x ∈ R, ∀ i, x i ∈ Y i}

theorem boxes_completary {ι U : Type} (R : Set (ι → U)) :
    IsCompletaryP (Boxes R) := by
  classical
  constructor
  · intro A B
    constructor
    · rintro ⟨x, hx, h⟩
      refine ⟨fun i => decide (x i ∈ B i), x, hx, fun i => ?_⟩
      by_cases hb : x i ∈ B i
      · simpa [hb]
      · simpa [hb] using (h i).resolve_right hb
    · rintro ⟨c, x, hx, h⟩
      refine ⟨x, hx, fun i => ?_⟩
      change x i ∈ A i ∨ x i ∈ B i
      specialize h i
      by_cases hc : c i = true
      · exact Or.inr (by simpa [hc] using h)
      · exact Or.inl (by simpa [hc] using h)
  · rintro Y ⟨i, hi⟩ ⟨x, _, hx⟩
    simpa [hi] using hx i

def spikes : Set (Option ℕ → ℕ) :=
  {x | ∃ k : ℕ, x none < k ∧ ∀ j : ℕ, x (some j) = if j = k then 1 else 0}

def filters (b : ℕ) : Option ℕ → Filter ℕ
  | none => Filter.atTop
  | some _ => Filter.principal {b}

theorem pair_in_upgrade :
    (fun i => filters 0 i ⊔ filters 1 i) ∈ upgrade (Boxes spikes) := by
  classical
  intro Y hY
  have hNone : Y none ∈ (Filter.atTop : Filter ℕ) := by
    simpa [filters] using Filter.le_principal_iff.mp (hY none)
  obtain ⟨n, hn⟩ := Filter.nonempty_of_mem hNone
  let x : Option ℕ → ℕ
    | none => n
    | some j => if j = n + 1 then 1 else 0
  refine ⟨x, ⟨n + 1, Nat.lt_succ_self n, fun _ => rfl⟩, ?_⟩
  intro i
  cases i with
  | none => exact hn
  | some j =>
    have h0 : 0 ∈ Y (some j) := by
      have hle : Filter.principal ({0} : Set ℕ) ≤ Filter.principal (Y (some j)) :=
        le_sup_left.trans (hY (some j))
      exact (Filter.principal_mono.mp hle) (Set.mem_singleton 0)
    have h1 : 1 ∈ Y (some j) := by
      have hle : Filter.principal ({1} : Set ℕ) ≤ Filter.principal (Y (some j)) :=
        le_sup_right.trans (hY (some j))
      exact (Filter.principal_mono.mp hle) (Set.mem_singleton 1)
    by_cases hj : j = n + 1
    · simpa [x, hj] using h1
    · simpa [x, hj] using h0

def selectedValue (c : Option ℕ → Bool) (j : ℕ) : ℕ :=
  if c (some j) then 1 else 0

def tailBox (c : Option ℕ → Bool) (m : ℕ) : Option ℕ → Set ℕ
  | none => Set.Ici m
  | some j => {selectedValue c j}

theorem tailBox_above_selection (c : Option ℕ → Bool) (m : ℕ) (i : Option ℕ) :
    (if c i then filters 1 i else filters 0 i) ≤ Filter.principal (tailBox c m i) := by
  cases i with
  | none =>
    have h : (Filter.atTop : Filter ℕ) ≤ Filter.principal (Set.Ici m) :=
      Filter.le_principal_iff.mpr (Filter.eventually_ge_atTop m)
    simpa [filters, tailBox] using h
  | some j => cases h : c (some j) <;> simp [h, filters, tailBox, selectedValue]

theorem no_selection (c : Option ℕ → Bool) :
    (fun i => if c i then filters 1 i else filters 0 i) ∉ upgrade (Boxes spikes) := by
  classical
  intro h
  obtain ⟨x, ⟨k, _, hk⟩, hx⟩ := h (tailBox c 0) (tailBox_above_selection c 0)
  obtain ⟨y, ⟨l, hyl, hl⟩, hy⟩ := h (tailBox c k) (tailBox_above_selection c k)
  have hEq : x (some k) = y (some k) :=
    (Set.mem_singleton_iff.mp (hx (some k))).trans
      (Set.mem_singleton_iff.mp (hy (some k))).symm
  have hkl : k = l := by
    by_contra hne
    rw [hk k, hl k, if_pos rfl, if_neg hne] at hEq
    exact Nat.one_ne_zero hEq
  subst l
  exact (Nat.not_lt_of_ge (hy none)) hyl

end UpgradeCompletary

open UpgradeCompletary in
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_upgrading_a_completary_multifuncoid.main) := by
  intro h
  obtain ⟨c, hc⟩ := (h ℕ (Option ℕ) (Boxes spikes) (boxes_completary spikes)).1
    (filters 0) (filters 1) |>.mp pair_in_upgrade
  exact no_selection c hc
