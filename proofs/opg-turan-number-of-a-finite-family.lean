import OMAStatements.S_opg_turan_number_of_a_finite_family
import Mathlib

/-!
# Turan number of a finite family: the statement as formalized is false

The formal statement does not exclude forests. Take the family consisting of the path on
three vertices `P3` and the matching with two edges `M2`. Any graph with two distinct edges
contains one of them (the two edges either share a vertex or are disjoint), so the family
extremal number is at most `1`. But a perfect matching is `P3`-free and a star is `M2`-free,
so both single extremal numbers are unbounded.
-/

namespace OMA.TuranFamily

open SimpleGraph

/-- The path on three vertices, with centre `1`. -/
def P3 : SimpleGraph (Fin 3) where
  Adj a b := a ≠ b ∧ (a = 1 ∨ b = 1)
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- Two disjoint edges `0-1` and `2-3`. -/
def M2 : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b ∧ a.val / 2 = b.val / 2
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- The matching `2k - 2k+1` on `Fin n`. -/
def matching (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj a b := a ≠ b ∧ a.val / 2 = b.val / 2
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- The star centred at `0` on `Fin (n+1)`. -/
def star (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj a b := a ≠ b ∧ (a = 0 ∨ b = 0)
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

lemma P3_adj (a b : Fin 3) : P3.Adj a b ↔ a ≠ b ∧ (a = 1 ∨ b = 1) := Iff.rfl

lemma M2_adj (a b : Fin 4) : M2.Adj a b ↔ a ≠ b ∧ a.val / 2 = b.val / 2 := Iff.rfl

lemma matching_adj (n : ℕ) (a b : Fin (n + 1)) :
    (matching n).Adj a b ↔ a ≠ b ∧ a.val / 2 = b.val / 2 := Iff.rfl

lemma star_adj (n : ℕ) (a b : Fin (n + 1)) :
    (star n).Adj a b ↔ a ≠ b ∧ (a = 0 ∨ b = 0) := Iff.rfl

lemma p3_of {V : Type} (G : SimpleGraph V) (a b d : V) (hab : G.Adj a b) (had : G.Adj a d)
    (hbd : b ≠ d) : P3 ⊑ G := by
  have hba := hab.symm
  have hda := had.symm
  have h1 := hab.ne
  have h2 := had.ne
  refine ⟨⟨⟨![b, a, d], ?_⟩, ?_⟩⟩
  · intro x y hxy
    rw [P3_adj] at hxy
    obtain ⟨hne, hc⟩ := hxy
    fin_cases x <;> fin_cases y <;> simp_all
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all

lemma m2_of {V : Type} (G : SimpleGraph V) (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : M2 ⊑ G := by
  have hba := hab.symm
  have hdc := hcd.symm
  have h1 := hab.ne
  have h2 := hcd.ne
  refine ⟨⟨⟨![a, b, c, d], ?_⟩, ?_⟩⟩
  · intro x y hxy
    rw [M2_adj] at hxy
    obtain ⟨hne, hc⟩ := hxy
    fin_cases x <;> fin_cases y <;> simp_all
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all

lemma two_edges {V : Type} (G : SimpleGraph V) (e₁ e₂ : Sym2 V) (h₁ : e₁ ∈ G.edgeSet)
    (h₂ : e₂ ∈ G.edgeSet) (hne : e₁ ≠ e₂) : P3 ⊑ G ∨ M2 ⊑ G := by
  induction e₁ with
  | h a b =>
  induction e₂ with
  | h c d =>
  rw [mem_edgeSet] at h₁ h₂
  by_cases hac : a = c
  · subst hac
    refine Or.inl (p3_of G a b d h₁ h₂ ?_)
    rintro rfl
    exact hne rfl
  by_cases had : a = d
  · subst had
    refine Or.inl (p3_of G a b c h₁ h₂.symm ?_)
    rintro rfl
    exact hne Sym2.eq_swap
  by_cases hbc : b = c
  · subst hbc
    exact Or.inl (p3_of G b a d h₁.symm h₂ had)
  by_cases hbd : b = d
  · subst hbd
    exact Or.inl (p3_of G b a c h₁.symm h₂.symm hac)
  exact Or.inr (m2_of G a b c d h₁ h₂ hac had hbc hbd)

/-- The family: `P3` and `M2`. -/
abbrev W : Fin 2 → Type := fun i => Fin (i.val + 3)

instance : ∀ i, Fintype (W i) := fun i => inferInstanceAs (Fintype (Fin (i.val + 3)))

def F : ∀ i, SimpleGraph (W i) := fun i =>
  match i with
  | ⟨0, _⟩ => P3
  | ⟨1, _⟩ => M2

lemma family_le (n : ℕ) :
    OMA.S_opg_turan_number_of_a_finite_family.familyExtremalNumber n F ≤ 1 := by
  unfold OMA.S_opg_turan_number_of_a_finite_family.familyExtremalNumber
  rcases Set.eq_empty_or_nonempty
    {k | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = k ∧ ∀ i, ¬ (F i).IsContained G} with h | h
  · rw [h]; simp
  · refine csSup_le h ?_
    rintro k ⟨G, rfl, hG⟩
    by_contra hk
    push Not at hk
    obtain ⟨e₁, h₁, e₂, h₂, hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp hk
    rcases two_edges G e₁ e₂ h₁ h₂ hne with h | h
    · exact hG 0 h
    · exact hG 1 h

lemma matching_free (n : ℕ) : P3.Free (matching n) := by
  rintro ⟨f⟩
  have h01 : (matching n).Adj (f 0) (f 1) := f.toHom.map_adj (by simp [P3_adj])
  have h21 : (matching n).Adj (f 2) (f 1) := f.toHom.map_adj (by simp [P3_adj])
  have h02 : f 0 ≠ f 2 := fun h => by simpa using f.injective h
  rw [matching_adj] at h01 h21
  obtain ⟨a1, a2⟩ := h01
  obtain ⟨b1, b2⟩ := h21
  have c1 : (f 0).val ≠ (f 1).val := fun h => a1 (Fin.ext h)
  have c2 : (f 2).val ≠ (f 1).val := fun h => b1 (Fin.ext h)
  have c3 : (f 0).val ≠ (f 2).val := fun h => h02 (Fin.ext h)
  omega

lemma star_free (n : ℕ) : M2.Free (star n) := by
  rintro ⟨f⟩
  have h01 : (star n).Adj (f 0) (f 1) := f.toHom.map_adj (by simp [M2_adj])
  have h23 : (star n).Adj (f 2) (f 3) := f.toHom.map_adj (by simp [M2_adj])
  have i02 : f 0 ≠ f 2 := fun h => by simpa using f.injective h
  have i03 : f 0 ≠ f 3 := fun h => by simpa using f.injective h
  have i12 : f 1 ≠ f 2 := fun h => by simpa using f.injective h
  have i13 : f 1 ≠ f 3 := fun h => by simpa using f.injective h
  rw [star_adj] at h01 h23
  obtain ⟨-, a⟩ := h01
  obtain ⟨-, b⟩ := h23
  rcases a with a | a <;> rcases b with b | b <;> simp_all

lemma val_cast (m j : ℕ) (h : j < m + 1) : (Fin.ofNat (m + 1) j).val = j := by
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt h]

lemma matching_big (C m : ℕ) (hm : 2 * C + 1 < m + 1) : C < extremalNumber (m + 1) P3 := by
  classical
  have cnt : (Finset.range (C + 1)).card ≤ (matching m).edgeFinset.card := by
    refine Finset.card_le_card_of_injOn
      (fun k => s(Fin.ofNat (m + 1) (2 * k), Fin.ofNat (m + 1) (2 * k + 1))) ?_ ?_
    · intro k hk
      have hk' : k < C + 1 := by simpa using hk
      simp only [Finset.mem_coe, mem_edgeFinset, mem_edgeSet, matching_adj]
      refine ⟨fun h => ?_, ?_⟩
      · have := congrArg Fin.val h
        rw [val_cast m _ (by omega), val_cast m _ (by omega)] at this
        omega
      · rw [val_cast m _ (by omega), val_cast m _ (by omega)]
        omega
    · intro k hk k' hk' h
      have hk1 : k < C + 1 := by simpa using hk
      have hk2 : k' < C + 1 := by simpa using hk'
      simp only [Sym2.eq_iff] at h
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
      · have := congrArg Fin.val h1
        rw [val_cast m _ (by omega), val_cast m _ (by omega)] at this
        omega
      · have := congrArg Fin.val h1
        rw [val_cast m _ (by omega), val_cast m _ (by omega)] at this
        omega
  rw [Finset.card_range] at cnt
  have := (lt_extremalNumber_iff (V := Fin (m + 1)) P3 C).mpr
    ⟨matching m, inferInstance, matching_free m, by omega⟩
  simpa using this

lemma star_big (C m : ℕ) (hm : C + 1 < m + 1) : C < extremalNumber (m + 1) M2 := by
  classical
  have cnt : (Finset.range (C + 1)).card ≤ (star m).edgeFinset.card := by
    refine Finset.card_le_card_of_injOn
      (fun k => s((0 : Fin (m + 1)), Fin.ofNat (m + 1) (k + 1))) ?_ ?_
    · intro k hk
      have hk' : k < C + 1 := by simpa using hk
      simp only [Finset.mem_coe, mem_edgeFinset, mem_edgeSet, star_adj]
      refine ⟨fun h => ?_, Or.inl trivial⟩
      have := congrArg Fin.val h
      rw [val_cast m _ (by omega), Fin.val_zero] at this
      omega
    · intro k hk k' hk' h
      have hk1 : k < C + 1 := by simpa using hk
      have hk2 : k' < C + 1 := by simpa using hk'
      simp only [Sym2.eq_iff] at h
      rcases h with ⟨-, h1⟩ | ⟨-, h1⟩
      · have := congrArg Fin.val h1
        rw [val_cast m _ (by omega), val_cast m _ (by omega)] at this
        omega
      · have := congrArg Fin.val h1
        rw [val_cast m _ (by omega), Fin.val_zero] at this
        omega
  rw [Finset.card_range] at cnt
  have := (lt_extremalNumber_iff (V := Fin (m + 1)) M2 C).mpr
    ⟨star m, inferInstance, star_free m, by omega⟩
  simpa using this

end OMA.TuranFamily

open OMA.TuranFamily in
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_turan_number_of_a_finite_family.main) := by
  intro h
  obtain ⟨i, C, N, hb⟩ := h 2 (by norm_num) W F
  have h1 := hb (N + 2 * C + 1 + 1) (by omega)
  have h2 := Nat.mul_le_mul_left C (family_le (N + 2 * C + 1 + 1))
  fin_cases i
  · have h3 : C < SimpleGraph.extremalNumber (N + 2 * C + 1 + 1) (F 0) :=
      matching_big C (N + 2 * C + 1) (by omega)
    simp only [Fin.zero_eta] at h1
    omega
  · have h3 : C < SimpleGraph.extremalNumber (N + 2 * C + 1 + 1) (F 1) :=
      star_big C (N + 2 * C + 1) (by omega)
    simp only [Fin.mk_one] at h1
    omega
