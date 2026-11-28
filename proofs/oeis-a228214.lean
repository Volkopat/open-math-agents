import OMAStatements.S_oeis_a228214

namespace OMA.A228214Pf

open OMA.S_oeis_a228214

/-- Arrays that take the value `0` somewhere. -/
def Z (n : ℕ) : Finset (Fin (n + 2) → Fin 5) :=
  Finset.univ.filter (fun x => ∃ i, (x i).val = 0)

lemma card_Z (n : ℕ) : (Z n).card = 5 ^ (2 + n) - 4 ^ (2 + n) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 2) → Fin 5))) (fun x => ∃ i, (x i).val = 0)
  have hpos : (Finset.univ.filter
      (fun x : Fin (n + 2) → Fin 5 => ¬ ∃ i, (x i).val = 0)).card = 4 ^ (n + 2) := by
    have : (Finset.univ.filter
        (fun x : Fin (n + 2) → Fin 5 => ¬ ∃ i, (x i).val = 0)).card =
        (Finset.univ : Finset (Fin (n + 2) → Fin 4)).card := by
      refine Finset.card_bij (fun x _ i => ⟨(x i).val - 1, by omega⟩) (by simp) ?_ ?_
      · intro x hx y hy hxy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hx hy
        funext i
        have h := congrArg (fun f => (f i).val) hxy
        have := hx i
        have := hy i
        simp only at h
        exact Fin.ext (by omega)
      · intro z _
        refine ⟨fun i => ⟨(z i).val + 1, by omega⟩, ?_, ?_⟩
        · simp
        · funext i; exact Fin.ext (by simp)
    rw [this]; simp [Fintype.card_pi]
  have huniv : (Finset.univ : Finset (Fin (n + 2) → Fin 5)).card = 5 ^ (n + 2) := by
    simp [Fintype.card_pi]
  rw [huniv, hpos] at hsplit
  unfold Z
  rw [Nat.add_comm 2 n]
  omega

lemma image_eq (n : ℕ) : Finset.univ.image (secondDiff n) = (Z n).image (secondDiff n) := by
  refine Finset.Subset.antisymm ?_ (Finset.image_subset_image (Finset.filter_subset _ _))
  intro d hd
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => (x i).val)
    Finset.univ_nonempty
  let y : Fin (n + 2) → Fin 5 := fun i => ⟨(x i).val - (x i₀).val, by omega⟩
  refine Finset.mem_image.mpr ⟨y, ?_, ?_⟩
  · simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i₀, by simp [y]⟩
  · funext i
    simp only [secondDiff, y]
    have := hmin ⟨i.1, by omega⟩ (Finset.mem_univ _)
    have := hmin ⟨i.1 + 1, by omega⟩ (Finset.mem_univ _)
    have := hmin ⟨i.1 + 2, by omega⟩ (Finset.mem_univ _)
    omega

lemma linear (n : ℕ) (x y : Fin (n + 2) → Fin 5) (h : secondDiff n x = secondDiff n y)
    (k : ℕ) (hk : k < n + 2) :
    (y ⟨k, hk⟩ : ℤ) - x ⟨k, hk⟩ = ((y ⟨0, by omega⟩ : ℤ) - x ⟨0, by omega⟩) +
      k * (((y ⟨1, by omega⟩ : ℤ) - x ⟨1, by omega⟩) - ((y ⟨0, by omega⟩ : ℤ) - x ⟨0, by omega⟩)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, hk with
    | 0, _ => simp
    | 1, _ => simp
    | m + 2, hk =>
      have h0 := ih m (by omega) (by omega)
      have h1 := ih (m + 1) (by omega) (by omega)
      have hs := congrFun h ⟨m, by omega⟩
      simp only [secondDiff] at hs
      push_cast at h1 ⊢
      linarith

lemma injOn (n : ℕ) (hn : 7 < n) : Set.InjOn (secondDiff n) (Z n : Set (Fin (n + 2) → Fin 5)) := by
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Z, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  have hl := linear n x y hxy
  set c : ℤ := (y ⟨0, by omega⟩ : ℤ) - x ⟨0, by omega⟩ with hc
  set d : ℤ := ((y ⟨1, by omega⟩ : ℤ) - x ⟨1, by omega⟩) - c with hd
  have hlast := hl (n + 1) (by omega)
  have b1 : (x ⟨0, by omega⟩ : ℤ) < 5 := by have := (x ⟨0, by omega⟩).isLt; omega
  have b2 : (y ⟨0, by omega⟩ : ℤ) < 5 := by have := (y ⟨0, by omega⟩).isLt; omega
  have b3 : (x ⟨n + 1, by omega⟩ : ℤ) < 5 := by have := (x ⟨n + 1, by omega⟩).isLt; omega
  have b4 : (y ⟨n + 1, by omega⟩ : ℤ) < 5 := by have := (y ⟨n + 1, by omega⟩).isLt; omega
  have p1 : (0 : ℤ) ≤ (x ⟨0, by omega⟩ : ℤ) := by positivity
  have p2 : (0 : ℤ) ≤ (y ⟨0, by omega⟩ : ℤ) := by positivity
  have p3 : (0 : ℤ) ≤ (x ⟨n + 1, by omega⟩ : ℤ) := by positivity
  have p4 : (0 : ℤ) ≤ (y ⟨n + 1, by omega⟩ : ℤ) := by positivity
  have hd0 : d = 0 := by
    have hN : (9 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by omega
    have e1 : ((n + 1 : ℕ) : ℤ) * d ≤ 8 := by linarith
    have e2 : -8 ≤ ((n + 1 : ℕ) : ℤ) * d := by linarith
    rcases lt_trichotomy d 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  have hE := hd.symm.trans hd0
  have hconst : ∀ i : Fin (n + 2), (y i : ℤ) - x i = c := by
    intro i
    have := hl i.1 i.2
    simp only [Fin.eta] at this
    linear_combination this + ((i.1 : ℤ) - 1) * hc + (i.1 : ℤ) * hE
  obtain ⟨i₀, hi₀⟩ := hx
  obtain ⟨j₀, hj₀⟩ := hy
  have h1 := hconst i₀
  have h2 := hconst j₀
  have hc0 : c = 0 := by omega
  funext i
  have := hconst i
  exact Fin.ext (by omega)

end OMA.A228214Pf

theorem OMA.solution : type_of% @OMA.S_oeis_a228214.main := by
  intro n hn
  unfold OMA.S_oeis_a228214.a
  rw [OMA.A228214Pf.image_eq, Finset.card_image_of_injOn (OMA.A228214Pf.injOn n hn),
    OMA.A228214Pf.card_Z]
