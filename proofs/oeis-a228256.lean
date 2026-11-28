import OMAStatements.S_oeis_a228256

namespace OMA.A228256Pf

open OMA.S_oeis_a228256

/-- Arrays that take the value `0` somewhere. -/
def Z (n : ℕ) : Finset (Fin (n + 3) → Fin 5) :=
  Finset.univ.filter (fun x => ∃ i, (x i).val = 0)

lemma card_Z (n : ℕ) : (Z n).card = 5 ^ (3 + n) - 4 ^ (3 + n) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 3) → Fin 5))) (fun x => ∃ i, (x i).val = 0)
  have hpos : (Finset.univ.filter
      (fun x : Fin (n + 3) → Fin 5 => ¬ ∃ i, (x i).val = 0)).card = 4 ^ (n + 3) := by
    have : (Finset.univ.filter
        (fun x : Fin (n + 3) → Fin 5 => ¬ ∃ i, (x i).val = 0)).card =
        (Finset.univ : Finset (Fin (n + 3) → Fin 4)).card := by
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
  have huniv : (Finset.univ : Finset (Fin (n + 3) → Fin 5)).card = 5 ^ (n + 3) := by
    simp [Fintype.card_pi]
  rw [huniv, hpos] at hsplit
  unfold Z
  rw [Nat.add_comm 3 n]
  omega

lemma image_eq (n : ℕ) : Finset.univ.image (thirdDiff n) = (Z n).image (thirdDiff n) := by
  refine Finset.Subset.antisymm ?_ (Finset.image_subset_image (Finset.filter_subset _ _))
  intro d hd
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => (x i).val)
    Finset.univ_nonempty
  let y : Fin (n + 3) → Fin 5 := fun i => ⟨(x i).val - (x i₀).val, by omega⟩
  refine Finset.mem_image.mpr ⟨y, ?_, ?_⟩
  · simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i₀, by simp [y]⟩
  · funext i
    simp only [thirdDiff, y]
    have := hmin ⟨i.1, by omega⟩ (Finset.mem_univ _)
    have := hmin ⟨i.1 + 1, by omega⟩ (Finset.mem_univ _)
    have := hmin ⟨i.1 + 2, by omega⟩ (Finset.mem_univ _)
    have := hmin ⟨i.1 + 3, by omega⟩ (Finset.mem_univ _)
    omega

/-- Equal third differences force the difference `y - x` to be a quadratic in the index. -/
lemma quad (n : ℕ) (x y : Fin (n + 3) → Fin 5) (h : thirdDiff n x = thirdDiff n y)
    (k : ℕ) (hk : k < n + 3) :
    2 * ((y ⟨k, hk⟩ : ℤ) - x ⟨k, hk⟩) = 2 * ((y ⟨0, by omega⟩ : ℤ) - x ⟨0, by omega⟩) +
      2 * k * (((y ⟨1, by omega⟩ : ℤ) - x ⟨1, by omega⟩) - ((y ⟨0, by omega⟩ : ℤ) - x ⟨0, by omega⟩)) +
      k * (k - 1) * (((y ⟨2, by omega⟩ : ℤ) - x ⟨2, by omega⟩) -
        2 * ((y ⟨1, by omega⟩ : ℤ) - x ⟨1, by omega⟩) + ((y ⟨0, by omega⟩ : ℤ) - x ⟨0, by omega⟩)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, hk with
    | 0, _ => simp
    | 1, _ => push_cast; ring
    | 2, _ => push_cast; ring
    | m + 3, hk =>
      have h0 := ih m (by omega) (by omega)
      have h1 := ih (m + 1) (by omega) (by omega)
      have h2 := ih (m + 2) (by omega) (by omega)
      have hs := congrFun h ⟨m, by omega⟩
      simp only [thirdDiff] at hs
      push_cast at h1 h2 ⊢
      linear_combination 3 * h2 - 3 * h1 + h0 - 2 * hs

lemma injOn (n : ℕ) (hn : 6 < n) : Set.InjOn (thirdDiff n) (Z n : Set (Fin (n + 3) → Fin 5)) := by
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Z, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  have hq := quad n x y hxy
  have q4 := hq 4 (by omega)
  have q5 := hq 5 (by omega)
  have q9 := hq 9 (by omega)
  simp only [Nat.cast_ofNat] at q4 q5 q9
  have b0 := (x ⟨0, by omega⟩).isLt
  have c0 := (y ⟨0, by omega⟩).isLt
  have b1 := (x ⟨1, by omega⟩).isLt
  have c1 := (y ⟨1, by omega⟩).isLt
  have b2 := (x ⟨2, by omega⟩).isLt
  have c2 := (y ⟨2, by omega⟩).isLt
  have b4 := (x ⟨4, by omega⟩).isLt
  have c4 := (y ⟨4, by omega⟩).isLt
  have b5 := (x ⟨5, by omega⟩).isLt
  have c5 := (y ⟨5, by omega⟩).isLt
  have b9 := (x ⟨9, by omega⟩).isLt
  have c9 := (y ⟨9, by omega⟩).isLt
  have hE : ((y ⟨2, by omega⟩ : ℤ) - x ⟨2, by omega⟩) -
      2 * ((y ⟨1, by omega⟩ : ℤ) - x ⟨1, by omega⟩) + ((y ⟨0, by omega⟩ : ℤ) - x ⟨0, by omega⟩) = 0 := by
    omega
  have hD : ((y ⟨1, by omega⟩ : ℤ) - x ⟨1, by omega⟩) - ((y ⟨0, by omega⟩ : ℤ) - x ⟨0, by omega⟩) = 0 := by
    omega
  have hconst : ∀ i : Fin (n + 3), (y i : ℤ) - x i = (y ⟨0, by omega⟩ : ℤ) - x ⟨0, by omega⟩ := by
    intro i
    have := hq i.1 i.2
    simp only [Fin.eta] at this
    have h2 : 2 * (((y i : ℤ) - x i) - ((y ⟨0, by omega⟩ : ℤ) - x ⟨0, by omega⟩)) = 0 := by
      linear_combination this + 2 * (i.1 : ℤ) * hD + (i.1 : ℤ) * ((i.1 : ℤ) - 1) * hE
    omega
  obtain ⟨i₀, hi₀⟩ := hx
  obtain ⟨j₀, hj₀⟩ := hy
  have h1 := hconst i₀
  have h2 := hconst j₀
  funext i
  have := hconst i
  exact Fin.ext (by omega)

end OMA.A228256Pf

theorem OMA.solution : type_of% @OMA.S_oeis_a228256.main := by
  intro n hn
  unfold OMA.S_oeis_a228256.a
  rw [OMA.A228256Pf.image_eq, Finset.card_image_of_injOn (OMA.A228256Pf.injOn n hn),
    OMA.A228256Pf.card_Z]
