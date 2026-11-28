import OMAStatements.S_oeis_a228212

namespace OMA.A228212Proof

open OMA.S_oeis_a228212

private def zeroSet (n : ℕ) : Finset (Fin (n + 2) → Fin 3) :=
  Finset.univ.filter (fun x => ∃ i : Fin (n + 2), (x i).val = 0)

private lemma card_zeroSet (n : ℕ) : (zeroSet n).card = 3 ^ (2 + n) - 2 ^ (2 + n) := by
  have hcomp : (zeroSet n).card +
      (Finset.univ.filter (fun x : Fin (n + 2) → Fin 3 => ¬ ∃ i, (x i).val = 0)).card =
      (Finset.univ : Finset (Fin (n + 2) → Fin 3)).card :=
    Finset.card_filter_add_card_filter_not _
  have huniv : (Finset.univ : Finset (Fin (n + 2) → Fin 3)).card = 3 ^ (n + 2) := by
    simp [Fintype.card_pi]
  have hpos : (Finset.univ.filter (fun x : Fin (n + 2) → Fin 3 => ¬ ∃ i, (x i).val = 0)).card =
      2 ^ (n + 2) := by
    have hbij : (Finset.univ.filter (fun x : Fin (n + 2) → Fin 3 => ¬ ∃ i, (x i).val = 0)).card =
        (Finset.univ : Finset (Fin (n + 2) → Fin 2)).card := by
      refine Finset.card_bij (fun x _ i => ⟨(x i).val - 1, by omega⟩) ?_ ?_ ?_
      · intro x _; exact Finset.mem_univ _
      · intro x hx y hy hxy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hx hy
        funext i
        have hi := congrArg (fun f => (f i).val) hxy
        dsimp at hi
        have hx0 := hx i
        have hy0 := hy i
        exact Fin.ext (by omega)
      · intro z _
        refine ⟨fun i => ⟨(z i).val + 1, by omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
          intro i; omega
        · funext i; exact Fin.ext (by simp)
    rw [hbij]
    simp [Fintype.card_pi]
  rw [huniv, hpos] at hcomp
  have hcomm : 2 + n = n + 2 := Nat.add_comm 2 n
  rw [hcomm]
  omega

private lemma image_eq_zeroSet (n : ℕ) :
    Finset.univ.image (secondDiff n) = (zeroSet n).image (secondDiff n) := by
  apply Finset.Subset.antisymm
  · intro d hd
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
    let vals : Finset ℕ := Finset.univ.image (fun i : Fin (n + 2) => (x i).val)
    have hne : vals.Nonempty :=
      ⟨(x ⟨0, by omega⟩).val, Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩⟩
    let m := vals.min' hne
    have hm_mem : m ∈ vals := Finset.min'_mem vals hne
    obtain ⟨i₀, _, hi₀⟩ := Finset.mem_image.mp hm_mem
    have hm_le : ∀ i : Fin (n + 2), m ≤ (x i).val := fun i =>
      Finset.min'_le vals (x i).val (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    let y : Fin (n + 2) → Fin 3 := fun i => ⟨(x i).val - m, by omega⟩
    refine Finset.mem_image.mpr ⟨y, ?_, ?_⟩
    · simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i₀, by dsimp [y]; omega⟩
    · funext i
      simp only [secondDiff, y]
      have h0 := hm_le ⟨i.1, by omega⟩
      have h1 := hm_le ⟨i.1 + 1, by omega⟩
      have h2 := hm_le ⟨i.1 + 2, by omega⟩
      omega
  · exact Finset.image_subset_image (Finset.filter_subset _ _)

private lemma diff_linear (n : ℕ) (x y : Fin (n + 2) → Fin 3)
    (h : secondDiff n x = secondDiff n y) :
    ∀ k (hk : k < n + 2),
      ((y ⟨k, hk⟩ : ℤ) - (x ⟨k, hk⟩ : ℤ)) =
        ((y ⟨0, by omega⟩ : ℤ) - (x ⟨0, by omega⟩ : ℤ)) +
        (k : ℤ) * (((y ⟨1, by omega⟩ : ℤ) - (x ⟨1, by omega⟩ : ℤ)) -
          ((y ⟨0, by omega⟩ : ℤ) - (x ⟨0, by omega⟩ : ℤ))) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    rcases k with _ | _ | m
    · simp
    · simp
    · have hm0 := ih m (by omega) (by omega)
      have hm1 := ih (m + 1) (by omega) (by omega)
      have hsd := congrFun h ⟨m, by omega⟩
      simp only [secondDiff] at hsd
      push_cast at hm1 ⊢
      linarith

private lemma injOn_zeroSet (n : ℕ) (hn : 3 < n) :
    Set.InjOn (secondDiff n) (zeroSet n : Set (Fin (n + 2) → Fin 3)) := by
  intro x hx y hy hxy
  simp only [Finset.mem_coe, zeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  have hlin := diff_linear n x y hxy
  let c : ℤ := (y ⟨0, by omega⟩ : ℤ) - (x ⟨0, by omega⟩ : ℤ)
  let d : ℤ := ((y ⟨1, by omega⟩ : ℤ) - (x ⟨1, by omega⟩ : ℤ)) - c
  have hlast := hlin (n + 1) (by omega)
  have hbound : -4 ≤ ((n + 1 : ℕ) : ℤ) * d ∧ ((n + 1 : ℕ) : ℤ) * d ≤ 4 := by
    have hx0 : (x ⟨0, by omega⟩).val ≤ 2 := by omega
    have hy0 : (y ⟨0, by omega⟩).val ≤ 2 := by omega
    have hxn : (x ⟨n + 1, by omega⟩).val ≤ 2 := by omega
    have hyn : (y ⟨n + 1, by omega⟩).val ≤ 2 := by omega
    constructor <;> linarith
  have hd0 : d = 0 := by
    have hn5 : (5 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by omega
    nlinarith
  have hconst : ∀ i : Fin (n + 2), (y i : ℤ) - (x i : ℤ) = c := by
    intro i
    have hi := hlin i.1 i.2
    rw [show ((y ⟨1, by omega⟩ : ℤ) - (x ⟨1, by omega⟩ : ℤ)) -
        ((y ⟨0, by omega⟩ : ℤ) - (x ⟨0, by omega⟩ : ℤ)) = d from rfl, hd0, mul_zero, add_zero] at hi
    exact hi
  obtain ⟨i₀, hi₀⟩ := hx
  obtain ⟨j₀, hj₀⟩ := hy
  have hc_ge : 0 ≤ c := by
    have := hconst i₀
    have hxi : (x i₀ : ℤ) = 0 := by exact_mod_cast hi₀
    have hyi : (0 : ℤ) ≤ (y i₀ : ℤ) := Int.natCast_nonneg _
    linarith
  have hc_le : c ≤ 0 := by
    have := hconst j₀
    have hyj : (y j₀ : ℤ) = 0 := by exact_mod_cast hj₀
    have hxj : (0 : ℤ) ≤ (x j₀ : ℤ) := Int.natCast_nonneg _
    linarith
  have hc0 : c = 0 := le_antisymm hc_le hc_ge
  funext i
  have hi := hconst i
  rw [hc0] at hi
  exact Fin.ext (by omega)

end OMA.A228212Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a228212.main := by
  intro n hn
  unfold OMA.S_oeis_a228212.a
  rw [OMA.A228212Proof.image_eq_zeroSet,
    Finset.card_image_of_injOn (OMA.A228212Proof.injOn_zeroSet n hn),
    OMA.A228212Proof.card_zeroSet]
