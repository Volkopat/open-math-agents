import OMAStatements.S_mse_4107563
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_4107563.main) := by
  classical
  intro h
  let A := Σ n : ℕ, Fin (n + 1)
  let F : Set (Set A) := {X | ∀ ⦃x y : A⦄, y ∈ X → x.1 < y.1 → x ∈ X}
  let P (n : ℕ) : Set A := {x | x.1 < n}
  let point (n : ℕ) (i : Fin (n + 1)) : A := ⟨n, i⟩
  have hP (n : ℕ) : P n ∈ F := fun _ _ hy hxy => Nat.lt_trans hxy hy
  have hPinj : Function.Injective P := by
    intro m n heq
    have hle (a b : ℕ) (hab : P a ⊆ P b) : a ≤ b := by
      by_contra! hlt
      have hz : point b 0 ∈ P b := hab hlt
      exact (Nat.lt_irrefl b) hz
    exact le_antisymm (hle _ _ (by rw [heq])) (hle _ _ (by rw [heq]))
  have hPfin (n : ℕ) : (P n).Finite := by
    let f : (Σ i : Fin n, Fin (i.val + 1)) → A := fun x => ⟨x.1.val, x.2⟩
    apply (Set.finite_range f).subset
    rintro ⟨i, j⟩ hi
    exact ⟨⟨⟨i, hi⟩, j⟩, rfl⟩
  have hclosed : ∀ E ⊆ F, ⋂₀ E ∈ F := by
    intro E hE x y hy hxy
    exact Set.mem_sInter.mpr fun X hX => hE hX (Set.mem_sInter.mp hy X hX) hxy
  have hcover : ¬ ∃ (n : ℕ) (C : Fin n → Set (Set A)),
      (∀ i, IsChain (· ⊆ ·) (C i)) ∧ F = ⋃ i, C i := by
    rintro ⟨n, C, hC, hUnion⟩
    let B (i : Fin (n + 1)) : Set A := P n ∪ {point n i}
    have hB (i : Fin (n + 1)) : B i ∈ F := by
      intro x y hy hxy
      left
      rcases hy with hy | hy
      · exact Nat.lt_trans hxy hy
      · have heq : y = point n i := hy
        subst y
        exact hxy
    have hsubset (i j : Fin (n + 1)) (hij : B i ⊆ B j) : i = j := by
      have hx : point n i ∈ B j := hij (Or.inr rfl)
      rcases hx with hx | hx
      · exact ((Nat.lt_irrefl n) hx).elim
      · have heq : point n i = point n j := hx
        exact Fin.ext (congrArg (fun x : A => x.2.val) heq)
    have hc (i : Fin (n + 1)) : ∃ j, B i ∈ C j := by
      have hi := hB i
      rw [hUnion] at hi
      exact Set.mem_iUnion.mp hi
    choose c hc using hc
    have hci : Function.Injective c := by
      intro i j hij
      have hmem : B j ∈ C (c i) := hij ▸ hc j
      rcases (hC (c i)).total (hc i) hmem with hs | hs
      · exact hsubset i j hs
      · exact (hsubset j i hs).symm
    have hcard := Fintype.card_le_of_injective c hci
    simp at hcard
  obtain ⟨a, ha⟩ := h A F hclosed hcover
  have hfinite : {X : Set A | X ∈ F ∧ a ∉ X}.Finite := by
    apply (hPfin (a.1 + 1)).powerset.subset
    intro X hX x hx
    show x.1 < a.1 + 1
    by_contra! hb
    exact hX.2 (hX.1 hx (by omega))
  have hinfinite : {X : Set A | X ∈ F ∧ a ∈ X}.Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => P (a.1 + k + 1))
    · intro i j hij
      have heq := hPinj hij
      omega
    · intro i
      exact ⟨hP _, by change a.1 < a.1 + i + 1; omega⟩
  exact (not_lt_of_ge ha)
    ((Cardinal.mk_lt_aleph0_iff.mpr hfinite).trans_le
      (Cardinal.aleph0_le_mk_iff.mpr (Set.infinite_coe_iff.mpr hinfinite)))