import OMAStatements.S_oeis_a188865

-- Problem: A188865: Number of n x 8 binary arrays without the pattern 0 1 diagonally, vertically, or antidiagonally.
-- Credit: @ceejcake
-- Proof: Light-cone expansion forces any 0 in row 0 to propagate to all 8 columns by row 7.
-- Splitting valid (n+1) x 8 arrays by whether row 0 is all 1s gives a(n+1) = a(n) + T(n+1),
-- and for m >= 7, row m in T(m+1) is forced all 0s, giving T(m+1) = T(m).

namespace ProofA188865

open OMA.S_oeis_a188865
open scoped Classical
noncomputable section

private def validSet (n : ℕ) : Finset (Fin n → Fin 8 → Fin 2) :=
  Finset.univ.filter (isValid n)

private def hasZeroRow0 (n : ℕ) : Finset (Fin (n + 1) → Fin 8 → Fin 2) :=
  (validSet (n + 1)).filter (fun A => ∃ j : Fin 8, A 0 j = 0)

-- Light-cone lemma: if A i j = 0, then A (i + d) j' = 0 whenever |j' - j| ≤ d
private lemma light_cone {n : ℕ} {A : Fin n → Fin 8 → Fin 2} (hA : isValid n A) :
    ∀ (d : ℕ) (i : Fin n) (hd : i.1 + d < n) (j j' : Fin 8),
      j'.1 ≤ j.1 + d → j.1 ≤ j'.1 + d → A i j = 0 → A ⟨i.1 + d, hd⟩ j' = 0 := by
  intro d
  induction d with
  | zero =>
    intro i hd j j' h1 h2 h0
    have hjj : j = j' := Fin.ext (by omega)
    have hii : (⟨i.1 + 0, hd⟩ : Fin n) = i := Fin.ext (by simp)
    rw [hii, ← hjj]; exact h0
  | succ d ih =>
    intro i hd j j' h1 h2 h0
    -- Step from j toward j' by at most 1 at the last step: pick intermediate column jmid
    let jmid : Fin 8 :=
      if hlt : j'.1 < j.1 then ⟨j'.1 + 1, by omega⟩
      else if hgt : j.1 < j'.1 then ⟨j'.1 - 1, by omega⟩
      else j'
    have hmid1 : jmid.1 ≤ j.1 + d := by dsimp only [jmid]; split_ifs <;> (try dsimp only) <;> omega
    have hmid2 : j.1 ≤ jmid.1 + d := by dsimp only [jmid]; split_ifs <;> (try dsimp only) <;> omega
    have hprev : A ⟨i.1 + d, by omega⟩ jmid = 0 := ih i (by omega) j jmid hmid1 hmid2 h0
    have hstep1 : j'.1 ≤ jmid.1 + 1 := by dsimp only [jmid]; split_ifs <;> (try dsimp only) <;> omega
    have hstep2 : jmid.1 ≤ j'.1 + 1 := by dsimp only [jmid]; split_ifs <;> (try dsimp only) <;> omega
    have hres := hA ⟨i.1 + d, by omega⟩ (by dsimp only; omega) jmid j' hstep1 hstep2 hprev
    have heq : (⟨(⟨i.1 + d, by omega⟩ : Fin n).1 + 1, by dsimp only; omega⟩ : Fin n) = ⟨i.1 + (d + 1), hd⟩ :=
      Fin.ext (by dsimp only; omega)
    rwa [heq] at hres

-- Splitting validSet (n + 1) by whether row 0 is all 1s gives |validSet (n+1)| = |validSet n| + |hasZeroRow0 n|
private lemma card_validSet_succ (n : ℕ) :
    (validSet (n + 1)).card = (validSet n).card + (hasZeroRow0 n).card := by
  let allOneRow0 := (validSet (n + 1)).filter (fun A => ¬ ∃ j : Fin 8, A 0 j = 0)
  have hsplit : validSet (n + 1) = allOneRow0 ∪ hasZeroRow0 n := by
    ext A; simp only [allOneRow0, hasZeroRow0, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      by_cases hx : ∃ j : Fin 8, A 0 j = 0
      · exact Or.inr ⟨h, hx⟩
      · exact Or.inl ⟨h, hx⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint allOneRow0 (hasZeroRow0 n) := by
    rw [Finset.disjoint_left]; intro A h1 h2
    simp only [allOneRow0, hasZeroRow0, Finset.mem_filter] at h1 h2
    exact h1.2 h2.2
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  congr 1
  -- Bijection allOneRow0 ↔ validSet n by dropping / prepending an all-1 row 0
  refine Finset.card_bij (fun A _ i j => A i.succ j) ?_ ?_ ?_
  · intro A hA
    simp only [allOneRow0, validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    intro i hi j j' h1 h2 h0
    have := hA.1 i.succ (by simp only [Fin.val_succ]; omega) j j' h1 h2 h0
    have heq : (⟨i.succ.1 + 1, by simp only [Fin.val_succ]; omega⟩ : Fin (n + 1)) = (⟨i.1 + 1, hi⟩ : Fin n).succ :=
      Fin.ext (by simp)
    rwa [heq] at this
  · intro A1 hA1 A2 hA2 h
    simp only [allOneRow0, Finset.mem_filter] at hA1 hA2
    funext i j
    refine Fin.cases ?_ (fun k => congr_fun (congr_fun h k) j) i
    have h1 : A1 0 j = 1 := by
      have hne : (A1 0 j).1 ≠ 0 := fun hz => hA1.2 ⟨j, Fin.ext hz⟩
      have := (A1 0 j).2; exact Fin.ext (by omega)
    have h2 : A2 0 j = 1 := by
      have hne : (A2 0 j).1 ≠ 0 := fun hz => hA2.2 ⟨j, Fin.ext hz⟩
      have := (A2 0 j).2; exact Fin.ext (by omega)
    rw [h1, h2]
  · intro B hB
    simp only [validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hB
    let A : Fin (n + 1) → Fin 8 → Fin 2 := Fin.cons (fun _ => 1) B
    refine ⟨A, ?_, ?_⟩
    · simp only [allOneRow0, validSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun i hi j j' h1 h2 h0 => ?_, ?_⟩
      · cases i using Fin.cases with
        | zero => simp [A] at h0
        | succ k =>
          simp only [A, Fin.cons_succ] at h0
          have hk : k.1 + 1 < n := by simp only [Fin.val_succ] at hi; omega
          have heq : (⟨k.succ.1 + 1, hi⟩ : Fin (n + 1)) = (⟨k.1 + 1, hk⟩ : Fin n).succ :=
            Fin.ext (by simp)
          rw [heq]; simp only [A, Fin.cons_succ]
          exact hB k hk j j' h1 h2 h0
      · rintro ⟨j, hj⟩; simp [A] at hj
    · funext i j; simp [A]

-- For m ≥ 6 (so m + 1 ≥ 7), hasZeroRow0 (m + 1) bijects with hasZeroRow0 m by dropping the last row (which is forced all 0s)
private lemma card_hasZeroRow0_succ (m : ℕ) (hm : 6 ≤ m) :
    (hasZeroRow0 (m + 1)).card = (hasZeroRow0 m).card := by
  refine Finset.card_bij (fun A _ i j => A i.castSucc j) ?_ ?_ ?_
  · intro A hA
    simp only [hasZeroRow0, validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    refine ⟨fun i hi j j' h1 h2 h0 => ?_, ?_⟩
    · have := hA.1 i.castSucc (by simp only [Fin.val_castSucc]; omega) j j' h1 h2 h0
      have heq : (⟨i.castSucc.1 + 1, by simp only [Fin.val_castSucc]; omega⟩ : Fin (m + 2)) =
          (⟨i.1 + 1, hi⟩ : Fin (m + 1)).castSucc := Fin.ext (by simp)
      rwa [heq] at this
    · rcases hA.2 with ⟨j, hj⟩
      exact ⟨j, hj⟩
  · intro A1 hA1 A2 hA2 h
    simp only [hasZeroRow0, validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA1 hA2
    funext i j
    by_cases hi : i.1 < m + 1
    · exact congr_fun (congr_fun h ⟨i.1, hi⟩) j
    · have hlast : i = ⟨(0 : Fin (m + 2)).1 + (m + 1), by simp only [Fin.val_zero]; omega⟩ :=
        Fin.ext (by simp only [Fin.val_zero]; omega)
      rcases hA1.2 with ⟨j1, hj1⟩
      rcases hA2.2 with ⟨j2, hj2⟩
      have hz1 : A1 i j = 0 := by
        rw [hlast]
        exact light_cone hA1.1 (m + 1) 0 (by simp only [Fin.val_zero]; omega) j1 j (by omega) (by omega) hj1
      have hz2 : A2 i j = 0 := by
        rw [hlast]
        exact light_cone hA2.1 (m + 1) 0 (by simp only [Fin.val_zero]; omega) j2 j (by omega) (by omega) hj2
      rw [hz1, hz2]
  · intro B hB
    simp only [hasZeroRow0, validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hB
    let A : Fin (m + 2) → Fin 8 → Fin 2 := fun i j => if h : i.1 < m + 1 then B ⟨i.1, h⟩ j else 0
    refine ⟨A, ?_, ?_⟩
    · simp only [hasZeroRow0, validSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun i hi j j' h1 h2 h0 => ?_, ?_⟩
      · dsimp only [A]
        by_cases hlt : i.1 + 1 < m + 1
        · rw [dif_pos hlt]
          dsimp only [A] at h0
          rw [dif_pos (by omega)] at h0
          exact hB.1 ⟨i.1, by omega⟩ hlt j j' h1 h2 h0
        · rw [dif_neg hlt]
      · rcases hB.2 with ⟨j, hj⟩
        exact ⟨j, by dsimp only [A]; rw [dif_pos (by simp only [Fin.val_zero]; omega)]; exact hj⟩
    · funext i j; dsimp only [A]; simp only [Fin.val_castSucc, i.2, ↓reduceDIte]

theorem main :
    ∀ n : ℕ, 7 < n → a n + a (n - 2) = 2 * a (n - 1) := by
  intro n hn
  have ha : ∀ k : ℕ, a k = (validSet k).card := by
    intro k; unfold a validSet
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [ha n, ha (n - 2), ha (n - 1)]
  let k := n - 2
  have e0 : n - 2 = k := rfl
  have e1 : n - 1 = k + 1 := by omega
  have e2 : n = k + 2 := by omega
  rw [e0, e1, e2]
  have s1 : (validSet (k + 2)).card = (validSet (k + 1)).card + (hasZeroRow0 (k + 1)).card :=
    card_validSet_succ (k + 1)
  have s2 := card_validSet_succ k
  have hT := card_hasZeroRow0_succ k (by omega)
  omega

end
end ProofA188865

theorem OMA.solution : type_of% @OMA.S_oeis_a188865.main :=
  ProofA188865.main
