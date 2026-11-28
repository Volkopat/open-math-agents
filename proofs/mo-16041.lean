import OMAStatements.S_mo_16041
import Mathlib

-- Problem: mo-16041, a multiset of n integers from {1..m} and a multiset of m integers from
-- {1..n} always have nonempty sub-multisets with equal sums.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Order both multisets and let X_k, Y_l be the partial sums; say Y_m <= X_n (otherwise swap
-- the roles). For 1 <= l <= m let f(l) be the least index with X_{f(l)} >= Y_l. Then
-- 0 <= X_{f(l)} - Y_l < m. If some difference is 0 we are done; otherwise the m differences
-- lie in {1, ..., m-1}, so two of them agree, and subtracting gives two blocks of consecutive
-- terms with equal sums.

namespace MO16041

theorem aux (n m : ℕ) (a b : ℕ → ℕ)
    (ha : ∀ i < n, 1 ≤ a i ∧ a i ≤ m) (hb : ∀ j < m, 1 ≤ b j ∧ b j ≤ n)
    (hle : ∑ j ∈ Finset.range m, b j ≤ ∑ i ∈ Finset.range n, a i) :
    ∃ k k' l l', k < k' ∧ k' ≤ n ∧ l < l' ∧ l' ≤ m ∧
      ∑ i ∈ Finset.Ico k k', a i = ∑ j ∈ Finset.Ico l l', b j ∨ m = 0 := by
  by_cases hm0 : m = 0
  · exact ⟨0, 0, 0, 0, Or.inr hm0⟩
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℕ, ∀ k, X k = ∑ i ∈ Finset.range k, a i := ⟨_, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℕ, ∀ l, Y l = ∑ j ∈ Finset.range l, b j := ⟨_, fun _ => rfl⟩
  have hX0 : X 0 = 0 := by
    rw [hX]
    simp
  have hY0 : Y 0 = 0 := by
    rw [hY]
    simp
  have hXs : ∀ k, X (k + 1) = X k + a k := by
    intro k
    rw [hX, hX, Finset.sum_range_succ]
  have hYs : ∀ l, Y (l + 1) = Y l + b l := by
    intro l
    rw [hY, hY, Finset.sum_range_succ]
  have hXmono : ∀ k k', k ≤ k' → X k ≤ X k' := by
    intro k k' h
    rw [hX, hX]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono h)
  have hYmono : ∀ l l', l ≤ l' → Y l ≤ Y l' := by
    intro l l' h
    rw [hY, hY]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono h)
  have hYstrict : ∀ l l', l < l' → l' ≤ m → Y l < Y l' := by
    intro l l' hll hl'
    have h1 := hYmono (l + 1) l' hll
    have h2 := hYs l
    have h3 := (hb l (by omega)).1
    omega
  have hXI : ∀ k k', k ≤ k' → X k + ∑ i ∈ Finset.Ico k k', a i = X k' := by
    intro k k' h
    rw [hX, hX]
    exact Finset.sum_range_add_sum_Ico a h
  have hYI : ∀ l l', l ≤ l' → Y l + ∑ j ∈ Finset.Ico l l', b j = Y l' := by
    intro l l' h
    rw [hY, hY]
    exact Finset.sum_range_add_sum_Ico b h
  have hle' : Y m ≤ X n := by
    rw [hX, hY]
    exact hle
  have hmin : ∀ l, ∃ i, l ≤ m → (i ≤ n ∧ Y l ≤ X i ∧ ∀ i' < i, X i' < Y l) := by
    intro l
    by_cases hl : l ≤ m
    · have hex : ∃ i, Y l ≤ X i := ⟨n, (hYmono l m hl).trans hle'⟩
      exact ⟨Nat.find hex, fun _ => ⟨Nat.find_min' hex ((hYmono l m hl).trans hle'),
        Nat.find_spec hex, fun i' hi' => not_le.mp (Nat.find_min hex hi')⟩⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose f hf using hmin
  have hfpos : ∀ l, 1 ≤ l → l ≤ m → 1 ≤ f l := by
    intro l h1 hlm
    by_contra hcon
    have hf0 : f l = 0 := by omega
    have h2 := (hf l hlm).2.1
    rw [hf0, hX0] at h2
    have h3 := hYstrict 0 l (by omega) hlm
    omega
  have hd : ∀ l, 1 ≤ l → l ≤ m → X (f l) < Y l + m := by
    intro l h1 hlm
    have hp := hfpos l h1 hlm
    obtain ⟨hfn, -, hmin'⟩ := hf l hlm
    have h2 := hmin' (f l - 1) (by omega)
    have h3 := hXs (f l - 1)
    have h4 : f l - 1 + 1 = f l := by omega
    rw [h4] at h3
    have h5 := (ha (f l - 1) (by omega)).2
    omega
  have key : ∀ l1 l2, 1 ≤ l1 → l1 < l2 → l2 ≤ m → X (f l1) - Y l1 = X (f l2) - Y l2 →
      ∃ k k' l l', k < k' ∧ k' ≤ n ∧ l < l' ∧ l' ≤ m ∧
        ∑ i ∈ Finset.Ico k k', a i = ∑ j ∈ Finset.Ico l l', b j ∨ m = 0 := by
    intro l1 l2 h1 h12 h2m heq
    have g1 := (hf l1 (by omega)).2.1
    have g2 := (hf l2 h2m).2.1
    have hY12 := hYstrict l1 l2 h12 h2m
    have hXlt : X (f l1) < X (f l2) := by omega
    have hflt : f l1 < f l2 := by
      by_contra hcon
      have h3 := hXmono (f l2) (f l1) (by omega)
      omega
    have e1 := hXI (f l1) (f l2) hflt.le
    have e2 := hYI l1 l2 h12.le
    exact ⟨f l1, f l2, l1, l2, Or.inl ⟨hflt, (hf l2 h2m).1, h12, h2m, by omega⟩⟩
  by_cases h0 : ∃ l, 1 ≤ l ∧ l ≤ m ∧ X (f l) = Y l
  · obtain ⟨l, h1, hlm, heq⟩ := h0
    have e1 := hXI 0 (f l) (Nat.zero_le _)
    have e2 := hYI 0 l (Nat.zero_le _)
    exact ⟨0, f l, 0, l, Or.inl ⟨hfpos l h1 hlm, (hf l hlm).1, h1, hlm, by omega⟩⟩
  · have hne : ∀ l, 1 ≤ l → l ≤ m → X (f l) ≠ Y l := by
      intro l h1 hlm heq
      exact h0 ⟨l, h1, hlm, heq⟩
    have hmaps : Set.MapsTo (fun l => X (f l) - Y l) (Finset.Icc 1 m : Set ℕ)
        (Finset.Icc 1 (m - 1) : Set ℕ) := by
      intro l hl
      have hl' := Finset.mem_Icc.mp (Finset.mem_coe.mp hl)
      have g := (hf l hl'.2).2.1
      have g' := hd l hl'.1 hl'.2
      have g'' := hne l hl'.1 hl'.2
      show X (f l) - Y l ∈ Finset.Icc 1 (m - 1)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hcard : (Finset.Icc 1 (m - 1)).card < (Finset.Icc 1 m).card := by
      simp only [Nat.card_Icc]
      omega
    obtain ⟨l1, hl1, l2, hl2, hne12, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
    have hl1' := Finset.mem_Icc.mp hl1
    have hl2' := Finset.mem_Icc.mp hl2
    have heq' : X (f l1) - Y l1 = X (f l2) - Y l2 := heq
    rcases lt_or_gt_of_ne hne12 with hlt | hgt
    · exact key l1 l2 hl1'.1 hlt hl2'.2 heq'
    · exact key l2 l1 hl2'.1 hgt hl1'.2 heq'.symm

end MO16041

theorem OMA.solution : type_of% @OMA.S_mo_16041.main := by
  intro n m hn hm A B hAc hBc hA hB
  obtain ⟨la, rfl⟩ : ∃ la : List ℕ, (la : Multiset ℕ) = A := ⟨A.toList, Multiset.coe_toList A⟩
  obtain ⟨lb, rfl⟩ : ∃ lb : List ℕ, (lb : Multiset ℕ) = B := ⟨B.toList, Multiset.coe_toList B⟩
  rw [Multiset.coe_card] at hAc hBc
  have hget : ∀ (L : List ℕ) (i : ℕ) (hi : i < L.length), L.getD i 0 = L[i] := by
    intro L i hi
    simp [hi]
  have haB : ∀ i < n, 1 ≤ la.getD i 0 ∧ la.getD i 0 ≤ m := by
    intro i hi
    have hi' : i < la.length := by omega
    rw [hget la i hi']
    exact hA _ (Multiset.mem_coe.mpr (List.getElem_mem hi'))
  have hbB : ∀ j < m, 1 ≤ lb.getD j 0 ∧ lb.getD j 0 ≤ n := by
    intro j hj
    have hj' : j < lb.length := by omega
    rw [hget lb j hj']
    exact hB _ (Multiset.mem_coe.mpr (List.getElem_mem hj'))
  have hpre : ∀ (L : List ℕ) (k : ℕ), k ≤ L.length →
      ∑ i ∈ Finset.range k, L.getD i 0 = (L.take k).sum := by
    intro L k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hk' : k < L.length := by omega
      rw [Finset.sum_range_succ, ih (by omega), List.sum_take_succ L k hk', hget L k hk']
  have hblock : ∀ (L : List ℕ) (k k' : ℕ), k ≤ k' → k' ≤ L.length →
      (((L.take k').drop k : List ℕ) : Multiset ℕ).sum = ∑ i ∈ Finset.Ico k k', L.getD i 0 := by
    intro L k k' hkk hk'
    rw [Multiset.sum_coe]
    have e1 := List.sum_take_add_sum_drop (L.take k') k
    rw [List.take_take, min_eq_left hkk] at e1
    have e2 : ∑ i ∈ Finset.range k, L.getD i 0 + ∑ i ∈ Finset.Ico k k', L.getD i 0 =
        ∑ i ∈ Finset.range k', L.getD i 0 :=
      Finset.sum_range_add_sum_Ico (fun i => L.getD i 0) hkk
    rw [hpre L k (by omega), hpre L k' hk'] at e2
    omega
  have hsub : ∀ (L : List ℕ) (k k' : ℕ),
      (((L.take k').drop k : List ℕ) : Multiset ℕ) ≤ (L : Multiset ℕ) := by
    intro L k k'
    exact Multiset.coe_le.mpr ((List.drop_sublist k _).trans (List.take_sublist k' L)).subperm
  have concl : ∃ k k' l l', k < k' ∧ k' ≤ n ∧ l < l' ∧ l' ≤ m ∧
      ∑ i ∈ Finset.Ico k k', la.getD i 0 = ∑ j ∈ Finset.Ico l l', lb.getD j 0 := by
    rcases le_total (∑ j ∈ Finset.range m, lb.getD j 0) (∑ i ∈ Finset.range n, la.getD i 0)
      with h | h
    · obtain ⟨k, k', l, l', hres⟩ := MO16041.aux n m _ _ haB hbB h
      rcases hres with hres | hres
      · exact ⟨k, k', l, l', hres⟩
      · omega
    · obtain ⟨l, l', k, k', hres⟩ := MO16041.aux m n _ _ hbB haB h
      rcases hres with ⟨h1, h2, h3, h4, h5⟩ | hres
      · exact ⟨k, k', l, l', h3, h4, h1, h2, h5.symm⟩
      · omega
  obtain ⟨k, k', l, l', hkk, hk'n, hll, hl'm, hsum⟩ := concl
  have hsA := hblock la k k' hkk.le (by omega)
  have hsB := hblock lb l l' hll.le (by omega)
  have hposA : 1 ≤ ∑ i ∈ Finset.Ico k k', la.getD i 0 :=
    le_trans (haB k (by omega)).1
      (Finset.single_le_sum (f := fun i => la.getD i 0) (fun _ _ => Nat.zero_le _)
        (Finset.left_mem_Ico.mpr hkk))
  refine ⟨((la.take k').drop k : List ℕ), hsub la k k', ((lb.take l').drop l : List ℕ),
    hsub lb l l', ?_, ?_, ?_⟩
  · intro h0
    rw [h0, Multiset.sum_zero] at hsA
    omega
  · intro h0
    rw [h0, Multiset.sum_zero] at hsB
    omega
  · rw [hsA, hsB]
    exact hsum
