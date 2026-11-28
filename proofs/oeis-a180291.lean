import OMAStatements.S_oeis_a180291

-- Problem: A180291: Number of arrangements of n indistinguishable balls in n boxes with the maximum number of balls in any box equal to n-1.
-- Upstream: formal-conjectures statements/oeis-a180291.lean:0 (declaration OMA.S_oeis_a180291.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (Ferrigno's): for n = m + 3 the map (i, j) -> the arrangement with n - 1 balls in
-- box i, one ball in box j and none elsewhere is a bijection from the ordered pairs of distinct
-- boxes onto the arrangements counted by a(n): in such an arrangement the other boxes hold one
-- ball in total, so exactly one of them holds one ball. Hence a(n) = n*n - n = n*(n-1), and
-- 2*A000217(n-1) = (n-1)*n because (n-1)*n is even.

namespace R09A180291

open OMA.S_oeis_a180291

/-- The arrangement with m + 2 balls in box p.1, one ball in box p.2 and none elsewhere. -/
def g (m : ℕ) (p : Fin (m + 3) × Fin (m + 3)) : Fin (m + 3) → ℕ :=
  fun k => if k = p.1 then m + 2 else if k = p.2 then 1 else 0

theorem g_le (m : ℕ) (p : Fin (m + 3) × Fin (m + 3)) (k : Fin (m + 3)) : g m p k ≤ m + 2 := by
  simp only [g]
  split_ifs <;> omega

theorem g_at1 (m : ℕ) (p : Fin (m + 3) × Fin (m + 3)) : g m p p.1 = m + 2 := by
  simp [g]

theorem g_at2 (m : ℕ) (p : Fin (m + 3) × Fin (m + 3)) (hp : p.1 ≠ p.2) : g m p p.2 = 1 := by
  simp [g, hp.symm]

theorem g_other (m : ℕ) (p : Fin (m + 3) × Fin (m + 3)) (k : Fin (m + 3)) (h1 : k ≠ p.1)
    (h2 : k ≠ p.2) : g m p k = 0 := by
  simp [g, h1, h2]

theorem g_sum (m : ℕ) (p : Fin (m + 3) × Fin (m + 3)) (hp : p.1 ≠ p.2) :
    ∑ k, g m p k = m + 3 := by
  have h : ∀ k, g m p k = (if k = p.1 then m + 2 else 0) + (if k = p.2 then 1 else 0) := by
    intro k
    by_cases h1 : k = p.1
    · simp [g, h1, hp]
    · simp [g, h1]
  have e1 : ∑ k, (if k = p.1 then m + 2 else 0) = m + 2 := Fintype.sum_ite_eq' p.1 (fun _ => m + 2)
  have e2 : ∑ k, (if k = p.2 then 1 else 0) = 1 := Fintype.sum_ite_eq' p.2 (fun _ => 1)
  have e0 : ∑ k, g m p k =
      ∑ k, (if k = p.1 then m + 2 else 0) + ∑ k, (if k = p.2 then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => h k)
  omega

theorem card_eq (m : ℕ) : a (m + 3) = (m + 3) * (m + 2) := by
  have hsub : m + 3 - 1 = m + 2 := by omega
  have hcard : ((Finset.univ : Finset (Fin (m + 3))).offDiag).card = (m + 3) * (m + 2) := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_eq_of_eq_add (by ring)
  unfold a
  rw [hsub, ← hcard]
  symm
  apply Finset.card_bij (fun p _ => g m p)
  · intro p hp
    have hp2 : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    exact ⟨g_sum m p hp2, fun k => g_le m p k, p.1, g_at1 m p⟩
  · intro p hp q hq hpq
    have hp2 : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    have hq2 : q.1 ≠ q.2 := (Finset.mem_offDiag.mp hq).2.2
    have hpq' : g m p = g m q := hpq
    have e1 : g m q p.1 = m + 2 := by
      rw [← hpq']
      exact g_at1 m p
    have h1 : p.1 = q.1 := by
      by_contra hne
      by_cases h2 : p.1 = q.2
      · rw [h2, g_at2 m q hq2] at e1
        omega
      · rw [g_other m q p.1 hne h2] at e1
        omega
    have e2 : g m q p.2 = 1 := by
      rw [← hpq']
      exact g_at2 m p hp2
    have h2 : p.2 = q.2 := by
      by_contra hne
      by_cases h3 : p.2 = q.1
      · exact hp2 (h1.trans h3.symm)
      · rw [g_other m q p.2 h3 hne] at e2
        omega
    exact Prod.ext h1 h2
  · intro f hf
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hf
    obtain ⟨hsum, _, i, hi⟩ := hf
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin (m + 3))) f (Finset.mem_univ i)
    have hrest : ∑ x ∈ Finset.univ.erase i, f x = 1 := by omega
    have hex : ∃ j ∈ Finset.univ.erase i, f j ≠ 0 := by
      by_contra hcon
      have hcon' : ∀ j ∈ Finset.univ.erase i, f j = 0 := by
        intro j hj
        by_contra hne
        exact hcon ⟨j, hj, hne⟩
      have h0 : ∑ x ∈ Finset.univ.erase i, f x = 0 := Finset.sum_eq_zero hcon'
      omega
    obtain ⟨j, hj, hfj⟩ := hex
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hfj1 : f j = 1 := by
      have hle1 := Finset.single_le_sum (fun x _ => Nat.zero_le (f x)) hj
      omega
    have hzero : ∀ k, k ≠ i → k ≠ j → f k = 0 := by
      intro k hki hkj
      have hk : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩
      have hsubset : ({j, k} : Finset (Fin (m + 3))) ⊆ Finset.univ.erase i := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · rw [hx]
          exact hj
        · rw [hx]
          exact hk
      have hle2 : ∑ x ∈ ({j, k} : Finset (Fin (m + 3))), f x ≤
          ∑ x ∈ Finset.univ.erase i, f x := Finset.sum_le_sum_of_subset hsubset
      rw [Finset.sum_pair (Ne.symm hkj)] at hle2
      omega
    refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_offDiag]
      exact ⟨Finset.mem_univ _, Finset.mem_univ _, hji.symm⟩
    · funext k
      show g m (i, j) k = f k
      by_cases hki : k = i
      · rw [hki, hi]
        simp [g]
      · by_cases hkj : k = j
        · rw [hkj, hfj1]
          simp [g, hji]
        · rw [hzero k hki hkj]
          simp [g, hki, hkj]

end R09A180291

open OMA.S_oeis_a180291 R09A180291 in
theorem OMA.solution : type_of% @OMA.S_oeis_a180291.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hc := card_eq m
  have hsub : m + 3 - 1 = m + 2 := by omega
  rw [hsub]
  refine ⟨?_, ?_⟩
  · rw [hc]
  · rw [hc, A000217]
    have he := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (m + 2))
    rw [he]
    ring
