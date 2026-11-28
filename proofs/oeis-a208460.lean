import OMAStatements.S_oeis_a208460

theorem OMA.solution : type_of% @OMA.S_oeis_a208460.main := by
  intro n k hn hk1 hk2
  have hsort : (Nat.divisors n).sort = (Nat.properDivisors n).sort ++ [n] := by
    apply List.Perm.eq_of_pairwise' (r := fun a b : ℕ => a ≤ b)
    · exact Finset.pairwise_sort _ _
    · rw [List.pairwise_append]
      refine ⟨Finset.pairwise_sort _ _, by simp, ?_⟩
      intro a ha b hb
      rw [Finset.mem_sort, Nat.mem_properDivisors] at ha
      simp only [List.mem_singleton] at hb
      omega
    · rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)]
      · intro x
        simp only [List.mem_append, Finset.mem_sort, List.mem_singleton,
          Nat.mem_divisors, Nat.mem_properDivisors]
        constructor
        · rintro ⟨hx, -⟩
          by_cases hxn : x = n
          · exact Or.inr hxn
          · exact Or.inl ⟨hx, lt_of_le_of_ne (Nat.le_of_dvd (by omega) hx) hxn⟩
        · rintro (⟨hx, -⟩ | rfl)
          · exact ⟨hx, by omega⟩
          · exact ⟨dvd_refl _, by omega⟩
      · rw [List.nodup_append]
        refine ⟨Finset.sort_nodup _ _, by simp, ?_⟩
        intro a ha b hb
        rw [Finset.mem_sort, Nat.mem_properDivisors] at ha
        simp only [List.mem_singleton] at hb
        omega
  have hlen : k - 1 < ((Nat.properDivisors n).sort).length := by
    rw [Finset.length_sort]; omega
  have heq : OMA.S_oeis_a208460.kthDivisor n k = OMA.S_oeis_a208460.kthProperDivisor n k := by
    unfold OMA.S_oeis_a208460.kthDivisor OMA.S_oeis_a208460.kthProperDivisor
    rw [hsort, List.getD_append _ _ _ _ hlen]
  have hmem : OMA.S_oeis_a208460.kthProperDivisor n k ∈ Nat.properDivisors n := by
    unfold OMA.S_oeis_a208460.kthProperDivisor
    rw [List.getD_eq_getElem _ _ hlen, ← Finset.mem_sort (r := fun a b : ℕ => a ≤ b)]
    exact List.getElem_mem hlen
  rw [Nat.mem_properDivisors] at hmem
  rw [heq]
  exact Nat.dvd_sub hmem.1 (dvd_refl _)
