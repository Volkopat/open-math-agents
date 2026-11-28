import OMAStatements.S_oeis_a365429

namespace OMA.P_oeis_a365429

/-- If every element of a finset of naturals is at most one more than the sum of the smaller
elements, then every number up to the total sum is a subset sum. -/
lemma subset_sums (S : Finset ℕ) :
    (∀ x ∈ S, x ≤ 1 + ∑ y ∈ S.filter (· < x), y) →
    ∀ m ≤ ∑ y ∈ S, y, ∃ s ⊆ S, ∑ y ∈ s, y = m := by
  induction S using Finset.induction_on_max with
  | empty =>
    intro _ m hm
    refine ⟨∅, by simp, ?_⟩
    simp at hm ⊢
    omega
  | insert a T hlt ih =>
    intro hS m hm
    have haT : a ∉ T := fun h => lt_irrefl a (hlt a h)
    have hT : ∀ x ∈ T, x ≤ 1 + ∑ y ∈ T.filter (· < x), y := by
      intro x hx
      have h1 := hS x (Finset.mem_insert_of_mem hx)
      have hna : ¬ a < x := not_lt.mpr (hlt x hx).le
      have heq : (insert a T).filter (· < x) = T.filter (· < x) := by
        rw [Finset.filter_insert, if_neg hna]
      rwa [heq] at h1
    rw [Finset.sum_insert haT] at hm
    by_cases hmT : m ≤ ∑ y ∈ T, y
    · obtain ⟨s, hs, hsum⟩ := ih hT m hmT
      exact ⟨s, hs.trans (Finset.subset_insert _ _), hsum⟩
    · have ha := hS a (Finset.mem_insert_self _ _)
      have hfil : (insert a T).filter (· < a) = T := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h | h, hy⟩
          · omega
          · exact h
        · intro h
          exact ⟨Or.inr h, hlt y h⟩
      rw [hfil] at ha
      obtain ⟨s, hs, hsum⟩ := ih hT (m - a) (by omega)
      refine ⟨insert a s, Finset.insert_subset_insert _ hs, ?_⟩
      rw [Finset.sum_insert (fun h => haT (hs h))]
      omega

/-- For `n` whose divisors increase by a factor of at most `2`, each divisor is at most one more
than the sum of the smaller divisors. -/
lemma key (n : ℕ) (hd : OMA.S_oeis_a365429.IsDense n) :
    ∀ x ∈ n.divisors, x ≤ 1 + ∑ y ∈ n.divisors.filter (· < x), y := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro hx
  by_cases hx1 : x ≤ 1
  · omega
  · have hn : n ≠ 0 := (Nat.mem_divisors.mp hx).2
    have h1mem : 1 ∈ n.divisors.filter (· < x) := by
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨one_dvd n, hn⟩, by omega⟩
    obtain ⟨d, hdD, hdmax⟩ : ∃ d ∈ n.divisors.filter (· < x),
        ∀ y ∈ n.divisors.filter (· < x), y ≤ d :=
      ⟨_, Finset.max'_mem _ ⟨1, h1mem⟩, fun y hy => Finset.le_max' _ y hy⟩
    obtain ⟨hddiv, hdx⟩ := Finset.mem_filter.mp hdD
    have hxn : x ≤ n := Nat.divisor_le hx
    obtain ⟨e, he, hde, he2⟩ := hd d hddiv (by omega)
    have hex : x ≤ e := by
      by_contra hlt
      have hmem : e ∈ n.divisors.filter (· < x) := Finset.mem_filter.mpr ⟨he, by omega⟩
      have := hdmax e hmem
      omega
    have ihd := ih d hdx hddiv
    have hsub : insert d (n.divisors.filter (· < d)) ⊆ n.divisors.filter (· < x) := by
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hdD
      · rw [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, by omega⟩
    have hsum := Finset.sum_le_sum_of_subset (f := fun y => y) hsub
    rw [Finset.sum_insert (by simp)] at hsum
    omega

end OMA.P_oeis_a365429

theorem OMA.solution : type_of% @OMA.S_oeis_a365429.main := by
  intro n _
  unfold OMA.S_oeis_a365429.a OMA.S_oeis_a365429.b
  by_cases hd : OMA.S_oeis_a365429.IsDense n
  · have hp : OMA.S_oeis_a365429.IsPractical n := by
      intro k hk
      rw [ArithmeticFunction.sigma_one_apply] at hk
      obtain ⟨s, hs, hsum⟩ := OMA.P_oeis_a365429.subset_sums n.divisors
        (OMA.P_oeis_a365429.key n hd) k hk
      exact ⟨s, Finset.mem_powerset.mpr hs, hsum⟩
    simp [hd, hp]
  · simp [hd]
