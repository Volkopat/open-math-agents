import FormalConjectures.ErdosProblems.«127»

open SimpleGraph

private lemma ncard_sum {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr edgeSetSumEquiv, Nat.card_sum]

private lemma split_sum {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {G' : SimpleGraph W}
    {H : SimpleGraph (V ⊕ W)} (hH : H ≤ G ⊕g G') :
    H.edgeSet.ncard ≤ (H.comap Sum.inl).edgeSet.ncard + (H.comap Sum.inr).edgeSet.ncard ∧
      H.comap Sum.inr ≤ G' :=
  ⟨by rw [← ncard_sum]; exact Set.ncard_le_ncard (edgeSet_mono fun x y hxy => by
        have := hH hxy; rcases x with x | x <;> rcases y with y | y <;> simp_all [sum_adj, comap_adj]),
   fun _ _ h => by simpa [sum_adj] using hH h⟩

theorem OMA.solution : type_of% @Erdos127.erdos_127.variants.alon_upper := by
  classical
  refine ⟨2, fun m => ?_⟩
  have htop (n : ℕ) : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
  have hcb (r : ℕ) : (completeBipartiteGraph (Fin 1) (Fin r)).edgeSet.ncard = r := by
    rw [Set.ncard, encard_edgeSet_completeBipartiteGraph]; simp
  have hbip (k : ℕ) (H : SimpleGraph (Fin k)) (hH : H.IsBipartite) :
      4 * (H.edgeSet.ncard : ℝ) ≤ (k : ℝ) ^ 2 := by
    have h := hH.four_mul_encard_edgeSet_le
    rw [← (Set.toFinite _).cast_ncard_eq] at h
    simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h
    exact_mod_cast (show 4 * H.edgeSet.ncard ≤ k ^ 2 by exact_mod_cast h)
  have hdec : ∀ r : ℕ, ∃ s, s.choose 2 ≤ r ∧ r < s.choose 2 + s := fun r => by
    induction r with
    | zero => exact ⟨1, by simp, by simp⟩
    | succ r ih =>
      obtain ⟨s, h1, h2⟩ := ih
      by_cases h : r + 1 < s.choose 2 + s
      · exact ⟨s, by omega, h⟩
      · have : (s + 1).choose 2 = s.choose 2 + s := by
          rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring
        exact ⟨s + 1, by omega, by omega⟩
  obtain ⟨n, hn1, hn2⟩ := hdec m
  obtain ⟨s, hs1, hs2⟩ := hdec (m - n.choose 2)
  set r' := m - n.choose 2 - s.choose 2
  have hfm : Erdos127.f m ≤ s - 1 := csSup_le' fun k hk => by
    let G : SimpleGraph (Fin n ⊕ (Fin s ⊕ (Fin 1 ⊕ Fin r'))) :=
      ⊤ ⊕g (⊤ ⊕g completeBipartiteGraph (Fin 1) (Fin r'))
    obtain ⟨H, hHG, hHb, hHk⟩ := hk _ G (by simp only [G, ncard_sum, htop, hcb]; omega)
    obtain ⟨hc1, hH2G⟩ := split_sum hHG
    obtain ⟨hc2, hH22G⟩ := split_sum hH2G
    have hc3 : ((H.comap Sum.inr).comap Sum.inr).edgeSet.ncard ≤ r' :=
      (Set.ncard_le_ncard (edgeSet_mono hH22G)).trans (hcb r').le
    have hb1 := hbip n (H.comap Sum.inl) (Colorable.of_hom (Hom.comap _ _) hHb)
    have hb2 := hbip s ((H.comap Sum.inr).comap Sum.inl)
      (Colorable.of_hom (Hom.comap _ _) (Colorable.of_hom (Hom.comap _ _) hHb))
    have hmR : (m : ℝ) = n * (n - 1) / 2 + s * (s - 1) / 2 + r' := by
      have : m = n.choose 2 + s.choose 2 + r' := by omega
      rw [this]; push_cast [Nat.cast_choose_two]; ring
    have hsq : 2 * (n : ℝ) - 1 ≤ √(8 * m + 1) :=
      (le_abs_self _).trans <| (Real.sqrt_sq_eq_abs _).symm.le.trans <| Real.sqrt_le_sqrt <| by
        have : (n.choose 2 : ℝ) ≤ m := by exact_mod_cast hn1
        rw [Nat.cast_choose_two] at this; nlinarith
    have hr's : (r' : ℝ) + 1 ≤ s := by exact_mod_cast (show r' + 1 ≤ s by omega)
    have hc1R : (H.edgeSet.ncard : ℝ) ≤
        (H.comap Sum.inl).edgeSet.ncard + (H.comap Sum.inr).edgeSet.ncard := by exact_mod_cast hc1
    have hc2R : ((H.comap Sum.inr).edgeSet.ncard : ℝ) ≤
        ((H.comap Sum.inr).comap Sum.inl).edgeSet.ncard +
          ((H.comap Sum.inr).comap Sum.inr).edgeSet.ncard := by exact_mod_cast hc2
    have hc3R : (((H.comap Sum.inr).comap Sum.inr).edgeSet.ncard : ℝ) ≤ r' := by exact_mod_cast hc3
    have : k < s := by exact_mod_cast (show (k : ℝ) < s by nlinarith)
    omega
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have h4 : (t : ℝ) ^ 4 ≤ 8 * m := by
    have h1 : ((t + 1).choose 2 : ℝ) ≤ (m - n.choose 2 : ℕ) := by exact_mod_cast hs1
    have h2R : ((m - n.choose 2 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast (show m - n.choose 2 + 1 ≤ n by omega)
    have h3 : (n.choose 2 : ℝ) ≤ m := by exact_mod_cast hn1
    rw [Nat.cast_choose_two] at h1 h3; push_cast at h1
    have ht : (t : ℝ) ^ 2 ≤ 2 * ((n : ℝ) - 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) t]
    have hn : ((n : ℝ) - 1) ^ 2 ≤ 2 * m := by nlinarith
    nlinarith [sq_nonneg (t : ℝ)]
  refine (show (Erdos127.f m : ℝ) ≤ t by exact_mod_cast hfm).trans ?_
  by_contra hlt; push Not at hlt
  have h44 : ((m : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = m := by
    rw [one_div]; exact_mod_cast Real.rpow_inv_natCast_pow (Nat.cast_nonneg m) (by norm_num)
  have : (2 * (m : ℝ) ^ (1 / 4 : ℝ)) ^ 4 < (t : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
  rw [mul_pow, h44] at this; nlinarith
