import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1

-- Step Erdos835.erdos_835.variants.johnson.R1.H1.R1.H2: hypothesis H2 of reduction Erdos835.erdos_835.variants.johnson.R1.H1.R1
-- Credit: @ishaanzee
-- Proof: every vertex of Q misses exactly one color; every color is missed by an odd number of
-- vertices (the vertices it covers are paired by its edges and |Q| = k + 1 is odd); the k + 1
-- miss counts sum to k + 1, so each color is missed by exactly one vertex.

open Finset

namespace E835Aux

/-- In a proper edge coloring of the complete graph on `Q` (`k + 1` vertices, `k` even) with
`k + 1` colors, two different vertices cannot miss the same color. Every vertex misses exactly
one color, and every color is missed by an odd number of vertices (the vertices it covers are
paired up by its edges), hence by exactly one. -/
lemma core {n : ℕ} (k : ℕ) (hk : Even k) (Q : Finset (Fin n)) (hQ : Q.card = k + 1)
    (e : Fin n → Fin n → Fin (k + 1))
    (hsym : ∀ a ∈ Q, ∀ b ∈ Q, e a b = e b a)
    (hprop : ∀ a ∈ Q, ∀ b ∈ Q, ∀ d ∈ Q, b ≠ a → d ≠ a → b ≠ d → e a b ≠ e a d)
    (a b : Fin n) (ha : a ∈ Q) (hb : b ∈ Q) (hab : a ≠ b) (i : Fin (k + 1))
    (hia : ∀ t ∈ Q, t ≠ a → i ≠ e a t) (hib : ∀ t ∈ Q, t ≠ b → i ≠ e b t) : False := by
  classical
  -- the colors used at `t`
  set used : Fin n → Finset (Fin (k + 1)) := fun t => (Q.erase t).image (e t) with hused_def
  have hused : ∀ t ∈ Q, (used t).card = k := by
    intro t ht
    rw [hused_def]
    simp only
    rw [card_image_of_injOn, card_erase_of_mem ht, hQ, Nat.add_sub_cancel]
    intro x hx y hy hxy
    by_contra hne
    simp only [coe_erase, Set.mem_sdiff, mem_coe, Set.mem_singleton_iff] at hx hy
    exact hprop t ht x hx.1 y hy.1 hx.2 hy.2 hne hxy
  -- the vertices missing color `c`
  set miss : Fin (k + 1) → Finset (Fin n) := fun c => Q.filter (fun t => c ∉ used t)
    with hmiss_def
  have hodd : ∀ c, Odd (miss c).card := by
    intro c
    set P := (Q ×ˢ Q).filter (fun p => p.1 ≠ p.2 ∧ e p.1 p.2 = c) with hP_def
    set cov := Q.filter (fun t => c ∈ used t) with hcov_def
    have hcov : cov = P.image Prod.fst := by
      ext t
      simp only [hcov_def, hP_def, hused_def, mem_filter, mem_image, mem_erase, mem_product,
        Prod.exists]
      constructor
      · rintro ⟨ht, s, ⟨hst, hs⟩, hc⟩
        exact ⟨t, s, ⟨⟨ht, hs⟩, fun h => hst h.symm, hc⟩, rfl⟩
      · rintro ⟨x, s, ⟨⟨hx, hs⟩, hxs, hc⟩, rfl⟩
        exact ⟨hx, s, ⟨fun h => hxs h.symm, hs⟩, hc⟩
    have hcard1 : cov.card = P.card := by
      rw [hcov]
      apply card_image_of_injOn
      rintro ⟨x, s⟩ hp ⟨x', s'⟩ hp' hxx
      simp only at hxx
      subst hxx
      simp only [hP_def, coe_filter, mem_product, Set.mem_ofPred_eq] at hp hp'
      obtain ⟨⟨hx, hs⟩, hxs, hc⟩ := hp
      obtain ⟨⟨-, hs'⟩, hxs', hc'⟩ := hp'
      by_contra hne
      have hne' : s ≠ s' := fun h => hne (by rw [h])
      exact hprop x hx s hs s' hs' (Ne.symm hxs) (Ne.symm hxs') hne' (hc.trans hc'.symm)
    have hsplit : P = P.filter (fun p => p.1 < p.2) ∪ P.filter (fun p => p.2 < p.1) := by
      ext p
      simp only [mem_union, mem_filter]
      constructor
      · intro hp
        have : p.1 ≠ p.2 := (mem_filter.1 hp).2.1
        rcases lt_or_gt_of_ne this with h | h
        · exact Or.inl ⟨hp, h⟩
        · exact Or.inr ⟨hp, h⟩
      · rintro (⟨hp, -⟩ | ⟨hp, -⟩) <;> exact hp
    have hdisj : Disjoint (P.filter (fun p => p.1 < p.2)) (P.filter (fun p => p.2 < p.1)) := by
      rw [disjoint_filter]
      intro p _ h1 h2
      exact lt_asymm h1 h2
    have hswap : P.filter (fun p => p.2 < p.1) = (P.filter (fun p => p.1 < p.2)).image Prod.swap := by
      ext ⟨x, y⟩
      simp only [hP_def, mem_filter, mem_image, mem_product, Prod.exists, Prod.swap_prod_mk,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨hx, hy⟩, hxy, hc⟩, hlt⟩
        exact ⟨y, x, ⟨⟨⟨hy, hx⟩, fun h => hxy h.symm, by rw [hsym y hy x hx, hc]⟩, hlt⟩, rfl, rfl⟩
      · rintro ⟨u, v, ⟨⟨⟨hu, hv⟩, huv, hc⟩, hlt⟩, rfl, rfl⟩
        exact ⟨⟨⟨hv, hu⟩, fun h => huv h.symm, by rw [hsym v hv u hu, hc]⟩, hlt⟩
    have hPc := congrArg card hsplit
    rw [card_union_of_disjoint hdisj, hswap, card_image_of_injective _ Prod.swap_injective] at hPc
    have htot := card_filter_add_card_filter_not (s := Q) (fun t => c ∈ used t)
    rw [← hcov_def, hcard1, hPc, hQ] at htot
    obtain ⟨r, hr⟩ := hk
    refine ⟨r - (P.filter (fun p => p.1 < p.2)).card, ?_⟩
    have : (miss c).card = (Q.filter (fun t => ¬ c ∈ used t)).card := rfl
    omega
  have hsum : ∑ c : Fin (k + 1), (miss c).card = k + 1 := by
    calc ∑ c : Fin (k + 1), (miss c).card
        = ∑ c : Fin (k + 1), ∑ t ∈ Q, (if c ∉ used t then 1 else 0) := by
          apply sum_congr rfl
          intro c _
          rw [hmiss_def]
          simp only
          rw [card_filter]
      _ = ∑ t ∈ Q, ∑ c : Fin (k + 1), (if c ∉ used t then 1 else 0) := sum_comm
      _ = ∑ t ∈ Q, 1 := by
          apply sum_congr rfl
          intro t ht
          rw [← card_filter]
          have h : (univ.filter fun c => c ∉ used t) = (used t)ᶜ := by ext; simp
          rw [h, card_compl, Fintype.card_fin, hused t ht]
          omega
      _ = k + 1 := by rw [sum_const, smul_eq_mul, mul_one, hQ]
  have hmem : ∀ x ∈ Q, (∀ t ∈ Q, t ≠ x → i ≠ e x t) → x ∈ miss i := by
    intro x hx hx'
    refine mem_filter.2 ⟨hx, ?_⟩
    intro hi
    obtain ⟨t, ht, hti⟩ := mem_image.1 hi
    exact hx' t (mem_of_mem_erase ht) (ne_of_mem_erase ht) hti.symm
  have htwo : 2 ≤ (miss i).card := by
    have := one_lt_card.2 ⟨a, hmem a ha hia, b, hmem b hb hib, hab⟩
    omega
  have hlow : ∑ c : Fin (k + 1), (1 + if c = i then 1 else 0) ≤ ∑ c : Fin (k + 1), (miss c).card := by
    apply sum_le_sum
    intro c _
    by_cases hc : c = i
    · rw [if_pos hc, hc]
      exact htwo
    · rw [if_neg hc]
      obtain ⟨r, hr⟩ := hodd c
      omega
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    sum_ite_eq' univ i (fun _ => 1), if_pos (mem_univ i), hsum] at hlow
  omega

end E835Aux

open E835Aux

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.H2 := by
  intro k hk Q hQ e hsym hprop a ha b hb hab i j hia hib hij
  subst hij
  exact core k hk Q hQ e hsym hprop a b ha hb hab i hia hib
