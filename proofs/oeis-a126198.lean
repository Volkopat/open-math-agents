import OMAStatements.S_oeis_a126198

-- Problem: A126198: Triangle read by rows: T(n,k) (1 <= k <= n) = number of compositions of n into parts of size <= k.
-- Upstream: formal-conjectures statements/oeis-a126198.lean:0 (declaration OMA.S_oeis_a126198.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the lists of parts of the compositions of n+1 with parts at most k are the lists
-- (i+1) :: l with i < k, i <= n and l the list of parts of a composition of n-i with parts at
-- most k, so T(n+1,k) satisfies the recurrence of the postage stamp array F, and T(0,k) = 1 =
-- F(0,k). Hence T = F, and since F(n,0) = 0 for n >= 1 the row sum of F up to the diagonal is
-- the sum of T(n,k) over 1 <= k <= n.

open OMA.S_oeis_a126198 in
theorem OMA.solution : type_of% @OMA.S_oeis_a126198.main := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ → Finset (List ℕ), ∀ m k, G m k =
      ((Finset.univ : Finset (Composition m)).filter (fun c => ∀ b ∈ c.blocks, b ≤ k)).image
        (fun c => c.blocks) := ⟨_, fun _ _ => rfl⟩
  have hT : ∀ m k, T m k = (G m k).card := by
    intro m k
    have hinj : Function.Injective (fun c : Composition m => c.blocks) :=
      fun c d h => Composition.ext h
    unfold T
    rw [hG, Finset.card_image_of_injective _ hinj]
  have memG : ∀ m k (l : List ℕ), l ∈ G m k ↔ (∀ x ∈ l, 0 < x ∧ x ≤ k) ∧ l.sum = m := by
    intro m k l
    rw [hG, Finset.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [Finset.mem_filter] at hc
      exact ⟨fun x hx => ⟨c.blocks_pos hx, hc.2 x hx⟩, c.blocks_sum⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨l, fun hx => (h1 _ hx).1, h2⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun x hx => (h1 x hx).2⟩
  have hG0 : ∀ k, G 0 k = {[]} := by
    intro k
    ext l
    rw [memG, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      rcases l with _ | ⟨x, l'⟩
      · rfl
      · have hx := h1 x (List.mem_cons.mpr (Or.inl rfl))
        rw [List.sum_cons] at h2
        exfalso
        omega
    · rintro rfl
      exact ⟨fun x hx => by simp at hx, rfl⟩
  have hrec : ∀ n k, G (n + 1) k = ((Finset.range k).filter (fun i => i ≤ n)).biUnion
      (fun i => (G (n - i) k).image (List.cons (i + 1))) := by
    intro n k
    ext l
    rw [memG, Finset.mem_biUnion]
    constructor
    · rintro ⟨h1, h2⟩
      rcases l with _ | ⟨x, l'⟩
      · exfalso
        rw [List.sum_nil] at h2
        omega
      · have hx := h1 x (List.mem_cons.mpr (Or.inl rfl))
        rw [List.sum_cons] at h2
        refine ⟨x - 1, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_range]
          omega
        · rw [Finset.mem_image]
          refine ⟨l', ?_, ?_⟩
          · rw [memG]
            exact ⟨fun y hy => h1 y (List.mem_cons.mpr (Or.inr hy)), by omega⟩
          · rw [show x - 1 + 1 = x by omega]
    · rintro ⟨i, hi, hl⟩
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Finset.mem_image] at hl
      obtain ⟨l', hl', rfl⟩ := hl
      rw [memG] at hl'
      refine ⟨?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ⟨by omega, by omega⟩
        · exact hl'.1 y hy'
      · rw [List.sum_cons, hl'.2]
        omega
  have hcard : ∀ n k, T (n + 1) k = ∑ i ∈ Finset.range k, if i ≤ n then T (n - i) k else 0 := by
    intro n k
    rw [hT, hrec, Finset.card_biUnion, ← Finset.sum_filter]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Finset.card_image_of_injective _ List.cons_injective, hT]
    · intro i _ j _ hij
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro l hl1 hl2
      rw [Finset.mem_image] at hl1
      rw [Finset.mem_image] at hl2
      obtain ⟨a, _, rfl⟩ := hl1
      obtain ⟨b, _, hb⟩ := hl2
      have hji := (List.cons.inj hb).1
      omega
  have hTF : ∀ n k, T n k = F n k := by
    intro n k
    refine Nat.strong_induction_on n ?_
    intro n ih
    rcases n with _ | n
    · rw [hT, hG0, Finset.card_singleton, F.eq_1]
    · rw [hcard n k, F.eq_2]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i ≤ n
      · rw [if_pos h, if_pos h]
        exact ih (n - i) (by omega)
      · rw [if_neg h, if_neg h]
  have bridge : ∀ (N : ℕ) (f : ℕ → ℕ),
      ∑ k ∈ Finset.range (N + 1), f k = f 0 + ∑ k ∈ Finset.Icc 1 N, f k := by
    intro N f
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      ring
  intro n hn
  have hF0 : F n 0 = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [F.eq_2]
    simp
  unfold a039671
  rw [bridge n (F n), hF0, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  exact hTF n k
