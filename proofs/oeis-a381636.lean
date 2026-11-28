import OMAStatements.S_oeis_a381636

namespace OMA.P381636
open OMA.S_oeis_a381636

def HasPerm (M : Multiset ℕ) : Prop := ∃ l : List ℕ, (l : Multiset ℕ) = M ∧ (runSums l).Nodup

/-- multiset of a block list: block (v, len) contributes len copies of v -/
def flat (B : List (ℕ × ℕ)) : Multiset ℕ := (B.map fun b => Multiset.replicate b.2 b.1).sum

def σ (b : ℕ × ℕ) : ℕ := b.2 * b.1

def Good (B : List (ℕ × ℕ)) : Prop := (∀ b ∈ B, 0 < b.2) ∧ (B.map σ).Nodup

lemma flat_cons (b : ℕ × ℕ) (B : List (ℕ × ℕ)) :
    flat (b :: B) = Multiset.replicate b.2 b.1 + flat B := by
  simp [flat]

lemma flat_perm {B C : List (ℕ × ℕ)} (h : B.Perm C) : flat B = flat C := by
  unfold flat; exact (h.map _).sum_eq

lemma countP_disj (B : List (ℕ × ℕ)) (u w : ℕ) (h : u ≠ w) :
    B.countP (fun b => b.1 = u) + B.countP (fun b => b.1 = w) ≤ B.length := by
  induction B with
  | nil => simp
  | cons b B ih =>
    simp only [List.countP_cons, List.length_cons]
    by_cases h1 : b.1 = u <;> by_cases h2 : b.1 = w <;> simp_all <;> omega

lemma countP_erase_self (B : List (ℕ × ℕ)) (b : ℕ × ℕ) (hb : b ∈ B) (w : ℕ) :
    (B.erase b).countP (fun c => c.1 = w) + (if b.1 = w then 1 else 0) =
      B.countP (fun c => c.1 = w) := by
  have hp := List.perm_cons_erase hb
  have := hp.countP_eq (fun c => decide (c.1 = w))
  rw [this, List.countP_cons]
  simp only [decide_eq_true_eq]

/-- greedy arrangement: no two adjacent blocks with the same value -/
lemma arrange : ∀ (n : ℕ) (B : List (ℕ × ℕ)) (f : ℕ), B.length = n →
    (∀ v, 2 * B.countP (fun b => b.1 = v) ≤ B.length + 1) →
    2 * B.countP (fun b => b.1 = f) ≤ B.length →
    ∃ C : List (ℕ × ℕ), C.Perm B ∧ C.IsChain (fun a b => a.1 ≠ b.1) ∧
      ∀ h ∈ C.head?, h.1 ≠ f := by
  intro n
  induction n with
  | zero =>
    intro B f hB _ _
    rw [List.length_eq_zero_iff] at hB
    subst hB
    exact ⟨[], List.Perm.refl _, List.isChain_nil, by simp⟩
  | succ n ih =>
    intro B f hB hall hf
    -- a block whose value is not f
    have hex : ∃ b ∈ B, b.1 ≠ f := by
      by_contra hcon
      push Not at hcon
      have : B.countP (fun b => b.1 = f) = B.length := by
        rw [List.countP_eq_length]; intro a ha; simpa using hcon a ha
      omega
    let S : Finset ℕ := ((B.filter (fun b => b.1 ≠ f)).map Prod.fst).toFinset
    have hS : S.Nonempty := by
      obtain ⟨b, hb, hbf⟩ := hex
      exact ⟨b.1, by simp [S]; exact ⟨⟨b.2, hb⟩, hbf⟩⟩
    obtain ⟨u, huS, humax⟩ := Finset.exists_max_image S (fun v => B.countP (fun b => b.1 = v)) hS
    have huS' := huS
    simp only [S, List.mem_toFinset, List.mem_map, List.mem_filter] at huS'
    obtain ⟨b, ⟨hb, hbf⟩, rfl⟩ := huS'
    simp only [decide_eq_true_eq] at hbf
    have hlen : (B.erase b).length = n := by
      rw [List.length_erase_of_mem hb]; omega
    have hcu : 1 ≤ B.countP (fun c => c.1 = b.1) := by
      rw [Nat.one_le_iff_ne_zero, ne_eq, List.countP_eq_zero]; push Not
      exact ⟨b, hb, by simp⟩
    obtain ⟨C, hC, hCc, hCh⟩ := ih (B.erase b) b.1 hlen (by
        intro w
        have e := countP_erase_self B b hb w
        have hu := hall b.1
        by_cases hw : b.1 = w
        · subst hw; simp at e; omega
        · simp [hw] at e
          rw [hlen, e]
          by_cases hwf : w = f
          · subst hwf; omega
          · by_cases h0 : B.countP (fun c => c.1 = w) = 0
            · omega
            · have hwS : w ∈ S := by
                rw [List.countP_eq_zero] at h0; push Not at h0
                obtain ⟨c, hc, hcw⟩ := h0
                simp only [decide_eq_true_eq] at hcw
                simp [S]; exact ⟨⟨c.2, by rw [← hcw]; simpa using hc⟩, hwf⟩
              have := humax w hwS
              have := countP_disj B b.1 w hw
              omega)
      (by
        have e := countP_erase_self B b hb b.1
        simp at e
        have hu := hall b.1
        rw [hlen]; omega)
    refine ⟨b :: C, ?_, ?_, ?_⟩
    · exact (List.Perm.cons b hC).trans (List.perm_cons_erase hb).symm
    · exact List.IsChain.cons hCc (fun y hy => (hCh y hy).symm)
    · simpa using hbf


lemma coe_flatten_blocks (C : List (ℕ × ℕ)) :
    ((C.map fun b => List.replicate b.2 b.1).flatten : Multiset ℕ) = flat C := by
  induction C with
  | nil => simp [flat]
  | cons b C ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, flat_cons, Multiset.coe_replicate]

lemma mem_flat {B : List (ℕ × ℕ)} {b : ℕ × ℕ} (hb : b ∈ B) (h : 0 < b.2) : b.1 ∈ flat B := by
  rw [flat_perm (List.perm_cons_erase hb), flat_cons]
  exact Multiset.mem_add.2 (Or.inl (Multiset.mem_replicate.2 ⟨by omega, rfl⟩))

lemma split_blocks (C : List (ℕ × ℕ)) (hpos : ∀ b ∈ C, 0 < b.2)
    (hc : C.IsChain (fun a b => a.1 ≠ b.1)) :
    (C.map fun b => List.replicate b.2 b.1).flatten.splitBy (· == ·) =
      C.map fun b => List.replicate b.2 b.1 := by
  rw [List.splitBy_flatten]
  · simp only [List.mem_map, not_exists, not_and]
    intro b hb h
    have := hpos b hb
    rw [List.replicate_eq_nil_iff] at h; omega
  · intro m hm
    simp only [List.mem_map] at hm
    obtain ⟨b, _, rfl⟩ := hm
    exact List.isChain_replicate_of_rel _ (by simp)
  · rw [List.isChain_map]
    refine List.IsChain.imp_of_mem_imp ?_ hc
    intro a b ha hb hab
    have ha' := hpos a ha
    have hb' := hpos b hb
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    simp [hab]

lemma good_of_runs (l : List ℕ) (h : (runSums l).Nodup) :
    ∃ B : List (ℕ × ℕ), Good B ∧ flat B = (l : Multiset ℕ) := by
  have key : ∀ r ∈ l.splitBy (· == ·), r = List.replicate r.length (r.headD 0) := by
    intro r hr
    have hne := List.ne_nil_of_mem_splitBy hr
    have hch := List.isChain_of_mem_splitBy hr
    obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    rw [List.eq_replicate_iff]
    refine ⟨rfl, ?_⟩
    simp only [List.headD_cons]
    have : ∀ y ∈ x :: t, y = x := by
      clear hr hne
      induction t generalizing x with
      | nil => simp
      | cons z t ih2 =>
        rw [List.isChain_cons_cons] at hch
        have hxz : x = z := by simpa using hch.1
        subst hxz
        intro y hy
        rcases List.mem_cons.1 hy with h | h
        · exact h
        · exact ih2 x hch.2 y h
    exact this
  refine ⟨(l.splitBy (· == ·)).map (fun r => (r.headD 0, r.length)), ⟨?_, ?_⟩, ?_⟩
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨r, hr, rfl⟩ := hb
    exact List.length_pos_iff.2 (List.ne_nil_of_mem_splitBy hr)
  · have e : ((l.splitBy (· == ·)).map (fun r => (r.headD 0, r.length))).map σ = runSums l := by
      unfold runSums
      rw [List.map_map]
      apply List.map_congr_left
      intro r hr
      simp only [Function.comp_apply, σ]
      conv_rhs => rw [key r hr]
      rw [List.sum_replicate, smul_eq_mul]
    rw [e]; exact h
  · conv_rhs => rw [← List.flatten_splitBy (· == ·) l]
    have : (l.splitBy (· == ·)) = ((l.splitBy (· == ·)).map (fun r => (r.headD 0, r.length))).map
        (fun b => List.replicate b.2 b.1) := by
      rw [List.map_map]
      conv_lhs => rw [← List.map_id (l.splitBy (· == ·))]
      apply List.map_congr_left
      intro r hr
      exact key r hr
    conv_rhs => rw [this]
    rw [coe_flatten_blocks]

lemma part_of_good (M : Multiset ℕ) (hM : ∀ x ∈ M, 0 < x) (B : List (ℕ × ℕ)) (hG : Good B)
    (hf : flat B = M) : HasConstBlockPartition M := by
  refine ⟨((B.map fun b => Multiset.replicate b.2 b.1 : List (Multiset ℕ)) : Multiset (Multiset ℕ)),
    ?_, ?_, ?_⟩
  · rw [Multiset.sum_coe, ← hf]; rfl
  · intro m hm
    rw [Multiset.mem_coe, List.mem_map] at hm
    obtain ⟨b, hb, rfl⟩ := hm
    refine ⟨?_, b.1, by rw [Multiset.card_replicate]⟩
    have := hG.1 b hb
    intro h0
    have := congrArg Multiset.card h0
    rw [Multiset.card_replicate, Multiset.card_zero] at this; omega
  · rw [Multiset.map_coe, Multiset.coe_nodup, List.map_map]
    have e : (Multiset.sum ∘ fun b : ℕ × ℕ => Multiset.replicate b.2 b.1) = σ := by
      funext b; simp [σ, Multiset.sum_replicate]
    rw [e]; exact hG.2

lemma good_of_part (M : Multiset ℕ) (hM : ∀ x ∈ M, 0 < x) (h : HasConstBlockPartition M) :
    ∃ B : List (ℕ × ℕ), Good B ∧ flat B = M := by
  obtain ⟨P, hP, hc, hnd⟩ := h
  have hrep : ∀ b ∈ P, Multiset.replicate (Multiset.card b) (b.sum / Multiset.card b) = b ∧
      0 < Multiset.card b := by
    intro b hb
    obtain ⟨hne, v, hv⟩ := hc b hb
    have hk : 0 < Multiset.card b := Multiset.card_pos.2 hne
    refine ⟨?_, hk⟩
    conv_rhs => rw [hv]
    congr 1
    conv_lhs => rw [hv]
    rw [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul, Nat.mul_div_cancel_left _ hk]
  refine ⟨P.toList.map (fun b => (b.sum / Multiset.card b, Multiset.card b)), ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [List.mem_map, Multiset.mem_toList] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact (hrep b hb).2
  · have e : (P.toList.map (fun b => (b.sum / Multiset.card b, Multiset.card b))).map σ =
        P.toList.map Multiset.sum := by
      rw [List.map_map]
      apply List.map_congr_left
      intro b hb
      rw [Multiset.mem_toList] at hb
      simp only [Function.comp_apply, σ]
      conv_rhs => rw [← (hrep b hb).1]
      rw [Multiset.sum_replicate, smul_eq_mul]
    rw [e]
    have : (P.map Multiset.sum) = ((P.toList.map Multiset.sum : List ℕ) : Multiset ℕ) := by
      rw [← Multiset.map_coe, Multiset.coe_toList]
    rw [this, Multiset.coe_nodup] at hnd
    exact hnd
  · rw [← hP, flat, List.map_map]
    have : P.toList.map ((fun b : ℕ × ℕ => Multiset.replicate b.2 b.1) ∘
        fun b => (b.sum / Multiset.card b, Multiset.card b)) = P.toList.map id := by
      apply List.map_congr_left
      intro b hb
      rw [Multiset.mem_toList] at hb
      exact (hrep b hb).1
    rw [this, List.map_id, ← Multiset.sum_coe, Multiset.coe_toList]


lemma min_balanced (B : List (ℕ × ℕ)) (hG : Good B) (hv : ∀ b ∈ B, 0 < b.1)
    (hmin : ∀ C : List (ℕ × ℕ), Good C → flat C = flat B → B.length ≤ C.length) (v : ℕ) :
    2 * B.countP (fun b => b.1 = v) ≤ B.length + 1 := by
  classical
  set Bv := B.filter (fun b => b.1 = v) with hBv
  set Bo := B.filter (fun b => ¬ b.1 = v) with hBo
  have hk : B.countP (fun b => b.1 = v) = Bv.length := List.countP_eq_length_filter
  have hsum : B.length = Bv.length + Bo.length := by
    have := List.length_eq_length_filter_add (l := B) (fun b => decide (b.1 = v))
    simpa [hBv, hBo] using this
  have hnd := hG.2
  have hndv : (Bv.map σ).Nodup := (List.filter_sublist.map _).nodup hnd
  have hndo : (Bo.map σ).Nodup := (List.filter_sublist.map _).nodup hnd
  set Sv := (Bv.map σ).toFinset
  set So := (Bo.map σ).toFinset
  have hcv : Sv.card = Bv.length := by
    rw [List.card_toFinset, List.dedup_eq_self.2 hndv, List.length_map]
  have hco : So.card = Bo.length := by
    rw [List.card_toFinset, List.dedup_eq_self.2 hndo, List.length_map]
  rcases Nat.eq_zero_or_pos Bv.length with h0 | hpos
  · omega
  have hne : Sv.Nonempty := by
    rw [← Finset.card_pos]; omega
  set smax := Sv.max' hne
  have haS : smax ∈ Sv := Finset.max'_mem _ _
  have memSv : ∀ s ∈ Sv, ∃ b ∈ B, b.1 = v ∧ σ b = s := by
    intro s hs
    simp only [Sv, List.mem_toFinset, List.mem_map, hBv, List.mem_filter,
      decide_eq_true_eq] at hs
    obtain ⟨b, ⟨hb, hbv⟩, rfl⟩ := hs
    exact ⟨b, hb, hbv, rfl⟩
  have hbpos : ∀ b ∈ B, 0 < b.2 := hG.1
  have key : ∀ s ∈ Sv.erase smax, smax + s ∈ So := by
    intro s hs
    rw [Finset.mem_erase] at hs
    obtain ⟨hsa, hsS⟩ := hs
    by_contra hnot
    obtain ⟨β, hβ, hβv, hβs⟩ := memSv smax haS
    obtain ⟨γ, hγ, hγv, hγs⟩ := memSv s hsS
    have hγ' : γ ∈ B.erase β :=
      (List.mem_erase_of_ne (by intro e; rw [e] at hγs; exact hsa (hγs.symm.trans hβs))).2 hγ
    set rest := (B.erase β).erase γ
    have hperm : B.Perm (β :: γ :: rest) :=
      (List.perm_cons_erase hβ).trans (List.Perm.cons _ (List.perm_cons_erase hγ'))
    have hrestB : ∀ x ∈ rest, x ∈ B := fun x hx =>
      List.mem_of_mem_erase (List.mem_of_mem_erase hx)
    have hnd2 := (hperm.map σ).nodup_iff.1 hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd2
    have hbp := hbpos _ hβ
    have hcp := hbpos _ hγ
    have hvpos : 0 < v := hβv ▸ hv β hβ
    have hspos : 0 < s := by
      rw [← hγs]; simp only [σ]; rw [hγv]; positivity
    have hmerge : σ (v, β.2 + γ.2) = smax + s := by
      rw [← hβs, ← hγs]; simp only [σ]; rw [hβv, hγv]; ring
    have hGC : Good ((v, β.2 + γ.2) :: rest) := by
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · simp; omega
        · exact hbpos x (hrestB x hx)
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, hnd2.2.2⟩
        intro hm
        obtain ⟨x, hx, hx2⟩ := List.mem_map.1 hm
        rw [hmerge] at hx2
        have hxB := hrestB x hx
        by_cases hxv : x.1 = v
        · have : σ x ∈ Sv := by
            simp only [Sv, List.mem_toFinset, List.mem_map, hBv, List.mem_filter, decide_eq_true_eq]
            exact ⟨x, ⟨hxB, hxv⟩, rfl⟩
          have := Finset.le_max' Sv (σ x) this
          omega
        · apply hnot
          simp only [So, List.mem_toFinset, List.mem_map, hBo, List.mem_filter, decide_eq_true_eq]
          exact ⟨x, ⟨hxB, hxv⟩, hx2⟩
    have hfC : flat ((v, β.2 + γ.2) :: rest) = flat B := by
      rw [flat_perm hperm, flat_cons, flat_cons, flat_cons, ← add_assoc, hβv, hγv,
        ← Multiset.replicate_add]
    have := hmin _ hGC hfC
    have hl := hperm.length_eq
    simp only [List.length_cons] at this hl
    omega
  have himg : ((Sv.erase smax).image (fun s => smax + s)) ⊆ So := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hx
    exact key c hc
  have hcard := Finset.card_le_card himg
  rw [Finset.card_image_of_injective _ (add_right_injective smax),
    Finset.card_erase_of_mem haS] at hcard
  omega

lemma run_of_good (M : Multiset ℕ) (hM : ∀ x ∈ M, 0 < x) (B : List (ℕ × ℕ)) (hG : Good B)
    (hf : flat B = M) : HasPerm M := by
  classical
  have hex : ∃ m, ∃ C : List (ℕ × ℕ), Good C ∧ flat C = M ∧ C.length = m :=
    ⟨B.length, B, hG, hf, rfl⟩
  obtain ⟨Bm, hGm, hfm, hlm⟩ := Nat.find_spec hex
  have hmin : ∀ C : List (ℕ × ℕ), Good C → flat C = flat Bm → Bm.length ≤ C.length := by
    intro C hC hfC
    rw [hlm]
    exact Nat.find_min' hex ⟨C, hC, hfC.trans hfm, rfl⟩
  have hvpos : ∀ b ∈ Bm, 0 < b.1 := by
    intro b hb
    have := mem_flat hb (hGm.1 b hb)
    rw [hfm] at this
    exact hM _ this
  obtain ⟨C, hC, hCc, -⟩ := arrange Bm.length Bm 0 rfl (min_balanced Bm hGm hvpos hmin) (by
    have : Bm.countP (fun b => b.1 = 0) = 0 := by
      rw [List.countP_eq_zero]
      intro b hb
      have := hvpos b hb
      simp; omega
    rw [this]; omega)
  have hCpos : ∀ b ∈ C, 0 < b.2 := fun b hb => hGm.1 b (hC.subset hb)
  refine ⟨(C.map fun b => List.replicate b.2 b.1).flatten, ?_, ?_⟩
  · rw [coe_flatten_blocks, flat_perm hC, hfm]
  · unfold runSums
    rw [split_blocks C hCpos hCc, List.map_map]
    have e : (List.sum ∘ fun b : ℕ × ℕ => List.replicate b.2 b.1) = σ := by
      funext b; simp [σ, List.sum_replicate]
    rw [e]
    exact ((hC.map σ).nodup_iff).2 hGm.2


lemma equiv (M : Multiset ℕ) (hM : ∀ x ∈ M, 0 < x) : HasConstBlockPartition M ↔ HasPerm M := by
  constructor
  · intro h
    obtain ⟨B, hG, hf⟩ := good_of_part M hM h
    exact run_of_good M hM B hG hf
  · rintro ⟨l, hl, hnd⟩
    obtain ⟨B, hG, hf⟩ := good_of_runs l hnd
    exact part_of_good M hM B hG (hf.trans hl)

end OMA.P381636

open OMA.P381636 OMA.S_oeis_a381636 in
theorem OMA.solution : type_of% @OMA.S_oeis_a381636.main := by
  intro n hn
  have hM : ∀ x ∈ primeIndices n, 0 < x := by
    intro x hx
    simp only [primeIndices, primeIndexList, Multiset.mem_coe, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have hp2 := (Nat.prime_of_mem_primeFactorsList hp).two_le
    have h2 : Nat.primeCounting 2 = 1 := by decide
    have := Nat.monotone_primeCounting hp2
    omega
  unfold InA381636
  rw [equiv _ hM]
  unfold A382876 HasPerm
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h l hl hnd
    apply h
    refine ⟨l, ?_, hnd⟩
    rw [List.mem_toFinset, List.mem_permutations] at hl
    exact Multiset.coe_eq_coe.2 hl
  · rintro h ⟨l, hl, hnd⟩
    apply h _ hnd
    rw [List.mem_toFinset, List.mem_permutations]
    exact Multiset.coe_eq_coe.1 hl

