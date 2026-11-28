import OMAStatements.S_oeis_a183264

-- Problem: A183264: Number of singly defective permutations of 1..n with exactly 1 maximum.
-- Upstream: formal-conjectures statements/oeis-a183264.lean:0 (declaration OMA.S_oeis_a183264.main)
-- Credit: @lettucrisp (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA.A183264Proof
open OMA.S_oeis_a183264

variable {α : Type*} [LinearOrder α]

/-- The word with left side `u` and plateau of length `m`. -/
def word (M : α) (m : ℕ) (c' u : Multiset α) : List α :=
  u.sort (· ≤ ·) ++ List.replicate m M ++ (c' - u).sort (· ≥ ·)

lemma filter_not_lt (M : α) (c : Multiset α) (hc : ∀ x ∈ c, x ≤ M) :
    c.filter (fun x => ¬ x < M) = Multiset.replicate (c.count M) M := by
  rw [Multiset.eq_replicate]
  constructor
  · rw [Multiset.count_eq_card_filter_eq]
    congr 1
    apply Multiset.filter_congr
    intro x hx
    have := hc x hx
    constructor
    · intro h; exact (le_antisymm this (not_lt.mp h)).symm
    · rintro rfl; exact lt_irrefl _
  · intro x hx
    obtain ⟨hx, hlt⟩ := Multiset.mem_filter.mp hx
    exact le_antisymm (hc x hx) (not_lt.mp hlt)

lemma takeWhile_word (M : α) (m : ℕ) (hm : 1 ≤ m) (c' u : Multiset α) (hu : ∀ x ∈ u, x < M) :
    (word M m c' u).takeWhile (fun x => decide (x < M)) = u.sort (· ≤ ·) := by
  unfold word
  rw [List.append_assoc, List.takeWhile_append_of_pos]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp [List.replicate_succ]
  · intro x hx
    simpa using hu x ((Multiset.mem_sort _).mp hx)

lemma peakWords_eq (M : α) (c : Multiset α) (hc : ∀ x ∈ c, x ≤ M) (hM : 1 ≤ c.count M) :
    peakWords M c = word M (c.count M) (c.filter (· < M)) '' {u | u ≤ c.filter (· < M)} := by
  have split : c = c.filter (· < M) + Multiset.replicate (c.count M) M := by
    rw [← filter_not_lt M c hc, Multiset.filter_add_not]
  ext w
  constructor
  · rintro ⟨hw, up, down, k, hup, hdown, rfl⟩
    have hcw : c = up + Multiset.replicate (k + 1) M + down := by
      rw [← hw, ← Multiset.coe_add, ← Multiset.coe_add, Multiset.sort_eq, Multiset.sort_eq,
        Multiset.coe_replicate]
    have hcount : c.count M = k + 1 := by
      rw [hcw]
      simp [Multiset.count_replicate_self, Multiset.count_eq_zero.mpr (fun h => lt_irrefl _ (hup M h)),
        Multiset.count_eq_zero.mpr (fun h => lt_irrefl _ (hdown M h))]
    have hfil : c.filter (· < M) = up + down := by
      rw [hcw]
      simp only [Multiset.filter_add]
      rw [Multiset.filter_eq_self.mpr hup, Multiset.filter_eq_self.mpr hdown,
        Multiset.filter_eq_nil.mpr (fun x hx => by
          rw [Multiset.eq_of_mem_replicate hx]; exact lt_irrefl _)]
      simp
    refine ⟨up, ?_, ?_⟩
    · show up ≤ _; rw [hfil]; exact Multiset.le_add_right _ _
    · simp only [word, hcount, hfil, add_tsub_cancel_left]
  · rintro ⟨u, hu, rfl⟩
    have hu' : u ≤ c.filter (· < M) := hu
    have hlt : ∀ x ∈ u, x < M := fun x hx => (Multiset.mem_filter.mp (Multiset.mem_of_le hu' hx)).2
    refine ⟨?_, u, c.filter (· < M) - u, c.count M - 1, hlt, ?_, ?_⟩
    · simp only [word]
      rw [← Multiset.coe_add, ← Multiset.coe_add, Multiset.sort_eq, Multiset.sort_eq,
        Multiset.coe_replicate, add_right_comm, add_tsub_cancel_of_le hu']
      exact split.symm
    · intro x hx
      exact (Multiset.mem_filter.mp (Multiset.mem_of_le (tsub_le_self) hx)).2
    · simp only [word]; congr 2; congr 1; omega

lemma ncard_peak (M : α) (c : Multiset α) (hc : ∀ x ∈ c, x ≤ M) (hM : 1 ≤ c.count M) :
    (peakWords M c).ncard = {u : Multiset α | u ≤ c.filter (· < M)}.ncard := by
  rw [peakWords_eq M c hc hM]
  apply Set.ncard_image_of_injOn
  intro u hu v hv e
  have hlt (w : Multiset α) (hw : w ≤ c.filter (· < M)) : ∀ x ∈ w, x < M :=
    fun x hx => (Multiset.mem_filter.mp (Multiset.mem_of_le hw hx)).2
  have := congrArg (fun l => (l.takeWhile (fun x => decide (x < M)) : Multiset α)) e
  simp only [takeWhile_word M _ hM _ u (hlt u hu), takeWhile_word M _ hM _ v (hlt v hv),
    Multiset.sort_eq] at this
  exact this

lemma ncard_sub_nodup (s' : Finset α) : {u : Multiset α | u ≤ s'.val}.ncard = 2 ^ s'.card := by
  have h : {u : Multiset α | u ≤ s'.val} = (fun T : Finset α => T.val) '' ↑(s'.powerset) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_powerset, Set.mem_preimage,
      Set.mem_powerset_iff, Finset.coe_subset]
    constructor
    · intro hu
      exact ⟨⟨u, Multiset.nodup_of_le hu s'.nodup⟩, Finset.val_le_iff.mp hu, rfl⟩
    · rintro ⟨T, hT, rfl⟩
      exact Finset.val_le_iff.mpr hT
  rw [h, Set.ncard_image_of_injective _ Finset.val_injective, Set.ncard_coe_finset,
    Finset.card_powerset]

lemma ncard_sub_double (s0 : Finset α) (r : α) (hr : r ∉ s0) :
    {u : Multiset α | u ≤ r ::ₘ r ::ₘ s0.val}.ncard = 3 * 2 ^ s0.card := by
  classical
  let f : Finset α × ℕ → Multiset α := fun p => p.1.val + Multiset.replicate p.2 r
  have h : {u : Multiset α | u ≤ r ::ₘ r ::ₘ s0.val} = f '' ↑(s0.powerset ×ˢ Finset.range 3) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_product, Set.mem_prod,
      Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset,
      Finset.coe_range, Set.mem_Iio, Prod.exists, f]
    constructor
    · intro hu
      have hfil : u.filter (· ≠ r) ≤ s0.val := by
        have := Multiset.filter_le_filter (· ≠ r) hu
        rwa [Multiset.filter_cons_of_neg _ (by simp), Multiset.filter_cons_of_neg _ (by simp),
          Multiset.filter_eq_self.mpr (show ∀ x ∈ s0.val, x ≠ r from fun x hx e => hr (e ▸ hx))] at this
      refine ⟨⟨u.filter (· ≠ r), Multiset.nodup_of_le hfil s0.nodup⟩, u.count r,
        ⟨Finset.val_le_iff.mp hfil, ?_⟩, ?_⟩
      · have := Multiset.count_le_of_le r hu
        simp [Multiset.count_cons_self, Multiset.count_eq_zero.mpr hr] at this
        omega
      · show u.filter (· ≠ r) + Multiset.replicate (u.count r) r = u
        rw [← Multiset.filter_eq' u r]
        conv_rhs => rw [← Multiset.filter_add_not (· ≠ r) u]
        congr 1
        apply Multiset.filter_congr
        intro x _
        simp [eq_comm]
    · rintro ⟨T, j, ⟨hT, hj⟩, rfl⟩
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x = r
      · subst hx
        have hT0 : x ∉ T := fun h => hr (hT h)
        simp [Multiset.count_replicate_self, Multiset.count_eq_zero.mpr hT0,
          Multiset.count_eq_zero.mpr hr]
        omega
      · have := Multiset.count_le_of_le x (Finset.val_le_iff.mpr hT)
        simp [Multiset.count_replicate, Multiset.count_cons, hx, Ne.symm hx]
        omega
  rw [h, Set.ncard_image_of_injOn, Set.ncard_coe_finset, Finset.card_product, Finset.card_powerset,
    Finset.card_range]
  · ring
  · rintro ⟨T1, j1⟩ h1 ⟨T2, j2⟩ h2 e
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_powerset, Set.mem_preimage,
      Set.mem_powerset_iff, Finset.coe_subset, f] at h1 h2 e
    have c1 : r ∉ T1 := fun h => hr (h1.1 h)
    have c2 : r ∉ T2 := fun h => hr (h2.1 h)
    have hj : j1 = j2 := by
      have := congrArg (Multiset.count r) e
      simpa [Multiset.count_replicate_self, Multiset.count_eq_zero.mpr c1,
        Multiset.count_eq_zero.mpr c2] using this
    subst hj
    have hT : T1.val = T2.val := add_right_cancel e
    simp [Finset.val_inj.mp hT]

lemma countRepeats_eq (s : Finset α) (h : s.Nonempty) :
    countRepeats s = 2 ^ (s.card - 1) + (s.card - 1) * (3 * 2 ^ (s.card - 2)) := by
  unfold countRepeats
  rw [dif_pos h]
  set M := s.max' h with hMdef
  have hMs : M ∈ s := Finset.max'_mem s h
  have hle : ∀ x ∈ s, x ≤ M := fun x hx => Finset.le_max' s x hx
  have hval : s.val = M ::ₘ (s.erase M).val := by
    rw [Finset.erase_val, Multiset.cons_erase (Finset.mem_val.mpr hMs)]
  have hlt' : ∀ x ∈ (s.erase M).val, x < M := fun x hx => by
    have hx' := Finset.mem_erase.mp (Finset.mem_val.mp hx)
    exact lt_of_le_of_ne (hle x hx'.2) hx'.1
  have hcard : (s.erase M).card = s.card - 1 := Finset.card_erase_of_mem hMs
  rw [← Finset.add_sum_erase s _ hMs]
  congr 1
  · rw [ncard_peak M _ (fun x hx => by
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact hle x hx) (by simp [Multiset.count_cons_self])]
    have : (M ::ₘ s.val).filter (· < M) = (s.erase M).val := by
      rw [hval, Multiset.filter_cons_of_neg (p := fun x => x < M) _ (lt_irrefl M), Multiset.filter_cons_of_neg (p := fun x => x < M) _ (lt_irrefl M),
        Multiset.filter_eq_self.mpr hlt']
    rw [this, ncard_sub_nodup, hcard]
  · have each : ∀ r ∈ s.erase M, (peakWords M (r ::ₘ s.val)).ncard = 3 * 2 ^ (s.card - 2) := by
      intro r hr
      have hr' := Finset.mem_erase.mp hr
      have hrM : r < M := lt_of_le_of_ne (hle r hr'.2) hr'.1
      rw [ncard_peak M _ (fun x hx => by
          rcases Multiset.mem_cons.mp hx with rfl | hx
          · exact hrM.le
          · exact hle x hx) (by
          rw [Multiset.count_cons_of_ne (Ne.symm hr'.1)]
          exact Multiset.one_le_count_iff_mem.mpr (Finset.mem_val.mpr hMs))]
      have hval' : (s.erase M).val = r ::ₘ ((s.erase M).erase r).val := by
        rw [Finset.erase_val (s.erase M) r, Multiset.cons_erase (Finset.mem_val.mpr hr)]
      have : (r ::ₘ s.val).filter (· < M) = r ::ₘ r ::ₘ ((s.erase M).erase r).val := by
        rw [hval, Multiset.filter_cons_of_pos (p := fun x => x < M) _ hrM, Multiset.filter_cons_of_neg (p := fun x => x < M) _ (lt_irrefl M),
          Multiset.filter_eq_self.mpr hlt', hval']
      rw [this, ncard_sub_double _ r (Finset.notMem_erase r _), Finset.card_erase_of_mem hr, hcard,
        Nat.sub_sub]
    rw [Finset.sum_congr rfl each, Finset.sum_const, smul_eq_mul, hcard]

lemma a_eq (n : ℕ) (hn : 2 ≤ n) : a n = n * (2 ^ (n - 2) + (n - 2) * (3 * 2 ^ (n - 3))) := by
  unfold a
  have each : ∀ m : Fin n, countRepeats (Finset.univ.erase m) =
      2 ^ (n - 2) + (n - 2) * (3 * 2 ^ (n - 3)) := by
    intro m
    have hc : (Finset.univ.erase m).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
    rw [countRepeats_eq _ (Finset.card_pos.mp (by omega)), hc,
      show n - 1 - 1 = n - 2 by omega, show n - 1 - 2 = n - 3 by omega]
  rw [Finset.sum_congr rfl (fun m _ => each m), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

end OMA.A183264Proof

open OMA.A183264Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a183264.main := by
  intro n hn
  rw [a_eq n hn]
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have hz : ((k + 3 : ℕ) : ℤ) - 3 = (k : ℤ) := by push_cast; ring
    rw [hz, zpow_natCast]
    simp only [show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
    push_cast
    ring
