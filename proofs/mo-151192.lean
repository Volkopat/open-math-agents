import OMAStatements.S_mo_151192

section
open OMA.S_mo_151192

private lemma table_succ {k N n t : ℕ} {a : State k N} :
    table k N n (t + 1) a = true ↔
      (live a).card ≤ n ∨
        ∃ q : Query N,
          table k N n t (move a q false) = true ∧ table k N n t (move a q true) = true := by
  rw [table, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]

private lemma table_step {k N n : ℕ} :
    ∀ {t : ℕ} {a : State k N}, table k N n t a = true → table k N n (t + 1) a = true
  | 0, _, h => table_succ.mpr (Or.inl (decide_eq_true_eq.mp h))
  | _ + 1, _, h => by
    rcases table_succ.mp h with hle | ⟨q, hf, ht⟩
    · exact table_succ.mpr (Or.inl hle)
    · exact table_succ.mpr (Or.inr ⟨q, table_step hf, table_step ht⟩)

private lemma table_mono {k N n t₁ t₂ : ℕ} {a : State k N}
    (hle : t₁ ≤ t₂) (h : table k N n t₁ a = true) : table k N n t₂ a = true :=
  Nat.le_induction h (fun _ _ ih => table_step ih) t₂ hle

private lemma table_congr {k N n t t' : ℕ} (h : table k N n t = table k N n t') :
    table k N n (t + 1) = table k N n (t' + 1) := by
  funext a
  simp only [table, h]

private lemma table_fix_add {k N n t : ℕ}
    (h : table k N n t = table k N n (t + 1)) (d : ℕ) :
    table k N n (t + d) = table k N n t := by
  induction d with
  | zero => rfl
  | succ d ih => rw [← Nat.add_assoc, table_congr ih, ← h]

private def winSet (k N n t : ℕ) : Finset (State k N) :=
  Finset.univ.filter fun a => table k N n t a = true

private lemma card_lt_of_ne {k N n t : ℕ} (hne : table k N n t ≠ table k N n (t + 1)) :
    (winSet k N n t).card < (winSet k N n (t + 1)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨fun a ha => ?_, fun heq => hne ?_⟩
  · simp only [winSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact table_step ha
  · funext a
    have hmem : a ∈ winSet k N n t ↔ a ∈ winSet k N n (t + 1) := by rw [heq]
    simp only [winSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact Bool.eq_iff_iff.mpr hmem

private lemma fix_or_card (k N n t : ℕ) :
    table k N n t = table k N n (t + 1) ∨ t + 1 ≤ (winSet k N n (t + 1)).card := by
  induction t with
  | zero =>
    by_cases h : table k N n 0 = table k N n 1
    · exact Or.inl h
    · have := card_lt_of_ne h
      exact Or.inr (by omega)
  | succ t ih =>
    rcases ih with h | _
    · exact Or.inl (table_congr h)
    · by_cases h' : table k N n (t + 1) = table k N n (t + 2)
      · exact Or.inl h'
      · have := card_lt_of_ne h'
        exact Or.inr (by omega)

private lemma table_sound {k N n : ℕ} :
    ∀ {t : ℕ} {a : State k N}, table k N n t a = true → Wins k N n a
  | 0, a, h => Wins.stop a (decide_eq_true_eq.mp h)
  | _ + 1, a, h => by
    rcases table_succ.mp h with hle | ⟨q, hf, ht⟩
    · exact Wins.stop a hle
    · exact Wins.ask a q (table_sound hf) (table_sound ht)

private lemma wins_exists_table {k N n : ℕ} {a : State k N} (hw : Wins k N n a) :
    ∃ t : ℕ, table k N n t a = true := by
  induction hw with
  | stop a hle => exact ⟨0, decide_eq_true hle⟩
  | ask a q _ _ ihf iht =>
    rcases ihf with ⟨tf, htf⟩
    rcases iht with ⟨tt, htt⟩
    exact ⟨max tf tt + 1, table_succ.mpr (Or.inr ⟨q,
      table_mono (Nat.le_max_left tf tt) htf,
      table_mono (Nat.le_max_right tf tt) htt⟩)⟩

private lemma test_iff (k s : ℕ) :
    test k s = true ↔ Wins k (s + 1) s (initial k (s + 1)) := by
  refine ⟨table_sound, fun hw => ?_⟩
  rcases wins_exists_table hw with ⟨t, ht⟩
  dsimp only [test]
  set M := (k + 2) ^ (s + 1)
  rcases fix_or_card k (s + 1) s M with hfix | hbad
  · rcases le_total t M with hle | hge
    · exact table_mono hle ht
    · have heq := congrFun (table_fix_add hfix (t - M)) (initial k (s + 1))
      rw [Nat.add_sub_of_le hge] at heq
      exact heq.symm.trans ht
  · exfalso
    have hle : (winSet k (s + 1) s (M + 1)).card ≤ Fintype.card (State k (s + 1)) :=
      Finset.card_le_univ _
    have hcard : Fintype.card (State k (s + 1)) = M := by simp [State, M]
    omega

private lemma scan_spec (k : ℕ) :
    ∀ r : ℕ, (∀ s < scan k r, test k s = false) ∧ (test k (scan k r) = true ∨ scan k r = r)
  | 0 => ⟨fun _ hs => absurd hs (Nat.not_lt_zero _), Or.inr rfl⟩
  | r + 1 => by
    rcases scan_spec k r with ⟨ih1, ih2⟩
    rw [scan]
    cases h : test k (scan k r)
    · rw [if_neg Bool.false_ne_true]
      have hr : scan k r = r := ih2.resolve_left (by rw [h]; decide)
      refine ⟨fun s hs => ?_, Or.inr rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | rfl
      · rw [hr] at ih1; exact ih1 s hlt
      · rw [hr] at h; exact h
    · rw [if_pos rfl]
      exact ⟨ih1, Or.inl h⟩

private lemma stop_of_dead {k N n : ℕ} (hN : N ≤ n + 1) (a : State k N)
    (x : Fin N) (hx : k + 1 ≤ (a x).val) : Wins k N n a := by
  apply Wins.stop
  have hsub : live a ⊆ Finset.univ.erase x := fun i hi => by
    rw [live, Finset.mem_filter] at hi
    exact Finset.mem_erase.mpr ⟨by rintro rfl; omega, hi.1⟩
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin] at hcard
  omega

private lemma move_step {k N d : ℕ} (a : State k N) (q : Query N) (b : Bool)
    (x : Fin N) (hq : q x ≠ b) (hd : d ≤ k) (ha : d ≤ (a x).val) :
    d + 1 ≤ (move a q b x).val := by
  simp only [move, update, hq, ↓reduceIte]
  split_ifs
  · omega
  · change d + 1 ≤ (a x).val + 1; omega

private lemma phase2 (k : ℕ) : ∀ (r d : ℕ), r + d = k + 1 →
    ∀ (a : State k (2 ^ k + 1)) (T : Finset (Fin (2 ^ k + 1))),
    T.card = 2 ^ r → (∀ x ∈ T, d ≤ (a x).val) → Wins k (2 ^ k + 1) (2 ^ k) a
  | 0, d, hrd, a, T, hcard, hT => by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    exact stop_of_dead (by omega) a x (by have := hT x hx; omega)
  | r + 1, d, hrd, a, T, hcard, hT => by
    obtain ⟨T₁, hsub, hc₁⟩ := Finset.exists_subset_card_eq (s := T) (n := 2 ^ r)
      (by rw [hcard, pow_succ]; omega)
    let q : Query (2 ^ k + 1) := fun x => decide (x ∈ T₁)
    refine Wins.ask a q (phase2 k r (d + 1) (by omega) _ T₁ hc₁ ?_)
      (phase2 k r (d + 1) (by omega) _ (T \ T₁) ?_ ?_)
    · exact fun x hx => move_step a q false x (by simp [q, hx]) (by omega) (hT x (hsub hx))
    · rw [Finset.card_sdiff_of_subset hsub, hcard, hc₁, pow_succ]; omega
    · intro x hx
      rw [Finset.mem_sdiff] at hx
      exact move_step a q true x (by simp [q, hx.2]) (by omega) (hT x hx.1)

private lemma phase1 (k : ℕ) : ∀ (rem m : ℕ), rem + m = k + 1 →
    ∀ (a : State k (2 ^ k + 1)), m ≤ (a ⟨0, by positivity⟩).val →
    Wins k (2 ^ k + 1) (2 ^ k) a
  | 0, _, _, a, hm => stop_of_dead (by omega) a ⟨0, by positivity⟩ (by omega)
  | rem + 1, m, _, a, hm => by
    let x₀ : Fin (2 ^ k + 1) := ⟨0, by positivity⟩
    let q : Query (2 ^ k + 1) := fun x => decide (x = x₀)
    refine Wins.ask a q (phase1 k rem (m + 1) (by omega) _ ?_)
      (phase2 k k 1 (by omega) _ (Finset.univ.erase x₀) ?_ ?_)
    · exact move_step a q false x₀ (by simp [q]) (by omega) hm
    · simp [Finset.card_erase_of_mem]
    · exact fun x hx => move_step a q true x
        (by simp [q, Finset.ne_of_mem_erase hx]) (by omega) (Nat.zero_le _)

private lemma update_mono {k : ℕ} {x y : Fin (k + 2)} (h : x.val ≤ y.val) (t ans : Bool) :
    (update k x t ans).val ≤ (update k y t ans).val := by
  have := x.isLt; have := y.isLt
  simp only [update]
  split_ifs <;> try dsimp only
  all_goals try simp only [Fin.val_zero]
  all_goals omega

private lemma live_move_subset {k N : ℕ} (a : State k N) (q : Query N) (b : Bool) :
    live (move a q b) ⊆ live a := fun x hx => by
  rw [live, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have h2 := hx.2
  simp only [move, update] at h2
  split_ifs at h2
  · omega
  · have := (a x).isLt; omega
  · dsimp only at h2; omega

private lemma sim {k s N : ℕ} (e : Fin (s + 1) ↪ Fin N) {b : State k (s + 1)}
    (hw : Wins k (s + 1) s b) : ∀ {a : State k N},
    (∀ j, (b j).val ≤ (a (e j)).val) →
    (∀ a', live a' ⊆ live a → (∃ j, ¬ (a' (e j)).val ≤ k) → Wins k N s a') →
    Wins k N s a := by
  induction hw with
  | stop b hcard =>
    intro a hle hcont
    have hex : ∃ j : Fin (s + 1), ¬ (b j).val ≤ k := by
      by_contra hno
      have hcov : (Finset.univ : Finset (Fin (s + 1))) ⊆ live b := fun j _ =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, Classical.not_not.mp fun hn => hno ⟨j, hn⟩⟩
      have hc := Finset.card_le_card hcov
      simp only [Finset.card_univ, Fintype.card_fin] at hc
      omega
    obtain ⟨j, hj⟩ := hex
    exact hcont a Finset.Subset.rfl ⟨j, by have := hle j; omega⟩
  | ask b q _ _ ihf iht =>
    intro a hle hcont
    let q' : Query N := fun x => if h : ∃ j, e j = x then q (Classical.choose h) else false
    have hq : ∀ j, q' (e j) = q j := fun j => by
      have hex : ∃ j', e j' = e j := ⟨j, rfl⟩
      simp only [q', dif_pos hex, e.injective (Classical.choose_spec hex)]
    have hstep : ∀ (ans : Bool) (j : Fin (s + 1)),
        (move b q ans j).val ≤ (move a q' ans (e j)).val := fun ans j => by
      simpa only [move, hq j] using update_mono (hle j) (q j) ans
    exact Wins.ask a q'
      (ihf (hstep false) fun a' hsub hex =>
        hcont a' (hsub.trans (live_move_subset a q' false)) hex)
      (iht (hstep true) fun a' hsub hex =>
        hcont a' (hsub.trans (live_move_subset a q' true)) hex)

private lemma wins_of_card {k s N : ℕ} (h : Wins k (s + 1) s (initial k (s + 1))) :
    ∀ (m : ℕ) (a : State k N), (live a).card ≤ m → Wins k N s a
  | 0, a, _ => Wins.stop a (by omega)
  | m + 1, a, _ => by
    by_cases hle : (live a).card ≤ s
    · exact Wins.stop a hle
    · obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := live a) (n := s + 1) (by omega)
      let eqv := T.equivFinOfCardEq hTcard
      let e : Fin (s + 1) ↪ Fin N :=
        ⟨fun j => (eqv.symm j).1, fun _ _ heq => eqv.symm.injective (Subtype.ext heq)⟩
      refine sim e h (fun _ => Nat.zero_le _) fun a' hsub ⟨j, hj⟩ => ?_
      have hej_out : e j ∉ live a' := fun hmem => hj (Finset.mem_filter.mp hmem).2
      have hc := Finset.card_le_card (Finset.subset_erase.mpr ⟨hsub, hej_out⟩)
      rw [Finset.card_erase_of_mem (hTsub (eqv.symm j).2 : e j ∈ live a)] at hc
      exact wins_of_card h m a' (by omega)

end

theorem OMA.solution : type_of% @OMA.S_mo_151192.main := by
  intro k _
  rcases scan_spec k (2 ^ k) with ⟨hfalse, htrue⟩
  rw [← OMA.S_mo_151192.answer] at hfalse htrue
  have hpow : OMA.S_mo_151192.test k (2 ^ k) = true :=
    (test_iff k (2 ^ k)).mpr (phase1 k (k + 1) 0 (by omega) _ (Nat.zero_le _))
  have hans : OMA.S_mo_151192.test k (OMA.S_mo_151192.answer k) = true :=
    htrue.elim id fun heq => heq.symm ▸ hpow
  refine ⟨fun N => wins_of_card ((test_iff k (OMA.S_mo_151192.answer k)).mp hans) _ _ le_rfl,
    fun s hs => ⟨s + 1, fun hw => ?_⟩⟩
  have hts : OMA.S_mo_151192.test k s = true := (test_iff k s).mpr hw
  rw [hfalse s hs] at hts
  cases hts
