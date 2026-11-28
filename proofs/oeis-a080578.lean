import OMAStatements.S_oeis_a080578

-- Problem: A080578: a(1)=1; for n > 1, a(n) = a(n-1) + 1 if n is already in the sequence, a(n) = a(n-1) + 3 otherwise.
-- Upstream: formal-conjectures statements/oeis-a080578.lean:0 (declaration OMA.S_oeis_a080578.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: b(2j) = b(j) + 2j, b(2j+1) = b(2j) + 1 and b(2j+2) >= b(2j+1) + 2, so b is strictly
-- increasing, its values come in pairs, and Nat.count NotGen (b m) = b m - m; in particular
-- count NotGen (b(2j)) = b(j). With c(k) = Nat.nth NotGen k this gives
-- c(k+1) = c(k) + 1 if k+1 is not generated and c(k+1) = c(k) + 3 otherwise. Hence
-- e(1) = 1, e(n) = c(n-2) + 2 obeys the defining rule of A080578, and by induction the list of
-- the first terms is [e(1), ..., e(k+1)].

open OMA.S_oeis_a080578 in
theorem OMA.solution : type_of% @OMA.S_oeis_a080578.main := by
  classical
  have hb0 : b 0 = 0 := b.eq_1
  have hbS : ∀ n : ℕ, b (n + 1) = b ((n + 1) / 2) + (n + 1) := b.eq_2
  have hbe : ∀ j : ℕ, b (2 * j) = b j + 2 * j := by
    intro j
    cases j with
    | zero => simp [hb0]
    | succ j =>
      have h1 := hbS (2 * j + 1)
      have h2 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
      rw [h2] at h1
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      omega
  have hbo : ∀ j : ℕ, b (2 * j + 1) = b (2 * j) + 1 := by
    intro j
    have h1 := hbS (2 * j)
    have h2 : (2 * j + 1) / 2 = j := by omega
    rw [h2] at h1
    have h3 := hbe j
    omega
  have hstep : ∀ n : ℕ, b n + 1 ≤ b (n + 1) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · have := hbo j
      omega
    · have h1 := hbe (j + 1)
      have h2 := hbo j
      have h3 := hbe j
      have h4 := ih j (by omega)
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
      omega
  have hgap : ∀ j : ℕ, b (2 * j + 1) + 2 ≤ b (2 * j + 1 + 1) := by
    intro j
    have h1 := hbe (j + 1)
    have h2 := hbo j
    have h3 := hbe j
    have h4 := hstep j
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    omega
  have hmono : StrictMono b := strictMono_nat_of_lt_succ (fun n => by have := hstep n; omega)
  have hgen : ∀ m : ℕ, ¬ NotGen (b m) := fun m h => h m rfl
  have hbetween : ∀ m x : ℕ, b m < x → x < b (m + 1) → NotGen x := by
    intro m x h1 h2 m' hm'
    rcases Nat.lt_or_ge m' (m + 1) with h | h
    · have := hmono.monotone (show m' ≤ m by omega)
      omega
    · have := hmono.monotone h
      omega
  have hcount : ∀ m : ℕ, Nat.count NotGen (b m) = b m - m := by
    intro m
    induction m with
    | zero => simp [hb0]
    | succ m ih =>
      obtain ⟨g, hg⟩ : ∃ g, b (m + 1) = b m + g := ⟨b (m + 1) - b m, by have := hstep m; omega⟩
      have hg1 : 1 ≤ g := by have := hstep m; omega
      have hq : ∀ t : ℕ, 1 ≤ t → t ≤ g →
          Nat.count (fun k => NotGen (b m + k)) t = t - 1 := by
        intro t
        induction t with
        | zero => intro h; omega
        | succ t iht =>
          intro _ ht
          rw [Nat.count_succ]
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · subst h0
            simp [hgen m]
          · rw [iht h0 (by omega)]
            simp only [hbetween m (b m + t) (by omega) (by omega), ↓reduceIte]
            omega
      rw [hg, Nat.count_add, ih, hq g hg1 le_rfl]
      have := hmono.id_le m
      have h5 : m ≤ b m := this
      omega
  have hinf : (Set.ofPred NotGen).Infinite := by
    have hm : StrictMono (fun j : ℕ => b (2 * j + 1) + 1) := by
      apply strictMono_nat_of_lt_succ
      intro j
      have h1 := hmono (show 2 * j + 1 < 2 * (j + 1) + 1 by omega)
      show b (2 * j + 1) + 1 < b (2 * (j + 1) + 1) + 1
      omega
    exact Set.infinite_of_injective_forall_mem hm.injective (fun j =>
      show b (2 * j + 1) + 1 ∈ Set.ofPred NotGen from
        hbetween (2 * j + 1) (b (2 * j + 1) + 1) (by omega) (by have := hgap j; omega))
  have hM : ∀ k : ℕ, Nat.nth NotGen (k + 1) =
      Nat.nth NotGen k + (if NotGen (k + 1) then 1 else 3) := by
    intro k
    obtain ⟨x, hxdef⟩ : ∃ x, x = Nat.nth NotGen k := ⟨_, rfl⟩
    rw [← hxdef]
    have hx : NotGen x := by
      rw [hxdef]
      exact Nat.nth_mem_of_infinite hinf k
    have hcx : Nat.count NotGen x = k := by
      rw [hxdef]
      exact Nat.count_nth_of_infinite hinf k
    have c1 := Nat.count_succ (p := NotGen) x
    rw [if_pos hx, hcx] at c1
    by_cases hA : NotGen (x + 1)
    · have hk1 : NotGen (k + 1) := by
        intro j hj
        have hj0 : j ≠ 0 := by
          rintro rfl
          rw [hb0] at hj
          omega
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := hcount (2 * (i + 1))
        have e2 := hbe (i + 1)
        have hg := hgap i
        have hBB : 2 * i + 1 + 1 = 2 * (i + 1) := by ring
        rw [hBB] at hg
        have hn : NotGen (b (2 * (i + 1)) - 1) :=
          hbetween (2 * i + 1) (b (2 * (i + 1)) - 1) (by omega) (by rw [hBB]; omega)
        have c2 := Nat.count_succ (p := NotGen) (b (2 * (i + 1)) - 1)
        rw [if_pos hn, show b (2 * (i + 1)) - 1 + 1 = b (2 * (i + 1)) by omega] at c2
        have hck : Nat.count NotGen (b (2 * (i + 1)) - 1) = k := by omega
        have h3 := Nat.nth_count hn
        rw [hck, ← hxdef] at h3
        exact hA (2 * (i + 1)) (by omega)
      rw [if_pos hk1]
      have h4 := Nat.nth_count hA
      rw [c1] at h4
      exact h4
    · simp only [NotGen, not_forall, ne_eq, not_not] at hA
      obtain ⟨m, hm⟩ := hA
      rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
      · have hn1 : ¬ NotGen (x + 1) := fun h => h (2 * j) hm
        have hbo' := hbo j
        have hn2 : ¬ NotGen (x + 1 + 1) := fun h => h (2 * j + 1) (by omega)
        have hg := hgap j
        have hn3 : NotGen (x + 1 + 1 + 1) :=
          hbetween (2 * j + 1) (x + 1 + 1 + 1) (by omega) (by omega)
        have c2 := Nat.count_succ (p := NotGen) (x + 1)
        rw [if_neg hn1] at c2
        have c3 := Nat.count_succ (p := NotGen) (x + 1 + 1)
        rw [if_neg hn2] at c3
        have hk1 : ¬ NotGen (k + 1) := by
          intro h
          have e1 := hcount (2 * j)
          have e2 := hbe j
          rw [hm] at e1
          exact h j (by omega)
        rw [if_neg hk1]
        have h4 := Nat.nth_count hn3
        rw [show Nat.count NotGen (x + 1 + 1 + 1) = k + 1 by omega] at h4
        omega
      · exact (hx (2 * j) (by have := hbo j; omega)).elim
  have hb1 : b 1 = 1 := by simpa [hb0] using hbo 0
  have hb2 : b 2 = 3 := by simpa [hb1] using hbe 1
  have hc0 : Nat.nth NotGen 0 = 2 := by
    have hn2 : NotGen 2 := hbetween 1 2 (by omega) (by norm_num [hb2])
    have c1 := Nat.count_succ (p := NotGen) 1
    rw [if_neg (show ¬ NotGen 1 from fun h => h 1 hb1)] at c1
    have c0 := hcount 1
    rw [hb1] at c0
    have e : (1 : ℕ) + 1 = 2 := rfl
    rw [e] at c1
    have h := Nat.nth_count hn2
    rw [show Nat.count NotGen 2 = 0 by omega] at h
    exact h
  have hnth_ge : ∀ n : ℕ, n + 2 ≤ Nat.nth NotGen n := by
    intro n
    induction n with
    | zero => simp [hc0]
    | succ n ih =>
      have h := hM n
      have h1 : 1 ≤ (if NotGen (n + 1) then 1 else 3) := by split_ifs <;> omega
      omega
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = if i = 0 then 1 else Nat.nth NotGen (i - 1) + 2 :=
    ⟨_, fun _ => rfl⟩
  have hlast : ∀ k : ℕ, ((List.range (k + 1)).map f).getLast?.getD 0 = f k := by
    intro k
    rw [List.range_succ, List.map_append]
    simp
  have hval : ∀ k : ℕ,
      f k + (if k + 2 ∈ (List.range (k + 1)).map f then 1 else 3) = f (k + 1) := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp [hf, hc0]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hmem : j + 1 + 2 ∈ (List.range (j + 1 + 1)).map f ↔ NotGen (j + 1) := by
        rw [List.mem_map]
        constructor
        · rintro ⟨i, _, hfi⟩
          rw [hf] at hfi
          by_cases hi0 : i = 0
          · rw [if_pos hi0] at hfi
            omega
          · rw [if_neg hi0] at hfi
            have hmem' := Nat.nth_mem_of_infinite hinf (i - 1)
            rw [show Nat.nth NotGen (i - 1) = j + 1 by omega] at hmem'
            exact hmem'
        · intro hN
          refine ⟨Nat.count NotGen (j + 1) + 1, ?_, ?_⟩
          · rw [List.mem_range]
            have h1 := Nat.nth_count hN
            have h2 := hnth_ge (Nat.count NotGen (j + 1))
            omega
          · rw [hf, if_neg (show ¬ (Nat.count NotGen (j + 1) + 1 = 0) by omega),
              Nat.add_sub_cancel, Nat.nth_count hN]
      have h1 : f (j + 1) = Nat.nth NotGen j + 2 := by
        rw [hf, if_neg (show ¬ (j + 1 = 0) by omega), Nat.add_sub_cancel]
      have h2 : f (j + 1 + 1) = Nat.nth NotGen (j + 1) + 2 := by
        rw [hf, if_neg (show ¬ (j + 1 + 1 = 0) by omega), Nat.add_sub_cancel]
      have hM' := hM j
      by_cases hN : NotGen (j + 1)
      · rw [if_pos hN] at hM'
        rw [if_pos (hmem.mpr hN)]
        omega
      · rw [if_neg hN] at hM'
        rw [if_neg (fun h => hN (hmem.mp h))]
        omega
  have hterms : ∀ k : ℕ, terms k = (List.range (k + 1)).map f := by
    intro k
    induction k with
    | zero => simp [terms, hf]
    | succ k ih =>
      simp only [terms]
      rw [ih, hlast k, hval k]
      simp [List.range_succ]
  intro n hn
  unfold a
  rw [hterms (n - 1), hlast (n - 1), hf, if_neg (show ¬ (n - 1 = 0) by omega),
    show n - 1 - 1 = n - 2 by omega]
