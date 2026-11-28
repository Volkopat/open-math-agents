import OMAStatements.S_oeis_a197702

-- Problem: A197702: Smallest positive integer k such that n = +-1 +-3 +-... +-(2k-1) for some choice of +'s and -'s.
-- Upstream: formal-conjectures statements/oeis-a197702.lean:0 (declaration OMA.S_oeis_a197702.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: SO(k) = k^2, and for signs e(i) in {1, -1},
-- k^2 - Sum_{i<k} e(i)(2i+1) = Sum_{i<k} (1 - e(i))(2i+1) = T, where T >= 0, T is even and
-- T is not 4 (no set of distinct odd numbers sums to 2). So a signed sum of length j is at most
-- j^2, has the parity of j^2, and is never j^2 - 4. Conversely, flipping the sign of one odd
-- number 2q+1 (q < j) gives j^2 - 2(2q+1), and flipping 1 and 2p+1 (0 < p < j) gives
-- j^2 - 2(1 + 2p + 1). With n = (k'+1)^2 - t, 1 <= t <= 2k', these choices reach n with the
-- claimed length, and the three facts exclude every shorter length.

namespace P1A197702

open OMA.S_oeis_a197702

theorem SO_eq (k : ℕ) : SO k = k ^ 2 := by
  induction k with
  | zero => simp [SO]
  | succ k ih =>
    simp only [SO] at ih ⊢
    rw [Finset.sum_range_succ, ih]
    ring

theorem keyEq (e : ℕ → ℤ) (k : ℕ) :
    (k : ℤ) ^ 2 - ∑ i ∈ Finset.range k, e i * (2 * (i : ℤ) + 1) =
      ∑ i ∈ Finset.range k, (1 - e i) * (2 * (i : ℤ) + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    push_cast
    ring

theorem flipT (e : ℕ → ℤ) (he : ∀ i, e i = 1 ∨ e i = -1) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range k, (1 - e i) * (2 * (i : ℤ) + 1) ∧
    ∑ i ∈ Finset.range k, (1 - e i) * (2 * (i : ℤ) + 1) ≠ 4 ∧
    ∃ m : ℤ, ∑ i ∈ Finset.range k, (1 - e i) * (2 * (i : ℤ) + 1) = 2 * m := by
  induction k with
  | zero => exact ⟨by norm_num, by norm_num, ⟨0, by norm_num⟩⟩
  | succ k ih =>
    obtain ⟨h0, h4, m, hm⟩ := ih
    rw [Finset.sum_range_succ]
    rcases he k with hk | hk
    · rw [hk, sub_self, zero_mul, add_zero]
      exact ⟨h0, h4, m, hm⟩
    · rw [hk, show (1 : ℤ) - -1 = 2 by norm_num]
      have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
      refine ⟨by linarith, ?_, ⟨m + 2 * k + 1, by rw [hm]; ring⟩⟩
      rcases Nat.eq_zero_or_pos k with hk1 | hk1
      · subst hk1
        norm_num
      · have hk2 : (1 : ℤ) ≤ (k : ℤ) := by omega
        intro h
        linarith

theorem rep_nec (n : ℤ) (j : ℕ) (h : Rep n j) :
    n ≤ (j : ℤ) ^ 2 ∧ n ≠ (j : ℤ) ^ 2 - 4 ∧ ∃ m : ℤ, (j : ℤ) ^ 2 - n = 2 * m := by
  obtain ⟨e, he, hn⟩ := h
  obtain ⟨h0, h4, m, hm⟩ := flipT e he j
  have hk := keyEq e j
  rw [← hn] at hk
  refine ⟨by linarith, ?_, ⟨m, by rw [hk, hm]⟩⟩
  intro h'
  apply h4
  linarith

theorem rep_of_T (n : ℤ) (j : ℕ) (e : ℕ → ℤ) (he : ∀ i, e i = 1 ∨ e i = -1)
    (hT : ∑ i ∈ Finset.range j, (1 - e i) * (2 * (i : ℤ) + 1) = (j : ℤ) ^ 2 - n) : Rep n j := by
  have hk := keyEq e j
  show ∃ f : ℕ → ℤ, (∀ i, f i = 1 ∨ f i = -1) ∧
    n = ∑ i ∈ Finset.range j, f i * (2 * (i : ℤ) + 1)
  exact ⟨e, he, by linarith⟩

theorem T_single (j q : ℕ) (hq : q < j) :
    ∑ i ∈ Finset.range j, (1 - (if i = q then (-1 : ℤ) else 1)) * (2 * (i : ℤ) + 1) =
      2 * (2 * (q : ℤ) + 1) := by
  rw [Finset.sum_eq_single q]
  · rw [if_pos (rfl : q = q)]
    ring
  · intro b _ hb
    rw [if_neg hb]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr hq) h

theorem rep_single (j q : ℕ) (hq : q < j) : Rep ((j : ℤ) ^ 2 - 2 * (2 * (q : ℤ) + 1)) j := by
  apply rep_of_T _ j (fun i => if i = q then (-1 : ℤ) else 1)
  · intro i
    show (if i = q then (-1 : ℤ) else 1) = 1 ∨ (if i = q then (-1 : ℤ) else 1) = -1
    by_cases h : i = q
    · rw [if_pos h]
      right
      rfl
    · rw [if_neg h]
      left
      rfl
  · rw [T_single j q hq]
    ring

theorem two_point (p i : ℕ) (hp : 0 < p) :
    (1 - (if i = 0 then (-1 : ℤ) else if i = p then -1 else 1)) * (2 * (i : ℤ) + 1) =
      (1 - (if i = 0 then (-1 : ℤ) else 1)) * (2 * (i : ℤ) + 1) +
        (1 - (if i = p then (-1 : ℤ) else 1)) * (2 * (i : ℤ) + 1) := by
  by_cases h0 : i = 0
  · have hip : ¬ i = p := by omega
    rw [if_pos h0, if_pos h0, if_neg hip]
    ring
  · by_cases hp' : i = p
    · rw [if_neg h0, if_neg h0, if_pos hp']
      ring
    · rw [if_neg h0, if_neg h0, if_neg hp']
      ring

theorem T_two (j p : ℕ) (hp : 0 < p) (hpj : p < j) :
    ∑ i ∈ Finset.range j, (1 - (if i = 0 then (-1 : ℤ) else if i = p then -1 else 1)) *
      (2 * (i : ℤ) + 1) = 2 * (1 + (2 * (p : ℤ) + 1)) := by
  have hc : ∑ i ∈ Finset.range j,
      (1 - (if i = 0 then (-1 : ℤ) else if i = p then -1 else 1)) * (2 * (i : ℤ) + 1) =
      ∑ i ∈ Finset.range j, ((1 - (if i = 0 then (-1 : ℤ) else 1)) * (2 * (i : ℤ) + 1) +
        (1 - (if i = p then (-1 : ℤ) else 1)) * (2 * (i : ℤ) + 1)) :=
    Finset.sum_congr rfl (fun i _ => two_point p i hp)
  rw [hc, Finset.sum_add_distrib, T_single j 0 (by omega), T_single j p hpj, Nat.cast_zero]
  ring

theorem rep_two (j p : ℕ) (hp : 0 < p) (hpj : p < j) :
    Rep ((j : ℤ) ^ 2 - 2 * (1 + (2 * (p : ℤ) + 1))) j := by
  apply rep_of_T _ j (fun i => if i = 0 then (-1 : ℤ) else if i = p then -1 else 1)
  · intro i
    show (if i = 0 then (-1 : ℤ) else if i = p then -1 else 1) = 1 ∨
      (if i = 0 then (-1 : ℤ) else if i = p then -1 else 1) = -1
    by_cases h0 : i = 0
    · rw [if_pos h0]
      right
      rfl
    · rw [if_neg h0]
      by_cases hp' : i = p
      · rw [if_pos hp']
        right
        rfl
      · rw [if_neg hp']
        left
        rfl
  · rw [T_two j p hp hpj]
    ring

theorem rep_all (j : ℕ) : Rep ((j : ℤ) ^ 2) j := by
  apply rep_of_T _ j (fun _ => (1 : ℤ))
  · intro _
    left
    rfl
  · simp

theorem a_eq (n K : ℕ) (hK : 0 < K) (hrep : Rep (n : ℤ) K)
    (hmin : ∀ j, 0 < j → j < K → ¬ Rep (n : ℤ) j) : a n = K := by
  unfold a
  have hmem : K ∈ {k : ℕ | 0 < k ∧ Rep (n : ℤ) k} := ⟨hK, hrep⟩
  have hne : ({k : ℕ | 0 < k ∧ Rep (n : ℤ) k}).Nonempty := ⟨K, hmem⟩
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · refine le_csInf hne ?_
    rintro j ⟨hj, hr⟩
    by_contra hlt
    exact hmin j hj (by omega) hr

theorem small_not_rep (n : ℤ) (j k : ℕ) (hj : j ≤ k) (hn : (k : ℤ) ^ 2 < n) : ¬ Rep n j := by
  intro h
  obtain ⟨h1, -, -⟩ := rep_nec n j h
  have hj' : (j : ℤ) ≤ k := by exact_mod_cast hj
  have hj0 : (0 : ℤ) ≤ j := by positivity
  nlinarith

theorem odd_not_rep (n : ℤ) (j : ℕ) (u : ℤ) (hu : (j : ℤ) ^ 2 - n = 2 * u + 1) : ¬ Rep n j := by
  intro h
  obtain ⟨-, -, m, hm⟩ := rep_nec n j h
  have h2 : 2 * m = 2 * u + 1 := by rw [← hm, hu]
  omega

end P1A197702

open OMA.S_oeis_a197702 P1A197702 in
theorem OMA.solution : type_of% @OMA.S_oeis_a197702.main := by
  refine ⟨fun k hk => ?_, fun n k h1 h2 => ?_⟩
  · rw [SO_eq]
    apply a_eq (k ^ 2) k (by omega)
    · rw [Nat.cast_pow k 2]
      exact rep_all k
    · intro j _hj0 hjk hr
      obtain ⟨hle, -, -⟩ := rep_nec _ j hr
      have hjk' : (j : ℤ) + 1 ≤ k := by omega
      have hj0' : (0 : ℤ) ≤ j := by positivity
      push_cast at hle
      nlinarith
  · rw [SO_eq] at h1 h2 ⊢
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        simp at h2
      · exact h
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel] at h1
    obtain ⟨t, ht⟩ : ∃ t, (k' + 1) ^ 2 - n = t := ⟨_, rfl⟩
    rw [ht]
    have hX : (k' + 1) ^ 2 = k' ^ 2 + 2 * k' + 1 := by ring
    have hnt : n + t = (k' + 1) ^ 2 := by omega
    have ht1 : 1 ≤ t := by omega
    have ht2 : t ≤ 2 * k' := by omega
    have hN : (n : ℤ) + t = ((k' : ℤ) + 1) ^ 2 := by exact_mod_cast hnt
    have hN1 : (k' : ℤ) ^ 2 < n := by exact_mod_cast h1
    refine ⟨fun h4 => ?_, fun _h4 hodd => ?_, fun h4 heven => ?_⟩
    · -- SO(k) - n = 4: length k + 2
      have h4' : (t : ℤ) = 4 := by exact_mod_cast h4
      apply a_eq n (k' + 1 + 2) (by omega)
      · have e : (n : ℤ) =
            ((k' + 1 + 2 : ℕ) : ℤ) ^ 2 - 2 * (1 + (2 * ((k' + 2 : ℕ) : ℤ) + 1)) := by
          push_cast
          linear_combination hN - h4'
        rw [e]
        exact rep_two (k' + 1 + 2) (k' + 2) (by omega) (by omega)
      · intro j _hj0 hjk
        rcases Nat.lt_or_ge j (k' + 1) with hj | hj
        · exact small_not_rep n j k' (by omega) hN1
        · rcases Nat.lt_or_ge j (k' + 2) with hj' | hj'
          · have hjeq : j = k' + 1 := by omega
            subst hjeq
            intro hr
            obtain ⟨-, hne, -⟩ := rep_nec _ _ hr
            apply hne
            push_cast
            linear_combination hN - h4'
          · have hjeq : j = k' + 2 := by omega
            subst hjeq
            apply odd_not_rep _ _ (k' + 3)
            push_cast
            linear_combination h4' - hN
    · -- SO(k) - n odd: length k + 1
      obtain ⟨u, hu⟩ := hodd
      have hu' : (t : ℤ) = 2 * u + 1 := by exact_mod_cast hu
      have hmin : ∀ j, 0 < j → j < k' + 1 + 1 → ¬ Rep (n : ℤ) j := by
        intro j _hj0 hjk
        rcases Nat.lt_or_ge j (k' + 1) with hj | hj
        · exact small_not_rep n j k' (by omega) hN1
        · have hjeq : j = k' + 1 := by omega
          subst hjeq
          apply odd_not_rep _ _ u
          push_cast
          linear_combination hu' - hN
      refine a_eq n (k' + 1 + 1) (by omega) ?_ hmin
      obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' (k' + 2 + u)
      · obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
        have hq' : (k' : ℤ) + 2 + u = 2 * ((p : ℤ) + 1) := by exact_mod_cast hq
        have e : (n : ℤ) = ((k' + 1 + 1 : ℕ) : ℤ) ^ 2 - 2 * (1 + (2 * (p : ℤ) + 1)) := by
          push_cast
          linear_combination hN - hu' - 2 * hq'
        rw [e]
        exact rep_two (k' + 1 + 1) p (by omega) (by omega)
      · have hq' : (k' : ℤ) + 2 + u = 2 * (q : ℤ) + 1 := by exact_mod_cast hq
        have e : (n : ℤ) = ((k' + 1 + 1 : ℕ) : ℤ) ^ 2 - 2 * (2 * (q : ℤ) + 1) := by
          push_cast
          linear_combination hN - hu' - 2 * hq'
        rw [e]
        exact rep_single (k' + 1 + 1) q (by omega)
    · -- SO(k) - n even, not 4: length k
      obtain ⟨s, hs | hs⟩ := Nat.even_or_odd' t
      · have hs' : (t : ℤ) = 2 * s := by exact_mod_cast hs
        have hmin : ∀ j, 0 < j → j < k' + 1 → ¬ Rep (n : ℤ) j := by
          intro j _hj0 hjk
          exact small_not_rep n j k' (by omega) hN1
        refine a_eq n (k' + 1) (by omega) ?_ hmin
        obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' s
        · obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
          have hq' : (s : ℤ) = 2 * ((p : ℤ) + 1) := by exact_mod_cast hq
          have e : (n : ℤ) = ((k' + 1 : ℕ) : ℤ) ^ 2 - 2 * (1 + (2 * (p : ℤ) + 1)) := by
            push_cast
            linear_combination hN - hs' - 2 * hq'
          rw [e]
          exact rep_two (k' + 1) p (by omega) (by omega)
        · have hq' : (s : ℤ) = 2 * (q : ℤ) + 1 := by exact_mod_cast hq
          have e : (n : ℤ) = ((k' + 1 : ℕ) : ℤ) ^ 2 - 2 * (2 * (q : ℤ) + 1) := by
            push_cast
            linear_combination hN - hs' - 2 * hq'
          rw [e]
          exact rep_single (k' + 1) q (by omega)
      · exact (heven ⟨s, hs⟩).elim
