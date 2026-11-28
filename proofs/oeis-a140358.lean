import OMAStatements.S_oeis_a140358

-- Problem: A140358: Smallest nonnegative integer k such that n = +-1+-2+...+-k for some choice of +'s and -'s.
-- Upstream: formal-conjectures statements/oeis-a140358.lean:0 (declaration OMA.S_oeis_a140358.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with T(j) = j(j+1) = 2t(j), m is a signed sum of 1..j iff 2m <= T(j), -T(j) <= 2m and
-- T(j) - 2m is divisible by 4 (induction on j: change the sign of the last term; for the converse
-- take the last sign + when m > 0 and - otherwise). So a(n) is the least j with T(j) >= 2n and
-- T(j) = 2n mod 4; with T(k+1) = T(k)+2k+2, T(k+2) = T(k)+4k+6, T(k+3) = T(k)+6k+12 this least j
-- is the value of the conjecture in each of its five cases.

open OMA.S_oeis_a140358 in
theorem OMA.solution : type_of% @OMA.S_oeis_a140358.main := by
  intro n k hn hlo hhi
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℤ, ∀ j, T j = (j : ℤ) * ((j : ℤ) + 1) := ⟨_, fun _ => rfl⟩
  have hT0 : T 0 = 0 := by
    simp [hT]
  have hTs : ∀ j : ℕ, T (j + 1) = T j + 2 * (j : ℤ) + 2 := by
    intro j
    rw [hT, hT]
    push_cast
    ring
  have hTge : ∀ j : ℕ, 2 * (j : ℤ) ≤ T j := by
    intro j
    induction j with
    | zero =>
      simp [hT0]
    | succ j ih =>
      have h := hTs j
      push_cast
      omega
  have hTev : ∀ j : ℕ, T j % 2 = 0 := by
    intro j
    induction j with
    | zero =>
      simp [hT0]
    | succ j ih =>
      have h := hTs j
      omega
  have hTmono : ∀ i j : ℕ, i < j → T i < T j := by
    intro i j
    induction j with
    | zero =>
      intro h
      omega
    | succ j ih =>
      intro h
      have h1 := hTs j
      have h2 := hTge j
      by_cases h' : i < j
      · have h3 := ih h'
        omega
      · have h4 : i = j := by omega
        rw [h4]
        omega
  have L1 : ∀ (m : ℤ) (j : ℕ), IsSignedSum m j →
      2 * m ≤ T j ∧ -T j ≤ 2 * m ∧ (T j - 2 * m) % 4 = 0 := by
    rintro m j ⟨e, he, hs⟩
    rw [← hs]
    clear hs
    induction j with
    | zero =>
      rw [Finset.sum_range_zero, hT0]
      omega
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have h1 := hTs j
      rcases he j with h | h
      · rw [h]
        omega
      · rw [h]
        omega
  have L2 : ∀ (j : ℕ) (m : ℤ), 2 * m ≤ T j → -T j ≤ 2 * m → (T j - 2 * m) % 4 = 0 →
      IsSignedSum m j := by
    intro j
    induction j with
    | zero =>
      intro m h1 h2 _
      rw [hT0] at h1 h2
      refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
      rw [Finset.sum_range_zero]
      omega
    | succ j ih =>
      intro m h1 h2 h3
      have hs := hTs j
      have hg := hTge j
      have hev := hTev j
      by_cases hm : 0 < m
      · obtain ⟨e, he, hsum⟩ := ih (m - ((j : ℤ) + 1)) (by omega) (by omega) (by omega)
        refine ⟨Function.update e j 1, ?_, ?_⟩
        · intro i
          by_cases hij : i = j
          · rw [hij, Function.update_self]
            left
            rfl
          · rw [Function.update_of_ne hij]
            exact he i
        · rw [Finset.sum_range_succ, Function.update_self]
          have hc : ∑ i ∈ Finset.range j, Function.update e j 1 i * ((i : ℤ) + 1) =
              ∑ i ∈ Finset.range j, e i * ((i : ℤ) + 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mem_range] at hi
            rw [Function.update_of_ne (show i ≠ j by omega)]
          rw [hc, hsum]
          ring
      · obtain ⟨e, he, hsum⟩ := ih (m + ((j : ℤ) + 1)) (by omega) (by omega) (by omega)
        refine ⟨Function.update e j (-1), ?_, ?_⟩
        · intro i
          by_cases hij : i = j
          · rw [hij, Function.update_self]
            right
            rfl
          · rw [Function.update_of_ne hij]
            exact he i
        · rw [Finset.sum_range_succ, Function.update_self]
          have hc : ∑ i ∈ Finset.range j, Function.update e j (-1) i * ((i : ℤ) + 1) =
              ∑ i ∈ Finset.range j, e i * ((i : ℤ) + 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mem_range] at hi
            rw [Function.update_of_ne (show i ≠ j by omega)]
          rw [hc, hsum]
          ring
  have hfin : ∀ v : ℕ, IsSignedSum (n : ℤ) v → (∀ j : ℕ, j < v → ¬ IsSignedSum (n : ℤ) j) →
      a n = v := by
    intro v hv hmin
    have hmem : sInf {j : ℕ | IsSignedSum (n : ℤ) j} ∈ {j : ℕ | IsSignedSum (n : ℤ) j} :=
      Nat.sInf_mem ⟨v, hv⟩
    have hle : sInf {j : ℕ | IsSignedSum (n : ℤ) j} ≤ v := Nat.sInf_le hv
    unfold a
    by_contra hne
    exact hmin _ (lt_of_le_of_ne hle hne) hmem
  have hk2 : 2 * t k = k * (k + 1) := by
    unfold t
    exact Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd
  have hk12 : 2 * t (k + 1) = (k + 1) * (k + 1 + 1) := by
    unfold t
    exact Nat.mul_div_cancel' (Nat.even_mul_succ_self (k + 1)).two_dvd
  have htk : 2 * (t k : ℤ) = T k := by
    rw [hT]
    exact_mod_cast hk2
  have htk1 : 2 * (t (k + 1) : ℤ) = T (k + 1) := by
    rw [hT]
    exact_mod_cast hk12
  have e1 : T (k + 1) = T k + 2 * (k : ℤ) + 2 := hTs k
  have e2 : T (k + 2) = T k + 4 * (k : ℤ) + 6 := by
    rw [hT, hT]
    push_cast
    ring
  have e3 : T (k + 3) = T k + 6 * (k : ℤ) + 12 := by
    rw [hT, hT]
    push_cast
    ring
  by_cases h1 : n = t k
  · rw [if_pos h1]
    apply hfin k (L2 k n (by omega) (by omega) (by omega))
    intro j hj hS
    obtain ⟨b1, b2, b3⟩ := L1 n j hS
    have h5 := hTmono j k hj
    omega
  · rw [if_neg h1]
    by_cases h2 : k % 2 = 1
    · rw [if_pos h2]
      by_cases h3 : (n - t k) % 2 = 1
      · rw [if_pos h3]
        apply hfin (k + 2) (L2 (k + 2) n (by omega) (by omega) (by omega))
        intro j hj hS
        obtain ⟨b1, b2, b3⟩ := L1 n j hS
        rcases (show j < k ∨ j = k ∨ j = k + 1 by omega) with hj' | hj' | hj'
        · have h5 := hTmono j k hj'
          omega
        · rw [hj'] at b1
          omega
        · rw [hj'] at b3
          omega
      · rw [if_neg h3]
        apply hfin (k + 1) (L2 (k + 1) n (by omega) (by omega) (by omega))
        intro j hj hS
        obtain ⟨b1, b2, b3⟩ := L1 n j hS
        rcases (show j < k ∨ j = k by omega) with hj' | hj'
        · have h5 := hTmono j k hj'
          omega
        · rw [hj'] at b1
          omega
    · rw [if_neg h2]
      by_cases h3 : (n - t k) % 2 = 1
      · rw [if_pos h3]
        apply hfin (k + 1) (L2 (k + 1) n (by omega) (by omega) (by omega))
        intro j hj hS
        obtain ⟨b1, b2, b3⟩ := L1 n j hS
        rcases (show j < k ∨ j = k by omega) with hj' | hj'
        · have h5 := hTmono j k hj'
          omega
        · rw [hj'] at b1
          omega
      · rw [if_neg h3]
        apply hfin (k + 3) (L2 (k + 3) n (by omega) (by omega) (by omega))
        intro j hj hS
        obtain ⟨b1, b2, b3⟩ := L1 n j hS
        rcases (show j < k ∨ j = k ∨ j = k + 1 ∨ j = k + 2 by omega) with hj' | hj' | hj' | hj'
        · have h5 := hTmono j k hj'
          omega
        · rw [hj'] at b1
          omega
        · rw [hj'] at b3
          omega
        · rw [hj'] at b3
          omega
