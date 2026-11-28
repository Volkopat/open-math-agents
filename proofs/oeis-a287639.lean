import OMAStatements.S_oeis_a287639
import Mathlib

namespace OMA.A287639Proof

open OMA.S_oeis_a287639

/-- The set of admissible next terms after the list `l`. -/
def S (l : List ℕ) : Set ℕ := {k : ℕ | 1 ≤ k ∧ k ∉ l ∧ 10 ≤ wt (l.getLastD 0 + k)}

theorem mem_S {l : List ℕ} {k : ℕ} :
    k ∈ S l ↔ 1 ≤ k ∧ k ∉ l ∧ 10 ≤ wt (l.getLastD 0 + k) := Iff.rfl

theorem lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem le_sum_of_mem' : ∀ (l : List ℕ) (k : ℕ), k ∈ l → k ≤ l.sum
  | [], k, h => by simp at h
  | (b :: l), k, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with h1 | h1
    · omega
    · have := le_sum_of_mem' l k h1
      omega

-- Binary weight

theorem wt_eq (n : ℕ) : wt n = n % 2 + wt (n / 2) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [wt]
  · unfold wt
    rw [Nat.digits_def' (by norm_num) hn]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp <;> omega

theorem wt_two_pow_sub_one (K : ℕ) : wt (2 ^ K - 1) = K := by
  induction K with
  | zero => simp [wt]
  | succ K ih =>
    have hpos : 0 < 2 ^ K := pow_pos (by norm_num) K
    have h2 : (2 ^ (K + 1) - 1) % 2 = 1 := by rw [pow_succ]; omega
    have h3 : (2 ^ (K + 1) - 1) / 2 = 2 ^ K - 1 := by rw [pow_succ]; omega
    have h4 := wt_eq (2 ^ (K + 1) - 1)
    rw [h2, h3, ih] at h4
    omega

/-- The numbers below `2 ^ B` of weight at most `w` number at most `(B + 1) ^ w`. -/
theorem count_le (B : ℕ) :
    ∀ w : ℕ, ((Finset.range (2 ^ B)).filter (fun s => wt s ≤ w)).card ≤ (B + 1) ^ w := by
  induction B with
  | zero =>
    intro w
    calc _ ≤ (Finset.range (2 ^ 0)).card := Finset.card_filter_le _ _
      _ = 1 := by simp
      _ ≤ (0 + 1) ^ w := by simp
  | succ B ih =>
    intro w
    rcases w with _ | w
    · have hsub : (Finset.range (2 ^ (B + 1))).filter (fun s => wt s ≤ 0) ⊆
          ((Finset.range (2 ^ B)).filter (fun s => wt s ≤ 0)).image (fun s => 2 * s) := by
        intro s hs
        rw [Finset.mem_filter, Finset.mem_range] at hs
        rw [Finset.mem_image]
        have hw := wt_eq s
        rw [pow_succ] at hs
        refine ⟨s / 2, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_range]
          constructor <;> omega
        · show 2 * (s / 2) = s
          omega
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_image_le
        _ ≤ (B + 1) ^ 0 := ih 0
        _ ≤ (B + 1 + 1) ^ 0 := by simp
    · have hsub : (Finset.range (2 ^ (B + 1))).filter (fun s => wt s ≤ w + 1) ⊆
          ((Finset.range (2 ^ B)).filter (fun s => wt s ≤ w + 1)).image (fun s => 2 * s) ∪
          ((Finset.range (2 ^ B)).filter (fun s => wt s ≤ w)).image (fun s => 2 * s + 1) := by
        intro s hs
        rw [Finset.mem_filter, Finset.mem_range] at hs
        rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
        have hw := wt_eq s
        rw [pow_succ] at hs
        rcases Nat.mod_two_eq_zero_or_one s with h | h
        · left
          refine ⟨s / 2, ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_range]
            constructor <;> omega
          · show 2 * (s / 2) = s
            omega
        · right
          refine ⟨s / 2, ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_range]
            constructor <;> omega
          · show 2 * (s / 2) + 1 = s
            omega
      have hpow : (B + 1) ^ w ≤ (B + 1 + 1) ^ w := Nat.pow_le_pow_left (by omega) w
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ ((Finset.range (2 ^ B)).filter (fun s => wt s ≤ w + 1)).card +
            ((Finset.range (2 ^ B)).filter (fun s => wt s ≤ w)).card :=
          Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ ≤ (B + 1) ^ (w + 1) + (B + 1) ^ w := Nat.add_le_add (ih (w + 1)) (ih w)
        _ = (B + 1) ^ w * (B + 2) := by ring
        _ ≤ (B + 1 + 1) ^ w * (B + 2) := Nat.mul_le_mul hpow (le_refl _)
        _ = (B + 1 + 1) ^ (w + 1) := by ring

/-- Shifted count: `g < X` with `wt (c + g) ≤ 9` number at most `(B + 1) ^ 9` when `c + X ≤ 2 ^ B`. -/
theorem shift_count (c X B : ℕ) (h : c + X ≤ 2 ^ B) :
    ((Finset.range X).filter (fun g => wt (c + g) ≤ 9)).card ≤ (B + 1) ^ 9 := by
  have hsub : ((Finset.range X).filter (fun g => wt (c + g) ≤ 9)).image (fun g => c + g) ⊆
      (Finset.range (2 ^ B)).filter (fun s => wt s ≤ 9) := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    rw [Finset.mem_filter, Finset.mem_range] at hg ⊢
    exact ⟨by omega, hg.2⟩
  calc _ = (((Finset.range X).filter (fun g => wt (c + g) ≤ 9)).image (fun g => c + g)).card :=
        (Finset.card_image_of_injective _ (add_right_injective c)).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (B + 1) ^ 9 := count_le B 9

-- Polynomial against exponential, with explicit numbers

theorem step9 (B : ℕ) (hB : 14 ≤ B) : (B + 3) ^ 9 ≤ 2 * (B + 2) ^ 9 := by
  have h1 : (16 * (B + 3)) ^ 9 ≤ (17 * (B + 2)) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  rw [mul_pow, mul_pow] at h1
  have h3 : 16 ^ 9 * (B + 3) ^ 9 ≤ 16 ^ 9 * (2 * (B + 2) ^ 9) := by
    calc 16 ^ 9 * (B + 3) ^ 9 ≤ 17 ^ 9 * (B + 2) ^ 9 := h1
      _ ≤ (2 * 16 ^ 9) * (B + 2) ^ 9 := Nat.mul_le_mul (by norm_num) (le_refl _)
      _ = 16 ^ 9 * (2 * (B + 2) ^ 9) := by ring
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num)

theorem big_pow' (d : ℕ) : 4 * (64 + d + 2) ^ 9 ≤ 2 ^ (64 + d) := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    have h := step9 (64 + d) (by omega)
    have e1 : 64 + (d + 1) + 2 = 64 + d + 3 := by omega
    have e2 : 64 + (d + 1) = (64 + d) + 1 := by omega
    rw [e1, e2, pow_succ 2 (64 + d)]
    omega

theorem exists_B (K : ℕ) : ∃ B, 2 * (B + 2) ^ 9 + K + 1 < 2 ^ B := by
  refine ⟨64 + K, ?_⟩
  have h1 := big_pow' K
  have h2 : 2 * (K + 1) < 2 ^ (64 + K) := by
    calc 2 * (K + 1) < 4 * (K + 1) := by omega
      _ ≤ 2 ^ 64 * 2 ^ K := Nat.mul_le_mul (by norm_num) (lt_two_pow' K)
      _ = 2 ^ (64 + K) := (pow_add 2 64 K).symm
  omega

-- The greedy sequence

theorem pre_succ (n : ℕ) (hn : 1 ≤ n) : pre (n + 1) = pre n ++ [sInf (S (pre n))] := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

theorem getLastD_snoc (l : List ℕ) (b d : ℕ) : (l ++ [b]).getLastD d = b := by
  simp

theorem a_one : a 1 = 1 := rfl

theorem a_succ (n : ℕ) (hn : 1 ≤ n) : a (n + 1) = sInf (S (pre n)) := by
  show (pre (n + 1)).getLastD 0 = _
  rw [pre_succ n hn, getLastD_snoc]

theorem S_nonempty (l : List ℕ) : (S l).Nonempty := by
  have hK := lt_two_pow' (l.getLastD 0 + l.sum + 10)
  refine ⟨2 ^ (l.getLastD 0 + l.sum + 10) - 1 - l.getLastD 0, ?_⟩
  rw [mem_S]
  refine ⟨by omega, ?_, ?_⟩
  · intro hmem
    have := le_sum_of_mem' l _ hmem
    omega
  · have e : l.getLastD 0 + (2 ^ (l.getLastD 0 + l.sum + 10) - 1 - l.getLastD 0)
        = 2 ^ (l.getLastD 0 + l.sum + 10) - 1 := by omega
    rw [e, wt_two_pow_sub_one]
    omega

theorem a_succ_mem (n : ℕ) (hn : 1 ≤ n) : a (n + 1) ∈ S (pre n) := by
  rw [a_succ n hn]
  exact Nat.sInf_mem (S_nonempty _)

theorem a_succ_le (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ∈ S (pre n)) : a (n + 1) ≤ k := by
  rw [a_succ n hn]
  exact Nat.sInf_le hk

theorem pre_eq_map (n : ℕ) : pre n = (List.range n).map (fun i => a (i + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      rfl
    · rw [pre_succ n hn, List.range_succ, List.map_append, ← ih]
      simp only [List.map_cons, List.map_nil]
      rw [a_succ n hn]

theorem mem_pre (n k : ℕ) : k ∈ pre n ↔ ∃ j, 1 ≤ j ∧ j ≤ n ∧ a j = k := by
  rw [pre_eq_map, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    exact ⟨i + 1, by omega, by omega, rfl⟩
  · rintro ⟨j, hj1, hj2, rfl⟩
    refine ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
    show a (j - 1 + 1) = a j
    rw [Nat.sub_add_cancel hj1]

theorem a_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ a n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    exact le_of_eq a_one.symm
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (mem_S.mp (a_succ_mem k (by omega))).1

theorem a_ne (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) : a i ≠ a j := by
  intro h
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  have h1 := (mem_S.mp (a_succ_mem t (by omega))).2.1
  apply h1
  rw [mem_pre]
  exact ⟨i, hi, by omega, h⟩

theorem a_inj (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (h : a i = a j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (a_ne i j hi hlt)
  · exact heq
  · exact absurd h.symm (a_ne j i hj hgt)

theorem unbounded (X : ℕ) : ∃ n, 1 ≤ n ∧ X ≤ a n := by
  by_contra hcon
  push_neg at hcon
  have hmaps : ∀ n ∈ Finset.Icc 1 (X + 1), a n ∈ Finset.range X := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    exact hcon n hn.1
  have hinj : Set.InjOn a (Finset.Icc 1 (X + 1) : Set ℕ) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_Icc] at hi hj
    exact a_inj i j hi.1 hj.1 hij
  have hcard : (Finset.Icc 1 (X + 1)).card ≤ (Finset.range X).card :=
    Finset.card_le_card_of_injOn a (by intro n hn; exact hmaps n hn) hinj
  rw [Nat.card_Icc, Finset.card_range] at hcard
  omega

theorem exists_bound (T : ℕ) : ∃ K, ∀ j, j ≤ T → a j ≤ K := by
  induction T with
  | zero => exact ⟨a 0, fun j hj => le_of_eq (by rw [show j = 0 by omega])⟩
  | succ T ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨max K (a (T + 1)), fun j hj => ?_⟩
    rcases Nat.lt_or_ge j (T + 1) with h | h
    · exact le_trans (hK j (by omega)) (le_max_left _ _)
    · have h1 : j = T + 1 := by omega
      rw [h1]
      exact le_max_right _ _

-- Surjectivity

theorem no_least_missing (m : ℕ) (hm : 1 ≤ m) (hmiss : ∀ n, 1 ≤ n → a n ≠ m)
    (hprev : ∀ k, 1 ≤ k → k < m → ∃ n, 1 ≤ n ∧ a n = k) : False := by
  -- every value in [1, m) occurs among the first T terms
  have hT : ∀ M, M ≤ m → ∃ T, 1 ≤ T ∧ ∀ k, 1 ≤ k → k < M → k ∈ pre T := by
    intro M
    induction M with
    | zero => intro _; exact ⟨1, le_refl _, fun k _ hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ M ih =>
      intro hM
      obtain ⟨T, hT1, hT⟩ := ih (by omega)
      rcases Nat.eq_zero_or_pos M with h0 | hMpos
      · exact ⟨T, hT1, fun k hk1 hk2 => absurd hk2 (by omega)⟩
      · obtain ⟨j, hj1, hj⟩ := hprev M hMpos (by omega)
        refine ⟨max T j, le_trans hT1 (le_max_left T j), fun k hk1 hk2 => ?_⟩
        rw [mem_pre]
        rcases Nat.lt_or_ge k M with h | h
        · obtain ⟨i, hi1, hi2, hi3⟩ := (mem_pre T k).mp (hT k hk1 h)
          exact ⟨i, hi1, le_trans hi2 (le_max_left T j), hi3⟩
        · exact ⟨j, hj1, le_max_right T j, by omega⟩
  obtain ⟨T, hT1, hTm⟩ := hT m (le_refl _)
  -- (A) from step T on, a t + m has weight at most 9 (else m would be the next term)
  have hA : ∀ t, T ≤ t → wt (a t + m) ≤ 9 := by
    intro t ht
    by_contra hw
    push_neg at hw
    have hmS : m ∈ S (pre t) := by
      rw [mem_S]
      refine ⟨hm, ?_, ?_⟩
      · intro hmem
        obtain ⟨j, hj1, _, hj3⟩ := (mem_pre t m).mp hmem
        exact hmiss j hj1 hj3
      · show 10 ≤ wt (a t + m)
        omega
    have hle := a_succ_le t (by omega) m hmS
    have hmem := mem_S.mp (a_succ_mem t (by omega))
    rcases Nat.lt_or_ge (a (t + 1)) m with h | h
    · apply hmem.2.1
      obtain ⟨j, hj1, hj2, hj3⟩ := (mem_pre T _).mp (hTm _ hmem.1 h)
      exact (mem_pre t _).mpr ⟨j, hj1, by omega, hj3⟩
    · exact hmiss (t + 1) (by omega) (by omega)
  obtain ⟨K, hK⟩ := exists_bound T
  -- a value g > K with wt (m + g) ≥ 10 never occurs
  have hG : ∀ g, K < g → 10 ≤ wt (m + g) → ∀ n, 1 ≤ n → a n ≠ g := by
    intro g hg hw n hn h
    rcases Nat.lt_or_ge n T with h1 | h1
    · have := hK n (by omega)
      omega
    · have := hA n h1
      rw [h, add_comm] at this
      omega
  obtain ⟨B, hB⟩ := exists_B (K + m)
  have hex : ∃ n, 1 ≤ n ∧ 2 ^ B ≤ a n := unbounded (2 ^ B)
  obtain ⟨n0, hn0, hmin⟩ : ∃ n0, (1 ≤ n0 ∧ 2 ^ B ≤ a n0) ∧
      ∀ i, i < n0 → ¬ (1 ≤ i ∧ 2 ^ B ≤ a i) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hn0_2 : 2 ≤ n0 := by
    by_contra h
    have h1 : n0 = 1 := by omega
    have h2 := hn0.2
    rw [h1, a_one] at h2
    omega
  obtain ⟨t, rfl⟩ : ∃ t, n0 = t + 1 := ⟨n0 - 1, by omega⟩
  have hat : a t < 2 ^ B := by
    have h := hmin t (by omega)
    push_neg at h
    exact h (by omega)
  have hat1 : 2 ^ B ≤ a (t + 1) := hn0.2
  -- (B) at step t, every unused g < 2 ^ B was rejected
  have hrej : ∀ g, K < g → g < 2 ^ B → 10 ≤ wt (m + g) → wt (a t + g) ≤ 9 := by
    intro g hg1 hg2 hw
    by_contra hw2
    push_neg at hw2
    have hgS : g ∈ S (pre t) := by
      rw [mem_S]
      refine ⟨by omega, ?_, ?_⟩
      · intro hmem
        obtain ⟨j, hj1, _, hj3⟩ := (mem_pre t g).mp hmem
        exact hG g hg1 hw j hj1 hj3
      · show 10 ≤ wt (a t + g)
        omega
    have := a_succ_le t (by omega) g hgS
    omega
  -- counting: (K, 2 ^ B) is covered by two sets of low-weight shifts
  have hsub : Finset.Ico (K + 1) (2 ^ B) ⊆
      (Finset.range (2 ^ B)).filter (fun g => wt (m + g) ≤ 9) ∪
      (Finset.range (2 ^ B)).filter (fun g => wt (a t + g) ≤ 9) := by
    intro g hg
    rw [Finset.mem_Ico] at hg
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
    by_cases hw : wt (m + g) ≤ 9
    · exact Or.inl ⟨hg.2, hw⟩
    · push_neg at hw
      exact Or.inr ⟨hg.2, hrej g (by omega) hg.2 (by omega)⟩
  have hpow : 2 ^ (B + 1) = 2 * 2 ^ B := by rw [pow_succ]; ring
  have hc1 := shift_count m (2 ^ B) (B + 1) (by omega)
  have hc2 := shift_count (a t) (2 ^ B) (B + 1) (by omega)
  have e : B + 1 + 1 = B + 2 := by omega
  rw [e] at hc1 hc2
  have hcard := Finset.card_le_card hsub
  have hu := Finset.card_union_le ((Finset.range (2 ^ B)).filter (fun g => wt (m + g) ≤ 9))
      ((Finset.range (2 ^ B)).filter (fun g => wt (a t + g) ≤ 9))
  rw [Nat.card_Ico] at hcard
  omega

theorem surj (m : ℕ) : 1 ≤ m → ∃ n, 1 ≤ n ∧ a n = m := by
  refine Nat.strong_induction_on m ?_
  intro m ih hm
  by_contra hcon
  push_neg at hcon
  exact no_least_missing m hm hcon (fun k hk1 hk2 => ih k hk2 hk1)

end OMA.A287639Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a287639.main := by
  refine ⟨?_, ?_, ?_⟩
  · exact OMA.A287639Proof.a_pos
  · exact OMA.A287639Proof.a_inj
  · exact OMA.A287639Proof.surj
