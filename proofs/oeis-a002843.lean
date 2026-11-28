import OMAStatements.S_oeis_a002843
import Mathlib.Tactic

namespace OMA.P_oeis_a002843

open OMA.S_oeis_a002843

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℤ) (m n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℤ) ^ m * f) =
      if m ≤ n then PowerSeries.coeff (n - m) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single (m, n - m)]
    · simp [PowerSeries.coeff_X_pow]
    · rintro ⟨a, b⟩ hab hne
      rw [Finset.mem_antidiagonal] at hab
      have ham : a ≠ m := fun ha => hne (Prod.ext ha (by omega))
      dsimp only
      rw [PowerSeries.coeff_X_pow, if_neg ham, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_antidiagonal.mpr (by omega)) hnot
  · refine Finset.sum_eq_zero fun ⟨a, b⟩ hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    have ham : a ≠ m := by omega
    dsimp only
    rw [PowerSeries.coeff_X_pow, if_neg ham, zero_mul]

private lemma dyadic_part_ge_half (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℚ) / 2 ≤ ((2 ^ k - 1 : ℚ) / (2 ^ k : ℚ)) := by
  have h2k : (2 : ℚ) ≤ (2 : ℚ) ^ k := by
    calc (2 : ℚ) = (2 : ℚ) ^ 1 := by norm_num
      _ ≤ (2 : ℚ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hpos : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  rw [div_le_div_iff₀ (by norm_num) hpos]
  linarith

private lemma dyadic_card_le (n : ℕ) (s : Multiset ℕ) (hs : IsDyadicPartition n s) :
    s.card ≤ 2 * n := by
  have hle : ((s.card : ℕ) : ℚ) * ((1 : ℚ) / 2) ≤ (n : ℚ) := by
    rw [← hs.2]
    have h1 : ((s.card : ℕ) : ℚ) * ((1 : ℚ) / 2) = (s.map (fun _ => ((1 : ℚ) / 2))).sum := by
      simp [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
    rw [h1]
    have hrel : Multiset.Rel (· ≤ ·) (s.map (fun _ => ((1 : ℚ) / 2)))
        (s.map (fun k : ℕ => ((2 ^ k - 1 : ℚ) / (2 ^ k : ℚ)))) := by
      rw [Multiset.rel_map]
      refine Multiset.rel_refl_of_refl_on fun k hk => dyadic_part_ge_half k (hs.1 k hk)
    exact Multiset.sum_le_sum_of_rel_le hrel
  have hle2 : ((s.card : ℕ) : ℚ) ≤ ((2 * n : ℕ) : ℚ) := by push_cast; linarith
  exact_mod_cast hle2

private lemma dyadic_max_even_count (n M : ℕ) (s : Multiset ℕ) (hs : IsDyadicPartition n s)
    (hM1 : 1 ≤ M) (hMmax : ∀ k ∈ s, k ≤ M) :
    2 ∣ s.count M := by
  have hsum_split : (s.map (fun k : ℕ => ((2 ^ k - 1 : ℚ) / (2 ^ k : ℚ)))).sum =
      ((s.card : ℕ) : ℚ) - (s.map (fun k : ℕ => (1 : ℚ) / (2 ^ k : ℚ))).sum := by
    have hrew : s.map (fun k : ℕ => ((2 ^ k - 1 : ℚ) / (2 ^ k : ℚ))) =
        s.map (fun k : ℕ => (1 : ℚ) - (1 : ℚ) / (2 ^ k : ℚ)) := by
      refine Multiset.map_congr rfl fun k _ => ?_
      have hpos : (2 : ℚ) ^ k ≠ 0 := by positivity
      field_simp
    rw [hrew]
    have hadd : ∀ t : Multiset ℕ,
        (t.map (fun k : ℕ => (1 : ℚ) - (1 : ℚ) / (2 ^ k : ℚ))).sum +
        (t.map (fun k : ℕ => (1 : ℚ) / (2 ^ k : ℚ))).sum = ((t.card : ℕ) : ℚ) := by
      intro t
      induction t using Multiset.induction_on with
      | empty => simp
      | @cons a u ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
        linarith
    linarith [hadd s]
  have hdef_q : (s.map (fun k : ℕ => (1 : ℚ) / (2 ^ k : ℚ))).sum = ((s.card : ℕ) : ℚ) - (n : ℚ) := by
    linarith [hs.2, hsum_split]
  have hmul_q : ((s.map (fun k : ℕ => (2 : ℕ) ^ (M - k))).sum : ℚ) =
      ((2 : ℕ) ^ M : ℚ) * (((s.card : ℕ) : ℚ) - (n : ℚ)) := by
    rw [← hdef_q, ← Multiset.sum_map_mul_left]
    have hcast : ∀ t : Multiset ℕ,
        (((t.map (fun k : ℕ => (2 : ℕ) ^ (M - k))).sum : ℕ) : ℚ) =
        (t.map (fun k : ℕ => ((2 : ℚ) ^ (M - k)))).sum := by
      intro t
      induction t using Multiset.induction_on with
      | empty => simp
      | @cons a u ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
        rw [ih]
    rw [hcast s]
    congr 1
    refine Multiset.map_congr rfl fun k hk => ?_
    have hkM : k ≤ M := hMmax k hk
    have hpos : (2 : ℚ) ^ k ≠ 0 := by positivity
    rw [mul_one_div, eq_div_iff hpos, ← pow_add, Nat.sub_add_cancel hkM]
    push_cast; rfl
  have hle_n : n ≤ s.card := by
    have hnonneg : (0 : ℚ) ≤ (s.map (fun k : ℕ => (1 : ℚ) / (2 ^ k : ℚ))).sum := by
      refine Multiset.sum_nonneg fun x hx => ?_
      rcases Multiset.mem_map.mp hx with ⟨k, _, rfl⟩
      positivity
    have : (n : ℚ) ≤ ((s.card : ℕ) : ℚ) := by linarith
    exact_mod_cast this
  have hnat_eq : (s.map (fun k : ℕ => (2 : ℕ) ^ (M - k))).sum = 2 ^ M * (s.card - n) := by
    have hq : (((s.map (fun k : ℕ => (2 : ℕ) ^ (M - k))).sum : ℕ) : ℚ) =
        ((2 ^ M * (s.card - n) : ℕ) : ℚ) := by
      rw [hmul_q, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub hle_n]
    exact_mod_cast hq
  have hmod : (s.map (fun k : ℕ => (2 : ℕ) ^ (M - k))).sum % 2 = s.count M % 2 := by
    clear hnat_eq hmul_q hdef_q hsum_split hle_n hs
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a t ih =>
      have ha : a ≤ M := hMmax a (by simp)
      have ht : ∀ k ∈ t, k ≤ M := fun k hk => hMmax k (Multiset.mem_cons_of_mem hk)
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons]
      by_cases hEq : a = M
      · subst hEq
        simp only [Nat.sub_self, pow_zero, ite_true]
        have := ih ht
        omega
      · have hlt : 1 ≤ M - a := by omega
        have hev : 2 ∣ 2 ^ (M - a) := dvd_pow_self 2 (by omega)
        have hmod0 : 2 ^ (M - a) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hev
        have hne : M ≠ a := fun h => hEq h.symm
        simp only [if_neg hne]
        have := ih ht
        omega
  have hdvd2 : 2 ∣ 2 ^ M * (s.card - n) := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
  have h0 : s.count M % 2 = 0 := by
    rw [← hmod, hnat_eq]
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd2
  exact Nat.dvd_iff_mod_eq_zero.mpr h0

private lemma dyadic_elem_le :
    ∀ n : ℕ, ∀ s : Multiset ℕ, IsDyadicPartition n s → ∀ k ∈ s, k ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hs k hk
    cases n with
    | zero =>
      have hcard := dyadic_card_le 0 s hs
      have h0 : s = 0 := Multiset.card_eq_zero.mp (by omega)
      subst h0; simp at hk
    | succ m =>
      by_cases h1 : k ≤ 1
      · omega
      · have hexM : ∃ M ∈ s, ∀ j ∈ s, j ≤ M := by
          have hfin : s.toFinset.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            have : k ∈ s.toFinset := Multiset.mem_toFinset.mpr hk
            rw [hemp] at this; exact Finset.notMem_empty k this
          refine ⟨s.toFinset.max' hfin, Multiset.mem_toFinset.mp (Finset.max'_mem _ hfin), ?_⟩
          intro j hj
          exact Finset.le_max' _ j (Multiset.mem_toFinset.mpr hj)
        obtain ⟨M, hMs, hMmax⟩ := hexM
        have hkM : k ≤ M := hMmax k hk
        have hM2 : 2 ≤ M := by omega
        have heven : 2 ∣ s.count M := dyadic_max_even_count (m + 1) M s hs (by omega) hMmax
        have hcnt_pos : 1 ≤ s.count M := Multiset.count_pos.mpr hMs
        have hcnt2 : 2 ≤ s.count M := by omega
        have hle_sub : M ::ₘ M ::ₘ (0 : Multiset ℕ) ≤ s := by
          rw [Multiset.le_iff_count]
          intro x
          by_cases hx : x = M
          · subst hx; simp; omega
          · have hne : x ≠ M := hx
            simp [hne]
        let s0 := s - (M ::ₘ M ::ₘ (0 : Multiset ℕ))
        have hs_eq : s = M ::ₘ M ::ₘ s0 := by
          have h := Multiset.sub_add_cancel hle_sub
          calc s = s0 + (M ::ₘ M ::ₘ 0) := h.symm
            _ = M ::ₘ M ::ₘ s0 := by rw [add_comm]; simp [Multiset.cons_add]
        let s' := (M - 1) ::ₘ s0
        have hs'_part : IsDyadicPartition m s' := by
          constructor
          · intro j hj
            simp only [s', Multiset.mem_cons] at hj
            rcases hj with rfl | hj0
            · omega
            · exact hs.1 j (by rw [hs_eq]; simp [hj0])
          · have hsum_s := hs.2
            rw [hs_eq] at hsum_s
            simp only [Multiset.map_cons, Multiset.sum_cons] at hsum_s
            simp only [s', Multiset.map_cons, Multiset.sum_cons]
            have hpow : (2 : ℚ) ^ M = 2 * (2 : ℚ) ^ (M - 1) := by
              rw [← pow_succ', Nat.sub_add_cancel (by omega)]
            have hpos : (2 : ℚ) ^ (M - 1) ≠ 0 := by positivity
            have halg : ((2 ^ (M - 1) - 1 : ℚ) / (2 ^ (M - 1) : ℚ)) =
                2 * ((2 ^ M - 1 : ℚ) / (2 ^ M : ℚ)) - 1 := by
              rw [hpow]; field_simp; ring
            push_cast at hsum_s ⊢
            linarith
        have hM1_le : M - 1 ≤ m := ih m (by omega) s' hs'_part (M - 1) (by simp [s'])
        omega

private lemma finite_dyadicPartition (n : ℕ) :
    Set.Finite { s : Multiset ℕ | IsDyadicPartition n s } := by
  have hsub : { s : Multiset ℕ | IsDyadicPartition n s } ⊆
      (fun l : List ℕ => (l : Multiset ℕ)) ''
        { l : List ℕ | l.length ≤ 2 * n ∧ ∀ k ∈ l, k < n + 1 } := by
    intro s hs
    obtain ⟨l, rfl⟩ := Quotient.exists_rep s
    refine ⟨l, ⟨?_, ?_⟩, rfl⟩
    · exact dyadic_card_le n (l : Multiset ℕ) hs
    · intro k hk
      have hle := dyadic_elem_le n (l : Multiset ℕ) hs k hk
      omega
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.image _ ?_
  have hfin_len : ∀ L : ℕ, Set.Finite { l : List ℕ | l.length ≤ L ∧ ∀ k ∈ l, k < n + 1 } := by
    intro L
    induction L with
    | zero =>
      refine (Set.finite_singleton []).subset fun l hl => ?_
      have h0 : l.length ≤ 0 := hl.1
      exact List.eq_nil_of_length_eq_zero (by omega)
    | succ m ihm =>
      have hu : { l : List ℕ | l.length ≤ m + 1 ∧ ∀ k ∈ l, k < n + 1 } ⊆
          {[]} ∪ ⋃ a ∈ (Finset.range (n + 1) : Set ℕ),
            (List.cons a) '' { t : List ℕ | t.length ≤ m ∧ ∀ k ∈ t, k < n + 1 } := by
        intro l hl
        cases l with
        | nil => exact Or.inl rfl
        | cons a t =>
          right
          simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range, Set.mem_image]
          exact ⟨a, hl.2 a (by simp), t, ⟨by simpa using hl.1, fun k hk => hl.2 k (by simp [hk])⟩, rfl⟩
      refine Set.Finite.subset ((Set.finite_singleton []).union ?_) hu
      exact Set.Finite.biUnion (Finset.finite_toSet _) fun a _ => ihm.image _
  exact hfin_len (2 * n)

private def isSortedDesc : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (b ≤ a) && isSortedDesc (b :: t)

private def scaledSum (l : List ℕ) : ℕ :=
  (l.map (fun k => (2 ^ k - 1) * 2 ^ (11 - k))).sum

private def lexLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: t, b :: u => if a < b then true else if b < a then false else lexLt t u

private def isLexSorted : List (List ℕ) → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => lexLt a b && isLexSorted (b :: t)

private lemma lexLt_irrefl : ∀ l : List ℕ, lexLt l l = false := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [lexLt, lt_irrefl, ite_false]
    exact ih

private lemma lexLt_trans : ∀ l₁ l₂ l₃ : List ℕ,
    lexLt l₁ l₂ = true → lexLt l₂ l₃ = true → lexLt l₁ l₃ = true := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ l₃ h1 h2
    cases l₂ with
    | nil => simp [lexLt] at h1
    | cons _ _ =>
      cases l₃ with
      | nil => simp [lexLt] at h2
      | cons _ _ => rfl
  | cons a t ih =>
    intro l₂ l₃ h1 h2
    cases l₂ with
    | nil => simp [lexLt] at h1
    | cons b u =>
      cases l₃ with
      | nil => simp [lexLt] at h2
      | cons c v =>
        simp only [lexLt] at h1 h2 ⊢
        split_ifs at h1 h2 ⊢ <;> first | rfl | omega | exact ih u v h1 h2

private lemma isLexSorted_append : ∀ A B : List (List ℕ), (hA : A ≠ []) → (hB : B ≠ []) →
    isLexSorted A = true → isLexSorted B = true →
    lexLt (A.getLast hA) (B.head hB) = true →
    isLexSorted (A ++ B) = true := by
  intro A
  induction A with
  | nil => intro _ hA; exact absurd rfl hA
  | cons a t ih =>
    intro B _ hB hAs hBs hbridge
    cases t with
    | nil =>
      cases B with
      | nil => exact absurd rfl hB
      | cons b u =>
        simp only [List.cons_append, List.nil_append, isLexSorted, Bool.and_eq_true]
        exact ⟨by simpa using hbridge, hBs⟩
    | cons c u =>
      simp only [isLexSorted, Bool.and_eq_true] at hAs
      simp only [List.cons_append, isLexSorted, Bool.and_eq_true]
      refine ⟨hAs.1, ih B (List.cons_ne_nil c u) hB hAs.2 hBs ?_⟩
      simpa using hbridge

private lemma nodup_of_isLexSorted : ∀ L : List (List ℕ), isLexSorted L = true → L.Nodup := by
  have hpw : ∀ L : List (List ℕ), isLexSorted L = true → L.Pairwise (fun x y => lexLt x y = true) := by
    intro L
    induction L with
    | nil => intro _; exact List.Pairwise.nil
    | cons a t ih =>
      cases t with
      | nil => intro _; simp
      | cons b u =>
        intro h
        simp only [isLexSorted, Bool.and_eq_true] at h
        have hrec := ih h.2
        rw [List.pairwise_cons] at hrec ⊢
        refine ⟨fun x hx => ?_, List.pairwise_cons.mpr hrec⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hxu
        · exact h.1
        · exact lexLt_trans a b x h.1 (hrec.1 x hxu)
  intro L hL
  refine (hpw L hL).imp fun {x y} hxy hEq => ?_
  subst hEq
  rw [lexLt_irrefl] at hxy
  exact Bool.false_ne_true hxy

private def chunk0 : List (List ℕ) := [
  [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1],
  [2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1],
  [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1],
  [2,2,2,2,2,2,2,2,2,2,2,2,2,2,1],
  [3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1],
  [3,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1],
  [3,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1],
  [3,3,2,2,2,2,2,2,2,2,2,2,2,1,1],
  [3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1],
  [3,3,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1],
  [3,3,3,3,2,2,2,2,2,2,1,1,1,1,1,1],
  [3,3,3,3,2,2,2,2,2,2,2,2,1,1,1],
  [3,3,3,3,2,2,2,2,2,2,2,2,2,2],
  [3,3,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1],
  [3,3,3,3,3,3,2,2,2,1,1,1,1,1,1,1],
  [3,3,3,3,3,3,2,2,2,2,2,1,1,1,1],
  [3,3,3,3,3,3,2,2,2,2,2,2,2,1],
  [3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1],
  [3,3,3,3,3,3,3,3,2,2,1,1,1,1,1],
  [3,3,3,3,3,3,3,3,2,2,2,2,1,1],
  [3,3,3,3,3,3,3,3,3,3,2,1,1,1],
  [3,3,3,3,3,3,3,3,3,3,2,2,2],
  [3,3,3,3,3,3,3,3,3,3,3,3,1],
  [4,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [4,4,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1],
  [4,4,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1],
  [4,4,3,2,2,2,2,2,2,2,1,1,1,1,1,1],
  [4,4,3,2,2,2,2,2,2,2,2,2,1,1,1],
  [4,4,3,2,2,2,2,2,2,2,2,2,2,2],
  [4,4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [4,4,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1]
]

private def chunk1 : List (List ℕ) := [
  [4,4,3,3,3,2,2,2,2,1,1,1,1,1,1,1],
  [4,4,3,3,3,2,2,2,2,2,2,1,1,1,1],
  [4,4,3,3,3,2,2,2,2,2,2,2,2,1],
  [4,4,3,3,3,3,3,2,1,1,1,1,1,1,1,1],
  [4,4,3,3,3,3,3,2,2,2,1,1,1,1,1],
  [4,4,3,3,3,3,3,2,2,2,2,2,1,1],
  [4,4,3,3,3,3,3,3,3,1,1,1,1,1,1],
  [4,4,3,3,3,3,3,3,3,2,2,1,1,1],
  [4,4,3,3,3,3,3,3,3,2,2,2,2],
  [4,4,3,3,3,3,3,3,3,3,3,2,1],
  [4,4,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [4,4,4,4,2,2,2,1,1,1,1,1,1,1,1,1,1],
  [4,4,4,4,2,2,2,2,2,1,1,1,1,1,1,1],
  [4,4,4,4,2,2,2,2,2,2,2,1,1,1,1],
  [4,4,4,4,2,2,2,2,2,2,2,2,2,1],
  [4,4,4,4,3,3,1,1,1,1,1,1,1,1,1,1,1],
  [4,4,4,4,3,3,2,2,1,1,1,1,1,1,1,1],
  [4,4,4,4,3,3,2,2,2,2,1,1,1,1,1],
  [4,4,4,4,3,3,2,2,2,2,2,2,1,1],
  [4,4,4,4,3,3,3,3,2,1,1,1,1,1,1],
  [4,4,4,4,3,3,3,3,2,2,2,1,1,1],
  [4,4,4,4,3,3,3,3,2,2,2,2,2],
  [4,4,4,4,3,3,3,3,3,3,1,1,1,1],
  [4,4,4,4,3,3,3,3,3,3,2,2,1],
  [4,4,4,4,4,4,3,1,1,1,1,1,1,1,1,1],
  [4,4,4,4,4,4,3,2,2,1,1,1,1,1,1],
  [4,4,4,4,4,4,3,2,2,2,2,1,1,1],
  [4,4,4,4,4,4,3,2,2,2,2,2,2],
  [4,4,4,4,4,4,3,3,3,2,1,1,1,1],
  [4,4,4,4,4,4,3,3,3,2,2,2,1],
  [4,4,4,4,4,4,3,3,3,3,3,1,1],
  [4,4,4,4,4,4,4,4,1,1,1,1,1,1,1],
  [4,4,4,4,4,4,4,4,2,2,1,1,1,1],
  [4,4,4,4,4,4,4,4,2,2,2,2,1],
  [4,4,4,4,4,4,4,4,3,3,2,1,1],
  [4,4,4,4,4,4,4,4,3,3,3,3],
  [4,4,4,4,4,4,4,4,4,4,3,2],
  [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1]
]

private def chunk2 : List (List ℕ) := [
  [5,5,4,3,2,2,2,1,1,1,1,1,1,1,1,1,1],
  [5,5,4,3,2,2,2,2,2,1,1,1,1,1,1,1],
  [5,5,4,3,2,2,2,2,2,2,2,1,1,1,1],
  [5,5,4,3,2,2,2,2,2,2,2,2,2,1],
  [5,5,4,3,3,3,1,1,1,1,1,1,1,1,1,1,1],
  [5,5,4,3,3,3,2,2,1,1,1,1,1,1,1,1],
  [5,5,4,3,3,3,2,2,2,2,1,1,1,1,1],
  [5,5,4,3,3,3,2,2,2,2,2,2,1,1],
  [5,5,4,3,3,3,3,3,2,1,1,1,1,1,1],
  [5,5,4,3,3,3,3,3,2,2,2,1,1,1],
  [5,5,4,3,3,3,3,3,2,2,2,2,2],
  [5,5,4,3,3,3,3,3,3,3,1,1,1,1],
  [5,5,4,3,3,3,3,3,3,3,2,2,1],
  [5,5,4,4,4,2,1,1,1,1,1,1,1,1,1,1,1],
  [5,5,4,4,4,2,2,2,1,1,1,1,1,1,1,1],
  [5,5,4,4,4,2,2,2,2,2,1,1,1,1,1],
  [5,5,4,4,4,2,2,2,2,2,2,2,1,1],
  [5,5,4,4,4,3,3,1,1,1,1,1,1,1,1,1],
  [5,5,4,4,4,3,3,2,2,1,1,1,1,1,1],
  [5,5,4,4,4,3,3,2,2,2,2,1,1,1],
  [5,5,4,4,4,3,3,2,2,2,2,2,2],
  [5,5,4,4,4,3,3,3,3,2,1,1,1,1],
  [5,5,4,4,4,3,3,3,3,2,2,2,1],
  [5,5,4,4,4,3,3,3,3,3,3,1,1],
  [5,5,4,4,4,4,4,3,1,1,1,1,1,1,1],
  [5,5,4,4,4,4,4,3,2,2,1,1,1,1],
  [5,5,4,4,4,4,4,3,2,2,2,2,1],
  [5,5,4,4,4,4,4,3,3,3,2,1,1],
  [5,5,4,4,4,4,4,3,3,3,3,3],
  [5,5,4,4,4,4,4,4,4,1,1,1,1,1],
  [5,5,4,4,4,4,4,4,4,2,2,1,1],
  [5,5,4,4,4,4,4,4,4,3,3,2],
  [5,5,5,5,3,2,1,1,1,1,1,1,1,1,1,1,1],
  [5,5,5,5,3,2,2,2,1,1,1,1,1,1,1,1],
  [5,5,5,5,3,2,2,2,2,2,1,1,1,1,1],
  [5,5,5,5,3,2,2,2,2,2,2,2,1,1],
  [5,5,5,5,3,3,3,1,1,1,1,1,1,1,1,1],
  [5,5,5,5,3,3,3,2,2,1,1,1,1,1,1]
]

private def chunk3 : List (List ℕ) := [
  [5,5,5,5,3,3,3,2,2,2,2,1,1,1],
  [5,5,5,5,3,3,3,2,2,2,2,2,2],
  [5,5,5,5,3,3,3,3,3,2,1,1,1,1],
  [5,5,5,5,3,3,3,3,3,2,2,2,1],
  [5,5,5,5,3,3,3,3,3,3,3,1,1],
  [5,5,5,5,4,4,2,1,1,1,1,1,1,1,1,1],
  [5,5,5,5,4,4,2,2,2,1,1,1,1,1,1],
  [5,5,5,5,4,4,2,2,2,2,2,1,1,1],
  [5,5,5,5,4,4,2,2,2,2,2,2,2],
  [5,5,5,5,4,4,3,3,1,1,1,1,1,1,1],
  [5,5,5,5,4,4,3,3,2,2,1,1,1,1],
  [5,5,5,5,4,4,3,3,2,2,2,2,1],
  [5,5,5,5,4,4,3,3,3,3,2,1,1],
  [5,5,5,5,4,4,3,3,3,3,3,3],
  [5,5,5,5,4,4,4,4,3,1,1,1,1,1],
  [5,5,5,5,4,4,4,4,3,2,2,1,1],
  [5,5,5,5,4,4,4,4,3,3,3,2],
  [5,5,5,5,4,4,4,4,4,4,1,1,1],
  [5,5,5,5,4,4,4,4,4,4,2,2],
  [5,5,5,5,5,5,4,2,1,1,1,1,1,1,1],
  [5,5,5,5,5,5,4,2,2,2,1,1,1,1],
  [5,5,5,5,5,5,4,2,2,2,2,2,1],
  [5,5,5,5,5,5,4,3,3,1,1,1,1,1],
  [5,5,5,5,5,5,4,3,3,2,2,1,1],
  [5,5,5,5,5,5,4,3,3,3,3,2],
  [5,5,5,5,5,5,4,4,4,3,1,1,1],
  [5,5,5,5,5,5,4,4,4,3,2,2],
  [5,5,5,5,5,5,4,4,4,4,4,1],
  [5,5,5,5,5,5,5,5,2,1,1,1,1,1],
  [5,5,5,5,5,5,5,5,2,2,2,1,1],
  [5,5,5,5,5,5,5,5,3,3,1,1,1],
  [5,5,5,5,5,5,5,5,3,3,2,2],
  [5,5,5,5,5,5,5,5,4,4,3,1],
  [6,6,5,4,3,2,1,1,1,1,1,1,1,1,1,1,1],
  [6,6,5,4,3,2,2,2,1,1,1,1,1,1,1,1],
  [6,6,5,4,3,2,2,2,2,2,1,1,1,1,1],
  [6,6,5,4,3,2,2,2,2,2,2,2,1,1],
  [6,6,5,4,3,3,3,1,1,1,1,1,1,1,1,1]
]

private def chunk4 : List (List ℕ) := [
  [6,6,5,4,3,3,3,2,2,1,1,1,1,1,1],
  [6,6,5,4,3,3,3,2,2,2,2,1,1,1],
  [6,6,5,4,3,3,3,2,2,2,2,2,2],
  [6,6,5,4,3,3,3,3,3,2,1,1,1,1],
  [6,6,5,4,3,3,3,3,3,2,2,2,1],
  [6,6,5,4,3,3,3,3,3,3,3,1,1],
  [6,6,5,4,4,4,2,1,1,1,1,1,1,1,1,1],
  [6,6,5,4,4,4,2,2,2,1,1,1,1,1,1],
  [6,6,5,4,4,4,2,2,2,2,2,1,1,1],
  [6,6,5,4,4,4,2,2,2,2,2,2,2],
  [6,6,5,4,4,4,3,3,1,1,1,1,1,1,1],
  [6,6,5,4,4,4,3,3,2,2,1,1,1,1],
  [6,6,5,4,4,4,3,3,2,2,2,2,1],
  [6,6,5,4,4,4,3,3,3,3,2,1,1],
  [6,6,5,4,4,4,3,3,3,3,3,3],
  [6,6,5,4,4,4,4,4,3,1,1,1,1,1],
  [6,6,5,4,4,4,4,4,3,2,2,1,1],
  [6,6,5,4,4,4,4,4,3,3,3,2],
  [6,6,5,4,4,4,4,4,4,4,1,1,1],
  [6,6,5,4,4,4,4,4,4,4,2,2],
  [6,6,5,5,5,3,2,1,1,1,1,1,1,1,1,1],
  [6,6,5,5,5,3,2,2,2,1,1,1,1,1,1],
  [6,6,5,5,5,3,2,2,2,2,2,1,1,1],
  [6,6,5,5,5,3,2,2,2,2,2,2,2],
  [6,6,5,5,5,3,3,3,1,1,1,1,1,1,1],
  [6,6,5,5,5,3,3,3,2,2,1,1,1,1],
  [6,6,5,5,5,3,3,3,2,2,2,2,1],
  [6,6,5,5,5,3,3,3,3,3,2,1,1],
  [6,6,5,5,5,3,3,3,3,3,3,3],
  [6,6,5,5,5,4,4,2,1,1,1,1,1,1,1],
  [6,6,5,5,5,4,4,2,2,2,1,1,1,1],
  [6,6,5,5,5,4,4,2,2,2,2,2,1],
  [6,6,5,5,5,4,4,3,3,1,1,1,1,1],
  [6,6,5,5,5,4,4,3,3,2,2,1,1],
  [6,6,5,5,5,4,4,3,3,3,3,2],
  [6,6,5,5,5,4,4,4,4,3,1,1,1],
  [6,6,5,5,5,4,4,4,4,3,2,2],
  [6,6,5,5,5,4,4,4,4,4,4,1]
]

private def chunk5 : List (List ℕ) := [
  [6,6,5,5,5,5,5,4,2,1,1,1,1,1],
  [6,6,5,5,5,5,5,4,2,2,2,1,1],
  [6,6,5,5,5,5,5,4,3,3,1,1,1],
  [6,6,5,5,5,5,5,4,3,3,2,2],
  [6,6,5,5,5,5,5,4,4,4,3,1],
  [6,6,5,5,5,5,5,5,5,2,1,1,1],
  [6,6,5,5,5,5,5,5,5,2,2,2],
  [6,6,5,5,5,5,5,5,5,3,3,1],
  [6,6,6,6,4,3,2,1,1,1,1,1,1,1,1,1],
  [6,6,6,6,4,3,2,2,2,1,1,1,1,1,1],
  [6,6,6,6,4,3,2,2,2,2,2,1,1,1],
  [6,6,6,6,4,3,2,2,2,2,2,2,2],
  [6,6,6,6,4,3,3,3,1,1,1,1,1,1,1],
  [6,6,6,6,4,3,3,3,2,2,1,1,1,1],
  [6,6,6,6,4,3,3,3,2,2,2,2,1],
  [6,6,6,6,4,3,3,3,3,3,2,1,1],
  [6,6,6,6,4,3,3,3,3,3,3,3],
  [6,6,6,6,4,4,4,2,1,1,1,1,1,1,1],
  [6,6,6,6,4,4,4,2,2,2,1,1,1,1],
  [6,6,6,6,4,4,4,2,2,2,2,2,1],
  [6,6,6,6,4,4,4,3,3,1,1,1,1,1],
  [6,6,6,6,4,4,4,3,3,2,2,1,1],
  [6,6,6,6,4,4,4,3,3,3,3,2],
  [6,6,6,6,4,4,4,4,4,3,1,1,1],
  [6,6,6,6,4,4,4,4,4,3,2,2],
  [6,6,6,6,4,4,4,4,4,4,4,1],
  [6,6,6,6,5,5,3,2,1,1,1,1,1,1,1],
  [6,6,6,6,5,5,3,2,2,2,1,1,1,1],
  [6,6,6,6,5,5,3,2,2,2,2,2,1],
  [6,6,6,6,5,5,3,3,3,1,1,1,1,1],
  [6,6,6,6,5,5,3,3,3,2,2,1,1],
  [6,6,6,6,5,5,3,3,3,3,3,2],
  [6,6,6,6,5,5,4,4,2,1,1,1,1,1],
  [6,6,6,6,5,5,4,4,2,2,2,1,1],
  [6,6,6,6,5,5,4,4,3,3,1,1,1],
  [6,6,6,6,5,5,4,4,3,3,2,2],
  [6,6,6,6,5,5,4,4,4,4,3,1],
  [6,6,6,6,5,5,5,5,4,2,1,1,1]
]

private def chunk6 : List (List ℕ) := [
  [6,6,6,6,5,5,5,5,4,2,2,2],
  [6,6,6,6,5,5,5,5,4,3,3,1],
  [6,6,6,6,5,5,5,5,5,5,2,1],
  [6,6,6,6,6,6,5,3,2,1,1,1,1,1],
  [6,6,6,6,6,6,5,3,2,2,2,1,1],
  [6,6,6,6,6,6,5,3,3,3,1,1,1],
  [6,6,6,6,6,6,5,3,3,3,2,2],
  [6,6,6,6,6,6,5,4,4,2,1,1,1],
  [6,6,6,6,6,6,5,4,4,2,2,2],
  [6,6,6,6,6,6,5,4,4,3,3,1],
  [6,6,6,6,6,6,5,5,5,4,2,1],
  [6,6,6,6,6,6,6,6,3,2,1,1,1],
  [6,6,6,6,6,6,6,6,3,2,2,2],
  [6,6,6,6,6,6,6,6,3,3,3,1],
  [6,6,6,6,6,6,6,6,4,4,2,1],
  [7,7,6,5,4,3,2,1,1,1,1,1,1,1,1,1],
  [7,7,6,5,4,3,2,2,2,1,1,1,1,1,1],
  [7,7,6,5,4,3,2,2,2,2,2,1,1,1],
  [7,7,6,5,4,3,2,2,2,2,2,2,2],
  [7,7,6,5,4,3,3,3,1,1,1,1,1,1,1],
  [7,7,6,5,4,3,3,3,2,2,1,1,1,1],
  [7,7,6,5,4,3,3,3,2,2,2,2,1],
  [7,7,6,5,4,3,3,3,3,3,2,1,1],
  [7,7,6,5,4,3,3,3,3,3,3,3],
  [7,7,6,5,4,4,4,2,1,1,1,1,1,1,1],
  [7,7,6,5,4,4,4,2,2,2,1,1,1,1],
  [7,7,6,5,4,4,4,2,2,2,2,2,1],
  [7,7,6,5,4,4,4,3,3,1,1,1,1,1],
  [7,7,6,5,4,4,4,3,3,2,2,1,1],
  [7,7,6,5,4,4,4,3,3,3,3,2],
  [7,7,6,5,4,4,4,4,4,3,1,1,1],
  [7,7,6,5,4,4,4,4,4,3,2,2],
  [7,7,6,5,4,4,4,4,4,4,4,1],
  [7,7,6,5,5,5,3,2,1,1,1,1,1,1,1],
  [7,7,6,5,5,5,3,2,2,2,1,1,1,1],
  [7,7,6,5,5,5,3,2,2,2,2,2,1],
  [7,7,6,5,5,5,3,3,3,1,1,1,1,1],
  [7,7,6,5,5,5,3,3,3,2,2,1,1]
]

private def chunk7 : List (List ℕ) := [
  [7,7,6,5,5,5,3,3,3,3,3,2],
  [7,7,6,5,5,5,4,4,2,1,1,1,1,1],
  [7,7,6,5,5,5,4,4,2,2,2,1,1],
  [7,7,6,5,5,5,4,4,3,3,1,1,1],
  [7,7,6,5,5,5,4,4,3,3,2,2],
  [7,7,6,5,5,5,4,4,4,4,3,1],
  [7,7,6,5,5,5,5,5,4,2,1,1,1],
  [7,7,6,5,5,5,5,5,4,2,2,2],
  [7,7,6,5,5,5,5,5,4,3,3,1],
  [7,7,6,5,5,5,5,5,5,5,2,1],
  [7,7,6,6,6,4,3,2,1,1,1,1,1,1,1],
  [7,7,6,6,6,4,3,2,2,2,1,1,1,1],
  [7,7,6,6,6,4,3,2,2,2,2,2,1],
  [7,7,6,6,6,4,3,3,3,1,1,1,1,1],
  [7,7,6,6,6,4,3,3,3,2,2,1,1],
  [7,7,6,6,6,4,3,3,3,3,3,2],
  [7,7,6,6,6,4,4,4,2,1,1,1,1,1],
  [7,7,6,6,6,4,4,4,2,2,2,1,1],
  [7,7,6,6,6,4,4,4,3,3,1,1,1],
  [7,7,6,6,6,4,4,4,3,3,2,2],
  [7,7,6,6,6,4,4,4,4,4,3,1],
  [7,7,6,6,6,5,5,3,2,1,1,1,1,1],
  [7,7,6,6,6,5,5,3,2,2,2,1,1],
  [7,7,6,6,6,5,5,3,3,3,1,1,1],
  [7,7,6,6,6,5,5,3,3,3,2,2],
  [7,7,6,6,6,5,5,4,4,2,1,1,1],
  [7,7,6,6,6,5,5,4,4,2,2,2],
  [7,7,6,6,6,5,5,4,4,3,3,1],
  [7,7,6,6,6,5,5,5,5,4,2,1],
  [7,7,6,6,6,6,6,5,3,2,1,1,1],
  [7,7,6,6,6,6,6,5,3,2,2,2],
  [7,7,6,6,6,6,6,5,3,3,3,1],
  [7,7,6,6,6,6,6,5,4,4,2,1],
  [7,7,6,6,6,6,6,6,6,3,2,1],
  [7,7,7,7,5,4,3,2,1,1,1,1,1,1,1],
  [7,7,7,7,5,4,3,2,2,2,1,1,1,1],
  [7,7,7,7,5,4,3,2,2,2,2,2,1],
  [7,7,7,7,5,4,3,3,3,1,1,1,1,1]
]

private def chunk8 : List (List ℕ) := [
  [7,7,7,7,5,4,3,3,3,2,2,1,1],
  [7,7,7,7,5,4,3,3,3,3,3,2],
  [7,7,7,7,5,4,4,4,2,1,1,1,1,1],
  [7,7,7,7,5,4,4,4,2,2,2,1,1],
  [7,7,7,7,5,4,4,4,3,3,1,1,1],
  [7,7,7,7,5,4,4,4,3,3,2,2],
  [7,7,7,7,5,4,4,4,4,4,3,1],
  [7,7,7,7,5,5,5,3,2,1,1,1,1,1],
  [7,7,7,7,5,5,5,3,2,2,2,1,1],
  [7,7,7,7,5,5,5,3,3,3,1,1,1],
  [7,7,7,7,5,5,5,3,3,3,2,2],
  [7,7,7,7,5,5,5,4,4,2,1,1,1],
  [7,7,7,7,5,5,5,4,4,2,2,2],
  [7,7,7,7,5,5,5,4,4,3,3,1],
  [7,7,7,7,5,5,5,5,5,4,2,1],
  [7,7,7,7,6,6,4,3,2,1,1,1,1,1],
  [7,7,7,7,6,6,4,3,2,2,2,1,1],
  [7,7,7,7,6,6,4,3,3,3,1,1,1],
  [7,7,7,7,6,6,4,3,3,3,2,2],
  [7,7,7,7,6,6,4,4,4,2,1,1,1],
  [7,7,7,7,6,6,4,4,4,2,2,2],
  [7,7,7,7,6,6,4,4,4,3,3,1],
  [7,7,7,7,6,6,5,5,3,2,1,1,1],
  [7,7,7,7,6,6,5,5,3,2,2,2],
  [7,7,7,7,6,6,5,5,3,3,3,1],
  [7,7,7,7,6,6,5,5,4,4,2,1],
  [7,7,7,7,6,6,6,6,5,3,2,1],
  [7,7,7,7,7,7,6,4,3,2,1,1,1],
  [7,7,7,7,7,7,6,4,3,2,2,2],
  [7,7,7,7,7,7,6,4,3,3,3,1],
  [7,7,7,7,7,7,6,4,4,4,2,1],
  [7,7,7,7,7,7,6,5,5,3,2,1],
  [7,7,7,7,7,7,7,7,4,3,2,1],
  [8,8,7,6,5,4,3,2,1,1,1,1,1,1,1],
  [8,8,7,6,5,4,3,2,2,2,1,1,1,1],
  [8,8,7,6,5,4,3,2,2,2,2,2,1],
  [8,8,7,6,5,4,3,3,3,1,1,1,1,1],
  [8,8,7,6,5,4,3,3,3,2,2,1,1]
]

private def chunk9 : List (List ℕ) := [
  [8,8,7,6,5,4,3,3,3,3,3,2],
  [8,8,7,6,5,4,4,4,2,1,1,1,1,1],
  [8,8,7,6,5,4,4,4,2,2,2,1,1],
  [8,8,7,6,5,4,4,4,3,3,1,1,1],
  [8,8,7,6,5,4,4,4,3,3,2,2],
  [8,8,7,6,5,4,4,4,4,4,3,1],
  [8,8,7,6,5,5,5,3,2,1,1,1,1,1],
  [8,8,7,6,5,5,5,3,2,2,2,1,1],
  [8,8,7,6,5,5,5,3,3,3,1,1,1],
  [8,8,7,6,5,5,5,3,3,3,2,2],
  [8,8,7,6,5,5,5,4,4,2,1,1,1],
  [8,8,7,6,5,5,5,4,4,2,2,2],
  [8,8,7,6,5,5,5,4,4,3,3,1],
  [8,8,7,6,5,5,5,5,5,4,2,1],
  [8,8,7,6,6,6,4,3,2,1,1,1,1,1],
  [8,8,7,6,6,6,4,3,2,2,2,1,1],
  [8,8,7,6,6,6,4,3,3,3,1,1,1],
  [8,8,7,6,6,6,4,3,3,3,2,2],
  [8,8,7,6,6,6,4,4,4,2,1,1,1],
  [8,8,7,6,6,6,4,4,4,2,2,2],
  [8,8,7,6,6,6,4,4,4,3,3,1],
  [8,8,7,6,6,6,5,5,3,2,1,1,1],
  [8,8,7,6,6,6,5,5,3,2,2,2],
  [8,8,7,6,6,6,5,5,3,3,3,1],
  [8,8,7,6,6,6,5,5,4,4,2,1],
  [8,8,7,6,6,6,6,6,5,3,2,1],
  [8,8,7,7,7,5,4,3,2,1,1,1,1,1],
  [8,8,7,7,7,5,4,3,2,2,2,1,1],
  [8,8,7,7,7,5,4,3,3,3,1,1,1],
  [8,8,7,7,7,5,4,3,3,3,2,2],
  [8,8,7,7,7,5,4,4,4,2,1,1,1],
  [8,8,7,7,7,5,4,4,4,2,2,2],
  [8,8,7,7,7,5,4,4,4,3,3,1],
  [8,8,7,7,7,5,5,5,3,2,1,1,1],
  [8,8,7,7,7,5,5,5,3,2,2,2],
  [8,8,7,7,7,5,5,5,3,3,3,1],
  [8,8,7,7,7,5,5,5,4,4,2,1],
  [8,8,7,7,7,6,6,4,3,2,1,1,1]
]

private def chunk10 : List (List ℕ) := [
  [8,8,7,7,7,6,6,4,3,2,2,2],
  [8,8,7,7,7,6,6,4,3,3,3,1],
  [8,8,7,7,7,6,6,4,4,4,2,1],
  [8,8,7,7,7,6,6,5,5,3,2,1],
  [8,8,7,7,7,7,7,6,4,3,2,1],
  [8,8,8,8,6,5,4,3,2,1,1,1,1,1],
  [8,8,8,8,6,5,4,3,2,2,2,1,1],
  [8,8,8,8,6,5,4,3,3,3,1,1,1],
  [8,8,8,8,6,5,4,3,3,3,2,2],
  [8,8,8,8,6,5,4,4,4,2,1,1,1],
  [8,8,8,8,6,5,4,4,4,2,2,2],
  [8,8,8,8,6,5,4,4,4,3,3,1],
  [8,8,8,8,6,5,5,5,3,2,1,1,1],
  [8,8,8,8,6,5,5,5,3,2,2,2],
  [8,8,8,8,6,5,5,5,3,3,3,1],
  [8,8,8,8,6,5,5,5,4,4,2,1],
  [8,8,8,8,6,6,6,4,3,2,1,1,1],
  [8,8,8,8,6,6,6,4,3,2,2,2],
  [8,8,8,8,6,6,6,4,3,3,3,1],
  [8,8,8,8,6,6,6,4,4,4,2,1],
  [8,8,8,8,6,6,6,5,5,3,2,1],
  [8,8,8,8,7,7,5,4,3,2,1,1,1],
  [8,8,8,8,7,7,5,4,3,2,2,2],
  [8,8,8,8,7,7,5,4,3,3,3,1],
  [8,8,8,8,7,7,5,4,4,4,2,1],
  [8,8,8,8,7,7,5,5,5,3,2,1],
  [8,8,8,8,7,7,6,6,4,3,2,1],
  [8,8,8,8,8,8,7,5,4,3,2,1],
  [9,9,8,7,6,5,4,3,2,1,1,1,1,1],
  [9,9,8,7,6,5,4,3,2,2,2,1,1],
  [9,9,8,7,6,5,4,3,3,3,1,1,1],
  [9,9,8,7,6,5,4,3,3,3,2,2],
  [9,9,8,7,6,5,4,4,4,2,1,1,1],
  [9,9,8,7,6,5,4,4,4,2,2,2],
  [9,9,8,7,6,5,4,4,4,3,3,1],
  [9,9,8,7,6,5,5,5,3,2,1,1,1],
  [9,9,8,7,6,5,5,5,3,2,2,2],
  [9,9,8,7,6,5,5,5,3,3,3,1]
]

private def chunk11 : List (List ℕ) := [
  [9,9,8,7,6,5,5,5,4,4,2,1],
  [9,9,8,7,6,6,6,4,3,2,1,1,1],
  [9,9,8,7,6,6,6,4,3,2,2,2],
  [9,9,8,7,6,6,6,4,3,3,3,1],
  [9,9,8,7,6,6,6,4,4,4,2,1],
  [9,9,8,7,6,6,6,5,5,3,2,1],
  [9,9,8,7,7,7,5,4,3,2,1,1,1],
  [9,9,8,7,7,7,5,4,3,2,2,2],
  [9,9,8,7,7,7,5,4,3,3,3,1],
  [9,9,8,7,7,7,5,4,4,4,2,1],
  [9,9,8,7,7,7,5,5,5,3,2,1],
  [9,9,8,7,7,7,6,6,4,3,2,1],
  [9,9,8,8,8,6,5,4,3,2,1,1,1],
  [9,9,8,8,8,6,5,4,3,2,2,2],
  [9,9,8,8,8,6,5,4,3,3,3,1],
  [9,9,8,8,8,6,5,4,4,4,2,1],
  [9,9,8,8,8,6,5,5,5,3,2,1],
  [9,9,8,8,8,6,6,6,4,3,2,1],
  [9,9,8,8,8,7,7,5,4,3,2,1],
  [9,9,9,9,7,6,5,4,3,2,1,1,1],
  [9,9,9,9,7,6,5,4,3,2,2,2],
  [9,9,9,9,7,6,5,4,3,3,3,1],
  [9,9,9,9,7,6,5,4,4,4,2,1],
  [9,9,9,9,7,6,5,5,5,3,2,1],
  [9,9,9,9,7,6,6,6,4,3,2,1],
  [9,9,9,9,7,7,7,5,4,3,2,1],
  [9,9,9,9,8,8,6,5,4,3,2,1],
  [10,10,9,8,7,6,5,4,3,2,1,1,1],
  [10,10,9,8,7,6,5,4,3,2,2,2],
  [10,10,9,8,7,6,5,4,3,3,3,1],
  [10,10,9,8,7,6,5,4,4,4,2,1],
  [10,10,9,8,7,6,5,5,5,3,2,1],
  [10,10,9,8,7,6,6,6,4,3,2,1],
  [10,10,9,8,7,7,7,5,4,3,2,1],
  [10,10,9,8,8,8,6,5,4,3,2,1],
  [10,10,9,9,9,7,6,5,4,3,2,1],
  [10,10,10,10,8,7,6,5,4,3,2,1],
  [11,11,10,9,8,7,6,5,4,3,2,1]
]

private def allChunks : List (List (List ℕ)) :=
  [chunk0, chunk1, chunk2, chunk3, chunk4, chunk5, chunk6, chunk7, chunk8, chunk9, chunk10, chunk11]

private def parts11 : List (List ℕ) := allChunks.flatten

private lemma chunk0_ok :
    chunk0.length = 38 ∧
    isLexSorted chunk0 = true ∧
    chunk0.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk1_ok :
    chunk1.length = 38 ∧
    isLexSorted chunk1 = true ∧
    chunk1.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk2_ok :
    chunk2.length = 38 ∧
    isLexSorted chunk2 = true ∧
    chunk2.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk3_ok :
    chunk3.length = 38 ∧
    isLexSorted chunk3 = true ∧
    chunk3.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk4_ok :
    chunk4.length = 38 ∧
    isLexSorted chunk4 = true ∧
    chunk4.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk5_ok :
    chunk5.length = 38 ∧
    isLexSorted chunk5 = true ∧
    chunk5.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk6_ok :
    chunk6.length = 38 ∧
    isLexSorted chunk6 = true ∧
    chunk6.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk7_ok :
    chunk7.length = 38 ∧
    isLexSorted chunk7 = true ∧
    chunk7.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk8_ok :
    chunk8.length = 38 ∧
    isLexSorted chunk8 = true ∧
    chunk8.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk9_ok :
    chunk9.length = 38 ∧
    isLexSorted chunk9 = true ∧
    chunk9.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk10_ok :
    chunk10.length = 38 ∧
    isLexSorted chunk10 = true ∧
    chunk10.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma chunk11_ok :
    chunk11.length = 38 ∧
    isLexSorted chunk11 = true ∧
    chunk11.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  decide

private lemma bridges_ok :
  lexLt (chunk0.getLast (by decide)) (chunk1.head (by decide)) = true ∧
  lexLt (chunk1.getLast (by decide)) (chunk2.head (by decide)) = true ∧
  lexLt (chunk2.getLast (by decide)) (chunk3.head (by decide)) = true ∧
  lexLt (chunk3.getLast (by decide)) (chunk4.head (by decide)) = true ∧
  lexLt (chunk4.getLast (by decide)) (chunk5.head (by decide)) = true ∧
  lexLt (chunk5.getLast (by decide)) (chunk6.head (by decide)) = true ∧
  lexLt (chunk6.getLast (by decide)) (chunk7.head (by decide)) = true ∧
  lexLt (chunk7.getLast (by decide)) (chunk8.head (by decide)) = true ∧
  lexLt (chunk8.getLast (by decide)) (chunk9.head (by decide)) = true ∧
  lexLt (chunk9.getLast (by decide)) (chunk10.head (by decide)) = true ∧
  lexLt (chunk10.getLast (by decide)) (chunk11.head (by decide)) = true := by
  decide

private lemma parts11_check :
    parts11.length = 456 ∧
    isLexSorted parts11 = true ∧
    parts11.all (fun l =>
      isSortedDesc l &&
      l.all (fun k => decide (1 ≤ k ∧ k ≤ 11)) &&
      decide (scaledSum l = 11 * 2 ^ 11)) = true := by
  have hfl : parts11 = chunk0 ++ (chunk1 ++ (chunk2 ++ (chunk3 ++ (chunk4 ++ (chunk5 ++
      (chunk6 ++ (chunk7 ++ (chunk8 ++ (chunk9 ++ (chunk10 ++ chunk11)))))))))) := by
    simp [parts11, allChunks]
  rw [hfl]
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_append, chunk0_ok.1, chunk1_ok.1, chunk2_ok.1, chunk3_ok.1,
      chunk4_ok.1, chunk5_ok.1, chunk6_ok.1, chunk7_ok.1, chunk8_ok.1, chunk9_ok.1,
      chunk10_ok.1, chunk11_ok.1]
  · obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := bridges_ok
    have h10 : isLexSorted (chunk10 ++ chunk11) = true :=
      isLexSorted_append chunk10 chunk11 (by decide) (by decide) chunk10_ok.2.1 chunk11_ok.2.1 b10
    have h9 : isLexSorted (chunk9 ++ (chunk10 ++ chunk11)) = true :=
      isLexSorted_append chunk9 _ (by decide) (List.append_ne_nil_of_left_ne_nil (by decide) _) chunk9_ok.2.1 h10
        (by simpa [List.head_append_of_ne_nil (by decide : chunk10 ≠ [])] using b9)
    have h8 : isLexSorted (chunk8 ++ (chunk9 ++ (chunk10 ++ chunk11))) = true :=
      isLexSorted_append chunk8 _ (by decide) (List.append_ne_nil_of_left_ne_nil (by decide) _) chunk8_ok.2.1 h9
        (by simpa [List.head_append_of_ne_nil (by decide : chunk9 ≠ [])] using b8)
    have h7 : isLexSorted (chunk7 ++ (chunk8 ++ (chunk9 ++ (chunk10 ++ chunk11)))) = true :=
      isLexSorted_append chunk7 _ (by decide) (List.append_ne_nil_of_left_ne_nil (by decide) _) chunk7_ok.2.1 h8
        (by simpa [List.head_append_of_ne_nil (by decide : chunk8 ≠ [])] using b7)
    have h6 : isLexSorted (chunk6 ++ (chunk7 ++ (chunk8 ++ (chunk9 ++ (chunk10 ++ chunk11))))) = true :=
      isLexSorted_append chunk6 _ (by decide) (List.append_ne_nil_of_left_ne_nil (by decide) _) chunk6_ok.2.1 h7
        (by simpa [List.head_append_of_ne_nil (by decide : chunk7 ≠ [])] using b6)
    have h5 : isLexSorted (chunk5 ++ (chunk6 ++ (chunk7 ++ (chunk8 ++ (chunk9 ++ (chunk10 ++ chunk11)))))) = true :=
      isLexSorted_append chunk5 _ (by decide) (List.append_ne_nil_of_left_ne_nil (by decide) _) chunk5_ok.2.1 h6
        (by simpa [List.head_append_of_ne_nil (by decide : chunk6 ≠ [])] using b5)
    have h4 : isLexSorted (chunk4 ++ (chunk5 ++ (chunk6 ++ (chunk7 ++ (chunk8 ++ (chunk9 ++ (chunk10 ++ chunk11))))))) = true :=
      isLexSorted_append chunk4 _ (by decide) (List.append_ne_nil_of_left_ne_nil (by decide) _) chunk4_ok.2.1 h5
        (by simpa [List.head_append_of_ne_nil (by decide : chunk5 ≠ [])] using b4)
    have h3 : isLexSorted (chunk3 ++ (chunk4 ++ (chunk5 ++ (chunk6 ++ (chunk7 ++ (chunk8 ++ (chunk9 ++ (chunk10 ++ chunk11)))))))) = true :=
      isLexSorted_append chunk3 _ (by decide) (List.append_ne_nil_of_left_ne_nil (by decide) _) chunk3_ok.2.1 h4
        (by simpa [List.head_append_of_ne_nil (by decide : chunk4 ≠ [])] using b3)
    have h2 : isLexSorted (chunk2 ++ (chunk3 ++ (chunk4 ++ (chunk5 ++ (chunk6 ++ (chunk7 ++ (chunk8 ++ (chunk9 ++ (chunk10 ++ chunk11))))))))) = true :=
      isLexSorted_append chunk2 _ (by decide) (List.append_ne_nil_of_left_ne_nil (by decide) _) chunk2_ok.2.1 h3
        (by simpa [List.head_append_of_ne_nil (by decide : chunk3 ≠ [])] using b2)
    have h1 : isLexSorted (chunk1 ++ (chunk2 ++ (chunk3 ++ (chunk4 ++ (chunk5 ++ (chunk6 ++ (chunk7 ++ (chunk8 ++ (chunk9 ++ (chunk10 ++ chunk11)))))))))) = true :=
      isLexSorted_append chunk1 _ (by decide) (List.append_ne_nil_of_left_ne_nil (by decide) _) chunk1_ok.2.1 h2
        (by simpa [List.head_append_of_ne_nil (by decide : chunk2 ≠ [])] using b1)
    exact isLexSorted_append chunk0 _ (by decide) (List.append_ne_nil_of_left_ne_nil (by decide) _) chunk0_ok.2.1 h1
      (by simpa [List.head_append_of_ne_nil (by decide : chunk1 ≠ [])] using b0)
  · simp only [List.all_append, chunk0_ok.2.2, chunk1_ok.2.2, chunk2_ok.2.2, chunk3_ok.2.2,
      chunk4_ok.2.2, chunk5_ok.2.2, chunk6_ok.2.2, chunk7_ok.2.2, chunk8_ok.2.2, chunk9_ok.2.2,
      chunk10_ok.2.2, chunk11_ok.2.2, Bool.and_self]

private lemma isSortedDesc_head_ge : ∀ a : ℕ, ∀ t : List ℕ,
    isSortedDesc (a :: t) = true → ∀ x ∈ t, x ≤ a := by
  intro a t
  induction t generalizing a with
  | nil => intro _ _ hx; simp at hx
  | cons b u ih =>
    intro h x hx
    simp only [isSortedDesc, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxu
    · exact h.1
    · exact le_trans (ih b h.2 x hxu) h.1

private lemma isSortedDesc_tail : ∀ a : ℕ, ∀ t : List ℕ,
    isSortedDesc (a :: t) = true → isSortedDesc t = true := by
  intro a t h
  cases t with
  | nil => rfl
  | cons b u =>
    simp only [isSortedDesc, Bool.and_eq_true] at h
    exact h.2

private lemma sortedDesc_eq_of_perm :
    ∀ l₁ l₂ : List ℕ, isSortedDesc l₁ = true → isSortedDesc l₂ = true →
      (l₁ : Multiset ℕ) = (l₂ : Multiset ℕ) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ _ hperm
    cases l₂ with
    | nil => rfl
    | cons b u => exfalso; have := congrArg Multiset.card hperm; simp at this
  | cons a t ih =>
    intro l₂ h1 h2 hperm
    cases l₂ with
    | nil => simp at hperm
    | cons b u =>
      have hab : a = b := by
        have ha_mem : a ∈ b :: u := by
          have : a ∈ ((b :: u : List ℕ) : Multiset ℕ) := by rw [← hperm]; simp
          exact Multiset.mem_coe.mp this
        have hb_mem : b ∈ a :: t := by
          have : b ∈ ((a :: t : List ℕ) : Multiset ℕ) := by rw [hperm]; simp
          exact Multiset.mem_coe.mp this
        have hle1 : a ≤ b := by
          rcases List.mem_cons.mp ha_mem with rfl | hau
          · exact le_rfl
          · exact isSortedDesc_head_ge b u h2 a hau
        have hle2 : b ≤ a := by
          rcases List.mem_cons.mp hb_mem with rfl | hbt
          · exact le_rfl
          · exact isSortedDesc_head_ge a t h1 b hbt
        omega
      subst hab
      congr 1
      have hperm' : (t : Multiset ℕ) = (u : Multiset ℕ) := by
        simpa using hperm
      exact ih u (isSortedDesc_tail a t h1) (isSortedDesc_tail a u h2) hperm'

private lemma mem_parts11_valid (l : List ℕ) (hl : l ∈ parts11) :
    IsDyadicPartition 11 (l : Multiset ℕ) := by
  have hall := (List.all_eq_true.mp parts11_check.2.2) l hl
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hall
  rcases hall with ⟨⟨_, hbounds⟩, hsum⟩
  constructor
  · intro k hk
    have hkl : k ∈ l := hk
    exact (hbounds k hkl).1
  · have hlist : ∀ t : List ℕ, (∀ k ∈ t, 1 ≤ k ∧ k ≤ 11) →
        ((t.map (fun k : ℕ => ((2 ^ k - 1 : ℚ) / (2 ^ k : ℚ)))).sum) * (2 : ℚ) ^ 11 =
          ((scaledSum t : ℕ) : ℚ) := by
      intro t ht
      induction t with
      | nil => simp [scaledSum]
      | cons a u ih =>
        have ha := ht a (by simp)
        have hu := ih (fun k hk => ht k (by simp [hk]))
        simp only [List.map_cons, List.sum_cons, add_mul, scaledSum, Nat.cast_add]
        rw [hu]
        congr 1
        have hpos : (2 : ℚ) ^ a ≠ 0 := by positivity
        have hpow : (2 : ℚ) ^ 11 = (2 : ℚ) ^ a * (2 : ℚ) ^ (11 - a) := by
          rw [← pow_add, Nat.add_sub_of_le ha.2]
        have h2a : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by omega)
        rw [hpow, div_mul_eq_mul_div, mul_comm ((2 : ℚ) ^ a), ← mul_assoc,
            mul_div_cancel_right₀ _ hpos, Nat.cast_mul, Nat.cast_sub h2a, Nat.cast_pow,
            Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
    have hq : ((l.map (fun k : ℕ => ((2 ^ k - 1 : ℚ) / (2 ^ k : ℚ)))).sum) * (2 : ℚ) ^ 11 =
        (11 : ℚ) * (2 : ℚ) ^ 11 := by
      rw [hlist l hbounds, hsum]
      norm_num
    have hpos : (2 : ℚ) ^ 11 ≠ 0 := by positivity
    have hq_val : (l.map (fun k : ℕ => ((2 ^ k - 1 : ℚ) / (2 ^ k : ℚ)))).sum = (11 : ℚ) :=
      mul_right_cancel₀ hpos hq
    simpa using hq_val

private lemma A002843_11_ge : 456 ≤ A002843 11 := by
  let S : Finset (Multiset ℕ) := (parts11.toFinset).image (fun l : List ℕ => (l : Multiset ℕ))
  have hnodup : parts11.Nodup := nodup_of_isLexSorted parts11 parts11_check.2.1
  have hcard : S.card = 456 := by
    rw [Finset.card_image_of_injOn]
    · rw [List.toFinset_card_of_nodup hnodup, parts11_check.1]
    · intro l₁ hl₁ l₂ hl₂ heq
      have h1 : l₁ ∈ parts11 := List.mem_toFinset.mp hl₁
      have h2 : l₂ ∈ parts11 := List.mem_toFinset.mp hl₂
      have hs1 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
        ((List.all_eq_true.mp parts11_check.2.2) l₁ h1)).1).1
      have hs2 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
        ((List.all_eq_true.mp parts11_check.2.2) l₂ h2)).1).1
      exact sortedDesc_eq_of_perm l₁ l₂ hs1 hs2 heq
  have hsub : (S : Set (Multiset ℕ)) ⊆ { s : Multiset ℕ | IsDyadicPartition 11 s } := by
    intro s hs
    simp only [S, Finset.coe_image, Set.mem_image, Finset.mem_coe, List.mem_toFinset] at hs
    rcases hs with ⟨l, hl, rfl⟩
    exact mem_parts11_valid l hl
  unfold A002843
  calc 456 = S.card := hcard.symm
    _ = Set.ncard (S : Set (Multiset ℕ)) := (Set.ncard_coe_finset S).symm
    _ ≤ Set.ncard { s : Multiset ℕ | IsDyadicPartition 11 s } :=
        Set.ncard_le_ncard hsub (finite_dyadicPartition 11)

private theorem prove_disproof : ¬ type_of% @OMA.S_oeis_a002843.main := by
  intro hEq
  set A : PowerSeries ℤ := PowerSeries.mk fun n => (A002843 n : ℤ)
  have hId : (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X - PowerSeries.X ^ 3 +
      PowerSeries.C (3 : ℤ) * PowerSeries.X ^ 4) * A =
      1 - PowerSeries.X - PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
    convert hEq using 1
    ring
  have hstep : ∀ n : ℕ,
      (A002843 n : ℤ) -
        2 * (if 1 ≤ n then (A002843 (n - 1) : ℤ) else 0) -
        (if 3 ≤ n then (A002843 (n - 3) : ℤ) else 0) +
        3 * (if 4 ≤ n then (A002843 (n - 4) : ℤ) else 0) =
      (if n = 0 then 1 else 0) - (if n = 1 then 1 else 0) -
        (if n = 3 then 1 else 0) + (if n = 4 then 1 else 0) := by
    intro n
    have hc := congrArg (PowerSeries.coeff n) hId
    rw [add_mul, sub_mul, sub_mul, one_mul, mul_assoc, mul_assoc,
      map_add, map_sub, map_sub, map_add, map_sub, map_sub,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hc
    rw [show (PowerSeries.X : PowerSeries ℤ) * A = PowerSeries.X ^ 1 * A by rw [pow_one]] at hc
    rw [coeff_X_pow_mul_eq, coeff_X_pow_mul_eq, coeff_X_pow_mul_eq,
      PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X_pow] at hc
    simp only [A, PowerSeries.coeff_mk] at hc
    exact hc
  have hrec : ∀ n : ℕ, 5 ≤ n →
      (A002843 n : ℤ) =
        2 * (A002843 (n - 1) : ℤ) + (A002843 (n - 3) : ℤ) - 3 * (A002843 (n - 4) : ℤ) := by
    intro n hn
    have h := hstep n
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
    linarith
  have h0 : (A002843 0 : ℤ) = 1 := by
    have h := hstep 0
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h; linarith
  have h1 : (A002843 1 : ℤ) = 1 := by
    have h := hstep 1
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega)] at h
    norm_num [h0] at h; linarith
  have h2 : (A002843 2 : ℤ) = 2 := by
    have h := hstep 2
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
    norm_num [h1] at h; linarith
  have h3 : (A002843 3 : ℤ) = 4 := by
    have h := hstep 3
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega)] at h
    norm_num [h0, h2] at h; linarith
  have h4 : (A002843 4 : ℤ) = 7 := by
    have h := hstep 4
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl] at h
    norm_num [h0, h1, h3] at h; linarith
  have h5 : (A002843 5 : ℤ) = 13 := by have h := hrec 5 (by omega); norm_num [h1, h2, h4] at h; exact h
  have h6 : (A002843 6 : ℤ) = 24 := by have h := hrec 6 (by omega); norm_num [h2, h3, h5] at h; exact h
  have h7 : (A002843 7 : ℤ) = 43 := by have h := hrec 7 (by omega); norm_num [h3, h4, h6] at h; exact h
  have h8 : (A002843 8 : ℤ) = 78 := by have h := hrec 8 (by omega); norm_num [h4, h5, h7] at h; exact h
  have h9 : (A002843 9 : ℤ) = 141 := by have h := hrec 9 (by omega); norm_num [h5, h6, h8] at h; exact h
  have h10 : (A002843 10 : ℤ) = 253 := by have h := hrec 10 (by omega); norm_num [h6, h7, h9] at h; exact h
  have h11 : (A002843 11 : ℤ) = 455 := by have h := hrec 11 (by omega); norm_num [h7, h8, h10] at h; exact h
  have hge : (456 : ℤ) ≤ (A002843 11 : ℤ) := by exact_mod_cast A002843_11_ge
  linarith

end OMA.P_oeis_a002843

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002843.main) :=
  OMA.P_oeis_a002843.prove_disproof
