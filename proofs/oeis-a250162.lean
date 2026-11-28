import OMAStatements.S_oeis_a250162

/-!
# Proof of OEIS A250162 (Colin Barker's 2018 Conjecture)

We prove both the closed form
`∀ n ≥ 1, (a n : ℤ) = 2 * (2 - 3 * 2 ^ n + 4 ^ n + 2 * n)`
and the generating-function identity
`PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 2 * (1 - 2 * X) * (1 - 4 * X)) = 4 * X * (1 - 3 * X + 5 * X ^ 2)`.

Combinatorial proof:
1. For `x : Fin (n + 1) → Fin 4`, let `d i = |x (i + 1) - x i| ∈ {0, 1, 2, 3}` and let
   `c₁, c₂, c₃` count the occurrences of `1, 2, 3` among `d 0, ..., d (n - 1)`.
2. `SignedSumZero x` holds iff `Even (c₁ + c₃)` (equivalently `(x 0).val % 2 = (x (Fin.last n)).val % 2`,
   counting `2 * 4 ^ n` even-parity arrays) and `x` avoids two disjoint excluded families:
   - `B1`: `c₁ = 0 ∧ c₃ = 0 ∧ Odd c₂` (all steps in `{0, 2}` with odd flip count; exact bijection
     with `Fin 2 × (Fin n → Fin 2)` of cardinality `2 ^ (n + 1)`).
   - `B23`: `x ∈ E ∧ c₁ + c₂ = 1 ∧ 1 ≤ c₃` (either `c₁ = 1, c₂ = 0, Odd c₃` or
     `c₁ = 0, c₂ = 1, Even c₃, 2 ≤ c₃`). Reversal gives a bijection between the `{0, 3}`-prefix
     and `{1, 2}`-prefix halves, and the `{0, 3}`-prefix half bijects onto pairs `(i₀, f)` where
     `i₀ : Fin n` is the unique `{1, 2}`-step index and `f : Fin (i₀ + 1) → Bool` is non-constant,
     giving cardinality `2 * ∑ i < n, (2 ^ (i + 1) - 2) = 4 * 2 ^ n - 4 * n - 4`.
3. Subtracting `|B1| + |B23| = 6 * 2 ^ n - 4 * n - 4` from `|E| = 2 * 4 ^ n` yields the exact
   closed form, and coefficient comparison via `PowerSeries.ext` proves the g.f. identity.
-/

namespace OeisA250162

open OMA.S_oeis_a250162

private def absDiff {n : ℕ} (x : Fin (n + 1) → Fin 4) (i : Fin n) : ℕ :=
  Int.natAbs (((x i.succ).val : ℤ) - (x i.castSucc).val)

private def stepCount {n : ℕ} (x : Fin (n + 1) → Fin 4) (v : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin n => absDiff x i = v).card

private lemma absDiff_le_three {n : ℕ} (x : Fin (n + 1) → Fin 4) (i : Fin n) :
    absDiff x i ≤ 3 := by
  unfold absDiff
  have h1 := (x i.succ).isLt
  have h2 := (x i.castSucc).isLt
  omega

private lemma signedSumZero_iff_absDiff {n : ℕ} (x : Fin (n + 1) → Fin 4) :
    SignedSumZero x ↔
      ∃ b : Fin n → Bool, ∑ i : Fin n, sign (b i) * (absDiff x i : ℤ) = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    let b' : Fin n → Bool := fun i =>
      if ((x i.castSucc).val : ℤ) ≤ (x i.succ).val then b i else !b i
    refine ⟨b', ?_⟩
    rw [← hb]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold absDiff sign b'
    by_cases hle : ((x i.castSucc).val : ℤ) ≤ (x i.succ).val
    · simp only [hle, ↓reduceIte]
      have hnn : (0 : ℤ) ≤ ((x i.succ).val : ℤ) - (x i.castSucc).val := by omega
      rw [Int.natAbs_of_nonneg hnn]
    · simp only [hle, ↓reduceIte]
      have hneg : ((x i.succ).val : ℤ) - (x i.castSucc).val ≤ 0 := by omega
      have habs : (Int.natAbs (((x i.succ).val : ℤ) - (x i.castSucc).val) : ℤ) =
          -(((x i.succ).val : ℤ) - (x i.castSucc).val) := by omega
      rw [habs]
      cases b i <;> simp
  · rintro ⟨b, hb⟩
    let b' : Fin n → Bool := fun i =>
      if ((x i.castSucc).val : ℤ) ≤ (x i.succ).val then b i else !b i
    refine ⟨b', ?_⟩
    rw [← hb]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold absDiff sign b'
    by_cases hle : ((x i.castSucc).val : ℤ) ≤ (x i.succ).val
    · simp only [hle, ↓reduceIte]
      have hnn : (0 : ℤ) ≤ ((x i.succ).val : ℤ) - (x i.castSucc).val := by omega
      rw [Int.natAbs_of_nonneg hnn]
    · simp only [hle, ↓reduceIte]
      have habs : (Int.natAbs (((x i.succ).val : ℤ) - (x i.castSucc).val) : ℤ) =
          -(((x i.succ).val : ℤ) - (x i.castSucc).val) := by omega
      rw [habs]
      cases b i <;> simp

private lemma sum_sign_eq_two_mul_card_sub {α : Type*} [DecidableEq α]
    (s : Finset α) (b : α → Bool) :
    ∑ i ∈ s, sign (b i) = 2 * ((s.filter fun i => b i = true).card : ℤ) - (s.card : ℤ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Finset.filter_insert]
    cases hb : b a
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      have hsign : sign false = -1 := rfl
      rw [hsign, ih]; ring
    · have hna : a ∉ s.filter (fun i => b i = true) := fun h => ha (Finset.mem_filter.mp h).1
      simp only [↓reduceIte, Finset.card_insert_of_notMem hna, Nat.cast_add, Nat.cast_one]
      have hsign : sign true = 1 := rfl
      rw [hsign, ih]; ring

private lemma exists_sign_sum_eq {α : Type*} [DecidableEq α]
    (s : Finset α) (k : ℤ) (hlo : -(s.card : ℤ) ≤ k) (hhi : k ≤ (s.card : ℤ))
    (hpar : k % 2 = (s.card : ℤ) % 2) :
    ∃ b : α → Bool, ∑ i ∈ s, sign (b i) = k := by
  have hnonneg : (0 : ℤ) ≤ (s.card : ℤ) + k := by omega
  let p : ℕ := (((s.card : ℤ) + k) / 2).toNat
  have hp_le : p ≤ s.card := by
    have h2 : ((s.card : ℤ) + k) / 2 ≤ (s.card : ℤ) := by omega
    have h1 : (0 : ℤ) ≤ ((s.card : ℤ) + k) / 2 := by omega
    omega
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hp_le
  refine ⟨fun i => decide (i ∈ t), ?_⟩
  rw [sum_sign_eq_two_mul_card_sub]
  have hfilt : (s.filter fun i => decide (i ∈ t) = true) = t := by
    ext i
    simp only [Finset.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨ht_sub h, h⟩⟩
  rw [hfilt, ht_card]
  have hp_eq : (p : ℤ) = ((s.card : ℤ) + k) / 2 := by
    dsimp [p]
    exact Int.toNat_of_nonneg (by omega)
  omega

private lemma signedSumZero_iff_exists_k {n : ℕ} (x : Fin (n + 1) → Fin 4) :
    SignedSumZero x ↔
      ∃ k₁ k₂ k₃ : ℤ,
        -(stepCount x 1 : ℤ) ≤ k₁ ∧ k₁ ≤ (stepCount x 1 : ℤ) ∧ k₁ % 2 = (stepCount x 1 : ℤ) % 2 ∧
        -(stepCount x 2 : ℤ) ≤ k₂ ∧ k₂ ≤ (stepCount x 2 : ℤ) ∧ k₂ % 2 = (stepCount x 2 : ℤ) % 2 ∧
        -(stepCount x 3 : ℤ) ≤ k₃ ∧ k₃ ≤ (stepCount x 3 : ℤ) ∧ k₃ % 2 = (stepCount x 3 : ℤ) % 2 ∧
        k₁ + 2 * k₂ + 3 * k₃ = 0 := by
  rw [signedSumZero_iff_absDiff]
  let S₁ := Finset.univ.filter fun i : Fin n => absDiff x i = 1
  let S₂ := Finset.univ.filter fun i : Fin n => absDiff x i = 2
  let S₃ := Finset.univ.filter fun i : Fin n => absDiff x i = 3
  have hsum_decomp : ∀ b : Fin n → Bool,
      ∑ i : Fin n, sign (b i) * (absDiff x i : ℤ) =
        (∑ i ∈ S₁, sign (b i)) + 2 * (∑ i ∈ S₂, sign (b i)) + 3 * (∑ i ∈ S₃, sign (b i)) := by
    intro b
    have hsplit : ∀ i : Fin n,
        sign (b i) * (absDiff x i : ℤ) =
          (if absDiff x i = 1 then sign (b i) else 0) +
          (if absDiff x i = 2 then 2 * sign (b i) else 0) +
          (if absDiff x i = 3 then 3 * sign (b i) else 0) := by
      intro i
      have hle := absDiff_le_three x i
      interval_cases (absDiff x i) <;> simp <;> ring
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_filter]
    have h2 : ∑ i ∈ S₂, 2 * sign (b i) = 2 * ∑ i ∈ S₂, sign (b i) := by
      rw [← Finset.mul_sum]
    have h3 : ∑ i ∈ S₃, 3 * sign (b i) = 3 * ∑ i ∈ S₃, sign (b i) := by
      rw [← Finset.mul_sum]
    rw [h2, h3]
  constructor
  · rintro ⟨b, hb⟩
    rw [hsum_decomp b] at hb
    refine ⟨∑ i ∈ S₁, sign (b i), ∑ i ∈ S₂, sign (b i), ∑ i ∈ S₃, sign (b i), ?_⟩
    have hb1 := sum_sign_eq_two_mul_card_sub S₁ b
    have hb2 := sum_sign_eq_two_mul_card_sub S₂ b
    have hb3 := sum_sign_eq_two_mul_card_sub S₃ b
    have hc1 : (S₁.filter fun i => b i = true).card ≤ S₁.card := Finset.card_filter_le _ _
    have hc2 : (S₂.filter fun i => b i = true).card ≤ S₂.card := Finset.card_filter_le _ _
    have hc3 : (S₃.filter fun i => b i = true).card ≤ S₃.card := Finset.card_filter_le _ _
    change -(S₁.card : ℤ) ≤ _ ∧ _ ≤ (S₁.card : ℤ) ∧ _ % 2 = (S₁.card : ℤ) % 2 ∧
      -(S₂.card : ℤ) ≤ _ ∧ _ ≤ (S₂.card : ℤ) ∧ _ % 2 = (S₂.card : ℤ) % 2 ∧
      -(S₃.card : ℤ) ≤ _ ∧ _ ≤ (S₃.card : ℤ) ∧ _ % 2 = (S₃.card : ℤ) % 2 ∧ _
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, hb⟩
  · rintro ⟨k₁, k₂, k₃, h1l, h1u, h1p, h2l, h2u, h2p, h3l, h3u, h3p, hsum⟩
    obtain ⟨b₁, hb₁⟩ := exists_sign_sum_eq S₁ k₁ h1l h1u h1p
    obtain ⟨b₂, hb₂⟩ := exists_sign_sum_eq S₂ k₂ h2l h2u h2p
    obtain ⟨b₃, hb₃⟩ := exists_sign_sum_eq S₃ k₃ h3l h3u h3p
    let b : Fin n → Bool := fun i =>
      if absDiff x i = 1 then b₁ i else if absDiff x i = 2 then b₂ i else b₃ i
    refine ⟨b, ?_⟩
    rw [hsum_decomp b]
    have hs1 : ∑ i ∈ S₁, sign (b i) = ∑ i ∈ S₁, sign (b₁ i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have h := (Finset.mem_filter.mp hi).2
      simp [b, h]
    have hs2 : ∑ i ∈ S₂, sign (b i) = ∑ i ∈ S₂, sign (b₂ i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have h := (Finset.mem_filter.mp hi).2
      simp [b, h]
    have hs3 : ∑ i ∈ S₃, sign (b i) = ∑ i ∈ S₃, sign (b₃ i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have h := (Finset.mem_filter.mp hi).2
      simp [b, h]
    rw [hs1, hs2, hs3, hb₁, hb₂, hb₃, hsum]

private lemma signedSumZero_iff_counts {n : ℕ} (x : Fin (n + 1) → Fin 4) :
    SignedSumZero x ↔
      (stepCount x 1 + stepCount x 3) % 2 = 0 ∧
      ¬ (stepCount x 1 = 0 ∧ stepCount x 3 = 0 ∧ stepCount x 2 % 2 = 1) ∧
      ¬ (stepCount x 1 + stepCount x 2 = 1 ∧ 1 ≤ stepCount x 3) := by
  rw [signedSumZero_iff_exists_k]
  set c₁ := stepCount x 1
  set c₂ := stepCount x 2
  set c₃ := stepCount x 3
  constructor
  · rintro ⟨k₁, k₂, k₃, h1l, h1u, h1p, h2l, h2u, h2p, h3l, h3u, h3p, hsum⟩
    refine ⟨by omega, by omega, ?_⟩
    rintro ⟨h12, _⟩
    have hsplit : (c₁ = 1 ∧ c₂ = 0) ∨ (c₁ = 0 ∧ c₂ = 1) := by omega
    rcases hsplit with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
    · rw [hc1] at h1l h1u h1p
      rw [hc2] at h2l h2u h2p
      omega
    · rw [hc1] at h1l h1u h1p
      rw [hc2] at h2l h2u h2p
      omega
  · rintro ⟨hpar, hnotB1, hnotB23⟩
    by_cases hp1 : c₁ % 2 = 0
    · by_cases hp2 : c₂ % 2 = 0
      · exact ⟨0, 0, 0, by omega, by omega, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega⟩
      · by_cases hc1 : 2 ≤ c₁
        · exact ⟨-2, 1, 0, by omega, by omega, by omega, by omega, by omega, by omega,
            by omega, by omega, by omega, by omega⟩
        · have hc1_0 : c₁ = 0 := by omega
          have hc3_ge2 : 2 ≤ c₃ := by omega
          have hc2_ge3 : 3 ≤ c₂ := by omega
          exact ⟨0, -3, 2, by omega, by omega, by omega, by omega, by omega, by omega,
            by omega, by omega, by omega, by omega⟩
    · by_cases hp2 : c₂ % 2 = 0
      · by_cases hc1 : 3 ≤ c₁
        · exact ⟨-3, 0, 1, by omega, by omega, by omega, by omega, by omega, by omega,
            by omega, by omega, by omega, by omega⟩
        · have hc1_1 : c₁ = 1 := by omega
          have hc3_ge1 : 1 ≤ c₃ := by omega
          have hc2_ge2 : 2 ≤ c₂ := by omega
          exact ⟨1, -2, 1, by omega, by omega, by omega, by omega, by omega, by omega,
            by omega, by omega, by omega, by omega⟩
      · exact ⟨1, 1, -1, by omega, by omega, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega⟩

private lemma sum_adj_diff {n : ℕ} (x : Fin (n + 1) → Fin 4) :
    ∑ i : Fin n, (((x i.succ).val : ℤ) - (x i.castSucc).val) =
      ((x (Fin.last n)).val : ℤ) - (x 0).val := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun j => x j.castSucc)
    simp only [Fin.castSucc_succ, Fin.castSucc_zero] at hih ⊢
    rw [hih]
    have hlast : (Fin.last m).castSucc = (Fin.last m).castSucc := rfl
    change ((x (Fin.last m).castSucc).val : ℤ) - (x 0).val +
      (((x (Fin.last (m + 1))).val : ℤ) - (x (Fin.last m).castSucc).val) =
      ((x (Fin.last (m + 1))).val : ℤ) - (x 0).val
    ring

private lemma parity_iff_endpoints {n : ℕ} (x : Fin (n + 1) → Fin 4) :
    (stepCount x 1 + stepCount x 3) % 2 = 0 ↔
      (x 0).val % 2 = (x (Fin.last n)).val % 2 := by
  have hmod : ∀ i : Fin n,
      (((x i.succ).val : ℤ) - (x i.castSucc).val) % 2 =
        if absDiff x i = 1 ∨ absDiff x i = 3 then 1 else 0 := by
    intro i
    unfold absDiff
    have h1 := (x i.succ).isLt
    have h2 := (x i.castSucc).isLt
    omega
  have hsum_mod :
      (∑ i : Fin n, (((x i.succ).val : ℤ) - (x i.castSucc).val)) % 2 =
        ((stepCount x 1 + stepCount x 3 : ℕ) : ℤ) % 2 := by
    have h1 : (∑ i : Fin n, (((x i.succ).val : ℤ) - (x i.castSucc).val)) % 2 =
        (∑ i : Fin n, (if absDiff x i = 1 ∨ absDiff x i = 3 then (1 : ℤ) else 0)) % 2 := by
      have hcongr : ∀ s : Finset (Fin n),
          (∑ i ∈ s, (((x i.succ).val : ℤ) - (x i.castSucc).val)) % 2 =
          (∑ i ∈ s, (if absDiff x i = 1 ∨ absDiff x i = 3 then (1 : ℤ) else 0)) % 2 := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          have hm := hmod a
          omega
      exact hcongr Finset.univ
    rw [h1]
    have hcard :
        ∑ i : Fin n, (if absDiff x i = 1 ∨ absDiff x i = 3 then (1 : ℤ) else 0) =
          ((stepCount x 1 + stepCount x 3 : ℕ) : ℤ) := by
      unfold stepCount
      have hdisj : Disjoint
          (Finset.univ.filter fun i : Fin n => absDiff x i = 1)
          (Finset.univ.filter fun i : Fin n => absDiff x i = 3) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi3
        have h1 := (Finset.mem_filter.mp hi1).2
        have h3 := (Finset.mem_filter.mp hi3).2
        omega
      have hunion :
          (Finset.univ.filter fun i : Fin n => absDiff x i = 1 ∨ absDiff x i = 3) =
          (Finset.univ.filter fun i : Fin n => absDiff x i = 1) ∪
          (Finset.univ.filter fun i : Fin n => absDiff x i = 3) := by
        ext i
        simp
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hunion,
        Finset.card_union_of_disjoint hdisj]
    rw [hcard]
  rw [sum_adj_diff] at hsum_mod
  omega

private def evenSet (n : ℕ) : Finset (Fin (n + 1) → Fin 4) :=
  Finset.univ.filter fun x => (x 0).val % 2 = (x (Fin.last n)).val % 2

private def bad1Set (n : ℕ) : Finset (Fin (n + 1) → Fin 4) :=
  Finset.univ.filter fun x =>
    stepCount x 1 = 0 ∧ stepCount x 3 = 0 ∧ stepCount x 2 % 2 = 1

private def bad23Set (n : ℕ) : Finset (Fin (n + 1) → Fin 4) :=
  Finset.univ.filter fun x =>
    (x 0).val % 2 = (x (Fin.last n)).val % 2 ∧
    stepCount x 1 + stepCount x 2 = 1 ∧ 1 ≤ stepCount x 3

private lemma card_evenSet (n : ℕ) (hn : 1 ≤ n) : (evenSet n).card = 2 * 4 ^ n := by
  have hbij : (evenSet n).card = ((Finset.univ : Finset ((Fin n → Fin 4) × Fin 2))).card := by
    refine Finset.card_bij
      (fun x _ => (fun i : Fin n => x i.castSucc, ⟨(x (Fin.last n)).val / 2, by have := (x (Fin.last n)).isLt; omega⟩))
      ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro x₁ hx₁ x₂ hx₂ heq
      have hpar₁ := (Finset.mem_filter.mp hx₁).2
      have hpar₂ := (Finset.mem_filter.mp hx₂).2
      have hinit : ∀ i : Fin n, x₁ i.castSucc = x₂ i.castSucc :=
        fun i => congrFun (congrArg Prod.fst heq) i
      have hdiv : (x₁ (Fin.last n)).val / 2 = (x₂ (Fin.last n)).val / 2 :=
        congrArg Fin.val (congrArg Prod.snd heq)
      have h0 : x₁ 0 = x₂ 0 := by
        have := hinit ⟨0, hn⟩
        simpa using this
      funext j
      refine Fin.lastCases ?_ hinit j
      apply Fin.ext
      have h0v : (x₁ 0).val = (x₂ 0).val := congrArg Fin.val h0
      omega
    · rintro ⟨y, b⟩ _
      let x : Fin (n + 1) → Fin 4 :=
        Fin.lastCases ⟨2 * b.val + (y ⟨0, hn⟩).val % 2, by have := b.isLt; omega⟩ y
      have hx0 : x 0 = y ⟨0, hn⟩ := by
        change Fin.lastCases _ y (⟨0, hn⟩ : Fin n).castSucc = y ⟨0, hn⟩
        exact Fin.lastCases_castSucc ⟨0, hn⟩
      have hxlast : x (Fin.last n) = ⟨2 * b.val + (y ⟨0, hn⟩).val % 2, by have := b.isLt; omega⟩ := by
        dsimp [x]
        exact Fin.lastCases_last
      have hxlast_val : (x (Fin.last n)).val = 2 * b.val + (y ⟨0, hn⟩).val % 2 :=
        congrArg Fin.val hxlast
      refine ⟨x, ?_, ?_⟩
      · rw [evenSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hx0, hxlast_val]
        omega
      · ext i
        · simp [x]
        · simp only [hxlast_val]
          have := b.isLt
          omega
  simp only [hbij, Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

private lemma card_bad1Set (n : ℕ) (hn : 1 ≤ n) : (bad1Set n).card = 2 ^ (n + 1) := by
  have hchar : ∀ x : Fin (n + 1) → Fin 4,
      x ∈ bad1Set n ↔
        (∀ j : Fin (n + 1), (x j).val % 2 = (x 0).val % 2) ∧
        (x (Fin.last n)).val / 2 ≠ (x 0).val / 2 := by
    intro x
    rw [bad1Set, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    have hall_even : (stepCount x 1 = 0 ∧ stepCount x 3 = 0) ↔
        ∀ i : Fin n, (x i.succ).val % 2 = (x i.castSucc).val % 2 := by
      unfold stepCount
      rw [Finset.card_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
        Finset.filter_eq_empty_iff]
      constructor
      · rintro ⟨h1, h3⟩ i
        have hi1 : absDiff x i ≠ 1 := h1 (Finset.mem_univ i)
        have hi3 : absDiff x i ≠ 3 := h3 (Finset.mem_univ i)
        unfold absDiff at hi1 hi3
        have ha := (x i.succ).isLt
        have hb := (x i.castSucc).isLt
        omega
      · intro h
        refine ⟨fun i _ => ?_, fun i _ => ?_⟩
        · have hi := h i; unfold absDiff; omega
        · have hi := h i; unfold absDiff; omega
    have hall_const : (∀ i : Fin n, (x i.succ).val % 2 = (x i.castSucc).val % 2) ↔
        ∀ j : Fin (n + 1), (x j).val % 2 = (x 0).val % 2 := by
      constructor
      · intro h j
        obtain ⟨k, hk⟩ := j
        induction k with
        | zero => rfl
        | succ k ih =>
          have hk' : k < n := by omega
          have hstep := h ⟨k, hk'⟩
          have hprev := ih (by omega)
          exact hstep.trans hprev
      · intro h i
        rw [h i.succ, h i.castSucc]
    have hflip_parity : (∀ j : Fin (n + 1), (x j).val % 2 = (x 0).val % 2) →
        (stepCount x 2 % 2 = 1 ↔ (x (Fin.last n)).val / 2 ≠ (x 0).val / 2) := by
      intro hconst
      have hsum_div :
          ∑ i : Fin n, (((x i.succ).val / 2 : ℤ) - ((x i.castSucc).val / 2 : ℤ)) =
            ((x (Fin.last n)).val / 2 : ℤ) - ((x 0).val / 2 : ℤ) := by
        have hstep_eq : ∀ i : Fin n,
            (((x i.succ).val : ℤ) - (x i.castSucc).val) =
              2 * (((x i.succ).val / 2 : ℤ) - ((x i.castSucc).val / 2 : ℤ)) := by
          intro i
          have h1 := hconst i.succ
          have h2 := hconst i.castSucc
          omega
        have htot := sum_adj_diff x
        simp_rw [hstep_eq, ← Finset.mul_sum] at htot
        have h0 := hconst (Fin.last n)
        omega
      have hterm_mod : ∀ i : Fin n,
          (((x i.succ).val / 2 : ℤ) - ((x i.castSucc).val / 2 : ℤ)) % 2 =
            if absDiff x i = 2 then 1 else 0 := by
        intro i
        unfold absDiff
        have h1 := (x i.succ).isLt
        have h2 := (x i.castSucc).isLt
        have hp1 := hconst i.succ
        have hp2 := hconst i.castSucc
        omega
      have hsum_mod :
          (∑ i : Fin n, (((x i.succ).val / 2 : ℤ) - ((x i.castSucc).val / 2 : ℤ))) % 2 =
            (stepCount x 2 : ℤ) % 2 := by
        have h1 : ∀ s : Finset (Fin n),
            (∑ i ∈ s, (((x i.succ).val / 2 : ℤ) - ((x i.castSucc).val / 2 : ℤ))) % 2 =
            (∑ i ∈ s, (if absDiff x i = 2 then (1 : ℤ) else 0)) % 2 := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp
          | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha]
            have hm := hterm_mod a
            omega
        rw [h1 Finset.univ, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        rfl
      rw [hsum_div] at hsum_mod
      have hlt0 := (x 0).isLt
      have hltn := (x (Fin.last n)).isLt
      omega
    constructor
    · rintro ⟨h1, h3, h2⟩
      have hconst := hall_const.mp (hall_even.mp ⟨h1, h3⟩)
      exact ⟨hconst, (hflip_parity hconst).mp h2⟩
    · rintro ⟨hconst, hneq⟩
      have ⟨h1, h3⟩ := hall_even.mpr (hall_const.mpr hconst)
      exact ⟨h1, h3, (hflip_parity hconst).mpr hneq⟩
  have hbij : (bad1Set n).card = ((Finset.univ : Finset (Fin 2 × (Fin n → Fin 2)))).card := by
    refine Finset.card_bij
      (fun x _ => (⟨(x 0).val % 2, by omega⟩,
        fun i : Fin n => ⟨(x i.castSucc).val / 2, by have := (x i.castSucc).isLt; omega⟩))
      ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro x₁ hx₁ x₂ hx₂ heq
      obtain ⟨hc₁, hne₁⟩ := (hchar x₁).mp hx₁
      obtain ⟨hc₂, hne₂⟩ := (hchar x₂).mp hx₂
      have hp : (x₁ 0).val % 2 = (x₂ 0).val % 2 := congrArg Fin.val (congrArg Prod.fst heq)
      have hdiv : ∀ i : Fin n, (x₁ i.castSucc).val / 2 = (x₂ i.castSucc).val / 2 :=
        fun i => congrArg Fin.val (congrFun (congrArg Prod.snd heq) i)
      have hdiv0 : (x₁ 0).val / 2 = (x₂ 0).val / 2 := by
        have := hdiv ⟨0, hn⟩
        simpa using this
      funext j
      refine Fin.lastCases ?_ (fun i => Fin.ext (by have := hc₁ i.castSucc; have := hc₂ i.castSucc; have := hdiv i; omega)) j
      apply Fin.ext
      have h1 := hc₁ (Fin.last n)
      have h2 := hc₂ (Fin.last n)
      have hlt1 := (x₁ (Fin.last n)).isLt
      have hlt2 := (x₂ (Fin.last n)).isLt
      have hlt10 := (x₁ 0).isLt
      have hlt20 := (x₂ 0).isLt
      omega
    · rintro ⟨p, bits⟩ _
      let x : Fin (n + 1) → Fin 4 :=
        Fin.lastCases
          ⟨2 * (1 - (bits ⟨0, hn⟩).val) + p.val, by have := p.isLt; have := (bits ⟨0, hn⟩).isLt; omega⟩
          (fun i => ⟨2 * (bits i).val + p.val, by have := p.isLt; have := (bits i).isLt; omega⟩)
      have hx0 : x 0 = ⟨2 * (bits ⟨0, hn⟩).val + p.val, by have := p.isLt; have := (bits ⟨0, hn⟩).isLt; omega⟩ := by
        have h0eq : (0 : Fin (n + 1)) = (⟨0, hn⟩ : Fin n).castSucc := by ext; rfl
        rw [h0eq]
        exact Fin.lastCases_castSucc ⟨0, hn⟩
      have hxlast : x (Fin.last n) =
          ⟨2 * (1 - (bits ⟨0, hn⟩).val) + p.val, by have := p.isLt; have := (bits ⟨0, hn⟩).isLt; omega⟩ := by
        dsimp [x]
        exact Fin.lastCases_last
      have hx0_val : (x 0).val = 2 * (bits ⟨0, hn⟩).val + p.val := congrArg Fin.val hx0
      have hxlast_val : (x (Fin.last n)).val = 2 * (1 - (bits ⟨0, hn⟩).val) + p.val :=
        congrArg Fin.val hxlast
      refine ⟨x, ?_, ?_⟩
      · rw [hchar]
        refine ⟨fun j => ?_, ?_⟩
        · refine Fin.lastCases ?_ (fun i => ?_) j
          · rw [hx0_val, hxlast_val]; have := p.isLt; omega
          · rw [hx0_val]; simp only [x, Fin.lastCases_castSucc]; have := p.isLt; omega
        · rw [hx0_val, hxlast_val]; have := p.isLt; have := (bits ⟨0, hn⟩).isLt; omega
      · ext
        · simp only [hx0_val]; have := p.isLt; omega
        · simp only [x, Fin.lastCases_castSucc]; have := p.isLt; omega
  simp only [hbij, Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

private def bad23L (n : ℕ) : Finset (Fin (n + 1) → Fin 4) :=
  (bad23Set n).filter fun x => (x 0).val = 0 ∨ (x 0).val = 3

private def bad23R (n : ℕ) : Finset (Fin (n + 1) → Fin 4) :=
  (bad23Set n).filter fun x => (x 0).val = 1 ∨ (x 0).val = 2

private lemma bad23_structure {n : ℕ} {x : Fin (n + 1) → Fin 4} (hx : x ∈ bad23Set n) :
    ∃ i₀ : Fin n,
      (∀ i : Fin n, (absDiff x i = 1 ∨ absDiff x i = 2) ↔ i = i₀) ∧
      ((x 0).val = 0 ∨ (x 0).val = 3 →
        (∀ j : Fin (n + 1), j.val ≤ i₀.val → (x j).val = 0 ∨ (x j).val = 3) ∧
        (∀ j : Fin (n + 1), i₀.val < j.val → (x j).val = if (x 0).val = 3 then 1 else 2) ∧
        (∃ i : Fin n, i.val < i₀.val ∧ absDiff x i = 3)) ∧
      ((x 0).val = 1 ∨ (x 0).val = 2 → (x (Fin.last n)).val = 0 ∨ (x (Fin.last n)).val = 3) := by
  have hx' := (Finset.mem_filter.mp hx).2
  rcases hx' with ⟨hpar, h12, h3ge⟩
  have h12_card : (Finset.univ.filter fun i : Fin n => absDiff x i = 1 ∨ absDiff x i = 2).card = 1 := by
    have hunion :
        (Finset.univ.filter fun i : Fin n => absDiff x i = 1 ∨ absDiff x i = 2) =
        (Finset.univ.filter fun i : Fin n => absDiff x i = 1) ∪
        (Finset.univ.filter fun i : Fin n => absDiff x i = 2) := by
      ext i; simp
    have hdisj : Disjoint
        (Finset.univ.filter fun i : Fin n => absDiff x i = 1)
        (Finset.univ.filter fun i : Fin n => absDiff x i = 2) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj]
    exact h12
  obtain ⟨i₀, hi₀_eq⟩ := Finset.card_eq_one.mp h12_card
  have hi₀_iff : ∀ i : Fin n, (absDiff x i = 1 ∨ absDiff x i = 2) ↔ i = i₀ := by
    intro i
    have h := Finset.ext_iff.mp hi₀_eq i
    simpa [Finset.mem_filter, Finset.mem_singleton] using h
  have hother : ∀ i : Fin n, i ≠ i₀ → absDiff x i = 0 ∨ absDiff x i = 3 := by
    intro i hne
    have hnot := (hi₀_iff i).not.mpr hne
    have hle := absDiff_le_three x i
    omega
  have hstep03 : ∀ i : Fin n, i ≠ i₀ →
      (((x i.castSucc).val = 0 ∨ (x i.castSucc).val = 3) ↔ ((x i.succ).val = 0 ∨ (x i.succ).val = 3)) := by
    intro i hne
    have ho := hother i hne
    unfold absDiff at ho
    have ha := (x i.castSucc).isLt
    have hb := (x i.succ).isLt
    omega
  have hstep12 : ∀ i : Fin n, i ≠ i₀ →
      ((x i.castSucc).val = 1 ∨ (x i.castSucc).val = 2) → x i.succ = x i.castSucc := by
    intro i hne h12v
    have ho := hother i hne
    unfold absDiff at ho
    have ha := (x i.castSucc).isLt
    have hb := (x i.succ).isLt
    apply Fin.ext
    omega
  have hstep12_back : ∀ i : Fin n, i ≠ i₀ →
      ((x i.succ).val = 1 ∨ (x i.succ).val = 2) → x i.castSucc = x i.succ := by
    intro i hne h12v
    have ho := hother i hne
    unfold absDiff at ho
    have ha := (x i.castSucc).isLt
    have hb := (x i.succ).isLt
    apply Fin.ext
    omega
  have hcross : ((x i₀.castSucc).val = 0 ∨ (x i₀.castSucc).val = 3) →
      (x i₀.succ).val = 1 ∨ (x i₀.succ).val = 2 := by
    intro h03
    have h12i := (hi₀_iff i₀).mpr rfl
    unfold absDiff at h12i
    have hb := (x i₀.succ).isLt
    omega
  have hex3 : ∃ i₃ : Fin n, absDiff x i₃ = 3 := by
    have hne : (Finset.univ.filter fun i : Fin n => absDiff x i = 3).Nonempty :=
      Finset.card_pos.mp (by unfold stepCount at h3ge; omega)
    obtain ⟨i₃, hi₃⟩ := hne
    exact ⟨i₃, (Finset.mem_filter.mp hi₃).2⟩
  refine ⟨i₀, hi₀_iff, ?_, ?_⟩
  · intro h0_03
    have hpref : ∀ j : Fin (n + 1), j.val ≤ i₀.val → (x j).val = 0 ∨ (x j).val = 3 := by
      intro j hj
      obtain ⟨k, hk⟩ := j
      dsimp at hj
      induction k with
      | zero => exact h0_03
      | succ k ih =>
        have hk' : k < n := by omega
        have hprev := ih (by omega) (by omega)
        have hne : (⟨k, hk'⟩ : Fin n) ≠ i₀ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
        exact (hstep03 ⟨k, hk'⟩ hne).mp hprev
    have hsucc_12 : (x i₀.succ).val = 1 ∨ (x i₀.succ).val = 2 :=
      hcross (hpref i₀.castSucc le_rfl)
    have hsuff_eq : ∀ j : Fin (n + 1), i₀.val < j.val → x j = x i₀.succ := by
      intro j hj
      obtain ⟨k, hk⟩ := j
      dsimp at hj
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hkeq : k = i₀.val
        · have heq : (⟨k + 1, hk⟩ : Fin (n + 1)) = i₀.succ := by ext; simp [hkeq]
          rw [heq]
        · have hk' : k < n := by omega
          have hprev := ih (by omega) (by omega)
          have hne : (⟨k, hk'⟩ : Fin n) ≠ i₀ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
          have h12prev : (x (⟨k, hk'⟩ : Fin n).castSucc).val = 1 ∨
              (x (⟨k, hk'⟩ : Fin n).castSucc).val = 2 := by
            have heq : (⟨k, hk'⟩ : Fin n).castSucc = ⟨k, by omega⟩ := rfl
            rw [heq, hprev]
            exact hsucc_12
          have hstep := hstep12 ⟨k, hk'⟩ hne h12prev
          have heq1 : (⟨k, hk'⟩ : Fin n).succ = ⟨k + 1, hk⟩ := rfl
          have heq2 : (⟨k, hk'⟩ : Fin n).castSucc = ⟨k, by omega⟩ := rfl
          rw [← heq1, hstep, heq2, hprev]
    have hlast_eq : x (Fin.last n) = x i₀.succ := hsuff_eq (Fin.last n) i₀.isLt
    have hval_succ : (x i₀.succ).val = if (x 0).val = 3 then 1 else 2 := by
      rw [hlast_eq] at hpar
      rcases h0_03 with h0 | h0 <;> rcases hsucc_12 with hs | hs <;> simp [h0, hs] at hpar ⊢
    refine ⟨hpref, fun j hj => by rw [hsuff_eq j hj, hval_succ], ?_⟩
    obtain ⟨i₃, hi₃⟩ := hex3
    refine ⟨i₃, ?_, hi₃⟩
    by_contra hge
    have hi₃_gt : i₀.val < i₃.val := by
      have hne : i₃ ≠ i₀ := by
        intro h; rw [h] at hi₃
        have := (hi₀_iff i₀).mpr rfl
        omega
      have : i₃.val ≠ i₀.val := fun h => hne (Fin.ext h)
      omega
    have h1 := hsuff_eq i₃.castSucc hi₃_gt
    have h2 := hsuff_eq i₃.succ (by simp; omega)
    unfold absDiff at hi₃
    rw [h1, h2] at hi₃
    simp at hi₃
  · intro h0_12
    have hpref_eq : ∀ j : Fin (n + 1), j.val ≤ i₀.val → x j = x 0 := by
      intro j hj
      obtain ⟨k, hk⟩ := j
      dsimp at hj
      induction k with
      | zero => rfl
      | succ k ih =>
        have hk' : k < n := by omega
        have hprev := ih (by omega) (by omega)
        have hne : (⟨k, hk'⟩ : Fin n) ≠ i₀ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
        have h12prev : (x (⟨k, hk'⟩ : Fin n).castSucc).val = 1 ∨
            (x (⟨k, hk'⟩ : Fin n).castSucc).val = 2 := by
          have heq : (⟨k, hk'⟩ : Fin n).castSucc = ⟨k, by omega⟩ := rfl
          rw [heq, hprev]; exact h0_12
        have hstep := hstep12 ⟨k, hk'⟩ hne h12prev
        have heq1 : (⟨k, hk'⟩ : Fin n).succ = ⟨k + 1, hk⟩ := rfl
        have heq2 : (⟨k, hk'⟩ : Fin n).castSucc = ⟨k, by omega⟩ := rfl
        rw [← heq1, hstep, heq2, hprev]
    have hsucc_03 : (x i₀.succ).val = 0 ∨ (x i₀.succ).val = 3 := by
      by_contra hnot
      have hsucc_12 : (x i₀.succ).val = 1 ∨ (x i₀.succ).val = 2 := by
        have := (x i₀.succ).isLt; omega
      have hsuff_eq : ∀ j : Fin (n + 1), i₀.val < j.val → x j = x i₀.succ := by
        intro j hj
        obtain ⟨k, hk⟩ := j
        dsimp at hj
        induction k with
        | zero => omega
        | succ k ih =>
          by_cases hkeq : k = i₀.val
          · have heq : (⟨k + 1, hk⟩ : Fin (n + 1)) = i₀.succ := by ext; simp [hkeq]
            rw [heq]
          · have hk' : k < n := by omega
            have hprev := ih (by omega) (by omega)
            have hne : (⟨k, hk'⟩ : Fin n) ≠ i₀ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
            have h12prev : (x (⟨k, hk'⟩ : Fin n).castSucc).val = 1 ∨
                (x (⟨k, hk'⟩ : Fin n).castSucc).val = 2 := by
              have heq : (⟨k, hk'⟩ : Fin n).castSucc = ⟨k, by omega⟩ := rfl
              rw [heq, hprev]; exact hsucc_12
            have hstep := hstep12 ⟨k, hk'⟩ hne h12prev
            have heq1 : (⟨k, hk'⟩ : Fin n).succ = ⟨k + 1, hk⟩ := rfl
            have heq2 : (⟨k, hk'⟩ : Fin n).castSucc = ⟨k, by omega⟩ := rfl
            rw [← heq1, hstep, heq2, hprev]
      obtain ⟨i₃, hi₃⟩ := hex3
      have hne : i₃ ≠ i₀ := by
        intro h; rw [h] at hi₃; have := (hi₀_iff i₀).mpr rfl; omega
      by_cases hlt : i₃.val < i₀.val
      · have h1 := hpref_eq i₃.castSucc (by simp; omega)
        have h2 := hpref_eq i₃.succ (by simp; omega)
        unfold absDiff at hi₃; rw [h1, h2] at hi₃; simp at hi₃
      · have hgt : i₀.val < i₃.val := by
          have : i₃.val ≠ i₀.val := fun h => hne (Fin.ext h); omega
        have h1 := hsuff_eq i₃.castSucc hgt
        have h2 := hsuff_eq i₃.succ (by simp; omega)
        unfold absDiff at hi₃; rw [h1, h2] at hi₃; simp at hi₃
    have hsuff_03 : ∀ j : Fin (n + 1), i₀.val < j.val → (x j).val = 0 ∨ (x j).val = 3 := by
      intro j hj
      obtain ⟨k, hk⟩ := j
      dsimp at hj
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hkeq : k = i₀.val
        · have heq : (⟨k + 1, hk⟩ : Fin (n + 1)) = i₀.succ := by ext; simp [hkeq]
          rw [heq]; exact hsucc_03
        · have hk' : k < n := by omega
          have hprev := ih (by omega) (by omega)
          have hne : (⟨k, hk'⟩ : Fin n) ≠ i₀ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
          have heq1 : (⟨k, hk'⟩ : Fin n).succ = ⟨k + 1, hk⟩ := rfl
          have heq2 : (⟨k, hk'⟩ : Fin n).castSucc = ⟨k, by omega⟩ := rfl
          rw [← heq1]
          exact (hstep03 ⟨k, hk'⟩ hne).mp (heq2.symm ▸ hprev)
    exact hsuff_03 (Fin.last n) i₀.isLt

private lemma card_bad23L_eq_bad23R (n : ℕ) : (bad23L n).card = (bad23R n).card := by
  let revArr : (Fin (n + 1) → Fin 4) → (Fin (n + 1) → Fin 4) := fun x j => x j.rev
  have hrev_absDiff : ∀ (x : Fin (n + 1) → Fin 4) (i : Fin n),
      absDiff (revArr x) i = absDiff x i.rev := by
    intro x i
    unfold absDiff revArr
    have h1 : i.succ.rev = i.rev.castSucc := by
      ext; simp [Fin.val_rev]
    have h2 : i.castSucc.rev = i.rev.succ := by
      ext; simp [Fin.val_rev]; omega
    rw [h1, h2]
    omega
  have hrev_count : ∀ (x : Fin (n + 1) → Fin 4) (v : ℕ), stepCount (revArr x) v = stepCount x v := by
    intro x v
    unfold stepCount
    refine Finset.card_bij (fun i _ => i.rev) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, by rw [← hrev_absDiff x i]; exact hi.2⟩
    · intro i₁ _ i₂ _ h
      exact Fin.rev_injective h
    · intro j hj
      rw [Finset.mem_filter] at hj
      refine ⟨j.rev, ?_, Fin.rev_rev j⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [hrev_absDiff x j.rev, Fin.rev_rev]; exact hj.2⟩
  have hrev_mem : ∀ x, x ∈ bad23Set n → revArr x ∈ bad23Set n := by
    intro x hx
    rw [bad23Set, Finset.mem_filter] at hx ⊢
    rcases hx.2 with ⟨hpar, h12, h3ge⟩
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · simp only [revArr, Fin.rev_zero, Fin.rev_last]
      exact hpar.symm
    · rw [hrev_count, hrev_count]; exact h12
    · rw [hrev_count]; exact h3ge
  refine Finset.card_bij (fun x _ => revArr x) ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx23, hx0⟩
    rw [bad23R, Finset.mem_filter]
    refine ⟨hrev_mem x hx23, ?_⟩
    obtain ⟨i₀, _, hL, _⟩ := bad23_structure hx23
    have hlast := (hL hx0).2.1 (Fin.last n) i₀.isLt
    simp only [revArr, Fin.rev_zero]
    split_ifs at hlast <;> omega
  · intro x₁ _ x₂ _ h
    funext j
    have := congrFun h j.rev
    simpa [revArr, Fin.rev_rev] using this
  · intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hy23, hy0⟩
    refine ⟨revArr y, ?_, ?_⟩
    · rw [bad23L, Finset.mem_filter]
      refine ⟨hrev_mem y hy23, ?_⟩
      obtain ⟨_, _, _, hR⟩ := bad23_structure hy23
      simp only [revArr, Fin.rev_zero]
      exact hR hy0
    · funext j
      simp [revArr, Fin.rev_rev]

private lemma card_bad23L (n : ℕ) : (bad23L n).card = 2 ^ (n + 1) - 2 * n - 2 := by
  let T : Finset (Σ i₀ : Fin n, Fin (i₀.val + 1) → Bool) :=
    Finset.univ.sigma fun i₀ : Fin n =>
      (Finset.univ : Finset (Fin (i₀.val + 1) → Bool)).filter fun f => ¬ ∀ j, f j = f 0
  have hT_card : T.card = 2 ^ (n + 1) - 2 * n - 2 := by
    rw [Finset.card_sigma]
    have hfiber : ∀ i₀ : Fin n,
        ((Finset.univ : Finset (Fin (i₀.val + 1) → Bool)).filter fun f => ¬ ∀ j, f j = f 0).card =
          2 ^ (i₀.val + 1) - 2 := by
      intro i₀
      have hcomp :
          ((Finset.univ : Finset (Fin (i₀.val + 1) → Bool)).filter fun f => ∀ j, f j = f 0).card +
          ((Finset.univ : Finset (Fin (i₀.val + 1) → Bool)).filter fun f => ¬ ∀ j, f j = f 0).card =
          (Finset.univ : Finset (Fin (i₀.val + 1) → Bool)).card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
        congr 1
        ext f
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact iff_true_intro (em _)
      have hconst_set :
          ((Finset.univ : Finset (Fin (i₀.val + 1) → Bool)).filter fun f => ∀ j, f j = f 0) =
            {fun _ => false, fun _ => true} := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro h
          cases hf0 : f 0
          · left; funext j; rw [h j, hf0]
          · right; funext j; rw [h j, hf0]
        · rintro (rfl | rfl) <;> intro j <;> rfl
      have hne_const : (fun _ : Fin (i₀.val + 1) => false) ≠ (fun _ => true) := by
        intro h
        have := congrFun h 0
        simp at this
      have hconst_card :
          ((Finset.univ : Finset (Fin (i₀.val + 1) → Bool)).filter fun f => ∀ j, f j = f 0).card = 2 := by
        rw [hconst_set, Finset.card_pair hne_const]
      have htot : (Finset.univ : Finset (Fin (i₀.val + 1) → Bool)).card = 2 ^ (i₀.val + 1) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      omega
    simp_rw [hfiber]
    have hsum_range : ∀ m : ℕ, ∑ i : Fin m, (2 ^ (i.val + 1) - 2) = 2 ^ (m + 1) - 2 * m - 2 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih]
        have hge : 2 * m + 2 ≤ 2 ^ (m + 1) := by
          clear ih
          induction m with
          | zero => decide
          | succ k ihk =>
            calc 2 * (k + 1) + 2 ≤ 2 * (2 * k + 2) := by omega
              _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ihk
              _ = 2 ^ (k + 2) := by ring
        rw [pow_succ 2 (m + 1)]
        omega
    exact hsum_range n
  have hbij : T.card = (bad23L n).card := by
    let build : (p : Σ i₀ : Fin n, Fin (i₀.val + 1) → Bool) → (Fin (n + 1) → Fin 4) :=
      fun ⟨i₀, f⟩ j =>
        if hj : j.val ≤ i₀.val then
          if f ⟨j.val, by omega⟩ then 3 else 0
        else
          if f 0 then 1 else 2
    have hbuild_step_i₀ : ∀ (i₀ : Fin n) (f : Fin (i₀.val + 1) → Bool),
        absDiff (build ⟨i₀, f⟩) i₀ = 1 ∨ absDiff (build ⟨i₀, f⟩) i₀ = 2 := by
      intro i₀ f
      unfold absDiff
      have h1 : build ⟨i₀, f⟩ i₀.castSucc = if f ⟨i₀.val, by omega⟩ then 3 else 0 := by
        simp [build]
      have h2 : build ⟨i₀, f⟩ i₀.succ = if f 0 then 1 else 2 := by
        have hnot : ¬ (i₀.val + 1 ≤ i₀.val) := by omega
        simp [build, hnot]
      rw [h1, h2]
      cases f ⟨i₀.val, by omega⟩ <;> cases f 0 <;> decide
    have hbuild_step_other : ∀ (i₀ : Fin n) (f : Fin (i₀.val + 1) → Bool) (i : Fin n),
        i ≠ i₀ → absDiff (build ⟨i₀, f⟩) i = 0 ∨ absDiff (build ⟨i₀, f⟩) i = 3 := by
      intro i₀ f i hne
      unfold absDiff
      by_cases hlt : i.val < i₀.val
      · have h1 : build ⟨i₀, f⟩ i.castSucc = if f ⟨i.val, by omega⟩ then 3 else 0 := by
          simp [build, le_of_lt hlt]
        have h2 : build ⟨i₀, f⟩ i.succ = if f ⟨i.val + 1, by omega⟩ then 3 else 0 := by
          have hle : i.val + 1 ≤ i₀.val := by omega
          simp [build, hle]
        rw [h1, h2]
        cases f ⟨i.val, by omega⟩ <;> cases f ⟨i.val + 1, by omega⟩ <;> decide
      · have hgt : i₀.val < i.val := by
          have : i.val ≠ i₀.val := fun h => hne (Fin.ext h); omega
        have h1 : build ⟨i₀, f⟩ i.castSucc = if f 0 then 1 else 2 := by
          have hnot : ¬ (i.val ≤ i₀.val) := by omega
          simp [build, hnot]
        have h2 : build ⟨i₀, f⟩ i.succ = if f 0 then 1 else 2 := by
          have hnot : ¬ (i.val + 1 ≤ i₀.val) := by omega
          simp [build, hnot]
        rw [h1, h2]
        simp
    refine Finset.card_bij (fun p _ => build p) ?_ ?_ ?_
    · rintro ⟨i₀, f⟩ hp
      have hf_nc : ¬ ∀ j, f j = f 0 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
      have hx0 : build ⟨i₀, f⟩ 0 = if f 0 then 3 else 0 := by
        simp only [build, Fin.val_zero, Nat.zero_le, ↓reduceDIte]
        rfl
      have hxlast : build ⟨i₀, f⟩ (Fin.last n) = if f 0 then 1 else 2 := by
        have hnot : ¬ (n ≤ i₀.val) := not_le.mpr i₀.isLt
        simp [build, hnot]
      have h12_eq : stepCount (build ⟨i₀, f⟩) 1 + stepCount (build ⟨i₀, f⟩) 2 = 1 := by
        have hdisj : Disjoint
            (Finset.univ.filter fun i : Fin n => absDiff (build ⟨i₀, f⟩) i = 1)
            (Finset.univ.filter fun i : Fin n => absDiff (build ⟨i₀, f⟩) i = 2) := by
          rw [Finset.disjoint_left]; intro i h1 h2
          have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
        unfold stepCount
        rw [← Finset.card_union_of_disjoint hdisj]
        have hunion :
            (Finset.univ.filter fun i : Fin n => absDiff (build ⟨i₀, f⟩) i = 1) ∪
            (Finset.univ.filter fun i : Fin n => absDiff (build ⟨i₀, f⟩) i = 2) = {i₀} := by
          ext i
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          constructor
          · intro h
            by_contra hne
            have ho := hbuild_step_other i₀ f i hne
            omega
          · rintro rfl; exact hbuild_step_i₀ i f
        rw [hunion, Finset.card_singleton]
      have h3ge : 1 ≤ stepCount (build ⟨i₀, f⟩) 3 := by
        have hex_flip : ∃ (i : Fin n) (h : i.val < i₀.val),
            f ⟨i.val + 1, by omega⟩ ≠ f ⟨i.val, by omega⟩ := by
          by_contra hall
          push Not at hall
          apply hf_nc
          intro j
          obtain ⟨k, hk⟩ := j
          induction k with
          | zero => rfl
          | succ k ih =>
            have hk' : k < i₀.val := by omega
            have h1 := hall ⟨k, by omega⟩ hk'
            exact h1.trans (ih (by omega))
        obtain ⟨i, hilt, hflip⟩ := hex_flip
        have hi3 : absDiff (build ⟨i₀, f⟩) i = 3 := by
          unfold absDiff
          have h1 : build ⟨i₀, f⟩ i.castSucc = if f ⟨i.val, by omega⟩ then 3 else 0 := by
            simp [build, le_of_lt hilt]
          have h2 : build ⟨i₀, f⟩ i.succ = if f ⟨i.val + 1, by omega⟩ then 3 else 0 := by
            have hle : i.val + 1 ≤ i₀.val := by omega
            simp [build, hle]
          rw [h1, h2]
          cases ha : f ⟨i.val, by omega⟩ <;> cases hb : f ⟨i.val + 1, by omega⟩
          · exact absurd (hb.trans ha.symm) hflip
          · decide
          · decide
          · exact absurd (hb.trans ha.symm) hflip
        unfold stepCount
        exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi3⟩⟩
      rw [bad23L, Finset.mem_filter, bad23Set, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_, h12_eq, h3ge⟩, ?_⟩
      · rw [hx0, hxlast]; cases f 0 <;> decide
      · rw [hx0]; cases f 0 <;> decide
    · rintro ⟨i₁, f₁⟩ hp₁ ⟨i₂, f₂⟩ hp₂ heq
      have hi_eq : i₁ = i₂ := by
        by_contra hne
        have h1 := hbuild_step_i₀ i₁ f₁
        rw [heq] at h1
        have h2 := hbuild_step_other i₂ f₂ i₁ hne
        omega
      subst hi_eq
      congr 1
      funext j
      have hj := congrFun heq ⟨j.val, by omega⟩
      have hle : j.val ≤ i₁.val := by omega
      simp only [build, hle, ↓reduceDIte] at hj
      cases ha : f₁ j <;> cases hb : f₂ j <;> simp [ha, hb] at hj ⊢
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hx23, hx0⟩
      obtain ⟨i₀, _, hL, _⟩ := bad23_structure hx23
      obtain ⟨hpref, hsuff, i₃, hi₃_lt, hi₃_eq⟩ := hL hx0
      let f : Fin (i₀.val + 1) → Bool := fun j => decide ((x ⟨j.val, by omega⟩).val = 3)
      have hf_nc : ¬ ∀ j, f j = f 0 := by
        intro hall
        have ha := hall ⟨i₃.val, by omega⟩
        have hb := hall ⟨i₃.val + 1, by omega⟩
        have hsame : f ⟨i₃.val, by omega⟩ = f ⟨i₃.val + 1, by omega⟩ := ha.trans hb.symm
        have h1 := hpref i₃.castSucc (by simp; omega)
        have h2 := hpref i₃.succ (by simp; omega)
        change decide ((x i₃.castSucc).val = 3) = decide ((x i₃.succ).val = 3) at hsame
        unfold absDiff at hi₃_eq
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · simp [h1, h2] at hi₃_eq
        · simp [h1, h2] at hsame
        · simp [h1, h2] at hsame
        · simp [h1, h2] at hi₃_eq
      refine ⟨⟨i₀, f⟩, ?_, ?_⟩
      · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf_nc⟩⟩
      · funext j
        apply Fin.ext
        by_cases hj : j.val ≤ i₀.val
        · simp only [build, hj, ↓reduceDIte, f]
          have hp := hpref j hj
          have hjeq : (x ⟨j.val, by omega⟩).val = (x j).val :=
            congrArg (fun idx => (x idx).val) (show (⟨j.val, by omega⟩ : Fin (n + 1)) = j from by ext; rfl)
          simp only [hjeq]
          rcases hp with hp | hp <;> simp [hp]
        · have hgt : i₀.val < j.val := by omega
          simp only [build, hj, ↓reduceDIte, f]
          have hs := hsuff j hgt
          have h0eq : (x ⟨(0 : Fin (i₀.val + 1)).val, by omega⟩).val = (x 0).val :=
            congrArg (fun idx => (x idx).val) (show (⟨(0 : Fin (i₀.val + 1)).val, by omega⟩ : Fin (n + 1)) = 0 from by ext; rfl)
          simp only [h0eq]
          rcases hx0 with hx0 | hx0 <;> simp [hx0, hs]
  rw [← hbij, hT_card]

private lemma card_bad23Set (n : ℕ) : (bad23Set n).card = 4 * 2 ^ n - 4 * n - 4 := by
  have hunion : bad23Set n = bad23L n ∪ bad23R n := by
    ext x
    simp only [bad23L, bad23R, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      have hlt := (x 0).isLt
      by_cases h03 : (x 0).val = 0 ∨ (x 0).val = 3
      · exact Or.inl ⟨hx, h03⟩
      · exact Or.inr ⟨hx, by omega⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hdisj : Disjoint (bad23L n) (bad23R n) := by
    rw [Finset.disjoint_left]
    intro x hL hR
    have h1 := (Finset.mem_filter.mp hL).2
    have h2 := (Finset.mem_filter.mp hR).2
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj, ← card_bad23L_eq_bad23R, card_bad23L]
  have hge : ∀ m : ℕ, 2 * m + 2 ≤ 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => decide
    | succ k ih =>
      calc 2 * (k + 1) + 2 ≤ 2 * (2 * k + 2) := by omega
        _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 2) := by ring
  have hge_n := hge n
  rw [pow_succ 2 n] at hge_n ⊢
  omega

private lemma a_closed_form (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) = 2 * (2 - 3 * 2 ^ n + 4 ^ n + 2 * n) := by
  let goodSet := Finset.univ.filter fun x : Fin (n + 1) → Fin 4 => SignedSumZero x
  have hdisj_bad : Disjoint (bad1Set n) (bad23Set n) := by
    rw [Finset.disjoint_left]
    intro x h1 h23
    have hb1 := (Finset.mem_filter.mp h1).2
    have hb23 := (Finset.mem_filter.mp h23).2
    omega
  have hdisj_good : Disjoint goodSet (bad1Set n ∪ bad23Set n) := by
    rw [Finset.disjoint_left]
    intro x hgood hbad
    have hg := (signedSumZero_iff_counts x).mp (Finset.mem_filter.mp hgood).2
    rcases Finset.mem_union.mp hbad with h1 | h23
    · exact hg.2.1 (Finset.mem_filter.mp h1).2
    · exact hg.2.2 (Finset.mem_filter.mp h23).2.2
  have hunion_even : evenSet n = goodSet ∪ (bad1Set n ∪ bad23Set n) := by
    ext x
    simp only [evenSet, goodSet, bad1Set, bad23Set, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [signedSumZero_iff_counts, parity_iff_endpoints]
    constructor
    · intro hpar
      by_cases h1 : stepCount x 1 = 0 ∧ stepCount x 3 = 0 ∧ stepCount x 2 % 2 = 1
      · exact Or.inr (Or.inl h1)
      · by_cases h23 : stepCount x 1 + stepCount x 2 = 1 ∧ 1 ≤ stepCount x 3
        · exact Or.inr (Or.inr ⟨hpar, h23⟩)
        · exact Or.inl ⟨hpar, h1, h23⟩
    · rintro (⟨hpar, _, _⟩ | ⟨h1, h3, _⟩ | ⟨hpar, _⟩)
      · exact hpar
      · exact (parity_iff_endpoints x).mp (by omega)
      · exact hpar
  have hcard_eq : (evenSet n).card = a n + (bad1Set n).card + (bad23Set n).card := by
    change (evenSet n).card = goodSet.card + (bad1Set n).card + (bad23Set n).card
    rw [hunion_even, Finset.card_union_of_disjoint hdisj_good,
      Finset.card_union_of_disjoint hdisj_bad]
    omega
  rw [card_evenSet n hn, card_bad1Set n hn, card_bad23Set n] at hcard_eq
  have hge : ∀ m : ℕ, 4 * m + 4 ≤ 4 * 2 ^ m := by
    intro m
    induction m with
    | zero => decide
    | succ k ih =>
      calc 4 * (k + 1) + 4 ≤ 2 * (4 * k + 4) := by omega
        _ ≤ 2 * (4 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
        _ = 4 * 2 ^ (k + 1) := by ring
  have hge_n := hge n
  have hnat : 2 * 4 ^ n + 4 * n + 4 = a n + 2 ^ (n + 1) + 4 * 2 ^ n := by omega
  have hz : ((2 * 4 ^ n + 4 * n + 4 : ℕ) : ℤ) = ((a n + 2 ^ (n + 1) + 4 * 2 ^ n : ℕ) : ℤ) :=
    congrArg Nat.cast hnat
  push_cast at hz
  have hpow : (2 : ℤ) ^ (n + 1) = 2 * (2 : ℤ) ^ n := by ring
  linarith

private lemma gf_identity :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
      4 * PowerSeries.X * (1 - 3 * PowerSeries.X + 5 * PowerSeries.X ^ 2) := by
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have hlhs : F * ((1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
      F - 8 * (PowerSeries.X * F) + 21 * (PowerSeries.X ^ 2 * F) -
      22 * (PowerSeries.X ^ 3 * F) + 8 * (PowerSeries.X ^ 4 * F) := by
    ring
  have hrhs : (4 * PowerSeries.X * (1 - 3 * PowerSeries.X + 5 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
      4 * (PowerSeries.X * 1) - 12 * (PowerSeries.X ^ 2 * 1) + 20 * (PowerSeries.X ^ 3 * 1) := by
    ring
  change F * ((1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) = _
  rw [hlhs, hrhs]
  have hcf : ∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n F = 2 * (2 - 3 * 2 ^ n + 4 ^ n + 2 * (n : ℚ)) := by
    intro n hn
    have hne : n ≠ 0 := by omega
    have hz := a_closed_form n hn
    have hq : (a n : ℚ) = 2 * (2 - 3 * 2 ^ n + 4 ^ n + 2 * (n : ℚ)) := by
      exact_mod_cast hz
    simp only [F, PowerSeries.coeff_mk, hne, ↓reduceIte]
    exact hq
  have hcf0 : PowerSeries.coeff 0 F = 0 := by
    simp [F, PowerSeries.coeff_mk]
  ext n
  have hX1 : PowerSeries.X * F = PowerSeries.X ^ 1 * F := by ring
  have hX1' : (PowerSeries.X * (1 : PowerSeries ℚ)) = PowerSeries.X ^ 1 * 1 := by ring
  rw [hX1, hX1']
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    show (8 : PowerSeries ℚ) = PowerSeries.C 8 from rfl,
    show (21 : PowerSeries ℚ) = PowerSeries.C 21 from rfl,
    show (22 : PowerSeries ℚ) = PowerSeries.C 22 from rfl,
    show (4 : PowerSeries ℚ) = PowerSeries.C 4 from rfl,
    show (12 : PowerSeries ℚ) = PowerSeries.C 12 from rfl,
    show (20 : PowerSeries ℚ) = PowerSeries.C 20 from rfl,
    PowerSeries.coeff_X_pow_mul']
  match n with
  | 0 => simp [hcf0]
  | 1 =>
    have h1 := hcf 1 (by omega)
    norm_num [hcf0, h1, PowerSeries.coeff_one]
  | 2 =>
    have h1 := hcf 1 (by omega)
    have h2 := hcf 2 (by omega)
    norm_num [hcf0, h1, h2, PowerSeries.coeff_one]
  | 3 =>
    have h1 := hcf 1 (by omega)
    have h2 := hcf 2 (by omega)
    have h3 := hcf 3 (by omega)
    norm_num [hcf0, h1, h2, h3, PowerSeries.coeff_one]
  | 4 =>
    have h1 := hcf 1 (by omega)
    have h2 := hcf 2 (by omega)
    have h3 := hcf 3 (by omega)
    have h4 := hcf 4 (by omega)
    norm_num [hcf0, h1, h2, h3, h4, PowerSeries.coeff_one]
  | m + 5 =>
    have h1 := hcf (m + 1) (by omega)
    have h2 := hcf (m + 2) (by omega)
    have h3 := hcf (m + 3) (by omega)
    have h4 := hcf (m + 4) (by omega)
    have h5 := hcf (m + 5) (by omega)
    simp only [show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega,
      show 4 ≤ m + 5 by omega, ↓reduceIte,
      show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
      PowerSeries.coeff_one,
      show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega]
    rw [h1, h2, h3, h4, h5]
    push_cast
    ring

end OeisA250162

theorem OMA.solution : type_of% @OMA.S_oeis_a250162.main :=
  ⟨OeisA250162.gf_identity, OeisA250162.a_closed_form⟩
