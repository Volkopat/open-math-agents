import OMAStatements.S_oeis_a204565

-- Problem: A204565: Number of (n+1) x 2 0..3 arrays with every 2x2 subblock having equal diagonal or
-- equal antidiagonal elements, and new values 0..3 introduced in row-major order.
-- Credit: @ceejcake
-- Proof: Partition valid (n+1) x 2 arrays by maximum entry k ∈ Fin 4. Extending by one row gives
-- exact transition counts independent of the last row: (1,2) from 0, (3,2) from 1, (5,2) from 2, 7 from 3.

namespace ProofA204565

open OMA.S_oeis_a204565
open scoped Classical
noncomputable section

private def validSet (n : ℕ) : Finset (Fin (n + 1) → Fin 2 → Fin 4) :=
  Finset.univ.filter (isValid n)

private def validMax (n : ℕ) (k : Fin 4) : Finset (Fin (n + 1) → Fin 2 → Fin 4) :=
  (validSet n).filter (fun A => (∀ i j, A i j ≤ k) ∧ (∃ i j, A i j = k))

-- Partition validSet n by maximum entry k : Fin 4
private lemma card_valid_eq_sum (n : ℕ) :
    (validSet n).card =
      (validMax n 0).card + (validMax n 1).card + (validMax n 2).card + (validMax n 3).card := by
  have hunion : validSet n = validMax n 0 ∪ validMax n 1 ∪ validMax n 2 ∪ validMax n 3 := by
    ext A
    simp only [Finset.mem_union, validMax, Finset.mem_filter]
    constructor
    · intro hA
      let img := (Finset.univ : Finset (Fin (n + 1) × Fin 2)).image (fun p => A p.1 p.2)
      have hne : img.Nonempty := ⟨A 0 0, Finset.mem_image_of_mem _ (Finset.mem_univ (0, 0))⟩
      obtain ⟨m, hm_eq⟩ : ∃ m : Fin 4, m = img.max' hne := ⟨_, rfl⟩
      have hm_mem : m ∈ img := hm_eq ▸ Finset.max'_mem _ hne
      rcases Finset.mem_image.mp hm_mem with ⟨⟨i0, j0⟩, _, hij0⟩
      have hm_le : ∀ i j, A i j ≤ m := fun i j =>
        hm_eq ▸ Finset.le_max' img (A i j)
          (Finset.mem_image_of_mem (fun p : Fin (n + 1) × Fin 2 => A p.1 p.2) (Finset.mem_univ (i, j)))
      fin_cases m
      · exact Or.inl (Or.inl (Or.inl ⟨hA, hm_le, ⟨i0, j0, hij0⟩⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hA, hm_le, ⟨i0, j0, hij0⟩⟩))
      · exact Or.inl (Or.inr ⟨hA, hm_le, ⟨i0, j0, hij0⟩⟩)
      · exact Or.inr ⟨hA, hm_le, ⟨i0, j0, hij0⟩⟩
    · rintro (((h | h) | h) | h) <;> exact h.1
  have hdisj : ∀ j k : Fin 4, j ≠ k → Disjoint (validMax n j) (validMax n k) := by
    intro j k hjk
    rw [Finset.disjoint_left]; intro A hj hk
    simp only [validMax, Finset.mem_filter] at hj hk
    rcases hj.2.2 with ⟨i1, j1, h1⟩; rcases hk.2.2 with ⟨i2, j2, h2⟩
    exact hjk (le_antisymm (h1 ▸ hk.2.1 i1 j1) (h2 ▸ hj.2.1 i2 j2))
  rw [hunion]
  rw [Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
        exact ⟨⟨hdisj 0 3 (by decide), hdisj 1 3 (by decide)⟩, hdisj 2 3 (by decide)⟩)]
  rw [Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_union_left]
        exact ⟨hdisj 0 2 (by decide), hdisj 1 2 (by decide)⟩)]
  rw [Finset.card_union_of_disjoint (hdisj 0 1 (by decide))]

-- Helper: append a row (c, d) to an (n+1) x 2 array A
private def snocRow {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 4) (c d : Fin 4) :
    Fin (n + 2) → Fin 2 → Fin 4 :=
  fun i j => if h : i.1 < n + 1 then A ⟨i.1, h⟩ j else if j = 0 then c else d

private lemma snocRow_castSucc {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 4) (c d : Fin 4)
    (i : Fin (n + 1)) (j : Fin 2) :
    snocRow A c d i.castSucc j = A i j := by
  simp only [snocRow, Fin.val_castSucc, i.2, ↓reduceDIte]

private lemma snocRow_last0 {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 4) (c d : Fin 4) :
    snocRow A c d (Fin.last (n + 1)) 0 = c := by
  simp only [snocRow, Fin.val_last, lt_irrefl, ↓reduceDIte, ↓reduceIte]

private lemma snocRow_last1 {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 4) (c d : Fin 4) :
    snocRow A c d (Fin.last (n + 1)) 1 = d := by
  simp only [snocRow, Fin.val_last, lt_irrefl, ↓reduceDIte]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [if_neg h10]

-- Valid next rows (c, d) staying ≤ k given last row (a, b) with a, b ≤ k
private def sameNext (k a b : Fin 4) : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter (fun p => (p.1 = b ∨ p.2 = a) ∧ p.1 ≤ k ∧ p.2 ≤ k)

private lemma card_sameNext (k a b : Fin 4) (ha : a ≤ k) (hb : b ≤ k) :
    (sameNext k a b).card = 2 * k.1 + 1 := by
  revert ha hb; fin_cases k <;> fin_cases a <;> fin_cases b <;> decide

-- Valid next rows (c, d) introducing k (with k > 0) given last row (a, b) with a, b ≤ k - 1
private def upNext (k a b : Fin 4) : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter (fun p => (p.1 = b ∨ p.2 = a) ∧ p.1 ≤ k ∧ p.2 ≤ k ∧ (p.1 = k ∨ p.2 = k))

private lemma card_upNext (k a b : Fin 4) (hk : 0 < k.1) (ha : a.1 ≤ k.1 - 1) (hb : b.1 ≤ k.1 - 1) :
    (upNext k a b).card = 2 := by
  revert hk ha hb; fin_cases k <;> fin_cases a <;> fin_cases b <;> decide

-- State 0: always 1 array (all zeros)
private lemma card_validMax_zero (n : ℕ) : (validMax n 0).card = 1 := by
  have h : validMax n 0 = {fun _ _ => 0} := by
    ext A
    simp only [validMax, validSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hle, _⟩
      funext i j
      exact Fin.le_zero_iff.mp (hle i j)
    · rintro rfl
      refine ⟨⟨fun _ => Or.inl rfl, fun _ _ v hv => by dsimp only at hv; exact absurd hv (by omega)⟩,
              fun _ _ => le_rfl, ⟨0, 0, rfl⟩⟩
  rw [h, Finset.card_singleton]

-- Recurrence step for validMax (n + 1) k when k > 0:
-- |validMax (n+1) k| = (2*k + 1) * |validMax n k| + 2 * |validMax n (k - 1)|
private lemma card_validMax_succ (n : ℕ) (k : Fin 4) (hk : 0 < k.1) :
    (validMax (n + 1) k).card =
      (2 * k.1 + 1) * (validMax n k).card + 2 * (validMax n ⟨k.1 - 1, by omega⟩).card := by
  let prevK : Fin 4 := ⟨k.1 - 1, by omega⟩
  let S1 := (validMax (n + 1) k).filter (fun A => ∃ (i : Fin (n + 1)) (j : Fin 2), A i.castSucc j = k)
  let S2 := (validMax (n + 1) k).filter (fun A => ¬ ∃ (i : Fin (n + 1)) (j : Fin 2), A i.castSucc j = k)
  have hsplit : validMax (n + 1) k = S1 ∪ S2 := by
    ext A; simp only [S1, S2, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      by_cases hx : ∃ (i : Fin (n + 1)) (j : Fin 2), A i.castSucc j = k
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, hx⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro A h1 h2
    simp only [S1, S2, Finset.mem_filter] at h1 h2; exact h2.2 h1.2
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  -- Helper: prefix of a valid (n+2) x 2 array is valid (n+1) x 2
  have hpref_valid : ∀ A : Fin (n + 2) → Fin 2 → Fin 4, isValid (n + 1) A →
      isValid n (fun i j => A i.castSucc j) := by
    intro A hA
    refine ⟨fun i => ?_, fun i j v hv => ?_⟩
    · have h := hA.1 i.castSucc
      simpa only [Fin.succ_castSucc] using h
    · rcases hA.2 i.castSucc j v hv with ⟨i', j', hlt, heq⟩
      simp only [Fin.val_castSucc] at hlt
      exact ⟨⟨i'.1, by omega⟩, j', by dsimp only; omega, heq⟩
  -- Part 1: S1 ↔ Σ A ∈ validMax n k, sameNext k (A (Fin.last n) 0) (A (Fin.last n) 1)
  have hc1 : S1.card = (2 * k.1 + 1) * (validMax n k).card := by
    let T1 := (validMax n k).sigma (fun A => sameNext k (A (Fin.last n) 0) (A (Fin.last n) 1))
    have hT1 : T1.card = (2 * k.1 + 1) * (validMax n k).card := by
      rw [Finset.card_sigma]
      have hcongr : ∀ A ∈ validMax n k,
          (sameNext k (A (Fin.last n) 0) (A (Fin.last n) 1)).card = 2 * k.1 + 1 := by
        intro A hA
        simp only [validMax, Finset.mem_filter] at hA
        exact card_sameNext k _ _ (hA.2.1 (Fin.last n) 0) (hA.2.1 (Fin.last n) 1)
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [← hT1]
    refine Finset.card_bij
      (fun A _ => ⟨fun i j => A i.castSucc j, (A (Fin.last (n + 1)) 0, A (Fin.last (n + 1)) 1)⟩) ?_ ?_ ?_
    · intro A hA
      simp only [S1, validMax, validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      simp only [T1, Finset.mem_sigma, validMax, validSet, sameNext, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨⟨hpref_valid A hA.1.1, fun i j => hA.1.2.1 i.castSucc j, hA.2⟩, ?_,
              hA.1.2.1 (Fin.last (n + 1)) 0, hA.1.2.1 (Fin.last (n + 1)) 1⟩
      have hlast := hA.1.1.1 (Fin.last n)
      have hs : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
      rw [hs] at hlast
      rcases hlast with h | h
      · exact Or.inr h.symm
      · exact Or.inl h.symm
    · intro A1 _ A2 _ h
      simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at h
      rcases h with ⟨hp, h0, h1⟩
      funext i j
      by_cases hi : i.1 < n + 1
      · exact congr_fun (congr_fun hp ⟨i.1, hi⟩) j
      · have hlast : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
        rw [hlast]
        fin_cases j
        · exact h0
        · exact h1
    · intro ⟨A, c, d⟩ hA
      simp only [T1, Finset.mem_sigma, validMax, validSet, sameNext, Finset.mem_filter,
        Finset.mem_univ, true_and] at hA
      rcases hA with ⟨⟨hAv, hAle, hAhit⟩, hdiag, hc, hd⟩
      refine ⟨snocRow A c d, ?_, ?_⟩
      · simp only [S1, validMax, validSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨⟨fun i => ?_, fun i j v hv => ?_⟩, fun i j => ?_, ?_⟩, ?_⟩
        · by_cases hi : i.1 < n
          · have h1 : i.castSucc = (⟨i.1, hi⟩ : Fin n).castSucc.castSucc := Fin.ext (by simp)
            have h2 : i.succ = (⟨i.1, hi⟩ : Fin n).succ.castSucc := Fin.ext (by simp)
            rw [h1, h2, snocRow_castSucc, snocRow_castSucc, snocRow_castSucc, snocRow_castSucc]
            exact hAv.1 ⟨i.1, hi⟩
          · have hlast : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
            rw [hlast, Fin.succ_last, snocRow_castSucc, snocRow_castSucc, snocRow_last0, snocRow_last1]
            rcases hdiag with h | h
            · exact Or.inr h.symm
            · exact Or.inl h.symm
        · by_cases hi : i.1 < n + 1
          · simp only [snocRow, hi, ↓reduceDIte] at hv
            rcases hAv.2 ⟨i.1, hi⟩ j v hv with ⟨i', j', hlt, heq⟩
            exact ⟨i'.castSucc, j', by simp only [Fin.val_castSucc]; exact hlt, by rw [snocRow_castSucc]; exact heq⟩
          · have hlast : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
            rw [hlast] at hv
            have hvk : v < k := by
              match j with
              | 0 => rw [snocRow_last0] at hv; exact lt_of_lt_of_le hv hc
              | 1 => rw [snocRow_last1] at hv; exact lt_of_lt_of_le hv hd
            rcases hAhit with ⟨i0, j0, hij0⟩
            rcases hAv.2 i0 j0 v (hij0.symm ▸ hvk) with ⟨i', j', _, heq⟩
            exact ⟨i'.castSucc, j', by simp only [Fin.val_castSucc]; omega, by rw [snocRow_castSucc]; exact heq⟩
        · by_cases hi : i.1 < n + 1
          · simp only [snocRow, hi, ↓reduceDIte]; exact hAle ⟨i.1, hi⟩ j
          · have hlast : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
            rw [hlast]
            match j with
            | 0 => rw [snocRow_last0]; exact hc
            | 1 => rw [snocRow_last1]; exact hd
        · rcases hAhit with ⟨i0, j0, hij0⟩
          exact ⟨i0.castSucc, j0, by rw [snocRow_castSucc]; exact hij0⟩
        · rcases hAhit with ⟨i0, j0, hij0⟩
          exact ⟨i0, j0, by rw [snocRow_castSucc]; exact hij0⟩
      · simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, snocRow_last0, snocRow_last1,
          and_true, true_and]
        funext i j; exact snocRow_castSucc A c d i j
  -- Part 2: S2 ↔ Σ A ∈ validMax n prevK, upNext k (A (Fin.last n) 0) (A (Fin.last n) 1)
  have hc2 : S2.card = 2 * (validMax n prevK).card := by
    let T2 := (validMax n prevK).sigma (fun A => upNext k (A (Fin.last n) 0) (A (Fin.last n) 1))
    have hT2 : T2.card = 2 * (validMax n prevK).card := by
      rw [Finset.card_sigma]
      have hcongr : ∀ A ∈ validMax n prevK,
          (upNext k (A (Fin.last n) 0) (A (Fin.last n) 1)).card = 2 := by
        intro A hA
        simp only [validMax, Finset.mem_filter] at hA
        exact card_upNext k _ _ hk (hA.2.1 (Fin.last n) 0) (hA.2.1 (Fin.last n) 1)
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [← hT2]
    refine Finset.card_bij
      (fun A _ => ⟨fun i j => A i.castSucc j, (A (Fin.last (n + 1)) 0, A (Fin.last (n + 1)) 1)⟩) ?_ ?_ ?_
    · intro A hA
      simp only [S2, validMax, validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      simp only [T2, Finset.mem_sigma, validMax, validSet, upNext, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hlast_hit : A (Fin.last (n + 1)) 0 = k ∨ A (Fin.last (n + 1)) 1 = k := by
        rcases hA.1.2.2 with ⟨i0, j0, hij0⟩
        by_cases hi : i0.1 < n + 1
        · exact absurd ⟨⟨i0.1, hi⟩, j0, hij0⟩ hA.2
        · have : i0 = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
          rw [this] at hij0
          fin_cases j0
          · exact Or.inl hij0
          · exact Or.inr hij0
      have hpref_le : ∀ (i : Fin (n + 1)) (j : Fin 2), A i.castSucc j ≤ prevK := by
        intro i j
        have hle := hA.1.2.1 i.castSucc j
        have hne : A i.castSucc j ≠ k := fun h => hA.2 ⟨i, j, h⟩
        have hlt : (A i.castSucc j).1 < k.1 := lt_of_le_of_ne hle (fun h => hne (Fin.ext h))
        change (A i.castSucc j).1 ≤ k.1 - 1; omega
      have hpref_hit : ∃ (i : Fin (n + 1)) (j : Fin 2), A i.castSucc j = prevK := by
        have hlt : prevK < k := by change k.1 - 1 < k.1; omega
        rcases hlast_hit with h0 | h1
        · rcases hA.1.1.2 (Fin.last (n + 1)) 0 prevK (h0.symm ▸ hlt) with ⟨i', j', hlt', heq⟩
          simp only [Fin.val_last] at hlt'
          exact ⟨⟨i'.1, by omega⟩, j', heq⟩
        · rcases hA.1.1.2 (Fin.last (n + 1)) 1 prevK (h1.symm ▸ hlt) with ⟨i', j', hlt', heq⟩
          simp only [Fin.val_last] at hlt'
          by_cases hi' : i'.1 < n + 1
          · exact ⟨⟨i'.1, hi'⟩, j', heq⟩
          · -- If i' = last, then j' = 0 and A last 0 = prevK, wait: since A last 0 = A last_prev 1 or A last 1 = A last_prev 0
            -- Wait: A last 1 = k > prevK and A last_prev 0 ≤ prevK, so A last 1 ≠ A last_prev 0!
            -- Therefore by 2x2 subblock condition, A last 0 = A last_prev 1!
            -- So A last_prev 1 = prevK!
            have hi'last : i' = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
            have hj'0 : j' = 0 := Fin.ext (by omega)
            rw [hi'last, hj'0] at heq
            have hsub := hA.1.1.1 (Fin.last n)
            rw [Fin.succ_last] at hsub
            rcases hsub with hd | ha
            · have hle0 := hpref_le (Fin.last n) 0
              rw [hd, h1] at hle0
              change k.1 ≤ k.1 - 1 at hle0; omega
            · exact ⟨Fin.last n, 1, ha.trans heq⟩
      refine ⟨⟨hpref_valid A hA.1.1, hpref_le, hpref_hit⟩, ?_,
              hA.1.2.1 (Fin.last (n + 1)) 0, hA.1.2.1 (Fin.last (n + 1)) 1, hlast_hit⟩
      have hlast := hA.1.1.1 (Fin.last n)
      rw [Fin.succ_last] at hlast
      rcases hlast with h | h
      · exact Or.inr h.symm
      · exact Or.inl h.symm
    · intro A1 _ A2 _ h
      simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at h
      rcases h with ⟨hp, h0, h1⟩
      funext i j
      by_cases hi : i.1 < n + 1
      · exact congr_fun (congr_fun hp ⟨i.1, hi⟩) j
      · have hlast : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
        rw [hlast]
        fin_cases j
        · exact h0
        · exact h1
    · intro ⟨A, c, d⟩ hA
      simp only [T2, Finset.mem_sigma, validMax, validSet, upNext, Finset.mem_filter,
        Finset.mem_univ, true_and] at hA
      rcases hA with ⟨⟨hAv, hAle, hAhit⟩, hdiag, hc, hd, hcd⟩
      refine ⟨snocRow A c d, ?_, ?_⟩
      · simp only [S2, validMax, validSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨⟨fun i => ?_, fun i j v hv => ?_⟩, fun i j => ?_, ?_⟩, ?_⟩
        · by_cases hi : i.1 < n
          · have h1 : i.castSucc = (⟨i.1, hi⟩ : Fin n).castSucc.castSucc := Fin.ext (by simp)
            have h2 : i.succ = (⟨i.1, hi⟩ : Fin n).succ.castSucc := Fin.ext (by simp)
            rw [h1, h2, snocRow_castSucc, snocRow_castSucc, snocRow_castSucc, snocRow_castSucc]
            exact hAv.1 ⟨i.1, hi⟩
          · have hlast : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
            rw [hlast, Fin.succ_last, snocRow_castSucc, snocRow_castSucc, snocRow_last0, snocRow_last1]
            rcases hdiag with h | h
            · exact Or.inr h.symm
            · exact Or.inl h.symm
        · by_cases hi : i.1 < n + 1
          · simp only [snocRow, hi, ↓reduceDIte] at hv
            rcases hAv.2 ⟨i.1, hi⟩ j v hv with ⟨i', j', hlt, heq⟩
            exact ⟨i'.castSucc, j', by simp only [Fin.val_castSucc]; exact hlt, by rw [snocRow_castSucc]; exact heq⟩
          · have hlast : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
            rw [hlast] at hv
            have hvle : v ≤ prevK := by
              have hlt : v < k := by
                match j with
                | 0 => rw [snocRow_last0] at hv; exact lt_of_lt_of_le hv hc
                | 1 => rw [snocRow_last1] at hv; exact lt_of_lt_of_le hv hd
              change v.1 ≤ k.1 - 1; change v.1 < k.1 at hlt; omega
            rcases hAhit with ⟨i0, j0, hij0⟩
            by_cases hvprev : v = prevK
            · exact ⟨i0.castSucc, j0, by simp only [Fin.val_castSucc]; omega, by rw [snocRow_castSucc, hij0, hvprev]⟩
            · have hlt : v < A i0 j0 := by
                rw [hij0]
                exact lt_of_le_of_ne hvle hvprev
              rcases hAv.2 i0 j0 v hlt with ⟨i', j', _, heq⟩
              exact ⟨i'.castSucc, j', by simp only [Fin.val_castSucc]; omega, by rw [snocRow_castSucc]; exact heq⟩
        · by_cases hi : i.1 < n + 1
          · simp only [snocRow, hi, ↓reduceDIte]
            have h := hAle ⟨i.1, hi⟩ j
            change (A ⟨i.1, hi⟩ j).1 ≤ k.1
            change (A ⟨i.1, hi⟩ j).1 ≤ k.1 - 1 at h; omega
          · have hlast : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
            rw [hlast]
            match j with
            | 0 => rw [snocRow_last0]; exact hc
            | 1 => rw [snocRow_last1]; exact hd
        · rcases hcd with hck | hdk
          · exact ⟨Fin.last (n + 1), 0, (snocRow_last0 A c d).trans hck⟩
          · exact ⟨Fin.last (n + 1), 1, (snocRow_last1 A c d).trans hdk⟩
        · rintro ⟨i, j, hij⟩
          rw [snocRow_castSucc] at hij
          have h := hAle i j
          rw [hij] at h
          change k.1 ≤ k.1 - 1 at h; omega
      · simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, snocRow_last0, snocRow_last1,
          and_true, true_and]
        funext i j; exact snocRow_castSucc A c d i j
  rw [hc1, hc2]

-- Closed forms for all 4 states by induction on n
private lemma validMax_formulas (n : ℕ) :
    (validMax n 0).card = 1 ∧
    (validMax n 1).card + 1 = 2 * 3 ^ n ∧
    2 * (validMax n 2).card + 4 * 3 ^ n = 3 * 5 ^ n + 1 ∧
    6 * (validMax n 3).card + 9 * 5 ^ n + 1 = 4 * 7 ^ n + 6 * 3 ^ n := by
  induction n with
  | zero =>
    have h0 : (validMax 0 0).card = 1 := card_validMax_zero 0
    have h1 : (validMax 0 1).card = 1 := by
      have h : validMax 0 1 = {fun _ j => if j = 0 then 0 else 1} := by
        ext A
        simp only [validMax, validSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨_, hrgs⟩, hle, ⟨i0, j0, hij0⟩⟩
          have h00 : A 0 0 = 0 := by
            by_contra hne
            have hlt : (0 : Fin 4) < A 0 0 := Fin.pos_of_ne_zero hne
            rcases hrgs 0 0 0 hlt with ⟨i', j', hlt', _⟩
            have : i'.1 = 0 := by omega
            omega
          have hi0 : i0 = 0 := Fin.eq_zero i0
          rw [hi0] at hij0
          have hj0 : j0 = 1 := by
            match j0 with
            | 0 => rw [h00] at hij0; exact absurd hij0 (by decide)
            | 1 => rfl
          rw [hj0] at hij0
          funext i j
          have hi : i = 0 := Fin.eq_zero i
          rw [hi]
          match j with
          | 0 => exact h00
          | 1 => exact hij0
        · rintro rfl
          refine ⟨⟨fun i => Fin.elim0 i, fun i j v hv => ?_⟩, fun i j => ?_, ⟨0, 1, by decide⟩⟩
          · match j with
            | 0 => simp at hv
            | 1 =>
              have hv1 : v < (1 : Fin 4) := by simpa using hv
              have hv0 : v = 0 := Fin.ext (by change v.1 < 1 at hv1; omega)
              exact ⟨i, 0, by omega, by simp [hv0]⟩
          · match j with
            | 0 => simp
            | 1 => simp
      rw [h, Finset.card_singleton]
    have h2 : (validMax 0 2).card = 0 := by
      have h : validMax 0 2 = ∅ := by
        ext A
        simp only [validMax, validSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        rintro ⟨⟨_, hrgs⟩, _, ⟨i0, j0, hij0⟩⟩
        have h00 : A 0 0 = 0 := by
          by_contra hne
          rcases hrgs 0 0 0 (Fin.pos_of_ne_zero hne) with ⟨i', j', hlt', _⟩; omega
        have hi0 : i0 = 0 := Fin.eq_zero i0
        rw [hi0] at hij0
        match j0 with
        | 0 => rw [h00] at hij0; exact absurd hij0 (by decide)
        | 1 =>
          rcases hrgs 0 1 1 (by rw [hij0]; decide) with ⟨i', j', hlt', heq⟩
          have hi' : i' = 0 := Fin.eq_zero i'
          have hj' : j' = 0 := Fin.ext (by omega)
          rw [hi', hj', h00] at heq; exact absurd heq (by decide)
      rw [h, Finset.card_empty]
    have h3 : (validMax 0 3).card = 0 := by
      have h : validMax 0 3 = ∅ := by
        ext A
        simp only [validMax, validSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        rintro ⟨⟨_, hrgs⟩, _, ⟨i0, j0, hij0⟩⟩
        have h00 : A 0 0 = 0 := by
          by_contra hne
          rcases hrgs 0 0 0 (Fin.pos_of_ne_zero hne) with ⟨i', j', hlt', _⟩; omega
        have hi0 : i0 = 0 := Fin.eq_zero i0
        rw [hi0] at hij0
        match j0 with
        | 0 => rw [h00] at hij0; exact absurd hij0 (by decide)
        | 1 =>
          rcases hrgs 0 1 1 (by rw [hij0]; decide) with ⟨i', j', hlt', heq⟩
          have hi' : i' = 0 := Fin.eq_zero i'
          have hj' : j' = 0 := Fin.ext (by omega)
          rw [hi', hj', h00] at heq; exact absurd heq (by decide)
      rw [h, Finset.card_empty]
    rw [h0, h1, h2, h3]; norm_num
  | succ n ih =>
    rcases ih with ⟨ih0, ih1, ih2, ih3⟩
    have s0 : (validMax (n + 1) 0).card = 1 := card_validMax_zero (n + 1)
    have s1 : (validMax (n + 1) 1).card = 3 * (validMax n 1).card + 2 * (validMax n 0).card :=
      card_validMax_succ n 1 (by decide)
    have s2 : (validMax (n + 1) 2).card = 5 * (validMax n 2).card + 2 * (validMax n 1).card :=
      card_validMax_succ n 2 (by decide)
    have s3 : (validMax (n + 1) 3).card = 7 * (validMax n 3).card + 2 * (validMax n 2).card :=
      card_validMax_succ n 3 (by decide)
    have p3 : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
    have p5 : 5 ^ (n + 1) = 5 * 5 ^ n := by ring
    have p7 : 7 ^ (n + 1) = 7 * 7 ^ n := by ring
    refine ⟨s0, by omega, by omega, by omega⟩

theorem main :
    ∀ n : ℕ, 1 ≤ n → 3 * a n = 1 + 3 * 3 ^ n + 2 * 7 ^ n := by
  intro n _
  have ha : a n = (validSet n).card := by
    unfold a validSet
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [ha, card_valid_eq_sum n]
  rcases validMax_formulas n with ⟨h0, h1, h2, h3⟩
  omega

end
end ProofA204565

theorem OMA.solution : type_of% @OMA.S_oeis_a204565.main :=
  ProofA204565.main
