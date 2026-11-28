import OMAStatements.S_mo_284849

namespace OMA.S_mo_284849_Proof

open Matrix OMA.S_mo_284849

private lemma part1 (K : Type) [Field K] (n : ℕ) (A B : Mat K n) :
    (∃ e : Equiv.Perm (Fin n × Fin n), entries e A = B ∧ entries e A⁻¹ = B⁻¹) ↔
      ∀ v : K × K, Nat.card {p // paired A p = v} = Nat.card {p // paired B p = v} := by
  constructor
  · rintro ⟨e, hA, hAinv⟩ v
    have hp : ∀ p : Fin n × Fin n, paired A (e p) = paired B p := by
      rintro ⟨i, j⟩
      apply Prod.ext
      · exact congrFun (congrFun hA i) j
      · exact congrFun (congrFun hAinv i) j
    refine (Nat.card_congr ?_).symm
    exact
      { toFun := fun x => ⟨e x.1, by rw [hp x.1, x.2]⟩
        invFun := fun y => ⟨e.symm y.1, by rw [← hp (e.symm y.1), e.apply_symm_apply, y.2]⟩
        left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }
  · intro hcard
    classical
    let f : ∀ v : K × K, {p // paired B p = v} ≃ {p // paired A p = v} := fun v =>
      Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using (hcard v).symm)
    let e : Equiv.Perm (Fin n × Fin n) :=
      ((Equiv.sigmaFiberEquiv (paired B)).symm.trans (Equiv.sigmaCongrRight f)).trans
        (Equiv.sigmaFiberEquiv (paired A))
    have hep : ∀ p : Fin n × Fin n, paired A (e p) = paired B p :=
      fun p => (f (paired B p) ⟨p, rfl⟩).2
    refine ⟨e, ?_, ?_⟩
    · ext i j
      exact congrArg Prod.fst (hep (i, j))
    · ext i j
      exact congrArg Prod.snd (hep (i, j))

private lemma part2 (K : Type) [Field K] :
    ∃ (A : Mat K 3) (e : Equiv.Perm (Fin 3 × Fin 3)),
      IsUnit A.det ∧ IsUnit (entries e A).det ∧ entries e A⁻¹ = (entries e A)⁻¹ ∧
      ¬rowsCols A (entries e A) := by
  let A : Mat K 3 := !![0, 0, 1; 0, 1, 0; 1, 1, 1]
  let e : Equiv.Perm (Fin 3 × Fin 3) := Equiv.prodComm (Fin 3) (Fin 3)
  have hent : ∀ M : Mat K 3, entries e M = Mᵀ := fun M => by
    ext i j
    rfl
  have hdet : A.det = -1 := by
    simp [A, Matrix.det_fin_three]
  refine ⟨A, e, ?_, ?_, ?_, ?_⟩
  · rw [hdet]
    exact isUnit_one.neg
  · rw [hent A, Matrix.det_transpose, hdet]
    exact isUnit_one.neg
  · rw [hent A⁻¹, hent A, Matrix.transpose_nonsing_inv]
  · rintro ⟨s, t, hst⟩
    have hrow2 : ∀ k : Fin 3, A 2 k = 1 := by
      intro k
      fin_cases k <;> rfl
    have hall : ∀ j : Fin 3, A j (s.symm 2) = 1 := by
      intro j
      have h := hst (s.symm 2) j
      rw [hent A, Matrix.transpose_apply, s.apply_symm_apply, hrow2 (t j)] at h
      exact h
    have hfalse : ∀ i : Fin 3, (∀ j : Fin 3, A j i = 1) → False := by
      intro i hi
      fin_cases i
      · have h := hi 0; simp [A] at h
      · have h := hi 0; simp [A] at h
      · have h := hi 1; simp [A] at h
    exact hfalse (s.symm 2) hall

private def blkA (i : Fin 12) : ℕ :=
  if i.1 < 8 then 0 else if i.1 < 10 then 1 else 2

private def blkB (i : Fin 12) : ℕ :=
  if i.1 < 6 then 0 else 1

private def blockMat (blk : Fin 12 → ℕ) : Mat (ZMod 2) 12 :=
  Matrix.of (fun i j => if i ≠ j ∧ blk i = blk j then 1 else 0)

private lemma card_fin12_Ico (a b : ℕ) (hb : b ≤ 12) :
    (Finset.univ.filter (fun k : Fin 12 => a ≤ k.1 ∧ k.1 < b)).card = b - a := by
  rw [← Nat.card_Ico a b]
  apply Finset.card_bij (fun k _ => k.1)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico] at hk ⊢
    exact hk
  · intro k₁ _ k₂ _ hval
    exact Fin.ext hval
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    exact ⟨⟨n, by omega⟩, by simp [hn.1, hn.2], rfl⟩

private lemma card_blkA (i : Fin 12) :
    (Finset.univ.filter (fun k : Fin 12 => blkA k = blkA i)).card =
      if i.1 < 8 then 8 else 2 := by
  by_cases h8 : i.1 < 8
  · rw [if_pos h8]
    have hfilt :
        Finset.univ.filter (fun k : Fin 12 => blkA k = blkA i) =
        Finset.univ.filter (fun k : Fin 12 => 0 ≤ k.1 ∧ k.1 < 8) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold blkA
      by_cases hk8 : k.1 < 8
      · simp [h8, hk8]
      · by_cases hk10 : k.1 < 10 <;> simp [h8, hk8, hk10]
    rw [hfilt, card_fin12_Ico 0 8 (by omega)]
  · rw [if_neg h8]
    by_cases h10 : i.1 < 10
    · have hfilt :
          Finset.univ.filter (fun k : Fin 12 => blkA k = blkA i) =
          Finset.univ.filter (fun k : Fin 12 => 8 ≤ k.1 ∧ k.1 < 10) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        unfold blkA
        by_cases hk8 : k.1 < 8
        · simp [h8, h10, hk8]
        · by_cases hk10 : k.1 < 10
          · simp [h8, h10, hk8, hk10]; omega
          · simp [h8, h10, hk8, hk10]
      rw [hfilt, card_fin12_Ico 8 10 (by omega)]
    · have hfilt :
          Finset.univ.filter (fun k : Fin 12 => blkA k = blkA i) =
          Finset.univ.filter (fun k : Fin 12 => 10 ≤ k.1 ∧ k.1 < 12) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hk12 : k.1 < 12 := k.2
        unfold blkA
        by_cases hk8 : k.1 < 8
        · simp [h8, h10, hk8]; omega
        · by_cases hk10 : k.1 < 10
          · simp [h8, h10, hk8, hk10]
          · simp [h8, h10, hk8, hk10, hk12]; omega
      rw [hfilt, card_fin12_Ico 10 12 (by omega)]

private lemma card_blkB (i : Fin 12) :
    (Finset.univ.filter (fun k : Fin 12 => blkB k = blkB i)).card = 6 := by
  by_cases h6 : i.1 < 6
  · have hfilt :
        Finset.univ.filter (fun k : Fin 12 => blkB k = blkB i) =
        Finset.univ.filter (fun k : Fin 12 => 0 ≤ k.1 ∧ k.1 < 6) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold blkB
      by_cases hk6 : k.1 < 6 <;> simp [h6, hk6]
    rw [hfilt, card_fin12_Ico 0 6 (by omega)]
  · have hfilt :
        Finset.univ.filter (fun k : Fin 12 => blkB k = blkB i) =
        Finset.univ.filter (fun k : Fin 12 => 6 ≤ k.1 ∧ k.1 < 12) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hk12 : k.1 < 12 := k.2
      unfold blkB
      by_cases hk6 : k.1 < 6
      · simp [h6, hk6]
      · simp [h6, hk6, hk12]; omega
    rw [hfilt, card_fin12_Ico 6 12 (by omega)]

private lemma blockMat_isSymm (blk : Fin 12 → ℕ) : (blockMat blk).IsSymm := by
  ext i j
  simp [blockMat, eq_comm]

private lemma blockMat_diag (blk : Fin 12 → ℕ) (i : Fin 12) : blockMat blk i i = 0 := by
  simp [blockMat]

private lemma blockMat_sq_eq_one (blk : Fin 12 → ℕ)
    (heven : ∀ i : Fin 12, Even (Finset.univ.filter (fun k : Fin 12 => blk k = blk i)).card) :
    blockMat blk * blockMat blk = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin 12,
      blockMat blk i k * blockMat blk k j =
        if blk k = blk i ∧ blk k = blk j ∧ k ≠ i ∧ k ≠ j then (1 : ZMod 2) else 0 := by
    intro k
    simp only [blockMat, Matrix.of_apply]
    by_cases h1 : i ≠ k ∧ blk i = blk k <;> by_cases h2 : k ≠ j ∧ blk k = blk j
    · rw [if_pos h1, if_pos h2, mul_one, if_pos ⟨h1.2.symm, h2.2, h1.1.symm, h2.1⟩]
    · rw [if_pos h1, if_neg h2, mul_zero, if_neg]
      intro hc
      exact h2 ⟨hc.2.2.2, hc.2.1⟩
    · rw [if_neg h1, zero_mul, if_neg]
      intro hc
      exact h1 ⟨hc.2.2.1.symm, hc.1.symm⟩
    · rw [if_neg h1, zero_mul, if_neg]
      intro hc
      exact h1 ⟨hc.2.2.1.symm, hc.1.symm⟩
  simp_rw [hterm]
  rw [Finset.sum_boole]
  set S := Finset.univ.filter (fun k : Fin 12 => blk k = blk i)
  have hiS : i ∈ S := by simp [S]
  rcases heven i with ⟨m, hm⟩
  have hmS : S.card = m + m := hm
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hset : Finset.univ.filter (fun k : Fin 12 => blk k = blk i ∧ blk k = blk i ∧ k ≠ i ∧ k ≠ i) =
        S.erase i := by
      ext k
      simp [S, and_comm]
    rw [hset, Finset.card_erase_of_mem hiS]
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
    have hcard : S.card - 1 = 2 * (m - 1) + 1 := by omega
    rw [hcard]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := rfl
    simp [h2]
  · rw [if_neg hij]
    by_cases hblk : blk i = blk j
    · have hjS : j ∈ S := by simp [S, hblk]
      have hjErase : j ∈ S.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hjS⟩
      have hset : Finset.univ.filter (fun k : Fin 12 => blk k = blk i ∧ blk k = blk j ∧ k ≠ i ∧ k ≠ j) =
          (S.erase i).erase j := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, S, hblk]
        tauto
      rw [hset, Finset.card_erase_of_mem hjErase, Finset.card_erase_of_mem hiS]
      have hge2 : 2 ≤ S.card := by
        have hsub : ({i, j} : Finset (Fin 12)) ⊆ S := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hpair : ({i, j} : Finset (Fin 12)).card = 2 := Finset.card_pair hij
        exact hpair ▸ Finset.card_le_card hsub
      have hcard : S.card - 1 - 1 = 2 * (m - 1) := by omega
      rw [hcard]
      push_cast
      have h2 : (2 : ZMod 2) = 0 := rfl
      simp [h2]
    · have hset : Finset.univ.filter (fun k : Fin 12 => blk k = blk i ∧ blk k = blk j ∧ k ≠ i ∧ k ≠ j) = ∅ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hc
        exact hblk (hc.1.symm.trans hc.2.1)
      rw [hset]
      simp

private lemma row_ones_blockMat (blk : Fin 12 → ℕ) (i : Fin 12) :
    (Finset.univ.filter (fun j : Fin 12 => blockMat blk i j = 1)).card =
      (Finset.univ.filter (fun k : Fin 12 => blk k = blk i)).card - 1 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hset : Finset.univ.filter (fun j : Fin 12 => blockMat blk i j = 1) =
      (Finset.univ.filter (fun k : Fin 12 => blk k = blk i)).erase i := by
    ext j
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, blockMat, Matrix.of_apply]
    split_ifs with h
    · exact ⟨fun _ => ⟨h.1.symm, h.2.symm⟩, fun _ => rfl⟩
    · constructor
      · intro hc
        exact absurd hc.symm h10
      · intro hc
        exact absurd ⟨hc.1.symm, hc.2.symm⟩ h
  rw [hset, Finset.card_erase_of_mem (by simp)]

private lemma total_ones_eq (blk : Fin 12 → ℕ) :
    (Finset.univ.filter (fun p : Fin 12 × Fin 12 => blockMat blk p.1 p.2 = 1)).card =
      ∑ i : Fin 12, (Finset.univ.filter (fun j : Fin 12 => blockMat blk i j = 1)).card := by
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun p _ => ⟨p.1, p.2⟩)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma] at hp ⊢
    exact hp
  · intro p₁ _ p₂ _ h
    exact Prod.ext (congrArg Sigma.fst h) (by cases p₁; cases p₂; cases h; rfl)
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hij
    exact ⟨(i, j), by simp [hij], rfl⟩

private lemma total_ones_A :
    (Finset.univ.filter (fun p : Fin 12 × Fin 12 => blockMat blkA p.1 p.2 = 1)).card = 60 := by
  rw [total_ones_eq]
  have hrow : ∀ i : Fin 12,
      (Finset.univ.filter (fun j : Fin 12 => blockMat blkA i j = 1)).card =
        if i.1 < 8 then 7 else 1 := by
    intro i
    rw [row_ones_blockMat, card_blkA]
    split_ifs <;> rfl
  simp_rw [hrow]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  have hc1 : (Finset.univ.filter (fun i : Fin 12 => i.1 < 8)).card = 8 := by
    have h := card_fin12_Ico 0 8 (by omega)
    simpa only [Nat.zero_le, true_and] using h
  have hc2 : (Finset.univ.filter (fun i : Fin 12 => ¬i.1 < 8)).card = 4 := by
    have h := card_fin12_Ico 8 12 (by omega)
    have hfilt : Finset.univ.filter (fun i : Fin 12 => ¬i.1 < 8) =
        Finset.univ.filter (fun i : Fin 12 => 8 ≤ i.1 ∧ i.1 < 12) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hi := i.2
      omega
    rw [hfilt, h]
  rw [hc1, hc2]

private lemma total_ones_B :
    (Finset.univ.filter (fun p : Fin 12 × Fin 12 => blockMat blkB p.1 p.2 = 1)).card = 60 := by
  rw [total_ones_eq]
  have hrow : ∀ i : Fin 12,
      (Finset.univ.filter (fun j : Fin 12 => blockMat blkB i j = 1)).card = 5 := by
    intro i
    rw [row_ones_blockMat, card_blkB]
  simp_rw [hrow]
  simp

private lemma part3 :
    ∃ (A B : Mat (ZMod 2) 12) (e : Equiv.Perm (Fin 12 × Fin 12)),
      A.IsSymm ∧ B.IsSymm ∧ (∀ i, A i i = 0 ∧ B i i = 0) ∧ A * A = 1 ∧ B * B = 1 ∧
      entries e A = B ∧ entries e A⁻¹ = B⁻¹ ∧ ¬rowsCols A B := by
  let A := blockMat blkA
  let B := blockMat blkB
  have hAA : A * A = 1 := by
    apply blockMat_sq_eq_one
    intro i
    rw [card_blkA]
    split_ifs
    · exact ⟨4, rfl⟩
    · exact ⟨1, rfl⟩
  have hBB : B * B = 1 := by
    apply blockMat_sq_eq_one
    intro i
    rw [card_blkB]
    exact ⟨3, rfl⟩
  have hAinv : A⁻¹ = A := Matrix.inv_eq_right_inv hAA
  have hBinv : B⁻¹ = B := Matrix.inv_eq_right_inv hBB
  have hex : ∃ e : Equiv.Perm (Fin 12 × Fin 12), entries e A = B ∧ entries e A⁻¹ = B⁻¹ := by
    rw [part1]
    rintro ⟨a, b⟩
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    by_cases hab : a = b
    · subst hab
      have hsimp : ∀ M : Mat (ZMod 2) 12, M⁻¹ = M →
          Finset.univ.filter (fun p : Fin 12 × Fin 12 => paired M p = (a, a)) =
          Finset.univ.filter (fun p : Fin 12 × Fin 12 => M p.1 p.2 = a) := by
        intro M hMinv
        ext p
        simp [paired, hMinv]
      rw [hsimp A hAinv, hsimp B hBinv]
      have ha : a = 0 ∨ a = 1 := by
        fin_cases a
        · left; rfl
        · right; rfl
      rcases ha with rfl | rfl
      · have hcomp : ∀ M : Mat (ZMod 2) 12,
            (Finset.univ.filter (fun p : Fin 12 × Fin 12 => M p.1 p.2 = 0)).card +
            (Finset.univ.filter (fun p : Fin 12 × Fin 12 => M p.1 p.2 = 1)).card = 144 := by
          intro M
          have hdisj : Disjoint
              (Finset.univ.filter (fun p : Fin 12 × Fin 12 => M p.1 p.2 = 0))
              (Finset.univ.filter (fun p : Fin 12 × Fin 12 => M p.1 p.2 = 1)) := by
            rw [Finset.disjoint_filter]
            intro p _ h0 h1
            exact (by decide : (0 : ZMod 2) ≠ 1) (h0.symm.trans h1)
          rw [← Finset.card_union_of_disjoint hdisj]
          have hunion :
              Finset.univ.filter (fun p : Fin 12 × Fin 12 => M p.1 p.2 = 0) ∪
              Finset.univ.filter (fun p : Fin 12 × Fin 12 => M p.1 p.2 = 1) = Finset.univ := by
            ext p
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
            generalize M p.1 p.2 = x
            fin_cases x
            · left; rfl
            · right; rfl
          rw [hunion]
          simp
        have hA0 := hcomp A
        have hB0 := hcomp B
        have hA1 : (Finset.univ.filter (fun p : Fin 12 × Fin 12 => A p.1 p.2 = 1)).card = 60 :=
          total_ones_A
        have hB1 : (Finset.univ.filter (fun p : Fin 12 × Fin 12 => B p.1 p.2 = 1)).card = 60 :=
          total_ones_B
        omega
      · exact total_ones_A.trans total_ones_B.symm
    · have hempty : ∀ M : Mat (ZMod 2) 12, M⁻¹ = M →
          Finset.univ.filter (fun p : Fin 12 × Fin 12 => paired M p = (a, b)) = ∅ := by
        intro M hMinv
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          paired, hMinv, Prod.mk.injEq]
        intro h
        exact hab (h.1.symm.trans h.2)
      rw [hempty A hAinv, hempty B hBinv]
  rcases hex with ⟨e, heA, heAinv⟩
  refine ⟨A, B, e, blockMat_isSymm blkA, blockMat_isSymm blkB,
    fun i => ⟨blockMat_diag blkA i, blockMat_diag blkB i⟩, hAA, hBB, heA, heAinv, ?_⟩
  rintro ⟨s, t, hst⟩
  let i := s.symm 0
  have h5 : (Finset.univ.filter (fun j : Fin 12 => B i j = 1)).card = 5 := by
    rw [row_ones_blockMat, card_blkB]
  have h7 : (Finset.univ.filter (fun k : Fin 12 => A 0 k = 1)).card = 7 := by
    rw [row_ones_blockMat, card_blkA]
    rfl
  have heq : (Finset.univ.filter (fun j : Fin 12 => B i j = 1)).card =
      (Finset.univ.filter (fun k : Fin 12 => A 0 k = 1)).card := by
    apply Finset.card_bij (fun j _ => t j)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have h := hst i j
      simp only [i, s.apply_symm_apply] at h
      exact h.symm.trans hj
    · intro j₁ _ j₂ _ ht
      exact t.injective ht
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine ⟨t.symm k, ?_, t.apply_symm_apply k⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h := hst i (t.symm k)
      simp only [i, s.apply_symm_apply, t.apply_symm_apply] at h
      exact h.trans hk
  omega

end OMA.S_mo_284849_Proof

theorem OMA.solution : type_of% @OMA.S_mo_284849.main :=
  ⟨OMA.S_mo_284849_Proof.part1, OMA.S_mo_284849_Proof.part2, OMA.S_mo_284849_Proof.part3⟩
