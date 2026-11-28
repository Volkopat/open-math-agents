import OMAStatements.S_oeis_a201950
import Mathlib

namespace OMA.S_oeis_a201950

open Polynomial BigOperators

/-- Insert `0` at position `p : Fin (n + 2)` into a permutation `π` of `Fin (n + 1)`,
shifting all values of `π` up by `1`. -/
private def insertZero {n : ℕ} (p : Fin (n + 2)) (π : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) where
  toFun := p.succAboveCases 0 (fun j => (π j).succ)
  invFun := Fin.cases p (fun j => p.succAbove (π.symm j))
  left_inv x := by
    refine p.succAboveCases ?_ ?_ x
    · simp
    · intro j; simp
  right_inv y := by
    refine Fin.cases ?_ ?_ y
    · simp
    · intro j; simp

@[simp]
private lemma insertZero_self {n : ℕ} (p : Fin (n + 2)) (π : Equiv.Perm (Fin (n + 1))) :
    insertZero p π p = 0 := by
  simp [insertZero]

@[simp]
private lemma insertZero_succAbove {n : ℕ} (p : Fin (n + 2)) (π : Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) :
    insertZero p π (p.succAbove j) = (π j).succ := by
  simp [insertZero]

@[simp]
private lemma insertZero_symm_zero {n : ℕ} (p : Fin (n + 2)) (π : Equiv.Perm (Fin (n + 1))) :
    (insertZero p π).symm 0 = p := by
  simp [insertZero]

/-- Bijection `Equiv.Perm (Fin (n + 1)) × Fin (n + 2) ≃ Equiv.Perm (Fin (n + 2))`
given by inserting `0` at position `p`. -/
private noncomputable def permInsertEquiv (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) × Fin (n + 2) ≃ Equiv.Perm (Fin (n + 2)) :=
  Equiv.ofBijective (fun x => insertZero x.2 x.1)
    ⟨by
      rintro ⟨π₁, p₁⟩ ⟨π₂, p₂⟩ h
      have hp : p₁ = p₂ := by
        have h0 := congr_arg (fun σ : Equiv.Perm (Fin (n + 2)) => σ.symm 0) h
        simpa using h0
      subst hp
      have hπ : π₁ = π₂ := by
        ext j
        have hj := congr_arg (fun σ : Equiv.Perm (Fin (n + 2)) => σ (p₁.succAbove j)) h
        simp only [insertZero_succAbove] at hj
        exact congr_arg Fin.val (Fin.succ_injective _ hj)
      subst hπ
      rfl,
     by
      intro σ
      let p : Fin (n + 2) := σ.symm 0
      have hσp : σ p = 0 := σ.apply_symm_apply 0
      have hne0 : ∀ j : Fin (n + 1), σ (p.succAbove j) ≠ 0 := by
        intro j h
        have : p.succAbove j = p := σ.injective (h.trans hσp.symm)
        exact Fin.succAbove_ne p j this
      let f : Fin (n + 1) → Fin (n + 1) := fun j => (σ (p.succAbove j)).pred (hne0 j)
      have hf_inj : Function.Injective f := by
        intro j₁ j₂ h
        have hsucc : (f j₁).succ = (f j₂).succ := congr_arg Fin.succ h
        simp only [f, Fin.succ_pred] at hsucc
        exact Fin.succAbove_right_injective (σ.injective hsucc)
      let π : Equiv.Perm (Fin (n + 1)) :=
        Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
      refine ⟨(π, p), ?_⟩
      ext x
      refine p.succAboveCases ?_ ?_ x
      · simp [hσp]
      · intro j
        simp [π, f]⟩

/-- `lrMaxCount` increases by `1` iff `0` is inserted at position `0`. -/
private lemma lrMaxCount_insertZero {n : ℕ} (p : Fin (n + 2)) (π : Equiv.Perm (Fin (n + 1))) :
    lrMaxCount (insertZero p π) = lrMaxCount π + if p = 0 then 1 else 0 := by
  unfold lrMaxCount
  set S := Finset.univ.filter fun i : Fin (n + 2) =>
    ∀ j : Fin (n + 2), j < i → insertZero p π j < insertZero p π i
  set T := Finset.univ.filter fun i : Fin (n + 1) =>
    ∀ j : Fin (n + 1), j < i → π j < π i
  have hmem_succ : ∀ k : Fin (n + 1), p.succAbove k ∈ S ↔ k ∈ T := by
    intro k
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and, insertZero_succAbove]
    constructor
    · intro h j hj
      have hlt : p.succAbove j < p.succAbove k := Fin.succAbove_lt_succAbove_iff.mpr hj
      have := h (p.succAbove j) hlt
      simpa using this
    · intro h q hq
      refine p.succAboveCases ?_ ?_ q hq
      · intro _
        simp only [insertZero_self]
        exact Fin.succ_pos (π k)
      · intro j hj
        have hjk : j < k := Fin.succAbove_lt_succAbove_iff.mp hj
        simp only [insertZero_succAbove]
        exact Fin.succ_lt_succ_iff.mpr (h j hjk)
  have hmem_p : p ∈ S ↔ p = 0 := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, insertZero_self]
    constructor
    · intro h
      by_contra hp0
      have h0p : (0 : Fin (n + 2)) < p := Fin.pos_of_ne_zero hp0
      have := h 0 h0p
      exact Fin.not_lt_zero _ this
    · intro hp0 q hq
      subst hp0
      exact absurd hq (Fin.not_lt_zero q)
  have himg : S.erase p = T.image p.succAbove := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_image]
    refine p.succAboveCases ?_ ?_ x
    · simp [Fin.succAbove_ne]
    · intro k
      constructor
      · intro ⟨_, hk⟩
        exact ⟨k, (hmem_succ k).mp hk, rfl⟩
      · rintro ⟨j, hj, hjk⟩
        have hEq : j = k := Fin.succAbove_right_injective hjk
        subst hEq
        exact ⟨Fin.succAbove_ne p j, (hmem_succ j).mpr hj⟩
  have hcard_img : (S.erase p).card = T.card := by
    rw [himg, Finset.card_image_of_injective _ Fin.succAbove_right_injective]
  by_cases hp0 : p = 0
  · have hpS : p ∈ S := hmem_p.mpr hp0
    simp only [hp0, ↓reduceIte]
    rw [← hcard_img, Finset.card_erase_add_one hpS]
  · have hpS : p ∉ S := fun h => hp0 (hmem_p.mp h)
    simp only [hp0, ↓reduceIte, add_zero]
    rw [← hcard_img, Finset.erase_eq_of_notMem hpS]

/-- `rlMaxCount` increases by `1` iff `0` is inserted at position `Fin.last (n + 1)`. -/
private lemma rlMaxCount_insertZero {n : ℕ} (p : Fin (n + 2)) (π : Equiv.Perm (Fin (n + 1))) :
    rlMaxCount (insertZero p π) = rlMaxCount π + if p = Fin.last (n + 1) then 1 else 0 := by
  unfold rlMaxCount
  set S := Finset.univ.filter fun i : Fin (n + 2) =>
    ∀ j : Fin (n + 2), i < j → insertZero p π j < insertZero p π i
  set T := Finset.univ.filter fun i : Fin (n + 1) =>
    ∀ j : Fin (n + 1), i < j → π j < π i
  have hmem_succ : ∀ k : Fin (n + 1), p.succAbove k ∈ S ↔ k ∈ T := by
    intro k
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and, insertZero_succAbove]
    constructor
    · intro h j hj
      have hlt : p.succAbove k < p.succAbove j := Fin.succAbove_lt_succAbove_iff.mpr hj
      have := h (p.succAbove j) hlt
      simpa using this
    · intro h q hq
      refine p.succAboveCases ?_ ?_ q hq
      · intro _
        simp only [insertZero_self]
        exact Fin.succ_pos (π k)
      · intro j hj
        have hkj : k < j := Fin.succAbove_lt_succAbove_iff.mp hj
        simp only [insertZero_succAbove]
        exact Fin.succ_lt_succ_iff.mpr (h j hkj)
  have hmem_p : p ∈ S ↔ p = Fin.last (n + 1) := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, insertZero_self]
    constructor
    · intro h
      by_contra hplast
      have hplt : p < Fin.last (n + 1) := lt_of_le_of_ne (Fin.le_last p) hplast
      have := h (Fin.last (n + 1)) hplt
      exact Fin.not_lt_zero _ this
    · intro hplast q hq
      subst hplast
      exact absurd hq (not_lt.mpr (Fin.le_last q))
  have himg : S.erase p = T.image p.succAbove := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_image]
    refine p.succAboveCases ?_ ?_ x
    · simp [Fin.succAbove_ne]
    · intro k
      constructor
      · intro ⟨_, hk⟩
        exact ⟨k, (hmem_succ k).mp hk, rfl⟩
      · rintro ⟨j, hj, hjk⟩
        have hEq : j = k := Fin.succAbove_right_injective hjk
        subst hEq
        exact ⟨Fin.succAbove_ne p j, (hmem_succ j).mpr hj⟩
  have hcard_img : (S.erase p).card = T.card := by
    rw [himg, Finset.card_image_of_injective _ Fin.succAbove_right_injective]
  by_cases hplast : p = Fin.last (n + 1)
  · have hpS : p ∈ S := hmem_p.mpr hplast
    simp only [hplast, ↓reduceIte]
    rw [← hcard_img, Finset.card_erase_add_one hpS]
  · have hpS : p ∉ S := fun h => hplast (hmem_p.mp h)
    simp only [hplast, ↓reduceIte, add_zero]
    rw [← hcard_img, Finset.erase_eq_of_notMem hpS]

/-- Bounds on `lrMaxCount` and `rlMaxCount`: for any permutation of `Fin (n + 1)`,
both counts are between `1` and `n + 1`. -/
private lemma rlMaxCount_le {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    rlMaxCount σ ≤ n + 1 := by
  unfold rlMaxCount
  calc
    (Finset.univ.filter fun i : Fin (n + 1) => ∀ j : Fin (n + 1), i < j → σ j < σ i).card
      ≤ (Finset.univ : Finset (Fin (n + 1))).card := Finset.card_filter_le _ _
    _ = n + 1 := by simp

private lemma lrMaxCount_pos {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    1 ≤ lrMaxCount σ := by
  unfold lrMaxCount
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  exact absurd hj (Fin.not_lt_zero j)

/-- Generating polynomial identity:
`∑_{σ : Perm (Fin (n + 1))} X^(lrMaxCount σ + n - rlMaxCount σ) = ∏_{k=0}^{n-1} (1 + k * X + X^2)`. -/
private lemma genPoly_eq :
    ∀ n : ℕ,
      (∑ σ : Equiv.Perm (Fin (n + 1)),
        (Polynomial.X : Polynomial ℕ) ^ (lrMaxCount σ + n - rlMaxCount σ)) =
      ∏ k ∈ Finset.range n, (1 + Polynomial.C k * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ)
  | 0 => by
      have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by
        ext σ; simp [Subsingleton.elim σ 1]
      rw [huniv, Finset.sum_singleton, Finset.prod_range_zero]
      have hlr : lrMaxCount (1 : Equiv.Perm (Fin 1)) = 1 := by decide
      have hrl : rlMaxCount (1 : Equiv.Perm (Fin 1)) = 1 := by decide
      simp [hlr, hrl]
  | n + 1 => by
      rw [Finset.prod_range_succ, ← genPoly_eq n]
      rw [← Equiv.sum_comp (permInsertEquiv n)]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun π _ => ?_
      have hbound : rlMaxCount π ≤ lrMaxCount π + n := by
        have h1 := rlMaxCount_le π
        have h2 := lrMaxCount_pos π
        omega
      have hsplit : ∀ p : Fin (n + 2),
          (Polynomial.X : Polynomial ℕ) ^
            (lrMaxCount (insertZero p π) + (n + 1) - rlMaxCount (insertZero p π)) =
          (Polynomial.X : Polynomial ℕ) ^ (lrMaxCount π + n - rlMaxCount π) *
            (if p = 0 then Polynomial.X ^ 2
             else if p = Fin.last (n + 1) then 1
             else Polynomial.X) := by
        intro p
        rw [lrMaxCount_insertZero, rlMaxCount_insertZero]
        by_cases hp0 : p = 0
        · subst hp0
          have hne : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
            intro h
            have := congr_arg Fin.val h
            simp at this
          simp only [hne, ↓reduceIte, add_zero]
          have hexp : lrMaxCount π + 1 + (n + 1) - rlMaxCount π =
              (lrMaxCount π + n - rlMaxCount π) + 2 := by omega
          rw [hexp, pow_add]
        · by_cases hplast : p = Fin.last (n + 1)
          · subst hplast
            simp only [hp0, ↓reduceIte, add_zero, mul_one]
            congr 1; omega
          · simp only [hp0, hplast, ↓reduceIte, add_zero]
            have hexp : lrMaxCount π + (n + 1) - rlMaxCount π =
                (lrMaxCount π + n - rlMaxCount π) + 1 := by omega
            rw [hexp, pow_add, pow_one]
      have hperm_app : ∀ p : Fin (n + 2), permInsertEquiv n (π, p) = insertZero p π := fun _ => rfl
      simp only [hperm_app]
      have hsum_p :
          ∑ p : Fin (n + 2),
            (Polynomial.X : Polynomial ℕ) ^
              (lrMaxCount (insertZero p π) + (n + 1) - rlMaxCount (insertZero p π)) =
          (Polynomial.X : Polynomial ℕ) ^ (lrMaxCount π + n - rlMaxCount π) *
            ∑ p : Fin (n + 2),
              (if p = 0 then Polynomial.X ^ 2
               else if p = Fin.last (n + 1) then 1
               else Polynomial.X) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => hsplit p
      rw [hsum_p]
      congr 1
      -- Evaluate `∑ p : Fin (n + 2), ... = 1 + n * X + X^2`
      rw [Fin.sum_univ_succ]
      simp only [↓reduceIte]
      have htail :
          ∑ i : Fin (n + 1),
            (if i.succ = (0 : Fin (n + 2)) then (Polynomial.X : Polynomial ℕ) ^ 2
             else if i.succ = Fin.last (n + 1) then 1
             else Polynomial.X) =
          1 + Polynomial.C n * Polynomial.X := by
        rw [Fin.sum_univ_castSucc]
        have hlast : (Fin.last n).succ = Fin.last (n + 1) := by ext; simp
        have hlast_ne : Fin.last (n + 1) ≠ (0 : Fin (n + 2)) := by
          intro h; have := congr_arg Fin.val h; simp at this
        simp only [Fin.succ_ne_zero, ↓reduceIte, hlast, hlast_ne]
        have hmid :
            ∑ i : Fin n,
              (if i.castSucc.succ = Fin.last (n + 1) then (1 : Polynomial ℕ) else Polynomial.X) =
            Polynomial.C n * Polynomial.X := by
          have hne : ∀ i : Fin n, i.castSucc.succ ≠ Fin.last (n + 1) := by
            intro i h
            have := congr_arg Fin.val h
            simp at this
            omega
          simp only [hne, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          rw [show (n : Polynomial ℕ) = Polynomial.C n by simp]
        rw [hmid, add_comm]
      rw [htail]
      ring

theorem main_proof :
    ∀ n : ℕ,
      a201950 n =
        (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) =>
          lrMaxCount σ = rlMaxCount σ).card := by
  intro n
  unfold a201950
  rw [← genPoly_eq n, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hbound : rlMaxCount σ ≤ lrMaxCount σ + n := by
    have h1 := rlMaxCount_le σ
    have h2 := lrMaxCount_pos σ
    omega
  have hiff : lrMaxCount σ + n - rlMaxCount σ = n ↔ lrMaxCount σ = rlMaxCount σ := by omega
  by_cases h : lrMaxCount σ = rlMaxCount σ
  · simp [h]
  · have hne : lrMaxCount σ + n - rlMaxCount σ ≠ n := mt hiff.mp h
    simp [h, hne.symm]

end OMA.S_oeis_a201950

theorem OMA.solution : type_of% @OMA.S_oeis_a201950.main :=
  OMA.S_oeis_a201950.main_proof
