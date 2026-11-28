import OMAStatements.S_oeis_a386650
import Mathlib

/-!
# Proof of OEIS A386650 Conjecture

For `n >= 1`, a triangular `0..3` array `T` has all horizontal rows of equal average iff all rows
have average equal to the single entry `v = T 0 0 ∈ {0, 1, 2, 3}` of row 0, i.e. row `k` (length
`k + 1`) has entry sum `(k + 1) * v`.
- For `v = 0`, every entry must be `0` (`1` array).
- For `v = 3`, every entry must be `3` (`1` array).
- For `v = 1`, row `k` has `((1 + X + X^2 + X^3)^(k + 1)).coeff (k + 1) = quadrinomial (k + 1)`
  choices independently for each `k ∈ Fin n`, giving `∏_{k = 1..n} quadrinomial k = a(n)` arrays.
- For `v = 2`, the entrywise involution `x ↦ 3 - x` bijects rows of sum `2 * (k + 1)` with rows
  of sum `k + 1`, also giving `a(n)` arrays.
Summing over `v ∈ {0, 1, 2, 3}` yields `A214590(n) = 2 * a(n) + 2`.
-/

namespace OeisA386650Proof

open Finset OMA.S_oeis_a386650

private lemma card_row_sum_eq_coeff :
    ∀ k s : ℕ,
      (Finset.univ.filter fun row : Fin k → Fin 4 =>
        ∑ j : Fin k, (row j).1 = s).card =
      ((1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℕ) ^ k).coeff s := by
  intro k
  induction k with
  | zero =>
    intro s
    cases s with
    | zero => simp
    | succ s => simp [Polynomial.coeff_one]
  | succ k ih =>
    intro s
    let P : Polynomial ℕ := 1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3
    have hcoeff : (P ^ (k + 1)).coeff s =
        (P ^ k).coeff s +
        (if 1 ≤ s then (P ^ k).coeff (s - 1) else 0) +
        (if 2 ≤ s then (P ^ k).coeff (s - 2) else 0) +
        (if 3 ≤ s then (P ^ k).coeff (s - 3) else 0) := by
      rw [pow_succ]
      simp only [P, mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow']
      cases s with
      | zero => simp
      | succ s =>
        cases s with
        | zero => simp
        | succ s =>
          cases s with
          | zero => simp
          | succ s => simp
    rw [hcoeff]
    let e : (Fin (k + 1) → Fin 4) ≃ Fin 4 × (Fin k → Fin 4) :=
      { toFun := fun f => (f 0, fun j => f j.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun f => by ext i; cases i using Fin.cases <;> simp
        right_inv := fun ⟨a, g⟩ => by ext <;> simp }
    let T (d : Fin 4) : Finset (Fin 4 × (Fin k → Fin 4)) :=
      (Finset.univ.filter fun g : Fin k → Fin 4 =>
        d.1 + ∑ j : Fin k, (g j).1 = s).image (fun g => (d, g))
    have hTcard : ∀ d : Fin 4, (T d).card =
        (Finset.univ.filter fun g : Fin k → Fin 4 =>
          d.1 + ∑ j : Fin k, (g j).1 = s).card := fun d =>
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
    have hcard : (Finset.univ.filter fun row : Fin (k + 1) → Fin 4 =>
          ∑ j : Fin (k + 1), (row j).1 = s).card =
        ∑ d : Fin 4, (Finset.univ.filter fun g : Fin k → Fin 4 =>
          d.1 + ∑ j : Fin k, (g j).1 = s).card := by
      simp_rw [← hTcard]
      rw [← Finset.card_biUnion]
      · refine Finset.card_bij (fun f _ => e f) ?_ ?_ ?_
        · intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, T, Finset.mem_image,
            Finset.mem_filter, e]
          refine ⟨f 0, fun j => f j.succ, ?_, rfl⟩
          simpa [Fin.sum_univ_succ] using hf
        · intro f1 _ f2 _ h; exact e.injective h
        · intro p hp
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, T, Finset.mem_image,
            Finset.mem_filter] at hp
          rcases hp with ⟨d, g, hg, rfl⟩
          refine ⟨e.symm (d, g), ?_, e.apply_symm_apply _⟩
          simpa [e, Fin.sum_univ_succ] using hg
      · intro d1 _ d2 _ hne
        show Disjoint (T d1) (T d2)
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [T, Finset.mem_image] at hp1 hp2
        rcases hp1 with ⟨_, _, rfl⟩
        rcases hp2 with ⟨_, _, h⟩
        exact hne (congrArg Prod.fst h).symm
    rw [hcard, Fin.sum_univ_four]
    simp only [Fin.val_zero, zero_add, Fin.val_one, Fin.val_two]
    have hv3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [hv3]
    have h0 : (Finset.univ.filter fun g : Fin k → Fin 4 => ∑ j : Fin k, (g j).1 = s).card =
        (P ^ k).coeff s := ih s
    have h1 : (Finset.univ.filter fun g : Fin k → Fin 4 => 1 + ∑ j : Fin k, (g j).1 = s).card =
        if 1 ≤ s then (P ^ k).coeff (s - 1) else 0 := by
      split_ifs with hs
      · rw [← ih (s - 1)]
        congr 1; ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro g _; omega
    have h2 : (Finset.univ.filter fun g : Fin k → Fin 4 => 2 + ∑ j : Fin k, (g j).1 = s).card =
        if 2 ≤ s then (P ^ k).coeff (s - 2) else 0 := by
      split_ifs with hs
      · rw [← ih (s - 2)]
        congr 1; ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro g _; omega
    have h3 : (Finset.univ.filter fun g : Fin k → Fin 4 => 3 + ∑ j : Fin k, (g j).1 = s).card =
        if 3 ≤ s then (P ^ k).coeff (s - 3) else 0 := by
      split_ifs with hs
      · rw [← ih (s - 3)]
        congr 1; ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro g _; omega
    rw [h0, h1, h2, h3]

private lemma card_row_sum_zero (k : ℕ) :
    (Finset.univ.filter fun row : Fin k → Fin 4 => ∑ j : Fin k, (row j).1 = 0).card = 1 := by
  have heq : (Finset.univ.filter fun row : Fin k → Fin 4 => ∑ j : Fin k, (row j).1 = 0) =
      {fun _ => (0 : Fin 4)} := by
    ext row
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      funext j
      have hj := Finset.sum_eq_zero_iff.mp h j (Finset.mem_univ j)
      exact Fin.ext hj
    · rintro rfl; simp
  rw [heq, Finset.card_singleton]

private lemma card_row_sum_max (k : ℕ) :
    (Finset.univ.filter fun row : Fin k → Fin 4 => ∑ j : Fin k, (row j).1 = k * 3).card = 1 := by
  have heq : (Finset.univ.filter fun row : Fin k → Fin 4 => ∑ j : Fin k, (row j).1 = k * 3) =
      {fun _ => (3 : Fin 4)} := by
    ext row
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      funext j
      by_contra hne
      have hlt : (row j).1 < 3 := by
        have hlt4 := (row j).2
        have hne3 : (row j).1 ≠ 3 := fun heq3 => hne (Fin.ext heq3)
        omega
      have hsum_lt : ∑ i : Fin k, (row i).1 < ∑ _i : Fin k, 3 := by
        apply Finset.sum_lt_sum
        · intro i _; have := (row i).2; omega
        · exact ⟨j, Finset.mem_univ j, hlt⟩
      simp at hsum_lt
      omega
    · rintro rfl; simp
  rw [heq, Finset.card_singleton]

private lemma card_row_sum_two_eq_one (k : ℕ) :
    (Finset.univ.filter fun row : Fin k → Fin 4 => ∑ j : Fin k, (row j).1 = k * 2).card =
    (Finset.univ.filter fun row : Fin k → Fin 4 => ∑ j : Fin k, (row j).1 = k).card := by
  let flip : (Fin k → Fin 4) → (Fin k → Fin 4) := fun row j => ⟨3 - (row j).1, by omega⟩
  have hflip_sum : ∀ row : Fin k → Fin 4,
      (∑ j : Fin k, (flip row j).1) + (∑ j : Fin k, (row j).1) = k * 3 := by
    intro row
    rw [← Finset.sum_add_distrib]
    have hpt : ∀ j : Fin k, (flip row j).1 + (row j).1 = 3 := by
      intro j; dsimp [flip]; have := (row j).2; omega
    simp [hpt]
  have hflip_inv : ∀ row : Fin k → Fin 4, flip (flip row) = row := by
    intro row; funext j; apply Fin.ext; dsimp [flip]; have := (row j).2; omega
  refine Finset.card_bij (fun row _ => flip row) ?_ ?_ ?_
  · intro row hrow
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrow ⊢
    have hs := hflip_sum row
    omega
  · intro r1 _ r2 _ h
    calc r1 = flip (flip r1) := (hflip_inv r1).symm
      _ = flip (flip r2) := congrArg flip h
      _ = r2 := hflip_inv r2
  · intro row hrow
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrow
    refine ⟨flip row, ?_, hflip_inv row⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hs := hflip_sum row
    omega

end OeisA386650Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a386650.main := by
  intro n hn
  unfold OMA.S_oeis_a386650.A214590
  let k0 : Fin n := ⟨0, by omega⟩
  have hiff : ∀ T : (k : Fin n) → Fin (k.1 + 1) → Fin 4,
      (∀ k1 k2 : Fin n,
        (k2.1 + 1) * (∑ j : Fin (k1.1 + 1), (T k1 j).1) =
          (k1.1 + 1) * (∑ j : Fin (k2.1 + 1), (T k2 j).1)) ↔
      ∃ v : Fin 4, ∀ k : Fin n, ∑ j : Fin (k.1 + 1), (T k j).1 = (k.1 + 1) * v.1 := by
    intro T
    constructor
    · intro h
      refine ⟨T k0 ⟨0, by omega⟩, ?_⟩
      intro k
      have hk := h k0 k
      simp only [k0, zero_add, one_mul] at hk
      have hsum0 : ∑ j : Fin 1, (T k0 j).1 = (T k0 ⟨0, by omega⟩).1 := by
        rw [Fin.sum_univ_one]; rfl
      rw [hsum0] at hk
      exact hk.symm
    · rintro ⟨v, hv⟩ k1 k2
      rw [hv k1, hv k2]; ring
  let S (v : Fin 4) : Finset ((k : Fin n) → Fin (k.1 + 1) → Fin 4) :=
    Finset.univ.filter (fun T => ∀ k : Fin n, ∑ j : Fin (k.1 + 1), (T k j).1 = (k.1 + 1) * v.1)
  have hpart :
      (Finset.univ.filter fun T : (k : Fin n) → Fin (k.1 + 1) → Fin 4 =>
        ∀ k1 k2 : Fin n,
          (k2.1 + 1) * (∑ j : Fin (k1.1 + 1), (T k1 j).1) =
            (k1.1 + 1) * (∑ j : Fin (k2.1 + 1), (T k2 j).1)) =
      Finset.biUnion Finset.univ S := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, S]
    exact hiff T
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 4)) S := by
    intro v1 _ v2 _ hne
    show Disjoint (S v1) (S v2)
    rw [Finset.disjoint_left]
    intro T h1 h2
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have e1 := h1 k0
    have e2 := h2 k0
    simp only [k0, zero_add, one_mul] at e1 e2
    exact hne (Fin.ext (e1.symm.trans e2))
  rw [hpart, Finset.card_biUnion hdisj]
  have hcard_S : ∀ v : Fin 4,
      (S v).card = ∏ k : Fin n,
        (Finset.univ.filter fun row : Fin (k.1 + 1) → Fin 4 =>
          ∑ j : Fin (k.1 + 1), (row j).1 = (k.1 + 1) * v.1).card := by
    intro v
    have heq : S v = Fintype.piFinset (fun k : Fin n =>
        Finset.univ.filter fun row : Fin (k.1 + 1) → Fin 4 =>
          ∑ j : Fin (k.1 + 1), (row j).1 = (k.1 + 1) * v.1) := by
      ext T
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    rw [heq, Fintype.card_piFinset]
  simp_rw [hcard_S]
  rw [Fin.sum_univ_four]
  have hc0 : (∏ k : Fin n,
      (Finset.univ.filter fun row : Fin (k.1 + 1) → Fin 4 =>
        ∑ j : Fin (k.1 + 1), (row j).1 = (k.1 + 1) * (0 : Fin 4).1).card) = 1 := by
    apply Finset.prod_eq_one
    intro k _
    simpa using OeisA386650Proof.card_row_sum_zero (k.1 + 1)
  have hc3 : (∏ k : Fin n,
      (Finset.univ.filter fun row : Fin (k.1 + 1) → Fin 4 =>
        ∑ j : Fin (k.1 + 1), (row j).1 = (k.1 + 1) * (3 : Fin 4).1).card) = 1 := by
    apply Finset.prod_eq_one
    intro k _
    simpa using OeisA386650Proof.card_row_sum_max (k.1 + 1)
  have hc1 : (∏ k : Fin n,
      (Finset.univ.filter fun row : Fin (k.1 + 1) → Fin 4 =>
        ∑ j : Fin (k.1 + 1), (row j).1 = (k.1 + 1) * (1 : Fin 4).1).card) =
      OMA.S_oeis_a386650.a n := by
    unfold OMA.S_oeis_a386650.a
    rw [Finset.prod_range_succ']
    have h0 : OMA.S_oeis_a386650.quadrinomial 0 = 1 := by
      simp [OMA.S_oeis_a386650.quadrinomial]
    rw [h0, mul_one, ← Fin.prod_univ_eq_prod_range (fun k => OMA.S_oeis_a386650.quadrinomial (k + 1)) n]
    apply Finset.prod_congr rfl
    intro k _
    simpa [OMA.S_oeis_a386650.quadrinomial] using
      OeisA386650Proof.card_row_sum_eq_coeff (k.1 + 1) (k.1 + 1)
  have hc2 : (∏ k : Fin n,
      (Finset.univ.filter fun row : Fin (k.1 + 1) → Fin 4 =>
        ∑ j : Fin (k.1 + 1), (row j).1 = (k.1 + 1) * (2 : Fin 4).1).card) =
      OMA.S_oeis_a386650.a n := by
    rw [← hc1]
    apply Finset.prod_congr rfl
    intro k _
    simpa using OeisA386650Proof.card_row_sum_two_eq_one (k.1 + 1)
  rw [hc0, hc1, hc2, hc3]
  omega
