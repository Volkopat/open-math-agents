import OMAStatements.S_oeis_a269496
import Mathlib

namespace OMA.S_oeis_a269496_proof

open OMA.S_oeis_a269496 PowerSeries Classical

def adj1 {q : ℕ} (x y : Fin q) : Prop :=
  x.val = y.val + 1 ∨ y.val = x.val + 1

def badPred {q : ℕ} (x : Fin q × Fin q × Fin q × Fin q × Fin q) : Prop :=
  allowed (repeats x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) = false

def bad1 {q : ℕ} (x : Fin q × Fin q × Fin q × Fin q × Fin q) : Prop :=
  x.2.1 = x.1 ∧ x.2.2.2.1 = x.2.2.1 ∧ adj1 x.1 x.2.2.1

def bad2 {q : ℕ} (x : Fin q × Fin q × Fin q × Fin q × Fin q) : Prop :=
  x.2.1 = x.1 ∧ x.2.2.1 ≠ x.2.2.2.1 ∧ x.2.2.2.2 = x.2.2.2.1 ∧ adj1 x.1 x.2.2.2.1

def bad3 {q : ℕ} (x : Fin q × Fin q × Fin q × Fin q × Fin q) : Prop :=
  x.2.1 ≠ x.1 ∧ x.2.2.1 = x.2.1 ∧ x.2.2.2.2 = x.2.2.2.1 ∧ adj1 x.2.1 x.2.2.2.1

lemma badPred_iff {q : ℕ} (x : Fin q × Fin q × Fin q × Fin q × Fin q) :
    badPred x ↔ bad1 x ∨ bad2 x ∨ bad3 x := by
  rcases x with ⟨a, b, c, d, e⟩
  unfold badPred bad1 bad2 bad3 adj1
  dsimp only
  rcases eq_or_ne b a with rfl | h1 <;>
  rcases eq_or_ne c b with rfl | h2 <;>
  rcases eq_or_ne d c with rfl | h3 <;>
  rcases eq_or_ne e d with rfl | h4 <;>
  simp_all [repeats, allowed, Fin.ext_iff] <;>
  (constructor <;> intro h <;> omega)

lemma bad_disjoint {q : ℕ} (x : Fin q × Fin q × Fin q × Fin q × Fin q) :
    ¬ (bad1 x ∧ bad2 x) ∧ ¬ (bad1 x ∧ bad3 x) ∧ ¬ (bad2 x ∧ bad3 x) := by
  unfold bad1 bad2 bad3
  refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨hA, hB⟩
  · exact hB.2.1 hA.2.1.symm
  · exact hB.1 hA.1
  · exact hB.1 hA.1

lemma card_adj1 (n : ℕ) :
    Fintype.card { p : Fin (n + 1) × Fin (n + 1) // adj1 p.1 p.2 } = 2 * n := by
  let S : Finset (Fin (n + 1) × Fin (n + 1)) := Finset.univ.filter (fun p => adj1 p.1 p.2)
  let S1 : Finset (Fin (n + 1) × Fin (n + 1)) :=
    Finset.univ.filter (fun p => p.1.val = p.2.val + 1)
  let S2 : Finset (Fin (n + 1) × Fin (n + 1)) :=
    Finset.univ.filter (fun p => p.2.val = p.1.val + 1)
  have hS_eq : S = S1 ∪ S2 := by
    ext p
    dsimp only [S, S1, S2]
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    simp [adj1]
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [S1, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    omega
  have e1 : { p : Fin (n + 1) × Fin (n + 1) // p.1.val = p.2.val + 1 } ≃ Fin n :=
    { toFun := fun p => ⟨p.1.2.val, by have := p.1.1.isLt; omega⟩
      invFun := fun i => ⟨(i.succ, i.castSucc), by simp⟩
      left_inv := fun ⟨⟨a, b⟩, h⟩ => by
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> dsimp only at h ⊢ <;>
          simp only [Fin.val_succ, Fin.val_castSucc]; omega
      right_inv := fun i => by ext; rfl }
  have e2 : { p : Fin (n + 1) × Fin (n + 1) // p.2.val = p.1.val + 1 } ≃ Fin n :=
    { toFun := fun p => ⟨p.1.1.val, by have := p.1.2.isLt; omega⟩
      invFun := fun i => ⟨(i.castSucc, i.succ), by simp⟩
      left_inv := fun ⟨⟨a, b⟩, h⟩ => by
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> dsimp only at h ⊢ <;>
          simp only [Fin.val_succ, Fin.val_castSucc]; omega
      right_inv := fun i => by ext; rfl }
  have hcard1 : S1.card = n := by
    change (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1.val = p.2.val + 1)).card = n
    rw [← Fintype.card_subtype]
    simpa [Fintype.card_fin] using Fintype.card_congr e1
  have hcard2 : S2.card = n := by
    change (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.2.val = p.1.val + 1)).card = n
    rw [← Fintype.card_subtype]
    simpa [Fintype.card_fin] using Fintype.card_congr e2
  rw [Fintype.card_subtype]
  change S.card = 2 * n
  rw [hS_eq, Finset.card_union_of_disjoint hdisj, hcard1, hcard2]
  omega

lemma card_ne_fin (n : ℕ) (d : Fin (n + 1)) :
    Fintype.card { c : Fin (n + 1) // c ≠ d } = n := by
  have h := Fintype.card_subtype_compl (fun c : Fin (n + 1) => c = d)
  have heq : Fintype.card { c : Fin (n + 1) // c = d } = 1 := by
    let e : { c : Fin (n + 1) // c = d } ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨d, rfl⟩
        left_inv := fun ⟨c, hc⟩ => Subtype.ext hc.symm
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_unit]
  rw [Fintype.card_fin, heq] at h
  exact h

lemma card_bad1 (n : ℕ) :
    Fintype.card { x : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) // bad1 x } =
      2 * n * (n + 1) := by
  let e : { x : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) // bad1 x } ≃
      { p : Fin (n + 1) × Fin (n + 1) // adj1 p.1 p.2 } × Fin (n + 1) :=
    { toFun := fun ⟨x, hx⟩ => (⟨(x.1, x.2.2.1), hx.2.2⟩, x.2.2.2.2)
      invFun := fun ⟨p, e⟩ => ⟨(p.1.1, p.1.1, p.1.2, p.1.2, e), ⟨rfl, rfl, p.2⟩⟩
      left_inv := fun ⟨⟨a, b, c, d, e⟩, ⟨h1, h2, _⟩⟩ => by
        apply Subtype.ext; dsimp only at h1 h2 ⊢; rw [h1, h2]
      right_inv := fun ⟨⟨p, hp⟩, e⟩ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, card_adj1, Fintype.card_fin]

lemma card_bad2 (n : ℕ) :
    Fintype.card { x : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) // bad2 x } =
      2 * n * n := by
  let e : { x : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) // bad2 x } ≃
      (Σ p : { p : Fin (n + 1) × Fin (n + 1) // adj1 p.1 p.2 }, { c : Fin (n + 1) // c ≠ p.1.2 }) :=
    { toFun := fun ⟨x, hx⟩ => ⟨⟨(x.1, x.2.2.2.1), hx.2.2.2⟩, ⟨x.2.2.1, hx.2.1⟩⟩
      invFun := fun ⟨p, c⟩ => ⟨(p.1.1, p.1.1, c.1, p.1.2, p.1.2), ⟨rfl, c.2, rfl, p.2⟩⟩
      left_inv := fun ⟨⟨a, b, c, d, e⟩, ⟨h1, h2, h3, _⟩⟩ => by
        apply Subtype.ext; dsimp only at h1 h2 h3 ⊢; rw [h1, h3]
      right_inv := fun ⟨⟨p, hp⟩, c⟩ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [card_ne_fin, Finset.sum_const, Finset.card_univ, card_adj1, smul_eq_mul]

lemma card_bad3 (n : ℕ) :
    Fintype.card { x : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) // bad3 x } =
      2 * n * n := by
  let e : { x : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) // bad3 x } ≃
      (Σ p : { p : Fin (n + 1) × Fin (n + 1) // adj1 p.1 p.2 }, { a : Fin (n + 1) // a ≠ p.1.1 }) :=
    { toFun := fun ⟨x, hx⟩ => ⟨⟨(x.2.1, x.2.2.2.1), hx.2.2.2⟩, ⟨x.1, hx.1.symm⟩⟩
      invFun := fun ⟨p, a⟩ => ⟨(a.1, p.1.1, p.1.1, p.1.2, p.1.2), ⟨a.2.symm, rfl, rfl, p.2⟩⟩
      left_inv := fun ⟨⟨a, b, c, d, e⟩, ⟨h1, h2, h3, _⟩⟩ => by
        apply Subtype.ext; dsimp only at h1 h2 h3 ⊢; rw [h2, h3]
      right_inv := fun ⟨⟨p, hp⟩, a⟩ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [card_ne_fin, Finset.sum_const, Finset.card_univ, card_adj1, smul_eq_mul]

lemma count_eq (n : ℕ) :
    count n = (n : ℚ) ^ 5 + 5 * n ^ 4 + 10 * n ^ 3 + 4 * n ^ 2 + 3 * n + 1 := by
  let W := Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1)
  have hsum : count n = (Fintype.card { x : W // allowed (repeats x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) = true } : ℚ) := by
    unfold count
    have heq : (∑ a : Fin (n + 1), ∑ b : Fin (n + 1), ∑ c : Fin (n + 1),
        ∑ d : Fin (n + 1), ∑ e : Fin (n + 1),
          if allowed (repeats a b c d e) then (1 : ℚ) else 0) =
        ∑ x : W, if allowed (repeats x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) = true then (1 : ℚ) else 0 := by
      dsimp only [W]
      simp only [Fintype.sum_prod_type]
    rw [heq, Finset.sum_boole, Fintype.card_subtype]
  have hcompl := Fintype.card_subtype_compl (fun x : W => allowed (repeats x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) = true)
  have hW : Fintype.card W = (n + 1) ^ 5 := by
    simp [W, Fintype.card_prod, Fintype.card_fin]
    ring
  have hbad_eq : Fintype.card { x : W // ¬ allowed (repeats x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) = true } =
      Fintype.card { x : W // badPred x } := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun ⟨x, hx⟩ => ⟨x, Bool.eq_false_iff.mpr hx⟩
        invFun := fun ⟨x, hx⟩ => ⟨x, by simp [badPred] at hx; simp [hx]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hbad_sum : Fintype.card { x : W // badPred x } =
      Fintype.card { x : W // bad1 x } + Fintype.card { x : W // bad2 x } + Fintype.card { x : W // bad3 x } := by
    let e : { x : W // badPred x } ≃
        { x : W // bad1 x } ⊕ { x : W // bad2 x } ⊕ { x : W // bad3 x } :=
      { toFun := fun ⟨x, hx⟩ =>
          if h1 : bad1 x then Sum.inl ⟨x, h1⟩
          else if h2 : bad2 x then Sum.inr (Sum.inl ⟨x, h2⟩)
          else Sum.inr (Sum.inr ⟨x, ((badPred_iff x).mp hx).resolve_left h1 |>.resolve_left h2⟩)
        invFun
          | Sum.inl ⟨x, h1⟩ => ⟨x, (badPred_iff x).mpr (Or.inl h1)⟩
          | Sum.inr (Sum.inl ⟨x, h2⟩) => ⟨x, (badPred_iff x).mpr (Or.inr (Or.inl h2))⟩
          | Sum.inr (Sum.inr ⟨x, h3⟩) => ⟨x, (badPred_iff x).mpr (Or.inr (Or.inr h3))⟩
        left_inv := fun ⟨x, hx⟩ => by
          dsimp only
          split_ifs <;> rfl
        right_inv := fun y => by
          rcases y with ⟨x, h1⟩ | ⟨x, h2⟩ | ⟨x, h3⟩
          · simp [h1]
          · have nh1 : ¬ bad1 x := fun h => (bad_disjoint x).1 ⟨h, h2⟩
            simp [nh1, h2]
          · have nh1 : ¬ bad1 x := fun h => (bad_disjoint x).2.1 ⟨h, h3⟩
            have nh2 : ¬ bad2 x := fun h => (bad_disjoint x).2.2 ⟨h, h3⟩
            simp [nh1, nh2] }
    rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_sum]
    ring
  rw [hbad_eq, hbad_sum, card_bad1, card_bad2, card_bad3, hW] at hcompl
  have hgood_le : Fintype.card { x : W // allowed (repeats x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) = true } ≤ (n + 1) ^ 5 := by
    rw [← hW]
    exact Fintype.card_subtype_le _
  have hnat : Fintype.card { x : W // allowed (repeats x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) = true } +
      (2 * n * (n + 1) + 2 * n * n + 2 * n * n) = (n + 1) ^ 5 := by
    omega
  have hq : (Fintype.card { x : W // allowed (repeats x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) = true } : ℚ) +
      (2 * (n : ℚ) * (n + 1) + 2 * n * n + 2 * n * n) = (n + 1 : ℚ) ^ 5 := by
    exact_mod_cast hnat
  rw [hsum]
  linarith [hq]

lemma terms_recurrence (n : ℕ) :
    terms (n + 7) = 6 * terms (n + 6) - 15 * terms (n + 5) +
      20 * terms (n + 4) - 15 * terms (n + 3) + 6 * terms (n + 2) - terms (n + 1) := by
  simp only [terms, count_eq]
  push_cast
  ring

lemma coeff_X_pow_mul_mk (f : ℕ → ℚ) (d k : ℕ) :
    coeff k ((X : PowerSeries ℚ) ^ d * mk f) = if d ≤ k then f (k - d) else 0 := by
  rw [coeff_mul]
  by_cases hdk : d ≤ k
  · simp only [hdk, ↓reduceIte]
    rw [Finset.sum_eq_single (d, k - d)]
    · dsimp only
      rw [coeff_X_pow, if_pos rfl, one_mul, coeff_mk]
    · rintro ⟨a, b⟩ hab hne
      have ha : a ≠ d := by
        intro had
        apply hne
        ext
        · exact had
        · simp at hab
          omega
      dsimp only
      rw [coeff_X_pow, if_neg ha, zero_mul]
    · intro hnot
      exfalso
      apply hnot
      simp
      omega
  · simp only [hdk, ↓reduceIte]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    simp at hab
    have ha : a ≠ d := by omega
    dsimp only
    rw [coeff_X_pow, if_neg ha, zero_mul]

lemma gf_eq :
    (1 - X) ^ 6 * mk terms = (X * (24 + 71 * X + 34 * X ^ 2 - 18 * X ^ 3 + 10 * X ^ 4 - X ^ 5) :
      PowerSeries ℚ) := by
  have hpoly : (1 - X : PowerSeries ℚ) ^ 6 * mk terms =
      mk terms - C 6 * (X ^ 1 * mk terms) + C 15 * (X ^ 2 * mk terms) -
      C 20 * (X ^ 3 * mk terms) + C 15 * (X ^ 4 * mk terms) -
      C 6 * (X ^ 5 * mk terms) + X ^ 6 * mk terms := by
    simp only [show (C 6 : PowerSeries ℚ) = 6 from rfl,
      show (C 15 : PowerSeries ℚ) = 15 from rfl,
      show (C 20 : PowerSeries ℚ) = 20 from rfl]
    ring
  have hrhs : (X * (24 + 71 * X + 34 * X ^ 2 - 18 * X ^ 3 + 10 * X ^ 4 - X ^ 5) : PowerSeries ℚ) =
      C 24 * X ^ 1 + C 71 * X ^ 2 + C 34 * X ^ 3 - C 18 * X ^ 4 + C 10 * X ^ 5 - X ^ 6 := by
    simp only [show (C 24 : PowerSeries ℚ) = 24 from rfl,
      show (C 71 : PowerSeries ℚ) = 71 from rfl,
      show (C 34 : PowerSeries ℚ) = 34 from rfl,
      show (C 18 : PowerSeries ℚ) = 18 from rfl,
      show (C 10 : PowerSeries ℚ) = 10 from rfl]
    ring
  rw [hpoly, hrhs]
  ext k
  have ht0 : terms 0 = 0 := rfl
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul_mk, coeff_mk, coeff_X_pow]
  rcases k with _ | _ | _ | _ | _ | _ | _ | m
  · simp [ht0]
  · simp [terms, count_eq]; norm_num
  · simp [terms, count_eq]; norm_num
  · simp [terms, count_eq]; norm_num
  · simp [terms, count_eq]; norm_num
  · simp [terms, count_eq]; norm_num
  · simp [terms, count_eq]; norm_num
  · have hr := terms_recurrence m
    have h1 : 1 ≤ m + 7 := by omega
    have h2 : 2 ≤ m + 7 := by omega
    have h3 : 3 ≤ m + 7 := by omega
    have h4 : 4 ≤ m + 7 := by omega
    have h5 : 5 ≤ m + 7 := by omega
    have h6 : 6 ≤ m + 7 := by omega
    simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte]
    have hn1 : m + 7 ≠ 1 := by omega
    have hn2 : m + 7 ≠ 2 := by omega
    have hn3 : m + 7 ≠ 3 := by omega
    have hn4 : m + 7 ≠ 4 := by omega
    have hn5 : m + 7 ≠ 5 := by omega
    have hn6 : m + 7 ≠ 6 := by omega
    simp only [hn1, hn2, hn3, hn4, hn5, hn6, ↓reduceIte, mul_zero, add_zero, sub_zero]
    rw [show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 = m + 7 by omega]
    rw [show m + 7 - 1 = m + 6 by omega,
      show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega,
      show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega,
      show m + 7 - 6 = m + 1 by omega]
    linarith [hr]

theorem main_proof :
    (∀ n : ℕ, count n = (n : ℚ) ^ 5 + 5 * n ^ 4 + 10 * n ^ 3 + 4 * n ^ 2 + 3 * n + 1) ∧
    (∀ n : ℕ, terms (n + 7) = 6 * terms (n + 6) - 15 * terms (n + 5) +
      20 * terms (n + 4) - 15 * terms (n + 3) + 6 * terms (n + 2) - terms (n + 1)) ∧
    (1 - X) ^ 6 * mk terms = (X * (24 + 71 * X + 34 * X ^ 2 - 18 * X ^ 3 + 10 * X ^ 4 - X ^ 5) :
      PowerSeries ℚ) :=
  ⟨count_eq, terms_recurrence, gf_eq⟩

end OMA.S_oeis_a269496_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a269496.main :=
  OMA.S_oeis_a269496_proof.main_proof
