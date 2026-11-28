import OMAReductions.R_Erdos128_erdos_128_R2_H2_R1

/-!
# Reduction Erdos128.erdos_128.R2.H2.R1.H2.R1 of step Erdos128.erdos_128.R2.H2.R1.H2

Extends the weight-10 Grötzsch twin core `M` (`|M| > 2n/3`, proved in `R2.H2.R1`) to the exact
16-vertex triangle-free core `C16 = M ∪ W9` covering more than `5n/6` vertices:

1. **Weight-9 classification (`grotzsch_indep_weight_eq_nine`)**: Among all 103 independent sets
   of the 11-vertex Grötzsch graph under vertex weights `(3,3,3,3,3, 2,2,2,2,2, 4)`, every profile
   of weight exactly `9` is one of the 5 sets `{v r, u r, u (r+2), u (r+3)}` (`r : Fin 5`).
2. **Triangle-free 16-vertex homomorphism (`grotzsch_core16_structure`)**: Every pair of classes in
   `M ∪ W9` not linked by the 16-vertex allowed-adjacency graph `G16` shares a common Grötzsch
   neighbor (`grotzsch_core16_diam_two`), hence cannot be adjacent in triangle-free `G`. Moreover
   `W9` is an independent set in `G`, every `W9(r)` can be adjacent in `C16` only to `M_{v r}` and
   `M_{u r}, M_{u (r+2)}, M_{u (r+3)}`, and `G16` is itself triangle-free.
3. **Sharp residual bound**: Weighted double counting `∑ wt(x) > (29/3) * n` with `wt ≤ 10` on `M`,
   `wt = 9` on `W9`, and `wt ≤ 8` on `R = V \ (M ∪ W9)` yields unconditionally
   `3 * |W9| + 6 * |R| < n`, hence `5 * n < 6 * |M ∪ W9|` (upgrading `2/3` to `5/6`) and
   `6 * |R| < n`.

Splits `Erdos128.erdos_128.R2.H2.R1.H2` into two complementary regimes carrying the full `C16`
structure:
- `H1`: Near-pure Grötzsch twin core (`9 * n ≤ 10 * |M|`).
- `H2`: Significant non-twin mass (`10 * |M| < 9 * n`, with `2n/3 < |M|` and `|M ∪ W9| > 5n/6`).
-/

-- Credit: @sanchan (extending OMA.R_Erdos128_erdos_128_R2_H2_R1 by @therationalpie)

namespace OMA.R_Erdos128_erdos_128_R2_H2_R1_H2_R1

open Finset SimpleGraph OMA.R_Erdos128_erdos_128_R2_H2_R1

/- ### Part 1: Exact weight-9 Grötzsch profile classification -/

lemma grotzsch_indep_weight_eq_nine :
    ∀ (bv bu : Fin 5 → Bool) (bw : Bool),
      (∀ i : Fin 5,
        !(bv i && bv (i + 1)) ∧
        !(bu i && bv (i + 1)) ∧
        !(bu i && bv (i + 4)) ∧
        !(bw && bu i)) →
      3 * (∑ i : Fin 5, if bv i then 1 else 0) +
      2 * (∑ i : Fin 5, if bu i then 1 else 0) +
      (if bw then 4 else 0) = 9 →
      ∃ r : Fin 5,
        (∀ i : Fin 5, bv i = decide (i = r)) ∧
        (∀ i : Fin 5, bu i = decide (i = r ∨ i = r + 2 ∨ i = r + 3)) ∧
        bw = false := by
  intro bv bu bw h heq
  rw [sum_fin5_bool_toNat bv, sum_fin5_bool_toNat bu, bool_ite4_eq_toNat bw] at heq
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  simp only [Fin.reduceAdd] at h0 h1 h2 h3 h4
  have c0 := bool_toNat_le_one (bu 0); have c1 := bool_toNat_le_one (bu 1)
  have c2 := bool_toNat_le_one (bu 2); have c3 := bool_toNat_le_one (bu 3)
  have c4 := bool_toNat_le_one (bu 4)
  have cw := bool_toNat_le_one bw
  rcases c5_cases (bv 0) (bv 1) (bv 2) (bv 3) (bv 4) h0.1 h1.1 h2.1 h3.1 h4.1 with
    ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ |
    ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ |
    ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩ |
    ⟨v0, v1, v2, v3, v4⟩ | ⟨v0, v1, v2, v3, v4⟩
  · -- 0 v's: even weight != 9
    rw [v0, v1, v2, v3, v4] at heq
    simp only [Bool.toNat_false] at heq; omega
  · -- r = 0: bv 0 = true
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · have z1 := bool_zero_of_pair v0 h1.2.2.1
      have z4 := bool_zero_of_pair v0 h4.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq
      have u0 := bool_eq_true_of_toNat_one (by omega : (bu 0).toNat = 1)
      have u1 := bool_eq_false_of_toNat_zero z1
      have u2 := bool_eq_true_of_toNat_one (by omega : (bu 2).toNat = 1)
      have u3 := bool_eq_true_of_toNat_one (by omega : (bu 3).toNat = 1)
      have u4 := bool_eq_false_of_toNat_zero z4
      exact ⟨0, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- r = 1: bv 1 = true
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · have z0 := bool_zero_of_pair v1 h0.2.1
      have z2 := bool_zero_of_pair v1 h2.2.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq
      have u0 := bool_eq_false_of_toNat_zero z0
      have u1 := bool_eq_true_of_toNat_one (by omega : (bu 1).toNat = 1)
      have u2 := bool_eq_false_of_toNat_zero z2
      have u3 := bool_eq_true_of_toNat_one (by omega : (bu 3).toNat = 1)
      have u4 := bool_eq_true_of_toNat_one (by omega : (bu 4).toNat = 1)
      exact ⟨1, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- r = 2: bv 2 = true
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · have z1 := bool_zero_of_pair v2 h1.2.1
      have z3 := bool_zero_of_pair v2 h3.2.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq
      have u0 := bool_eq_true_of_toNat_one (by omega : (bu 0).toNat = 1)
      have u1 := bool_eq_false_of_toNat_zero z1
      have u2 := bool_eq_true_of_toNat_one (by omega : (bu 2).toNat = 1)
      have u3 := bool_eq_false_of_toNat_zero z3
      have u4 := bool_eq_true_of_toNat_one (by omega : (bu 4).toNat = 1)
      exact ⟨2, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- r = 3: bv 3 = true
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · have z2 := bool_zero_of_pair v3 h2.2.1
      have z4 := bool_zero_of_pair v3 h4.2.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq
      have u0 := bool_eq_true_of_toNat_one (by omega : (bu 0).toNat = 1)
      have u1 := bool_eq_true_of_toNat_one (by omega : (bu 1).toNat = 1)
      have u2 := bool_eq_false_of_toNat_zero z2
      have u3 := bool_eq_true_of_toNat_one (by omega : (bu 3).toNat = 1)
      have u4 := bool_eq_false_of_toNat_zero z4
      exact ⟨3, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- r = 4: bv 4 = true
    rw [v0, v1, v2, v3, v4] at heq
    cases bw
    · have z0 := bool_zero_of_pair v4 h0.2.2.1
      have z3 := bool_zero_of_pair v4 h3.2.1
      simp only [Bool.toNat_true, Bool.toNat_false] at heq
      have u0 := bool_eq_false_of_toNat_zero z0
      have u1 := bool_eq_true_of_toNat_one (by omega : (bu 1).toNat = 1)
      have u2 := bool_eq_true_of_toNat_one (by omega : (bu 2).toNat = 1)
      have u3 := bool_eq_false_of_toNat_zero z3
      have u4 := bool_eq_true_of_toNat_one (by omega : (bu 4).toNat = 1)
      exact ⟨4, fin5_eq_of_vals v0 v1 v2 v3 v4, fin5_eq_of_vals u0 u1 u2 u3 u4, rfl⟩
    · have := bool_zero_of_pair' h0.2.2.2; have := bool_zero_of_pair' h1.2.2.2
      have := bool_zero_of_pair' h2.2.2.2; have := bool_zero_of_pair' h3.2.2.2
      have := bool_zero_of_pair' h4.2.2.2
      simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · -- 2 v's: even weight != 9
    rw [v0, v1, v2, v3, v4] at heq; simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · rw [v0, v1, v2, v3, v4] at heq; simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · rw [v0, v1, v2, v3, v4] at heq; simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · rw [v0, v1, v2, v3, v4] at heq; simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega
  · rw [v0, v1, v2, v3, v4] at heq; simp only [Bool.toNat_true, Bool.toNat_false] at heq; omega

/- ### Part 2: Common-neighbor exclusion on the 16-vertex extended core -/

lemma grotzsch_core16_diam_two (t1 t2 : Fin 4) (i1 i2 : Fin 5) :
    ¬ ((t1 = 0 ∧ t2 = 0 ∧ (i2 = i1 + 1 ∨ i2 = i1 + 4)) ∨
       (t1 = 0 ∧ t2 = 1 ∧ (i2 = i1 + 1 ∨ i2 = i1 + 4)) ∨
       (t1 = 1 ∧ t2 = 0 ∧ (i2 = i1 + 1 ∨ i2 = i1 + 4)) ∨
       (t1 = 1 ∧ t2 = 2) ∨
       (t1 = 2 ∧ t2 = 1) ∨
       (t1 = 3 ∧ t2 = 0 ∧ i2 = i1) ∨
       (t1 = 0 ∧ t2 = 3 ∧ i2 = i1) ∨
       (t1 = 3 ∧ t2 = 1 ∧ (i2 = i1 ∨ i2 = i1 + 2 ∨ i2 = i1 + 3)) ∨
       (t1 = 1 ∧ t2 = 3 ∧ (i1 = i2 ∨ i1 = i2 + 2 ∨ i1 = i2 + 3))) →
    (∃ j : Fin 5,
      ((t1 = 0 ∧ (j = i1 + 1 ∨ j = i1 + 4)) ∨
       (t1 = 1 ∧ (j = i1 + 1 ∨ j = i1 + 4)) ∨
       (t1 = 3 ∧ j = i1)) ∧
      ((t2 = 0 ∧ (j = i2 + 1 ∨ j = i2 + 4)) ∨
       (t2 = 1 ∧ (j = i2 + 1 ∨ j = i2 + 4)) ∨
       (t2 = 3 ∧ j = i2))) ∨
    (∃ j : Fin 5,
      ((t1 = 0 ∧ (j = i1 + 1 ∨ j = i1 + 4)) ∨
       t1 = 2 ∨
       (t1 = 3 ∧ (j = i1 ∨ j = i1 + 2 ∨ j = i1 + 3))) ∧
      ((t2 = 0 ∧ (j = i2 + 1 ∨ j = i2 + 4)) ∨
       t2 = 2 ∨
       (t2 = 3 ∧ (j = i2 ∨ j = i2 + 2 ∨ j = i2 + 3)))) ∨
    (t1 = 1 ∧ t2 = 1) := by
  intro hnot
  have hrel : i1 = i2 ∨ i2 = i1 + 1 ∨ i2 = i1 + 2 ∨ i2 = i1 + 3 ∨ i2 = i1 + 4 := by
    have hd : i2 - i1 = 0 ∨ i2 - i1 = 1 ∨ i2 - i1 = 2 ∨ i2 - i1 = 3 ∨ i2 - i1 = 4 := by
      generalize i2 - i1 = d
      fin_cases d <;> simp
    rcases hd with h | h | h | h | h
    · left; exact (sub_eq_zero.mp h).symm
    · right; left; exact eq_add_of_sub_eq' h
    · right; right; left; exact eq_add_of_sub_eq' h
    · right; right; right; left; exact eq_add_of_sub_eq' h
    · right; right; right; right; exact eq_add_of_sub_eq' h
  fin_cases t1 <;> fin_cases t2
  · rcases hrel with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i1 + 1, by simp⟩
    · exact absurd (Or.inl ⟨rfl, rfl, Or.inl rfl⟩) hnot
    · exact Or.inl ⟨i1 + 1, by simp [add_assoc]⟩
    · exact Or.inl ⟨i1 + 4, by simp [add_assoc]⟩
    · exact absurd (Or.inl ⟨rfl, rfl, Or.inr rfl⟩) hnot
  · rcases hrel with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i1 + 1, by simp⟩
    · exact absurd (Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩)) hnot
    · exact Or.inl ⟨i1 + 1, by simp [add_assoc]⟩
    · exact Or.inl ⟨i1 + 4, by simp [add_assoc]⟩
    · exact absurd (Or.inr (Or.inl ⟨rfl, rfl, Or.inr rfl⟩)) hnot
  · exact Or.inr (Or.inl ⟨i1 + 1, by simp⟩)
  · rcases hrel with rfl | rfl | rfl | rfl | rfl
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))) hnot
    · exact Or.inl ⟨i1 + 1, by simp⟩
    · exact Or.inr (Or.inl ⟨i1 + 4, by simp [add_assoc]⟩)
    · exact Or.inr (Or.inl ⟨i1 + 1, by simp [add_assoc]⟩)
    · exact Or.inl ⟨i1 + 4, by simp⟩
  · rcases hrel with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i1 + 1, by simp⟩
    · exact absurd (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩))) hnot
    · exact Or.inl ⟨i1 + 1, by simp [add_assoc]⟩
    · exact Or.inl ⟨i1 + 4, by simp [add_assoc]⟩
    · exact absurd (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inr rfl⟩))) hnot
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hnot
  · rcases hrel with rfl | rfl | rfl | rfl | rfl
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, Or.inl rfl⟩)))))))) hnot
    · exact Or.inl ⟨i1 + 1, by simp⟩
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, Or.inr (Or.inr (by simp [add_assoc]))⟩)))))))) hnot
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, Or.inr (Or.inl (by simp [add_assoc]))⟩)))))))) hnot
    · exact Or.inl ⟨i1 + 4, by simp⟩
  · exact Or.inr (Or.inl ⟨i2 + 1, by simp⟩)
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))) hnot
  · exact Or.inr (Or.inl ⟨0, by simp⟩)
  · exact Or.inr (Or.inl ⟨i2, by simp⟩)
  · rcases hrel with rfl | rfl | rfl | rfl | rfl
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))) hnot
    · exact Or.inl ⟨i1, by simp [add_assoc]⟩
    · exact Or.inr (Or.inl ⟨i1 + 3, by simp [add_assoc]⟩)
    · exact Or.inr (Or.inl ⟨i1 + 2, by simp [add_assoc]⟩)
    · exact Or.inl ⟨i1, by simp [add_assoc]⟩
  · rcases hrel with rfl | rfl | rfl | rfl | rfl
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩)))))))) hnot
    · exact Or.inl ⟨i1, by simp [add_assoc]⟩
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inr (Or.inl rfl)⟩)))))))) hnot
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inr (Or.inr rfl)⟩)))))))) hnot
    · exact Or.inl ⟨i1, by simp [add_assoc]⟩
  · exact Or.inr (Or.inl ⟨i1, by simp⟩)
  · rcases hrel with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨i1, by simp⟩)
    · exact Or.inr (Or.inl ⟨i1 + 3, by simp [add_assoc]⟩)
    · exact Or.inr (Or.inl ⟨i1 + 2, by simp⟩)
    · exact Or.inr (Or.inl ⟨i1 + 3, by simp⟩)
    · exact Or.inr (Or.inl ⟨i1 + 2, by simp [add_assoc]⟩)

/- ### Part 3: Full 16-vertex triangle-free core and sharp residual bound -/

lemma grotzsch_core16_structure {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcf : G.CliqueFree 3)
    (hmin : ∀ z : V, Fintype.card V < 3 * (G.neighborSet z).ncard)
    (v u : Fin 5 → V) (w : V)
    (hg : ∀ i : Fin 5,
      G.Adj (v i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 4)) ∧
      G.Adj w (u i)) :
    ∃ (M W9 : Set V) (tag : V → Fin 4) (idx : V → Fin 5),
      Disjoint M W9 ∧
      2 * Fintype.card V < 3 * M.ncard ∧
      3 * W9.ncard + 6 * (Fintype.card V - M.ncard - W9.ncard) < Fintype.card V ∧
      5 * Fintype.card V < 6 * (M ∪ W9).ncard ∧
      G.IsIndepSet W9 ∧
      (∀ x ∈ M, tag x = 0 ∨ tag x = 1 ∨ tag x = 2) ∧
      (∀ x ∈ W9, tag x = 3) ∧
      ∀ x ∈ M ∪ W9, ∀ y ∈ M ∪ W9, G.Adj x y →
        (tag x = 0 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 0 ∧ tag y = 1 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 1 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 1 ∧ tag y = 2) ∨
        (tag x = 2 ∧ tag y = 1) ∨
        (tag x = 3 ∧ tag y = 0 ∧ idx y = idx x) ∨
        (tag x = 0 ∧ tag y = 3 ∧ idx y = idx x) ∨
        (tag x = 3 ∧ tag y = 1 ∧ (idx y = idx x ∨ idx y = idx x + 2 ∨ idx y = idx x + 3)) ∨
        (tag x = 1 ∧ tag y = 3 ∧ (idx x = idx y ∨ idx x = idx y + 2 ∨ idx x = idx y + 3)) := by
  let wt : V → ℕ := fun x =>
    3 * (∑ i : Fin 5, if decide (G.Adj x (v i)) then (1 : ℕ) else 0) +
    2 * (∑ i : Fin 5, if decide (G.Adj x (u i)) then (1 : ℕ) else 0) +
    (if decide (G.Adj x w) then (4 : ℕ) else 0)
  have hwt_le : ∀ x : V, wt x ≤ 10 := fun x =>
    grotzsch_indep_weight_le
      (fun i => decide (G.Adj x (v i)))
      (fun i => decide (G.Adj x (u i)))
      (decide (G.Adj x w))
      (grotzsch_profile_valid hcf v u w hg x)
  let Mf : Finset V := Finset.univ.filter (fun x => wt x = 10)
  let Wf : Finset V := Finset.univ.filter (fun x => wt x = 9)
  let Rf : Finset V := Finset.univ.filter (fun x => wt x ≤ 8)
  have hdisj_MW : Disjoint Mf Wf := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have a := (Finset.mem_filter.mp h1).2
    have b := (Finset.mem_filter.mp h2).2
    omega
  have hdisj_C_R : Disjoint (Mf ∪ Wf) Rf := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have c := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with hM | hW
    · have a := (Finset.mem_filter.mp hM).2; omega
    · have b := (Finset.mem_filter.mp hW).2; omega
  have huniv_eq : (Mf ∪ Wf) ∪ Rf = Finset.univ := by
    ext x
    dsimp only [Mf, Wf, Rf]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have hle := hwt_le x
    omega
  have hcard_part : Mf.card + Wf.card + Rf.card = Fintype.card V := by
    have h1 := Finset.card_union_of_disjoint hdisj_C_R
    have h2 := Finset.card_union_of_disjoint hdisj_MW
    rw [huniv_eq, Finset.card_univ] at h1
    omega
  have hsum_gt : 29 * Fintype.card V < 3 * ∑ x : V, wt x := by
    dsimp only [wt]
    rw [grotzsch_weighted_sum_eq G v u w, Fin.sum_univ_five, Fin.sum_univ_five]
    have hv0 := hmin (v 0); have hv1 := hmin (v 1); have hv2 := hmin (v 2); have hv3 := hmin (v 3); have hv4 := hmin (v 4)
    have hu0 := hmin (u 0); have hu1 := hmin (u 1); have hu2 := hmin (u 2); have hu3 := hmin (u 3); have hu4 := hmin (u 4)
    have hw := hmin w
    have sv : 5 * Fintype.card V < 3 * ((G.neighborSet (v 0)).ncard + (G.neighborSet (v 1)).ncard +
        (G.neighborSet (v 2)).ncard + (G.neighborSet (v 3)).ncard + (G.neighborSet (v 4)).ncard) := by
      have h01 : 2 * Fintype.card V < 3 * ((G.neighborSet (v 0)).ncard + (G.neighborSet (v 1)).ncard) := by omega
      have h23 : 2 * Fintype.card V < 3 * ((G.neighborSet (v 2)).ncard + (G.neighborSet (v 3)).ncard) := by omega
      omega
    have su : 5 * Fintype.card V < 3 * ((G.neighborSet (u 0)).ncard + (G.neighborSet (u 1)).ncard +
        (G.neighborSet (u 2)).ncard + (G.neighborSet (u 3)).ncard + (G.neighborSet (u 4)).ncard) := by
      have h01 : 2 * Fintype.card V < 3 * ((G.neighborSet (u 0)).ncard + (G.neighborSet (u 1)).ncard) := by omega
      have h23 : 2 * Fintype.card V < 3 * ((G.neighborSet (u 2)).ncard + (G.neighborSet (u 3)).ncard) := by omega
      omega
    generalize (G.neighborSet (v 0)).ncard + (G.neighborSet (v 1)).ncard +
        (G.neighborSet (v 2)).ncard + (G.neighborSet (v 3)).ncard + (G.neighborSet (v 4)).ncard = Sv at sv ⊢
    generalize (G.neighborSet (u 0)).ncard + (G.neighborSet (u 1)).ncard +
        (G.neighborSet (u 2)).ncard + (G.neighborSet (u 3)).ncard + (G.neighborSet (u 4)).ncard = Su at su ⊢
    omega
  have hsum_ub : ∑ x : V, wt x ≤ 10 * Mf.card + 9 * Wf.card + 8 * Rf.card := by
    have hsplit : ∑ x : V, wt x = (∑ x ∈ Mf, wt x) + (∑ x ∈ Wf, wt x) + (∑ x ∈ Rf, wt x) := by
      rw [← Finset.sum_union hdisj_MW, ← Finset.sum_union hdisj_C_R, huniv_eq]
    have hMsum : ∑ x ∈ Mf, wt x = 10 * Mf.card := by
      rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2),
          Finset.sum_const, smul_eq_mul, mul_comm]
    have hWsum : ∑ x ∈ Wf, wt x = 9 * Wf.card := by
      rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2),
          Finset.sum_const, smul_eq_mul, mul_comm]
    have hRsum : ∑ x ∈ Rf, wt x ≤ 8 * Rf.card := by
      calc ∑ x ∈ Rf, wt x ≤ ∑ _x ∈ Rf, (8 : ℕ) :=
            Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
        _ = 8 * Rf.card := by simp only [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  -- Classify every x ∈ Mf ∪ Wf into its exact (tag, idx) in Fin 4 × Fin 5
  have hclass : ∀ x : V, x ∈ Mf ∪ Wf →
      ∃ (t : Fin 4) (r : Fin 5),
        (x ∈ Mf → t = 0 ∨ t = 1 ∨ t = 2) ∧
        (x ∈ Wf → t = 3) ∧
        ((t = 0 ∧ (∀ i : Fin 5, G.Adj x (v i) ↔ (i = r + 1 ∨ i = r + 4)) ∧
                  (∀ i : Fin 5, G.Adj x (u i) ↔ (i = r + 1 ∨ i = r + 4)) ∧ ¬ G.Adj x w) ∨
         (t = 1 ∧ (∀ i : Fin 5, G.Adj x (v i) ↔ (i = r + 1 ∨ i = r + 4)) ∧
                  (∀ i : Fin 5, ¬ G.Adj x (u i)) ∧ G.Adj x w) ∨
         (t = 2 ∧ (∀ i : Fin 5, ¬ G.Adj x (v i)) ∧
                  (∀ i : Fin 5, G.Adj x (u i)) ∧ ¬ G.Adj x w) ∨
         (t = 3 ∧ (∀ i : Fin 5, G.Adj x (v i) ↔ i = r) ∧
                  (∀ i : Fin 5, G.Adj x (u i) ↔ (i = r ∨ i = r + 2 ∨ i = r + 3)) ∧ ¬ G.Adj x w)) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hM | hW
    · have hnotW : x ∉ Wf := Finset.disjoint_left.mp hdisj_MW hM
      have hwt10 : wt x = 10 := (Finset.mem_filter.mp hM).2
      have hc := grotzsch_indep_weight_eq_ten
        (fun i => decide (G.Adj x (v i)))
        (fun i => decide (G.Adj x (u i)))
        (decide (G.Adj x w))
        (grotzsch_profile_valid hcf v u w hg x) hwt10
      rcases hc with ⟨r, hbv, hbu, hbw⟩ | ⟨r, hbv, hbu, hbw⟩ | ⟨hbv, hbu, hbw⟩
      · refine ⟨0, r, fun _ => Or.inl rfl, fun hw => (hnotW hw).elim, Or.inl ⟨rfl, ?_, ?_, ?_⟩⟩
        · intro i; exact decide_eq_decide.mp (hbv i)
        · intro i; exact decide_eq_decide.mp (hbu i)
        · exact of_decide_eq_false hbw
      · refine ⟨1, r, fun _ => Or.inr (Or.inl rfl), fun hw => (hnotW hw).elim, Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)⟩
        · intro i; exact decide_eq_decide.mp (hbv i)
        · intro i; exact of_decide_eq_false (hbu i)
        · exact of_decide_eq_true hbw
      · refine ⟨2, 0, fun _ => Or.inr (Or.inr rfl), fun hw => (hnotW hw).elim, Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩))⟩
        · intro i; exact of_decide_eq_false (hbv i)
        · intro i; exact of_decide_eq_true (hbu i)
        · exact of_decide_eq_false hbw
    · have hnotM : x ∉ Mf := Finset.disjoint_right.mp hdisj_MW hW
      have hwt9 : wt x = 9 := (Finset.mem_filter.mp hW).2
      have hc := grotzsch_indep_weight_eq_nine
        (fun i => decide (G.Adj x (v i)))
        (fun i => decide (G.Adj x (u i)))
        (decide (G.Adj x w))
        (grotzsch_profile_valid hcf v u w hg x) hwt9
      obtain ⟨r, hbv, hbu, hbw⟩ := hc
      refine ⟨3, r, fun hm => (hnotM hm).elim, fun _ => rfl, Or.inr (Or.inr (Or.inr ⟨rfl, ?_, ?_, ?_⟩))⟩
      · intro i; exact decide_eq_decide.mp (hbv i)
      · intro i; exact decide_eq_decide.mp (hbu i)
      · exact of_decide_eq_false hbw
  choose tag' idx' hspec using fun (x : {x : V // x ∈ Mf ∪ Wf}) => hclass x.1 x.2
  let tag : V → Fin 4 := fun x => if hx : x ∈ Mf ∪ Wf then tag' ⟨x, hx⟩ else 0
  let idx : V → Fin 5 := fun x => if hx : x ∈ Mf ∪ Wf then idx' ⟨x, hx⟩ else 0
  have hadj16 : ∀ x ∈ (Mf : Set V) ∪ (Wf : Set V), ∀ y ∈ (Mf : Set V) ∪ (Wf : Set V), G.Adj x y →
      (tag x = 0 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
      (tag x = 0 ∧ tag y = 1 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
      (tag x = 1 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
      (tag x = 1 ∧ tag y = 2) ∨
      (tag x = 2 ∧ tag y = 1) ∨
      (tag x = 3 ∧ tag y = 0 ∧ idx y = idx x) ∨
      (tag x = 0 ∧ tag y = 3 ∧ idx y = idx x) ∨
      (tag x = 3 ∧ tag y = 1 ∧ (idx y = idx x ∨ idx y = idx x + 2 ∨ idx y = idx x + 3)) ∨
      (tag x = 1 ∧ tag y = 3 ∧ (idx x = idx y ∨ idx x = idx y + 2 ∨ idx x = idx y + 3)) := by
    intro x hx y hy hxy
    have hx' : x ∈ Mf ∪ Wf := by simpa [Finset.mem_union] using hx
    have hy' : y ∈ Mf ∪ Wf := by simpa [Finset.mem_union] using hy
    have hsx := (hspec ⟨x, hx'⟩).2.2
    have hsy := (hspec ⟨y, hy'⟩).2.2
    simp only [tag, idx, dif_pos hx', dif_pos hy']
    by_contra hnot
    have hdiam := grotzsch_core16_diam_two (tag' ⟨x, hx'⟩) (tag' ⟨y, hy'⟩) (idx' ⟨x, hx'⟩) (idx' ⟨y, hy'⟩) hnot
    rcases hdiam with ⟨j, hj1, hj2⟩ | ⟨j, hj1, hj2⟩ | ⟨ht1, ht2⟩
    · have hxj : G.Adj x (v j) := by
        rcases hsx with ⟨ht, hfv, _, _⟩ | ⟨ht, hfv, _, _⟩ | ⟨ht, _, _, _⟩ | ⟨ht, hfv, _, _⟩
        · rcases hj1 with ⟨_, h⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
          · exact (hfv j).mpr h
          · rw [ht] at h0; exact absurd h0 (by decide)
          · rw [ht] at h0; exact absurd h0 (by decide)
        · rcases hj1 with ⟨h0, _⟩ | ⟨_, h⟩ | ⟨h0, _⟩
          · rw [ht] at h0; exact absurd h0 (by decide)
          · exact (hfv j).mpr h
          · rw [ht] at h0; exact absurd h0 (by decide)
        · rcases hj1 with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ <;> (rw [ht] at h0; exact absurd h0 (by decide))
        · rcases hj1 with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, h⟩
          · rw [ht] at h0; exact absurd h0 (by decide)
          · rw [ht] at h0; exact absurd h0 (by decide)
          · exact (hfv j).mpr h
      have hyj : G.Adj y (v j) := by
        rcases hsy with ⟨ht, hfv, _, _⟩ | ⟨ht, hfv, _, _⟩ | ⟨ht, _, _, _⟩ | ⟨ht, hfv, _, _⟩
        · rcases hj2 with ⟨_, h⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
          · exact (hfv j).mpr h
          · rw [ht] at h0; exact absurd h0 (by decide)
          · rw [ht] at h0; exact absurd h0 (by decide)
        · rcases hj2 with ⟨h0, _⟩ | ⟨_, h⟩ | ⟨h0, _⟩
          · rw [ht] at h0; exact absurd h0 (by decide)
          · exact (hfv j).mpr h
          · rw [ht] at h0; exact absurd h0 (by decide)
        · rcases hj2 with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ <;> (rw [ht] at h0; exact absurd h0 (by decide))
        · rcases hj2 with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, h⟩
          · rw [ht] at h0; exact absurd h0 (by decide)
          · rw [ht] at h0; exact absurd h0 (by decide)
          · exact (hfv j).mpr h
      exact not_adj_both_of_cliqueFree hcf hxj.symm hyj.symm hxy
    · have hxj : G.Adj x (u j) := by
        rcases hsx with ⟨ht, _, hfu, _⟩ | ⟨ht, _, _, _⟩ | ⟨ht, _, hfu, _⟩ | ⟨ht, _, hfu, _⟩
        · rcases hj1 with ⟨_, h⟩ | h0 | ⟨h0, _⟩
          · exact (hfu j).mpr h
          · rw [ht] at h0; exact absurd h0 (by decide)
          · rw [ht] at h0; exact absurd h0 (by decide)
        · rcases hj1 with ⟨h0, _⟩ | h0 | ⟨h0, _⟩ <;> (rw [ht] at h0; exact absurd h0 (by decide))
        · exact hfu j
        · rcases hj1 with ⟨h0, _⟩ | h0 | ⟨_, h⟩
          · rw [ht] at h0; exact absurd h0 (by decide)
          · rw [ht] at h0; exact absurd h0 (by decide)
          · exact (hfu j).mpr h
      have hyj : G.Adj y (u j) := by
        rcases hsy with ⟨ht, _, hfu, _⟩ | ⟨ht, _, _, _⟩ | ⟨ht, _, hfu, _⟩ | ⟨ht, _, hfu, _⟩
        · rcases hj2 with ⟨_, h⟩ | h0 | ⟨h0, _⟩
          · exact (hfu j).mpr h
          · rw [ht] at h0; exact absurd h0 (by decide)
          · rw [ht] at h0; exact absurd h0 (by decide)
        · rcases hj2 with ⟨h0, _⟩ | h0 | ⟨h0, _⟩ <;> (rw [ht] at h0; exact absurd h0 (by decide))
        · exact hfu j
        · rcases hj2 with ⟨h0, _⟩ | h0 | ⟨_, h⟩
          · rw [ht] at h0; exact absurd h0 (by decide)
          · rw [ht] at h0; exact absurd h0 (by decide)
          · exact (hfu j).mpr h
      exact not_adj_both_of_cliqueFree hcf hxj.symm hyj.symm hxy
    · have hxw : G.Adj x w := by
        rcases hsx with ⟨ht, _, _, _⟩ | ⟨_, _, _, hfw⟩ | ⟨ht, _, _, _⟩ | ⟨ht, _, _, _⟩
        · rw [ht] at ht1; exact absurd ht1 (by decide)
        · exact hfw
        · rw [ht] at ht1; exact absurd ht1 (by decide)
        · rw [ht] at ht1; exact absurd ht1 (by decide)
      have hyw : G.Adj y w := by
        rcases hsy with ⟨ht, _, _, _⟩ | ⟨_, _, _, hfw⟩ | ⟨ht, _, _, _⟩ | ⟨ht, _, _, _⟩
        · rw [ht] at ht2; exact absurd ht2 (by decide)
        · exact hfw
        · rw [ht] at ht2; exact absurd ht2 (by decide)
        · rw [ht] at ht2; exact absurd ht2 (by decide)
      exact not_adj_both_of_cliqueFree hcf hxw.symm hyw.symm hxy
  have hMtag : ∀ x ∈ (Mf : Set V), tag x = 0 ∨ tag x = 1 ∨ tag x = 2 := by
    intro x hx
    have hxM : x ∈ Mf := Finset.mem_coe.mp hx
    have hxU : x ∈ Mf ∪ Wf := Finset.mem_union_left _ hxM
    simp only [tag, dif_pos hxU]
    exact (hspec ⟨x, hxU⟩).1 hxM
  have hWtag : ∀ x ∈ (Wf : Set V), tag x = 3 := by
    intro x hx
    have hxW : x ∈ Wf := Finset.mem_coe.mp hx
    have hxU : x ∈ Mf ∪ Wf := Finset.mem_union_right _ hxW
    simp only [tag, dif_pos hxU]
    exact (hspec ⟨x, hxU⟩).2.1 hxW
  have hWindep : G.IsIndepSet (Wf : Set V) := by
    intro x hx y hy _ hxy
    have h1 := hadj16 x (Set.mem_union_right _ hx) y (Set.mem_union_right _ hy) hxy
    have htx := hWtag x hx
    have hty := hWtag y hy
    rw [htx, hty] at h1
    rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ <;>
      exact absurd h (by decide)
  have hMnc : (Mf : Set V).ncard = Mf.card := Set.ncard_coe_finset Mf
  have hWnc : (Wf : Set V).ncard = Wf.card := Set.ncard_coe_finset Wf
  have hUnc : ((Mf : Set V) ∪ (Wf : Set V)).ncard = Mf.card + Wf.card := by
    rw [← Finset.coe_union, Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj_MW]
  refine ⟨(Mf : Set V), (Wf : Set V), tag, idx, Finset.disjoint_coe.mpr hdisj_MW, ?_, ?_, ?_,
    hWindep, hMtag, hWtag, hadj16⟩
  · rw [hMnc]; omega
  · rw [hMnc, hWnc]; omega
  · rw [hUnc]; omega

/- ### Hypotheses and Main Reduction -/

/-- Near-pure Grötzsch twin-core regime (`9 * n ≤ 10 * |M|`), with the full 16-vertex
triangle-free extended core `M ∪ W9` covering `> 5n/6` vertices and `3 * |W9| + 6 * |R| < n`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    12 ≤ Fintype.card V →
    73 * Fintype.card V ^ 2 < 800 * G.edgeSet.ncard →
    500000 * G.edgeSet.ncard < 99999 * Fintype.card V ^ 2 →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
    ¬ G.Colorable 3 →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) →
    (∃ v : V, 29 * (G.neighborSet v).ncard ≤ 10 * Fintype.card V) →
    (∃ (M W9 : Set V) (tag : V → Fin 4) (idx : V → Fin 5),
      Disjoint M W9 ∧ 9 * Fintype.card V ≤ 10 * M.ncard ∧
      3 * W9.ncard + 6 * (Fintype.card V - M.ncard - W9.ncard) < Fintype.card V ∧
      5 * Fintype.card V < 6 * (M ∪ W9).ncard ∧ G.IsIndepSet W9 ∧
      (∀ x ∈ M, tag x = 0 ∨ tag x = 1 ∨ tag x = 2) ∧ (∀ x ∈ W9, tag x = 3) ∧
      ∀ x ∈ M ∪ W9, ∀ y ∈ M ∪ W9, G.Adj x y →
        (tag x = 0 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 0 ∧ tag y = 1 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 1 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 1 ∧ tag y = 2) ∨ (tag x = 2 ∧ tag y = 1) ∨
        (tag x = 3 ∧ tag y = 0 ∧ idx y = idx x) ∨ (tag x = 0 ∧ tag y = 3 ∧ idx y = idx x) ∨
        (tag x = 3 ∧ tag y = 1 ∧ (idx y = idx x ∨ idx y = idx x + 2 ∨ idx y = idx x + 3)) ∨
        (tag x = 1 ∧ tag y = 3 ∧ (idx x = idx y ∨ idx x = idx y + 2 ∨ idx x = idx y + 3))) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    ¬ G.CliqueFree 3

/-- Moderate twin-core regime (`2n/3 < |M| < 9n/10`), carrying the triangle-free 16-vertex
extended core `M ∪ W9` (`> 5n/6` vertices, `W9` independent, `3 * |W9| + 6 * |R| < n`). -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    12 ≤ Fintype.card V →
    73 * Fintype.card V ^ 2 < 800 * G.edgeSet.ncard →
    500000 * G.edgeSet.ncard < 99999 * Fintype.card V ^ 2 →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
    ¬ G.Colorable 3 →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) →
    (∃ v : V, 29 * (G.neighborSet v).ncard ≤ 10 * Fintype.card V) →
    (∃ (M W9 : Set V) (tag : V → Fin 4) (idx : V → Fin 5),
      Disjoint M W9 ∧ 2 * Fintype.card V < 3 * M.ncard ∧ 10 * M.ncard < 9 * Fintype.card V ∧
      3 * W9.ncard + 6 * (Fintype.card V - M.ncard - W9.ncard) < Fintype.card V ∧
      5 * Fintype.card V < 6 * (M ∪ W9).ncard ∧ G.IsIndepSet W9 ∧
      (∀ x ∈ M, tag x = 0 ∨ tag x = 1 ∨ tag x = 2) ∧ (∀ x ∈ W9, tag x = 3) ∧
      ∀ x ∈ M ∪ W9, ∀ y ∈ M ∪ W9, G.Adj x y →
        (tag x = 0 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 0 ∧ tag y = 1 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 1 ∧ tag y = 0 ∧ (idx y = idx x + 1 ∨ idx y = idx x + 4)) ∨
        (tag x = 1 ∧ tag y = 2) ∨ (tag x = 2 ∧ tag y = 1) ∨
        (tag x = 3 ∧ tag y = 0 ∧ idx y = idx x) ∨ (tag x = 0 ∧ tag y = 3 ∧ idx y = idx x) ∨
        (tag x = 3 ∧ tag y = 1 ∧ (idx y = idx x ∨ idx y = idx x + 2 ∨ idx y = idx x + 3)) ∨
        (tag x = 1 ∧ tag y = 3 ∧ (idx x = idx y ∨ idx x = idx y + 2 ∨ idx x = idx y + 3))) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    ¬ G.CliqueFree 3

theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R2_H2_R1.H2 := by
  intro h1 h2 V _ G h12 h73 h500 hind hcol3 hmin h29 ⟨v, u, w, hg⟩ _ hdense hcf
  classical
  obtain ⟨M, W9, tag, idx, hdisj, h23, hres, h56, hWind, hMtag, hWtag, hadj16⟩ :=
    grotzsch_core16_structure G hcf hmin v u w hg
  by_cases h90 : 9 * Fintype.card V ≤ 10 * M.ncard
  · exact h1 V G h12 h73 h500 hind hcol3 hmin h29
      ⟨M, W9, tag, idx, hdisj, h90, hres, h56, hWind, hMtag, hWtag, hadj16⟩ hdense hcf
  · push Not at h90
    exact h2 V G h12 h73 h500 hind hcol3 hmin h29
      ⟨M, W9, tag, idx, hdisj, h23, h90, hres, h56, hWind, hMtag, hWtag, hadj16⟩ hdense hcf

end OMA.R_Erdos128_erdos_128_R2_H2_R1_H2_R1
