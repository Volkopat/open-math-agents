import OMAReductions.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1_H3_R1

/-!
Step SumnerUniversalTournamentConjecture.sumner_conjecture.R1.H3.R1.H1:
Theorem 5.1 — Every oriented tree with Heart order h = 4 (and not Heart h = 3) embeds in every
no-source, no-sink tournament on 2n - 2 vertices (strictly improving Ai & Lian 2026: 2n + 3 -> 2n - 2,
and closing all n - k = 4 and all n = 9 trees in R1.H3).
Credit: @iskamag
-/

namespace ProofWork.HeartFourStep

open SimpleGraph Digraph SumnerUniversalTournamentConjecture
open OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1
open OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1_H3_R1

-- MODULE 3: S4+++ (cntP <= 1) Virtual-Vertex Right Skip + Left Cut Glue
-- ============================================================================

lemma s4ppp_right_p3_eq_4
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (_h01 : D.Adj (u ⟨0, by decide⟩) (u ⟨1, by decide⟩))
    (_h02 : D.Adj (u ⟨0, by decide⟩) (u ⟨2, by decide⟩))
    (_h03 : D.Adj (u ⟨0, by decide⟩) (u ⟨3, by decide⟩))
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno1A : ∀ x ∈ A, ¬ D.Adj (u ⟨1, by decide⟩) x)
    (hno2A : ∀ x ∈ A, ¬ D.Adj (u ⟨2, by decide⟩) x)
    (hRkP : ∃ rkP : ↥(Finset.univ.image u ∪ A) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (r p2 : ℕ) (hp2 : p2 = 2 ∨ p2 = 3) (hr5 : r + 5 ≤ 2 * n - 2)
    (hG01 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1, by omega⟩))
    (hG0p2 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + p2, by omega⟩))
    (hG04 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 4, by omega⟩))
    (hG0not : ¬ G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + (5 - p2), by omega⟩))
    (hLen : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r) :
    ∃ gR : ↥(Finset.univ.image u ∪ A) → Fin (Fintype.card V),
      Function.Injective gR ∧
      gR ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩ = ⟨r, by omega⟩ ∧
      gR ⟨u ⟨1, by decide⟩, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩ = ⟨r + 1, by omega⟩ ∧
      gR ⟨u ⟨2, by decide⟩, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩ = ⟨r + p2, by omega⟩ ∧
      gR ⟨u ⟨3, by decide⟩, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩ = ⟨r + 4, by omega⟩ ∧
      (∀ x : ↥(Finset.univ.image u ∪ A), x.1 ∈ A → r + 4 < (gR x).val) ∧
      (∀ x y : ↥(Finset.univ.image u ∪ A), D.Adj x.1 y.1 → G.Adj (σ (gR x)) (σ (gR y))) := by
  classical
  let H : Finset W := Finset.univ.image u
  have hu_memH : ∀ i : Fin 4, u i ∈ H := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let lenR : ℕ := 2 * n - 2 - r
  let lenV : ℕ := lenR - 2
  have hlenV_ge3 : 3 ≤ lenV := by omega
  -- Virtual digraph on Fin lenV: 0 -> r, 1 -> virtual vertex, k >= 2 -> r + k + 2
  let Gv : Digraph (Fin lenV) := ⟨fun a b =>
    if a.val = 1 then 2 ≤ b.val
    else if b.val = 1 then a.val = 0
    else
      let ia : ℕ := if a.val = 0 then r else r + a.val + 2
      let ib : ℕ := if b.val = 0 then r else r + b.val + 2
      G.Adj (σ ⟨ia, by have := a.isLt; dsimp only [ia, lenV, lenR]; split_ifs <;> omega⟩)
        (σ ⟨ib, by have := b.isLt; dsimp only [ib, lenV, lenR]; split_ifs <;> omega⟩)⟩
  let σv : Fin (Fintype.card (Fin lenV)) ≃ Fin lenV := finCongr (Fintype.card_fin lenV)
  have hRv : ∀ i j : Fin (Fintype.card (Fin lenV)), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card (Fin lenV)) =>
        i < k ∧ k ≤ j ∧ Gv.Adj (σv i) (σv k))).card := by
    intro i j hij
    have hij_v : i.val < j.val := hij
    have hj_lt : j.val < lenV := by simpa using j.isLt
    by_cases hi1 : i.val = 1
    · -- Virtual vertex 1 beats EVERY k with 2 <= k <= j!
      have hcard_all : (Finset.univ.filter (fun k : Fin (Fintype.card (Fin lenV)) =>
          i < k ∧ k ≤ j ∧ Gv.Adj (σv i) (σv k))).card = j.val - 1 := by
        have heq : (Finset.univ.filter (fun k : Fin (Fintype.card (Fin lenV)) =>
            i < k ∧ k ≤ j ∧ Gv.Adj (σv i) (σv k))).card = (Finset.Ioc 1 j.val).card := by
          refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            exact Finset.mem_Ioc.mpr ⟨by have : i.val < k.val := hk.1; omega, hk.2.1⟩
          · intro a _ b _ h; exact Fin.ext h
          · intro m hm
            have ⟨h1, h2⟩ := Finset.mem_Ioc.mp hm
            refine ⟨⟨m, by rw [Fintype.card_fin]; omega⟩, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨by change i.val < m; omega, by change m ≤ j.val; omega, ?_⟩
            simp only [Gv, σv, finCongr_apply, Fin.val_cast, hi1, ↓reduceIte]; omega
        rw [heq, Nat.card_Ioc]
      rw [hcard_all]; omega
    · by_cases hi0 : i.val = 0
      · by_cases hj1 : j.val = 1
        · have hmem : (⟨1, by rw [Fintype.card_fin]; omega⟩ : Fin (Fintype.card (Fin lenV))) ∈
              Finset.univ.filter (fun k : Fin (Fintype.card (Fin lenV)) =>
                i < k ∧ k ≤ j ∧ Gv.Adj (σv i) (σv k)) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨by change i.val < 1; omega, by change 1 ≤ j.val; omega, ?_⟩
            have hvi : (σv i).val = 0 := by simpa [σv] using hi0
            have hvk : (σv ⟨1, by rw [Fintype.card_fin]; omega⟩).val = 1 := by simp [σv]
            dsimp only [Gv]; rw [if_neg (by omega), if_pos hvk]; exact hvi
          have hpos : 1 ≤ (Finset.univ.filter (fun k : Fin (Fintype.card (Fin lenV)) =>
              i < k ∧ k ≤ j ∧ Gv.Adj (σv i) (σv k))).card := Finset.one_le_card.mpr ⟨_, hmem⟩
          omega
        · -- i = 0, j >= 2: compare against hR on [r, r + j + 2]!
          have hj2 : 2 ≤ j.val := by omega
          let i' : Fin (Fintype.card V) := ⟨r, by omega⟩
          let j' : Fin (Fintype.card V) := ⟨r + j.val + 2, by dsimp only [lenV, lenR] at hj_lt; omega⟩
          have h0 := hR i' j' (by change r < r + j.val + 2; omega)
          have hdiff : j'.val - i'.val = j.val + 2 := by dsimp only [i', j']; omega
          rw [hdiff] at h0
          let Sbig := Finset.univ.filter (fun k : Fin (Fintype.card V) => i' < k ∧ k ≤ j' ∧ G.Adj (σ i') (σ k))
          let Shead := Sbig.filter (fun k => k.val < r + 4)
          let Stail := Sbig.filter (fun k => r + 4 ≤ k.val)
          have hSsplit : Sbig.card = Shead.card + Stail.card := by
            have := card_filter_add_card_filter_not_eq Sbig (fun k => k.val < r + 4)
            have heq : Sbig.filter (fun k => ¬ k.val < r + 4) = Stail := by
              ext k; simp only [Stail, Finset.mem_filter, not_lt]
            rw [heq] at this; exact this.symm
          have hShead_le : Shead.card ≤ 2 := by
            have hsub : Shead ⊆ {⟨r + 1, by omega⟩, ⟨r + p2, by omega⟩} := by
              intro k hk
              have hk1 := (Finset.mem_filter.mp hk).1
              have hklt : k.val < r + 4 := (Finset.mem_filter.mp hk).2
              have hkb := (Finset.mem_filter.mp hk1).2
              have hkr : r < k.val := hkb.1
              simp only [Finset.mem_insert, Finset.mem_singleton]
              by_cases hkv1 : k.val = r + 1
              · exact Or.inl (Fin.ext hkv1)
              · by_cases hkvp : k.val = r + p2
                · exact Or.inr (Fin.ext hkvp)
                · exfalso
                  have hkv_eq : k = ⟨r + (5 - p2), by omega⟩ := Fin.ext (by dsimp only; omega)
                  rw [hkv_eq] at hkb
                  exact hG0not hkb.2.2
            exact (Finset.card_le_card hsub).trans Finset.card_le_two
          let Sv := Finset.univ.filter (fun k : Fin (Fintype.card (Fin lenV)) =>
            i < k ∧ k ≤ j ∧ Gv.Adj (σv i) (σv k))
          have h1mem : (⟨1, by rw [Fintype.card_fin]; omega⟩ : Fin (Fintype.card (Fin lenV))) ∈ Sv := by
            simp only [Sv, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨by change i.val < 1; omega, by change 1 ≤ j.val; omega, ?_⟩
            have hvi : (σv i).val = 0 := by simpa [σv] using hi0
            have hvk : (σv ⟨1, by rw [Fintype.card_fin]; omega⟩).val = 1 := by simp [σv]
            dsimp only [Gv]; rw [if_neg (by omega), if_pos hvk]; exact hvi
          have hStail_eq : Stail.card = (Sv.erase ⟨1, by rw [Fintype.card_fin]; omega⟩).card := by
            refine Finset.card_bij (fun k hk => ⟨k.val - r - 2, by
              have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2.2.1
              have h2 := (Finset.mem_filter.mp hk).2
              rw [Fintype.card_fin]; change k.val ≤ r + j.val + 2 at h1; omega⟩) ?_ ?_ ?_
            · intro k hk
              have hkb := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
              have hkge : r + 4 ≤ k.val := (Finset.mem_filter.mp hk).2
              have hkle : k.val ≤ r + j.val + 2 := hkb.2.1
              refine Finset.mem_erase.mpr ⟨fun h => by have := congrArg Fin.val h; dsimp only at this; omega, ?_⟩
              simp only [Sv, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨by change i.val < k.val - r - 2; omega, by change k.val - r - 2 ≤ j.val; omega, ?_⟩
              have hvi : (σv i).val = 0 := by simpa [σv] using hi0
              have hvk : (σv ⟨k.val - r - 2, by rw [Fintype.card_fin]; omega⟩).val = k.val - r - 2 := by simp [σv]
              dsimp only [Gv]; rw [if_neg (by omega), if_neg (by omega)]
              have heqa : (⟨if (σv i).val = 0 then r else r + (σv i).val + 2, by
                  have := (σv i).isLt; dsimp only [lenV, lenR] at this; split_ifs; omega⟩ : Fin (Fintype.card V)) = i' :=
                Fin.ext (by dsimp only; rw [if_pos hvi])
              have heqb : (⟨if (σv ⟨k.val - r - 2, by rw [Fintype.card_fin]; omega⟩).val = 0 then r
                  else r + (σv ⟨k.val - r - 2, by rw [Fintype.card_fin]; omega⟩).val + 2, by
                  have := (σv ⟨k.val - r - 2, by rw [Fintype.card_fin]; omega⟩).isLt; dsimp only [lenV, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) = k :=
                Fin.ext (by dsimp only; rw [if_neg (by omega), hvk]; omega)
              rw [heqa, heqb]; exact hkb.2.2
            · intro a ha b hb h
              have ha4 := (Finset.mem_filter.mp ha).2
              have hb4 := (Finset.mem_filter.mp hb).2
              have hv := congrArg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
            · intro k hk
              have hne1 : k.val ≠ 1 := fun h => (Finset.mem_erase.mp hk).1 (Fin.ext h)
              have hkb := (Finset.mem_filter.mp (Finset.mem_erase.mp hk).2).2
              have hkgt : i.val < k.val := hkb.1
              have hkle : k.val ≤ j.val := hkb.2.1
              have hkge2 : 2 ≤ k.val := by omega
              refine ⟨⟨r + k.val + 2, by dsimp only [lenV, lenR] at hj_lt; omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
              refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                by change r < r + k.val + 2; omega, by change r + k.val + 2 ≤ r + j.val + 2; omega, ?_⟩,
                by dsimp only; omega⟩
              have hadj := hkb.2.2
              have hvi : (σv i).val = 0 := by simpa [σv] using hi0
              have hvk : (σv k).val = k.val := by simp [σv]
              dsimp only [Gv] at hadj
              rw [if_neg (by omega), if_neg (by omega)] at hadj
              have heqa : (⟨if (σv i).val = 0 then r else r + (σv i).val + 2, by
                  have := (σv i).isLt; dsimp only [lenV, lenR] at this; split_ifs; omega⟩ : Fin (Fintype.card V)) = i' :=
                Fin.ext (by dsimp only; rw [if_pos hvi])
              have heqb : (⟨if (σv k).val = 0 then r else r + (σv k).val + 2, by
                  have := (σv k).isLt; dsimp only [lenV, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) =
                  ⟨r + k.val + 2, by dsimp only [lenV, lenR] at hj_lt; omega⟩ :=
                Fin.ext (by dsimp only; rw [if_neg (by omega), hvk])
              rw [heqa, heqb] at hadj; exact hadj
          have hSv_card : Sv.card = Stail.card + 1 := by
            rw [hStail_eq, Finset.card_erase_of_mem h1mem]
            have := Finset.one_le_card.mpr ⟨_, h1mem⟩; omega
          change j.val - i.val ≤ 2 * Sv.card
          dsimp only [Sbig] at hSsplit; omega
      · -- 2 <= i < j: pure shift of [r + i + 2, r + j + 2]
        have hi2 : 2 ≤ i.val := by omega
        let i' : Fin (Fintype.card V) := ⟨r + i.val + 2, by dsimp only [lenV, lenR] at hj_lt; omega⟩
        let j' : Fin (Fintype.card V) := ⟨r + j.val + 2, by dsimp only [lenV, lenR] at hj_lt; omega⟩
        have h0 := hR i' j' (by change r + i.val + 2 < r + j.val + 2; omega)
        have hdiff : j'.val - i'.val = j.val - i.val := by dsimp only [i', j']; omega
        have hcard : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
            i' < k ∧ k ≤ j' ∧ G.Adj (σ i') (σ k))).card =
          (Finset.univ.filter (fun k : Fin (Fintype.card (Fin lenV)) =>
            i < k ∧ k ≤ j ∧ Gv.Adj (σv i) (σv k))).card := by
          refine Finset.card_bij (fun k hk => ⟨k.val - r - 2, by
            have h2 := (Finset.mem_filter.mp hk).2.2.1
            rw [Fintype.card_fin]; change k.val ≤ r + j.val + 2 at h2; omega⟩) ?_ ?_ ?_
          · intro k hk
            have hkb := (Finset.mem_filter.mp hk).2
            have h1 : r + i.val + 2 < k.val := hkb.1
            have h2 : k.val ≤ r + j.val + 2 := hkb.2.1
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨by change i.val < k.val - r - 2; omega, by change k.val - r - 2 ≤ j.val; omega, ?_⟩
            have hvi : (σv i).val = i.val := by simp [σv]
            have hvk : (σv ⟨k.val - r - 2, by rw [Fintype.card_fin]; omega⟩).val = k.val - r - 2 := by simp [σv]
            dsimp only [Gv]; rw [if_neg (by omega), if_neg (by omega)]
            have heqa : (⟨if (σv i).val = 0 then r else r + (σv i).val + 2, by
                have := (σv i).isLt; dsimp only [lenV, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) = i' :=
              Fin.ext (by dsimp only; rw [if_neg (by omega), hvi])
            have heqb : (⟨if (σv ⟨k.val - r - 2, by rw [Fintype.card_fin]; omega⟩).val = 0 then r
                else r + (σv ⟨k.val - r - 2, by rw [Fintype.card_fin]; omega⟩).val + 2, by
                have := (σv ⟨k.val - r - 2, by rw [Fintype.card_fin]; omega⟩).isLt; dsimp only [lenV, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) = k :=
              Fin.ext (by dsimp only; rw [if_neg (by omega), hvk]; omega)
            rw [heqa, heqb]; exact hkb.2.2
          · intro a ha b hb h
            have h1 : r + i.val + 2 < a.val := (Finset.mem_filter.mp ha).2.1
            have h2 : r + i.val + 2 < b.val := (Finset.mem_filter.mp hb).2.1
            have hv := congrArg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
          · intro k hk
            have hkb := (Finset.mem_filter.mp hk).2
            have h1 : i.val < k.val := hkb.1
            have h2 : k.val ≤ j.val := hkb.2.1
            refine ⟨⟨r + k.val + 2, by dsimp only [lenV, lenR] at hj_lt; omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨by change r + i.val + 2 < r + k.val + 2; omega,
              by change r + k.val + 2 ≤ r + j.val + 2; omega, ?_⟩
            have hadj := hkb.2.2
            have hvi : (σv i).val = i.val := by simp [σv]
            have hvk : (σv k).val = k.val := by simp [σv]
            dsimp only [Gv] at hadj
            rw [if_neg (by omega), if_neg (by omega)] at hadj
            have heqa : (⟨if (σv i).val = 0 then r else r + (σv i).val + 2, by
                have := (σv i).isLt; dsimp only [lenV, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) = i' :=
              Fin.ext (by dsimp only; rw [if_neg (by omega), hvi])
            have heqb : (⟨if (σv k).val = 0 then r else r + (σv k).val + 2, by
                have := (σv k).isLt; dsimp only [lenV, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) =
                ⟨r + k.val + 2, by dsimp only [lenV, lenR] at hj_lt; omega⟩ :=
              Fin.ext (by dsimp only; rw [if_neg (by omega), hvk])
            rw [heqa, heqb] at hadj; exact hadj
        rw [hdiff, hcard] at h0; exact h0
  -- Subforest Fv on (H.erase (u 2)) ∪ A with 3 roots (u 0, u 1, u 3)
  let H3 : Finset W := {u ⟨0, by decide⟩, u ⟨1, by decide⟩, u ⟨3, by decide⟩}
  have hH3_card : H3.card = 3 := by
    have h01' : u ⟨0, by decide⟩ ≠ u ⟨1, by decide⟩ := fun h => by have := hu_inj h; simp at this
    have h03' : u ⟨0, by decide⟩ ≠ u ⟨3, by decide⟩ := fun h => by have := hu_inj h; simp at this
    have h13' : u ⟨1, by decide⟩ ≠ u ⟨3, by decide⟩ := fun h => by have := hu_inj h; simp at this
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h01', h03'⟩),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact h13'), Finset.card_singleton]
  have hH3A_disj : Disjoint H3 A := Finset.disjoint_left.mpr (fun x hx hxA => by
    simp only [H3, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact hHA_disj _ hxA)
  have hH3_sub : H3 ⊆ H := fun x hx => by
    simp only [H3, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact hu_memH _
  let Fv : Digraph ↥(H3 ∪ A) := ⟨fun x y => y.1 ∈ A ∧ D.Adj x.1 y.1⟩
  have hFv_rank : ∃ rk : ↥(H3 ∪ A) → ℕ, ∀ x y, Fv.Adj x y → rk x < rk y := by
    obtain ⟨rkP, hrkP⟩ := hRkP
    refine ⟨fun x => rkP ⟨x.1, Finset.union_subset_union_left hH3_sub x.2⟩, fun x y hxy => hrkP _ _ hxy.1 hxy.2⟩
  have hFv_in : ∀ w u1 u2 : ↥(H3 ∪ A), Fv.Adj u1 w → Fv.Adj u2 w → u1 = u2 := by
    intro w a1 a2 h1 h2
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hA_in w.1 h1.1)
    have e1 : a1.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.2⟩)
    have e2 : a2.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.2⟩)
    exact Subtype.ext (e1.trans e2.symm)
  let r0 : ↥(H3 ∪ A) := ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (by simp [H3])⟩
  let r1 : ↥(H3 ∪ A) := ⟨u ⟨1, by decide⟩, Finset.mem_union_left _ (by simp [H3])⟩
  let r3 : ↥(H3 ∪ A) := ⟨u ⟨3, by decide⟩, Finset.mem_union_left _ (by simp [H3])⟩
  let roots : Fin 3 → ↥(H3 ∪ A) := fun j =>
    match j.val with | 0 => r0 | 1 => r1 | _ => r3
  have hroots_inj : Function.Injective roots := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals
      dsimp only [roots, r0, r1, r3] at h
      have := hu_inj (congrArg Subtype.val h); simp at this
  have hroots_iff : ∀ w : ↥(H3 ∪ A), (∀ z, ¬ Fv.Adj z w) ↔ ∃ j : Fin 3, roots j = w := by
    intro w
    constructor
    · intro hno
      by_cases hwA : w.1 ∈ A
      · exfalso
        have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj z w.1)).card := by rw [hA_in w.1 hwA]; omega
        obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
        have hDzw := (Finset.mem_filter.mp hz).2
        have hzH3A : z ∈ H3 ∪ A := by
          by_cases hzA : z ∈ A
          · exact Finset.mem_union_right _ hzA
          · by_cases hzH : z ∈ H
            · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzH
              fin_cases i
              · exact Finset.mem_union_left _ (by simp [H3])
              · exact Finset.mem_union_left _ (by simp [H3])
              · exact absurd hDzw (hno2A w.1 hwA)
              · exact Finset.mem_union_left _ (by simp [H3])
            · exact absurd hDzw (hno_AB w.1 hwA z (fun i hi => hzH (hi ▸ hu_memH i)) hzA).2
        exact hno ⟨z, hzH3A⟩ ⟨hwA, hDzw⟩
      · have hwH3 : w.1 ∈ H3 := (Finset.mem_union.mp w.2).resolve_right hwA
        simp only [H3, Finset.mem_insert, Finset.mem_singleton] at hwH3
        rcases hwH3 with h | h | h
        · exact ⟨⟨0, by decide⟩, Subtype.ext (by dsimp only [roots, r0]; exact h.symm)⟩
        · exact ⟨⟨1, by decide⟩, Subtype.ext (by dsimp only [roots, r1]; exact h.symm)⟩
        · exact ⟨⟨2, by decide⟩, Subtype.ext (by dsimp only [roots, r3]; exact h.symm)⟩
    · rintro ⟨j, rfl⟩ z hFv
      fin_cases j <;> dsimp only [roots, r0, r1, r3] at hFv <;> exact hHA_disj _ hFv.1
  -- Pick q = 2 if u 0 has no A-child, else q = 0!
  let q : ℕ := if ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x then 2 else 0
  have hpref : ∀ j : Fin 3, j.val < q → ∀ z, ¬ Fv.Adj (roots j) z := by
    intro j hjq z hFv
    by_cases h0no : ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x
    · fin_cases j
      · exact h0no z.1 hFv.1 hFv.2
      · exact hno1A z.1 hFv.1 hFv.2
      · dsimp only [q] at hjq; rw [if_pos h0no] at hjq; omega
    · dsimp only [q] at hjq; rw [if_neg h0no] at hjq; omega
  have hcardW : Fintype.card ↥(H3 ∪ A) = 3 + A.card := by
    rw [Fintype.card_coe, Finset.card_union_of_disjoint hH3A_disj, hH3_card]
  have hleaves_le : (Finset.univ.filter (fun w : ↥(H3 ∪ A) => ∀ z, ¬ Fv.Adj w z)).card ≤
      (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card + 2 + (if ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x then 1 else 0) := by
    let LF := Finset.univ.filter (fun w : ↥(H3 ∪ A) => ∀ z, ¬ Fv.Adj w z)
    let SA := LF.filter (fun w => w.1 ∈ A)
    let SH := LF.filter (fun w => w.1 ∉ A)
    have hsplit : LF.card = SA.card + SH.card := (card_filter_add_card_filter_not_eq LF _).symm
    have hSA : SA.card ≤ (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card := by
      have himg : SA.image Subtype.val ⊆ A.filter (fun x => ∀ z : W, ¬ D.Adj x z) := by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
        have hwA := (Finset.mem_filter.mp hw).2
        have hno := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
        refine Finset.mem_filter.mpr ⟨hwA, fun z hDwz => ?_⟩
        by_cases hzA : z ∈ A
        · exact hno ⟨z, Finset.mem_union_right _ hzA⟩ ⟨hzA, hDwz⟩
        · by_cases hzH : z ∈ H
          · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzH; exact hno_AH w.1 hwA i hDwz
          · exact (hno_AB w.1 hwA z (fun i hi => hzH (hi ▸ hu_memH i)) hzA).1 hDwz
      rw [← Finset.card_image_of_injective SA Subtype.val_injective]
      exact Finset.card_le_card himg
    have hSH : SH.card ≤ 2 + (if ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x then 1 else 0) := by
      by_cases h0no : ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x
      · rw [if_pos h0no]
        have hsub : SH.image Subtype.val ⊆ H3 := fun x hx => by
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
          exact (Finset.mem_union.mp w.2).resolve_right (Finset.mem_filter.mp hw).2
        rw [← Finset.card_image_of_injective SH Subtype.val_injective]
        exact (Finset.card_le_card hsub).trans (by omega)
      · rw [if_neg h0no]
        push Not at h0no
        obtain ⟨c0, hc0A, hD0c⟩ := h0no
        have hsub : SH.image Subtype.val ⊆ {u ⟨1, by decide⟩, u ⟨3, by decide⟩} := by
          intro x hx
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
          have hwH3 : w.1 ∈ H3 := (Finset.mem_union.mp w.2).resolve_right (Finset.mem_filter.mp hw).2
          have hno := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
          simp only [H3, Finset.mem_insert, Finset.mem_singleton] at hwH3 ⊢
          rcases hwH3 with h0' | h1' | h3'
          · exfalso; exact hno ⟨c0, Finset.mem_union_right _ hc0A⟩ ⟨hc0A, h0' ▸ hD0c⟩
          · exact Or.inl h1'
          · exact Or.inr h3'
        rw [← Finset.card_image_of_injective SH Subtype.val_injective]
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
    dsimp only [LF] at hsplit; omega
  obtain ⟨fv, hfv_inj, hfv_roots⟩ := greedy_out_branching_embeds Fv hFv_rank hFv_in Gv hRv
    roots hroots_inj hroots_iff (by rw [Fintype.card_fin]; omega) q (by dsimp only [q]; split_ifs <;> omega)
    hpref (by rw [hcardW, Fintype.card_fin]; dsimp only [q, lenV, lenR] at *; split_ifs at hleaves_le ⊢ <;> omega)
  have hfv_r0 : (fv r0).val = 0 := by
    have := congrArg Fin.val (hfv_roots ⟨0, by decide⟩); simpa [roots, σv] using this
  have hfv_r1 : (fv r1).val = 1 := by
    have := congrArg Fin.val (hfv_roots ⟨1, by decide⟩); simpa [roots, σv] using this
  have hfv_r3 : (fv r3).val = 2 := by
    have := congrArg Fin.val (hfv_roots ⟨2, by decide⟩); simpa [roots, σv] using this
  have hfv_A_ge3 : ∀ x : ↥(H3 ∪ A), x.1 ∈ A → 3 ≤ (fv x).val := by
    intro x hxA
    have h0 : (fv x).val ≠ 0 := fun h => hHA_disj ⟨0, by decide⟩
      ((congrArg Subtype.val (hfv_inj (Fin.ext (h.trans hfv_r0.symm)))) ▸ hxA)
    have h1 : (fv x).val ≠ 1 := fun h => hHA_disj ⟨1, by decide⟩
      ((congrArg Subtype.val (hfv_inj (Fin.ext (h.trans hfv_r1.symm)))) ▸ hxA)
    have h2 : (fv x).val ≠ 2 := fun h => hHA_disj ⟨3, by decide⟩
      ((congrArg Subtype.val (hfv_inj (Fin.ext (h.trans hfv_r3.symm)))) ▸ hxA)
    omega
  -- Translate fv to real Fin (Fintype.card V) indices!
  let gR : ↥(H ∪ A) → Fin (Fintype.card V) := fun w =>
    if hw2 : w.1 = u ⟨2, by decide⟩ then ⟨r + p2, by omega⟩
    else
      have hwH3A : w.1 ∈ H3 ∪ A := by
        rcases Finset.mem_union.mp w.2 with hwH | hwA
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hwH
          fin_cases i
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
          · exact absurd hi.symm hw2
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
        · exact Finset.mem_union_right _ hwA
      let k := (fv ⟨w.1, hwH3A⟩).val
      if k = 0 then ⟨r, by omega⟩
      else if k = 1 then ⟨r + 1, by omega⟩
      else ⟨r + k + 2, by have := (fv ⟨w.1, hwH3A⟩).isLt; dsimp only [lenV, lenR] at this; omega⟩
  have hgR_u0 : gR ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ = ⟨r, by omega⟩ := by
    have hne : u ⟨0, by decide⟩ ≠ u ⟨2, by decide⟩ := fun h => by have := hu_inj h; simp at this
    apply Fin.ext; dsimp only [gR]; rw [dif_neg hne]
    have hval : (fv r0).val = 0 := hfv_r0
    change (if (fv r0).val = 0 then (⟨r, _⟩ : Fin (Fintype.card V)) else _).val = r
    rw [if_pos hval]
  have hgR_u1 : gR ⟨u ⟨1, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ = ⟨r + 1, by omega⟩ := by
    have hne : u ⟨1, by decide⟩ ≠ u ⟨2, by decide⟩ := fun h => by have := hu_inj h; simp at this
    apply Fin.ext; dsimp only [gR]; rw [dif_neg hne]
    have hval : (fv r1).val = 1 := hfv_r1
    change (if (fv r1).val = 0 then (⟨r, _⟩ : Fin (Fintype.card V))
      else if (fv r1).val = 1 then ⟨r + 1, _⟩ else _).val = r + 1
    rw [if_neg (by omega), if_pos hval]
  have hgR_u2 : gR ⟨u ⟨2, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ = ⟨r + p2, by omega⟩ := by
    dsimp only [gR]; rw [dif_pos rfl]
  have hgR_u3 : gR ⟨u ⟨3, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ = ⟨r + 4, by omega⟩ := by
    have hne : u ⟨3, by decide⟩ ≠ u ⟨2, by decide⟩ := fun h => by have := hu_inj h; simp at this
    apply Fin.ext; dsimp only [gR]; rw [dif_neg hne]
    have hval : (fv r3).val = 2 := hfv_r3
    change (if (fv r3).val = 0 then (⟨r, _⟩ : Fin (Fintype.card V))
      else if (fv r3).val = 1 then ⟨r + 1, _⟩ else ⟨r + (fv r3).val + 2, _⟩).val = r + 4
    rw [if_neg (by omega), if_neg (by omega)]; dsimp only; omega
  have hgR_A_eq : ∀ (x : ↥(H ∪ A)) (hxA : x.1 ∈ A),
      gR x = ⟨r + (fv ⟨x.1, Finset.mem_union_right _ hxA⟩).val + 2, by
        have := (fv ⟨x.1, Finset.mem_union_right _ hxA⟩).isLt; dsimp only [lenV, lenR] at this; omega⟩ := by
    intro x hxA
    have hne : x.1 ≠ u ⟨2, by decide⟩ := fun h => hHA_disj ⟨2, by decide⟩ (h ▸ hxA)
    have hge3 := hfv_A_ge3 ⟨x.1, Finset.mem_union_right _ hxA⟩ hxA
    apply Fin.ext; dsimp only [gR]; rw [dif_neg hne]
    rw [if_neg (by omega), if_neg (by omega)]
  have hgR_A_gt : ∀ x : ↥(H ∪ A), x.1 ∈ A → r + 4 < (gR x).val := by
    intro x hxA
    rw [hgR_A_eq x hxA]
    have hge3 := hfv_A_ge3 ⟨x.1, Finset.mem_union_right _ hxA⟩ hxA
    dsimp only; omega
  have hgR_val_u : ∀ (w : ↥(H ∪ A)) (i : Fin 4), w.1 = u i →
      (gR w).val = match i.val with | 0 => r | 1 => r + 1 | 2 => r + p2 | _ => r + 4 := by
    intro w i hw
    fin_cases i
    · rw [show w = ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hw, hgR_u0]; rfl
    · rw [show w = ⟨u ⟨1, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hw, hgR_u1]; rfl
    · rw [show w = ⟨u ⟨2, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hw, hgR_u2]; rfl
    · rw [show w = ⟨u ⟨3, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hw, hgR_u3]; rfl
  have hgR_inj : Function.Injective gR := by
    have hp2_bnd : 2 ≤ p2 ∧ p2 ≤ 3 := by rcases hp2 with rfl | rfl <;> omega
    intro x y hxy
    have hval := congrArg Fin.val hxy
    by_cases hx2 : x.1 = u ⟨2, by decide⟩ <;> by_cases hy2 : y.1 = u ⟨2, by decide⟩
    · exact Subtype.ext (hx2.trans hy2.symm)
    · exfalso
      have hxv := hgR_val_u x ⟨2, by decide⟩ hx2
      simp only at hxv
      by_cases hyA : y.1 ∈ A
      · have := hgR_A_gt y hyA; omega
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((Finset.mem_union.mp y.2).resolve_right hyA)
        have hyv := hgR_val_u y i hi.symm
        fin_cases i <;> (simp only at hyv; first | exact hy2 hi.symm | omega)
    · exfalso
      have hyv := hgR_val_u y ⟨2, by decide⟩ hy2
      simp only at hyv
      by_cases hxA : x.1 ∈ A
      · have := hgR_A_gt x hxA; omega
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((Finset.mem_union.mp x.2).resolve_right hxA)
        have hxv := hgR_val_u x i hi.symm
        fin_cases i <;> (simp only at hxv; first | exact hx2 hi.symm | omega)
    · have hxH3A : x.1 ∈ H3 ∪ A := by
        rcases Finset.mem_union.mp x.2 with h | h
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
          fin_cases i
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
          · exact absurd hi.symm hx2
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
        · exact Finset.mem_union_right _ h
      have hyH3A : y.1 ∈ H3 ∪ A := by
        rcases Finset.mem_union.mp y.2 with h | h
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
          fin_cases i
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
          · exact absurd hi.symm hy2
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
        · exact Finset.mem_union_right _ h
      dsimp only [gR] at hval
      rw [dif_neg hx2, dif_neg hy2] at hval
      have hfv_eq : (fv ⟨x.1, hxH3A⟩).val = (fv ⟨y.1, hyH3A⟩).val := by
        set kx := (fv ⟨x.1, hxH3A⟩).val; set ky := (fv ⟨y.1, hyH3A⟩).val
        split_ifs at hval <;> (simp only at hval; omega)
      exact Subtype.ext (congrArg (fun z : ↥(H3 ∪ A) => z.1) (hfv_inj (Fin.ext hfv_eq)))
  have hgR_adj : ∀ x y : ↥(H ∪ A), D.Adj x.1 y.1 → G.Adj (σ (gR x)) (σ (gR y)) := by
    intro x y hDxy
    by_cases hyA : y.1 ∈ A
    · have hxne2 : x.1 ≠ u ⟨2, by decide⟩ := fun h => hno2A y.1 hyA (h ▸ hDxy)
      have hxne1 : x.1 ≠ u ⟨1, by decide⟩ := fun h => hno1A y.1 hyA (h ▸ hDxy)
      have hxH3A : x.1 ∈ H3 ∪ A := by
        rcases Finset.mem_union.mp x.2 with h | h
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
          fin_cases i
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
          · exact absurd hi.symm hxne1
          · exact absurd hi.symm hxne2
          · exact Finset.mem_union_left _ (by simp [H3, ← hi])
        · exact Finset.mem_union_right _ h
      have hfv_adj : Gv.Adj (fv ⟨x.1, hxH3A⟩) (fv ⟨y.1, Finset.mem_union_right _ hyA⟩) :=
        fv.map_adj' (show Fv.Adj ⟨x.1, hxH3A⟩ ⟨y.1, Finset.mem_union_right _ hyA⟩ from ⟨hyA, hDxy⟩)
      have hfx_ne1 : (fv ⟨x.1, hxH3A⟩).val ≠ 1 := fun h =>
        hxne1 (congrArg (fun z : ↥(H3 ∪ A) => z.1) (hfv_inj (Fin.ext (h.trans hfv_r1.symm))))
      have hfy_ge3 := hfv_A_ge3 ⟨y.1, Finset.mem_union_right _ hyA⟩ hyA
      dsimp only [Gv] at hfv_adj
      rw [if_neg hfx_ne1, if_neg (by omega)] at hfv_adj
      have hgx_eq : gR x = ⟨if (fv ⟨x.1, hxH3A⟩).val = 0 then r else r + (fv ⟨x.1, hxH3A⟩).val + 2, by
          have := (fv ⟨x.1, hxH3A⟩).isLt; dsimp only [lenV, lenR] at this; split_ifs <;> omega⟩ := by
        apply Fin.ext; dsimp only [gR]; rw [dif_neg hxne2]
        by_cases h0 : (fv ⟨x.1, hxH3A⟩).val = 0
        · rw [if_pos h0, if_pos h0]
        · rw [if_neg h0, if_neg hfx_ne1, if_neg h0]
      have hgy_eq : gR y = ⟨if (fv ⟨y.1, Finset.mem_union_right _ hyA⟩).val = 0 then r
          else r + (fv ⟨y.1, Finset.mem_union_right _ hyA⟩).val + 2, by
          have := (fv ⟨y.1, Finset.mem_union_right _ hyA⟩).isLt; dsimp only [lenV, lenR] at this; split_ifs <;> omega⟩ := by
        rw [hgR_A_eq y hyA]; apply Fin.ext; dsimp only; rw [if_neg (by omega)]
      rw [hgx_eq, hgy_eq]; exact hfv_adj
    · have hyH : y.1 ∈ H := (Finset.mem_union.mp y.2).resolve_right hyA
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hyH
      have hxH : x.1 ∈ H := by
        rcases Finset.mem_union.mp x.2 with h | hxA
        · exact h
        · exact absurd (hj.symm ▸ hDxy) (hno_AH x.1 hxA j)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hxH
      have ⟨hi0, hj0⟩ := hH_only i j (hi ▸ hj ▸ hDxy)
      subst hi0
      rw [show x = ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hi.symm, hgR_u0]
      fin_cases j
      · exact absurd rfl hj0
      · rw [show y = ⟨u ⟨1, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hj.symm, hgR_u1]; exact hG01
      · rw [show y = ⟨u ⟨2, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hj.symm, hgR_u2]; exact hG0p2
      · rw [show y = ⟨u ⟨3, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hj.symm, hgR_u3]; exact hG04
  exact ⟨gR, hgR_inj, hgR_u0, hgR_u1, hgR_u2, hgR_u3, hgR_A_gt, hgR_adj⟩

lemma s4ppp_right_p3_eq_5
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno1A : ∀ x ∈ A, ¬ D.Adj (u ⟨1, by decide⟩) x)
    (hno2A : ∀ x ∈ A, ¬ D.Adj (u ⟨2, by decide⟩) x)
    (hRkP : ∃ rkP : ↥(Finset.univ.image u ∪ A) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (r p2 : ℕ) (hp2 : p2 = 2 ∨ p2 = 3) (hr6 : r + 6 ≤ 2 * n - 2)
    (hG01 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1, by omega⟩))
    (hG0p2 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + p2, by omega⟩))
    (hG05 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 5, by omega⟩))
    (hG0notA : ¬ G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + (5 - p2), by omega⟩))
    (hG0not4 : ¬ G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 4, by omega⟩))
    (hLen : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r) :
    ∃ gR : ↥(Finset.univ.image u ∪ A) → Fin (Fintype.card V),
      Function.Injective gR ∧
      gR ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩ = ⟨r, by omega⟩ ∧
      gR ⟨u ⟨1, by decide⟩, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩ = ⟨r + 1, by omega⟩ ∧
      gR ⟨u ⟨2, by decide⟩, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩ = ⟨r + p2, by omega⟩ ∧
      gR ⟨u ⟨3, by decide⟩, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩ = ⟨r + 5, by omega⟩ ∧
      (∀ x : ↥(Finset.univ.image u ∪ A), x.1 ∈ A → r + 5 < (gR x).val) ∧
      (∀ x y : ↥(Finset.univ.image u ∪ A), D.Adj x.1 y.1 → G.Adj (σ (gR x)) (σ (gR y))) := by
  classical
  let H : Finset W := Finset.univ.image u
  have hu_memH : ∀ i : Fin 4, u i ∈ H := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let lenR : ℕ := 2 * n - 2 - r
  let lenS : ℕ := lenR - 4
  have hlenS_ge2 : 2 ≤ lenS := by omega
  -- Subdigraph Gs on Fin lenS: 0 -> r, k >= 1 -> r + k + 4
  let Gs : Digraph (Fin lenS) := ⟨fun a b =>
    let ia : ℕ := if a.val = 0 then r else r + a.val + 4
    let ib : ℕ := if b.val = 0 then r else r + b.val + 4
    G.Adj (σ ⟨ia, by have := a.isLt; dsimp only [ia, lenS, lenR]; split_ifs <;> omega⟩)
      (σ ⟨ib, by have := b.isLt; dsimp only [ib, lenS, lenR]; split_ifs <;> omega⟩)⟩
  let σs : Fin (Fintype.card (Fin lenS)) ≃ Fin lenS := finCongr (Fintype.card_fin lenS)
  have hRs : ∀ i j : Fin (Fintype.card (Fin lenS)), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card (Fin lenS)) =>
        i < k ∧ k ≤ j ∧ Gs.Adj (σs i) (σs k))).card := by
    intro i j hij
    have hij_v : i.val < j.val := hij
    have hj_lt : j.val < lenS := by simpa using j.isLt
    by_cases hi0 : i.val = 0
    · let i' : Fin (Fintype.card V) := ⟨r, by omega⟩
      let j' : Fin (Fintype.card V) := ⟨r + j.val + 4, by dsimp only [lenS, lenR] at hj_lt; omega⟩
      have h0 := hR i' j' (by change r < r + j.val + 4; omega)
      have hdiff : j'.val - i'.val = j.val + 4 := by dsimp only [i', j']; omega
      rw [hdiff] at h0
      let Sbig := Finset.univ.filter (fun k : Fin (Fintype.card V) => i' < k ∧ k ≤ j' ∧ G.Adj (σ i') (σ k))
      let Shead := Sbig.filter (fun k => k.val < r + 5)
      let Stail := Sbig.filter (fun k => r + 5 ≤ k.val)
      have hSsplit : Sbig.card = Shead.card + Stail.card := by
        have := card_filter_add_card_filter_not_eq Sbig (fun k => k.val < r + 5)
        have heq : Sbig.filter (fun k => ¬ k.val < r + 5) = Stail := by
          ext k; simp only [Stail, Finset.mem_filter, not_lt]
        rw [heq] at this; exact this.symm
      have hShead_le : Shead.card ≤ 2 := by
        have hsub : Shead ⊆ {⟨r + 1, by omega⟩, ⟨r + p2, by omega⟩} := by
          intro k hk
          have hk1 := (Finset.mem_filter.mp hk).1
          have hklt : k.val < r + 5 := (Finset.mem_filter.mp hk).2
          have hkb := (Finset.mem_filter.mp hk1).2
          have hkr : r < k.val := hkb.1
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases hkv1 : k.val = r + 1
          · exact Or.inl (Fin.ext hkv1)
          · by_cases hkvp : k.val = r + p2
            · exact Or.inr (Fin.ext hkvp)
            · exfalso
              by_cases hkv4 : k.val = r + 4
              · have hk_eq : k = ⟨r + 4, by omega⟩ := Fin.ext hkv4
                rw [hk_eq] at hkb; exact hG0not4 hkb.2.2
              · have hk_eq : k = ⟨r + (5 - p2), by omega⟩ := Fin.ext (by dsimp only; omega)
                rw [hk_eq] at hkb; exact hG0notA hkb.2.2
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
      have hStail_eq : Stail.card = (Finset.univ.filter (fun k : Fin (Fintype.card (Fin lenS)) =>
          i < k ∧ k ≤ j ∧ Gs.Adj (σs i) (σs k))).card := by
        refine Finset.card_bij (fun k hk => ⟨k.val - r - 4, by
          have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2.2.1
          rw [Fintype.card_fin]; change k.val ≤ r + j.val + 4 at h2; omega⟩) ?_ ?_ ?_
        · intro k hk
          have hkb := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
          have hkge : r + 5 ≤ k.val := (Finset.mem_filter.mp hk).2
          have hkle : k.val ≤ r + j.val + 4 := hkb.2.1
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨by change i.val < k.val - r - 4; omega, by change k.val - r - 4 ≤ j.val; omega, ?_⟩
          have hvi : (σs i).val = 0 := by simpa [σs] using hi0
          have hvk : (σs ⟨k.val - r - 4, by rw [Fintype.card_fin]; omega⟩).val = k.val - r - 4 := by simp [σs]
          dsimp only [Gs]
          have heqa : (⟨if (σs i).val = 0 then r else r + (σs i).val + 4, by
              have := (σs i).isLt; dsimp only [lenS, lenR] at this; split_ifs; omega⟩ : Fin (Fintype.card V)) = i' :=
            Fin.ext (by dsimp only; rw [if_pos hvi])
          have heqb : (⟨if (σs ⟨k.val - r - 4, by rw [Fintype.card_fin]; omega⟩).val = 0 then r
              else r + (σs ⟨k.val - r - 4, by rw [Fintype.card_fin]; omega⟩).val + 4, by
              have := (σs ⟨k.val - r - 4, by rw [Fintype.card_fin]; omega⟩).isLt; dsimp only [lenS, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) = k :=
            Fin.ext (by dsimp only; rw [if_neg (by omega), hvk]; omega)
          rw [heqa, heqb]; exact hkb.2.2
        · intro a ha b hb h
          have ha5 := (Finset.mem_filter.mp ha).2
          have hb5 := (Finset.mem_filter.mp hb).2
          have hv := congrArg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
        · intro k hk
          have hkb := (Finset.mem_filter.mp hk).2
          have h1 : i.val < k.val := hkb.1
          have h2 : k.val ≤ j.val := hkb.2.1
          refine ⟨⟨r + k.val + 4, by dsimp only [lenS, lenR] at hj_lt; omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            by change r < r + k.val + 4; omega, by change r + k.val + 4 ≤ r + j.val + 4; omega, ?_⟩,
            by dsimp only; omega⟩
          have hadj := hkb.2.2
          have hvi : (σs i).val = 0 := by simpa [σs] using hi0
          have hvk : (σs k).val = k.val := by simp [σs]
          dsimp only [Gs] at hadj
          have heqa : (⟨if (σs i).val = 0 then r else r + (σs i).val + 4, by
              have := (σs i).isLt; dsimp only [lenS, lenR] at this; split_ifs; omega⟩ : Fin (Fintype.card V)) = i' :=
            Fin.ext (by dsimp only; rw [if_pos hvi])
          have heqb : (⟨if (σs k).val = 0 then r else r + (σs k).val + 4, by
              have := (σs k).isLt; dsimp only [lenS, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) =
              ⟨r + k.val + 4, by dsimp only [lenS, lenR] at hj_lt; omega⟩ :=
            Fin.ext (by dsimp only; rw [if_neg (by omega), hvk])
          rw [heqa, heqb] at hadj; exact hadj
      dsimp only [Sbig] at hSsplit; omega
    · let i' : Fin (Fintype.card V) := ⟨r + i.val + 4, by dsimp only [lenS, lenR] at hj_lt; omega⟩
      let j' : Fin (Fintype.card V) := ⟨r + j.val + 4, by dsimp only [lenS, lenR] at hj_lt; omega⟩
      have h0 := hR i' j' (by change r + i.val + 4 < r + j.val + 4; omega)
      have hdiff : j'.val - i'.val = j.val - i.val := by dsimp only [i', j']; omega
      have hcard : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          i' < k ∧ k ≤ j' ∧ G.Adj (σ i') (σ k))).card =
        (Finset.univ.filter (fun k : Fin (Fintype.card (Fin lenS)) =>
          i < k ∧ k ≤ j ∧ Gs.Adj (σs i) (σs k))).card := by
        refine Finset.card_bij (fun k hk => ⟨k.val - r - 4, by
          have h2 := (Finset.mem_filter.mp hk).2.2.1
          rw [Fintype.card_fin]; change k.val ≤ r + j.val + 4 at h2; omega⟩) ?_ ?_ ?_
        · intro k hk
          have hkb := (Finset.mem_filter.mp hk).2
          have h1 : r + i.val + 4 < k.val := hkb.1
          have h2 : k.val ≤ r + j.val + 4 := hkb.2.1
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨by change i.val < k.val - r - 4; omega, by change k.val - r - 4 ≤ j.val; omega, ?_⟩
          have hvi : (σs i).val = i.val := by simp [σs]
          have hvk : (σs ⟨k.val - r - 4, by rw [Fintype.card_fin]; omega⟩).val = k.val - r - 4 := by simp [σs]
          dsimp only [Gs]
          have heqa : (⟨if (σs i).val = 0 then r else r + (σs i).val + 4, by
              have := (σs i).isLt; dsimp only [lenS, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) = i' :=
            Fin.ext (by dsimp only; rw [if_neg (by omega), hvi])
          have heqb : (⟨if (σs ⟨k.val - r - 4, by rw [Fintype.card_fin]; omega⟩).val = 0 then r
              else r + (σs ⟨k.val - r - 4, by rw [Fintype.card_fin]; omega⟩).val + 4, by
              have := (σs ⟨k.val - r - 4, by rw [Fintype.card_fin]; omega⟩).isLt; dsimp only [lenS, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) = k :=
            Fin.ext (by dsimp only; rw [if_neg (by omega), hvk]; omega)
          rw [heqa, heqb]; exact hkb.2.2
        · intro a ha b hb h
          have h1 : r + i.val + 4 < a.val := (Finset.mem_filter.mp ha).2.1
          have h2 : r + i.val + 4 < b.val := (Finset.mem_filter.mp hb).2.1
          have hv := congrArg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
        · intro k hk
          have hkb := (Finset.mem_filter.mp hk).2
          have h1 : i.val < k.val := hkb.1
          have h2 : k.val ≤ j.val := hkb.2.1
          refine ⟨⟨r + k.val + 4, by dsimp only [lenS, lenR] at hj_lt; omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨by change r + i.val + 4 < r + k.val + 4; omega,
            by change r + k.val + 4 ≤ r + j.val + 4; omega, ?_⟩
          have hadj := hkb.2.2
          have hvi : (σs i).val = i.val := by simp [σs]
          have hvk : (σs k).val = k.val := by simp [σs]
          dsimp only [Gs] at hadj
          have heqa : (⟨if (σs i).val = 0 then r else r + (σs i).val + 4, by
              have := (σs i).isLt; dsimp only [lenS, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) = i' :=
            Fin.ext (by dsimp only; rw [if_neg (by omega), hvi])
          have heqb : (⟨if (σs k).val = 0 then r else r + (σs k).val + 4, by
              have := (σs k).isLt; dsimp only [lenS, lenR] at this; split_ifs <;> omega⟩ : Fin (Fintype.card V)) =
              ⟨r + k.val + 4, by dsimp only [lenS, lenR] at hj_lt; omega⟩ :=
            Fin.ext (by dsimp only; rw [if_neg (by omega), hvk])
          rw [heqa, heqb] at hadj; exact hadj
      rw [hdiff, hcard] at h0; exact h0
  -- Subforest Fs on {u 0, u 3} ∪ A with 2 roots (u 0, u 3)
  let H2 : Finset W := {u ⟨0, by decide⟩, u ⟨3, by decide⟩}
  have hH2_card : H2.card = 2 := by
    have h03' : u ⟨0, by decide⟩ ≠ u ⟨3, by decide⟩ := fun h => by have := hu_inj h; simp at this
    exact Finset.card_pair h03'
  have hH2A_disj : Disjoint H2 A := Finset.disjoint_left.mpr (fun x hx hxA => by
    simp only [H2, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact hHA_disj _ hxA)
  have hH2_sub : H2 ⊆ H := fun x hx => by
    simp only [H2, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact hu_memH _
  let Fs : Digraph ↥(H2 ∪ A) := ⟨fun x y => y.1 ∈ A ∧ D.Adj x.1 y.1⟩
  have hFs_rank : ∃ rk : ↥(H2 ∪ A) → ℕ, ∀ x y, Fs.Adj x y → rk x < rk y := by
    obtain ⟨rkP, hrkP⟩ := hRkP
    refine ⟨fun x => rkP ⟨x.1, Finset.union_subset_union_left hH2_sub x.2⟩, fun x y hxy => hrkP _ _ hxy.1 hxy.2⟩
  have hFs_in : ∀ w u1 u2 : ↥(H2 ∪ A), Fs.Adj u1 w → Fs.Adj u2 w → u1 = u2 := by
    intro w a1 a2 h1 h2
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hA_in w.1 h1.1)
    have e1 : a1.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.2⟩)
    have e2 : a2.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.2⟩)
    exact Subtype.ext (e1.trans e2.symm)
  let r0 : ↥(H2 ∪ A) := ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (by simp [H2])⟩
  let r3 : ↥(H2 ∪ A) := ⟨u ⟨3, by decide⟩, Finset.mem_union_left _ (by simp [H2])⟩
  let roots : Fin 2 → ↥(H2 ∪ A) := fun j => if j.val = 0 then r0 else r3
  have hroots_inj : Function.Injective roots := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals dsimp only [roots, r0, r3] at h; have := hu_inj (congrArg Subtype.val h); simp at this
  have hroots_iff : ∀ w : ↥(H2 ∪ A), (∀ z, ¬ Fs.Adj z w) ↔ ∃ j : Fin 2, roots j = w := by
    intro w
    constructor
    · intro hno
      by_cases hwA : w.1 ∈ A
      · exfalso
        have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj z w.1)).card := by rw [hA_in w.1 hwA]; omega
        obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
        have hDzw := (Finset.mem_filter.mp hz).2
        have hzH2A : z ∈ H2 ∪ A := by
          by_cases hzA : z ∈ A
          · exact Finset.mem_union_right _ hzA
          · by_cases hzH : z ∈ H
            · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzH
              fin_cases i
              · exact Finset.mem_union_left _ (by simp [H2])
              · exact absurd hDzw (hno1A w.1 hwA)
              · exact absurd hDzw (hno2A w.1 hwA)
              · exact Finset.mem_union_left _ (by simp [H2])
            · exact absurd hDzw (hno_AB w.1 hwA z (fun i hi => hzH (hi ▸ hu_memH i)) hzA).2
        exact hno ⟨z, hzH2A⟩ ⟨hwA, hDzw⟩
      · have hwH2 : w.1 ∈ H2 := (Finset.mem_union.mp w.2).resolve_right hwA
        simp only [H2, Finset.mem_insert, Finset.mem_singleton] at hwH2
        rcases hwH2 with h | h
        · exact ⟨⟨0, by decide⟩, Subtype.ext h.symm⟩
        · exact ⟨⟨1, by decide⟩, Subtype.ext h.symm⟩
    · rintro ⟨j, rfl⟩ z hFs
      fin_cases j <;> dsimp only [roots, r0, r3] at hFs <;> exact hHA_disj _ hFs.1
  let q : ℕ := if ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x then 1 else 0
  have hpref : ∀ j : Fin 2, j.val < q → ∀ z, ¬ Fs.Adj (roots j) z := by
    intro j hjq z hFs
    by_cases h0no : ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x
    · fin_cases j
      · exact h0no z.1 hFs.1 hFs.2
      · dsimp only [q] at hjq; rw [if_pos h0no] at hjq; omega
    · dsimp only [q] at hjq; rw [if_neg h0no] at hjq; omega
  have hcardW : Fintype.card ↥(H2 ∪ A) = 2 + A.card := by
    rw [Fintype.card_coe, Finset.card_union_of_disjoint hH2A_disj, hH2_card]
  have hleaves_le : (Finset.univ.filter (fun w : ↥(H2 ∪ A) => ∀ z, ¬ Fs.Adj w z)).card ≤
      (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card + 1 + (if ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x then 1 else 0) := by
    let LF := Finset.univ.filter (fun w : ↥(H2 ∪ A) => ∀ z, ¬ Fs.Adj w z)
    let SA := LF.filter (fun w => w.1 ∈ A)
    let SH := LF.filter (fun w => w.1 ∉ A)
    have hsplit : LF.card = SA.card + SH.card := (card_filter_add_card_filter_not_eq LF _).symm
    have hSA : SA.card ≤ (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card := by
      have himg : SA.image Subtype.val ⊆ A.filter (fun x => ∀ z : W, ¬ D.Adj x z) := by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
        have hwA := (Finset.mem_filter.mp hw).2
        have hno := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
        refine Finset.mem_filter.mpr ⟨hwA, fun z hDwz => ?_⟩
        by_cases hzA : z ∈ A
        · exact hno ⟨z, Finset.mem_union_right _ hzA⟩ ⟨hzA, hDwz⟩
        · by_cases hzH : z ∈ H
          · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzH; exact hno_AH w.1 hwA i hDwz
          · exact (hno_AB w.1 hwA z (fun i hi => hzH (hi ▸ hu_memH i)) hzA).1 hDwz
      rw [← Finset.card_image_of_injective SA Subtype.val_injective]
      exact Finset.card_le_card himg
    have hSH : SH.card ≤ 1 + (if ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x then 1 else 0) := by
      by_cases h0no : ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x
      · rw [if_pos h0no]
        have hsub : SH.image Subtype.val ⊆ H2 := fun x hx => by
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
          exact (Finset.mem_union.mp w.2).resolve_right (Finset.mem_filter.mp hw).2
        rw [← Finset.card_image_of_injective SH Subtype.val_injective]
        exact (Finset.card_le_card hsub).trans (by omega)
      · rw [if_neg h0no]; push Not at h0no; obtain ⟨c0, hc0A, hD0c⟩ := h0no
        have hsub : SH.image Subtype.val ⊆ {u ⟨3, by decide⟩} := by
          intro x hx
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
          have hwH2 : w.1 ∈ H2 := (Finset.mem_union.mp w.2).resolve_right (Finset.mem_filter.mp hw).2
          have hno := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
          simp only [H2, Finset.mem_insert, Finset.mem_singleton] at hwH2 ⊢
          rcases hwH2 with h0' | h3'
          · exfalso; exact hno ⟨c0, Finset.mem_union_right _ hc0A⟩ ⟨hc0A, h0' ▸ hD0c⟩
          · exact h3'
        rw [← Finset.card_image_of_injective SH Subtype.val_injective]
        exact (Finset.card_le_card hsub).trans (by simp)
    dsimp only [LF] at hsplit; omega
  obtain ⟨fs, hfs_inj, hfs_roots⟩ := greedy_out_branching_embeds Fs hFs_rank hFs_in Gs hRs
    roots hroots_inj hroots_iff (by rw [Fintype.card_fin]; omega) q (by dsimp only [q]; split_ifs <;> omega)
    hpref (by rw [hcardW, Fintype.card_fin]; dsimp only [q, lenS, lenR] at *; split_ifs at hleaves_le ⊢ <;> omega)
  have hfs_r0 : (fs r0).val = 0 := by
    have := congrArg Fin.val (hfs_roots ⟨0, by decide⟩); simpa [roots, σs] using this
  have hfs_r3 : (fs r3).val = 1 := by
    have := congrArg Fin.val (hfs_roots ⟨1, by decide⟩); simpa [roots, σs] using this
  have hfs_A_ge2 : ∀ x : ↥(H2 ∪ A), x.1 ∈ A → 2 ≤ (fs x).val := by
    intro x hxA
    have h0 : (fs x).val ≠ 0 := fun h => hHA_disj ⟨0, by decide⟩
      ((congrArg Subtype.val (hfs_inj (Fin.ext (h.trans hfs_r0.symm)))) ▸ hxA)
    have h1 : (fs x).val ≠ 1 := fun h => hHA_disj ⟨3, by decide⟩
      ((congrArg Subtype.val (hfs_inj (Fin.ext (h.trans hfs_r3.symm)))) ▸ hxA)
    omega
  let gR : ↥(H ∪ A) → Fin (Fintype.card V) := fun w =>
    if hw1 : w.1 = u ⟨1, by decide⟩ then ⟨r + 1, by omega⟩
    else if hw2 : w.1 = u ⟨2, by decide⟩ then ⟨r + p2, by omega⟩
    else
      have hwH2A : w.1 ∈ H2 ∪ A := by
        rcases Finset.mem_union.mp w.2 with hwH | hwA
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hwH
          fin_cases i
          · exact Finset.mem_union_left _ (by simp [H2, ← hi])
          · exact absurd hi.symm hw1
          · exact absurd hi.symm hw2
          · exact Finset.mem_union_left _ (by simp [H2, ← hi])
        · exact Finset.mem_union_right _ hwA
      let k := (fs ⟨w.1, hwH2A⟩).val
      if k = 0 then ⟨r, by omega⟩
      else ⟨r + k + 4, by have := (fs ⟨w.1, hwH2A⟩).isLt; dsimp only [lenS, lenR] at this; omega⟩
  have hgR_u0 : gR ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ = ⟨r, by omega⟩ := by
    have h1 : u ⟨0, by decide⟩ ≠ u ⟨1, by decide⟩ := fun h => by have := hu_inj h; simp at this
    have h2 : u ⟨0, by decide⟩ ≠ u ⟨2, by decide⟩ := fun h => by have := hu_inj h; simp at this
    apply Fin.ext; dsimp only [gR]; rw [dif_neg h1, dif_neg h2]
    change (if (fs r0).val = 0 then (⟨r, _⟩ : Fin (Fintype.card V)) else _).val = r
    rw [if_pos hfs_r0]
  have hgR_u1 : gR ⟨u ⟨1, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ = ⟨r + 1, by omega⟩ := by
    dsimp only [gR]; rw [dif_pos rfl]
  have hgR_u2 : gR ⟨u ⟨2, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ = ⟨r + p2, by omega⟩ := by
    have h1 : u ⟨2, by decide⟩ ≠ u ⟨1, by decide⟩ := fun h => by have := hu_inj h; simp at this
    dsimp only [gR]; rw [dif_neg h1, dif_pos rfl]
  have hgR_u3 : gR ⟨u ⟨3, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ = ⟨r + 5, by omega⟩ := by
    have h1 : u ⟨3, by decide⟩ ≠ u ⟨1, by decide⟩ := fun h => by have := hu_inj h; simp at this
    have h2 : u ⟨3, by decide⟩ ≠ u ⟨2, by decide⟩ := fun h => by have := hu_inj h; simp at this
    apply Fin.ext; dsimp only [gR]; rw [dif_neg h1, dif_neg h2]
    change (if (fs r3).val = 0 then (⟨r, _⟩ : Fin (Fintype.card V)) else ⟨r + (fs r3).val + 4, _⟩).val = r + 5
    rw [if_neg (by omega)]; dsimp only; omega
  have hgR_A_eq : ∀ (x : ↥(H ∪ A)) (hxA : x.1 ∈ A),
      gR x = ⟨r + (fs ⟨x.1, Finset.mem_union_right _ hxA⟩).val + 4, by
        have := (fs ⟨x.1, Finset.mem_union_right _ hxA⟩).isLt; dsimp only [lenS, lenR] at this; omega⟩ := by
    intro x hxA
    have h1 : x.1 ≠ u ⟨1, by decide⟩ := fun h => hHA_disj ⟨1, by decide⟩ (h ▸ hxA)
    have h2 : x.1 ≠ u ⟨2, by decide⟩ := fun h => hHA_disj ⟨2, by decide⟩ (h ▸ hxA)
    have hge2 := hfs_A_ge2 ⟨x.1, Finset.mem_union_right _ hxA⟩ hxA
    apply Fin.ext; dsimp only [gR]; rw [dif_neg h1, dif_neg h2, if_neg (by omega)]
  have hgR_A_gt : ∀ x : ↥(H ∪ A), x.1 ∈ A → r + 5 < (gR x).val := by
    intro x hxA; rw [hgR_A_eq x hxA]
    have hge2 := hfs_A_ge2 ⟨x.1, Finset.mem_union_right _ hxA⟩ hxA; dsimp only; omega
  have hgR_val_u : ∀ (w : ↥(H ∪ A)) (i : Fin 4), w.1 = u i →
      (gR w).val = match i.val with | 0 => r | 1 => r + 1 | 2 => r + p2 | _ => r + 5 := by
    intro w i hw
    fin_cases i
    · rw [show w = ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hw, hgR_u0]; rfl
    · rw [show w = ⟨u ⟨1, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hw, hgR_u1]; rfl
    · rw [show w = ⟨u ⟨2, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hw, hgR_u2]; rfl
    · rw [show w = ⟨u ⟨3, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hw, hgR_u3]; rfl
  have hgR_inj : Function.Injective gR := by
    have hp2_bnd : 2 ≤ p2 ∧ p2 ≤ 3 := by rcases hp2 with rfl | rfl <;> omega
    intro x y hxy
    have hval := congrArg Fin.val hxy
    by_cases hx1 : x.1 = u ⟨1, by decide⟩
    · have hxv := hgR_val_u x ⟨1, by decide⟩ hx1; simp only at hxv
      by_cases hyA : y.1 ∈ A
      · exfalso; have := hgR_A_gt y hyA; omega
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((Finset.mem_union.mp y.2).resolve_right hyA)
        have hyv := hgR_val_u y i hi.symm
        fin_cases i <;> (simp only at hyv; first | exact Subtype.ext (hx1.trans hi) | omega)
    · by_cases hx2 : x.1 = u ⟨2, by decide⟩
      · have hxv := hgR_val_u x ⟨2, by decide⟩ hx2; simp only at hxv
        by_cases hyA : y.1 ∈ A
        · exfalso; have := hgR_A_gt y hyA; omega
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((Finset.mem_union.mp y.2).resolve_right hyA)
          have hyv := hgR_val_u y i hi.symm
          fin_cases i <;> (simp only at hyv; first | exact Subtype.ext (hx2.trans hi) | omega)
      · by_cases hy1 : y.1 = u ⟨1, by decide⟩
        · exfalso; have hyv := hgR_val_u y ⟨1, by decide⟩ hy1; simp only at hyv
          by_cases hxA : x.1 ∈ A
          · have := hgR_A_gt x hxA; omega
          · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((Finset.mem_union.mp x.2).resolve_right hxA)
            have hxv := hgR_val_u x i hi.symm
            fin_cases i <;> (simp only at hxv; first | exact hx1 hi.symm | exact hx2 hi.symm | omega)
        · by_cases hy2 : y.1 = u ⟨2, by decide⟩
          · exfalso; have hyv := hgR_val_u y ⟨2, by decide⟩ hy2; simp only at hyv
            by_cases hxA : x.1 ∈ A
            · have := hgR_A_gt x hxA; omega
            · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((Finset.mem_union.mp x.2).resolve_right hxA)
              have hxv := hgR_val_u x i hi.symm
              fin_cases i <;> (simp only at hxv; first | exact hx1 hi.symm | exact hx2 hi.symm | omega)
          · have hxH2A : x.1 ∈ H2 ∪ A := by
              rcases Finset.mem_union.mp x.2 with h | h
              · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
                fin_cases i
                · exact Finset.mem_union_left _ (by simp [H2, ← hi])
                · exact absurd hi.symm hx1
                · exact absurd hi.symm hx2
                · exact Finset.mem_union_left _ (by simp [H2, ← hi])
              · exact Finset.mem_union_right _ h
            have hyH2A : y.1 ∈ H2 ∪ A := by
              rcases Finset.mem_union.mp y.2 with h | h
              · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
                fin_cases i
                · exact Finset.mem_union_left _ (by simp [H2, ← hi])
                · exact absurd hi.symm hy1
                · exact absurd hi.symm hy2
                · exact Finset.mem_union_left _ (by simp [H2, ← hi])
              · exact Finset.mem_union_right _ h
            dsimp only [gR] at hval
            rw [dif_neg hx1, dif_neg hx2, dif_neg hy1, dif_neg hy2] at hval
            have hfs_eq : (fs ⟨x.1, hxH2A⟩).val = (fs ⟨y.1, hyH2A⟩).val := by
              set kx := (fs ⟨x.1, hxH2A⟩).val; set ky := (fs ⟨y.1, hyH2A⟩).val
              split_ifs at hval <;> (simp only at hval; omega)
            exact Subtype.ext (congrArg (fun z : ↥(H2 ∪ A) => z.1) (hfs_inj (Fin.ext hfs_eq)))
  have hgR_adj : ∀ x y : ↥(H ∪ A), D.Adj x.1 y.1 → G.Adj (σ (gR x)) (σ (gR y)) := by
    intro x y hDxy
    by_cases hyA : y.1 ∈ A
    · have hxne1 : x.1 ≠ u ⟨1, by decide⟩ := fun h => hno1A y.1 hyA (h ▸ hDxy)
      have hxne2 : x.1 ≠ u ⟨2, by decide⟩ := fun h => hno2A y.1 hyA (h ▸ hDxy)
      have hxH2A : x.1 ∈ H2 ∪ A := by
        rcases Finset.mem_union.mp x.2 with h | h
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
          fin_cases i
          · exact Finset.mem_union_left _ (by simp [H2, ← hi])
          · exact absurd hi.symm hxne1
          · exact absurd hi.symm hxne2
          · exact Finset.mem_union_left _ (by simp [H2, ← hi])
        · exact Finset.mem_union_right _ h
      have hfs_adj : Gs.Adj (fs ⟨x.1, hxH2A⟩) (fs ⟨y.1, Finset.mem_union_right _ hyA⟩) :=
        fs.map_adj' (show Fs.Adj ⟨x.1, hxH2A⟩ ⟨y.1, Finset.mem_union_right _ hyA⟩ from ⟨hyA, hDxy⟩)
      have hfy_ge2 := hfs_A_ge2 ⟨y.1, Finset.mem_union_right _ hyA⟩ hyA
      dsimp only [Gs] at hfs_adj
      have hgx_eq : gR x = ⟨if (fs ⟨x.1, hxH2A⟩).val = 0 then r else r + (fs ⟨x.1, hxH2A⟩).val + 4, by
          have := (fs ⟨x.1, hxH2A⟩).isLt; dsimp only [lenS, lenR] at this; split_ifs <;> omega⟩ := by
        apply Fin.ext; dsimp only [gR]; rw [dif_neg hxne1, dif_neg hxne2]; split_ifs <;> rfl
      have hgy_eq : gR y = ⟨if (fs ⟨y.1, Finset.mem_union_right _ hyA⟩).val = 0 then r
          else r + (fs ⟨y.1, Finset.mem_union_right _ hyA⟩).val + 4, by
          have := (fs ⟨y.1, Finset.mem_union_right _ hyA⟩).isLt; dsimp only [lenS, lenR] at this; split_ifs <;> omega⟩ := by
        rw [hgR_A_eq y hyA]; apply Fin.ext; dsimp only; rw [if_neg (by omega)]
      rw [hgx_eq, hgy_eq]; exact hfs_adj
    · have hyH : y.1 ∈ H := (Finset.mem_union.mp y.2).resolve_right hyA
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hyH
      have hxH : x.1 ∈ H := by
        rcases Finset.mem_union.mp x.2 with h | hxA
        · exact h
        · exact absurd (hj.symm ▸ hDxy) (hno_AH x.1 hxA j)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hxH
      have ⟨hi0, hj0⟩ := hH_only i j (hi ▸ hj ▸ hDxy)
      subst hi0
      rw [show x = ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hi.symm, hgR_u0]
      fin_cases j
      · exact absurd rfl hj0
      · rw [show y = ⟨u ⟨1, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hj.symm, hgR_u1]; exact hG01
      · rw [show y = ⟨u ⟨2, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hj.symm, hgR_u2]; exact hG0p2
      · rw [show y = ⟨u ⟨3, by decide⟩, Finset.mem_union_left _ (hu_memH _)⟩ from Subtype.ext hj.symm, hgR_u3]; exact hG05
  exact ⟨gR, hgR_inj, hgR_u0, hgR_u1, hgR_u2, hgR_u3, hgR_A_gt, hgR_adj⟩

-- Left-side glue for S4+++ (cntP <= 1) when gR places u at (0, 1, p2, p3) and A strictly > r + p3!
lemma s4ppp_left_and_glue
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (A : Finset W) (_hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hRkM : ∃ rkM : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))),
        x.1 ∈ Finset.univ \ (Finset.univ.image u ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2)
    {σ : Fin (Fintype.card V) ≃ V}
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (r p3 : ℕ) (hrp3 : r + p3 < 2 * n - 2)
    (pos : Fin 4 → Fin (p3 + 1)) (hpos_inj : Function.Injective pos)
    (gR : ↥(Finset.univ.image u ∪ A) → Fin (Fintype.card V))
    (hgR_inj : Function.Injective gR)
    (hgR_u : ∀ i : Fin 4, gR ⟨u i, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩ =
      ⟨r + (pos i).val, by omega⟩)
    (hgR_A_gt : ∀ x : ↥(Finset.univ.image u ∪ A), x.1 ∈ A → r + p3 < (gR x).val)
    (hgR_adj : ∀ x y : ↥(Finset.univ.image u ∪ A), D.Adj x.1 y.1 → G.Adj (σ (gR x)) (σ (gR y)))
    (fL : Fin (p3 + 1) → Option (Fin 4))
    (hfL_inj : ∀ t1 t2 : Fin (p3 + 1), (∀ i, pos i ≠ t1) → (∀ i, pos i ≠ t2) →
      ∀ h : Fin 4, fL t1 = some h → fL t2 = some h → t1 = t2)
    (hfL_valid : ∀ t : Fin (p3 + 1), (∀ i, pos i ≠ t) → ∀ h : Fin 4, fL t = some h →
      t.val < (pos h).val ∧
      G.Adj (σ ⟨r + t.val, by omega⟩) (σ ⟨r + (pos h).val, by omega⟩) ∧
      ∃ c ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj c (u h))
    (hBoundL : ∀ exhL : Finset (Fin 4),
      (∀ i ∈ exhL, ∃ t : Fin (p3 + 1), (∀ j, pos j ≠ t) ∧ fL t = some i) →
      ∃ qL : ℕ, qL ≤ p3 + 1 ∧
        (∀ t : Fin (p3 + 1), p3 - t.val < qL →
          (∀ i : Fin 4, pos i = t →
            (∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i)) ∨ i ∈ exhL) ∧
          ((∀ i : Fin 4, pos i ≠ t) → fL t = none)) ∧
        4 + (Finset.univ \ (Finset.univ.image u ∪ A)).card +
          ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card +
          2 * (Finset.univ.filter (fun t : Fin (p3 + 1) => (∀ i, pos i ≠ t) ∧ fL t = none)).card +
          (Finset.univ.filter (fun i : Fin 4 =>
            ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card + exhL.card
          ≤ (r + p3 + 1) + 1 + qL) :
    Embeds D G := by
  classical
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let L : ℕ := p3 + 1
  have hu_memH : ∀ i : Fin 4, u i ∈ H := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hH_card : H.card = 4 := by
    rw [Finset.card_image_of_injective _ hu_inj, Finset.card_univ, Fintype.card_fin]
  have hHB_disj' : Disjoint H B := Finset.disjoint_left.mpr (fun x hxH hxB =>
    (Finset.mem_sdiff.mp hxB).2 (Finset.mem_union_left _ hxH))
  let DumL : Finset (Fin L) := Finset.univ.filter (fun t : Fin L => (∀ i, pos i ≠ t) ∧ fL t = none)
  let cutChildL : ∀ t : Fin L, (∀ i, pos i ≠ t) → ∀ h : Fin 4, fL t = some h → W :=
    fun t ht h hft => Classical.choose (hfL_valid t ht h hft).2.2
  have hcutL_spec : ∀ (t : Fin L) (ht : ∀ i, pos i ≠ t) (h : Fin 4) (hft : fL t = some h),
      cutChildL t ht h hft ∈ B ∧ D.Adj (cutChildL t ht h hft) (u h) :=
    fun t ht h hft => Classical.choose_spec (hfL_valid t ht h hft).2.2
  let isCutL : W → Prop := fun y => ∃ (t : Fin L) (ht : ∀ i, pos i ≠ t) (h : Fin 4) (hft : fL t = some h),
    cutChildL t ht h hft = y
  have hcutL_inj_val : ∀ (t1 : Fin L) (ht1 : ∀ i, pos i ≠ t1) (h1 : Fin 4) (hf1 : fL t1 = some h1)
      (t2 : Fin L) (ht2 : ∀ i, pos i ≠ t2) (h2 : Fin 4) (hf2 : fL t2 = some h2),
      cutChildL t1 ht1 h1 hf1 = cutChildL t2 ht2 h2 hf2 → t1 = t2 := by
    intro t1 ht1 h1 hf1 t2 ht2 h2 hf2 heq
    have hc1 := hcutL_spec t1 ht1 h1 hf1
    have hc2 := hcutL_spec t2 ht2 h2 hf2
    have hnotHA := (Finset.mem_sdiff.mp hc1.1).2
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hB_out (cutChildL t1 ht1 h1 hf1)
      (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
      (fun h => hnotHA (Finset.mem_union_right _ h)))
    have e1 : u h1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1.2⟩)
    have e2 : u h2 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq ▸ hc2.2⟩)
    exact hfL_inj t1 t2 ht1 ht2 h1 hf1 (hu_inj (e1.trans e2.symm) ▸ hf2)
  let WL := ↥(H ∪ B) ⊕ ↥DumL
  let Fm : Digraph WL := ⟨fun x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => a.1 ∈ B ∧ ¬ isCutL a.1 ∧ D.Adj a.1 b.1
    | _, _ => False⟩
  have hFm_rank : ∃ rk : WL → ℕ, ∀ x y, Fm.Adj x y → rk y < rk x := by
    obtain ⟨rkM, hrkM⟩ := hRkM
    refine ⟨Sum.elim rkM (fun _ => 0), fun x y hxy => ?_⟩
    cases x <;> cases y <;> simp only [Fm] at hxy
    exact hrkM _ _ hxy.1 hxy.2.2
  have hFm_out : ∀ w u1 u2 : WL, Fm.Adj w u1 → Fm.Adj w u2 → u1 = u2 := by
    intro w a1 a2 h1 h2
    cases w <;> cases a1 <;> cases a2 <;> simp only [Fm] at h1 h2
    rename_i w' b1 b2
    have hnotHA := (Finset.mem_sdiff.mp h1.1).2
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hB_out w'.1
      (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
      (fun h => hnotHA (Finset.mem_union_right _ h)))
    have e1 : b1.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.2.2⟩)
    have e2 : b2.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.2.2⟩)
    exact congrArg Sum.inl (Subtype.ext (e1.trans e2.symm))
  let revL : Fin L → Fin L := fun j => ⟨p3 - j.val, by omega⟩
  have hrevL_inv : ∀ j : Fin L, revL (revL j) = j := fun j => Fin.ext (by dsimp only [revL]; omega)
  have hrevL_inj : Function.Injective revL := fun j1 j2 h => by
    have := congrArg revL h; rwa [hrevL_inv, hrevL_inv] at this
  let rootsL : Fin L → WL := fun j =>
    let t := revL j
    if hi_ex : ∃ i : Fin 4, pos i = t then
      Sum.inl ⟨u (Classical.choose hi_ex), Finset.mem_union_left _ (hu_memH _)⟩
    else match hft : fL t with
    | none => Sum.inr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => hi_ex ⟨i, hi⟩, hft⟩⟩
    | some h =>
      let ht : ∀ i, pos i ≠ t := fun i hi => hi_ex ⟨i, hi⟩
      Sum.inl ⟨cutChildL t ht h hft, Finset.mem_union_right _ (hcutL_spec t ht h hft).1⟩
  have hrootsL_pos : ∀ i : Fin 4, rootsL (revL (pos i)) = Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ := by
    intro i
    have hex : ∃ k : Fin 4, pos k = pos i := ⟨i, rfl⟩
    simp only [rootsL, hrevL_inv, hex, ↓reduceDIte]
    exact congrArg Sum.inl (Subtype.ext (congrArg u (hpos_inj (Classical.choose_spec hex))))
  have hrootsL_free_none : ∀ (t : Fin L) (ht : ∀ i, pos i ≠ t) (hft : fL t = none),
      rootsL (revL t) = Sum.inr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hft⟩⟩ := by
    intro t ht hft
    have hnot : ¬ ∃ i : Fin 4, pos i = t := fun ⟨i, hi⟩ => ht i hi
    dsimp only [rootsL]; rw [hrevL_inv, dif_neg hnot]; split
    · rfl
    · rename_i _ heq; rw [hft] at heq; cases heq
  have hrootsL_free_some : ∀ (t : Fin L) (ht : ∀ i, pos i ≠ t) (h : Fin 4) (hft : fL t = some h),
      rootsL (revL t) = Sum.inl ⟨cutChildL t ht h hft, Finset.mem_union_right _ (hcutL_spec t ht h hft).1⟩ := by
    intro t ht h hft
    have hnot : ¬ ∃ i : Fin 4, pos i = t := fun ⟨i, hi⟩ => ht i hi
    dsimp only [rootsL]; rw [hrevL_inv, dif_neg hnot]; split
    · rename_i heq; rw [hft] at heq; cases heq
    · rename_i h' heq
      have hh : h' = h := Option.some.inj (heq.symm.trans hft)
      subst hh; rfl
  have hrootsL_inj : Function.Injective rootsL := by
    intro j1 j2 heq
    apply hrevL_inj
    set t1 := revL j1; set t2 := revL j2
    have heq' : rootsL (revL t1) = rootsL (revL t2) := by rwa [hrevL_inv, hrevL_inv]
    by_cases h1 : ∃ i, pos i = t1 <;> by_cases h2 : ∃ i, pos i = t2
    · obtain ⟨i1, hi1⟩ := h1; obtain ⟨i2, hi2⟩ := h2
      rw [← hi1, ← hi2, hrootsL_pos i1, hrootsL_pos i2] at heq'
      rw [← hi1, ← hi2, hu_inj (congrArg Subtype.val (Sum.inl.inj heq'))]
    · obtain ⟨i1, hi1⟩ := h1
      have ht2 : ∀ i, pos i ≠ t2 := fun i hi => h2 ⟨i, hi⟩
      rw [← hi1, hrootsL_pos i1] at heq'
      cases hf2 : fL t2 with
      | none => rw [hrootsL_free_none t2 ht2 hf2] at heq'; exact absurd heq' (by simp)
      | some h =>
        rw [hrootsL_free_some t2 ht2 h hf2] at heq'
        have heqW : u i1 = cutChildL t2 ht2 h hf2 := congrArg Subtype.val (Sum.inl.inj heq')
        exact absurd (heqW ▸ (hcutL_spec t2 ht2 h hf2).1)
          (Finset.disjoint_left.mp hHB_disj' (hu_memH i1))
    · obtain ⟨i2, hi2⟩ := h2
      have ht1 : ∀ i, pos i ≠ t1 := fun i hi => h1 ⟨i, hi⟩
      rw [← hi2, hrootsL_pos i2] at heq'
      cases hf1 : fL t1 with
      | none => rw [hrootsL_free_none t1 ht1 hf1] at heq'; exact absurd heq' (by simp)
      | some h =>
        rw [hrootsL_free_some t1 ht1 h hf1] at heq'
        have heqW : cutChildL t1 ht1 h hf1 = u i2 := congrArg Subtype.val (Sum.inl.inj heq')
        exact absurd (heqW ▸ (hcutL_spec t1 ht1 h hf1).1)
          (Finset.disjoint_left.mp hHB_disj' (hu_memH i2))
    · have ht1 : ∀ i, pos i ≠ t1 := fun i hi => h1 ⟨i, hi⟩
      have ht2 : ∀ i, pos i ≠ t2 := fun i hi => h2 ⟨i, hi⟩
      cases hf1 : fL t1 with
      | none =>
        rw [hrootsL_free_none t1 ht1 hf1] at heq'
        cases hf2 : fL t2 with
        | none => rw [hrootsL_free_none t2 ht2 hf2] at heq'; exact congrArg Subtype.val (Sum.inr.inj heq')
        | some h2' => rw [hrootsL_free_some t2 ht2 h2' hf2] at heq'; exact absurd heq' (by simp)
      | some h1' =>
        rw [hrootsL_free_some t1 ht1 h1' hf1] at heq'
        cases hf2 : fL t2 with
        | none => rw [hrootsL_free_none t2 ht2 hf2] at heq'; exact absurd heq' (by simp)
        | some h2' =>
          rw [hrootsL_free_some t2 ht2 h2' hf2] at heq'
          exact hcutL_inj_val t1 ht1 h1' hf1 t2 ht2 h2' hf2 (congrArg Subtype.val (Sum.inl.inj heq'))
  have hrootsL_iff : ∀ w : WL, (∀ z, ¬ Fm.Adj w z) ↔ ∃ j : Fin L, rootsL j = w := by
    intro w
    constructor
    · intro hno
      cases w with
      | inr d =>
        have hd := Finset.mem_filter.mp d.2
        exact ⟨revL d.1, by rw [hrootsL_free_none d.1 hd.2.1 hd.2.2]⟩
      | inl a =>
        by_cases haH : a.1 ∈ H
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp haH
          exact ⟨revL (pos i), by rw [hrootsL_pos i]; exact congrArg Sum.inl (Subtype.ext hi)⟩
        · have haB : a.1 ∈ B := (Finset.mem_union.mp a.2).resolve_left haH
          by_cases hcut : isCutL a.1
          · obtain ⟨t, ht, h, hft, heqc⟩ := hcut
            exact ⟨revL t, by rw [hrootsL_free_some t ht h hft]; exact congrArg Sum.inl (Subtype.ext heqc)⟩
          · exfalso
            have hnotHA := (Finset.mem_sdiff.mp haB).2
            have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj a.1 z)).card := by
              rw [hB_out a.1 (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
                (fun h => hnotHA (Finset.mem_union_right _ h))]; omega
            obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
            have hDaz := (Finset.mem_filter.mp hz).2
            have hzHB : z ∈ H ∪ B := by
              by_contra hznot
              have hzH : z ∉ H := fun h => hznot (Finset.mem_union_left _ h)
              have hzA : z ∈ A := by
                by_contra hznotA
                exact hznot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
                  (Finset.mem_union.mp h).elim hzH hznotA⟩))
              exact (hno_AB z hzA a.1 (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
                (fun h => hnotHA (Finset.mem_union_right _ h))).2 hDaz
            exact hno (Sum.inl ⟨z, hzHB⟩) ⟨haB, hcut, hDaz⟩
    · rintro ⟨j, rfl⟩ z hFm
      set t := revL j
      have hrj : rootsL j = rootsL (revL t) := by rw [hrevL_inv]
      rw [hrj] at hFm
      by_cases h1 : ∃ i, pos i = t
      · obtain ⟨i, hi⟩ := h1
        rw [← hi, hrootsL_pos i] at hFm
        cases z <;> simp only [Fm] at hFm
        exact Finset.disjoint_left.mp hHB_disj' (hu_memH i) hFm.1
      · have ht : ∀ i, pos i ≠ t := fun i hi => h1 ⟨i, hi⟩
        cases hft : fL t with
        | none => rw [hrootsL_free_none t ht hft] at hFm; cases z <;> simp only [Fm] at hFm
        | some h => rw [hrootsL_free_some t ht h hft] at hFm; cases z <;> simp only [Fm] at hFm; exact hFm.2.1 ⟨t, ht, h, hft, rfl⟩
  let exhL : Finset (Fin 4) := Finset.univ.filter (fun i : Fin 4 =>
    (∃ y ∈ B, D.Adj y (u i)) ∧ ∀ z : WL, ¬ Fm.Adj z (Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩))
  have hexhL_cut : ∀ i ∈ exhL, ∃ t : Fin L, (∀ j, pos j ≠ t) ∧ fL t = some i := by
    intro i hi
    obtain ⟨⟨y, hyB, hDyu⟩, hnoFm⟩ := (Finset.mem_filter.mp hi).2
    have hcuty : isCutL y := by by_contra hnc; exact hnoFm (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩) ⟨hyB, hnc, hDyu⟩
    obtain ⟨t, ht, h, hft, heqc⟩ := hcuty
    have hc := hcutL_spec t ht h hft
    have hnotHA := (Finset.mem_sdiff.mp hyB).2
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hB_out y
      (fun k hk => hnotHA (Finset.mem_union_left _ (hk ▸ hu_memH k)))
      (fun h' => hnotHA (Finset.mem_union_right _ h')))
    have e1 : u i = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDyu⟩)
    have e2 : u h = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqc ▸ hc.2⟩)
    exact ⟨t, ht, hu_inj (e2.trans e1.symm) ▸ hft⟩
  obtain ⟨qL, hqL_le, hqL_pref, hqL_card⟩ := hBoundL exhL hexhL_cut
  have hFm_cardW : Fintype.card WL = 4 + B.card + DumL.card := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Finset.card_union_of_disjoint hHB_disj', hH_card]
  have hFm_leaves : (Finset.univ.filter (fun w : WL => ∀ z, ¬ Fm.Adj z w)).card ≤
      (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card + DumL.card +
      (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card + exhL.card := by
    let LFm := Finset.univ.filter (fun w : WL => ∀ z, ¬ Fm.Adj z w)
    let S1 := LFm.filter (fun w => match w with | Sum.inl a => a.1 ∈ B | Sum.inr _ => False)
    let S2 := LFm.filter (fun w => match w with | Sum.inl _ => False | Sum.inr _ => True)
    let S3 := LFm.filter (fun w => match w with | Sum.inl a => a.1 ∈ H | Sum.inr _ => False)
    have hcov : LFm ⊆ S1 ∪ S2 ∪ S3 := by
      intro w hw
      cases w with
      | inr d => exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, trivial⟩))
      | inl a =>
        rcases Finset.mem_union.mp a.2 with haH | haB
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, haH⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, haB⟩))
    have hS1 : S1.card ≤ (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card := by
      have hle : S1.card ≤ (S1.image (Sum.elim (fun a => a.1) (fun _ => u ⟨0, by decide⟩))).card := by
        rw [Finset.card_image_of_injOn]
        intro w1 hw1 w2 hw2 heq
        have h1 := (Finset.mem_filter.mp hw1).2; have h2 := (Finset.mem_filter.mp hw2).2
        cases w1 <;> cases w2 <;> simp only at h1 h2 heq
        exact congrArg Sum.inl (Subtype.ext heq)
      refine hle.trans (Finset.card_le_card (fun y hy => ?_))
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hwL, hwB⟩ := Finset.mem_filter.mp hw
      cases w with
      | inr _ => exact absurd hwB id
      | inl a =>
        dsimp only [Sum.elim] at hwB ⊢
        refine Finset.mem_filter.mpr ⟨hwB, fun z hDza => ?_⟩
        by_cases hzB : z ∈ B
        · have hnoFm := (Finset.mem_filter.mp hwL).2 (Sum.inl ⟨z, Finset.mem_union_right _ hzB⟩)
          have hcutz : isCutL z := by by_contra hnc; exact hnoFm ⟨hzB, hnc, hDza⟩
          obtain ⟨t, ht, h, hft, heqc⟩ := hcutz
          have hc := hcutL_spec t ht h hft
          have hnotHA := (Finset.mem_sdiff.mp hzB).2
          obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hB_out z
            (fun k hk => hnotHA (Finset.mem_union_left _ (hk ▸ hu_memH k)))
            (fun h' => hnotHA (Finset.mem_union_right _ h')))
          have e1 : a.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDza⟩)
          have e2 : u h = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqc ▸ hc.2⟩)
          exact Finset.disjoint_left.mp hHB_disj' (hu_memH h) (e2.trans e1.symm ▸ hwB)
        · by_cases hzH : z ∈ H
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hzH; exact hno_HB j a.1 hwB hDza
          · have hzA : z ∈ A := by
              by_contra hznotA
              exact hzB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hznotA⟩)
            have hanotHA := (Finset.mem_sdiff.mp hwB).2
            exact (hno_AB z hzA a.1 (fun j hj => hanotHA (Finset.mem_union_left _ (hj ▸ hu_memH j)))
              (fun h => hanotHA (Finset.mem_union_right _ h))).1 hDza
    have hS2 : S2.card ≤ DumL.card := by
      have himg : S2 ⊆ (Finset.univ : Finset ↥DumL).image Sum.inr := fun w hw => by
        cases w with
        | inl _ => exact absurd (Finset.mem_filter.mp hw).2 id
        | inr d => exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩
      simpa using (Finset.card_le_card himg).trans Finset.card_image_le
    have hS3 : S3.card ≤ (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card + exhL.card := by
      let Z0 := Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))
      have himg : S3 ⊆ (Z0 ∪ exhL).image (fun i => Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩) := by
        intro w hw
        obtain ⟨hwL, hwH⟩ := Finset.mem_filter.mp hw
        cases w with
        | inr _ => exact absurd hwH id
        | inl a =>
          dsimp only at hwH
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hwH
          refine Finset.mem_image.mpr ⟨i, ?_, congrArg Sum.inl (Subtype.ext hi)⟩
          by_cases hex : ∃ y ∈ B, D.Adj y (u i)
          · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex, ?_⟩)
            have haeq : a = ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ := Subtype.ext hi.symm
            exact haeq ▸ (Finset.mem_filter.mp hwL).2
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy hD => hex ⟨y, hy, hD⟩⟩)
      exact ((Finset.card_le_card himg).trans Finset.card_image_le).trans (Finset.card_union_le _ _)
    calc LFm.card ≤ (S1 ∪ S2 ∪ S3).card := Finset.card_le_card hcov
      _ ≤ (S1 ∪ S2).card + S3.card := Finset.card_union_le _ _
      _ ≤ S1.card + S2.card + S3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ _ := by omega
  have hFm_pref : ∀ j : Fin L, j.val < qL → ∀ z : WL, ¬ Fm.Adj z (rootsL j) := by
    intro j hjq z hFm
    set t := revL j
    have htq : p3 - t.val < qL := by dsimp only [t, revL]; omega
    have hp := hqL_pref t htq
    have hrj : rootsL j = rootsL (revL t) := by rw [hrevL_inv]
    rw [hrj] at hFm
    by_cases h1 : ∃ i, pos i = t
    · obtain ⟨i, hi_eq⟩ := h1
      rw [← hi_eq, hrootsL_pos i] at hFm
      rcases hp.1 i hi_eq with hnoB | hi_exh
      · cases z <;> simp only [Fm] at hFm; exact hnoB _ hFm.1 hFm.2.2
      · exact (Finset.mem_filter.mp hi_exh).2.2 z hFm
    · have ht : ∀ i, pos i ≠ t := fun i hi_eq => h1 ⟨i, hi_eq⟩
      rw [hrootsL_free_none t ht (hp.2 ht)] at hFm
      cases z <;> simp only [Fm] at hFm
  obtain ⟨gL, hgL_inj, hgL_range, hgL_adj, hgL_roots⟩ := greedy_left_interval Fm hFm_rank hFm_out G hL
    (r + p3) (r + p3 + 1) (le_refl _) (by omega) rootsL hrootsL_inj hrootsL_iff (by omega) qL hqL_le hFm_pref
    (by rw [hFm_cardW]; dsimp only [B, H, DumL, L] at hFm_leaves ⊢; omega)
  have hgL_u : ∀ i : Fin 4, gL (Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩) =
      ⟨r + (pos i).val, by omega⟩ := by
    intro i; rw [← hrootsL_pos i, hgL_roots (revL (pos i))]; apply Fin.ext; dsimp only [revL]; omega
  -- Glue gR (on H ∪ A) and gL (on H ∪ B): ZERO overlap because gR(A) > r + p3 >= gL(B)!
  let φ : W → Fin (Fintype.card V) := fun w =>
    if hwHA : w ∈ H ∪ A then gR ⟨w, hwHA⟩
    else gL (Sum.inl ⟨w, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwHA⟩)⟩)
  have hφ_on_HB : ∀ w (hw : w ∈ H ∪ B), φ w = gL (Sum.inl ⟨w, hw⟩) := by
    intro w hw
    by_cases hwH : w ∈ H
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwH
      simp only [φ, Finset.mem_union_left _ (hu_memH i), ↓reduceDIte]
      rw [hgR_u i, hgL_u i]
    · have hwB : w ∈ B := (Finset.mem_union.mp hw).resolve_left hwH
      simp only [φ, (Finset.mem_sdiff.mp hwB).2, ↓reduceDIte]
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    by_cases hx : x ∈ H ∪ A <;> by_cases hy : y ∈ H ∪ A
    · simp only [φ, hx, hy, ↓reduceDIte] at hxy
      exact congrArg Subtype.val (hgR_inj hxy)
    · exfalso
      have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩
      by_cases hxH : x ∈ H
      · rw [hφ_on_HB x (Finset.mem_union_left _ hxH), hφ_on_HB y (Finset.mem_union_right _ hyB)] at hxy
        have heq : x = y := congrArg Subtype.val (Sum.inl.inj (hgL_inj hxy))
        exact Finset.disjoint_left.mp hHB_disj' hxH (heq ▸ hyB)
      · have hxA : x ∈ A := (Finset.mem_union.mp hx).resolve_left hxH
        simp only [φ, hx, hy, ↓reduceDIte] at hxy
        have hgt := hgR_A_gt ⟨x, hx⟩ hxA
        have hle := (hgL_range (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩)).2
        have hv := congrArg Fin.val hxy
        omega
    · exfalso
      have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
      by_cases hyH : y ∈ H
      · rw [hφ_on_HB x (Finset.mem_union_right _ hxB), hφ_on_HB y (Finset.mem_union_left _ hyH)] at hxy
        have heq : x = y := congrArg Subtype.val (Sum.inl.inj (hgL_inj hxy))
        exact Finset.disjoint_left.mp hHB_disj' hyH (heq ▸ hxB)
      · have hyA : y ∈ A := (Finset.mem_union.mp hy).resolve_left hyH
        simp only [φ, hx, hy, ↓reduceDIte] at hxy
        have hgt := hgR_A_gt ⟨y, hy⟩ hyA
        have hle := (hgL_range (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩)).2
        have hv := congrArg Fin.val hxy
        omega
    · simp only [φ, hx, hy, ↓reduceDIte] at hxy
      exact congrArg Subtype.val (Sum.inl.inj (hgL_inj hxy))
  have hφ_adj : ∀ x y : W, D.Adj x y → G.Adj (σ (φ x)) (σ (φ y)) := by
    intro x y hDxy
    by_cases hxHA : x ∈ H ∪ A
    · by_cases hyHA : y ∈ H ∪ A
      · simp only [φ, hxHA, hyHA, ↓reduceDIte]
        exact hgR_adj ⟨x, hxHA⟩ ⟨y, hyHA⟩ hDxy
      · exfalso
        have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyHA⟩
        rcases Finset.mem_union.mp hxHA with hxH | hxA
        · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH; exact hno_HB i y hyB hDxy
        · exact (hno_AB x hxA y (fun i hi => hyHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
            (fun h => hyHA (Finset.mem_union_right _ h))).1 hDxy
    · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxHA⟩
      have hyHB : y ∈ H ∪ B := by
        by_contra hynot
        have hyH : y ∉ H := fun h => hynot (Finset.mem_union_left _ h)
        have hyA : y ∈ A := by
          by_contra hynotA
          exact hynot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
            (Finset.mem_union.mp h).elim hyH hynotA⟩))
        exact (hno_AB y hyA x (fun i hi => hxHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
          (fun h => hxHA (Finset.mem_union_right _ h))).2 hDxy
      rw [hφ_on_HB x (Finset.mem_union_right _ hxB), hφ_on_HB y hyHB]
      by_cases hcut : isCutL x
      · obtain ⟨t, ht, h, hft, heqc⟩ := hcut
        have hc := hcutL_spec t ht h hft
        obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hB_out x
          (fun i hi => hxHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
          (fun h' => hxHA (Finset.mem_union_right _ h')))
        have e1 : y = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDxy⟩)
        have e2 : u h = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqc ▸ hc.2⟩)
        have hyu : y = u h := e1.trans e2.symm
        have hgx : gL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩) = ⟨r + t.val, by omega⟩ := by
          have hx_eq : (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩ : WL) = rootsL (revL t) := by
            rw [hrootsL_free_some t ht h hft]; exact congrArg Sum.inl (Subtype.ext heqc.symm)
          rw [hx_eq, hgL_roots (revL t)]; apply Fin.ext; dsimp only [revL]; omega
        have hgy : gL (Sum.inl ⟨y, hyHB⟩) = ⟨r + (pos h).val, by omega⟩ := by
          rw [show (Sum.inl ⟨y, hyHB⟩ : WL) = Sum.inl ⟨u h, Finset.mem_union_left _ (hu_memH h)⟩ from
            congrArg Sum.inl (Subtype.ext hyu), hgL_u h]
        rw [hgx, hgy]; exact (hfL_valid t ht h hft).2.1
      · exact hgL_adj _ _ ⟨hxB, hcut, hDxy⟩
  exact ⟨⟨fun w => σ (φ w), fun h => hφ_adj _ _ h⟩, fun x y h => hφ_inj (σ.injective h)⟩

-- ============================================================================

-- MODULE 6A: M2 Window Lemmas, Minimality (Heart-3), Pure-4 Wrapper & Topologies 1-4
-- ============================================================================

lemma m2_right_4 {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (a : ℕ) (ha : a + 3 < Fintype.card V)
    (hnot : ¬ G.Adj (σ ⟨a, by omega⟩) (σ ⟨a + 3, by omega⟩)) :
    G.Adj (σ ⟨a, by omega⟩) (σ ⟨a + 2, by omega⟩) := by
  classical
  by_contra hnot2
  have hm := hR ⟨a, by omega⟩ ⟨a + 3, ha⟩ (by change a < a + 3; omega)
  have hsub : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      (⟨a, by omega⟩ : Fin (Fintype.card V)) < k ∧ k ≤ ⟨a + 3, ha⟩ ∧
      G.Adj (σ ⟨a, by omega⟩) (σ k)) ⊆ {⟨a + 1, by omega⟩} := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    have h1 : a < k.val := hk'.1; have h2 : k.val ≤ a + 3 := hk'.2.1
    rw [Finset.mem_singleton]
    rcases (by omega : k.val = a + 1 ∨ k.val = a + 2 ∨ k.val = a + 3) with h | h | h
    · exact Fin.ext h
    · exfalso; exact hnot2 ((show k = ⟨a + 2, by omega⟩ from Fin.ext h) ▸ hk'.2.2)
    · exfalso; exact hnot ((show k = ⟨a + 3, by omega⟩ from Fin.ext h) ▸ hk'.2.2)
  have hle := (Finset.card_le_card hsub).trans (by rw [Finset.card_singleton])
  dsimp only at hm; omega

lemma m2_left_4 {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] {σ : Fin (Fintype.card V) ≃ V}
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (a : ℕ) (ha : a + 3 < Fintype.card V)
    (hnot : ¬ G.Adj (σ ⟨a, by omega⟩) (σ ⟨a + 3, by omega⟩)) :
    G.Adj (σ ⟨a + 1, by omega⟩) (σ ⟨a + 3, by omega⟩) := by
  classical
  by_contra hnot1
  have hm := hL ⟨a, by omega⟩ ⟨a + 3, ha⟩ (by change a < a + 3; omega)
  have hsub : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      (⟨a, by omega⟩ : Fin (Fintype.card V)) ≤ k ∧ k < ⟨a + 3, ha⟩ ∧
      G.Adj (σ k) (σ ⟨a + 3, ha⟩)) ⊆ {⟨a + 2, by omega⟩} := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    have h1 : a ≤ k.val := hk'.1; have h2 : k.val < a + 3 := hk'.2.1
    rw [Finset.mem_singleton]
    rcases (by omega : k.val = a ∨ k.val = a + 1 ∨ k.val = a + 2) with h | h | h
    · exfalso; exact hnot ((show k = ⟨a, by omega⟩ from Fin.ext h) ▸ hk'.2.2)
    · exfalso; exact hnot1 ((show k = ⟨a + 1, by omega⟩ from Fin.ext h) ▸ hk'.2.2)
    · exact Fin.ext h
  have hle := (Finset.card_le_card hsub).trans (by rw [Finset.card_singleton])
  dsimp only at hm; omega

lemma m2_right_6_ge3 {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (r : ℕ) (hr : r + 5 < Fintype.card V) :
    3 ≤ (Finset.univ.filter (fun k : Fin 5 =>
      G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1 + k.val, by omega⟩))).card := by
  classical
  have hm := hR ⟨r, by omega⟩ ⟨r + 5, hr⟩ (by change r < r + 5; omega)
  have hbij : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      (⟨r, by omega⟩ : Fin (Fintype.card V)) < k ∧ k ≤ ⟨r + 5, hr⟩ ∧
      G.Adj (σ ⟨r, by omega⟩) (σ k))).card =
    (Finset.univ.filter (fun k : Fin 5 =>
      G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1 + k.val, by omega⟩))).card := by
    refine Finset.card_bij (fun k hk => ⟨k.val - r - 1, by
      have hk' := (Finset.mem_filter.mp hk).2; have h1 : r < k.val := hk'.1; have h2 : k.val ≤ r + 5 := hk'.2.1; omega⟩) ?_ ?_ ?_
    · intro k hk
      have hk' := (Finset.mem_filter.mp hk).2; have h1 : r < k.val := hk'.1; have h2 : k.val ≤ r + 5 := hk'.2.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      convert hk'.2.2 using 2; apply Fin.ext; dsimp only; omega
    · intro a ha b hb h
      have h1 : r < a.val := (Finset.mem_filter.mp ha).2.1
      have h2 : r < b.val := (Finset.mem_filter.mp hb).2.1
      have hv := congrArg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
    · intro k hk
      refine ⟨⟨r + 1 + k.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by change r < r + 1 + k.val; omega, by change r + 1 + k.val ≤ r + 5; omega,
        (Finset.mem_filter.mp hk).2⟩, Fin.ext (by dsimp only; omega)⟩
  dsimp only at hm; omega

lemma m2_left_6_ge3 {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] {σ : Fin (Fintype.card V) ≃ V}
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (r : ℕ) (hr : r + 5 < Fintype.card V) :
    3 ≤ (Finset.univ.filter (fun k : Fin 5 =>
      G.Adj (σ ⟨r + k.val, by omega⟩) (σ ⟨r + 5, hr⟩))).card := by
  classical
  have hm := hL ⟨r, by omega⟩ ⟨r + 5, hr⟩ (by change r < r + 5; omega)
  have hbij : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      (⟨r, by omega⟩ : Fin (Fintype.card V)) ≤ k ∧ k < ⟨r + 5, hr⟩ ∧
      G.Adj (σ k) (σ ⟨r + 5, hr⟩))).card =
    (Finset.univ.filter (fun k : Fin 5 =>
      G.Adj (σ ⟨r + k.val, by omega⟩) (σ ⟨r + 5, hr⟩))).card := by
    refine Finset.card_bij (fun k hk => ⟨k.val - r, by
      have hk' := (Finset.mem_filter.mp hk).2; have h1 : r ≤ k.val := hk'.1; have h2 : k.val < r + 5 := hk'.2.1; omega⟩) ?_ ?_ ?_
    · intro k hk
      have hk' := (Finset.mem_filter.mp hk).2; have h1 : r ≤ k.val := hk'.1; have h2 : k.val < r + 5 := hk'.2.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      convert hk'.2.2 using 2; apply Fin.ext; dsimp only; omega
    · intro a ha b hb h
      have h1 : r ≤ a.val := (Finset.mem_filter.mp ha).2.1
      have h2 : r ≤ b.val := (Finset.mem_filter.mp hb).2.1
      have hv := congrArg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
    · intro k hk
      refine ⟨⟨r + k.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by change r ≤ r + k.val; omega, by change r + k.val < r + 5; omega,
        (Finset.mem_filter.mp hk).2⟩, Fin.ext (by dsimp only; omega)⟩
  dsimp only at hm; omega

-- Pure-M2 6-window covering lemmas for S4+++ Families F1, F2, F3
lemma lmo6_F1 {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] (_hG : G.IsTournament)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (r : ℕ) (hr : r + 5 < Fintype.card V) :
    let v : Fin 6 → V := fun k => σ ⟨r + k.val, by omega⟩
    (G.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) ∧ G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩)) ∨
    (G.Adj (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) ∧ G.Adj (v ⟨1, by decide⟩) (v ⟨4, by decide⟩)) ∨
    (G.Adj (v ⟨2, by decide⟩) (v ⟨4, by decide⟩) ∧ G.Adj (v ⟨2, by decide⟩) (v ⟨5, by decide⟩)) ∨
    (G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) ∧ G.Adj (v ⟨0, by decide⟩) (v ⟨4, by decide⟩)) ∨
    (G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) ∧ G.Adj (v ⟨0, by decide⟩) (v ⟨5, by decide⟩)) ∨
    (G.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) ∧ G.Adj (v ⟨0, by decide⟩) (v ⟨5, by decide⟩)) ∨
    (G.Adj (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) ∧ G.Adj (v ⟨1, by decide⟩) (v ⟨5, by decide⟩)) := by
  classical
  intro v
  by_contra hall
  push Not at hall
  obtain ⟨nP1, nP2, nP3, nP4, nP5, nP6, nP7⟩ := hall
  have hnot03 : ¬ G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) := by
    intro h03
    have hnot02 : ¬ G.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) := fun h => nP1 h h03
    have hnot04 : ¬ G.Adj (v ⟨0, by decide⟩) (v ⟨4, by decide⟩) := fun h => nP4 h03 h
    have hnot05 : ¬ G.Adj (v ⟨0, by decide⟩) (v ⟨5, by decide⟩) := fun h => nP5 h03 h
    have hge3 := m2_right_6_ge3 hR r hr
    have hsub : Finset.univ.filter (fun k : Fin 5 =>
        G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1 + k.val, by omega⟩)) ⊆ {⟨0, by decide⟩, ⟨2, by decide⟩} := by
      intro k hk
      have hadj := (Finset.mem_filter.mp hk).2
      fin_cases k
      · exact Finset.mem_insert_self _ _
      · exfalso; exact hnot02 hadj
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exfalso; exact hnot04 hadj
      · exfalso; exact hnot05 hadj
    have hle := (Finset.card_le_card hsub).trans (Finset.card_le_two)
    omega
  have h02 : G.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) := m2_right_4 hR r (by omega) hnot03
  have hnot05 : ¬ G.Adj (v ⟨0, by decide⟩) (v ⟨5, by decide⟩) := fun h => nP6 h02 h
  have h13 : G.Adj (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) := m2_left_4 hL r (by omega) hnot03
  have hnot14 : ¬ G.Adj (v ⟨1, by decide⟩) (v ⟨4, by decide⟩) := fun h => nP2 h13 h
  have hnot15 : ¬ G.Adj (v ⟨1, by decide⟩) (v ⟨5, by decide⟩) := fun h => nP7 h13 h
  have h25 : G.Adj (v ⟨2, by decide⟩) (v ⟨5, by decide⟩) := by
    by_contra hnot25
    have hge3 := m2_left_6_ge3 hL r hr
    have hsub : Finset.univ.filter (fun k : Fin 5 =>
        G.Adj (σ ⟨r + k.val, by omega⟩) (σ ⟨r + 5, hr⟩)) ⊆ {⟨3, by decide⟩, ⟨4, by decide⟩} := by
      intro k hk
      have hadj := (Finset.mem_filter.mp hk).2
      fin_cases k
      · exfalso; exact hnot05 hadj
      · exfalso; exact hnot15 hadj
      · exfalso; exact hnot25 hadj
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hle := (Finset.card_le_card hsub).trans (Finset.card_le_two)
    omega
  have hnot24 : ¬ G.Adj (v ⟨2, by decide⟩) (v ⟨4, by decide⟩) := fun h => nP3 h h25
  have h24 : G.Adj (v ⟨2, by decide⟩) (v ⟨4, by decide⟩) := by
    have hnot14' : ¬ G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 1 + 3, by omega⟩) := by
      dsimp only [v] at hnot14; convert hnot14 using 2
    have h := m2_left_4 hL (r + 1) (by omega) hnot14'
    dsimp only [v]; convert h using 2
  exact hnot24 h24

lemma lmo6_F2 {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] (hG : G.IsTournament)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (r : ℕ) (hr : r + 5 < Fintype.card V) :
    let v : Fin 6 → V := fun k => σ ⟨r + k.val, by omega⟩
    (G.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) ∧ G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩)) ∨
    (G.Adj (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) ∧ G.Adj (v ⟨1, by decide⟩) (v ⟨4, by decide⟩)) ∨
    (G.Adj (v ⟨2, by decide⟩) (v ⟨4, by decide⟩) ∧ G.Adj (v ⟨2, by decide⟩) (v ⟨5, by decide⟩)) ∨
    (G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) ∧ G.Adj (v ⟨0, by decide⟩) (v ⟨4, by decide⟩)) ∨
    (G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) ∧ G.Adj (v ⟨0, by decide⟩) (v ⟨5, by decide⟩)) ∨
    (G.Adj (v ⟨3, by decide⟩) (v ⟨5, by decide⟩) ∧ G.Adj (v ⟨3, by decide⟩) (v ⟨0, by decide⟩) ∧
     G.Adj (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) ∧ G.Adj (v ⟨2, by decide⟩) (v ⟨4, by decide⟩)) := by
  classical
  intro v
  by_contra hall
  push Not at hall
  obtain ⟨nP1, nP2, nP3, nP4, nP5, nP6'⟩ := hall
  have hnot03 : ¬ G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) := by
    intro h03
    have hnot02 : ¬ G.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) := fun h => nP1 h h03
    have hnot04 : ¬ G.Adj (v ⟨0, by decide⟩) (v ⟨4, by decide⟩) := fun h => nP4 h03 h
    have hnot05 : ¬ G.Adj (v ⟨0, by decide⟩) (v ⟨5, by decide⟩) := fun h => nP5 h03 h
    have hge3 := m2_right_6_ge3 hR r hr
    have hsub : Finset.univ.filter (fun k : Fin 5 =>
        G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1 + k.val, by omega⟩)) ⊆ {⟨0, by decide⟩, ⟨2, by decide⟩} := by
      intro k hk
      have hadj := (Finset.mem_filter.mp hk).2
      fin_cases k
      · exact Finset.mem_insert_self _ _
      · exfalso; exact hnot02 hadj
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exfalso; exact hnot04 hadj
      · exfalso; exact hnot05 hadj
    have hle := (Finset.card_le_card hsub).trans (Finset.card_le_two)
    omega
  have h30 : G.Adj (v ⟨3, by decide⟩) (v ⟨0, by decide⟩) :=
    (adj_or_rev_of_isTournament hG (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only at this; omega)).resolve_left hnot03
  have h13 : G.Adj (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) := m2_left_4 hL r (by omega) hnot03
  have hnot14 : ¬ G.Adj (v ⟨1, by decide⟩) (v ⟨4, by decide⟩) := fun h => nP2 h13 h
  have h24 : G.Adj (v ⟨2, by decide⟩) (v ⟨4, by decide⟩) := by
    have hnot14' : ¬ G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 1 + 3, by omega⟩) := by
      dsimp only [v] at hnot14; convert hnot14 using 2
    have h := m2_left_4 hL (r + 1) (by omega) hnot14'
    dsimp only [v]; convert h using 2
  have hnot25 : ¬ G.Adj (v ⟨2, by decide⟩) (v ⟨5, by decide⟩) := fun h => nP3 h24 h
  have h35 : G.Adj (v ⟨3, by decide⟩) (v ⟨5, by decide⟩) := by
    have hnot25' : ¬ G.Adj (σ ⟨r + 2, by omega⟩) (σ ⟨r + 2 + 3, by omega⟩) := by
      dsimp only [v] at hnot25; convert hnot25 using 2
    have h := m2_left_4 hL (r + 2) (by omega) hnot25'
    dsimp only [v]; convert h using 2
  exact nP6' h35 h30 h13 h24

lemma lmo6_F3 {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] (hG : G.IsTournament)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (r : ℕ) (hr : r + 5 < Fintype.card V) :
    let v : Fin 6 → V := fun k => σ ⟨r + k.val, by omega⟩
    (G.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) ∧ G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩)) ∨
    (G.Adj (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) ∧ G.Adj (v ⟨1, by decide⟩) (v ⟨4, by decide⟩)) ∨
    (G.Adj (v ⟨2, by decide⟩) (v ⟨4, by decide⟩) ∧ G.Adj (v ⟨2, by decide⟩) (v ⟨5, by decide⟩)) ∨
    (G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) ∧ G.Adj (v ⟨0, by decide⟩) (v ⟨4, by decide⟩)) ∨
    (G.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) ∧ G.Adj (v ⟨0, by decide⟩) (v ⟨4, by decide⟩)) ∨
    (G.Adj (v ⟨3, by decide⟩) (v ⟨5, by decide⟩) ∧ G.Adj (v ⟨3, by decide⟩) (v ⟨1, by decide⟩)) ∨
    (G.Adj (v ⟨2, by decide⟩) (v ⟨0, by decide⟩) ∧ G.Adj (v ⟨2, by decide⟩) (v ⟨5, by decide⟩)) ∨
    (G.Adj (v ⟨4, by decide⟩) (v ⟨1, by decide⟩) ∧ G.Adj (v ⟨4, by decide⟩) (v ⟨0, by decide⟩) ∧
     G.Adj (v ⟨3, by decide⟩) (v ⟨5, by decide⟩)) := by
  classical
  intro v
  by_contra hall
  push Not at hall
  obtain ⟨nP1, nP2, nP3, nP4, nQ5, nQ6, nQ8, nQ9⟩ := hall
  have hne : ∀ a b : Fin 6, a ≠ b → v a ≠ v b := fun a b hab h =>
    hab (Fin.ext (by have := congrArg Fin.val (σ.injective h); dsimp only [v] at this; omega))
  by_cases h03 : G.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩)
  · have h20 : G.Adj (v ⟨2, by decide⟩) (v ⟨0, by decide⟩) :=
      (adj_or_rev_of_isTournament hG (hne ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide))).resolve_left (fun h => nP1 h h03)
    have h40 : G.Adj (v ⟨4, by decide⟩) (v ⟨0, by decide⟩) :=
      (adj_or_rev_of_isTournament hG (hne ⟨0, by decide⟩ ⟨4, by decide⟩ (by decide))).resolve_left (fun h => nP4 h03 h)
    have hnot25 : ¬ G.Adj (v ⟨2, by decide⟩) (v ⟨5, by decide⟩) := fun h => nQ8 h20 h
    have h35 : G.Adj (v ⟨3, by decide⟩) (v ⟨5, by decide⟩) := by
      have hnot25' : ¬ G.Adj (σ ⟨r + 2, by omega⟩) (σ ⟨r + 2 + 3, by omega⟩) := by
        dsimp only [v] at hnot25; convert hnot25 using 2
      have h := m2_left_4 hL (r + 2) (by omega) hnot25'
      dsimp only [v]; convert h using 2
    have h13 : G.Adj (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) :=
      (adj_or_rev_of_isTournament hG (hne ⟨3, by decide⟩ ⟨1, by decide⟩ (by decide))).resolve_left (fun h => nQ6 h35 h)
    have h41 : G.Adj (v ⟨4, by decide⟩) (v ⟨1, by decide⟩) :=
      (adj_or_rev_of_isTournament hG (hne ⟨1, by decide⟩ ⟨4, by decide⟩ (by decide))).resolve_left (fun h => nP2 h13 h)
    exact nQ9 h41 h40 h35
  · have h02 : G.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) := m2_right_4 hR r (by omega) h03
    have h40 : G.Adj (v ⟨4, by decide⟩) (v ⟨0, by decide⟩) :=
      (adj_or_rev_of_isTournament hG (hne ⟨0, by decide⟩ ⟨4, by decide⟩ (by decide))).resolve_left (fun h => nQ5 h02 h)
    have h13 : G.Adj (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) := m2_left_4 hL r (by omega) h03
    have hnot14 : ¬ G.Adj (v ⟨1, by decide⟩) (v ⟨4, by decide⟩) := fun h => nP2 h13 h
    have h41 : G.Adj (v ⟨4, by decide⟩) (v ⟨1, by decide⟩) :=
      (adj_or_rev_of_isTournament hG (hne ⟨1, by decide⟩ ⟨4, by decide⟩ (by decide))).resolve_left hnot14
    have h24 : G.Adj (v ⟨2, by decide⟩) (v ⟨4, by decide⟩) := by
      have hnot14' : ¬ G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 1 + 3, by omega⟩) := by
        dsimp only [v] at hnot14; convert hnot14 using 2
      have h := m2_left_4 hL (r + 1) (by omega) hnot14'
      dsimp only [v]; convert h using 2
    have hnot25 : ¬ G.Adj (v ⟨2, by decide⟩) (v ⟨5, by decide⟩) := fun h => nP3 h24 h
    have h35 : G.Adj (v ⟨3, by decide⟩) (v ⟨5, by decide⟩) := by
      have hnot25' : ¬ G.Adj (σ ⟨r + 2, by omega⟩) (σ ⟨r + 2 + 3, by omega⟩) := by
        dsimp only [v] at hnot25; convert hnot25 using 2
      have h := m2_left_4 hL (r + 2) (by omega) hnot25'
      dsimp only [v]; convert h using 2
    exact nQ9 h41 h40 h35

-- Minimality helpers: missing mandatory attachment yields a Heart of size 3!
lemma heart_four_drop_leaf_to_B
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (i0 j0 a b c : Fin 4)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ i0 ≠ a ∧ i0 ≠ b ∧ i0 ≠ c)
    (hH3_top : (D.Adj (u a) (u b) ∧ D.Adj (u b) (u c)) ∨
      (D.Adj (u a) (u b) ∧ D.Adj (u a) (u c)) ∨
      (D.Adj (u b) (u a) ∧ D.Adj (u c) (u a)))
    (hi0_adj : D.Adj (u i0) (u j0))
    (hi0_uniq : ∀ j : Fin 4, D.Adj (u i0) (u j) → j = j0)
    (hnoA : ∀ x ∈ A, ¬ D.Adj (u i0) x) :
    ∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
      ((D.Adj u1 u2 ∧ D.Adj u2 u3) ∨ (D.Adj u1 u2 ∧ D.Adj u1 u3) ∨ (D.Adj u2 u1 ∧ D.Adj u3 u1)) ∧
      ∃ A' : Finset W, u1 ∉ A' ∧ u2 ∉ A' ∧ u3 ∉ A' ∧
        (∀ x ∈ A', (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
        (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' →
          (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
        (∀ x ∈ A', ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → ¬ D.Adj x y ∧ ¬ D.Adj y x) := by
  classical
  have hcov4 : ∀ k : Fin 4, k = a ∨ k = b ∨ k = c ∨ k = i0 := by
    have h4 : ({a, b, c, i0} : Finset (Fin 4)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hdist.1, hdist.2.1, hdist.2.2.2.1.symm]),
        Finset.card_insert_of_notMem (by simp [hdist.2.2.1, hdist.2.2.2.2.1.symm]),
        Finset.card_insert_of_notMem (by simp [hdist.2.2.2.2.2.symm]), Finset.card_singleton]
    have heq := Finset.eq_univ_of_card ({a, b, c, i0} : Finset (Fin 4)) (by rw [h4, Fintype.card_fin])
    intro k; have hk : k ∈ ({a, b, c, i0} : Finset (Fin 4)) := by rw [heq]; exact Finset.mem_univ k
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk; exact hk
  refine ⟨u a, u b, u c, fun h => hdist.1 (hu_inj h), fun h => hdist.2.1 (hu_inj h),
    fun h => hdist.2.2.1 (hu_inj h), hH3_top, A, hHA_disj a, hHA_disj b, hHA_disj c, hA_in, ?_, ?_⟩
  · intro y hya hyb hyc hyA
    by_cases hy0 : y = u i0
    · subst hy0
      have heq : Finset.univ.filter (fun z : W => D.Adj (u i0) z) = {u j0} := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hDz
          by_cases hzH : z ∈ Finset.univ.image u
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hzH; rw [hi0_uniq j hDz]
          · by_cases hzA : z ∈ A
            · exact absurd hDz (hnoA z hzA)
            · exact absurd hDz (hno_HB i0 z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hzA⟩))
        · rintro rfl; exact hi0_adj
      rw [heq, Finset.card_singleton]
    · exact hB_out y (fun k => by rcases hcov4 k with rfl | rfl | rfl | rfl <;> assumption) hyA
  · intro x hxA y hya hyb hyc hyA
    by_cases hy0 : y = u i0
    · subst hy0; exact ⟨hno_AH x hxA i0, hnoA x hxA⟩
    · exact hno_AB x hxA y (fun k => by rcases hcov4 k with rfl | rfl | rfl | rfl <;> assumption) hyA

lemma heart_four_drop_leaf_to_A
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (i0 j0 a b c : Fin 4)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ i0 ≠ a ∧ i0 ≠ b ∧ i0 ≠ c)
    (hH3_top : (D.Adj (u a) (u b) ∧ D.Adj (u b) (u c)) ∨
      (D.Adj (u a) (u b) ∧ D.Adj (u a) (u c)) ∨
      (D.Adj (u b) (u a) ∧ D.Adj (u c) (u a)))
    (hi0_adj : D.Adj (u j0) (u i0))
    (hi0_uniq : ∀ j : Fin 4, D.Adj (u j) (u i0) → j = j0)
    (hnoB : ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i0)) :
    ∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
      ((D.Adj u1 u2 ∧ D.Adj u2 u3) ∨ (D.Adj u1 u2 ∧ D.Adj u1 u3) ∨ (D.Adj u2 u1 ∧ D.Adj u3 u1)) ∧
      ∃ A' : Finset W, u1 ∉ A' ∧ u2 ∉ A' ∧ u3 ∉ A' ∧
        (∀ x ∈ A', (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
        (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' →
          (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
        (∀ x ∈ A', ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → ¬ D.Adj x y ∧ ¬ D.Adj y x) := by
  classical
  have hcov4 : ∀ k : Fin 4, k = a ∨ k = b ∨ k = c ∨ k = i0 := by
    have h4 : ({a, b, c, i0} : Finset (Fin 4)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hdist.1, hdist.2.1, hdist.2.2.2.1.symm]),
        Finset.card_insert_of_notMem (by simp [hdist.2.2.1, hdist.2.2.2.2.1.symm]),
        Finset.card_insert_of_notMem (by simp [hdist.2.2.2.2.2.symm]), Finset.card_singleton]
    have heq := Finset.eq_univ_of_card ({a, b, c, i0} : Finset (Fin 4)) (by rw [h4, Fintype.card_fin])
    intro k; have hk : k ∈ ({a, b, c, i0} : Finset (Fin 4)) := by rw [heq]; exact Finset.mem_univ k
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk; exact hk
  let A' := insert (u i0) A
  refine ⟨u a, u b, u c, fun h => hdist.1 (hu_inj h), fun h => hdist.2.1 (hu_inj h),
    fun h => hdist.2.2.1 (hu_inj h), hH3_top, A',
    fun h => (Finset.mem_insert.mp h).elim (fun e => hdist.2.2.2.1 (hu_inj e).symm) (hHA_disj a),
    fun h => (Finset.mem_insert.mp h).elim (fun e => hdist.2.2.2.2.1 (hu_inj e).symm) (hHA_disj b),
    fun h => (Finset.mem_insert.mp h).elim (fun e => hdist.2.2.2.2.2 (hu_inj e).symm) (hHA_disj c),
    ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxA
    · have heq : Finset.univ.filter (fun z : W => D.Adj z (u i0)) = {u j0} := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hDz
          by_cases hzH : z ∈ Finset.univ.image u
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hzH; rw [hi0_uniq j hDz]
          · by_cases hzA : z ∈ A
            · exact absurd hDz (hno_AH z hzA i0)
            · exact absurd hDz (hnoB z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hzA⟩))
        · rintro rfl; exact hi0_adj
      rw [heq, Finset.card_singleton]
    · exact hA_in x hxA
  · intro y hya hyb hyc hyA'
    have hy0 : y ≠ u i0 := fun h => hyA' (Finset.mem_insert.mpr (Or.inl h))
    have hyA : y ∉ A := fun h => hyA' (Finset.mem_insert.mpr (Or.inr h))
    exact hB_out y (fun k => by rcases hcov4 k with rfl | rfl | rfl | rfl <;> assumption) hyA
  · intro x hxA' y hya hyb hyc hyA'
    have hy0 : y ≠ u i0 := fun h => hyA' (Finset.mem_insert.mpr (Or.inl h))
    have hyA : y ∉ A := fun h => hyA' (Finset.mem_insert.mpr (Or.inr h))
    have hyB : y ∈ Finset.univ \ (Finset.univ.image u ∪ A) :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim
        (fun hH => by obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hH; rcases hcov4 k with rfl | rfl | rfl | rfl <;> exact absurd hk.symm (by assumption)) hyA⟩
    rcases Finset.mem_insert.mp hxA' with rfl | hxA
    · exact ⟨hno_HB i0 y hyB, hnoB y hyB⟩
    · exact hno_AB x hxA y (fun k => by rcases hcov4 k with rfl | rfl | rfl | rfl <;> assumption) hyA

lemma hasHeart3_rev {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (h : ∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
      ((D.Adj u2 u1 ∧ D.Adj u3 u2) ∨ (D.Adj u2 u1 ∧ D.Adj u3 u1) ∨ (D.Adj u1 u2 ∧ D.Adj u1 u3)) ∧
      ∃ A : Finset W, u1 ∉ A ∧ u2 ∉ A ∧ u3 ∉ A ∧
        (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj x z)).card = 1) ∧
        (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
          (Finset.univ.filter (fun z : W => D.Adj z y)).card = 1) ∧
        (∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A → ¬ D.Adj y x ∧ ¬ D.Adj x y)) :
    ∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
      ((D.Adj u1 u2 ∧ D.Adj u2 u3) ∨ (D.Adj u1 u2 ∧ D.Adj u1 u3) ∨ (D.Adj u2 u1 ∧ D.Adj u3 u1)) ∧
      ∃ A : Finset W, u1 ∉ A ∧ u2 ∉ A ∧ u3 ∉ A ∧
        (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
        (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
          (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
        (∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x) := by
  classical
  obtain ⟨u1, u2, u3, h12, h13, h23, htop, A, hu1A, hu2A, hu3A, hA_out, hB_in, hno_AB⟩ := h
  let B : Finset W := Finset.univ \ ({u1, u2, u3} ∪ A)
  have hB_mem : ∀ y : W, y ∈ B ↔ y ≠ u1 ∧ y ≠ u2 ∧ y ≠ u3 ∧ y ∉ A := by
    intro y; simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩
  have hswap : ∀ (v1 v2 v3 : W), (∀ w, (w = v1 ∨ w = v2 ∨ w = v3) ↔ (w = u1 ∨ w = u2 ∨ w = u3)) →
      v1 ≠ v2 → v1 ≠ v3 → v2 ≠ v3 →
      ((D.Adj v1 v2 ∧ D.Adj v2 v3) ∨ (D.Adj v1 v2 ∧ D.Adj v1 v3) ∨ (D.Adj v2 v1 ∧ D.Adj v3 v1)) →
      ∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
        ((D.Adj u1 u2 ∧ D.Adj u2 u3) ∨ (D.Adj u1 u2 ∧ D.Adj u1 u3) ∨ (D.Adj u2 u1 ∧ D.Adj u3 u1)) ∧
        ∃ A' : Finset W, u1 ∉ A' ∧ u2 ∉ A' ∧ u3 ∉ A' ∧
          (∀ x ∈ A', (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
          (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' →
            (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
          (∀ x ∈ A', ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → ¬ D.Adj x y ∧ ¬ D.Adj y x) := by
    intro v1 v2 v3 hset hv12 hv13 hv23 hvtop
    have hmem : ∀ w, (w ≠ v1 ∧ w ≠ v2 ∧ w ≠ v3) ↔ (w ≠ u1 ∧ w ≠ u2 ∧ w ≠ u3) := by
      intro w; constructor
      · intro ⟨h1, h2, h3⟩
        refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
        · rcases (hset w).mpr (Or.inl e) with r | r | r <;> [exact h1 r; exact h2 r; exact h3 r]
        · rcases (hset w).mpr (Or.inr (Or.inl e)) with r | r | r <;> [exact h1 r; exact h2 r; exact h3 r]
        · rcases (hset w).mpr (Or.inr (Or.inr e)) with r | r | r <;> [exact h1 r; exact h2 r; exact h3 r]
      · intro ⟨h1, h2, h3⟩
        refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
        · rcases (hset w).mp (Or.inl e) with r | r | r <;> [exact h1 r; exact h2 r; exact h3 r]
        · rcases (hset w).mp (Or.inr (Or.inl e)) with r | r | r <;> [exact h1 r; exact h2 r; exact h3 r]
        · rcases (hset w).mp (Or.inr (Or.inr e)) with r | r | r <;> [exact h1 r; exact h2 r; exact h3 r]
    refine ⟨v1, v2, v3, hv12, hv13, hv23, hvtop, B,
      fun h => by have := (hB_mem v1).mp h; have := (hmem v1).mpr ⟨this.1, this.2.1, this.2.2.1⟩; exact this.1 rfl,
      fun h => by have := (hB_mem v2).mp h; have := (hmem v2).mpr ⟨this.1, this.2.1, this.2.2.1⟩; exact this.2.1 rfl,
      fun h => by have := (hB_mem v3).mp h; have := (hmem v3).mpr ⟨this.1, this.2.1, this.2.2.1⟩; exact this.2.2 rfl,
      fun x hxB => by obtain ⟨h1, h2, h3, hA⟩ := (hB_mem x).mp hxB; exact hB_in x h1 h2 h3 hA,
      fun y hy1 hy2 hy3 hyB => by
        obtain ⟨u1', u2', u3'⟩ := (hmem y).mp ⟨hy1, hy2, hy3⟩
        have hyA : y ∈ A := by by_contra hnot; exact hyB ((hB_mem y).mpr ⟨u1', u2', u3', hnot⟩)
        exact hA_out y hyA,
      fun x hxB y hy1 hy2 hy3 hyB => by
        obtain ⟨h1, h2, h3, hA⟩ := (hB_mem x).mp hxB
        obtain ⟨u1', u2', u3'⟩ := (hmem y).mp ⟨hy1, hy2, hy3⟩
        have hyA : y ∈ A := by by_contra hnot; exact hyB ((hB_mem y).mpr ⟨u1', u2', u3', hnot⟩)
        exact hno_AB y hyA x h1 h2 h3 hA⟩
  rcases htop with ⟨h21, h32⟩ | hS3m | hS3p
  · exact hswap u3 u2 u1 (fun w => ⟨fun h => by rcases h with rfl | rfl | rfl; exact Or.inr (Or.inr rfl); exact Or.inr (Or.inl rfl); exact Or.inl rfl,
      fun h => by rcases h with rfl | rfl | rfl; exact Or.inr (Or.inr rfl); exact Or.inr (Or.inl rfl); exact Or.inl rfl⟩)
      h23.symm h13.symm h12.symm (Or.inl ⟨h32, h21⟩)
  · exact hswap u1 u2 u3 (fun _ => Iff.rfl) h12 h13 h23 (Or.inr (Or.inr hS3m))
  · exact hswap u1 u2 u3 (fun _ => Iff.rfl) h12 h13 h23 (Or.inr (Or.inl hS3p))

-- Zero-cut, zero-dummy L = 4 wrapper around embeds_heart_four_of_pure_plan
lemma embeds_pure_4
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hRkP : ∃ rkP : ↥(Finset.univ.image u ∪ A) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y)
    (hRkM : ∃ rkM : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))),
        x.1 ∈ Finset.univ \ (Finset.univ.image u ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (lo : ℕ) (hhi : lo + 3 < 2 * n - 2)
    (pos : Fin 4 → Fin 4) (hpos_inj : Function.Injective pos)
    (hpos_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) →
      G.Adj (σ ⟨lo + (pos i).val, by omega⟩) (σ ⟨lo + (pos j).val, by omega⟩))
    (qR : ℕ) (hqR_le : qR ≤ 4)
    (hqR_pref : ∀ t : Fin 4, t.val < qR → ∀ i : Fin 4, pos i = t → ∀ x ∈ A, ¬ D.Adj (u i) x)
    (hR_bnd : 4 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
      (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ (2 * n - 2 - lo) + 1 + qR)
    (qL : ℕ) (hqL_le : qL ≤ 4)
    (hqL_pref : ∀ t : Fin 4, 3 - t.val < qL → ∀ i : Fin 4, pos i = t →
      ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))
    (hL_bnd : 4 + (Finset.univ \ (Finset.univ.image u ∪ A)).card +
      ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card +
      (Finset.univ.filter (fun i : Fin 4 =>
        ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ (lo + 4) + 1 + qL) :
    Embeds D G := by
  classical
  have hpos_surj : Function.Surjective pos := Finite.surjective_of_injective hpos_inj
  let pos' : Fin 4 → Fin (lo + 3 - lo + 1) := fun i => ⟨(pos i).val, by omega⟩
  have hpos'_inj : Function.Injective pos' := fun i j h => hpos_inj (Fin.ext (congrArg (fun x : Fin (lo + 3 - lo + 1) => x.val) h))
  have hno_free : ∀ t : Fin (lo + 3 - lo + 1), ¬ (∀ i : Fin 4, pos' i ≠ t) := by
    intro t ht
    obtain ⟨i, hi⟩ := hpos_surj ⟨t.val, by omega⟩
    exact ht i (Fin.ext (by dsimp only [pos']; rw [hi]))
  have hdum0 : (Finset.univ.filter (fun t : Fin (lo + 3 - lo + 1) =>
      (∀ i, pos' i ≠ t) ∧ (fun _ : Fin (lo + 3 - lo + 1) => (none : Option (Fin 4))) t = none)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ h; exact hno_free t h.1
  refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
    hV hR hL lo (lo + 3) (by omega) hhi pos' hpos'_inj hpos_adj (fun _ => none) (fun _ => none)
    (fun _ _ => Or.inl rfl)
    (fun t1 _ ht1 _ _ _ => absurd ht1 (hno_free t1))
    (fun t ht _ _ => absurd ht (hno_free t))
    (fun t1 _ ht1 _ _ _ => absurd ht1 (hno_free t1))
    (fun t ht _ _ => absurd ht (hno_free t))
    ?_ ?_
  · intro exhR hexh
    have he0 : exhR.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi; obtain ⟨t, ht, _⟩ := hexh i hi; exact hno_free t ht
    refine ⟨qR, by omega, fun t ht => ⟨fun i hi => Or.inl (hqR_pref ⟨t.val, by omega⟩ ht i
      (Fin.ext (congrArg (fun x : Fin (lo + 3 - lo + 1) => x.val) hi))), fun _ => rfl⟩, ?_⟩
    rw [hdum0, he0]; omega
  · intro exhL hexh
    have he0 : exhL.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi; obtain ⟨t, ht, _⟩ := hexh i hi; exact hno_free t ht
    refine ⟨qL, by omega, fun t ht => ⟨fun i hi => Or.inl (hqL_pref ⟨t.val, by omega⟩ (by dsimp only; omega) i
      (Fin.ext (congrArg (fun x : Fin (lo + 3 - lo + 1) => x.val) hi))), fun _ => rfl⟩, ?_⟩
    rw [hdum0, he0]; omega

-- Helper: filter cardinality sum for maskP / maskM complements on Fin 4
lemma card_mask_compl_fin4 (P : Fin 4 → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card + (Finset.univ.filter (fun i : Fin 4 => ¬ P i)).card = 4 := by
  have h := card_filter_add_card_filter_not_eq (Finset.univ : Finset (Fin 4)) P
  rwa [Finset.card_univ, Fintype.card_fin] at h

lemma forall_of_filter_card_eq {α : Type*} [DecidableEq α] {S : Finset α} {P : α → Prop} [DecidablePred P]
    (h : (S.filter P).card = S.card) : ∀ x ∈ S, P x := by
  have heq : S.filter P = S := Finset.eq_of_subset_of_card_le (Finset.filter_subset P S) (by omega)
  intro x hx; exact (Finset.mem_filter.mp (heq ▸ hx)).2

lemma sigma_adj_congr {V : Type*} [Fintype V] {G : Digraph V} {σ : Fin (Fintype.card V) ≃ V}
    {a b a' b' : ℕ} {ha : a < Fintype.card V} {hb : b < Fintype.card V}
    {ha' : a' < Fintype.card V} {hb' : b' < Fintype.card V}
    (h : G.Adj (σ ⟨a, ha⟩) (σ ⟨b, hb⟩)) (ea : a = a') (eb : b = b') :
    G.Adj (σ ⟨a', ha'⟩) (σ ⟨b', hb'⟩) := by
  subst ea; subst eb; exact h

lemma card_mask_rev4_le {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hlt : ¬ (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card ≤
      (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u i))).card) :
    (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ Finset.univ \ (Finset.univ.image u ∪ A),
      D.Adj x (u ⟨3 - i.val, by omega⟩))).card ≤
    (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ Finset.univ \ (Finset.univ.image (fun i : Fin 4 => u ⟨3 - i.val, by omega⟩) ∪
      (Finset.univ \ (Finset.univ.image u ∪ A))), D.Adj (u ⟨3 - i.val, by omega⟩) y)).card := by
  classical
  let rev4 : Fin 4 → Fin 4 := fun i => ⟨3 - i.val, by omega⟩
  have hrev_inv : ∀ i : Fin 4, rev4 (rev4 i) = i := fun i => Fin.ext (by dsimp only [rev4]; omega)
  have hrev_inj : Function.Injective rev4 := fun i j h => by rw [← hrev_inv i, ← hrev_inv j, h]
  have hH_eq : Finset.univ.image (fun i : Fin 4 => u (rev4 i)) = Finset.univ.image u := by
    ext w; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨rev4 i, hi⟩, fun ⟨i, hi⟩ => ⟨rev4 i, by rw [hrev_inv]; exact hi⟩⟩
  have hA_eq : Finset.univ \ (Finset.univ.image (fun i : Fin 4 => u (rev4 i)) ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) = A := by
    rw [hH_eq]; ext w; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hwH : w ∈ Finset.univ.image u
    · exact ⟨fun h => absurd (Or.inl hwH) h, fun hwA => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwH; exact absurd hwA (hHA_disj i)⟩
    · tauto
  have hcard_rev4 : ∀ (P : Fin 4 → Prop) [DecidablePred P] [DecidablePred (fun i => P (rev4 i))],
      (Finset.univ.filter (fun i : Fin 4 => P (rev4 i))).card = (Finset.univ.filter P).card := by
    intro P _ _
    refine Finset.card_bij (fun i _ => rev4 i) ?_ (fun i _ j _ h => hrev_inj h) ?_
    · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi
    · intro i hi; refine ⟨rev4 i, ?_, hrev_inv i⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; rwa [hrev_inv]
  have h1 : (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ Finset.univ \ (Finset.univ.image u ∪ A),
      D.Adj x (u ⟨3 - i.val, by omega⟩))).card =
      (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u i))).card := by
    convert hcard_rev4 (fun i : Fin 4 => ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u i))
  have h2 : (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ Finset.univ \ (Finset.univ.image (fun i : Fin 4 => u ⟨3 - i.val, by omega⟩) ∪
      (Finset.univ \ (Finset.univ.image u ∪ A))), D.Adj (u ⟨3 - i.val, by omega⟩) y)).card =
      (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card := by
    have hA_eq' : Finset.univ \ (Finset.univ.image (fun i : Fin 4 => u ⟨3 - i.val, by omega⟩) ∪
        (Finset.univ \ (Finset.univ.image u ∪ A))) = A := hA_eq
    rw [hA_eq']
    convert hcard_rev4 (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)
  have hlt' : ¬ (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card ≤
      (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u i))).card := by
    convert hlt
  omega

-- Helper: Claim D reversal wrapper for P4+++ Case 4 (n - k = 5, A = kA + 1, B = kB)
lemma embeds_of_claim_D_rev
    {n : ℕ} (hn6 : 6 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i.val + 1 = j.val)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hcard_id : 4 + A.card + (Finset.univ \ (Finset.univ.image u ∪ A)).card = n)
    (hB_leaf : ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ∀ z : W, ¬ D.Adj z y)
    (hA_one : A.card = (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card + 1)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hmaskP0 : ∀ i : Fin 4, i ≠ ⟨0, by decide⟩ → ∀ x ∈ A, ¬ D.Adj (u i) x)
    (hmaskM3 : ∀ i : Fin 4, i ≠ ⟨3, by decide⟩ →
      ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))
    (hloopless : ∀ w : W, ¬ D.Adj w w)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v) (hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u) :
    Embeds D G := by
  classical
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let Drev : Digraph W := ⟨fun x y => D.Adj y x⟩
  let Grev : Digraph V := ⟨fun x y => G.Adj y x⟩
  let u' : Fin 4 → W := fun i => u ⟨3 - i.val, by omega⟩
  have hu'_inj : Function.Injective u' := fun i j h => Fin.ext (by have := congrArg Fin.val (hu_inj h); dsimp only at this; omega)
  have hH'_eq : Finset.univ.image u' = H := by
    ext w; simp only [H, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨⟨3 - i.val, by omega⟩, hi⟩, fun ⟨i, hi⟩ => ⟨⟨3 - i.val, by omega⟩, by convert hi using 2; apply Fin.ext; dsimp only; omega⟩⟩
  have hA_eq_sdiff : Finset.univ \ (Finset.univ.image u' ∪ B) = A := by
    rw [hH'_eq]; ext w; simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hwH : w ∈ H
    · exact ⟨fun h => absurd (Or.inl hwH) h, fun hwA => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwH; exact absurd hwA (hHA_disj i)⟩
    · tauto
  have hnotB_to_A : ∀ y : W, (∀ i : Fin 4, y ≠ u' i) → y ∉ B → y ∈ A := by
    intro y hyu hyB; by_contra hnotA
    exact hyB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim
      (fun hH => by obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hH; exact hyu ⟨3 - i.val, by omega⟩ (by dsimp only [u']; convert hi.symm using 2; apply Fin.ext; dsimp only; omega)) hnotA⟩)
  refine embeds_rev (embeds_of_claim_D (D := Drev) (G := Grev) hn6 u' hu'_inj ?_ B ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hloopless hV ⟨fun v => hG.1 v, fun x y hne => hG.2 y x hne.symm⟩ hNoSnk hNoSrc)
  · intro i j hD; have := hH_only ⟨3 - j.val, by omega⟩ ⟨3 - i.val, by omega⟩ hD; simp only at this; omega
  · intro i hi; exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨3 - i.val, by omega⟩, Finset.mem_univ _, rfl⟩))
  · rw [hA_eq_sdiff]; dsimp only [B, H]; omega
  · intro y hyB z; exact hB_leaf y hyB z
  · rw [hA_eq_sdiff]; exact hA_one
  · intro x hxB; have hnot := (Finset.mem_sdiff.mp hxB).2
    exact hB_out x (fun i hi => hnot (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
      (fun h => hnot (Finset.mem_union_right _ h))
  · intro y hyu hyB; exact hA_in y (hnotB_to_A y hyu hyB)
  · intro x hxB y hyu hyB
    have hnot := (Finset.mem_sdiff.mp hxB).2
    exact hno_AB y (hnotB_to_A y hyu hyB) x
      (fun i hi => hnot (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
      (fun h => hnot (Finset.mem_union_right _ h))
  · intro i y hyA; rw [hA_eq_sdiff] at hyA; exact hno_AH y hyA ⟨3 - i.val, by omega⟩
  · intro i hi y hyB; exact hmaskM3 ⟨3 - i.val, by omega⟩ (fun h => hi (Fin.ext (by have := congrArg Fin.val h; simp only at this ⊢; omega))) y hyB
  · intro i hi y hyA; rw [hA_eq_sdiff] at hyA
    exact hmaskP0 ⟨3 - i.val, by omega⟩ (fun h => hi (Fin.ext (by have := congrArg Fin.val h; simp only at this ⊢; omega))) y hyA

-- ============================================================================
-- TOPOLOGY 1: P4+++ (u0 -> u1 -> u2 -> u3; mandP = {0}, mandM = {3})
-- ============================================================================

lemma embeds_heart_four_P4ppp_le
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (h01 : D.Adj (u ⟨0, by decide⟩) (u ⟨1, by decide⟩))
    (h12 : D.Adj (u ⟨1, by decide⟩) (u ⟨2, by decide⟩))
    (h23 : D.Adj (u ⟨2, by decide⟩) (u ⟨3, by decide⟩))
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i.val + 1 = j.val)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hMandP0 : ∃ x ∈ A, D.Adj (u ⟨0, by decide⟩) x)
    (hMandM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    (hMaskLe : (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card ≤
      (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u i))).card)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v) (hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u) :
    Embeds D G := by
  classical
  have hH_parent : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (u j) (u i) := by
    intro i hi; fin_cases i
    · exact absurd rfl hi
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h01⟩
    · exact ⟨⟨1, by decide⟩, by decide, hO.1 _ _ h12⟩
    · exact ⟨⟨2, by decide⟩, by decide, hO.1 _ _ h23⟩
  obtain ⟨hno_AH, hno_HB, hRkP, hRkM, _, h2mP, h2mM, hcard_id⟩ :=
    heart_four_structure D hT hO u hu_inj hH_parent A hHA_disj hA_in hB_out hno_AB
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let kA := (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card
  let kB := (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
  let mP := (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card
  let mM := (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card
  let ZP := (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card
  let ZM := (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card
  have hZP_eq : mP + ZP = 4 := by
    have h := card_mask_compl_fin4 (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)
    have heq : Finset.univ.filter (fun i : Fin 4 => ¬ ∃ x ∈ A, D.Adj (u i) x) =
        Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    rw [heq] at h; exact h
  have hZM_eq : mM + ZM = 4 := by
    have h := card_mask_compl_fin4 (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))
    have heq : Finset.univ.filter (fun i : Fin 4 => ¬ ∃ y ∈ B, D.Adj y (u i)) =
        Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    rw [heq] at h; exact h
  have hmP_pos : 1 ≤ mP := Finset.one_le_card.mpr ⟨⟨0, by decide⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP0⟩⟩
  have hmM_pos : 1 ≤ mM := Finset.one_le_card.mpr ⟨⟨3, by decide⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM3⟩⟩
  have hkA_le : kA ≤ A.card := Finset.card_filter_le _ _
  have hkB_le : kB ≤ B.card := Finset.card_filter_le _ _
  have hn6 : 6 ≤ n := by dsimp only [mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hmP_pos hmM_pos hkA_le hkB_le; omega
  have hH_deg : ∀ i : Fin 4, (Finset.univ.filter (fun z : W => D.Adj (u i) z ∨ D.Adj z (u i))).card ≠ 1 := by
    intro i; have h2 : 2 ≤ (Finset.univ.filter (fun z : W => D.Adj (u i) z ∨ D.Adj z (u i))).card := by
      fin_cases i
      · obtain ⟨x, hxA, h0x⟩ := hMandP0
        have hne : u ⟨1, by decide⟩ ≠ x := fun h => hHA_disj ⟨1, by decide⟩ (h ▸ hxA)
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h01⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h0x⟩))
      · have hne : u ⟨0, by decide⟩ ≠ u ⟨2, by decide⟩ := fun h => by have := hu_inj h; simp at this
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h01⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h12⟩))
      · have hne : u ⟨1, by decide⟩ ≠ u ⟨3, by decide⟩ := fun h => by have := hu_inj h; simp at this
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h12⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h23⟩))
      · obtain ⟨y, hyB, hy3⟩ := hMandM3
        have hne : u ⟨2, by decide⟩ ≠ y := fun h => (Finset.mem_sdiff.mp hyB).2 (Finset.mem_union_left _ (h ▸ Finset.mem_image.mpr ⟨⟨2, by decide⟩, Finset.mem_univ _, rfl⟩))
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h23⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hy3⟩))
    omega
  have hk_eq := no_H_leaf_implies_k_eq u A hHA_disj hA_in hB_out hH_deg ⟨T, hO⟩
  let k := (Finset.univ.filter (fun w : W => (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card
  have hnk_id : 4 + (A.card - kA) + (B.card - kB) = n - k := by
    dsimp only [k, kA, kB, B, H] at hk_eq hcard_id hkA_le hkB_le ⊢; omega
  obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
  have hpos_id_adj : ∀ (lo : ℕ) (hhi : lo + 3 < 2 * n - 2) (i j : Fin 4),
      D.Adj (u i) (u j) → G.Adj (σ ⟨lo + i.val, by omega⟩) (σ ⟨lo + j.val, by omega⟩) := by
    intro lo hhi i j hDij
    have hstep := hH_only i j hDij
    have hm := median_adj_succ hR ⟨lo + i.val, by omega⟩ (by dsimp only; omega)
    convert hm using 2; apply Fin.ext; dsimp only; omega
  -- Case 1: mP >= 2 (and mM >= 2) => pure L = 4 at delta = 1
  rw [hW] at hcard_id
  have hMaskLe' : mP ≤ mM := by dsimp only [mP, mM, B, H]; convert hMaskLe
  by_cases hmP2 : 2 ≤ mP
  · have hhi : B.card + kB + 1 + 3 < 2 * n - 2 := by
      dsimp only [mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hkA_le hkB_le ⊢; omega
    refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      (B.card + kB + 1) hhi
      id Function.injective_id (hpos_id_adj _ hhi) 0 (by decide) (fun _ h => by omega)
      (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP2 ⊢; omega)
      0 (by decide) (fun _ h => by omega)
      (by have hZM2 : ZM ≤ 2 := by omega
          have hZM_eq' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card = ZM := by
            congr 1
          rw [hZM_eq']; dsimp only [kB, B, H]; omega)
  · -- Now mP = 1, so maskP = {0}
    have hmaskP0 : ∀ i : Fin 4, i ≠ ⟨0, by decide⟩ → ∀ x ∈ A, ¬ D.Adj (u i) x := by
      intro i hi x hxA hD
      have h2 : 2 ≤ mP := (Finset.card_pair hi).symm.trans_le (Finset.card_le_card (fun j hj => by
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxA, hD⟩
        · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP0⟩))
      omega
    -- Case 2: mM >= 3 => pure L = 4 at delta = 0
    by_cases hmM3 : 3 ≤ mM
    · have hhi : B.card + kB + 3 < 2 * n - 2 := by
        dsimp only [mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hkA_le hkB_le ⊢; omega
      refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
        (B.card + kB) hhi
        id Function.injective_id (hpos_id_adj _ hhi) 0 (by decide) (fun _ h => by omega)
        (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le ⊢; omega)
        0 (by decide) (fun _ h => by omega)
        (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM3 ⊢; omega)
    · -- Now mM <= 2 (mM = 2 or mM = 1)
      by_cases hmM2 : 2 ≤ mM
      · -- Case 3: mP = 1, mM = 2
        by_cases hnk5 : 5 ≤ n - k
        · have hhi : B.card + kB + 1 + 3 < 2 * n - 2 := by
            dsimp only [mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hkA_le hkB_le ⊢; omega
          refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
            (B.card + kB + 1) hhi
            id Function.injective_id (hpos_id_adj _ hhi) 0 (by decide) (fun _ h => by omega)
            (by dsimp only [mP, mM, ZP, ZM, kA, kB, k, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hnk_id hnk5 ⊢; omega)
            0 (by decide) (fun _ h => by omega)
            (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM2 ⊢; omega)
        · -- n - k = 4: all vertices in A and B are leaves!
          have hA_leaf : ∀ x ∈ A, ∀ z : W, ¬ D.Adj x z :=
            forall_of_filter_card_eq (by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 ⊢; omega)
          have hB_leaf : ∀ y ∈ B, ∀ z : W, ¬ D.Adj z y :=
            forall_of_filter_card_eq (by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 ⊢; omega)
          -- Find the unique other element ix != 3 in maskM
          have hex_other : ∃ ix : Fin 4, ix ≠ ⟨3, by decide⟩ ∧ ∃ y ∈ B, D.Adj y (u ix) := by
            by_contra hno; push Not at hno
            have hsub : Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i)) ⊆ {⟨3, by decide⟩} := by
              intro i hi; rw [Finset.mem_singleton]; by_contra hne
              obtain ⟨y, hyB, hyi⟩ := (Finset.mem_filter.mp hi).2; exact hno i hne y hyB hyi
            have hle := (Finset.card_le_card hsub).trans (by rw [Finset.card_singleton])
            dsimp only [mM] at hmM2; omega
          obtain ⟨ix, hix_ne3, hix_ex⟩ := hex_other
          have hmaskM_ix : ∀ i : Fin 4, i ≠ ix → i ≠ ⟨3, by decide⟩ → ∀ y ∈ B, ¬ D.Adj y (u i) := by
            intro i h1 h2 y hyB hD
            have h3 : 3 ≤ mM := by
              have hcard3 : ({i, ix, ⟨3, by decide⟩} : Finset (Fin 4)).card = 3 := by
                rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2⟩),
                  Finset.card_pair hix_ne3]
              refine hcard3.symm.trans_le (Finset.card_le_card (fun j hj => ?_))
              simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl | rfl
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hyB, hD⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hix_ex⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM3⟩
            omega
          fin_cases ix
          · exact embeds_middle_six_P4ppp u hu_inj hH_only A hHA_disj hcard_id
              hA_leaf hB_leaf hA_in hB_out hno_AB hno_HB hmaskP0 ⟨0, by decide⟩ (Or.inl rfl) hmaskM_ix hix_ex hV hG hR hL
          · exact embeds_middle_six_P4ppp u hu_inj hH_only A hHA_disj hcard_id
              hA_leaf hB_leaf hA_in hB_out hno_AB hno_HB hmaskP0 ⟨1, by decide⟩ (Or.inr rfl) hmaskM_ix hix_ex hV hG hR hL
          · -- ix = 2 => Claim A!
            obtain ⟨w0, w1, w2, w3, d01, d02, d03, d12, d13, d23, e01, e12, e23, hd0, hd2, hd3⟩ :=
              claim_A hn6 hV hG hNoSrc hNoSnk
            let t : Fin 4 → V := fun i => match i.val with | 0 => w0 | 1 => w1 | 2 => w2 | _ => w3
            refine embeds_of_Vp_Vm_core4 u hu_inj A hHA_disj hcard_id
              hA_leaf hB_leaf hA_in hB_out hno_AB hno_HB ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
              hmaskP0 hmaskM_ix hG t ?_ ?_ (by simpa [t] using hd0) (by simpa [t] using hd2) (by simpa [t] using hd3)
            · intro i j h; fin_cases i <;> fin_cases j <;> dsimp only [t] at h <;>
                first | rfl | exact absurd h d01 | exact absurd h d02 | exact absurd h d03 |
                  exact absurd h d01.symm | exact absurd h d12 | exact absurd h d13 |
                  exact absurd h d02.symm | exact absurd h d12.symm | exact absurd h d23 |
                  exact absurd h d03.symm | exact absurd h d13.symm | exact absurd h d23.symm
            · intro i j hD; have hst := hH_only i j hD
              fin_cases i <;> fin_cases j <;> simp at hst <;> dsimp only [t] <;> assumption
          · exact absurd rfl hix_ne3
      · -- Case 4: mP = 1, mM = 1 (maskP = {0}, maskM = {3})
        have hmaskM3 : ∀ i : Fin 4, i ≠ ⟨3, by decide⟩ → ∀ y ∈ B, ¬ D.Adj y (u i) := by
          intro i hi y hyB hD
          have h2 : 2 ≤ mM := (Finset.card_pair hi).symm.trans_le (Finset.card_le_card (fun j hj => by
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hyB, hD⟩
            · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM3⟩))
          omega
        by_cases hnk6 : 6 ≤ n - k
        · have hhi : B.card + kB + 2 + 3 < 2 * n - 2 := by
            dsimp only [mP, mM, kA, kB, k, B, H] at h2mP h2mM hcard_id hkA_le hkB_le hnk_id hnk6 ⊢; omega
          refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
            (B.card + kB + 2) hhi
            id Function.injective_id (hpos_id_adj _ hhi) 0 (by decide) (fun _ h => by omega)
            (by dsimp only [mP, mM, ZP, ZM, kA, kB, k, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hnk_id hnk6 ⊢; omega)
            0 (by decide) (fun _ h => by omega)
            (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_pos ⊢; omega)
        · by_cases hnk5 : 5 ≤ n - k
          · -- n - k = 5: Claim D (up to arc reversal)!
            by_cases hA_eq : A.card = kA
            · have hA_leaf : ∀ x ∈ A, ∀ z : W, ¬ D.Adj x z := forall_of_filter_card_eq hA_eq.symm
              have hB_one : B.card = kB + 1 := by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 hnk6 hA_eq ⊢; omega
              exact embeds_of_claim_D hn6 u hu_inj hH_only A hHA_disj hcard_id
                hA_leaf hB_one hA_in hB_out hno_AB hno_HB hmaskP0 hmaskM3 (fun w h => T.loopless.irrefl w (hO.1 w w h)) hV hG hNoSrc hNoSnk
            · -- B.card = kB and A.card = kA + 1: reverse (D, G) with u' i = u (3 - i)!
              have hB_eq : B.card = kB := by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 hnk6 hA_eq ⊢; omega
              have hA_one : A.card = kA + 1 := by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 hnk6 hA_eq ⊢; omega
              have hB_leaf : ∀ y ∈ B, ∀ z : W, ¬ D.Adj z y := forall_of_filter_card_eq hB_eq.symm
              exact embeds_of_claim_D_rev hn6 u hu_inj hH_only A hHA_disj hcard_id
                hB_leaf hA_one hA_in hB_out hno_AB hno_AH hmaskP0 hmaskM3
                (fun w h => T.loopless.irrefl w (hO.1 w w h)) hV hG hNoSrc hNoSnk
          · -- n - k = 4: Claim A!
            have hA_leaf : ∀ x ∈ A, ∀ z : W, ¬ D.Adj x z :=
              forall_of_filter_card_eq (by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 ⊢; omega)
            have hB_leaf : ∀ y ∈ B, ∀ z : W, ¬ D.Adj z y :=
              forall_of_filter_card_eq (by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 ⊢; omega)
            obtain ⟨w0, w1, w2, w3, d01, d02, d03, d12, d13, d23, e01, e12, e23, hd0, hd2, hd3⟩ :=
              claim_A hn6 hV hG hNoSrc hNoSnk
            let t : Fin 4 → V := fun i => match i.val with | 0 => w0 | 1 => w1 | 2 => w2 | _ => w3
            refine embeds_of_Vp_Vm_core4 u hu_inj A hHA_disj hcard_id
              hA_leaf hB_leaf hA_in hB_out hno_AB hno_HB ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
              hmaskP0 (fun i _ h3 y hyB => hmaskM3 i h3 y hyB) hG t ?_ ?_
              (by simpa [t] using hd0) (by simpa [t] using hd2) (by simpa [t] using hd3)
            · intro i j h; fin_cases i <;> fin_cases j <;> dsimp only [t] at h <;>
                first | rfl | exact absurd h d01 | exact absurd h d02 | exact absurd h d03 |
                  exact absurd h d01.symm | exact absurd h d12 | exact absurd h d13 |
                  exact absurd h d02.symm | exact absurd h d12.symm | exact absurd h d23 |
                  exact absurd h d03.symm | exact absurd h d13.symm | exact absurd h d23.symm
            · intro i j hD; have hst := hH_only i j hD
              fin_cases i <;> fin_cases j <;> simp at hst <;> dsimp only [t] <;> assumption

lemma embeds_heart_four_P4ppp
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (h01 : D.Adj (u ⟨0, by decide⟩) (u ⟨1, by decide⟩))
    (h12 : D.Adj (u ⟨1, by decide⟩) (u ⟨2, by decide⟩))
    (h23 : D.Adj (u ⟨2, by decide⟩) (u ⟨3, by decide⟩))
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i.val + 1 = j.val)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hMandP0 : ∃ x ∈ A, D.Adj (u ⟨0, by decide⟩) x)
    (hMandM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v) (hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u) :
    Embeds D G := by
  classical
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  by_cases hle : (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card ≤
      (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card
  · exact embeds_heart_four_P4ppp_le hW hT hO u hu_inj h01 h12 h23 hH_only A hHA_disj hA_in hB_out hno_AB
      hMandP0 hMandM3 (by dsimp only [B, H] at hle; convert hle) hV hG hNoSrc hNoSnk
  · -- Reverse arcs & reverse u: u' i = u (3 - i), A' = B
    let Drev : Digraph W := ⟨fun x y => D.Adj y x⟩
    let Grev : Digraph V := ⟨fun x y => G.Adj y x⟩
    let u' : Fin 4 → W := fun i => u ⟨3 - i.val, by omega⟩
    have hu'_inj : Function.Injective u' := fun i j h => Fin.ext (by have := congrArg Fin.val (hu_inj h); dsimp only at this; omega)
    have hH'_eq : Finset.univ.image u' = H := by
      ext w; simp only [H, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi⟩ => ⟨⟨3 - i.val, by omega⟩, hi⟩, fun ⟨i, hi⟩ => ⟨⟨3 - i.val, by omega⟩, by convert hi using 2; apply Fin.ext; dsimp only; omega⟩⟩
    have hA_eq_sdiff : Finset.univ \ (Finset.univ.image u' ∪ B) = A := by
      rw [hH'_eq]; ext w; simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hwH : w ∈ H
      · exact ⟨fun h => absurd (Or.inl hwH) h, fun hwA => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwH; exact absurd hwA (hHA_disj i)⟩
      · tauto
    refine embeds_rev (embeds_heart_four_P4ppp_le (D := Drev) (G := Grev) hW hT
      ⟨fun x y h => (hO.1 y x h).symm, fun x y h => hO.2 y x h.symm⟩ u' hu'_inj h23 h12 h01
      (fun i j hD => by have := hH_only ⟨3 - j.val, by omega⟩ ⟨3 - i.val, by omega⟩ hD; dsimp only at this; omega)
      B (fun i hi => (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨3 - i.val, by omega⟩, Finset.mem_univ _, rfl⟩)))
      (fun x hxB => by
        have hnot := (Finset.mem_sdiff.mp hxB).2
        exact hB_out x (fun i hi => hnot (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
          (fun h => hnot (Finset.mem_union_right _ h)))
      (fun y hyu hyB => by
        have hyA : y ∈ A := by
          by_contra hnotA; exact hyB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim
            (fun hH => by obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hH; exact hyu ⟨3 - i.val, by omega⟩ (by dsimp only [u']; convert hi.symm using 2; apply Fin.ext; dsimp only; omega)) hnotA⟩)
        exact hA_in y hyA)
      (fun x hxB y hyu hyB => by
        have hyA : y ∈ A := by
          by_contra hnotA; exact hyB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim
            (fun hH => by obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hH; exact hyu ⟨3 - i.val, by omega⟩ (by dsimp only [u']; convert hi.symm using 2; apply Fin.ext; dsimp only; omega)) hnotA⟩)
        have hnot := (Finset.mem_sdiff.mp hxB).2
        have h := hno_AB y hyA x (fun i hi => hnot (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
          (fun h => hnot (Finset.mem_union_right _ h))
        exact ⟨h.1, h.2⟩)
      hMandM3 (by rw [hA_eq_sdiff]; exact hMandP0) ?_ hV
      ⟨fun v => hG.1 v, fun x y hne => hG.2 y x hne.symm⟩ hNoSnk hNoSrc)
    have hbij1 := card_mask_rev4_le u A hHA_disj (by dsimp only [B, H] at hle; convert hle)
    dsimp only [Drev, u', B, H]
    convert hbij1

-- ============================================================================
-- TOPOLOGY 2: P4++- (u0 -> u1 -> u2 <- u3; mandP = {0, 3}, mandM = empty)
-- ============================================================================

lemma embeds_heart_four_P4ppm
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (h01 : D.Adj (u ⟨0, by decide⟩) (u ⟨1, by decide⟩))
    (h12 : D.Adj (u ⟨1, by decide⟩) (u ⟨2, by decide⟩))
    (h32 : D.Adj (u ⟨3, by decide⟩) (u ⟨2, by decide⟩))
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) →
      (i = ⟨0, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨
      (i = ⟨1, by decide⟩ ∧ j = ⟨2, by decide⟩) ∨
      (i = ⟨3, by decide⟩ ∧ j = ⟨2, by decide⟩))
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hMandP0 : ∃ x ∈ A, D.Adj (u ⟨0, by decide⟩) x)
    (hMandP3 : ∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament) :
    Embeds D G := by
  classical
  have hH_parent : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (u j) (u i) := by
    intro i hi; fin_cases i
    · exact absurd rfl hi
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h01⟩
    · exact ⟨⟨1, by decide⟩, by decide, hO.1 _ _ h12⟩
    · exact ⟨⟨2, by decide⟩, by decide, (hO.1 _ _ h32).symm⟩
  obtain ⟨hno_AH, hno_HB, hRkP, hRkM, _, h2mP, h2mM, hcard_id⟩ :=
    heart_four_structure D hT hO u hu_inj hH_parent A hHA_disj hA_in hB_out hno_AB
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let kA := (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card
  let kB := (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
  let mP := (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card
  let mM := (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card
  let ZP := (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card
  let ZM := (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card
  have hZP_eq : mP + ZP = 4 := by
    have h := card_mask_compl_fin4 (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)
    have heq : Finset.univ.filter (fun i : Fin 4 => ¬ ∃ x ∈ A, D.Adj (u i) x) =
        Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    rw [heq] at h; exact h
  have hZM_eq : mM + ZM = 4 := by
    have h := card_mask_compl_fin4 (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))
    have heq : Finset.univ.filter (fun i : Fin 4 => ¬ ∃ y ∈ B, D.Adj y (u i)) =
        Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    rw [heq] at h; exact h
  have hmP_ge2 : 2 ≤ mP := (Finset.card_pair (Fin.ne_of_val_ne (by decide) : (⟨0, by decide⟩ : Fin 4) ≠ ⟨3, by decide⟩)).symm.trans_le
    (Finset.card_le_card (fun j hj => by
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP0⟩
      · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP3⟩))
  have hkA_le : kA ≤ A.card := Finset.card_filter_le _ _
  have hkB_le : kB ≤ B.card := Finset.card_filter_le _ _
  have hH_deg : ∀ i : Fin 4, (Finset.univ.filter (fun z : W => D.Adj (u i) z ∨ D.Adj z (u i))).card ≠ 1 := by
    intro i; have h2 : 2 ≤ (Finset.univ.filter (fun z : W => D.Adj (u i) z ∨ D.Adj z (u i))).card := by
      fin_cases i
      · obtain ⟨x, hxA, h0x⟩ := hMandP0
        have hne : u ⟨1, by decide⟩ ≠ x := fun h => hHA_disj ⟨1, by decide⟩ (h ▸ hxA)
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h01⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h0x⟩))
      · have hne : u ⟨0, by decide⟩ ≠ u ⟨2, by decide⟩ := fun h => by have := hu_inj h; simp at this
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h01⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h12⟩))
      · have hne : u ⟨1, by decide⟩ ≠ u ⟨3, by decide⟩ := fun h => by have := hu_inj h; simp at this
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h12⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h32⟩))
      · obtain ⟨x, hxA, h3x⟩ := hMandP3
        have hne : u ⟨2, by decide⟩ ≠ x := fun h => hHA_disj ⟨2, by decide⟩ (h ▸ hxA)
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h32⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h3x⟩))
    omega
  have hk_eq := no_H_leaf_implies_k_eq u A hHA_disj hA_in hB_out hH_deg ⟨T, hO⟩
  let k := (Finset.univ.filter (fun w : W => (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card
  have hnk_id : 4 + (A.card - kA) + (B.card - kB) = n - k := by
    dsimp only [k, kA, kB, B, H] at hk_eq hcard_id hkA_le hkB_le ⊢; omega
  obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
  -- Universal L=4 placement placing u2 at slot 3 ALWAYS!
  have hex_pos4 : ∀ (lo : ℕ) (hhi : lo + 3 < 2 * n - 2),
      ∃ pos : Fin 4 → Fin 4, Function.Injective pos ∧ pos ⟨2, by decide⟩ = ⟨3, by decide⟩ ∧
        (∀ i j : Fin 4, D.Adj (u i) (u j) →
          G.Adj (σ ⟨lo + (pos i).val, by omega⟩) (σ ⟨lo + (pos j).val, by omega⟩)) := by
    intro lo hhi
    by_cases h13 : G.Adj (σ ⟨lo + 1, by omega⟩) (σ ⟨lo + 3, by omega⟩)
    · let pos : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨2, by decide⟩
      refine ⟨pos, fun i j h => by fin_cases i <;> fin_cases j <;> simp [pos] at h ⊢, rfl, fun i j hD => ?_⟩
      rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact median_adj_succ hR ⟨lo, by omega⟩ (by dsimp only; omega)
      · exact h13
      · exact median_adj_succ hR ⟨lo + 2, by omega⟩ (by dsimp only; omega)
    · have h03 : G.Adj (σ ⟨lo, by omega⟩) (σ ⟨lo + 3, by omega⟩) := by
        by_contra hnot03; exact h13 (m2_left_4 hL lo (by omega) hnot03)
      let pos : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨1, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨0, by decide⟩
      refine ⟨pos, fun i j h => by fin_cases i <;> fin_cases j <;> simp [pos] at h ⊢, rfl, fun i j hD => ?_⟩
      rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact median_adj_succ hR ⟨lo + 1, by omega⟩ (by dsimp only; omega)
      · exact median_adj_succ hR ⟨lo + 2, by omega⟩ (by dsimp only; omega)
      · exact h03
  -- Case 1: mP >= 3 => delta = 2
  rw [hW] at hcard_id
  by_cases hmP3 : 3 ≤ mP
  · have hhi : B.card + kB + 2 + 3 < 2 * n - 2 := by
      dsimp only [mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hkA_le hkB_le hmP3 ⊢; omega
    obtain ⟨pos, hpos_inj, _, hpos_adj⟩ := hex_pos4 (B.card + kB + 2) hhi
    by_cases hmM0 : mM = 0
    · have hnoM : ∀ i : Fin 4, ∀ y ∈ B, ¬ D.Adj y (u i) := by
        intro i y hyB hD
        have h1 : 1 ≤ mM := Finset.one_le_card.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hyB, hD⟩⟩
        omega
      refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
        (B.card + kB + 2) hhi pos hpos_inj hpos_adj 0 (by decide) (fun _ h => by omega)
        (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP3 ⊢; omega)
        4 (by decide) (fun _ _ i _ => hnoM i)
        (by have hZM_eq' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card = ZM := by congr 1
            rw [hZM_eq']; dsimp only [kB, B, H]; omega)
    · refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
        (B.card + kB + 2) hhi pos hpos_inj hpos_adj 0 (by decide) (fun _ h => by omega)
        (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP3 ⊢; omega)
        0 (by decide) (fun _ h => by omega)
        (by have hZM3 : ZM ≤ 3 := by omega
            have hZM_eq' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card = ZM := by congr 1
            rw [hZM_eq']; dsimp only [kB, B, H]; omega)
  · -- Now mP = 2 (maskP = {0, 3})
    have hmaskP03 : ∀ i : Fin 4, i ≠ ⟨0, by decide⟩ → i ≠ ⟨3, by decide⟩ → ∀ x ∈ A, ¬ D.Adj (u i) x := by
      intro i h0 h3 x hxA hD
      have h3m : 3 ≤ mP := by
        have hcard3 : ({i, ⟨0, by decide⟩, ⟨3, by decide⟩} : Finset (Fin 4)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h0, h3⟩),
            Finset.card_pair (by decide)]
        refine hcard3.symm.trans_le (Finset.card_le_card (fun j hj => ?_))
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxA, hD⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP0⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP3⟩
      omega
    -- Case 2: mM = 0 => delta = 0, qL = 4
    by_cases hmM0 : mM = 0
    · have hnoM : ∀ i : Fin 4, ∀ y ∈ B, ¬ D.Adj y (u i) := by
        intro i y hyB hD
        have h1 : 1 ≤ mM := Finset.one_le_card.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hyB, hD⟩⟩
        omega
      have hhi : B.card + kB + 3 < 2 * n - 2 := by
        dsimp only [mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hkA_le hkB_le hmP_ge2 ⊢; omega
      obtain ⟨pos, hpos_inj, _, hpos_adj⟩ := hex_pos4 (B.card + kB) hhi
      refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
        (B.card + kB) hhi pos hpos_inj hpos_adj 0 (by decide) (fun _ h => by omega)
        (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP_ge2 ⊢; omega)
        4 (by decide) (fun _ _ i _ => hnoM i)
        (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le ⊢; omega)
    · -- Case 3: mM >= 2 OR 2 not in maskM => delta = 1
      by_cases hcase3 : 2 ≤ mM ∨ (∀ y ∈ B, ¬ D.Adj y (u ⟨2, by decide⟩))
      · have hhi : B.card + kB + 1 + 3 < 2 * n - 2 := by
          dsimp only [mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hkA_le hkB_le hmP_ge2 ⊢; omega
        obtain ⟨pos, hpos_inj, hpos2, hpos_adj⟩ := hex_pos4 (B.card + kB + 1) hhi
        rcases hcase3 with hmM2 | hno2
        · refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
            (B.card + kB + 1) hhi pos hpos_inj hpos_adj 0 (by decide) (fun _ h => by omega)
            (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP_ge2 ⊢; omega)
            0 (by decide) (fun _ h => by omega)
            (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM2 ⊢; omega)
        · refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
            (B.card + kB + 1) hhi pos hpos_inj hpos_adj 0 (by decide) (fun _ h => by omega)
            (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP_ge2 ⊢; omega)
            1 (by decide) (fun t ht i hi => by
              have ht3 : t = ⟨3, by decide⟩ := Fin.ext (by have := t.isLt; simp only; omega)
              have hi2 : i = ⟨2, by decide⟩ := hpos_inj (hi.trans (ht3.trans hpos2.symm))
              exact hi2 ▸ hno2)
            (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM0 ⊢; omega)
      · -- Case 4: maskP = {0, 3}, maskM = {2}
        push Not at hcase3
        obtain ⟨hmM_lt2, h2_ex⟩ := hcase3
        have hmaskM2 : ∀ i : Fin 4, i ≠ ⟨2, by decide⟩ → ∀ y ∈ B, ¬ D.Adj y (u i) := by
          intro i hi y hyB hD
          have h2 : 2 ≤ mM := (Finset.card_pair hi).symm.trans_le (Finset.card_le_card (fun j hj => by
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hyB, hD⟩
            · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2_ex⟩))
          omega
        by_cases hnk5 : 5 ≤ n - k
        · have hhi : B.card + kB + 2 + 3 < 2 * n - 2 := by
            dsimp only [mP, mM, kA, kB, k, B, H] at h2mP h2mM hcard_id hkA_le hkB_le hmP_ge2 hnk_id hnk5 ⊢; omega
          obtain ⟨pos, hpos_inj, _, hpos_adj⟩ := hex_pos4 (B.card + kB + 2) hhi
          refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
            (B.card + kB + 2) hhi pos hpos_inj hpos_adj 0 (by decide) (fun _ h => by omega)
            (by dsimp only [mP, mM, ZP, ZM, kA, kB, k, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP_ge2 hnk_id hnk5 ⊢; omega)
            0 (by decide) (fun _ h => by omega)
            (by dsimp only [mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM0 ⊢; omega)
        · -- n - k = 4 => Middle-6!
          have hA_leaf : ∀ x ∈ A, ∀ z : W, ¬ D.Adj x z :=
            forall_of_filter_card_eq (by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 ⊢; omega)
          have hB_leaf : ∀ y ∈ B, ∀ z : W, ¬ D.Adj z y :=
            forall_of_filter_card_eq (by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 ⊢; omega)
          exact embeds_middle_six_P4ppm u hu_inj hH_only A hHA_disj hcard_id
            hA_leaf hB_leaf hA_in hB_out hno_AB hno_HB hmaskP03 hMandP3 hmaskM2 hV hG hR hL

-- ============================================================================
-- TOPOLOGY 3: P4+-+ (u0 -> u1 <- u2 -> u3; mandP = {0}, mandM = {3})
-- ============================================================================

lemma embeds_heart_four_P4pmp_le
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (h01 : D.Adj (u ⟨0, by decide⟩) (u ⟨1, by decide⟩))
    (h21 : D.Adj (u ⟨2, by decide⟩) (u ⟨1, by decide⟩))
    (h23 : D.Adj (u ⟨2, by decide⟩) (u ⟨3, by decide⟩))
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) →
      (i = ⟨0, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨
      (i = ⟨2, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨
      (i = ⟨2, by decide⟩ ∧ j = ⟨3, by decide⟩))
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hMandP0 : ∃ x ∈ A, D.Adj (u ⟨0, by decide⟩) x)
    (hMandM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    (hMaskLe : (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card ≤
      (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u i))).card)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament) :
    Embeds D G := by
  classical
  have hH_parent : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (u j) (u i) := by
    intro i hi; fin_cases i
    · exact absurd rfl hi
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h01⟩
    · exact ⟨⟨1, by decide⟩, by decide, (hO.1 _ _ h21).symm⟩
    · exact ⟨⟨2, by decide⟩, by decide, hO.1 _ _ h23⟩
  obtain ⟨hno_AH, hno_HB, hRkP, hRkM, _, h2mP, h2mM, hcard_id⟩ :=
    heart_four_structure D hT hO u hu_inj hH_parent A hHA_disj hA_in hB_out hno_AB
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let kA := (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card
  let kB := (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
  let mP := (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card
  let mM := (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card
  let ZP := (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card
  let ZM := (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card
  have hZP_eq : mP + ZP = 4 := by
    have h := card_mask_compl_fin4 (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)
    have heq : Finset.univ.filter (fun i : Fin 4 => ¬ ∃ x ∈ A, D.Adj (u i) x) =
        Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    rw [heq] at h; exact h
  have hZM_eq : mM + ZM = 4 := by
    have h := card_mask_compl_fin4 (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))
    have heq : Finset.univ.filter (fun i : Fin 4 => ¬ ∃ y ∈ B, D.Adj y (u i)) =
        Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    rw [heq] at h; exact h
  have hmP_pos : 1 ≤ mP := Finset.one_le_card.mpr ⟨⟨0, by decide⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP0⟩⟩
  have hmM_pos : 1 ≤ mM := Finset.one_le_card.mpr ⟨⟨3, by decide⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM3⟩⟩
  have hkA_le : kA ≤ A.card := Finset.card_filter_le _ _
  have hkB_le : kB ≤ B.card := Finset.card_filter_le _ _
  obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
  rw [hW] at hcard_id
  have hMaskLe' : mP ≤ mM := by dsimp only [mP, mM, B, H]; convert hMaskLe
  let r := B.card + kB + 1
  have hr4 : r + 4 < 2 * n - 2 := by
    dsimp only [r, mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hmP_pos hmM_pos hkA_le hkB_le ⊢; omega
  -- Case 1: mP >= 2 (and mM >= 2) => pure L = 4 at [r, r+3]
  by_cases hmP2 : 2 ≤ mP
  · have hZM2 : ZM ≤ 2 := by omega
    have hZM_eq' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card = ZM := by congr 1
    by_cases h03 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 3, by omega⟩)
    · let pos : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨2, by decide⟩ | 1 => ⟨3, by decide⟩ | 2 => ⟨0, by decide⟩ | _ => ⟨1, by decide⟩
      refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
        r (by omega) pos (fun i j h => by fin_cases i <;> fin_cases j <;> simp [pos] at h ⊢)
        (fun i j hD => by
          rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact median_adj_succ hR ⟨r + 2, by omega⟩ (by dsimp only; omega)
          · exact h03
          · exact median_adj_succ hR ⟨r, by omega⟩ (by dsimp only; omega))
        0 (by decide) (fun _ h => by omega)
        (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP2 ⊢; omega)
        0 (by decide) (fun _ h => by omega)
        (by rw [hZM_eq']; dsimp only [r, kB, B, H]; omega)
    · have h02 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 2, by omega⟩) := m2_right_4 hR r (by omega) h03
      have h13 : G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 3, by omega⟩) := m2_left_4 hL r (by omega) h03
      let pos : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨1, by decide⟩ | _ => ⟨3, by decide⟩
      refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
        r (by omega) pos (fun i j h => by fin_cases i <;> fin_cases j <;> simp [pos] at h ⊢)
        (fun i j hD => by
          rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h02
          · exact median_adj_succ hR ⟨r + 1, by omega⟩ (by dsimp only; omega)
          · exact h13)
        0 (by decide) (fun _ h => by omega)
        (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP2 ⊢; omega)
        0 (by decide) (fun _ h => by omega)
        (by rw [hZM_eq']; dsimp only [r, kB, B, H]; omega)
  · -- Case 2: mP = 1 (maskP = {0}) on W = 5 window [r, r + 4]
    have hmaskP0 : ∀ i : Fin 4, i ≠ ⟨0, by decide⟩ → ∀ x ∈ A, ¬ D.Adj (u i) x := by
      intro i hi x hxA hD
      have h2 : 2 ≤ mP := (Finset.card_pair hi).symm.trans_le (Finset.card_le_card (fun j hj => by
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxA, hD⟩
        · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP0⟩))
      omega
    by_cases h03 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 3, by omega⟩)
    · let pos : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨2, by decide⟩ | 1 => ⟨3, by decide⟩ | 2 => ⟨0, by decide⟩ | _ => ⟨1, by decide⟩
      have hpos_inj : Function.Injective pos := fun i j h => by fin_cases i <;> fin_cases j <;> simp [pos] at h ⊢
      have hpos_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) →
          G.Adj (σ ⟨r + (pos i).val, by omega⟩) (σ ⟨r + (pos j).val, by omega⟩) := fun i j hD => by
        rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact median_adj_succ hR ⟨r + 2, by omega⟩ (by dsimp only; omega)
        · exact h03
        · exact median_adj_succ hR ⟨r, by omega⟩ (by dsimp only; omega)
      have hqR_p : ∀ t : Fin 4, t.val < 2 → ∀ i : Fin 4, pos i = t → ∀ x ∈ A, ¬ D.Adj (u i) x := by
        intro t ht i hi; apply hmaskP0 i; intro h0; subst h0; simp [pos] at hi; rw [← hi] at ht; omega
      by_cases h1M : ∃ y ∈ B, D.Adj y (u ⟨1, by decide⟩)
      · have hmM2 : 2 ≤ mM := (Finset.card_pair (Fin.ne_of_val_ne (by decide) : (⟨1, by decide⟩ : Fin 4) ≠ ⟨3, by decide⟩)).symm.trans_le
          (Finset.card_le_card (fun j hj => by
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1M⟩
            · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM3⟩))
        refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
          r (by omega) pos hpos_inj hpos_adj 2 (by decide) hqR_p
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le ⊢; omega)
          0 (by decide) (fun _ h => by omega)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM2 ⊢; omega)
      · push Not at h1M
        refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
          r (by omega) pos hpos_inj hpos_adj 2 (by decide) hqR_p
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le ⊢; omega)
          1 (by decide) (fun t ht i hi => by
            have ht3 : t = ⟨3, by decide⟩ := Fin.ext (by have := t.isLt; simp only; omega)
            have hi1 : i = ⟨1, by decide⟩ := hpos_inj (hi.trans ht3)
            exact hi1 ▸ h1M)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_pos ⊢; omega)
    · by_cases h14 : G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 4, by omega⟩)
      · let pos : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨2, by decide⟩ | 1 => ⟨3, by decide⟩ | 2 => ⟨0, by decide⟩ | _ => ⟨1, by decide⟩
        refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
          (r + 1) (by omega) pos (fun i j h => by fin_cases i <;> fin_cases j <;> simp [pos] at h ⊢)
          (fun i j hD => by
            rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · have hm := median_adj_succ hR ⟨r + 3, by omega⟩ (by dsimp only; omega)
              exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
            · exact sigma_adj_congr h14 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
            · have hm := median_adj_succ hR ⟨r + 1, by omega⟩ (by dsimp only; omega)
              exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
          2 (by decide) (fun t ht i hi => by
            apply hmaskP0 i; intro h0; subst h0; simp [pos] at hi; rw [← hi] at ht; omega)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le ⊢; omega)
          0 (by decide) (fun _ h => by omega)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_pos ⊢; omega)
      · -- 3 -> 0 and 4 -> 1 => M2-Right gives 0 -> 2; use L = 5 on [r, r+4], pos = (4, 1, 0, 2), F = {3}
        have h02 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 2, by omega⟩) := m2_right_4 hR r (by omega) h03
        have h41 : G.Adj (σ ⟨r + 4, by omega⟩) (σ ⟨r + 1, by omega⟩) :=
          (adj_or_rev_of_isTournament hG (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only at this; omega)).resolve_left h14
        let pos : Fin 4 → Fin (r + 4 - r + 1) := fun i =>
          match i.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨0, by omega⟩ | _ => ⟨2, by omega⟩
        have hpos_inj : Function.Injective pos := fun i j h => by
          have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp [pos] at hv ⊢
        have hfree_eq3 : ∀ t : Fin (r + 4 - r + 1), (∀ i : Fin 4, pos i ≠ t) → t.val = 3 := by
          intro t ht
          have h0 : t.val ≠ 4 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos, h]))
          have h1 : t.val ≠ 1 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos, h]))
          have h2 : t.val ≠ 0 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos, h]))
          have h3 : t.val ≠ 2 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos, h]))
          have := t.isLt; omega
        have hpos_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) →
            G.Adj (σ ⟨r + (pos i).val, by omega⟩) (σ ⟨r + (pos j).val, by omega⟩) := fun i j hD => by
          rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h41
          · exact median_adj_succ hR ⟨r, by omega⟩ (by dsimp only; omega)
          · exact h02
        have hDumR1 : (Finset.univ.filter (fun t : Fin (r + 4 - r + 1) =>
            (∀ i, pos i ≠ t) ∧ (fun _ : Fin (r + 4 - r + 1) => (none : Option (Fin 4))) t = none)).card ≤ 1 := by
          have hsub : Finset.univ.filter (fun t : Fin (r + 4 - r + 1) =>
              (∀ i, pos i ≠ t) ∧ (fun _ : Fin (r + 4 - r + 1) => (none : Option (Fin 4))) t = none) ⊆ {⟨3, by omega⟩} := by
            intro t ht; rw [Finset.mem_singleton]; exact Fin.ext (hfree_eq3 t (Finset.mem_filter.mp ht).2.1)
          exact (Finset.card_le_card hsub).trans (by rw [Finset.card_singleton])
        have hBoundR : ∀ exhR : Finset (Fin 4),
            (∀ i ∈ exhR, ∃ t : Fin (r + 4 - r + 1), (∀ j, pos j ≠ t) ∧ (none : Option (Fin 4)) = some i) →
            ∃ qR : ℕ, qR ≤ r + 4 - r + 1 ∧
              (∀ t : Fin (r + 4 - r + 1), t.val < qR →
                (∀ i : Fin 4, pos i = t → (∀ x ∈ A, ¬ D.Adj (u i) x) ∨ i ∈ exhR) ∧
                ((∀ i : Fin 4, pos i ≠ t) → (none : Option (Fin 4)) = none)) ∧
              4 + A.card + kA +
                2 * (Finset.univ.filter (fun t : Fin (r + 4 - r + 1) =>
                  (∀ i, pos i ≠ t) ∧ (fun _ : Fin (r + 4 - r + 1) => (none : Option (Fin 4))) t = none)).card +
                ZP + exhR.card ≤ (2 * n - 2 - r) + 1 + qR := by
          intro exhR hexh
          have he0 : exhR.card = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro i hi; obtain ⟨_, _, hc⟩ := hexh i hi; cases hc
          refine ⟨4, by omega, fun t ht => ⟨fun i hi => Or.inl (hmaskP0 i (fun h0 => by subst h0; have := congrArg Fin.val hi; simp only [pos] at this; omega)),
            fun _ => rfl⟩, ?_⟩
          rw [he0]; dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hDumR1 ⊢; omega
        by_cases h0M : ∃ y ∈ B, D.Adj y (u ⟨0, by decide⟩)
        · -- fL(3) = some 0
          let fL : Fin (r + 4 - r + 1) → Option (Fin 4) := fun t => if t.val = 3 then some ⟨0, by decide⟩ else none
          have hmM2 : 2 ≤ mM := (Finset.card_pair (Fin.ne_of_val_ne (by decide) : (⟨0, by decide⟩ : Fin 4) ≠ ⟨3, by decide⟩)).symm.trans_le
            (Finset.card_le_card (fun j hj => by
              rcases Finset.mem_insert.mp hj with rfl | hj'
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0M⟩
              · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM3⟩))
          refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
            hV hR hL r (r + 4) (by omega) hr4 pos hpos_inj hpos_adj (fun _ => none) fL
            (fun _ _ => Or.inl rfl)
            (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
            (fun t1 t2 ht1 ht2 _ _ _ => Fin.ext ((hfree_eq3 t1 ht1).trans (hfree_eq3 t2 ht2).symm))
            (fun t ht h hft => by
              have ht3 := hfree_eq3 t ht
              have hh0 : h = ⟨0, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht3] at hft; exact Option.some.inj hft.symm
              subst hh0; refine ⟨by simp only [pos]; omega, ?_, h0M⟩
              have hm := median_adj_succ hR ⟨r + 3, by omega⟩ (by dsimp only; omega)
              exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
            hBoundR ?_
          intro exhL hexh
          have hd0 : (Finset.univ.filter (fun t : Fin (r + 4 - r + 1) => (∀ i, pos i ≠ t) ∧ fL t = none)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro t _ ⟨ht, hf⟩
            have ht3 := hfree_eq3 t ht; dsimp only [fL] at hf; rw [if_pos ht3] at hf; cases hf
          have he1 : exhL.card ≤ 1 := by
            have hsub : exhL ⊆ {⟨0, by decide⟩} := fun i hi => by
              obtain ⟨t, ht, hft⟩ := hexh i hi
              have ht3 := hfree_eq3 t ht; dsimp only [fL] at hft; rw [if_pos ht3] at hft
              rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
            exact (Finset.card_le_card hsub).trans (by rw [Finset.card_singleton])
          refine ⟨0, by omega, fun _ h => by omega, ?_⟩
          rw [hd0]; dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM2 he1 ⊢; omega
        · -- 0 not in maskM => fL = none, qL = 2 (slots 4 = u0 and 3 = dummy)
          push Not at h0M
          refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
            hV hR hL r (r + 4) (by omega) hr4 pos hpos_inj hpos_adj (fun _ => none) (fun _ => none)
            (fun _ _ => Or.inl rfl)
            (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
            (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
            hBoundR ?_
          intro exhL hexh
          have he0 : exhL.card = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro i hi; obtain ⟨_, _, hc⟩ := hexh i hi; cases hc
          refine ⟨2, by omega, fun t ht => ⟨fun i hi => Or.inl (by
            have hi0 : i = ⟨0, by decide⟩ := by
              fin_cases i
              · rfl
              · exfalso; have := congrArg Fin.val hi; simp only [pos] at this; omega
              · exfalso; have := congrArg Fin.val hi; simp only [pos] at this; omega
              · exfalso; have := congrArg Fin.val hi; simp only [pos] at this; omega
            exact hi0 ▸ h0M), fun _ => rfl⟩, ?_⟩
          rw [he0]; dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_pos hDumR1 ⊢; omega

lemma embeds_heart_four_P4pmp
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (h01 : D.Adj (u ⟨0, by decide⟩) (u ⟨1, by decide⟩))
    (h21 : D.Adj (u ⟨2, by decide⟩) (u ⟨1, by decide⟩))
    (h23 : D.Adj (u ⟨2, by decide⟩) (u ⟨3, by decide⟩))
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) →
      (i = ⟨0, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨
      (i = ⟨2, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨
      (i = ⟨2, by decide⟩ ∧ j = ⟨3, by decide⟩))
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hMandP0 : ∃ x ∈ A, D.Adj (u ⟨0, by decide⟩) x)
    (hMandM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament) :
    Embeds D G := by
  classical
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  by_cases hle : (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card ≤
      (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card
  · exact embeds_heart_four_P4pmp_le hW hT hO u hu_inj h01 h21 h23 hH_only A hHA_disj hA_in hB_out hno_AB
      hMandP0 hMandM3 (by dsimp only [B, H] at hle; convert hle) hV hG
  · let Drev : Digraph W := ⟨fun x y => D.Adj y x⟩
    let Grev : Digraph V := ⟨fun x y => G.Adj y x⟩
    let u' : Fin 4 → W := fun i => u ⟨3 - i.val, by omega⟩
    have hu'_inj : Function.Injective u' := fun i j h => Fin.ext (by have := congrArg Fin.val (hu_inj h); dsimp only at this; omega)
    have hH'_eq : Finset.univ.image u' = H := by
      ext w; simp only [H, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi⟩ => ⟨⟨3 - i.val, by omega⟩, hi⟩, fun ⟨i, hi⟩ => ⟨⟨3 - i.val, by omega⟩, by convert hi using 2; apply Fin.ext; dsimp only; omega⟩⟩
    have hA_eq_sdiff : Finset.univ \ (Finset.univ.image u' ∪ B) = A := by
      rw [hH'_eq]; ext w; simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hwH : w ∈ H
      · exact ⟨fun h => absurd (Or.inl hwH) h, fun hwA => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwH; exact absurd hwA (hHA_disj i)⟩
      · tauto
    refine embeds_rev (embeds_heart_four_P4pmp_le (D := Drev) (G := Grev) hW hT
      ⟨fun x y h => (hO.1 y x h).symm, fun x y h => hO.2 y x h.symm⟩ u' hu'_inj h23 h21 h01
      (fun i j hD => by
        rcases hH_only ⟨3 - j.val, by omega⟩ ⟨3 - i.val, by omega⟩ hD with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right; right; exact ⟨Fin.ext (by have := congrArg Fin.val h2; simp only at this ⊢; omega),
            Fin.ext (by have := congrArg Fin.val h1; simp only at this ⊢; omega)⟩
        · right; left; exact ⟨Fin.ext (by have := congrArg Fin.val h2; simp only at this ⊢; omega),
            Fin.ext (by have := congrArg Fin.val h1; simp only at this ⊢; omega)⟩
        · left; exact ⟨Fin.ext (by have := congrArg Fin.val h2; simp only at this ⊢; omega),
            Fin.ext (by have := congrArg Fin.val h1; simp only at this ⊢; omega)⟩)
      B (fun i hi => (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨3 - i.val, by omega⟩, Finset.mem_univ _, rfl⟩)))
      (fun x hxB => by
        have hnot := (Finset.mem_sdiff.mp hxB).2
        exact hB_out x (fun i hi => hnot (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
          (fun h => hnot (Finset.mem_union_right _ h)))
      (fun y hyu hyB => by
        have hyA : y ∈ A := by
          by_contra hnotA; exact hyB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim
            (fun hH => by obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hH; exact hyu ⟨3 - i.val, by omega⟩ (by dsimp only [u']; convert hi.symm using 2; apply Fin.ext; dsimp only; omega)) hnotA⟩)
        exact hA_in y hyA)
      (fun x hxB y hyu hyB => by
        have hyA : y ∈ A := by
          by_contra hnotA; exact hyB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim
            (fun hH => by obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hH; exact hyu ⟨3 - i.val, by omega⟩ (by dsimp only [u']; convert hi.symm using 2; apply Fin.ext; dsimp only; omega)) hnotA⟩)
        have hnot := (Finset.mem_sdiff.mp hxB).2
        have h := hno_AB y hyA x (fun i hi => hnot (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
          (fun h => hnot (Finset.mem_union_right _ h))
        exact ⟨h.1, h.2⟩)
      hMandM3 (by rw [hA_eq_sdiff]; exact hMandP0) ?_ hV
      ⟨fun v => hG.1 v, fun x y hne => hG.2 y x hne.symm⟩)
    have hbij1 := card_mask_rev4_le u A hHA_disj (by dsimp only [B, H] at hle; convert hle)
    dsimp only [Drev, u', B, H]
    convert hbij1

-- ============================================================================
-- TOPOLOGY 4: S4++- (u3 -> u0, u0 -> u1, u0 -> u2; mandP = {3}, mandM = {1, 2})
-- ============================================================================

lemma embeds_heart_four_S4ppm
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (h30 : D.Adj (u ⟨3, by decide⟩) (u ⟨0, by decide⟩))
    (h01 : D.Adj (u ⟨0, by decide⟩) (u ⟨1, by decide⟩))
    (h02 : D.Adj (u ⟨0, by decide⟩) (u ⟨2, by decide⟩))
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) →
      (i = ⟨3, by decide⟩ ∧ j = ⟨0, by decide⟩) ∨
      (i = ⟨0, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨
      (i = ⟨0, by decide⟩ ∧ j = ⟨2, by decide⟩))
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hMandP3 : ∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x)
    (hMandM1 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨1, by decide⟩))
    (hMandM2 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨2, by decide⟩))
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v) (hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u) :
    Embeds D G := by
  classical
  have hH_parent : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (u j) (u i) := by
    intro i hi; fin_cases i
    · exact absurd rfl hi
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h01⟩
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h02⟩
    · exact ⟨⟨0, by decide⟩, by decide, (hO.1 _ _ h30).symm⟩
  obtain ⟨hno_AH, hno_HB, hRkP, hRkM, _, h2mP, h2mM, hcard_id⟩ :=
    heart_four_structure D hT hO u hu_inj hH_parent A hHA_disj hA_in hB_out hno_AB
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let kA := (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card
  let kB := (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
  let mP := (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card
  let mM := (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card
  let ZP := (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card
  let ZM := (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card
  have hZP_eq : mP + ZP = 4 := by
    have h := card_mask_compl_fin4 (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)
    have heq : Finset.univ.filter (fun i : Fin 4 => ¬ ∃ x ∈ A, D.Adj (u i) x) =
        Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    rw [heq] at h; exact h
  have hZM_eq : mM + ZM = 4 := by
    have h := card_mask_compl_fin4 (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))
    have heq : Finset.univ.filter (fun i : Fin 4 => ¬ ∃ y ∈ B, D.Adj y (u i)) =
        Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    rw [heq] at h; exact h
  have hmP_pos : 1 ≤ mP := Finset.one_le_card.mpr ⟨⟨3, by decide⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP3⟩⟩
  have hmM_ge2 : 2 ≤ mM := (Finset.card_pair (Fin.ne_of_val_ne (by decide) : (⟨1, by decide⟩ : Fin 4) ≠ ⟨2, by decide⟩)).symm.trans_le
    (Finset.card_le_card (fun j hj => by
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM1⟩
      · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM2⟩))
  have hkA_le : kA ≤ A.card := Finset.card_filter_le _ _
  have hkB_le : kB ≤ B.card := Finset.card_filter_le _ _
  have hn6 : 6 ≤ n := by dsimp only [mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hmP_pos hmM_ge2 hkA_le hkB_le; omega
  have hH_deg : ∀ i : Fin 4, (Finset.univ.filter (fun z : W => D.Adj (u i) z ∨ D.Adj z (u i))).card ≠ 1 := by
    intro i; have h2 : 2 ≤ (Finset.univ.filter (fun z : W => D.Adj (u i) z ∨ D.Adj z (u i))).card := by
      fin_cases i
      · have hne : u ⟨1, by decide⟩ ≠ u ⟨2, by decide⟩ := fun h => by have := hu_inj h; simp at this
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h01⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h02⟩))
      · obtain ⟨y, hyB, hy1⟩ := hMandM1
        have hne : u ⟨0, by decide⟩ ≠ y := fun h => (Finset.mem_sdiff.mp hyB).2 (Finset.mem_union_left _ (h ▸ Finset.mem_image.mpr ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩))
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h01⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hy1⟩))
      · obtain ⟨y, hyB, hy2⟩ := hMandM2
        have hne : u ⟨0, by decide⟩ ≠ y := fun h => (Finset.mem_sdiff.mp hyB).2 (Finset.mem_union_left _ (h ▸ Finset.mem_image.mpr ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩))
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h02⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hy2⟩))
      · obtain ⟨x, hxA, h3x⟩ := hMandP3
        have hne : u ⟨0, by decide⟩ ≠ x := fun h => hHA_disj ⟨0, by decide⟩ (h ▸ hxA)
        exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h30⟩
          · rw [Finset.mem_singleton.mp hz']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h3x⟩))
    omega
  have hk_eq := no_H_leaf_implies_k_eq u A hHA_disj hA_in hB_out hH_deg ⟨T, hO⟩
  let k := (Finset.univ.filter (fun w : W => (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card
  have hnk_id : 4 + (A.card - kA) + (B.card - kB) = n - k := by
    dsimp only [k, kA, kB, B, H] at hk_eq hcard_id hkA_le hkB_le ⊢; omega
  obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
  -- Helper: run Plan A (if r+1 -> r+3) or Plan B1/B2 (if r+3 -> r+1) on window [r, r+4]!
  let posA : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨1, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨0, by decide⟩
  let posB1 : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨2, by decide⟩
  let posB2 : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨2, by decide⟩ | 1 => ⟨0, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨1, by decide⟩
  have hPlanA : ∀ (r : ℕ) (hr : r + 4 < 2 * n - 2),
      G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 3, by omega⟩) →
      4 + A.card + kA + ZP ≤ (2 * n - 2 - r) + 1 →
      4 + B.card + kB + ZM ≤ (r + 4) + 1 → Embeds D G := by
    intro r hr h13 hRb hLb
    refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      r (by omega) posA (fun i j h => by fin_cases i <;> fin_cases j <;> simp [posA] at h ⊢)
      (fun i j hD => by
        rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact median_adj_succ hR ⟨r, by omega⟩ (by dsimp only; omega)
        · exact median_adj_succ hR ⟨r + 1, by omega⟩ (by dsimp only; omega)
        · exact h13)
      0 (by decide) (fun _ h => by omega) (by dsimp only [kA, ZP, B, H] at hRb ⊢; omega)
      0 (by decide) (fun _ h => by omega) (by dsimp only [kB, ZM, B, H] at hLb ⊢; omega)
  have hPlanB1 : ∀ (r : ℕ) (hr : r + 4 < 2 * n - 2),
      ¬ G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 3, by omega⟩) →
      ∀ (qR : ℕ) (hqR : qR ≤ 4),
      (∀ t : Fin 4, t.val < qR → ∀ i : Fin 4, posB1 i = t → ∀ x ∈ A, ¬ D.Adj (u i) x) →
      4 + A.card + kA + ZP ≤ (2 * n - 2 - (r + 1)) + 1 + qR →
      4 + B.card + kB + ZM ≤ (r + 5) + 1 → Embeds D G := by
    intro r hr hnot13 qR hqR hqRp hRb hLb
    have h31 : G.Adj (σ ⟨r + 3, by omega⟩) (σ ⟨r + 1, by omega⟩) :=
      (adj_or_rev_of_isTournament hG (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only at this; omega)).resolve_left hnot13
    have h14 : G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 4, by omega⟩) := by
      by_contra hnot14
      have h13 := m2_right_4 hR (r + 1) (by omega) (by convert hnot14 using 2)
      exact hnot13 (by convert h13 using 2)
    refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      (r + 1) (by omega) posB1 (fun i j h => by fin_cases i <;> fin_cases j <;> simp [posB1] at h ⊢)
      (fun i j hD => by
        rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact sigma_adj_congr h31 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
        · have hm := median_adj_succ hR ⟨r + 1, by omega⟩ (by dsimp only; omega)
          exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
        · exact sigma_adj_congr h14 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
      qR hqR hqRp (by dsimp only [kA, ZP, B, H] at hRb ⊢; omega)
      0 (by decide) (fun _ h => by omega) (by dsimp only [kB, ZM, B, H] at hLb ⊢; omega)
  have hPlanB2 : ∀ (r : ℕ) (hr : r + 4 < 2 * n - 2),
      ¬ G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 3, by omega⟩) →
      ∀ (qR : ℕ) (hqR : qR ≤ 4),
      (∀ t : Fin 4, t.val < qR → ∀ i : Fin 4, posB2 i = t → ∀ x ∈ A, ¬ D.Adj (u i) x) →
      4 + A.card + kA + ZP ≤ (2 * n - 2 - (r + 1)) + 1 + qR →
      4 + B.card + kB + ZM ≤ (r + 5) + 1 → Embeds D G := by
    intro r hr hnot13 qR hqR hqRp hRb hLb
    have h31 : G.Adj (σ ⟨r + 3, by omega⟩) (σ ⟨r + 1, by omega⟩) :=
      (adj_or_rev_of_isTournament hG (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only at this; omega)).resolve_left hnot13
    refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      (r + 1) (by omega) posB2 (fun i j h => by fin_cases i <;> fin_cases j <;> simp [posB2] at h ⊢)
      (fun i j hD => by
        rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hm := median_adj_succ hR ⟨r + 2, by omega⟩ (by dsimp only; omega)
          exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
        · exact sigma_adj_congr h31 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
        · have hm := median_adj_succ hR ⟨r + 3, by omega⟩ (by dsimp only; omega)
          exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
      qR hqR hqRp (by dsimp only [kA, ZP, B, H] at hRb ⊢; omega)
      0 (by decide) (fun _ h => by omega) (by dsimp only [kB, ZM, B, H] at hLb ⊢; omega)
  rw [hW] at hcard_id
  -- Case 1: 0 in maskP => delta = 1, Plan A or Plan B2
  by_cases h0P : ∃ x ∈ A, D.Adj (u ⟨0, by decide⟩) x
  · have hmP2 : 2 ≤ mP := (Finset.card_pair (Fin.ne_of_val_ne (by decide) : (⟨0, by decide⟩ : Fin 4) ≠ ⟨3, by decide⟩)).symm.trans_le
      (Finset.card_le_card (fun j hj => by
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0P⟩
        · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP3⟩))
    let r := B.card + kB + 1
    have hr : r + 4 < 2 * n - 2 := by dsimp only [r, mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hmP2 hmM_ge2 hkA_le hkB_le ⊢; omega
    by_cases h13 : G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 3, by omega⟩)
    · exact hPlanA r hr h13
        (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP2 ⊢; omega)
        (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_ge2 ⊢; omega)
    · by_cases h1P : ∃ x ∈ A, D.Adj (u ⟨1, by decide⟩) x
      · have hmP3 : 3 ≤ mP := by
          have hcard3 : ({⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin 4)).card = 3 := by decide
          refine hcard3.symm.trans_le (Finset.card_le_card (fun j hj => ?_))
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl | rfl
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0P⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1P⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP3⟩
        exact hPlanB2 r hr h13 0 (by decide) (fun _ h => by omega)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP3 ⊢; omega)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_ge2 ⊢; omega)
      · push Not at h1P
        exact hPlanB2 r hr h13 1 (by decide) (fun t ht i hi => by
            have ht0 : t = ⟨0, by decide⟩ := Fin.ext (by simp only; omega)
            have hi1 : i = ⟨1, by decide⟩ := by fin_cases i <;> simp [posB2, ht0] at hi ⊢
            exact hi1 ▸ h1P)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP2 ⊢; omega)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_ge2 ⊢; omega)
  · -- Now 0 not in maskP!
    push Not at h0P
    -- Case 2: mP >= 2 (so 1 or 2 in maskP) => delta = 1, Plan A or Plan B1 (qR = 1 since u0 at slot 0!)
    by_cases hmP2 : 2 ≤ mP
    · let r := B.card + kB + 1
      have hr : r + 4 < 2 * n - 2 := by dsimp only [r, mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hmP2 hmM_ge2 hkA_le hkB_le ⊢; omega
      by_cases h13 : G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 3, by omega⟩)
      · exact hPlanA r hr h13
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP2 ⊢; omega)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_ge2 ⊢; omega)
      · exact hPlanB1 r hr h13 1 (by decide) (fun t ht i hi => by
            have ht0 : t = ⟨0, by decide⟩ := Fin.ext (by simp only; omega)
            have hi0 : i = ⟨0, by decide⟩ := by fin_cases i <;> simp [posB1, ht0] at hi ⊢
            exact hi0 ▸ h0P)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hmP2 ⊢; omega)
          (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_ge2 ⊢; omega)
    · -- Now mP = 1 (maskP = {3})!
      have hmaskP3 : ∀ i : Fin 4, i ≠ ⟨3, by decide⟩ → ∀ x ∈ A, ¬ D.Adj (u i) x := by
        intro i hi x hxA hD
        have h2 : 2 ≤ mP := (Finset.card_pair hi).symm.trans_le (Finset.card_le_card (fun j hj => by
          rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxA, hD⟩
          · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandP3⟩))
        omega
      -- Case 3: mM >= 3 => delta = 0, Plan A or Plan B1 (qR = 2 since u0, u1 not in maskP!)
      by_cases hmM3 : 3 ≤ mM
      · let r := B.card + kB
        have hr : r + 4 < 2 * n - 2 := by dsimp only [r, mP, mM, kA, kB, B, H] at h2mP h2mM hcard_id hmP_pos hmM3 hkA_le hkB_le ⊢; omega
        by_cases h13 : G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 3, by omega⟩)
        · exact hPlanA r hr h13
            (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le ⊢; omega)
            (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM3 ⊢; omega)
        · exact hPlanB1 r hr h13 2 (by decide) (fun t ht i hi => by
              apply hmaskP3 i; intro h3; subst h3; simp [posB1] at hi; rw [← hi] at ht; omega)
            (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le ⊢; omega)
            (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM3 ⊢; omega)
      · -- Case 4: maskP = {3}, maskM = {1, 2}
        have hmaskM12 : ∀ i : Fin 4, i ≠ ⟨1, by decide⟩ → i ≠ ⟨2, by decide⟩ → ∀ y ∈ B, ¬ D.Adj y (u i) := by
          intro i h1 h2 y hyB hD
          have h3 : 3 ≤ mM := by
            have hcard3 : ({i, ⟨1, by decide⟩, ⟨2, by decide⟩} : Finset (Fin 4)).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2⟩),
                Finset.card_pair (by decide)]
            refine hcard3.symm.trans_le (Finset.card_le_card (fun j hj => ?_))
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hyB, hD⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM1⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM2⟩
          omega
        by_cases hnk5 : 5 ≤ n - k
        · let r := B.card + kB + 1
          have hr : r + 4 < 2 * n - 2 := by dsimp only [r, mP, mM, kA, kB, k, B, H] at h2mP h2mM hcard_id hmP_pos hmM_ge2 hkA_le hkB_le hnk_id hnk5 ⊢; omega
          by_cases h13 : G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 3, by omega⟩)
          · exact hPlanA r hr h13
              (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, k, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hnk_id hnk5 ⊢; omega)
              (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_ge2 ⊢; omega)
          · exact hPlanB1 r hr h13 2 (by decide) (fun t ht i hi => by
                apply hmaskP3 i; intro h3; subst h3; simp [posB1] at hi; rw [← hi] at ht; omega)
              (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, k, B, H] at h2mP h2mM hcard_id hZP_eq hkA_le hkB_le hnk_id hnk5 ⊢; omega)
              (by dsimp only [r, mP, mM, ZP, ZM, kA, kB, B, H] at h2mP h2mM hcard_id hZM_eq hkA_le hkB_le hmM_ge2 ⊢; omega)
        · -- n - k = 4 => Claim B!
          have hA_leaf : ∀ x ∈ A, ∀ z : W, ¬ D.Adj x z :=
            forall_of_filter_card_eq (by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 ⊢; omega)
          have hB_leaf : ∀ y ∈ B, ∀ z : W, ¬ D.Adj z y :=
            forall_of_filter_card_eq (by dsimp only [kA, kB, k, B, H] at hnk_id hkA_le hkB_le hnk5 ⊢; omega)
          obtain ⟨w0, w1, w2, w3, d01, d02, d03, d12, d13, d23, e30, e01, e02, hd3, hd1, hd2⟩ :=
            claim_B hn6 hV hG hNoSrc hNoSnk
          let t : Fin 4 → V := fun i => match i.val with | 0 => w0 | 1 => w1 | 2 => w2 | _ => w3
          refine embeds_of_Vp_Vm_core4 u hu_inj A hHA_disj hcard_id
            hA_leaf hB_leaf hA_in hB_out hno_AB hno_HB ⟨3, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
            hmaskP3 hmaskM12 hG t ?_ ?_ (by simpa [t] using hd3) (by simpa [t] using hd1) (by simpa [t] using hd2)
          · intro i j h; fin_cases i <;> fin_cases j <;> dsimp only [t] at h <;>
              first | rfl | exact absurd h d01 | exact absurd h d02 | exact absurd h d03 |
                exact absurd h d01.symm | exact absurd h d12 | exact absurd h d13 |
                exact absurd h d02.symm | exact absurd h d12.symm | exact absurd h d23 |
                exact absurd h d03.symm | exact absurd h d13.symm | exact absurd h d23.symm
          · intro i j hD
            rcases hH_only i j hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp only [t] <;> assumption

-- ============================================================================
-- MODULE 6B: TOPOLOGY 5 — S4+++ (u0 -> u1, u0 -> u2, u0 -> u3; mandM = {1, 2, 3})
-- ============================================================================

-- Helper avoiding DecidablePred mismatches on dummy-slot counts in hBoundR / hBoundL
lemma pure_plan_arith_bound {α : Type*} [Fintype α] [DecidableEq α]
    {P : α → Prop} [DecidablePred P] (S : Finset α)
    (hsub : ∀ x : α, P x → x ∈ S) {base z e rhs : ℕ}
    (h : base + 2 * S.card + z + e ≤ rhs) :
    base + 2 * (Finset.univ.filter P).card + z + e ≤ rhs := by
  have hle : (Finset.univ.filter P).card ≤ S.card :=
    Finset.card_le_card (fun x hx => hsub x (Finset.mem_filter.mp hx).2)
  omega

-- Subcase 5A: 1, 2 not in maskP (1-Root Virtual-Vertex Skip Construction!)
lemma embeds_heart_four_S4ppp_le1
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (h01 : D.Adj (u ⟨0, by decide⟩) (u ⟨1, by decide⟩))
    (h02 : D.Adj (u ⟨0, by decide⟩) (u ⟨2, by decide⟩))
    (h03 : D.Adj (u ⟨0, by decide⟩) (u ⟨3, by decide⟩))
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hMandM1 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨1, by decide⟩))
    (hMandM2 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨2, by decide⟩))
    (hMandM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    (hno1A : ∀ x ∈ A, ¬ D.Adj (u ⟨1, by decide⟩) x)
    (hno2A : ∀ x ∈ A, ¬ D.Adj (u ⟨2, by decide⟩) x)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament) :
    Embeds D G := by
  classical
  have hH_parent : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (u j) (u i) := by
    intro i hi; fin_cases i
    · exact absurd rfl hi
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h01⟩
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h02⟩
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h03⟩
  obtain ⟨hno_AH, hno_HB, hRkP, hRkM, _, h2mP, h2mM, hcard_id⟩ :=
    heart_four_structure D hT hO u hu_inj hH_parent A hHA_disj hA_in hB_out hno_AB
  rw [hW] at hcard_id
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let kA := (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card
  let kB := (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
  let mP := (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card
  let mM := (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card
  let ZP := (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card
  let ZM := (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card
  have hZP_eq : mP + ZP = 4 := by
    have h := card_mask_compl_fin4 (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)
    have heq : Finset.univ.filter (fun i : Fin 4 => ¬ ∃ x ∈ A, D.Adj (u i) x) =
        Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    rw [heq] at h; exact h
  have hZM_eq : mM + ZM = 4 := by
    have h := card_mask_compl_fin4 (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))
    have heq : Finset.univ.filter (fun i : Fin 4 => ¬ ∃ y ∈ B, D.Adj y (u i)) =
        Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    rw [heq] at h; exact h
  have hmM_ge3 : 3 ≤ mM := by
    have hcard3 : ({⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} : Finset (Fin 4)).card = 3 := by decide
    refine hcard3.symm.trans_le (Finset.card_le_card (fun j hj => ?_))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM3⟩
  have hkA_le : kA ≤ A.card := Finset.card_filter_le _ _
  have hkB_le : kB ≤ B.card := Finset.card_filter_le _ _
  have hBkB_ge6 : 6 ≤ B.card + kB := by dsimp only [mM, kB, B, H] at h2mM hmM_ge3 ⊢; omega
  let r := if (∃ y ∈ B, D.Adj y (u ⟨0, by decide⟩)) then B.card + kB - 1 else B.card + kB
  have hr_eq : B.card + kB + ZM = r + 1 := by
    by_cases h0M : ∃ y ∈ B, D.Adj y (u ⟨0, by decide⟩)
    · have hmM4 : mM = 4 := by
        have h4 : (Finset.univ : Finset (Fin 4)).card ≤ mM := Finset.card_le_card (fun j _ => by
          fin_cases j
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0M⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM1⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM2⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM3⟩)
        rw [Finset.card_univ, Fintype.card_fin] at h4
        have hle4 := Finset.card_filter_le (Finset.univ : Finset (Fin 4)) (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))
        rw [Finset.card_univ, Fintype.card_fin] at hle4; dsimp only [mM] at h4 ⊢; omega
      dsimp only [r]; rw [if_pos h0M]; omega
    · have hmM3 : mM = 3 := by
        have hsub : Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i)) ⊆ {⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} := by
          intro i hi; fin_cases i
          · exact absurd (Finset.mem_filter.mp hi).2 h0M
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        have hle3 : mM ≤ 3 := (Finset.card_le_card hsub).trans (by decide)
        omega
      dsimp only [r]; rw [if_neg h0M]; omega
  have hr_le_BkB : r ≤ B.card + kB := by dsimp only [r]; split_ifs <;> omega
  have hr6 : r + 6 ≤ 2 * n - 2 := by
    dsimp only [kA, kB, B, H] at hcard_id hkA_le hkB_le hr_le_BkB ⊢; omega
  have hLen : 6 + A.card + kA ≤ 2 * n - 2 - r := by
    dsimp only [kA, kB, B, H] at hcard_id hkA_le hkB_le hr_le_BkB ⊢; omega
  have hZM_conv : (Finset.univ.filter (fun i : Fin 4 =>
      ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card = ZM := by congr 1
  have hBkB_eq : (Finset.univ \ (Finset.univ.image u ∪ A)).card +
      ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = B.card + kB := by
    congr 1
  obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
  have hG01 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1, by omega⟩) :=
    median_adj_succ hR ⟨r, by omega⟩ (by dsimp only; omega)
  by_cases hG02 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 2, by omega⟩)
  · by_cases hG03 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 3, by omega⟩)
    · -- Triple (1, 2, 3): pure L = 4 at [r, r+3]
      by_cases h0P : ∃ x ∈ A, D.Adj (u ⟨0, by decide⟩) x
      · have hmP_ge1 : 1 ≤ mP := Finset.one_le_card.mpr ⟨⟨0, by decide⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0P⟩⟩
        refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
          r (by omega) id Function.injective_id (fun i j hD => by
            obtain ⟨rfl, hj⟩ := hH_only i j hD
            fin_cases j
            · exact absurd rfl hj
            · exact hG01
            · exact hG02
            · exact hG03)
          0 (by decide) (fun _ h => by omega)
          (by dsimp only [mP, ZP, kA, B, H] at hZP_eq hmP_ge1 hLen ⊢; omega)
          0 (by decide) (fun _ h => by omega)
          (by rw [hZM_conv]; dsimp only [kB, B, H] at hr_eq ⊢; omega)
      · push Not at h0P
        refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
          r (by omega) id Function.injective_id (fun i j hD => by
            obtain ⟨rfl, hj⟩ := hH_only i j hD
            fin_cases j
            · exact absurd rfl hj
            · exact hG01
            · exact hG02
            · exact hG03)
          3 (by decide) (fun t ht i hi => by
            have hi' : i = t := hi
            rw [hi']; fin_cases t
            · exact h0P
            · exact hno1A
            · exact hno2A
            · simp at ht)
          (by dsimp only [mP, ZP, kA, B, H] at hZP_eq hLen ⊢; omega)
          0 (by decide) (fun _ h => by omega)
          (by rw [hZM_conv]; dsimp only [kB, B, H] at hr_eq ⊢; omega)
    · by_cases hG04 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 4, by omega⟩)
      · -- Triple (1, 2, 4): s4ppp_right_p3_eq_4 (p2 = 2) + s4ppp_left_and_glue (fL 3 = some 3)
        obtain ⟨gR, hgR_inj, hgR0, hgR1, hgR2, hgR3, hgR_A, hgR_adj⟩ :=
          s4ppp_right_p3_eq_4 u hu_inj h01 h02 h03 hH_only A hHA_disj hA_in hno_AB hno_AH hno1A hno2A
            hRkP hV hR r 2 (Or.inl rfl) (by omega) hG01 hG02 hG04 hG03 hLen
        let pos4 : Fin 4 → Fin 5 := fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨2, by decide⟩ | _ => ⟨4, by decide⟩
        have hpos4_inj : Function.Injective pos4 := fun i j h => by fin_cases i <;> fin_cases j <;> simp [pos4] at h ⊢
        have hfree_eq3 : ∀ t : Fin 5, (∀ i : Fin 4, pos4 i ≠ t) → t.val = 3 := by
          intro t ht
          have h0 : t.val ≠ 0 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos4, h]))
          have h1 : t.val ≠ 1 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos4, h]))
          have h2 : t.val ≠ 2 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos4, h]))
          have h4 : t.val ≠ 4 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos4, h]))
          have := t.isLt; omega
        let fL : Fin 5 → Option (Fin 4) := fun t => if t.val = 3 then some ⟨3, by decide⟩ else none
        refine s4ppp_left_and_glue u hu_inj A hHA_disj hB_out hno_AB hno_HB hRkM hV hL r 4 (by omega)
          pos4 hpos4_inj gR hgR_inj
          (fun i => by fin_cases i; exact hgR0; exact hgR1; exact hgR2; exact hgR3)
          hgR_A hgR_adj fL
          (fun t1 t2 ht1 ht2 _ _ _ => Fin.ext ((hfree_eq3 t1 ht1).trans (hfree_eq3 t2 ht2).symm))
          (fun t ht h hft => by
            have ht3 := hfree_eq3 t ht
            have hh3 : h = ⟨3, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht3] at hft; exact Option.some.inj hft.symm
            subst hh3; refine ⟨by simp only [pos4]; omega, ?_, hMandM3⟩
            have hm := median_adj_succ hR ⟨r + 3, by omega⟩ (by dsimp only; omega)
            exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
          ?_
        intro exhL hexh
        have hsub3 : exhL ⊆ {⟨3, by decide⟩} := fun i hi => by
          obtain ⟨t, ht, hft⟩ := hexh i hi
          have ht3 := hfree_eq3 t ht; dsimp only [fL] at hft; rw [if_pos ht3] at hft
          rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
        have he1 : exhL.card ≤ 1 := (Finset.card_le_card hsub3).trans (by rw [Finset.card_singleton])
        refine ⟨0, by decide, fun _ h => by omega, ?_⟩
        refine pure_plan_arith_bound (∅ : Finset (Fin 5)) (fun t ⟨ht, hf⟩ => by
          have ht3 := hfree_eq3 t ht; dsimp only [fL] at hf; rw [if_pos ht3] at hf; cases hf) ?_
        rw [Finset.card_empty, hZM_conv]; dsimp only [kB, B, H] at hr_eq ⊢; omega
      · -- Triple (1, 2, 5): m2_right_6_ge3 forces r -> r + 5!
        have hG05 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 5, by omega⟩) := by
          by_contra hnot05
          have hge3 := m2_right_6_ge3 hR r (by omega)
          have hsub : Finset.univ.filter (fun k : Fin 5 =>
              G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1 + k.val, by omega⟩)) ⊆ {⟨0, by decide⟩, ⟨1, by decide⟩} := by
            intro k hk; have hadj := (Finset.mem_filter.mp hk).2
            fin_cases k
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            · exact absurd hadj hG03
            · exact absurd hadj hG04
            · exact absurd hadj hnot05
          have hle := (Finset.card_le_card hsub).trans Finset.card_le_two; omega
        obtain ⟨gR, hgR_inj, hgR0, hgR1, hgR2, hgR3, hgR_A, hgR_adj⟩ :=
          s4ppp_right_p3_eq_5 u hu_inj hH_only A hHA_disj hA_in hno_AB hno_AH hno1A hno2A
            hRkP hV hR r 2 (Or.inl rfl) hr6 hG01 hG02 hG05 hG03 hG04 hLen
        let pos4 : Fin 4 → Fin 6 := fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨2, by decide⟩ | _ => ⟨5, by decide⟩
        have hpos4_inj : Function.Injective pos4 := fun i j h => by fin_cases i <;> fin_cases j <;> simp [pos4] at h ⊢
        have hfree34 : ∀ t : Fin 6, (∀ i : Fin 4, pos4 i ≠ t) → t.val = 3 ∨ t.val = 4 := by
          intro t ht
          have h0 : t.val ≠ 0 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos4, h]))
          have h1 : t.val ≠ 1 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos4, h]))
          have h2 : t.val ≠ 2 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos4, h]))
          have h5 : t.val ≠ 5 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos4, h]))
          have := t.isLt; omega
        let fL : Fin 6 → Option (Fin 4) := fun t => if t.val = 4 then some ⟨3, by decide⟩ else none
        refine s4ppp_left_and_glue u hu_inj A hHA_disj hB_out hno_AB hno_HB hRkM hV hL r 5 (by omega)
          pos4 hpos4_inj gR hgR_inj
          (fun i => by fin_cases i; exact hgR0; exact hgR1; exact hgR2; exact hgR3)
          hgR_A hgR_adj fL
          (fun t1 t2 _ _ _ hf1 hf2 => by
            have h1 : t1.val = 4 := by by_contra hne; dsimp only [fL] at hf1; rw [if_neg hne] at hf1; cases hf1
            have h2 : t2.val = 4 := by by_contra hne; dsimp only [fL] at hf2; rw [if_neg hne] at hf2; cases hf2
            exact Fin.ext (h1.trans h2.symm))
          (fun t _ h hft => by
            have ht4 : t.val = 4 := by by_contra hne; dsimp only [fL] at hft; rw [if_neg hne] at hft; cases hft
            have hh3 : h = ⟨3, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht4] at hft; exact Option.some.inj hft.symm
            subst hh3; refine ⟨by simp only [pos4]; omega, ?_, hMandM3⟩
            have hm := median_adj_succ hR ⟨r + 4, by omega⟩ (by dsimp only; omega)
            exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
          ?_
        intro exhL hexh
        have hsub3 : exhL ⊆ {⟨3, by decide⟩} := fun i hi => by
          obtain ⟨t, _, hft⟩ := hexh i hi
          have ht4 : t.val = 4 := by by_contra hne; dsimp only [fL] at hft; rw [if_neg hne] at hft; cases hft
          dsimp only [fL] at hft; rw [if_pos ht4] at hft; rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
        have hdum_mem : ∀ t : Fin 6, ((∀ i : Fin 4, pos4 i ≠ t) ∧ fL t = none) → t ∈ ({⟨3, by decide⟩} : Finset (Fin 6)) := by
          intro t ⟨ht, hf⟩; rw [Finset.mem_singleton]
          rcases hfree34 t ht with h3 | h4
          · exact Fin.ext h3
          · exfalso; dsimp only [fL] at hf; rw [if_pos h4] at hf; cases hf
        by_cases h3in : ⟨3, by decide⟩ ∈ exhL
        · have he1 : exhL.card ≤ 1 := (Finset.card_le_card hsub3).trans (by rw [Finset.card_singleton])
          refine ⟨1, by decide, fun t ht => ⟨fun i hi => Or.inr (by
            have ht5 : t = ⟨5, by decide⟩ := Fin.ext (by have := t.isLt; simp only; omega)
            have hi3 : i = ⟨3, by decide⟩ := hpos4_inj (hi.trans ht5)
            exact hi3 ▸ h3in), fun hfree => by
            exfalso; rcases hfree34 t hfree with h3 | h4 <;> omega⟩, ?_⟩
          refine pure_plan_arith_bound ({⟨3, by decide⟩} : Finset (Fin 6)) hdum_mem ?_
          rw [Finset.card_singleton, hZM_conv]; dsimp only [kB, B, H] at hr_eq ⊢; omega
        · have he0 : exhL.card = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro i hi; exact h3in (Finset.mem_singleton.mp (hsub3 hi) ▸ hi)
          refine ⟨0, by decide, fun _ h => by omega, ?_⟩
          refine pure_plan_arith_bound ({⟨3, by decide⟩} : Finset (Fin 6)) hdum_mem ?_
          rw [Finset.card_singleton, he0, hZM_conv]; dsimp only [kB, B, H] at hr_eq ⊢; omega
  · -- ¬(0 -> 2): M2-Right on [r, r+3] forces 0 -> 3!
    have hG03 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 3, by omega⟩) := by
      by_contra hnot03; exact hG02 (m2_right_4 hR r (by omega) hnot03)
    by_cases hG04 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 4, by omega⟩)
    · -- Triple (1, 3, 4): s4ppp_right_p3_eq_4 (p2 = 3) + s4ppp_left_and_glue (fL 2 = some 2)
      obtain ⟨gR, hgR_inj, hgR0, hgR1, hgR2, hgR3, hgR_A, hgR_adj⟩ :=
        s4ppp_right_p3_eq_4 u hu_inj h01 h02 h03 hH_only A hHA_disj hA_in hno_AB hno_AH hno1A hno2A
          hRkP hV hR r 3 (Or.inr rfl) (by omega) hG01 hG03 hG04 hG02 hLen
      let pos4 : Fin 4 → Fin 5 := fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨4, by decide⟩
      have hpos4_inj : Function.Injective pos4 := fun i j h => by fin_cases i <;> fin_cases j <;> simp [pos4] at h ⊢
      have hfree_eq2 : ∀ t : Fin 5, (∀ i : Fin 4, pos4 i ≠ t) → t.val = 2 := by
        intro t ht
        have h0 : t.val ≠ 0 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos4, h]))
        have h1 : t.val ≠ 1 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos4, h]))
        have h3 : t.val ≠ 3 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos4, h]))
        have h4 : t.val ≠ 4 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos4, h]))
        have := t.isLt; omega
      let fL : Fin 5 → Option (Fin 4) := fun t => if t.val = 2 then some ⟨2, by decide⟩ else none
      refine s4ppp_left_and_glue u hu_inj A hHA_disj hB_out hno_AB hno_HB hRkM hV hL r 4 (by omega)
        pos4 hpos4_inj gR hgR_inj
        (fun i => by fin_cases i; exact hgR0; exact hgR1; exact hgR2; exact hgR3)
        hgR_A hgR_adj fL
        (fun t1 t2 ht1 ht2 _ _ _ => Fin.ext ((hfree_eq2 t1 ht1).trans (hfree_eq2 t2 ht2).symm))
        (fun t ht h hft => by
          have ht2 := hfree_eq2 t ht
          have hh2 : h = ⟨2, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht2] at hft; exact Option.some.inj hft.symm
          subst hh2; refine ⟨by simp only [pos4]; omega, ?_, hMandM2⟩
          have hm := median_adj_succ hR ⟨r + 2, by omega⟩ (by dsimp only; omega)
          exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
        ?_
      intro exhL hexh
      have hsub2 : exhL ⊆ {⟨2, by decide⟩} := fun i hi => by
        obtain ⟨t, ht, hft⟩ := hexh i hi
        have ht2 := hfree_eq2 t ht; dsimp only [fL] at hft; rw [if_pos ht2] at hft
        rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
      have he1 : exhL.card ≤ 1 := (Finset.card_le_card hsub2).trans (by rw [Finset.card_singleton])
      refine ⟨0, by decide, fun _ h => by omega, ?_⟩
      refine pure_plan_arith_bound (∅ : Finset (Fin 5)) (fun t ⟨ht, hf⟩ => by
        have ht2 := hfree_eq2 t ht; dsimp only [fL] at hf; rw [if_pos ht2] at hf; cases hf) ?_
      rw [Finset.card_empty, hZM_conv]; dsimp only [kB, B, H] at hr_eq ⊢; omega
    · -- Triple (1, 3, 5): m2_right_6_ge3 forces r -> r + 5!
      have hG05 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 5, by omega⟩) := by
        by_contra hnot05
        have hge3 := m2_right_6_ge3 hR r (by omega)
        have hsub : Finset.univ.filter (fun k : Fin 5 =>
            G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1 + k.val, by omega⟩)) ⊆ {⟨0, by decide⟩, ⟨2, by decide⟩} := by
          intro k hk; have hadj := (Finset.mem_filter.mp hk).2
          fin_cases k
          · exact Finset.mem_insert_self _ _
          · exact absurd hadj hG02
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · exact absurd hadj hG04
          · exact absurd hadj hnot05
        have hle := (Finset.card_le_card hsub).trans Finset.card_le_two; omega
      obtain ⟨gR, hgR_inj, hgR0, hgR1, hgR2, hgR3, hgR_A, hgR_adj⟩ :=
        s4ppp_right_p3_eq_5 u hu_inj hH_only A hHA_disj hA_in hno_AB hno_AH hno1A hno2A
          hRkP hV hR r 3 (Or.inr rfl) hr6 hG01 hG03 hG05 hG02 hG04 hLen
      let pos4 : Fin 4 → Fin 6 := fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨5, by decide⟩
      have hpos4_inj : Function.Injective pos4 := fun i j h => by fin_cases i <;> fin_cases j <;> simp [pos4] at h ⊢
      have hfree24 : ∀ t : Fin 6, (∀ i : Fin 4, pos4 i ≠ t) → t.val = 2 ∨ t.val = 4 := by
        intro t ht
        have h0 : t.val ≠ 0 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos4, h]))
        have h1 : t.val ≠ 1 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos4, h]))
        have h3 : t.val ≠ 3 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos4, h]))
        have h5 : t.val ≠ 5 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos4, h]))
        have := t.isLt; omega
      let fL : Fin 6 → Option (Fin 4) := fun t => if t.val = 2 then some ⟨2, by decide⟩ else if t.val = 4 then some ⟨3, by decide⟩ else none
      refine s4ppp_left_and_glue u hu_inj A hHA_disj hB_out hno_AB hno_HB hRkM hV hL r 5 (by omega)
        pos4 hpos4_inj gR hgR_inj
        (fun i => by fin_cases i; exact hgR0; exact hgR1; exact hgR2; exact hgR3)
        hgR_A hgR_adj fL
        (fun t1 t2 ht1 ht2 _ hf1 hf2 => by
          rcases hfree24 t1 ht1 with h1 | h1 <;> rcases hfree24 t2 ht2 with h2 | h2
          · exact Fin.ext (h1.trans h2.symm)
          · exfalso; dsimp only [fL] at hf1 hf2; rw [if_pos h1] at hf1; rw [if_neg (by omega), if_pos h2] at hf2
            have := Option.some.inj (hf1.trans hf2.symm); simp at this
          · exfalso; dsimp only [fL] at hf1 hf2; rw [if_neg (by omega), if_pos h1] at hf1; rw [if_pos h2] at hf2
            have := Option.some.inj (hf1.trans hf2.symm); simp at this
          · exact Fin.ext (h1.trans h2.symm))
        (fun t ht h hft => by
          rcases hfree24 t ht with ht2 | ht4
          · have hh2 : h = ⟨2, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht2] at hft; exact Option.some.inj hft.symm
            subst hh2; refine ⟨by simp only [pos4]; omega, ?_, hMandM2⟩
            have hm := median_adj_succ hR ⟨r + 2, by omega⟩ (by dsimp only; omega)
            exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta)
          · have hh3 : h = ⟨3, by decide⟩ := by dsimp only [fL] at hft; rw [if_neg (by omega), if_pos ht4] at hft; exact Option.some.inj hft.symm
            subst hh3; refine ⟨by simp only [pos4]; omega, ?_, hMandM3⟩
            have hm := median_adj_succ hR ⟨r + 4, by omega⟩ (by dsimp only; omega)
            exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
        ?_
      intro exhL hexh
      have hsub23 : exhL ⊆ {⟨2, by decide⟩, ⟨3, by decide⟩} := fun i hi => by
        obtain ⟨t, ht, hft⟩ := hexh i hi
        rcases hfree24 t ht with h2 | h4
        · dsimp only [fL] at hft; rw [if_pos h2] at hft; rw [Option.some.inj hft.symm]; exact Finset.mem_insert_self _ _
        · dsimp only [fL] at hft; rw [if_neg (by omega), if_pos h4] at hft; rw [Option.some.inj hft.symm]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have he2 : exhL.card ≤ 2 := (Finset.card_le_card hsub23).trans Finset.card_le_two
      refine ⟨0, by decide, fun _ h => by omega, ?_⟩
      refine pure_plan_arith_bound (∅ : Finset (Fin 6)) (fun t ⟨ht, hf⟩ => by
        rcases hfree24 t ht with h2 | h4
        · dsimp only [fL] at hf; rw [if_pos h2] at hf; cases hf
        · dsimp only [fL] at hf; rw [if_neg (by omega), if_pos h4] at hf; cases hf) ?_
      rw [Finset.card_empty, hZM_conv]; dsimp only [kB, B, H] at hr_eq ⊢; omega

-- Subcase 5B: 1, 2 in maskP — modular shared plan helpers + Families F1, F2, F3!
lemma s4ppp_ge2_P123
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hRkP : ∃ rkP : ↥(Finset.univ.image u ∪ A) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y)
    (hRkM : ∃ rkM : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))),
        x.1 ∈ Finset.univ \ (Finset.univ.image u ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (lo : ℕ) (hhi : lo + 3 < 2 * n - 2)
    (ha2 : G.Adj (σ ⟨lo, by omega⟩) (σ ⟨lo + 2, by omega⟩))
    (ha3 : G.Adj (σ ⟨lo, by omega⟩) (σ ⟨lo + 3, by omega⟩))
    (hRb : 4 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
      (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ (2 * n - 2 - lo) + 1)
    (hLb : 4 + (Finset.univ \ (Finset.univ.image u ∪ A)).card +
      ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card +
      (Finset.univ.filter (fun i : Fin 4 =>
        ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ (lo + 4) + 1) :
    Embeds D G := by
  classical
  refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
    lo hhi id Function.injective_id (fun i j hD => by
      obtain ⟨rfl, hj⟩ := hH_only i j hD
      fin_cases j
      · exact absurd rfl hj
      · exact median_adj_succ hR ⟨lo, by omega⟩ (by dsimp only; omega)
      · exact ha2
      · exact ha3)
    0 (by decide) (fun _ h => by omega) (by convert hRb using 1)
    0 (by decide) (fun _ h => by omega) (by convert hLb using 1)

lemma s4ppp_ge2_P4
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hRkP : ∃ rkP : ↥(Finset.univ.image u ∪ A) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y)
    (hRkM : ∃ rkM : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))),
        x.1 ∈ Finset.univ \ (Finset.univ.image u ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    (hMandM2 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨2, by decide⟩))
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (r : ℕ) (hr : r + 4 < 2 * n - 2)
    (h03 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 3, by omega⟩))
    (h04 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 4, by omega⟩))
    (qR : ℕ) (hqR : qR ≤ 1)
    (hqR0 : qR = 1 → ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x)
    (hRb : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
      (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ (2 * n - 2 - r) + 1 + qR)
    (hLb : 5 + (Finset.univ \ (Finset.univ.image u ∪ A)).card +
      ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card +
      (Finset.univ.filter (fun i : Fin 4 =>
        ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ (r + 5) + 1) :
    Embeds D G := by
  classical
  let pos : Fin 4 → Fin (r + 4 - r + 1) := fun i =>
    match i.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨4, by omega⟩
  have hpos_inj : Function.Injective pos := fun i j h => by
    have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp [pos] at hv ⊢
  have hfree2 : ∀ t : Fin (r + 4 - r + 1), (∀ i : Fin 4, pos i ≠ t) → t.val = 2 := by
    intro t ht
    have h0 : t.val ≠ 0 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos, h]))
    have h1 : t.val ≠ 1 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos, h]))
    have h3 : t.val ≠ 3 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos, h]))
    have h4 : t.val ≠ 4 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos, h]))
    have := t.isLt; omega
  let fL : Fin (r + 4 - r + 1) → Option (Fin 4) := fun t => if t.val = 2 then some ⟨2, by decide⟩ else none
  refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
    hV hR hL r (r + 4) (by omega) hr pos hpos_inj (fun i j hD => by
      obtain ⟨rfl, hj⟩ := hH_only i j hD
      fin_cases j
      · exact absurd rfl hj
      · exact median_adj_succ hR ⟨r, by omega⟩ (by dsimp only; omega)
      · exact h03
      · exact h04)
    (fun _ => none) fL (fun _ _ => Or.inl rfl)
    (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    (fun t1 t2 ht1 ht2 _ _ _ => Fin.ext ((hfree2 t1 ht1).trans (hfree2 t2 ht2).symm))
    (fun t ht h hft => by
      have ht2 := hfree2 t ht
      have hh2 : h = ⟨2, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht2] at hft; exact Option.some.inj hft.symm
      subst hh2; refine ⟨by simp only [pos]; omega, ?_, hMandM2⟩
      have hm := median_adj_succ hR ⟨r + 2, by omega⟩ (by dsimp only; omega)
      exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
    ?_ ?_
  · intro exhR hexh
    have he0 : exhR.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro i hi; obtain ⟨_, _, hc⟩ := hexh i hi; cases hc
    refine ⟨qR, by omega, fun t ht => ⟨fun i hi => Or.inl (by
      have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
      · exact hqR0 (by omega)
      · omega
      · omega
      · omega), fun _ => rfl⟩, ?_⟩
    refine pure_plan_arith_bound ({⟨2, by omega⟩} : Finset (Fin (r + 4 - r + 1)))
      (fun t ht => Finset.mem_singleton.mpr (Fin.ext (hfree2 t ht.1))) ?_
    rw [Finset.card_singleton, he0]
    have hRb' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
        (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ (2 * n - 2 - r) + 1 + qR := by convert hRb
    omega
  · intro exhL hexh
    have he1 : exhL.card ≤ 1 := by
      have hsub : exhL ⊆ {⟨2, by decide⟩} := fun i hi => by
        obtain ⟨t, ht, hft⟩ := hexh i hi
        have ht2 := hfree2 t ht; dsimp only [fL] at hft; rw [if_pos ht2] at hft
        rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
      exact (Finset.card_le_card hsub).trans (by rw [Finset.card_singleton])
    refine ⟨0, by omega, fun _ h => by omega, ?_⟩
    refine pure_plan_arith_bound (∅ : Finset (Fin (r + 4 - r + 1)))
      (fun t ⟨ht, hf⟩ => by have ht2 := hfree2 t ht; dsimp only [fL] at hf; rw [if_pos ht2] at hf; cases hf) ?_
    rw [Finset.card_empty]
    have hLb' : 5 + (Finset.univ \ (Finset.univ.image u ∪ A)).card +
        ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card +
        (Finset.univ.filter (fun i : Fin 4 =>
          ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ (r + 5) + 1 := by convert hLb
    omega

lemma s4ppp_ge2_P5
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hRkP : ∃ rkP : ↥(Finset.univ.image u ∪ A) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y)
    (hRkM : ∃ rkM : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))),
        x.1 ∈ Finset.univ \ (Finset.univ.image u ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    (h1P : ∃ x ∈ A, D.Adj (u ⟨1, by decide⟩) x)
    (hMandM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (r : ℕ) (hr : r + 5 < 2 * n - 2)
    (h03 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 3, by omega⟩))
    (h05 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 5, by omega⟩))
    (hRb : ((∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x) ∧
        6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
        (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ (2 * n - 2 - r) + 2) ∨
      7 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
        (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ (2 * n - 2 - r) + 1)
    (hLb : 6 + (Finset.univ \ (Finset.univ.image u ∪ A)).card +
      ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card +
      (Finset.univ.filter (fun i : Fin 4 =>
        ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ (r + 6) + 1) :
    Embeds D G := by
  classical
  let pos : Fin 4 → Fin (r + 5 - r + 1) := fun i =>
    match i.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨5, by omega⟩
  have hpos_inj : Function.Injective pos := fun i j h => by
    have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp [pos] at hv ⊢
  have hfree24 : ∀ t : Fin (r + 5 - r + 1), (∀ i : Fin 4, pos i ≠ t) → t.val = 2 ∨ t.val = 4 := by
    intro t ht
    have h0 : t.val ≠ 0 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos, h]))
    have h1 : t.val ≠ 1 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos, h]))
    have h3 : t.val ≠ 3 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos, h]))
    have h5 : t.val ≠ 5 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos, h]))
    have := t.isLt; omega
  let fR : Fin (r + 5 - r + 1) → Option (Fin 4) := fun t => if t.val = 2 then some ⟨1, by decide⟩ else none
  let fL : Fin (r + 5 - r + 1) → Option (Fin 4) := fun t => if t.val = 4 then some ⟨3, by decide⟩ else none
  refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
    hV hR hL r (r + 5) (by omega) hr pos hpos_inj (fun i j hD => by
      obtain ⟨rfl, hj⟩ := hH_only i j hD
      fin_cases j
      · exact absurd rfl hj
      · exact median_adj_succ hR ⟨r, by omega⟩ (by dsimp only; omega)
      · exact h03
      · exact h05)
    fR fL (fun t ht => by rcases hfree24 t ht with h2 | h4; right; simp [fL, h2]; left; simp [fR, h4])
    (fun t1 t2 _ _ _ hf1 hf2 => by
      have h1 : t1.val = 2 := by by_contra hne; dsimp only [fR] at hf1; rw [if_neg hne] at hf1; cases hf1
      have h2 : t2.val = 2 := by by_contra hne; dsimp only [fR] at hf2; rw [if_neg hne] at hf2; cases hf2
      exact Fin.ext (h1.trans h2.symm))
    (fun t _ h hft => by
      have ht2 : t.val = 2 := by by_contra hne; dsimp only [fR] at hft; rw [if_neg hne] at hft; cases hft
      have hh1 : h = ⟨1, by decide⟩ := by dsimp only [fR] at hft; rw [if_pos ht2] at hft; exact Option.some.inj hft.symm
      subst hh1; refine ⟨by simp only [pos]; omega, ?_, h1P⟩
      have hm := median_adj_succ hR ⟨r + 1, by omega⟩ (by dsimp only; omega)
      exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta; omega))
    (fun t1 t2 _ _ _ hf1 hf2 => by
      have h1 : t1.val = 4 := by by_contra hne; dsimp only [fL] at hf1; rw [if_neg hne] at hf1; cases hf1
      have h2 : t2.val = 4 := by by_contra hne; dsimp only [fL] at hf2; rw [if_neg hne] at hf2; cases hf2
      exact Fin.ext (h1.trans h2.symm))
    (fun t _ h hft => by
      have ht4 : t.val = 4 := by by_contra hne; dsimp only [fL] at hft; rw [if_neg hne] at hft; cases hft
      have hh3 : h = ⟨3, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht4] at hft; exact Option.some.inj hft.symm
      subst hh3; refine ⟨by simp only [pos]; omega, ?_, hMandM3⟩
      have hm := median_adj_succ hR ⟨r + 4, by omega⟩ (by dsimp only; omega)
      exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
    ?_ ?_
  · intro exhR hexh
    have hsub1 : exhR ⊆ {⟨1, by decide⟩} := fun i hi => by
      obtain ⟨t, _, hft⟩ := hexh i hi
      have ht2 : t.val = 2 := by by_contra hne; dsimp only [fR] at hft; rw [if_neg hne] at hft; cases hft
      dsimp only [fR] at hft; rw [if_pos ht2] at hft; rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
    have he1 : exhR.card ≤ 1 := (Finset.card_le_card hsub1).trans (by rw [Finset.card_singleton])
    have hdumR : ∀ t : Fin (r + 5 - r + 1), ((∀ i : Fin 4, pos i ≠ t) ∧ fR t = none) → t ∈ ({⟨4, by omega⟩} : Finset (Fin (r + 5 - r + 1))) := by
      intro t ⟨ht, hf⟩; rw [Finset.mem_singleton]
      rcases hfree24 t ht with h2 | h4
      · exfalso; dsimp only [fR] at hf; rw [if_pos h2] at hf; cases hf
      · exact Fin.ext h4
    rcases hRb with ⟨hno0A, hRb'⟩ | hRb'
    · by_cases h1in : ⟨1, by decide⟩ ∈ exhR
      · refine ⟨2, by omega, fun t ht => ⟨fun i hi => by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · exact Or.inl hno0A
          · exact Or.inr h1in
          · omega
          · omega, fun hfree => by exfalso; rcases hfree24 t hfree with h2 | h4 <;> omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨4, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumR ?_
        rw [Finset.card_singleton]
        have hR0 : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
            (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ (2 * n - 2 - r) + 2 := by convert hRb'
        omega
      · have he0 : exhR.card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro i hi; exact h1in (Finset.mem_singleton.mp (hsub1 hi) ▸ hi)
        refine ⟨1, by omega, fun t ht => ⟨fun i hi => Or.inl (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · exact hno0A
          · omega
          · omega
          · omega), fun hfree => by exfalso; rcases hfree24 t hfree with h2 | h4 <;> omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨4, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumR ?_
        rw [Finset.card_singleton, he0]
        have hR0 : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
            (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ (2 * n - 2 - r) + 2 := by convert hRb'
        omega
    · refine ⟨0, by omega, fun _ h => by omega, ?_⟩
      refine pure_plan_arith_bound ({⟨4, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumR ?_
      rw [Finset.card_singleton]
      have hR0 : 7 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
          (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ (2 * n - 2 - r) + 1 := by convert hRb'
      omega
  · intro exhL hexh
    have hsub3 : exhL ⊆ {⟨3, by decide⟩} := fun i hi => by
      obtain ⟨t, _, hft⟩ := hexh i hi
      have ht4 : t.val = 4 := by by_contra hne; dsimp only [fL] at hft; rw [if_neg hne] at hft; cases hft
      dsimp only [fL] at hft; rw [if_pos ht4] at hft; rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
    have hdumL : ∀ t : Fin (r + 5 - r + 1), ((∀ i : Fin 4, pos i ≠ t) ∧ fL t = none) → t ∈ ({⟨2, by omega⟩} : Finset (Fin (r + 5 - r + 1))) := by
      intro t ⟨ht, hf⟩; rw [Finset.mem_singleton]
      rcases hfree24 t ht with h2 | h4
      · exact Fin.ext h2
      · exfalso; dsimp only [fL] at hf; rw [if_pos h4] at hf; cases hf
    by_cases h3in : ⟨3, by decide⟩ ∈ exhL
    · have he1 : exhL.card ≤ 1 := (Finset.card_le_card hsub3).trans (by rw [Finset.card_singleton])
      refine ⟨1, by omega, fun t ht => ⟨fun i hi => Or.inr (by
        have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
        · omega
        · omega
        · omega
        · exact h3in), fun hfree => by exfalso; rcases hfree24 t hfree with h2 | h4 <;> omega⟩, ?_⟩
      refine pure_plan_arith_bound ({⟨2, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumL ?_
      rw [Finset.card_singleton]
      have hL0 : 6 + (Finset.univ \ (Finset.univ.image u ∪ A)).card +
          ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card +
          (Finset.univ.filter (fun i : Fin 4 =>
            ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ (r + 6) + 1 := by convert hLb
      omega
    · have he0 : exhL.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro i hi; exact h3in (Finset.mem_singleton.mp (hsub3 hi) ▸ hi)
      refine ⟨0, by omega, fun _ h => by omega, ?_⟩
      refine pure_plan_arith_bound ({⟨2, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumL ?_
      rw [Finset.card_singleton, he0]
      have hL0 : 6 + (Finset.univ \ (Finset.univ.image u ∪ A)).card +
          ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card +
          (Finset.univ.filter (fun i : Fin 4 =>
            ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ (r + 6) + 1 := by convert hLb
      omega

-- Family F2: 0, 1, 2 in maskP and 0, 1, 2, 3 in maskM (delta = -1, r = B + kB - 1)
lemma embeds_heart_four_S4ppp_F2
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hRkP : ∃ rkP : ↥(Finset.univ.image u ∪ A) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y)
    (hRkM : ∃ rkM : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))),
        x.1 ∈ Finset.univ \ (Finset.univ.image u ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    (h0P : ∃ x ∈ A, D.Adj (u ⟨0, by decide⟩) x)
    (h1P : ∃ x ∈ A, D.Adj (u ⟨1, by decide⟩) x)
    (h2P : ∃ x ∈ A, D.Adj (u ⟨2, by decide⟩) x)
    (h0M : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨0, by decide⟩))
    (h1M : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨1, by decide⟩))
    (h2M : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨2, by decide⟩))
    (h3M : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    (r : ℕ) (hr : r + 5 < 2 * n - 2)
    (hAkA : 7 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r)
    (hBkB : (Finset.univ \ (Finset.univ.image u ∪ A)).card +
      ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r + 1)
    (hZP1 : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1)
    (hZM0 : (Finset.univ.filter (fun i : Fin 4 =>
      ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card = 0)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card) :
    Embeds D G := by
  classical
  rcases lmo6_F2 hG hR hL r (by omega) with
    ⟨a02, a03⟩ | ⟨a13, a14⟩ | ⟨a24, a25⟩ | ⟨a03, a04⟩ | ⟨a03, a05⟩ | ⟨a35, a30, a13, a24⟩
  · exact s4ppp_ge2_P123 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      r (by omega) a02 a03 (by omega) (by omega)
  · exact s4ppp_ge2_P123 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      (r + 1) (by omega) (by exact sigma_adj_congr a13 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
      (by exact sigma_adj_congr a14 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)) (by omega) (by omega)
  · exact s4ppp_ge2_P123 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      (r + 2) (by omega) (by exact sigma_adj_congr a24 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
      (by exact sigma_adj_congr a25 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)) (by omega) (by omega)
  · exact s4ppp_ge2_P4 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM h2M hV hR hL
      r (by omega) a03 a04 0 (by decide) (fun h => by omega) (by omega) (by omega)
  · exact s4ppp_ge2_P5 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM h1P h3M hV hR hL
      r hr a03 a05 (Or.inr (by omega)) (by omega)
  · -- Plan P6': [r, r+5], pos = (3, 4, 5, 0), F = {1, 2}, fR = none, fL(1) = some 0, fL(2) = some 1!
    let pos : Fin 4 → Fin (r + 5 - r + 1) := fun i =>
      match i.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨4, by omega⟩ | 2 => ⟨5, by omega⟩ | _ => ⟨0, by omega⟩
    have hpos_inj : Function.Injective pos := fun i j h => by
      have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp [pos] at hv ⊢
    have hfree12 : ∀ t : Fin (r + 5 - r + 1), (∀ i : Fin 4, pos i ≠ t) → t.val = 1 ∨ t.val = 2 := by
      intro t ht
      have h0 : t.val ≠ 0 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h3 : t.val ≠ 3 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h4 : t.val ≠ 4 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h5 : t.val ≠ 5 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos, h]))
      have := t.isLt; omega
    let fL : Fin (r + 5 - r + 1) → Option (Fin 4) := fun t => if t.val = 1 then some ⟨0, by decide⟩ else if t.val = 2 then some ⟨1, by decide⟩ else none
    refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
      hV hR hL r (r + 5) (by omega) hr pos hpos_inj (fun i j hD => by
        obtain ⟨rfl, hj⟩ := hH_only i j hD
        fin_cases j
        · exact absurd rfl hj
        · exact median_adj_succ hR ⟨r + 3, by omega⟩ (by dsimp only; omega)
        · exact a35
        · exact a30)
      (fun _ => none) fL (fun _ _ => Or.inl rfl)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun t1 t2 ht1 ht2 _ hf1 hf2 => by
        rcases hfree12 t1 ht1 with h1 | h1 <;> rcases hfree12 t2 ht2 with h2 | h2
        · exact Fin.ext (h1.trans h2.symm)
        · exfalso; dsimp only [fL] at hf1 hf2; rw [if_pos h1] at hf1; rw [if_neg (by omega), if_pos h2] at hf2
          have := Option.some.inj (hf1.trans hf2.symm); simp at this
        · exfalso; dsimp only [fL] at hf1 hf2; rw [if_neg (by omega), if_pos h1] at hf1; rw [if_pos h2] at hf2
          have := Option.some.inj (hf1.trans hf2.symm); simp at this
        · exact Fin.ext (h1.trans h2.symm))
      (fun t ht h hft => by
        rcases hfree12 t ht with ht1 | ht2
        · have hh0 : h = ⟨0, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht1] at hft; exact Option.some.inj hft.symm
          subst hh0; refine ⟨by simp only [pos]; omega, ?_, h0M⟩
          exact sigma_adj_congr a13 (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta)
        · have hh1 : h = ⟨1, by decide⟩ := by dsimp only [fL] at hft; rw [if_neg (by omega), if_pos ht2] at hft; exact Option.some.inj hft.symm
          subst hh1; refine ⟨by simp only [pos]; omega, ?_, h1M⟩
          exact sigma_adj_congr a24 (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
      ?_ ?_
    · intro exhR hexh
      have he0 : exhR.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro i hi; obtain ⟨_, _, hc⟩ := hexh i hi; cases hc
      have hdum : ∀ t : Fin (r + 5 - r + 1), ((∀ i : Fin 4, pos i ≠ t) ∧ (none : Option (Fin 4)) = none) →
          t ∈ ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (r + 5 - r + 1))) := by
        intro t ht; rcases hfree12 t ht.1 with h1 | h2
        · rw [Finset.mem_insert]; exact Or.inl (Fin.ext h1)
        · rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Fin.ext h2)
      have hcard2 : ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (r + 5 - r + 1))).card ≤ 2 := Finset.card_le_two
      by_cases h3P : ∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x
      · have hZP0 : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro i _ hi
          fin_cases i
          · obtain ⟨x, hx, h⟩ := h0P; exact hi x hx h
          · obtain ⟨x, hx, h⟩ := h1P; exact hi x hx h
          · obtain ⟨x, hx, h⟩ := h2P; exact hi x hx h
          · obtain ⟨x, hx, h⟩ := h3P; exact hi x hx h
        refine ⟨0, by omega, fun _ h => by omega, ?_⟩
        refine pure_plan_arith_bound ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdum ?_
        rw [he0]; have hZP0' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card = 0 := by convert hZP0
        have hA' : 7 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        omega
      · push Not at h3P
        refine ⟨3, by omega, fun t ht => ⟨fun i hi => Or.inl (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · omega
          · omega
          · omega
          · exact h3P), fun _ => rfl⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdum ?_
        rw [he0]; have hZP1' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1 := by convert hZP1
        have hA' : 7 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        omega
    · intro exhL hexh
      have he2 : exhL.card ≤ 2 := by
        have hsub : exhL ⊆ {⟨0, by decide⟩, ⟨1, by decide⟩} := fun i hi => by
          obtain ⟨t, ht, hft⟩ := hexh i hi
          rcases hfree12 t ht with h1 | h2
          · dsimp only [fL] at hft; rw [if_pos h1] at hft; rw [Option.some.inj hft.symm]; exact Finset.mem_insert_self _ _
          · dsimp only [fL] at hft; rw [if_neg (by omega), if_pos h2] at hft; rw [Option.some.inj hft.symm]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
      refine ⟨0, by omega, fun _ h => by omega, ?_⟩
      refine pure_plan_arith_bound (∅ : Finset (Fin (r + 5 - r + 1))) (fun t ⟨ht, hf⟩ => by
        rcases hfree12 t ht with h1 | h2
        · dsimp only [fL] at hf; rw [if_pos h1] at hf; cases hf
        · dsimp only [fL] at hf; rw [if_neg (by omega), if_pos h2] at hf; cases hf) ?_
      rw [Finset.card_empty]
      have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card + ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r + 1 := by convert hBkB
      have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card = 0 := by convert hZM0
      omega

-- Family F3: 0, 1, 2 in maskP and 0 not in maskM (delta = 0, r = B + kB)
lemma embeds_heart_four_S4ppp_F3
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hRkP : ∃ rkP : ↥(Finset.univ.image u ∪ A) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y)
    (hRkM : ∃ rkM : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))),
        x.1 ∈ Finset.univ \ (Finset.univ.image u ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    (h0P : ∃ x ∈ A, D.Adj (u ⟨0, by decide⟩) x)
    (h1P : ∃ x ∈ A, D.Adj (u ⟨1, by decide⟩) x)
    (h2P : ∃ x ∈ A, D.Adj (u ⟨2, by decide⟩) x)
    (h2M : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨2, by decide⟩))
    (h3M : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    (r : ℕ) (hr : r + 5 < 2 * n - 2)
    (hAkA : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r)
    (hBkB : (Finset.univ \ (Finset.univ.image u ∪ A)).card +
      ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r)
    (hZP1 : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1)
    (hZM1 : (Finset.univ.filter (fun i : Fin 4 =>
      ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card) :
    Embeds D G := by
  classical
  have hZP0_of_3 : (∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x) →
      (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card = 0 := by
    intro h3P; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro i _ hi
    fin_cases i
    · obtain ⟨x, hx, h⟩ := h0P; exact hi x hx h
    · obtain ⟨x, hx, h⟩ := h1P; exact hi x hx h
    · obtain ⟨x, hx, h⟩ := h2P; exact hi x hx h
    · obtain ⟨x, hx, h⟩ := h3P; exact hi x hx h
  rcases lmo6_F3 hG hR hL r (by omega) with
    ⟨a02, a03⟩ | ⟨a13, a14⟩ | ⟨a24, a25⟩ | ⟨a03, a04⟩ | ⟨a02, a04⟩ | ⟨a35, a31⟩ | ⟨a20, a25⟩ | ⟨a41, a40, a35⟩
  · exact s4ppp_ge2_P123 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      r (by omega) a02 a03 (by omega) (by omega)
  · exact s4ppp_ge2_P123 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      (r + 1) (by omega) (by exact sigma_adj_congr a13 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
      (by exact sigma_adj_congr a14 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)) (by omega) (by omega)
  · exact s4ppp_ge2_P123 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      (r + 2) (by omega) (by exact sigma_adj_congr a24 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
      (by exact sigma_adj_congr a25 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)) (by omega) (by omega)
  · exact s4ppp_ge2_P4 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM h2M hV hR hL
      r (by omega) a03 a04 0 (by decide) (fun h => by omega) (by omega) (by omega)
  · -- Plan Q5: [r, r+4], pos = (0, 1, 2, 4), F = {3}, fR = none, fL(3) = some 3!
    let pos : Fin 4 → Fin (r + 4 - r + 1) := fun i =>
      match i.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨2, by omega⟩ | _ => ⟨4, by omega⟩
    have hpos_inj : Function.Injective pos := fun i j h => by
      have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp [pos] at hv ⊢
    have hfree3 : ∀ t : Fin (r + 4 - r + 1), (∀ i : Fin 4, pos i ≠ t) → t.val = 3 := by
      intro t ht
      have h0 : t.val ≠ 0 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h1 : t.val ≠ 1 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h2 : t.val ≠ 2 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h4 : t.val ≠ 4 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos, h]))
      have := t.isLt; omega
    let fL : Fin (r + 4 - r + 1) → Option (Fin 4) := fun t => if t.val = 3 then some ⟨3, by decide⟩ else none
    refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
      hV hR hL r (r + 4) (by omega) (by omega) pos hpos_inj (fun i j hD => by
        obtain ⟨rfl, hj⟩ := hH_only i j hD
        fin_cases j
        · exact absurd rfl hj
        · exact median_adj_succ hR ⟨r, by omega⟩ (by dsimp only; omega)
        · exact a02
        · exact a04)
      (fun _ => none) fL (fun _ _ => Or.inl rfl)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun t1 t2 ht1 ht2 _ _ _ => Fin.ext ((hfree3 t1 ht1).trans (hfree3 t2 ht2).symm))
      (fun t ht h hft => by
        have ht3 := hfree3 t ht
        have hh3 : h = ⟨3, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht3] at hft; exact Option.some.inj hft.symm
        subst hh3; refine ⟨by simp only [pos]; omega, ?_, h3M⟩
        have hm := median_adj_succ hR ⟨r + 3, by omega⟩ (by dsimp only; omega)
        exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
      ?_ ?_
    · intro exhR hexh
      have he0 : exhR.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro i hi; obtain ⟨_, _, hc⟩ := hexh i hi; cases hc
      refine ⟨0, by omega, fun _ h => by omega, ?_⟩
      refine pure_plan_arith_bound ({⟨3, by omega⟩} : Finset (Fin (r + 4 - r + 1)))
        (fun t ht => Finset.mem_singleton.mpr (Fin.ext (hfree3 t ht.1))) ?_
      rw [Finset.card_singleton, he0]
      have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
      have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1 := by convert hZP1
      omega
    · intro exhL hexh
      have he1 : exhL.card ≤ 1 := by
        have hsub : exhL ⊆ {⟨3, by decide⟩} := fun i hi => by
          obtain ⟨t, ht, hft⟩ := hexh i hi
          have ht3 := hfree3 t ht; dsimp only [fL] at hft; rw [if_pos ht3] at hft
          rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
        exact (Finset.card_le_card hsub).trans (by rw [Finset.card_singleton])
      refine ⟨0, by omega, fun _ h => by omega, ?_⟩
      refine pure_plan_arith_bound (∅ : Finset (Fin (r + 4 - r + 1)))
        (fun t ⟨ht, hf⟩ => by have ht3 := hfree3 t ht; dsimp only [fL] at hf; rw [if_pos ht3] at hf; cases hf) ?_
      rw [Finset.card_empty]
      have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card + ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r := by convert hBkB
      have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1 := by convert hZM1
      omega
  · -- Plan Q6: [r+1, r+5], pos = (2, 3, 4, 0), F = {1}, fR = fL = none!
    let pos : Fin 4 → Fin (r + 5 - (r + 1) + 1) := fun i =>
      match i.val with | 0 => ⟨2, by omega⟩ | 1 => ⟨3, by omega⟩ | 2 => ⟨4, by omega⟩ | _ => ⟨0, by omega⟩
    have hpos_inj : Function.Injective pos := fun i j h => by
      have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp [pos] at hv ⊢
    have hfree1 : ∀ t : Fin (r + 5 - (r + 1) + 1), (∀ i : Fin 4, pos i ≠ t) → t.val = 1 := by
      intro t ht
      have h0 : t.val ≠ 0 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h2 : t.val ≠ 2 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h3 : t.val ≠ 3 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h4 : t.val ≠ 4 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos, h]))
      have := t.isLt; omega
    refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
      hV hR hL (r + 1) (r + 5) (by omega) hr pos hpos_inj (fun i j hD => by
        obtain ⟨rfl, hj⟩ := hH_only i j hD
        fin_cases j
        · exact absurd rfl hj
        · have hm := median_adj_succ hR ⟨r + 3, by omega⟩ (by dsimp only; omega)
          exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
        · exact sigma_adj_congr a35 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
        · exact sigma_adj_congr a31 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
      (fun _ => none) (fun _ => none) (fun _ _ => Or.inl rfl)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      ?_ ?_
    · intro exhR hexh
      have he0 : exhR.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro i hi; obtain ⟨_, _, hc⟩ := hexh i hi; cases hc
      by_cases h3P : ∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x
      · have hZP0 := hZP0_of_3 h3P
        refine ⟨0, by omega, fun _ h => by omega, ?_⟩
        refine pure_plan_arith_bound ({⟨1, by omega⟩} : Finset (Fin (r + 5 - (r + 1) + 1)))
          (fun t ht => Finset.mem_singleton.mpr (Fin.ext (hfree1 t ht.1))) ?_
        rw [Finset.card_singleton, he0]
        have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card = 0 := by convert hZP0
        omega
      · push Not at h3P
        refine ⟨2, by omega, fun t ht => ⟨fun i hi => Or.inl (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · omega
          · omega
          · omega
          · exact h3P), fun _ => rfl⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨1, by omega⟩} : Finset (Fin (r + 5 - (r + 1) + 1)))
          (fun t ht => Finset.mem_singleton.mpr (Fin.ext (hfree1 t ht.1))) ?_
        rw [Finset.card_singleton, he0]
        have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1 := by convert hZP1
        omega
    · intro exhL hexh
      have he0 : exhL.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro i hi; obtain ⟨_, _, hc⟩ := hexh i hi; cases hc
      refine ⟨0, by omega, fun _ h => by omega, ?_⟩
      refine pure_plan_arith_bound ({⟨1, by omega⟩} : Finset (Fin (r + 5 - (r + 1) + 1)))
        (fun t ht => Finset.mem_singleton.mpr (Fin.ext (hfree1 t ht.1))) ?_
      rw [Finset.card_singleton, he0]
      have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card + ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r := by convert hBkB
      have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1 := by convert hZM1
      omega
  · -- Plan Q8: [r, r+5], pos = (2, 0, 3, 5), F = {1, 4}, fR(1) = some 1, fL(4) = some 3!
    let pos : Fin 4 → Fin (r + 5 - r + 1) := fun i =>
      match i.val with | 0 => ⟨2, by omega⟩ | 1 => ⟨0, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨5, by omega⟩
    have hpos_inj : Function.Injective pos := fun i j h => by
      have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp [pos] at hv ⊢
    have hfree14 : ∀ t : Fin (r + 5 - r + 1), (∀ i : Fin 4, pos i ≠ t) → t.val = 1 ∨ t.val = 4 := by
      intro t ht
      have h0 : t.val ≠ 0 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h2 : t.val ≠ 2 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h3 : t.val ≠ 3 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h5 : t.val ≠ 5 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos, h]))
      have := t.isLt; omega
    let fR : Fin (r + 5 - r + 1) → Option (Fin 4) := fun t => if t.val = 1 then some ⟨1, by decide⟩ else none
    let fL : Fin (r + 5 - r + 1) → Option (Fin 4) := fun t => if t.val = 4 then some ⟨3, by decide⟩ else none
    refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
      hV hR hL r (r + 5) (by omega) hr pos hpos_inj (fun i j hD => by
        obtain ⟨rfl, hj⟩ := hH_only i j hD
        fin_cases j
        · exact absurd rfl hj
        · exact a20
        · exact median_adj_succ hR ⟨r + 2, by omega⟩ (by dsimp only; omega)
        · exact a25)
      fR fL (fun t ht => by rcases hfree14 t ht with h1 | h4; right; simp [fL, h1]; left; simp [fR, h4])
      (fun t1 t2 _ _ _ hf1 hf2 => by
        have h1 : t1.val = 1 := by by_contra hne; dsimp only [fR] at hf1; rw [if_neg hne] at hf1; cases hf1
        have h2 : t2.val = 1 := by by_contra hne; dsimp only [fR] at hf2; rw [if_neg hne] at hf2; cases hf2
        exact Fin.ext (h1.trans h2.symm))
      (fun t _ h hft => by
        have ht1 : t.val = 1 := by by_contra hne; dsimp only [fR] at hft; rw [if_neg hne] at hft; cases hft
        have hh1 : h = ⟨1, by decide⟩ := by dsimp only [fR] at hft; rw [if_pos ht1] at hft; exact Option.some.inj hft.symm
        subst hh1; refine ⟨by simp only [pos]; omega, ?_, h1P⟩
        have hm := median_adj_succ hR ⟨r, by omega⟩ (by dsimp only; omega)
        exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta; omega))
      (fun t1 t2 _ _ _ hf1 hf2 => by
        have h1 : t1.val = 4 := by by_contra hne; dsimp only [fL] at hf1; rw [if_neg hne] at hf1; cases hf1
        have h2 : t2.val = 4 := by by_contra hne; dsimp only [fL] at hf2; rw [if_neg hne] at hf2; cases hf2
        exact Fin.ext (h1.trans h2.symm))
      (fun t _ h hft => by
        have ht4 : t.val = 4 := by by_contra hne; dsimp only [fL] at hft; rw [if_neg hne] at hft; cases hft
        have hh3 : h = ⟨3, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht4] at hft; exact Option.some.inj hft.symm
        subst hh3; refine ⟨by simp only [pos]; omega, ?_, h3M⟩
        have hm := median_adj_succ hR ⟨r + 4, by omega⟩ (by dsimp only; omega)
        exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
      ?_ ?_
    · intro exhR hexh
      have hsub1 : exhR ⊆ {⟨1, by decide⟩} := fun i hi => by
        obtain ⟨t, _, hft⟩ := hexh i hi
        have ht1 : t.val = 1 := by by_contra hne; dsimp only [fR] at hft; rw [if_neg hne] at hft; cases hft
        dsimp only [fR] at hft; rw [if_pos ht1] at hft; rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
      have hdumR : ∀ t : Fin (r + 5 - r + 1), ((∀ i : Fin 4, pos i ≠ t) ∧ fR t = none) → t ∈ ({⟨4, by omega⟩} : Finset (Fin (r + 5 - r + 1))) := by
        intro t ⟨ht, hf⟩; rw [Finset.mem_singleton]
        rcases hfree14 t ht with h1 | h4
        · exfalso; dsimp only [fR] at hf; rw [if_pos h1] at hf; cases hf
        · exact Fin.ext h4
      by_cases h1in : ⟨1, by decide⟩ ∈ exhR
      · have he1 : exhR.card ≤ 1 := (Finset.card_le_card hsub1).trans (by rw [Finset.card_singleton])
        refine ⟨1, by omega, fun t ht => ⟨fun i hi => Or.inr (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · omega
          · exact h1in
          · omega
          · omega), fun hfree => by exfalso; rcases hfree14 t hfree with h1 | h4 <;> omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨4, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumR ?_
        rw [Finset.card_singleton]
        have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1 := by convert hZP1
        omega
      · have he0 : exhR.card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro i hi; exact h1in (Finset.mem_singleton.mp (hsub1 hi) ▸ hi)
        refine ⟨0, by omega, fun _ h => by omega, ?_⟩
        refine pure_plan_arith_bound ({⟨4, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumR ?_
        rw [Finset.card_singleton, he0]
        have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1 := by convert hZP1
        omega
    · intro exhL hexh
      have hsub3 : exhL ⊆ {⟨3, by decide⟩} := fun i hi => by
        obtain ⟨t, _, hft⟩ := hexh i hi
        have ht4 : t.val = 4 := by by_contra hne; dsimp only [fL] at hft; rw [if_neg hne] at hft; cases hft
        dsimp only [fL] at hft; rw [if_pos ht4] at hft; rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
      have hdumL : ∀ t : Fin (r + 5 - r + 1), ((∀ i : Fin 4, pos i ≠ t) ∧ fL t = none) → t ∈ ({⟨1, by omega⟩} : Finset (Fin (r + 5 - r + 1))) := by
        intro t ⟨ht, hf⟩; rw [Finset.mem_singleton]
        rcases hfree14 t ht with h1 | h4
        · exact Fin.ext h1
        · exfalso; dsimp only [fL] at hf; rw [if_pos h4] at hf; cases hf
      by_cases h3in : ⟨3, by decide⟩ ∈ exhL
      · have he1 : exhL.card ≤ 1 := (Finset.card_le_card hsub3).trans (by rw [Finset.card_singleton])
        refine ⟨1, by omega, fun t ht => ⟨fun i hi => Or.inr (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · omega
          · omega
          · omega
          · exact h3in), fun hfree => by exfalso; rcases hfree14 t hfree with h1 | h4 <;> omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨1, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumL ?_
        rw [Finset.card_singleton]
        have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card + ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r := by convert hBkB
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1 := by convert hZM1
        omega
      · have he0 : exhL.card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro i hi; exact h3in (Finset.mem_singleton.mp (hsub3 hi) ▸ hi)
        refine ⟨0, by omega, fun _ h => by omega, ?_⟩
        refine pure_plan_arith_bound ({⟨1, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumL ?_
        rw [Finset.card_singleton, he0]
        have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card + ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r := by convert hBkB
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1 := by convert hZM1
        omega
  · -- Plan Q9: [r, r+5], pos = (4, 1, 5, 0), F = {2, 3}, fR(2) = some 1, fL(3) = some 2!
    let pos : Fin 4 → Fin (r + 5 - r + 1) := fun i =>
      match i.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨5, by omega⟩ | _ => ⟨0, by omega⟩
    have hpos_inj : Function.Injective pos := fun i j h => by
      have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp [pos] at hv ⊢
    have hfree23 : ∀ t : Fin (r + 5 - r + 1), (∀ i : Fin 4, pos i ≠ t) → t.val = 2 ∨ t.val = 3 := by
      intro t ht
      have h0 : t.val ≠ 0 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h1 : t.val ≠ 1 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h4 : t.val ≠ 4 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h5 : t.val ≠ 5 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos, h]))
      have := t.isLt; omega
    let fR : Fin (r + 5 - r + 1) → Option (Fin 4) := fun t => if t.val = 2 then some ⟨1, by decide⟩ else none
    let fL : Fin (r + 5 - r + 1) → Option (Fin 4) := fun t => if t.val = 3 then some ⟨2, by decide⟩ else none
    refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
      hV hR hL r (r + 5) (by omega) hr pos hpos_inj (fun i j hD => by
        obtain ⟨rfl, hj⟩ := hH_only i j hD
        fin_cases j
        · exact absurd rfl hj
        · exact a41
        · exact median_adj_succ hR ⟨r + 4, by omega⟩ (by dsimp only; omega)
        · exact a40)
      fR fL (fun t ht => by rcases hfree23 t ht with h2 | h3; right; simp [fL, h2]; left; simp [fR, h3])
      (fun t1 t2 _ _ _ hf1 hf2 => by
        have h1 : t1.val = 2 := by by_contra hne; dsimp only [fR] at hf1; rw [if_neg hne] at hf1; cases hf1
        have h2 : t2.val = 2 := by by_contra hne; dsimp only [fR] at hf2; rw [if_neg hne] at hf2; cases hf2
        exact Fin.ext (h1.trans h2.symm))
      (fun t _ h hft => by
        have ht2 : t.val = 2 := by by_contra hne; dsimp only [fR] at hft; rw [if_neg hne] at hft; cases hft
        have hh1 : h = ⟨1, by decide⟩ := by dsimp only [fR] at hft; rw [if_pos ht2] at hft; exact Option.some.inj hft.symm
        subst hh1; refine ⟨by simp only [pos]; omega, ?_, h1P⟩
        have hm := median_adj_succ hR ⟨r + 1, by omega⟩ (by dsimp only; omega)
        exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta; omega))
      (fun t1 t2 _ _ _ hf1 hf2 => by
        have h1 : t1.val = 3 := by by_contra hne; dsimp only [fL] at hf1; rw [if_neg hne] at hf1; cases hf1
        have h2 : t2.val = 3 := by by_contra hne; dsimp only [fL] at hf2; rw [if_neg hne] at hf2; cases hf2
        exact Fin.ext (h1.trans h2.symm))
      (fun t _ h hft => by
        have ht3 : t.val = 3 := by by_contra hne; dsimp only [fL] at hft; rw [if_neg hne] at hft; cases hft
        have hh2 : h = ⟨2, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht3] at hft; exact Option.some.inj hft.symm
        subst hh2; refine ⟨by simp only [pos]; omega, ?_, h2M⟩
        exact sigma_adj_congr a35 (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
      ?_ ?_
    · intro exhR hexh
      have hsub1 : exhR ⊆ {⟨1, by decide⟩} := fun i hi => by
        obtain ⟨t, _, hft⟩ := hexh i hi
        have ht2 : t.val = 2 := by by_contra hne; dsimp only [fR] at hft; rw [if_neg hne] at hft; cases hft
        dsimp only [fR] at hft; rw [if_pos ht2] at hft; rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
      have he1 : exhR.card ≤ 1 := (Finset.card_le_card hsub1).trans (by rw [Finset.card_singleton])
      have hdumR : ∀ t : Fin (r + 5 - r + 1), ((∀ i : Fin 4, pos i ≠ t) ∧ fR t = none) → t ∈ ({⟨3, by omega⟩} : Finset (Fin (r + 5 - r + 1))) := by
        intro t ⟨ht, hf⟩; rw [Finset.mem_singleton]
        rcases hfree23 t ht with h2 | h3
        · exfalso; dsimp only [fR] at hf; rw [if_pos h2] at hf; cases hf
        · exact Fin.ext h3
      by_cases h3P : ∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x
      · have hZP0 := hZP0_of_3 h3P
        refine ⟨0, by omega, fun _ h => by omega, ?_⟩
        refine pure_plan_arith_bound ({⟨3, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumR ?_
        rw [Finset.card_singleton]
        have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card = 0 := by convert hZP0
        omega
      · push Not at h3P
        refine ⟨1, by omega, fun t ht => ⟨fun i hi => Or.inl (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · omega
          · omega
          · omega
          · exact h3P), fun hfree => by exfalso; rcases hfree23 t hfree with h2 | h3 <;> omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨3, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumR ?_
        rw [Finset.card_singleton]
        have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1 := by convert hZP1
        omega
    · intro exhL hexh
      have hsub2 : exhL ⊆ {⟨2, by decide⟩} := fun i hi => by
        obtain ⟨t, _, hft⟩ := hexh i hi
        have ht3 : t.val = 3 := by by_contra hne; dsimp only [fL] at hft; rw [if_neg hne] at hft; cases hft
        dsimp only [fL] at hft; rw [if_pos ht3] at hft; rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
      have hdumL : ∀ t : Fin (r + 5 - r + 1), ((∀ i : Fin 4, pos i ≠ t) ∧ fL t = none) → t ∈ ({⟨2, by omega⟩} : Finset (Fin (r + 5 - r + 1))) := by
        intro t ⟨ht, hf⟩; rw [Finset.mem_singleton]
        rcases hfree23 t ht with h2 | h3
        · exact Fin.ext h2
        · exfalso; dsimp only [fL] at hf; rw [if_pos h3] at hf; cases hf
      by_cases h2in : ⟨2, by decide⟩ ∈ exhL
      · have he1 : exhL.card ≤ 1 := (Finset.card_le_card hsub2).trans (by rw [Finset.card_singleton])
        refine ⟨1, by omega, fun t ht => ⟨fun i hi => Or.inr (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · omega
          · omega
          · exact h2in
          · omega), fun hfree => by exfalso; rcases hfree23 t hfree with h2 | h3 <;> omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨2, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumL ?_
        rw [Finset.card_singleton]
        have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card + ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r := by convert hBkB
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1 := by convert hZM1
        omega
      · have he0 : exhL.card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro i hi; exact h2in (Finset.mem_singleton.mp (hsub2 hi) ▸ hi)
        refine ⟨0, by omega, fun _ h => by omega, ?_⟩
        refine pure_plan_arith_bound ({⟨2, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumL ?_
        rw [Finset.card_singleton, he0]
        have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card + ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r := by convert hBkB
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1 := by convert hZM1
        omega

-- Family F1: 0 not in maskP, 1, 2 in maskP (delta = 0, r = B + kB)
lemma embeds_heart_four_S4ppp_F1
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hRkP : ∃ rkP : ↥(Finset.univ.image u ∪ A) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y)
    (hRkM : ∃ rkM : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))),
        x.1 ∈ Finset.univ \ (Finset.univ.image u ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    (h0P : ∀ x ∈ A, ¬ D.Adj (u ⟨0, by decide⟩) x)
    (h1P : ∃ x ∈ A, D.Adj (u ⟨1, by decide⟩) x)
    (h2P : ∃ x ∈ A, D.Adj (u ⟨2, by decide⟩) x)
    (h2M : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨2, by decide⟩))
    (h3M : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    (r : ℕ) (hr : r + 5 < 2 * n - 2)
    (hAkA : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r)
    (hBkB : (Finset.univ \ (Finset.univ.image u ∪ A)).card +
      ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r)
    (hZP2 : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 2)
    (hZM1 : (Finset.univ.filter (fun i : Fin 4 =>
      ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card) :
    Embeds D G := by
  classical
  have hZP1_of_3 : (∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x) →
      (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1 := by
    intro h3P
    have hsub : Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x) ⊆ {⟨0, by decide⟩} := by
      intro i hi; have hni := (Finset.mem_filter.mp hi).2; fin_cases i
      · exact Finset.mem_singleton_self _
      · obtain ⟨x, hx, h⟩ := h1P; exact absurd h (hni x hx)
      · obtain ⟨x, hx, h⟩ := h2P; exact absurd h (hni x hx)
      · obtain ⟨x, hx, h⟩ := h3P; exact absurd h (hni x hx)
    exact (Finset.card_le_card hsub).trans (by rw [Finset.card_singleton])
  rcases lmo6_F1 hG hR hL r (by omega) with
    ⟨a02, a03⟩ | ⟨a13, a14⟩ | ⟨a24, a25⟩ | ⟨a03, a04⟩ | ⟨a03, a05⟩ | ⟨a02, a05⟩ | ⟨a13, a15⟩
  · exact s4ppp_ge2_P123 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      r (by omega) a02 a03 (by omega) (by omega)
  · exact s4ppp_ge2_P123 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      (r + 1) (by omega) (by exact sigma_adj_congr a13 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
      (by exact sigma_adj_congr a14 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)) (by omega) (by omega)
  · -- P3: [r+2, r+5], qR = 1 since u0 at local slot 0 is not in maskP!
    refine embeds_pure_4 u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM hV hR hL
      (r + 2) (by omega) id Function.injective_id (fun i j hD => by
        obtain ⟨rfl, hj⟩ := hH_only i j hD
        fin_cases j
        · exact absurd rfl hj
        · exact median_adj_succ hR ⟨r + 2, by omega⟩ (by dsimp only; omega)
        · exact sigma_adj_congr a24 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
        · exact sigma_adj_congr a25 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
      1 (by decide) (fun t ht i hi => by
        have hi0 : i = ⟨0, by decide⟩ := Fin.ext (by have := congrArg Fin.val hi; dsimp only [id] at this ⊢; omega)
        exact hi0 ▸ h0P)
      (by have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
          have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 2 := by convert hZP2
          omega)
      0 (by decide) (fun _ h => by omega)
      (by have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card +
            ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r := by convert hBkB
          have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1 := by convert hZM1
          omega)
  · exact s4ppp_ge2_P4 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM h2M hV hR hL
      r (by omega) a03 a04 1 (by decide) (fun _ => h0P) (by omega) (by omega)
  · exact s4ppp_ge2_P5 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM h1P h3M hV hR hL
      r hr a03 a05 (Or.inl ⟨h0P, by omega⟩) (by omega)
  · -- Plan P6: [r, r+5], pos = (0, 2, 5, 1), F = {3, 4}, fR(3) = some 1, fL(4) = some 2!
    let pos : Fin 4 → Fin (r + 5 - r + 1) := fun i =>
      match i.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨5, by omega⟩ | _ => ⟨1, by omega⟩
    have hpos_inj : Function.Injective pos := fun i j h => by
      have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp [pos] at hv ⊢
    have hfree34 : ∀ t : Fin (r + 5 - r + 1), (∀ i : Fin 4, pos i ≠ t) → t.val = 3 ∨ t.val = 4 := by
      intro t ht
      have h0 : t.val ≠ 0 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h1 : t.val ≠ 1 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h2 : t.val ≠ 2 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h5 : t.val ≠ 5 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos, h]))
      have := t.isLt; omega
    let fR : Fin (r + 5 - r + 1) → Option (Fin 4) := fun t => if t.val = 3 then some ⟨1, by decide⟩ else none
    let fL : Fin (r + 5 - r + 1) → Option (Fin 4) := fun t => if t.val = 4 then some ⟨2, by decide⟩ else none
    refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
      hV hR hL r (r + 5) (by omega) hr pos hpos_inj (fun i j hD => by
        obtain ⟨rfl, hj⟩ := hH_only i j hD
        fin_cases j
        · exact absurd rfl hj
        · exact a02
        · exact a05
        · exact median_adj_succ hR ⟨r, by omega⟩ (by dsimp only; omega))
      fR fL (fun t ht => by rcases hfree34 t ht with h3 | h4; right; simp [fL, h3]; left; simp [fR, h4])
      (fun t1 t2 _ _ _ hf1 hf2 => by
        have h1 : t1.val = 3 := by by_contra hne; dsimp only [fR] at hf1; rw [if_neg hne] at hf1; cases hf1
        have h2 : t2.val = 3 := by by_contra hne; dsimp only [fR] at hf2; rw [if_neg hne] at hf2; cases hf2
        exact Fin.ext (h1.trans h2.symm))
      (fun t _ h hft => by
        have ht3 : t.val = 3 := by by_contra hne; dsimp only [fR] at hft; rw [if_neg hne] at hft; cases hft
        have hh1 : h = ⟨1, by decide⟩ := by dsimp only [fR] at hft; rw [if_pos ht3] at hft; exact Option.some.inj hft.symm
        subst hh1; refine ⟨by simp only [pos]; omega, ?_, h1P⟩
        have hm := median_adj_succ hR ⟨r + 2, by omega⟩ (by dsimp only; omega)
        exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta; omega))
      (fun t1 t2 _ _ _ hf1 hf2 => by
        have h1 : t1.val = 4 := by by_contra hne; dsimp only [fL] at hf1; rw [if_neg hne] at hf1; cases hf1
        have h2 : t2.val = 4 := by by_contra hne; dsimp only [fL] at hf2; rw [if_neg hne] at hf2; cases hf2
        exact Fin.ext (h1.trans h2.symm))
      (fun t _ h hft => by
        have ht4 : t.val = 4 := by by_contra hne; dsimp only [fL] at hft; rw [if_neg hne] at hft; cases hft
        have hh2 : h = ⟨2, by decide⟩ := by dsimp only [fL] at hft; rw [if_pos ht4] at hft; exact Option.some.inj hft.symm
        subst hh2; refine ⟨by simp only [pos]; omega, ?_, h2M⟩
        have hm := median_adj_succ hR ⟨r + 4, by omega⟩ (by dsimp only; omega)
        exact sigma_adj_congr hm (by simp +arith +zetaDelta; omega) (by simp +arith +zetaDelta))
      ?_ ?_
    · intro exhR hexh
      have hsub1 : exhR ⊆ {⟨1, by decide⟩} := fun i hi => by
        obtain ⟨t, _, hft⟩ := hexh i hi
        have ht3 : t.val = 3 := by by_contra hne; dsimp only [fR] at hft; rw [if_neg hne] at hft; cases hft
        dsimp only [fR] at hft; rw [if_pos ht3] at hft; rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
      have he1 : exhR.card ≤ 1 := (Finset.card_le_card hsub1).trans (by rw [Finset.card_singleton])
      have hdumR : ∀ t : Fin (r + 5 - r + 1), ((∀ i : Fin 4, pos i ≠ t) ∧ fR t = none) → t ∈ ({⟨4, by omega⟩} : Finset (Fin (r + 5 - r + 1))) := by
        intro t ⟨ht, hf⟩; rw [Finset.mem_singleton]
        rcases hfree34 t ht with h3 | h4
        · exfalso; dsimp only [fR] at hf; rw [if_pos h3] at hf; cases hf
        · exact Fin.ext h4
      by_cases h3P : ∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x
      · have hZP1 := hZP1_of_3 h3P
        refine ⟨1, by omega, fun t ht => ⟨fun i hi => Or.inl (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · exact h0P
          · omega
          · omega
          · omega), fun hfree => by exfalso; rcases hfree34 t hfree with h3 | h4 <;> omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨4, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumR ?_
        rw [Finset.card_singleton]
        have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1 := by convert hZP1
        omega
      · push Not at h3P
        refine ⟨2, by omega, fun t ht => ⟨fun i hi => Or.inl (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · exact h0P
          · omega
          · omega
          · exact h3P), fun hfree => by exfalso; rcases hfree34 t hfree with h3 | h4 <;> omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨4, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumR ?_
        rw [Finset.card_singleton]
        have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 2 := by convert hZP2
        omega
    · intro exhL hexh
      have hsub2 : exhL ⊆ {⟨2, by decide⟩} := fun i hi => by
        obtain ⟨t, _, hft⟩ := hexh i hi
        have ht4 : t.val = 4 := by by_contra hne; dsimp only [fL] at hft; rw [if_neg hne] at hft; cases hft
        dsimp only [fL] at hft; rw [if_pos ht4] at hft; rw [Finset.mem_singleton]; exact Option.some.inj hft.symm
      have hdumL : ∀ t : Fin (r + 5 - r + 1), ((∀ i : Fin 4, pos i ≠ t) ∧ fL t = none) → t ∈ ({⟨3, by omega⟩} : Finset (Fin (r + 5 - r + 1))) := by
        intro t ⟨ht, hf⟩; rw [Finset.mem_singleton]
        rcases hfree34 t ht with h3 | h4
        · exact Fin.ext h3
        · exfalso; dsimp only [fL] at hf; rw [if_pos h4] at hf; cases hf
      by_cases h2in : ⟨2, by decide⟩ ∈ exhL
      · have he1 : exhL.card ≤ 1 := (Finset.card_le_card hsub2).trans (by rw [Finset.card_singleton])
        refine ⟨1, by omega, fun t ht => ⟨fun i hi => Or.inr (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · omega
          · omega
          · exact h2in
          · omega), fun hfree => by exfalso; rcases hfree34 t hfree with h3 | h4 <;> omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨3, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumL ?_
        rw [Finset.card_singleton]
        have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card + ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r := by convert hBkB
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1 := by convert hZM1
        omega
      · have he0 : exhL.card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro i hi; exact h2in (Finset.mem_singleton.mp (hsub2 hi) ▸ hi)
        refine ⟨0, by omega, fun _ h => by omega, ?_⟩
        refine pure_plan_arith_bound ({⟨3, by omega⟩} : Finset (Fin (r + 5 - r + 1))) hdumL ?_
        rw [Finset.card_singleton, he0]
        have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card + ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r := by convert hBkB
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1 := by convert hZM1
        omega
  · -- Plan P7: [r+1, r+5], pos = (0, 2, 4, 1), F = {3}, fR = fL = none!
    let pos : Fin 4 → Fin (r + 5 - (r + 1) + 1) := fun i =>
      match i.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨4, by omega⟩ | _ => ⟨1, by omega⟩
    have hpos_inj : Function.Injective pos := fun i j h => by
      have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp [pos] at hv ⊢
    have hfree3 : ∀ t : Fin (r + 5 - (r + 1) + 1), (∀ i : Fin 4, pos i ≠ t) → t.val = 3 := by
      intro t ht
      have h0 : t.val ≠ 0 := fun h => ht ⟨0, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h1 : t.val ≠ 1 := fun h => ht ⟨3, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h2 : t.val ≠ 2 := fun h => ht ⟨1, by decide⟩ (Fin.ext (by simp [pos, h]))
      have h4 : t.val ≠ 4 := fun h => ht ⟨2, by decide⟩ (Fin.ext (by simp [pos, h]))
      have := t.isLt; omega
    refine embeds_heart_four_of_pure_plan u hu_inj A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
      hV hR hL (r + 1) (r + 5) (by omega) hr pos hpos_inj (fun i j hD => by
        obtain ⟨rfl, hj⟩ := hH_only i j hD
        fin_cases j
        · exact absurd rfl hj
        · exact sigma_adj_congr a13 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
        · exact sigma_adj_congr a15 (by simp +arith +zetaDelta) (by simp +arith +zetaDelta)
        · have hm := median_adj_succ hR ⟨r + 1, by omega⟩ (by dsimp only; omega)
          exact sigma_adj_congr hm (by simp +arith +zetaDelta) (by simp +arith +zetaDelta))
      (fun _ => none) (fun _ => none) (fun _ _ => Or.inl rfl)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      ?_ ?_
    · intro exhR hexh
      have he0 : exhR.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro i hi; obtain ⟨_, _, hc⟩ := hexh i hi; cases hc
      by_cases h3P : ∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x
      · have hZP1 := hZP1_of_3 h3P
        refine ⟨1, by omega, fun t ht => ⟨fun i hi => Or.inl (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · exact h0P
          · omega
          · omega
          · omega), fun hfree => by exfalso; have := hfree3 t hfree; omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨3, by omega⟩} : Finset (Fin (r + 5 - (r + 1) + 1)))
          (fun t ht => Finset.mem_singleton.mpr (Fin.ext (hfree3 t ht.1))) ?_
        rw [Finset.card_singleton, he0]
        have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1 := by convert hZP1
        omega
      · push Not at h3P
        refine ⟨2, by omega, fun t ht => ⟨fun i hi => Or.inl (by
          have hv := congrArg Fin.val hi; fin_cases i <;> simp only [pos] at hv
          · exact h0P
          · omega
          · omega
          · exact h3P), fun hfree => by exfalso; have := hfree3 t hfree; omega⟩, ?_⟩
        refine pure_plan_arith_bound ({⟨3, by omega⟩} : Finset (Fin (r + 5 - (r + 1) + 1)))
          (fun t ht => Finset.mem_singleton.mpr (Fin.ext (hfree3 t ht.1))) ?_
        rw [Finset.card_singleton, he0]
        have hA' : 6 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ 2 * n - 2 - r := by convert hAkA
        have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 2 := by convert hZP2
        omega
    · intro exhL hexh
      have he0 : exhL.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro i hi; obtain ⟨_, _, hc⟩ := hexh i hi; cases hc
      refine ⟨0, by omega, fun _ h => by omega, ?_⟩
      refine pure_plan_arith_bound ({⟨3, by omega⟩} : Finset (Fin (r + 5 - (r + 1) + 1)))
        (fun t ht => Finset.mem_singleton.mpr (Fin.ext (hfree3 t ht.1))) ?_
      rw [Finset.card_singleton, he0]
      have hB' : (Finset.univ \ (Finset.univ.image u ∪ A)).card + ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card = r := by convert hBkB
      have hZ' : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card ≤ 1 := by convert hZM1
      omega

-- Subcase 5B dispatcher: routes 1, 2 in maskP cleanly to F1, F2, or F3!
lemma embeds_heart_four_S4ppp_ge2
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (h01 : D.Adj (u ⟨0, by decide⟩) (u ⟨1, by decide⟩))
    (h02 : D.Adj (u ⟨0, by decide⟩) (u ⟨2, by decide⟩))
    (h03 : D.Adj (u ⟨0, by decide⟩) (u ⟨3, by decide⟩))
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hMandM1 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨1, by decide⟩))
    (hMandM2 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨2, by decide⟩))
    (hMandM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    (h1P : ∃ x ∈ A, D.Adj (u ⟨1, by decide⟩) x)
    (h2P : ∃ x ∈ A, D.Adj (u ⟨2, by decide⟩) x)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament) :
    Embeds D G := by
  classical
  have hH_parent : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (u j) (u i) := by
    intro i hi; fin_cases i
    · exact absurd rfl hi
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h01⟩
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h02⟩
    · exact ⟨⟨0, by decide⟩, by decide, hO.1 _ _ h03⟩
  obtain ⟨hno_AH, hno_HB, hRkP, hRkM, _, h2mP, h2mM, hcard_id⟩ :=
    heart_four_structure D hT hO u hu_inj hH_parent A hHA_disj hA_in hB_out hno_AB
  rw [hW] at hcard_id
  let B : Finset W := Finset.univ \ (Finset.univ.image u ∪ A)
  have hkA_le : (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ A.card := Finset.card_filter_le _ _
  have hkB_le : (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card ≤ B.card := Finset.card_filter_le _ _
  have hmP_ge2 : 2 ≤ (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card :=
    (Finset.card_pair (Fin.ne_of_val_ne (by decide) : (⟨1, by decide⟩ : Fin 4) ≠ ⟨2, by decide⟩)).symm.trans_le
      (Finset.card_le_card (fun j hj => by
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1P⟩
        · rw [Finset.mem_singleton.mp hj']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2P⟩))
  have hmM_ge3 : 3 ≤ (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card := by
    have hcard3 : ({⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} : Finset (Fin 4)).card = 3 := by decide
    refine hcard3.symm.trans_le (Finset.card_le_card (fun j hj => ?_))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMandM3⟩
  have hZM1 : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card ≤ 1 := by
    have hsub : Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i)) ⊆ {⟨0, by decide⟩} := by
      intro i hi; have hni := (Finset.mem_filter.mp hi).2; fin_cases i
      · exact Finset.mem_singleton_self _
      · obtain ⟨y, hy, h⟩ := hMandM1; exact absurd h (hni y hy)
      · obtain ⟨y, hy, h⟩ := hMandM2; exact absurd h (hni y hy)
      · obtain ⟨y, hy, h⟩ := hMandM3; exact absurd h (hni y hy)
    exact (Finset.card_le_card hsub).trans (by rw [Finset.card_singleton])
  have hZP2 : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 2 := by
    have hsub : Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x) ⊆ {⟨0, by decide⟩, ⟨3, by decide⟩} := by
      intro i hi; have hni := (Finset.mem_filter.mp hi).2; fin_cases i
      · exact Finset.mem_insert_self _ _
      · obtain ⟨x, hx, h⟩ := h1P; exact absurd h (hni x hx)
      · obtain ⟨x, hx, h⟩ := h2P; exact absurd h (hni x hx)
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
  have hAkA_ge4 : 4 ≤ A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card := by
    have h2' : 2 * (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card ≤
        A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card := by convert h2mP
    omega
  have hBkB_ge6 : 6 ≤ B.card + (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card := by
    have h2' : 2 * (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card ≤
        B.card + (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card := by dsimp only [B]; convert h2mM
    omega
  by_cases h0P : ∃ x ∈ A, D.Adj (u ⟨0, by decide⟩) x
  · have hZP1 : (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card ≤ 1 := by
      have hsub : Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x) ⊆ {⟨3, by decide⟩} := by
        intro i hi; have hni := (Finset.mem_filter.mp hi).2; fin_cases i
        · obtain ⟨x, hx, h⟩ := h0P; exact absurd h (hni x hx)
        · obtain ⟨x, hx, h⟩ := h1P; exact absurd h (hni x hx)
        · obtain ⟨x, hx, h⟩ := h2P; exact absurd h (hni x hx)
        · exact Finset.mem_singleton_self _
      exact (Finset.card_le_card hsub).trans (by rw [Finset.card_singleton])
    by_cases h0M : ∃ y ∈ B, D.Adj y (u ⟨0, by decide⟩)
    · have hZM0 : (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro i _ hni
        fin_cases i
        · obtain ⟨y, hy, h⟩ := h0M; exact hni y hy h
        · obtain ⟨y, hy, h⟩ := hMandM1; exact hni y hy h
        · obtain ⟨y, hy, h⟩ := hMandM2; exact hni y hy h
        · obtain ⟨y, hy, h⟩ := hMandM3; exact hni y hy h
      let r := B.card + (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card - 1
      exact embeds_heart_four_S4ppp_F2 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
        h0P h1P h2P h0M hMandM1 hMandM2 hMandM3 r
        (by dsimp only [r, B] at hBkB_ge6 hkA_le hkB_le ⊢; omega)
        (by dsimp only [r, B] at hBkB_ge6 hkA_le hkB_le ⊢; omega)
        (by dsimp only [r, B] at hBkB_ge6 ⊢; omega)
        (by convert hZP1) (by dsimp only [B] at hZM0; convert hZM0) hV hG hR hL
    · let r := B.card + (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
      exact embeds_heart_four_S4ppp_F3 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
        h0P h1P h2P hMandM2 hMandM3 r
        (by dsimp only [r, B] at hAkA_ge4 hkA_le hkB_le ⊢; omega)
        (by dsimp only [r, B] at hkA_le hkB_le ⊢; omega)
        (by dsimp only [r, B])
        (by convert hZP1) (by dsimp only [B] at hZM1; convert hZM1) hV hG hR hL
  · push Not at h0P
    let r := B.card + (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
    exact embeds_heart_four_S4ppp_F1 u hu_inj hH_only A hHA_disj hA_in hB_out hno_AB hno_AH hno_HB hRkP hRkM
      h0P h1P h2P hMandM2 hMandM3 r
      (by dsimp only [r, B] at hAkA_ge4 hkA_le hkB_le ⊢; omega)
      (by dsimp only [r, B] at hkA_le hkB_le ⊢; omega)
      (by dsimp only [r, B])
      (by convert hZP2) (by dsimp only [B] at hZM1; convert hZM1) hV hG hR hL

-- Full S4+++ dispatcher: permutes {1, 2, 3} into Subcase 5A (le1) or Subcase 5B (ge2)!
lemma embeds_heart_four_S4ppp
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n) {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (h01 : D.Adj (u ⟨0, by decide⟩) (u ⟨1, by decide⟩))
    (h02 : D.Adj (u ⟨0, by decide⟩) (u ⟨2, by decide⟩))
    (h03 : D.Adj (u ⟨0, by decide⟩) (u ⟨3, by decide⟩))
    (hH_only : ∀ i j : Fin 4, D.Adj (u i) (u j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hMandM1 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨1, by decide⟩))
    (hMandM2 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨2, by decide⟩))
    (hMandM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ⟨3, by decide⟩))
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament) :
    Embeds D G := by
  classical
  have hperm : ∀ (π : Fin 4 → Fin 4), Function.Injective π → π ⟨0, by decide⟩ = ⟨0, by decide⟩ →
      ((∃ x ∈ A, D.Adj (u (π ⟨1, by decide⟩)) x) ∧ (∃ x ∈ A, D.Adj (u (π ⟨2, by decide⟩)) x) ∨
       (∀ x ∈ A, ¬ D.Adj (u (π ⟨1, by decide⟩)) x) ∧ (∀ x ∈ A, ¬ D.Adj (u (π ⟨2, by decide⟩)) x)) →
      Embeds D G := by
    intro π hπ_inj hπ0 hcase
    have hπ_surj : Function.Surjective π := Finite.surjective_of_injective hπ_inj
    let u' : Fin 4 → W := fun i => u (π i)
    have himg : Finset.univ.image u' = Finset.univ.image u := by
      ext w; simp only [u', Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi⟩ => ⟨π i, hi⟩, fun ⟨j, hj⟩ => by obtain ⟨i, rfl⟩ := hπ_surj j; exact ⟨i, hj⟩⟩
    have hu'_adj : ∀ j : Fin 4, j ≠ ⟨0, by decide⟩ → D.Adj (u' ⟨0, by decide⟩) (u' j) := by
      intro j hj
      have hne : π j ≠ ⟨0, by decide⟩ := fun h => hj (hπ_inj (h.trans hπ0.symm))
      dsimp only [u']; rw [hπ0]
      generalize hkj : π j = k at hne ⊢
      fin_cases k
      · exact absurd rfl hne
      · exact h01
      · exact h02
      · exact h03
    have hMand' : ∀ j : Fin 4, j ≠ ⟨0, by decide⟩ →
        ∃ y ∈ Finset.univ \ (Finset.univ.image u' ∪ A), D.Adj y (u' j) := by
      intro j hj; rw [himg]
      have hne : π j ≠ ⟨0, by decide⟩ := fun h => hj (hπ_inj (h.trans hπ0.symm))
      dsimp only [u']; generalize hkj : π j = k at hne ⊢
      fin_cases k
      · exact absurd rfl hne
      · exact hMandM1
      · exact hMandM2
      · exact hMandM3
    have honly' : ∀ i j : Fin 4, D.Adj (u' i) (u' j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩ := by
      intro i j hD; obtain ⟨h1, h2⟩ := hH_only (π i) (π j) hD
      exact ⟨hπ_inj (h1.trans hπ0.symm), fun h => h2 (h ▸ hπ0)⟩
    have hB' : ∀ y : W, (∀ i : Fin 4, y ≠ u' i) → y ∉ A → (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1 :=
      fun y hy hyA => hB_out y (fun j => by obtain ⟨i, rfl⟩ := hπ_surj j; exact hy i) hyA
    have hAB' : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u' i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x :=
      fun x hx y hy hyA => hno_AB x hx y (fun j => by obtain ⟨i, rfl⟩ := hπ_surj j; exact hy i) hyA
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact embeds_heart_four_S4ppp_ge2 hW hT hO u' (hu_inj.comp hπ_inj)
        (hu'_adj ⟨1, by decide⟩ (by decide)) (hu'_adj ⟨2, by decide⟩ (by decide)) (hu'_adj ⟨3, by decide⟩ (by decide))
        honly' A (fun i => hHA_disj (π i)) hA_in hB' hAB'
        (hMand' ⟨1, by decide⟩ (by decide)) (hMand' ⟨2, by decide⟩ (by decide)) (hMand' ⟨3, by decide⟩ (by decide))
        h1 h2 hV hG
    · exact embeds_heart_four_S4ppp_le1 hW hT hO u' (hu_inj.comp hπ_inj)
        (hu'_adj ⟨1, by decide⟩ (by decide)) (hu'_adj ⟨2, by decide⟩ (by decide)) (hu'_adj ⟨3, by decide⟩ (by decide))
        honly' A (fun i => hHA_disj (π i)) hA_in hB' hAB'
        (hMand' ⟨1, by decide⟩ (by decide)) (hMand' ⟨2, by decide⟩ (by decide)) (hMand' ⟨3, by decide⟩ (by decide))
        h1 h2 hV hG
  by_cases h1 : ∃ x ∈ A, D.Adj (u ⟨1, by decide⟩) x
  · by_cases h2 : ∃ x ∈ A, D.Adj (u ⟨2, by decide⟩) x
    · exact hperm id Function.injective_id rfl (Or.inl ⟨h1, h2⟩)
    · push Not at h2
      by_cases h3 : ∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x
      · exact hperm (fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨2, by decide⟩)
          (fun i j h => by fin_cases i <;> fin_cases j <;> simp at h ⊢) rfl (Or.inl ⟨h1, h3⟩)
      · push Not at h3
        exact hperm (fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨1, by decide⟩)
          (fun i j h => by fin_cases i <;> fin_cases j <;> simp at h ⊢) rfl (Or.inr ⟨h2, h3⟩)
  · push Not at h1
    by_cases h2 : ∃ x ∈ A, D.Adj (u ⟨2, by decide⟩) x
    · by_cases h3 : ∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x
      · exact hperm (fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨1, by decide⟩)
          (fun i j h => by fin_cases i <;> fin_cases j <;> simp at h ⊢) rfl (Or.inl ⟨h2, h3⟩)
      · push Not at h3
        exact hperm (fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨2, by decide⟩)
          (fun i j h => by fin_cases i <;> fin_cases j <;> simp at h ⊢) rfl (Or.inr ⟨h1, h3⟩)
    · push Not at h2
      exact hperm id Function.injective_id rfl (Or.inr ⟨h1, h2⟩)

-- ============================================================================
-- MODULE 7: MAIN THEOREMS — Theorem 5.1 (Heart h = 4) & Corollary 5.2 (n - k <= 4)
-- ============================================================================

-- Helper: acyclic graph on 4 vertices with 3 spanning edges has NO other edges (via unique paths)!
lemma tree_star4_only_adj {W : Type*} {T : SimpleGraph W} (hT : T.IsTree)
    (v : Fin 4 → W) (hv_inj : Function.Injective v)
    (h01 : T.Adj (v ⟨0, by decide⟩) (v ⟨1, by decide⟩))
    (h02 : T.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩))
    (h03 : T.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩)) :
    ∀ i j : Fin 4, T.Adj (v i) (v j) → (i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩) ∨ (j = ⟨0, by decide⟩ ∧ i ≠ ⟨0, by decide⟩) := by
  intro i j hij
  have hne : i ≠ j := fun h => T.loopless.irrefl _ (h ▸ hij)
  have hno_tri : ∀ a b : Fin 4, a ≠ ⟨0, by decide⟩ → b ≠ ⟨0, by decide⟩ → a ≠ b →
      T.Adj (v ⟨0, by decide⟩) (v a) → T.Adj (v ⟨0, by decide⟩) (v b) → ¬ T.Adj (v a) (v b) := by
    intro a b ha0 hb0 hab h0a h0b hab'
    let p1 : T.Walk (v a) (v b) := SimpleGraph.Walk.cons hab' SimpleGraph.Walk.nil
    let p2 : T.Walk (v a) (v b) := SimpleGraph.Walk.cons h0a.symm (SimpleGraph.Walk.cons h0b SimpleGraph.Walk.nil)
    have hp1 : p1.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      simp only [p1, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_false_eq_true, and_true]
      exact fun h => hab (hv_inj h))
    have hp2 : p2.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      simp only [p2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_or, not_false_eq_true, and_true]
      exact ⟨⟨fun h => ha0 (hv_inj h), fun h => hab (hv_inj h)⟩, fun h => hb0 (hv_inj h).symm⟩)
    have heq : p1 = p2 := congrArg Subtype.val ((hT.isAcyclic.subsingleton_path (v a) (v b)).elim ⟨p1, hp1⟩ ⟨p2, hp2⟩)
    have hlen := congrArg SimpleGraph.Walk.length heq
    simp [p1, p2] at hlen
  fin_cases i <;> fin_cases j
  · exact absurd rfl hne
  · exact Or.inl ⟨rfl, by decide⟩
  · exact Or.inl ⟨rfl, by decide⟩
  · exact Or.inl ⟨rfl, by decide⟩
  · exact Or.inr ⟨rfl, by decide⟩
  · exact absurd rfl hne
  · exact absurd hij (hno_tri ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide) (by decide) h01 h02)
  · exact absurd hij (hno_tri ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide) (by decide) h01 h03)
  · exact Or.inr ⟨rfl, by decide⟩
  · exact absurd hij.symm (hno_tri ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide) (by decide) h01 h02)
  · exact absurd rfl hne
  · exact absurd hij (hno_tri ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide) (by decide) h02 h03)
  · exact Or.inr ⟨rfl, by decide⟩
  · exact absurd hij.symm (hno_tri ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide) (by decide) h01 h03)
  · exact absurd hij.symm (hno_tri ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide) (by decide) h02 h03)
  · exact absurd rfl hne

lemma tree_path4_only_adj {W : Type*} {T : SimpleGraph W} (hT : T.IsTree)
    (v : Fin 4 → W) (hv_inj : Function.Injective v)
    (h01 : T.Adj (v ⟨0, by decide⟩) (v ⟨1, by decide⟩))
    (h12 : T.Adj (v ⟨1, by decide⟩) (v ⟨2, by decide⟩))
    (h23 : T.Adj (v ⟨2, by decide⟩) (v ⟨3, by decide⟩)) :
    ∀ i j : Fin 4, T.Adj (v i) (v j) → i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  intro i j hij
  have hne : i ≠ j := fun h => T.loopless.irrefl _ (h ▸ hij)
  have hno02 : ¬ T.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) := by
    intro h02
    let p1 : T.Walk (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) := SimpleGraph.Walk.cons h02 SimpleGraph.Walk.nil
    let p2 : T.Walk (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) := SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12 SimpleGraph.Walk.nil)
    have hp1 : p1.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      simp only [p1, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_false_eq_true, and_true]
      exact fun h => by have := hv_inj h; simp at this)
    have hp2 : p2.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      simp only [p2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_or, not_false_eq_true, and_true]
      exact ⟨⟨fun h => by have := hv_inj h; simp at this, fun h => by have := hv_inj h; simp at this⟩,
        fun h => by have := hv_inj h; simp at this⟩)
    have hlen := congrArg SimpleGraph.Walk.length (congrArg Subtype.val ((hT.isAcyclic.subsingleton_path _ _).elim ⟨p1, hp1⟩ ⟨p2, hp2⟩))
    simp [p1, p2] at hlen
  have hno13 : ¬ T.Adj (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) := by
    intro h13
    let p1 : T.Walk (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) := SimpleGraph.Walk.cons h13 SimpleGraph.Walk.nil
    let p2 : T.Walk (v ⟨1, by decide⟩) (v ⟨3, by decide⟩) := SimpleGraph.Walk.cons h12 (SimpleGraph.Walk.cons h23 SimpleGraph.Walk.nil)
    have hp1 : p1.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      simp only [p1, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_false_eq_true, and_true]
      exact fun h => by have := hv_inj h; simp at this)
    have hp2 : p2.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      simp only [p2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_or, not_false_eq_true, and_true]
      exact ⟨⟨fun h => by have := hv_inj h; simp at this, fun h => by have := hv_inj h; simp at this⟩,
        fun h => by have := hv_inj h; simp at this⟩)
    have hlen := congrArg SimpleGraph.Walk.length (congrArg Subtype.val ((hT.isAcyclic.subsingleton_path _ _).elim ⟨p1, hp1⟩ ⟨p2, hp2⟩))
    simp [p1, p2] at hlen
  have hno03 : ¬ T.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) := by
    intro h03
    let p1 : T.Walk (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) := SimpleGraph.Walk.cons h03 SimpleGraph.Walk.nil
    let p2 : T.Walk (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) :=
      SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12 (SimpleGraph.Walk.cons h23 SimpleGraph.Walk.nil))
    have hp1 : p1.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      simp only [p1, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_false_eq_true, and_true]
      exact fun h => by have := hv_inj h; simp at this)
    have hp2 : p2.IsPath := SimpleGraph.Walk.IsPath.mk' (by
      simp only [p2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_or, not_false_eq_true, and_true]
      exact ⟨⟨fun h => by have := hv_inj h; simp at this, fun h => by have := hv_inj h; simp at this,
        fun h => by have := hv_inj h; simp at this⟩,
        ⟨fun h => by have := hv_inj h; simp at this, fun h => by have := hv_inj h; simp at this⟩,
        fun h => by have := hv_inj h; simp at this⟩)
    have hlen := congrArg SimpleGraph.Walk.length (congrArg Subtype.val ((hT.isAcyclic.subsingleton_path _ _).elim ⟨p1, hp1⟩ ⟨p2, hp2⟩))
    simp [p1, p2] at hlen
  fin_cases i <;> fin_cases j <;> dsimp only at hij hne ⊢ <;>
    first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hne |
      exact absurd hij hno02 | exact absurd hij.symm hno02 |
      exact absurd hij hno13 | exact absurd hij.symm hno13 |
      exact absurd hij hno03 | exact absurd hij.symm hno03

-- Theorem 5.1: Every oriented tree with Heart order h = 4 embeds in every no-source, no-sink tournament on 2n - 2 vertices
-- (assuming Heart order h <= 3 already embeds)!
theorem embeds_heart_four {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hTree : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v) (hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u)
    (hH3 : (∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
      ((D.Adj u1 u2 ∧ D.Adj u2 u3) ∨ (D.Adj u1 u2 ∧ D.Adj u1 u3) ∨ (D.Adj u2 u1 ∧ D.Adj u3 u1)) ∧
      ∃ A : Finset W, u1 ∉ A ∧ u2 ∉ A ∧ u3 ∉ A ∧
        (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
        (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
          (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
        (∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)) →
      Embeds D G)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_parent : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧
      (D.Adj (u j) (u i) ∨ D.Adj (u i) (u j)))
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x) :
    Embeds D G := by
  classical
  obtain ⟨T, hT, hO⟩ := hTree
  have hT_parent : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (u j) (u i) := by
    intro i hi; obtain ⟨j, hj, hD⟩ := hH_parent i hi
    exact ⟨j, hj, hD.elim (hO.1 _ _) (fun h => (hO.1 _ _ h).symm)⟩
  -- Canonical dispatchers (check mandatory leaves -> Heart 3 or call Topology 1-5!)
  have hdo_P4ppp : ∀ {D' : Digraph W} [DecidableRel D'.Adj] {G' : Digraph V} [DecidableRel G'.Adj],
      D'.IsOrientation T → G'.IsTournament →
      (∀ v : V, ∃ x : V, G'.Adj x v) → (∀ v : V, ∃ x : V, G'.Adj v x) →
      ((∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
        ((D'.Adj u1 u2 ∧ D'.Adj u2 u3) ∨ (D'.Adj u1 u2 ∧ D'.Adj u1 u3) ∨ (D'.Adj u2 u1 ∧ D'.Adj u3 u1)) ∧
        ∃ A' : Finset W, u1 ∉ A' ∧ u2 ∉ A' ∧ u3 ∉ A' ∧
          (∀ x ∈ A', (Finset.univ.filter (fun z : W => D'.Adj z x)).card = 1) ∧
          (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → (Finset.univ.filter (fun z : W => D'.Adj y z)).card = 1) ∧
          (∀ x ∈ A', ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → ¬ D'.Adj x y ∧ ¬ D'.Adj y x)) → Embeds D' G') →
      ∀ (v : Fin 4 → W), Function.Injective v →
      D'.Adj (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) → D'.Adj (v ⟨1, by decide⟩) (v ⟨2, by decide⟩) → D'.Adj (v ⟨2, by decide⟩) (v ⟨3, by decide⟩) →
      ∀ (A' : Finset W), (∀ i : Fin 4, v i ∉ A') →
      (∀ x ∈ A', (Finset.univ.filter (fun z : W => D'.Adj z x)).card = 1) →
      (∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A' → (Finset.univ.filter (fun z : W => D'.Adj y z)).card = 1) →
      (∀ x ∈ A', ∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A' → ¬ D'.Adj x y ∧ ¬ D'.Adj y x) →
      Embeds D' G' := by
    intro D' _ G' _ hO' hG' hNS hNK hH3' v hv_inj e01 e12 e23 A' hvA hAi hBo hAB
    have honlyT := tree_path4_only_adj hT v hv_inj (hO'.1 _ _ e01) (hO'.1 _ _ e12) (hO'.1 _ _ e23)
    have honlyD : ∀ i j : Fin 4, D'.Adj (v i) (v j) → i.val + 1 = j.val := by
      intro i j hD
      rcases honlyT i j (hO'.1 _ _ hD) with h | h
      · exact h
      · exfalso; fin_cases i <;> fin_cases j <;> simp at h
        · exact not_adj_rev_of_isOrientation hO' e01 hD
        · exact not_adj_rev_of_isOrientation hO' e12 hD
        · exact not_adj_rev_of_isOrientation hO' e23 hD
    have hpar : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (v j) (v i) := fun i hi => by
      fin_cases i; exact absurd rfl hi; exact ⟨⟨0, by decide⟩, by decide, hO'.1 _ _ e01⟩
      exact ⟨⟨1, by decide⟩, by decide, hO'.1 _ _ e12⟩; exact ⟨⟨2, by decide⟩, by decide, hO'.1 _ _ e23⟩
    obtain ⟨hno_AH, hno_HB, _, _, _, _, _, _⟩ := heart_four_structure D' hT hO' v hv_inj hpar A' hvA hAi hBo hAB
    by_cases hM0 : ∃ x ∈ A', D'.Adj (v ⟨0, by decide⟩) x
    · by_cases hM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image v ∪ A'), D'.Adj y (v ⟨3, by decide⟩)
      · exact embeds_heart_four_P4ppp hW hT hO' v hv_inj e01 e12 e23 honlyD A' hvA hAi hBo hAB hM0 hM3 hV hG' hNS hNK
      · push Not at hM3
        exact hH3' (heart_four_drop_leaf_to_A v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
          ⟨3, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
          (by decide) (Or.inl ⟨e01, e12⟩) e23 (fun j hD => Fin.ext (by have := honlyD j ⟨3, by decide⟩ hD; simp at this ⊢; omega)) hM3)
    · push Not at hM0
      exact hH3' (heart_four_drop_leaf_to_B v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
        ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩
        (by decide) (Or.inl ⟨e12, e23⟩) e01 (fun j hD => Fin.ext (by have := honlyD ⟨0, by decide⟩ j hD; simp at this ⊢; omega)) hM0)
  have hdo_P4ppm : ∀ {D' : Digraph W} [DecidableRel D'.Adj] {G' : Digraph V} [DecidableRel G'.Adj],
      D'.IsOrientation T → G'.IsTournament →
      ((∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
        ((D'.Adj u1 u2 ∧ D'.Adj u2 u3) ∨ (D'.Adj u1 u2 ∧ D'.Adj u1 u3) ∨ (D'.Adj u2 u1 ∧ D'.Adj u3 u1)) ∧
        ∃ A' : Finset W, u1 ∉ A' ∧ u2 ∉ A' ∧ u3 ∉ A' ∧
          (∀ x ∈ A', (Finset.univ.filter (fun z : W => D'.Adj z x)).card = 1) ∧
          (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → (Finset.univ.filter (fun z : W => D'.Adj y z)).card = 1) ∧
          (∀ x ∈ A', ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → ¬ D'.Adj x y ∧ ¬ D'.Adj y x)) → Embeds D' G') →
      ∀ (v : Fin 4 → W), Function.Injective v →
      D'.Adj (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) → D'.Adj (v ⟨1, by decide⟩) (v ⟨2, by decide⟩) → D'.Adj (v ⟨3, by decide⟩) (v ⟨2, by decide⟩) →
      ∀ (A' : Finset W), (∀ i : Fin 4, v i ∉ A') →
      (∀ x ∈ A', (Finset.univ.filter (fun z : W => D'.Adj z x)).card = 1) →
      (∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A' → (Finset.univ.filter (fun z : W => D'.Adj y z)).card = 1) →
      (∀ x ∈ A', ∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A' → ¬ D'.Adj x y ∧ ¬ D'.Adj y x) →
      Embeds D' G' := by
    intro D' _ G' _ hO' hG' hH3' v hv_inj e01 e12 e32 A' hvA hAi hBo hAB
    have honlyT := tree_path4_only_adj hT v hv_inj (hO'.1 _ _ e01) (hO'.1 _ _ e12) (hO'.1 _ _ e32).symm
    have honlyD : ∀ i j : Fin 4, D'.Adj (v i) (v j) →
        (i = ⟨0, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨ (i = ⟨1, by decide⟩ ∧ j = ⟨2, by decide⟩) ∨ (i = ⟨3, by decide⟩ ∧ j = ⟨2, by decide⟩) := by
      intro i j hD
      have h := honlyT i j (hO'.1 _ _ hD)
      fin_cases i <;> fin_cases j <;> simp at h
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd hD (not_adj_rev_of_isOrientation hO' e01)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact absurd hD (not_adj_rev_of_isOrientation hO' e12)
      · exact absurd hD (not_adj_rev_of_isOrientation hO' e32)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    have hpar : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (v j) (v i) := fun i hi => by
      fin_cases i; exact absurd rfl hi; exact ⟨⟨0, by decide⟩, by decide, hO'.1 _ _ e01⟩
      exact ⟨⟨1, by decide⟩, by decide, hO'.1 _ _ e12⟩; exact ⟨⟨2, by decide⟩, by decide, (hO'.1 _ _ e32).symm⟩
    obtain ⟨hno_AH, hno_HB, _, _, _, _, _, _⟩ := heart_four_structure D' hT hO' v hv_inj hpar A' hvA hAi hBo hAB
    by_cases hM0 : ∃ x ∈ A', D'.Adj (v ⟨0, by decide⟩) x
    · by_cases hM3 : ∃ x ∈ A', D'.Adj (v ⟨3, by decide⟩) x
      · exact embeds_heart_four_P4ppm hW hT hO' v hv_inj e01 e12 e32 honlyD A' hvA hAi hBo hAB hM0 hM3 hV hG'
      · push Not at hM3
        exact hH3' (heart_four_drop_leaf_to_B v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
          ⟨3, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
          (by decide) (Or.inl ⟨e01, e12⟩) e32 (fun j hD => by rcases honlyD ⟨3, by decide⟩ j hD with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ <;> first | rfl | (simp at h)) hM3)
    · push Not at hM0
      exact hH3' (heart_four_drop_leaf_to_B v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
        ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩
        (by decide) (Or.inr (Or.inr ⟨e12, e32⟩)) e01 (fun j hD => by rcases honlyD ⟨0, by decide⟩ j hD with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> first | rfl | (simp at h)) hM0)
  have hdo_P4pmp : ∀ {D' : Digraph W} [DecidableRel D'.Adj] {G' : Digraph V} [DecidableRel G'.Adj],
      D'.IsOrientation T → G'.IsTournament →
      ((∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
        ((D'.Adj u1 u2 ∧ D'.Adj u2 u3) ∨ (D'.Adj u1 u2 ∧ D'.Adj u1 u3) ∨ (D'.Adj u2 u1 ∧ D'.Adj u3 u1)) ∧
        ∃ A' : Finset W, u1 ∉ A' ∧ u2 ∉ A' ∧ u3 ∉ A' ∧
          (∀ x ∈ A', (Finset.univ.filter (fun z : W => D'.Adj z x)).card = 1) ∧
          (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → (Finset.univ.filter (fun z : W => D'.Adj y z)).card = 1) ∧
          (∀ x ∈ A', ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → ¬ D'.Adj x y ∧ ¬ D'.Adj y x)) → Embeds D' G') →
      ∀ (v : Fin 4 → W), Function.Injective v →
      D'.Adj (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) → D'.Adj (v ⟨2, by decide⟩) (v ⟨1, by decide⟩) → D'.Adj (v ⟨2, by decide⟩) (v ⟨3, by decide⟩) →
      ∀ (A' : Finset W), (∀ i : Fin 4, v i ∉ A') →
      (∀ x ∈ A', (Finset.univ.filter (fun z : W => D'.Adj z x)).card = 1) →
      (∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A' → (Finset.univ.filter (fun z : W => D'.Adj y z)).card = 1) →
      (∀ x ∈ A', ∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A' → ¬ D'.Adj x y ∧ ¬ D'.Adj y x) →
      Embeds D' G' := by
    intro D' _ G' _ hO' hG' hH3' v hv_inj e01 e21 e23 A' hvA hAi hBo hAB
    have honlyT := tree_path4_only_adj hT v hv_inj (hO'.1 _ _ e01) (hO'.1 _ _ e21).symm (hO'.1 _ _ e23)
    have honlyD : ∀ i j : Fin 4, D'.Adj (v i) (v j) →
        (i = ⟨0, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨ (i = ⟨2, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨ (i = ⟨2, by decide⟩ ∧ j = ⟨3, by decide⟩) := by
      intro i j hD
      have h := honlyT i j (hO'.1 _ _ hD)
      fin_cases i <;> fin_cases j <;> simp at h
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd hD (not_adj_rev_of_isOrientation hO' e01)
      · exact absurd hD (not_adj_rev_of_isOrientation hO' e21)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact absurd hD (not_adj_rev_of_isOrientation hO' e23)
    have hpar : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (v j) (v i) := fun i hi => by
      fin_cases i; exact absurd rfl hi; exact ⟨⟨0, by decide⟩, by decide, hO'.1 _ _ e01⟩
      exact ⟨⟨1, by decide⟩, by decide, (hO'.1 _ _ e21).symm⟩; exact ⟨⟨2, by decide⟩, by decide, hO'.1 _ _ e23⟩
    obtain ⟨hno_AH, hno_HB, _, _, _, _, _, _⟩ := heart_four_structure D' hT hO' v hv_inj hpar A' hvA hAi hBo hAB
    by_cases hM0 : ∃ x ∈ A', D'.Adj (v ⟨0, by decide⟩) x
    · by_cases hM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image v ∪ A'), D'.Adj y (v ⟨3, by decide⟩)
      · exact embeds_heart_four_P4pmp hW hT hO' v hv_inj e01 e21 e23 honlyD A' hvA hAi hBo hAB hM0 hM3 hV hG'
      · push Not at hM3
        exact hH3' (heart_four_drop_leaf_to_A v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
          ⟨3, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩
          (by decide) (Or.inr (Or.inr ⟨e01, e21⟩)) e23 (fun j hD => by rcases honlyD j ⟨3, by decide⟩ hD with ⟨_, h⟩ | ⟨_, h⟩ | ⟨rfl, _⟩ <;> first | rfl | (simp at h)) hM3)
    · push Not at hM0
      exact hH3' (heart_four_drop_leaf_to_B v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
        ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩
        (by decide) (Or.inr (Or.inl ⟨e21, e23⟩)) e01 (fun j hD => by rcases honlyD ⟨0, by decide⟩ j hD with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> first | rfl | (simp at h)) hM0)
  have hdo_S4ppm : ∀ {D' : Digraph W} [DecidableRel D'.Adj] {G' : Digraph V} [DecidableRel G'.Adj],
      D'.IsOrientation T → G'.IsTournament →
      (∀ v : V, ∃ x : V, G'.Adj x v) → (∀ v : V, ∃ x : V, G'.Adj v x) →
      ((∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
        ((D'.Adj u1 u2 ∧ D'.Adj u2 u3) ∨ (D'.Adj u1 u2 ∧ D'.Adj u1 u3) ∨ (D'.Adj u2 u1 ∧ D'.Adj u3 u1)) ∧
        ∃ A' : Finset W, u1 ∉ A' ∧ u2 ∉ A' ∧ u3 ∉ A' ∧
          (∀ x ∈ A', (Finset.univ.filter (fun z : W => D'.Adj z x)).card = 1) ∧
          (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → (Finset.univ.filter (fun z : W => D'.Adj y z)).card = 1) ∧
          (∀ x ∈ A', ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → ¬ D'.Adj x y ∧ ¬ D'.Adj y x)) → Embeds D' G') →
      ∀ (v : Fin 4 → W), Function.Injective v →
      D'.Adj (v ⟨3, by decide⟩) (v ⟨0, by decide⟩) → D'.Adj (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) → D'.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) →
      ∀ (A' : Finset W), (∀ i : Fin 4, v i ∉ A') →
      (∀ x ∈ A', (Finset.univ.filter (fun z : W => D'.Adj z x)).card = 1) →
      (∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A' → (Finset.univ.filter (fun z : W => D'.Adj y z)).card = 1) →
      (∀ x ∈ A', ∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A' → ¬ D'.Adj x y ∧ ¬ D'.Adj y x) →
      Embeds D' G' := by
    intro D' _ G' _ hO' hG' hNS hNK hH3' v hv_inj e30 e01 e02 A' hvA hAi hBo hAB
    have honlyT := tree_star4_only_adj hT v hv_inj (hO'.1 _ _ e01) (hO'.1 _ _ e02) (hO'.1 _ _ e30).symm
    have honlyD : ∀ i j : Fin 4, D'.Adj (v i) (v j) →
        (i = ⟨3, by decide⟩ ∧ j = ⟨0, by decide⟩) ∨ (i = ⟨0, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨ (i = ⟨0, by decide⟩ ∧ j = ⟨2, by decide⟩) := by
      intro i j hD
      have h := honlyT i j (hO'.1 _ _ hD)
      fin_cases i <;> fin_cases j <;> simp at h
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact absurd hD (not_adj_rev_of_isOrientation hO' e30)
      · exact absurd hD (not_adj_rev_of_isOrientation hO' e01)
      · exact absurd hD (not_adj_rev_of_isOrientation hO' e02)
      · exact Or.inl ⟨rfl, rfl⟩
    have hpar : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (v j) (v i) := fun i hi => by
      fin_cases i; exact absurd rfl hi; exact ⟨⟨0, by decide⟩, by decide, hO'.1 _ _ e01⟩
      exact ⟨⟨0, by decide⟩, by decide, hO'.1 _ _ e02⟩; exact ⟨⟨0, by decide⟩, by decide, (hO'.1 _ _ e30).symm⟩
    obtain ⟨hno_AH, hno_HB, _, _, _, _, _, _⟩ := heart_four_structure D' hT hO' v hv_inj hpar A' hvA hAi hBo hAB
    by_cases hM3 : ∃ x ∈ A', D'.Adj (v ⟨3, by decide⟩) x
    · by_cases hM1 : ∃ y ∈ Finset.univ \ (Finset.univ.image v ∪ A'), D'.Adj y (v ⟨1, by decide⟩)
      · by_cases hM2 : ∃ y ∈ Finset.univ \ (Finset.univ.image v ∪ A'), D'.Adj y (v ⟨2, by decide⟩)
        · exact embeds_heart_four_S4ppm hW hT hO' v hv_inj e30 e01 e02 honlyD A' hvA hAi hBo hAB hM3 hM1 hM2 hV hG' hNS hNK
        · push Not at hM2
          exact hH3' (heart_four_drop_leaf_to_A v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
            ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨3, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩
            (by decide) (Or.inl ⟨e30, e01⟩) e02 (fun j hD => by rcases honlyD j ⟨2, by decide⟩ hD with ⟨_, h⟩ | ⟨_, h⟩ | ⟨rfl, _⟩ <;> first | rfl | (simp at h)) hM2)
      · push Not at hM1
        exact hH3' (heart_four_drop_leaf_to_A v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
          ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨3, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩
          (by decide) (Or.inl ⟨e30, e02⟩) e01 (fun j hD => by rcases honlyD j ⟨1, by decide⟩ hD with ⟨_, h⟩ | ⟨rfl, _⟩ | ⟨_, h⟩ <;> first | rfl | (simp at h)) hM1)
    · push Not at hM3
      exact hH3' (heart_four_drop_leaf_to_B v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
        ⟨3, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
        (by decide) (Or.inr (Or.inl ⟨e01, e02⟩)) e30 (fun j hD => by rcases honlyD ⟨3, by decide⟩ j hD with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> first | rfl | (simp at h)) hM3)
  have hdo_S4ppp : ∀ {D' : Digraph W} [DecidableRel D'.Adj] {G' : Digraph V} [DecidableRel G'.Adj],
      D'.IsOrientation T → G'.IsTournament →
      ((∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
        ((D'.Adj u1 u2 ∧ D'.Adj u2 u3) ∨ (D'.Adj u1 u2 ∧ D'.Adj u1 u3) ∨ (D'.Adj u2 u1 ∧ D'.Adj u3 u1)) ∧
        ∃ A' : Finset W, u1 ∉ A' ∧ u2 ∉ A' ∧ u3 ∉ A' ∧
          (∀ x ∈ A', (Finset.univ.filter (fun z : W => D'.Adj z x)).card = 1) ∧
          (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → (Finset.univ.filter (fun z : W => D'.Adj y z)).card = 1) ∧
          (∀ x ∈ A', ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → ¬ D'.Adj x y ∧ ¬ D'.Adj y x)) → Embeds D' G') →
      ∀ (v : Fin 4 → W), Function.Injective v →
      D'.Adj (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) → D'.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) → D'.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) →
      ∀ (A' : Finset W), (∀ i : Fin 4, v i ∉ A') →
      (∀ x ∈ A', (Finset.univ.filter (fun z : W => D'.Adj z x)).card = 1) →
      (∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A' → (Finset.univ.filter (fun z : W => D'.Adj y z)).card = 1) →
      (∀ x ∈ A', ∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A' → ¬ D'.Adj x y ∧ ¬ D'.Adj y x) →
      Embeds D' G' := by
    intro D' _ G' _ hO' hG' hH3' v hv_inj e01 e02 e03 A' hvA hAi hBo hAB
    have honlyT := tree_star4_only_adj hT v hv_inj (hO'.1 _ _ e01) (hO'.1 _ _ e02) (hO'.1 _ _ e03)
    have honlyD : ∀ i j : Fin 4, D'.Adj (v i) (v j) → i = ⟨0, by decide⟩ ∧ j ≠ ⟨0, by decide⟩ := by
      intro i j hD
      rcases honlyT i j (hO'.1 _ _ hD) with h | ⟨rfl, hi0⟩
      · exact h
      · exfalso; fin_cases i
        · exact hi0 rfl
        · exact not_adj_rev_of_isOrientation hO' e01 hD
        · exact not_adj_rev_of_isOrientation hO' e02 hD
        · exact not_adj_rev_of_isOrientation hO' e03 hD
    have hpar : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (v j) (v i) := fun i hi => by
      fin_cases i; exact absurd rfl hi; exact ⟨⟨0, by decide⟩, by decide, hO'.1 _ _ e01⟩
      exact ⟨⟨0, by decide⟩, by decide, hO'.1 _ _ e02⟩; exact ⟨⟨0, by decide⟩, by decide, hO'.1 _ _ e03⟩
    obtain ⟨hno_AH, hno_HB, _, _, _, _, _, _⟩ := heart_four_structure D' hT hO' v hv_inj hpar A' hvA hAi hBo hAB
    by_cases hM1 : ∃ y ∈ Finset.univ \ (Finset.univ.image v ∪ A'), D'.Adj y (v ⟨1, by decide⟩)
    · by_cases hM2 : ∃ y ∈ Finset.univ \ (Finset.univ.image v ∪ A'), D'.Adj y (v ⟨2, by decide⟩)
      · by_cases hM3 : ∃ y ∈ Finset.univ \ (Finset.univ.image v ∪ A'), D'.Adj y (v ⟨3, by decide⟩)
        · exact embeds_heart_four_S4ppp hW hT hO' v hv_inj e01 e02 e03 honlyD A' hvA hAi hBo hAB hM1 hM2 hM3 hV hG'
        · push Not at hM3
          exact hH3' (heart_four_drop_leaf_to_A v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
            ⟨3, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
            (by decide) (Or.inr (Or.inl ⟨e01, e02⟩)) e03 (fun j hD => (honlyD j ⟨3, by decide⟩ hD).1) hM3)
      · push Not at hM2
        exact hH3' (heart_four_drop_leaf_to_A v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
          ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩
          (by decide) (Or.inr (Or.inl ⟨e01, e03⟩)) e02 (fun j hD => (honlyD j ⟨2, by decide⟩ hD).1) hM2)
    · push Not at hM1
      exact hH3' (heart_four_drop_leaf_to_A v hv_inj A' hvA hAi hBo hAB hno_AH hno_HB
        ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩
        (by decide) (Or.inr (Or.inl ⟨e02, e03⟩)) e01 (fun j hD => (honlyD j ⟨1, by decide⟩ hD).1) hM1)
  -- Reversed digraph / tournament setup for arc-reversal cases
  let Drev : Digraph W := ⟨fun x y => D.Adj y x⟩
  let Grev : Digraph V := ⟨fun x y => G.Adj y x⟩
  have hOrev : Drev.IsOrientation T := ⟨fun x y h => (hO.1 y x h).symm, fun x y h => hO.2 y x h.symm⟩
  have hGrev : Grev.IsTournament := ⟨fun v => hG.1 v, fun x y hne => hG.2 y x hne.symm⟩
  have hH3_rev : (∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
      ((Drev.Adj u1 u2 ∧ Drev.Adj u2 u3) ∨ (Drev.Adj u1 u2 ∧ Drev.Adj u1 u3) ∨ (Drev.Adj u2 u1 ∧ Drev.Adj u3 u1)) ∧
      ∃ A' : Finset W, u1 ∉ A' ∧ u2 ∉ A' ∧ u3 ∉ A' ∧
        (∀ x ∈ A', (Finset.univ.filter (fun z : W => Drev.Adj z x)).card = 1) ∧
        (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → (Finset.univ.filter (fun z : W => Drev.Adj y z)).card = 1) ∧
        (∀ x ∈ A', ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A' → ¬ Drev.Adj x y ∧ ¬ Drev.Adj y x)) →
      Embeds Drev Grev := by
    intro h; obtain ⟨f, hfinj⟩ := hH3 (hasHeart3_rev h)
    exact ⟨⟨f, fun hxy => f.map_adj' hxy⟩, hfinj⟩
  -- Helper: transport Heart-4 conditions along any permutation of u (and optionally reverse D <-> Drev)
  let B : Finset W := Finset.univ \ (Finset.univ.image u ∪ A)
  have hB_rev_A : ∀ (v : Fin 4 → W) (hv_img : Finset.univ.image v = Finset.univ.image u),
      (∀ i : Fin 4, v i ∉ B) ∧
      (∀ x ∈ B, (Finset.univ.filter (fun z : W => Drev.Adj z x)).card = 1) ∧
      (∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ B → (Finset.univ.filter (fun z : W => Drev.Adj y z)).card = 1) ∧
      (∀ x ∈ B, ∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ B → ¬ Drev.Adj x y ∧ ¬ Drev.Adj y x) := by
    intro v hv_img
    have hmem_v : ∀ w, (∃ i : Fin 4, w = v i) ↔ (∃ i : Fin 4, w = u i) := by
      intro w; have := Finset.ext_iff.mp hv_img w
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at this
      exact ⟨fun ⟨i, hi⟩ => by obtain ⟨j, hj⟩ := this.mp ⟨i, hi.symm⟩; exact ⟨j, hj.symm⟩,
        fun ⟨j, hj⟩ => by obtain ⟨i, hi⟩ := this.mpr ⟨j, hj.symm⟩; exact ⟨i, hi.symm⟩⟩
    refine ⟨fun i hi => (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ (hv_img ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)),
      fun x hxB => by
        have hnot := (Finset.mem_sdiff.mp hxB).2
        exact hB_out x (fun i hi => hnot (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
          (fun h => hnot (Finset.mem_union_right _ h)),
      fun y hyv hyB => by
        have hyA : y ∈ A := by
          by_contra hnotA; exact hyB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim
            (fun hH => by obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hH; obtain ⟨i, hi⟩ := (hmem_v y).mpr ⟨j, hj.symm⟩; exact hyv i hi) hnotA⟩)
        exact hA_in y hyA,
      fun x hxB y hyv hyB => by
        have hyA : y ∈ A := by
          by_contra hnotA; exact hyB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim
            (fun hH => by obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hH; obtain ⟨i, hi⟩ := (hmem_v y).mpr ⟨j, hj.symm⟩; exact hyv i hi) hnotA⟩)
        have hnot := (Finset.mem_sdiff.mp hxB).2
        have h := hno_AB y hyA x (fun i hi => hnot (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
          (fun h => hnot (Finset.mem_union_right _ h))
        exact ⟨h.1, h.2⟩⟩
  -- Handle ANY T-star (8 orientations) and ANY T-path (8 orientations)!
  have hsolve_star : ∀ (v : Fin 4 → W), Function.Injective v → Finset.univ.image v = Finset.univ.image u →
      T.Adj (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) → T.Adj (v ⟨0, by decide⟩) (v ⟨2, by decide⟩) →
      T.Adj (v ⟨0, by decide⟩) (v ⟨3, by decide⟩) → Embeds D G := by
    intro v hv_inj hv_img t01 t02 t03
    have hmem_v : ∀ w, (∀ i : Fin 4, w ≠ v i) → (∀ i : Fin 4, w ≠ u i) := by
      intro w hw j hj
      have : w ∈ Finset.univ.image v := hv_img ▸ (hj ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp this; exact hw i hi.symm
    have hvA : ∀ i : Fin 4, v i ∉ A := fun i => by
      have : v i ∈ Finset.univ.image u := hv_img ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp this; exact hj ▸ hHA_disj j
    have hBo' : ∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A → (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1 :=
      fun y hy => hB_out y (hmem_v y hy)
    have hAB' : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ v i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x :=
      fun x hx y hy => hno_AB x hx y (hmem_v y hy)
    obtain ⟨hvB, hBi, hAo, hBA⟩ := hB_rev_A v hv_img
    have hperm_star : ∀ (π : Fin 4 → Fin 4), Function.Injective π →
        (D.Adj (v (π ⟨3, by decide⟩)) (v (π ⟨0, by decide⟩)) ∧ D.Adj (v (π ⟨0, by decide⟩)) (v (π ⟨1, by decide⟩)) ∧ D.Adj (v (π ⟨0, by decide⟩)) (v (π ⟨2, by decide⟩)) ∨
         D.Adj (v (π ⟨0, by decide⟩)) (v (π ⟨3, by decide⟩)) ∧ D.Adj (v (π ⟨1, by decide⟩)) (v (π ⟨0, by decide⟩)) ∧ D.Adj (v (π ⟨2, by decide⟩)) (v (π ⟨0, by decide⟩))) →
        Embeds D G := by
      intro π hπ_inj hor
      have hπ_surj := Finite.surjective_of_injective hπ_inj
      let v' : Fin 4 → W := fun i => v (π i)
      have hv'_img : Finset.univ.image v' = Finset.univ.image u := by
        rw [← hv_img]; ext w; simp only [v', Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨fun ⟨i, hi⟩ => ⟨π i, hi⟩, fun ⟨j, hj⟩ => by obtain ⟨i, rfl⟩ := hπ_surj j; exact ⟨i, hj⟩⟩
      rcases hor with ⟨e30, e01, e02⟩ | ⟨e03, e10, e20⟩
      · exact hdo_S4ppm hO hG hNoSrc hNoSnk hH3 v' (hv_inj.comp hπ_inj) e30 e01 e02 A
          (fun i => hvA (π i)) hA_in (fun y hy => hBo' y (fun j => by obtain ⟨i, rfl⟩ := hπ_surj j; exact hy i))
          (fun x hx y hy => hAB' x hx y (fun j => by obtain ⟨i, rfl⟩ := hπ_surj j; exact hy i))
      · obtain ⟨hv'B, hB'i, hA'o, hB'A⟩ := hB_rev_A v' hv'_img
        exact embeds_rev (hdo_S4ppm hOrev hGrev hNoSnk hNoSrc hH3_rev v' (hv_inj.comp hπ_inj) e03 e10 e20 B hv'B hB'i hA'o hB'A)
    rcases adj_or_rev_of_isOrientation hO t01 with d01 | d10 <;>
    rcases adj_or_rev_of_isOrientation hO t02 with d02 | d20 <;>
    rcases adj_or_rev_of_isOrientation hO t03 with d03 | d30
    · exact hdo_S4ppp hO hG hH3 v hv_inj d01 d02 d03 A hvA hA_in hBo' hAB'
    · exact hperm_star id Function.injective_id (Or.inl ⟨d30, d01, d02⟩)
    · exact hperm_star (fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨2, by decide⟩)
        (fun i j h => by fin_cases i <;> fin_cases j <;> simp at h ⊢) (Or.inl ⟨d20, d01, d03⟩)
    · exact hperm_star (fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨1, by decide⟩)
        (fun i j h => by fin_cases i <;> fin_cases j <;> simp at h ⊢) (Or.inr ⟨d01, d20, d30⟩)
    · exact hperm_star (fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨1, by decide⟩)
        (fun i j h => by fin_cases i <;> fin_cases j <;> simp at h ⊢) (Or.inl ⟨d10, d02, d03⟩)
    · exact hperm_star (fun i => match i.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨2, by decide⟩)
        (fun i j h => by fin_cases i <;> fin_cases j <;> simp at h ⊢) (Or.inr ⟨d02, d10, d30⟩)
    · exact hperm_star id Function.injective_id (Or.inr ⟨d03, d10, d20⟩)
    · exact embeds_rev (hdo_S4ppp hOrev hGrev hH3_rev v hv_inj d10 d20 d30 B hvB hBi hAo hBA)
  have hsolve_path : ∀ (v : Fin 4 → W), Function.Injective v → Finset.univ.image v = Finset.univ.image u →
      T.Adj (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) → T.Adj (v ⟨1, by decide⟩) (v ⟨2, by decide⟩) →
      T.Adj (v ⟨2, by decide⟩) (v ⟨3, by decide⟩) → Embeds D G := by
    intro v hv_inj hv_img t01 t12 t23
    let vrev : Fin 4 → W := fun i => v ⟨3 - i.val, by omega⟩
    have hvrev_inj : Function.Injective vrev := fun i j h => Fin.ext (by have := congrArg Fin.val (hv_inj h); dsimp only at this; omega)
    have hvrev_img : Finset.univ.image vrev = Finset.univ.image u := by
      rw [← hv_img]; ext w; simp only [vrev, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi⟩ => ⟨⟨3 - i.val, by omega⟩, hi⟩, fun ⟨i, hi⟩ => ⟨⟨3 - i.val, by omega⟩, by convert hi using 2; apply Fin.ext; dsimp only; omega⟩⟩
    have hmem_v : ∀ w, (∀ i : Fin 4, w ≠ v i) → (∀ i : Fin 4, w ≠ u i) := by
      intro w hw j hj
      have : w ∈ Finset.univ.image v := hv_img ▸ (hj ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp this; exact hw i hi.symm
    have hmem_vr : ∀ w, (∀ i : Fin 4, w ≠ vrev i) → (∀ i : Fin 4, w ≠ u i) := by
      intro w hw j hj
      have : w ∈ Finset.univ.image vrev := hvrev_img ▸ (hj ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp this; exact hw i hi.symm
    have hvA : ∀ i : Fin 4, v i ∉ A := fun i => by
      have : v i ∈ Finset.univ.image u := hv_img ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp this; exact hj ▸ hHA_disj j
    have hvrA : ∀ i : Fin 4, vrev i ∉ A := fun i => hvA ⟨3 - i.val, by omega⟩
    obtain ⟨hvB, hBi, hAo, hBA⟩ := hB_rev_A v hv_img
    obtain ⟨hvrB, hBri, hAro, hBrA⟩ := hB_rev_A vrev hvrev_img
    rcases adj_or_rev_of_isOrientation hO t01 with d01 | d10 <;>
    rcases adj_or_rev_of_isOrientation hO t12 with d12 | d21 <;>
    rcases adj_or_rev_of_isOrientation hO t23 with d23 | d32
    · exact hdo_P4ppp hO hG hNoSrc hNoSnk hH3 v hv_inj d01 d12 d23 A hvA hA_in (fun y hy => hB_out y (hmem_v y hy)) (fun x hx y hy => hno_AB x hx y (hmem_v y hy))
    · exact hdo_P4ppm hO hG hH3 v hv_inj d01 d12 d32 A hvA hA_in (fun y hy => hB_out y (hmem_v y hy)) (fun x hx y hy => hno_AB x hx y (hmem_v y hy))
    · exact hdo_P4pmp hO hG hH3 v hv_inj d01 d21 d23 A hvA hA_in (fun y hy => hB_out y (hmem_v y hy)) (fun x hx y hy => hno_AB x hx y (hmem_v y hy))
    · exact hdo_P4ppm hO hG hH3 vrev hvrev_inj d32 d21 d01 A hvrA hA_in (fun y hy => hB_out y (hmem_vr y hy)) (fun x hx y hy => hno_AB x hx y (hmem_vr y hy))
    · exact embeds_rev (hdo_P4ppm hOrev hGrev hH3_rev vrev hvrev_inj d23 d12 d10 B hvrB hBri hAro hBrA)
    · exact hdo_P4pmp hO hG hH3 vrev hvrev_inj d32 d12 d10 A hvrA hA_in (fun y hy => hB_out y (hmem_vr y hy)) (fun x hx y hy => hno_AB x hx y (hmem_vr y hy))
    · exact embeds_rev (hdo_P4ppm hOrev hGrev hH3_rev v hv_inj d10 d21 d23 B hvB hBi hAo hBA)
    · exact hdo_P4ppp hO hG hNoSrc hNoSnk hH3 vrev hvrev_inj d32 d21 d10 A hvrA hA_in (fun y hy => hB_out y (hmem_vr y hy)) (fun x hx y hy => hno_AB x hx y (hmem_vr y hy))
  -- Classify (p(1), p(2), p(3)) from hT_parent into the 6 trees on 4 vertices (2 stars, 4 paths)!
  obtain ⟨p1, hp1_lt, ht1⟩ := hT_parent ⟨1, by decide⟩ (by decide)
  have hp1 : p1 = ⟨0, by decide⟩ := Fin.ext (by dsimp only at hp1_lt ⊢; omega)
  subst hp1
  obtain ⟨p2, hp2_lt, ht2⟩ := hT_parent ⟨2, by decide⟩ (by decide)
  obtain ⟨p3, hp3_lt, ht3⟩ := hT_parent ⟨3, by decide⟩ (by decide)
  have himg_perm : ∀ (π : Fin 4 → Fin 4), Function.Injective π → Finset.univ.image (fun i => u (π i)) = Finset.univ.image u := by
    intro π hπ; have hs := Finite.surjective_of_injective hπ
    ext w; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨π i, hi⟩, fun ⟨j, hj⟩ => by obtain ⟨i, rfl⟩ := hs j; exact ⟨i, hj⟩⟩
  fin_cases p2
  · fin_cases p3
    · -- (0, 0, 0): star at u 0
      exact hsolve_star u hu_inj rfl ht1 ht2 ht3
    · -- (0, 0, 1): path u2 - u0 - u1 - u3
      let π : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨2, by decide⟩ | 1 => ⟨0, by decide⟩ | 2 => ⟨1, by decide⟩ | _ => ⟨3, by decide⟩
      have hπ : Function.Injective π := fun i j h => by fin_cases i <;> fin_cases j <;> simp [π] at h ⊢
      exact hsolve_path (fun i => u (π i)) (hu_inj.comp hπ) (himg_perm π hπ) ht2.symm ht1 ht3
    · -- (0, 0, 2): path u1 - u0 - u2 - u3
      let π : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨1, by decide⟩ | 1 => ⟨0, by decide⟩ | 2 => ⟨2, by decide⟩ | _ => ⟨3, by decide⟩
      have hπ : Function.Injective π := fun i j h => by fin_cases i <;> fin_cases j <;> simp [π] at h ⊢
      exact hsolve_path (fun i => u (π i)) (hu_inj.comp hπ) (himg_perm π hπ) ht1.symm ht2 ht3
    · simp at hp3_lt
  · fin_cases p3
    · -- (0, 1, 0): path u3 - u0 - u1 - u2
      let π : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨3, by decide⟩ | 1 => ⟨0, by decide⟩ | 2 => ⟨1, by decide⟩ | _ => ⟨2, by decide⟩
      have hπ : Function.Injective π := fun i j h => by fin_cases i <;> fin_cases j <;> simp [π] at h ⊢
      exact hsolve_path (fun i => u (π i)) (hu_inj.comp hπ) (himg_perm π hπ) ht3.symm ht1 ht2
    · -- (0, 1, 1): star at u 1
      let π : Fin 4 → Fin 4 := fun i => match i.val with | 0 => ⟨1, by decide⟩ | 1 => ⟨0, by decide⟩ | 2 => ⟨2, by decide⟩ | _ => ⟨3, by decide⟩
      have hπ : Function.Injective π := fun i j h => by fin_cases i <;> fin_cases j <;> simp [π] at h ⊢
      exact hsolve_star (fun i => u (π i)) (hu_inj.comp hπ) (himg_perm π hπ) ht1.symm ht2 ht3
    · -- (0, 1, 2): path u0 - u1 - u2 - u3
      exact hsolve_path u hu_inj rfl ht1 ht2 ht3
    · simp at hp3_lt
  · simp at hp2_lt
  · simp at hp2_lt


end ProofWork.HeartFourStep

theorem OMA.solution : OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1_H3_R1.H1 := by
  intro n _hn9 W _ _ D _ hW hTree hNotH3 ⟨u, hu_inj, hH_parent, A, hHA_disj, hA_in, hB_out, hno_AB⟩ V _ _ G _ hV hG hNoSrc hNoSnk
  exact ProofWork.HeartFourStep.embeds_heart_four D hW hTree G hV hG hNoSrc hNoSnk
    (fun h => absurd h hNotH3) u hu_inj hH_parent A hHA_disj hA_in hB_out hno_AB
