import FormalConjectures.ErdosProblems.«59»
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Data.Nat.Choose.Bounds

/-!
Self-contained proof of `Erdos59.erdos_59.variants.erdos_frankl_rodl` (Erdős–Frankl–Rödl 1986):
for any non-bipartite graph `H` on `Fin k`, the number of labelled `H`-free graphs on `Fin n` is
at most `2 ^ ((1 + ε) * extremalNumber n H)` for all sufficiently large `n`.

Proof architecture:
1. Regularity embedding lemma: a homomorphism of `H` into the dense `η`-uniform reduced graph of
   an equipartition yields a copy of `H` in `G`.
2. Container family `C` via Szemerédi's regularity lemma (`szemeredi_regularity`), indexed by
   `M`-colorings, reduced graphs on `Fin M`, and sparse remainder graphs (`≤ β n^2` edges),
   counted via the elementary binomial generating-function bound `t^r ∑_{j ≤ r} C(N, j) ≤ (1 + t)^N`.
3. Supersaturation (`H2`) and bipartite lower bound (`H3`), adapted from the merged reduction
   `Erdos59.erdos_59.variants.erdos_frankl_rodl.R1`, closing `Erdos59.erdos_59.variants.erdos_frankl_rodl`.
-/

open Filter SimpleGraph Finset Fintype SzemerediRegularity
open scoped Classical Topology

namespace Erdos59EFR

noncomputable section

/- ### Part 1: Regularity bad-vertex bound and `H`-embedding lemma -/

private lemma bad_vertices_card_lt {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {U W C : Finset α} {η d : ℝ}
    (hη : 0 < η) (hU : U.Nonempty) (hW : W.Nonempty)
    (hunif : G.IsUniform η U W) (hdens : d ≤ (G.edgeDensity U W : ℝ))
    (hCW : C ⊆ W) (hC_card : (W.card : ℝ) * η ≤ (C.card : ℝ)) :
    ((U.filter fun u => ((C.filter (G.Adj u)).card : ℝ) ≤ (d - η) * (C.card : ℝ)).card : ℝ) <
      (U.card : ℝ) * η := by
  let B := U.filter fun u => ((C.filter (G.Adj u)).card : ℝ) ≤ (d - η) * (C.card : ℝ)
  by_contra hge
  push Not at hge
  have hBsub : B ⊆ U := Finset.filter_subset _ _
  have hBpos : (0 : ℝ) < (B.card : ℝ) := lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr hU.card_pos) hη) hge
  have hCpos : (0 : ℝ) < (C.card : ℝ) := lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr hW.card_pos) hη) hC_card
  have hclose := hunif hBsub hCW hge hC_card
  have hgt : d - η < (G.edgeDensity B C : ℝ) := by
    have h1 := (abs_lt.mp hclose).1
    linarith
  have hinter_eq : (G.interedges B C).card = ∑ u ∈ B, (C.filter (G.Adj u)).card := by
    let F : α → Finset (α × α) := fun u =>
      (C.filter (G.Adj u)).map ⟨fun w => (u, w), fun _ _ h => (Prod.mk.inj h).2⟩
    have h1 : G.interedges B C = B.biUnion F := by
      ext ⟨u, w⟩
      simp only [SimpleGraph.mem_interedges_iff, Finset.mem_biUnion, F, Finset.mem_map,
        Finset.mem_filter]
      constructor
      · rintro ⟨hu, hw, hadj⟩
        exact ⟨u, hu, w, ⟨hw, hadj⟩, rfl⟩
      · rintro ⟨u', hu', w', ⟨hw', hadj⟩, hpair⟩
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        exact ⟨hu', hw', hadj⟩
    rw [h1, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun u _ => Finset.card_map _
    · intro u1 _ u2 _ hne
      change Disjoint (F u1) (F u2)
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_map.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_map.mp hp2 with ⟨_, _, h2⟩
      exact hne (Prod.mk.inj h2).1.symm
  have hinter_le : ((G.interedges B C).card : ℝ) ≤ (B.card : ℝ) * ((d - η) * (C.card : ℝ)) := by
    rw [hinter_eq, Nat.cast_sum]
    calc ∑ u ∈ B, ((C.filter (G.Adj u)).card : ℝ)
        ≤ ∑ _u ∈ B, ((d - η) * (C.card : ℝ)) :=
          Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
      _ = (B.card : ℝ) * ((d - η) * (C.card : ℝ)) := by simp
  have hdens_le : (G.edgeDensity B C : ℝ) ≤ d - η := by
    have hdef : (G.edgeDensity B C : ℝ) = ((G.interedges B C).card : ℝ) / ((B.card : ℝ) * (C.card : ℝ)) := by
      rw [← SimpleGraph.card_interedges_div_card]
      push_cast
      rfl
    rw [hdef, div_le_iff₀ (mul_pos hBpos hCpos)]
    linarith
  linarith

private lemma embedding_of_uniform_hom {k n : ℕ}
    (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (φ : Fin k → Finset (Fin n))
    {η d s : ℝ} (hη : 0 < η) (_hd : 0 < d) (hηd : η < d) (hd1 : d ≤ 1)
    (hs_pos : 0 < s)
    (hpart_card : ∀ i : Fin k, s ≤ ((φ i).card : ℝ))
    (hpart_unif : ∀ i j : Fin k, H.Adj i j →
      G.IsUniform η (φ i) (φ j) ∧ d ≤ (G.edgeDensity (φ i) (φ j) : ℝ))
    (hη_small : 2 * (k : ℝ) * η ≤ (d - η) ^ k)
    (hs_big : 2 * (k : ℝ) < (d - η) ^ k * s) :
    ¬ H.Free G := by
  have hdη_pos : 0 < d - η := sub_pos.mpr hηd
  have hdη_le1 : d - η ≤ 1 := by linarith
  have hpart_ne : ∀ i : Fin k, (φ i).Nonempty := by
    intro i
    have h1 : (0 : ℝ) < ((φ i).card : ℝ) := lt_of_lt_of_le hs_pos (hpart_card i)
    exact Finset.card_pos.mp (Nat.cast_pos.mp h1)
  have hpow_mono : ∀ {a b : ℕ}, a ≤ b → (d - η) ^ b ≤ (d - η) ^ a := fun hab =>
    pow_le_pow_of_le_one hdη_pos.le hdη_le1 hab
  have hind : ∀ (m : ℕ) (hm : m ≤ k),
      ∃ f : Fin m → Fin n,
        (∀ a : Fin m, f a ∈ φ ⟨a.1, lt_of_lt_of_le a.2 hm⟩) ∧
        Function.Injective f ∧
        (∀ a b : Fin m, H.Adj ⟨a.1, lt_of_lt_of_le a.2 hm⟩ ⟨b.1, lt_of_lt_of_le b.2 hm⟩ →
          G.Adj (f a) (f b)) ∧
        (∀ j : Fin k, m ≤ j.1 →
          (d - η) ^ m * ((φ j).card : ℝ) ≤
            (((φ j).filter fun w => ∀ a : Fin m,
              H.Adj ⟨a.1, lt_of_lt_of_le a.2 hm⟩ j → G.Adj (f a) w).card : ℝ)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, ?_⟩
      intro j _
      simp
    | succ m ih =>
      intro hms
      obtain ⟨f, hf_mem, hf_inj, hf_adj, hf_cand⟩ := ih (Nat.le_of_succ_le hms)
      let i0 : Fin k := ⟨m, hms⟩
      let Ci0 : Finset (Fin n) := (φ i0).filter fun w =>
        ∀ a : Fin m, H.Adj ⟨a.1, lt_of_lt_of_le a.2 (Nat.le_of_succ_le hms)⟩ i0 → G.Adj (f a) w
      have hCi0_card : (d - η) ^ k * ((φ i0).card : ℝ) ≤ (Ci0.card : ℝ) := by
        have h1 := hf_cand i0 le_rfl
        have h2 : (d - η) ^ k ≤ (d - η) ^ m := hpow_mono (Nat.le_of_succ_le hms)
        exact (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)).trans h1
      let Future := Finset.univ.filter fun j : Fin k => m + 1 ≤ j.1 ∧ H.Adj i0 j
      let Cj (j : Fin k) : Finset (Fin n) := (φ j).filter fun w =>
        ∀ a : Fin m, H.Adj ⟨a.1, lt_of_lt_of_le a.2 (Nat.le_of_succ_le hms)⟩ j → G.Adj (f a) w
      let Bad (j : Fin k) : Finset (Fin n) :=
        (φ i0).filter fun u => (((Cj j).filter (G.Adj u)).card : ℝ) ≤ (d - η) * ((Cj j).card : ℝ)
      have hBad_lt : ∀ j ∈ Future, ((Bad j).card : ℝ) < ((φ i0).card : ℝ) * η := by
        intro j hj
        have hj1 := (Finset.mem_filter.mp hj).2.1
        have hjadj := (Finset.mem_filter.mp hj).2.2
        have hCj_ge : ((φ j).card : ℝ) * η ≤ ((Cj j).card : ℝ) := by
          have h1 := hf_cand j (by omega)
          have h2 : η ≤ (d - η) ^ m := by
            have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
            have h3 : η ≤ (d - η) ^ k := by nlinarith
            exact h3.trans (hpow_mono (Nat.le_of_succ_le hms))
          calc ((φ j).card : ℝ) * η = η * ((φ j).card : ℝ) := mul_comm _ _
            _ ≤ (d - η) ^ m * ((φ j).card : ℝ) := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
            _ ≤ ((Cj j).card : ℝ) := h1
        have hpair := hpart_unif i0 j hjadj
        exact bad_vertices_card_lt G hη (hpart_ne i0) (hpart_ne j) hpair.1 hpair.2
          (Finset.filter_subset _ _) hCj_ge
      let Used : Finset (Fin n) := Finset.univ.image f
      let AllBad : Finset (Fin n) := Used ∪ Future.biUnion Bad
      have hAllBad_le : (AllBad.card : ℝ) ≤ (m : ℝ) + (k : ℝ) * (((φ i0).card : ℝ) * η) := by
        have h1 : AllBad.card ≤ Used.card + (Future.biUnion Bad).card := Finset.card_union_le _ _
        have h2 : Used.card ≤ m := by
          calc Used.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
            _ = m := by simp
        have h3 : ((Future.biUnion Bad).card : ℝ) ≤ (k : ℝ) * (((φ i0).card : ℝ) * η) := by
          have hbi : ((Future.biUnion Bad).card : ℝ) ≤ ∑ j ∈ Future, ((Bad j).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
          have hsum : ∑ j ∈ Future, ((Bad j).card : ℝ) ≤ ∑ _j ∈ Future, (((φ i0).card : ℝ) * η) :=
            Finset.sum_le_sum fun j hj => (hBad_lt j hj).le
          have hFc : (Future.card : ℝ) ≤ (k : ℝ) := by
            have : Future.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
            simpa using (Nat.cast_le (α := ℝ)).mpr this
          calc ((Future.biUnion Bad).card : ℝ)
              ≤ ∑ _j ∈ Future, (((φ i0).card : ℝ) * η) := hbi.trans hsum
            _ = (Future.card : ℝ) * (((φ i0).card : ℝ) * η) := by simp
            _ ≤ (k : ℝ) * (((φ i0).card : ℝ) * η) := mul_le_mul_of_nonneg_right hFc (by positivity)
        have h1R : (AllBad.card : ℝ) ≤ (Used.card : ℝ) + ((Future.biUnion Bad).card : ℝ) := by exact_mod_cast h1
        have h2R : (Used.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2
        linarith
      have hGood_ne : (Ci0 \ AllBad).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : Ci0 ⊆ AllBad := Finset.sdiff_eq_empty_iff_subset.mp hemp
        have hle : (Ci0.card : ℝ) ≤ (AllBad.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        have hcard_i0 : s ≤ ((φ i0).card : ℝ) := hpart_card i0
        have hprod1 : 2 * (k : ℝ) < (d - η) ^ k * ((φ i0).card : ℝ) :=
          lt_of_lt_of_le hs_big (mul_le_mul_of_nonneg_left hcard_i0 (pow_nonneg hdη_pos.le k))
        have hprod2 : (k : ℝ) * (((φ i0).card : ℝ) * η) ≤ (1 / 2) * ((d - η) ^ k * ((φ i0).card : ℝ)) := by
          have : (k : ℝ) * η ≤ (1 / 2) * (d - η) ^ k := by linarith
          have hm := mul_le_mul_of_nonneg_right this (Nat.cast_nonneg (α := ℝ) (φ i0).card)
          linarith
        have hmk : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.le_of_succ_le hms)
        linarith
      obtain ⟨v, hv⟩ := hGood_ne
      have hv_Ci0 : v ∈ Ci0 := (Finset.mem_sdiff.mp hv).1
      have hv_nAllBad : v ∉ AllBad := (Finset.mem_sdiff.mp hv).2
      have hv_phi : v ∈ φ i0 := (Finset.mem_filter.mp hv_Ci0).1
      have hv_adj_prev : ∀ a : Fin m, H.Adj ⟨a.1, lt_of_lt_of_le a.2 (Nat.le_of_succ_le hms)⟩ i0 →
          G.Adj (f a) v := (Finset.mem_filter.mp hv_Ci0).2
      have hv_nUsed : v ∉ Used := fun h => hv_nAllBad (Finset.mem_union_left _ h)
      have hv_nBad : ∀ j ∈ Future, v ∉ Bad j := fun j hj h =>
        hv_nAllBad (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, h⟩))
      let f' : Fin (m + 1) → Fin n := fun a =>
        if h : a.1 < m then f ⟨a.1, h⟩ else v
      refine ⟨f', ?_, ?_, ?_, ?_⟩
      · intro a
        by_cases ha : a.1 < m
        · simp only [f', dif_pos ha]; exact hf_mem ⟨a.1, ha⟩
        · simp only [f', dif_neg ha]
          have heq : (⟨a.1, lt_of_lt_of_le a.2 hms⟩ : Fin k) = i0 := Fin.ext (by dsimp [i0]; omega)
          rw [heq]; exact hv_phi
      · intro a b hab
        by_cases ha : a.1 < m <;> by_cases hb : b.1 < m
        · simp only [f', dif_pos ha, dif_pos hb] at hab
          exact Fin.ext (congrArg (Fin.val : Fin m → ℕ) (hf_inj hab))
        · simp only [f', dif_pos ha, dif_neg hb] at hab
          exfalso; exact hv_nUsed (Finset.mem_image.mpr ⟨⟨a.1, ha⟩, Finset.mem_univ _, hab⟩)
        · simp only [f', dif_neg ha, dif_pos hb] at hab
          exfalso; exact hv_nUsed (Finset.mem_image.mpr ⟨⟨b.1, hb⟩, Finset.mem_univ _, hab.symm⟩)
        · exact Fin.ext (by omega)
      · intro a b hadj
        by_cases ha : a.1 < m <;> by_cases hb : b.1 < m
        · simp only [f', dif_pos ha, dif_pos hb]
          exact hf_adj ⟨a.1, ha⟩ ⟨b.1, hb⟩ hadj
        · simp only [f', dif_pos ha, dif_neg hb]
          have hb' : (⟨b.1, lt_of_lt_of_le b.2 hms⟩ : Fin k) = i0 := Fin.ext (by dsimp [i0]; omega)
          rw [hb'] at hadj
          exact hv_adj_prev ⟨a.1, ha⟩ hadj
        · simp only [f', dif_neg ha, dif_pos hb]
          have ha' : (⟨a.1, lt_of_lt_of_le a.2 hms⟩ : Fin k) = i0 := Fin.ext (by dsimp [i0]; omega)
          rw [ha'] at hadj
          exact (hv_adj_prev ⟨b.1, hb⟩ hadj.symm).symm
        · exfalso
          have hab_eq : (⟨a.1, lt_of_lt_of_le a.2 hms⟩ : Fin k) = ⟨b.1, lt_of_lt_of_le b.2 hms⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hab_eq] at hadj
          exact H.loopless.irrefl _ hadj
      · intro j hj
        by_cases hadj : H.Adj i0 j
        · have hjF : j ∈ Future := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hadj⟩
          have hv_good : (d - η) * ((Cj j).card : ℝ) < (((Cj j).filter (G.Adj v)).card : ℝ) := by
            have hnb := hv_nBad j hjF
            simp only [Bad, Finset.mem_filter, hv_phi, true_and, not_le] at hnb
            exact hnb
          have hsub : (Cj j).filter (G.Adj v) ⊆
              (φ j).filter fun w => ∀ a : Fin (m + 1),
                H.Adj ⟨a.1, lt_of_lt_of_le a.2 hms⟩ j → G.Adj (f' a) w := by
            intro w hw
            have hw1 := (Finset.mem_filter.mp hw).1
            have hwv := (Finset.mem_filter.mp hw).2
            refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw1).1, ?_⟩
            intro a ha
            dsimp [f']
            split_ifs with hlt
            · exact (Finset.mem_filter.mp hw1).2 ⟨a.1, hlt⟩ ha
            · exact hwv
          have hcard_le : (((Cj j).filter (G.Adj v)).card : ℝ) ≤
              (((φ j).filter fun w => ∀ a : Fin (m + 1),
                H.Adj ⟨a.1, lt_of_lt_of_le a.2 hms⟩ j → G.Adj (f' a) w).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
          have hprev := hf_cand j (by omega)
          calc (d - η) ^ (m + 1) * ((φ j).card : ℝ)
              = (d - η) * ((d - η) ^ m * ((φ j).card : ℝ)) := by ring
            _ ≤ (d - η) * ((Cj j).card : ℝ) := mul_le_mul_of_nonneg_left hprev hdη_pos.le
            _ ≤ (((Cj j).filter (G.Adj v)).card : ℝ) := hv_good.le
            _ ≤ _ := hcard_le
        · have hsub : Cj j ⊆
              (φ j).filter fun w => ∀ a : Fin (m + 1),
                H.Adj ⟨a.1, lt_of_lt_of_le a.2 hms⟩ j → G.Adj (f' a) w := by
            intro w hw
            refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, ?_⟩
            intro a ha
            dsimp [f']
            split_ifs with hlt
            · exact (Finset.mem_filter.mp hw).2 ⟨a.1, hlt⟩ ha
            · exfalso
              have ha' : (⟨a.1, lt_of_lt_of_le a.2 hms⟩ : Fin k) = i0 := Fin.ext (by dsimp [i0]; omega)
              rw [ha'] at ha
              exact hadj ha
          have hcard_le : ((Cj j).card : ℝ) ≤
              (((φ j).filter fun w => ∀ a : Fin (m + 1),
                H.Adj ⟨a.1, lt_of_lt_of_le a.2 hms⟩ j → G.Adj (f' a) w).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
          have hprev := hf_cand j (by omega)
          have hmono : (d - η) ^ (m + 1) ≤ (d - η) ^ m := hpow_mono (Nat.le_succ m)
          calc (d - η) ^ (m + 1) * ((φ j).card : ℝ)
              ≤ (d - η) ^ m * ((φ j).card : ℝ) := mul_le_mul_of_nonneg_right hmono (Nat.cast_nonneg _)
            _ ≤ ((Cj j).card : ℝ) := hprev
            _ ≤ _ := hcard_le
  obtain ⟨f, _, hf_inj, hf_adj, _⟩ := hind k le_rfl
  intro hfree
  exact hfree ⟨⟨⟨f, fun {a b} hab => hf_adj a b hab⟩, hf_inj⟩⟩

/- ### Part 2: Sparse remainder edge bound for arbitrary `η ≤ β / 8` and `d = β / 4` -/

private lemma unreduced_edges_card_le {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (P : Finpartition (Finset.univ : Finset (Fin n)))
    {η β : ℝ} (hη : 0 < η) (hβ : 0 < β) (hηβ : η ≤ β / 8)
    (hP : P.IsEquipartition) (hPη : P.IsUniform G η) (hP' : 4 / β ≤ (P.parts.card : ℝ)) :
    let E_rem : SimpleGraph (Fin n) :=
      { Adj := fun u v => G.Adj u v ∧ ¬ (G.regularityReduced P η (β / 4)).Adj u v
        symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
        loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩ }
    (E_rem.edgeFinset.card : ℝ) ≤ β * (n : ℝ) ^ 2 := by
  intro E_rem
  let A := (P.nonUniforms G η).biUnion fun (U, V) ↦ U ×ˢ V
  let B := P.parts.biUnion offDiag
  let C := (P.sparsePairs G (β / 4)).biUnion fun (U, V) ↦ G.interedges U V
  have hsub : ((Finset.univ : Finset (Fin n)) ×ˢ Finset.univ).filter (fun p => E_rem.Adj p.1 p.2) ⊆
      A ∪ B ∪ C := by
    rintro ⟨x, y⟩ hxy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, E_rem,
      SimpleGraph.regularityReduced_adj, not_and, not_exists, not_le] at hxy
    rcases hxy with ⟨hG, hnot⟩
    replace hnot := hnot hG
    obtain ⟨U, hU, hx⟩ := P.exists_mem (Finset.mem_univ x)
    obtain ⟨V, hV, hy⟩ := P.exists_mem (Finset.mem_univ y)
    simp only [A, B, C, Finset.mem_union, Finset.mem_biUnion, Finset.mem_product, Prod.exists,
      Finset.mem_offDiag, Finpartition.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs,
      SimpleGraph.mem_interedges_iff]
    obtain rfl | hUV := eq_or_ne U V
    · exact Or.inl (Or.inr ⟨U, hU, hx, hy, G.ne_of_adj hG⟩)
    by_cases hu : G.IsUniform η U V
    · exact Or.inr ⟨U, V, ⟨hU, hV, hUV, hnot U hU V hV hx hy hUV hu⟩, hx, hy, hG⟩
    · exact Or.inl (Or.inl ⟨U, V, ⟨hU, hV, hUV, hu⟩, hx, hy⟩)
  have h2e : 2 * (E_rem.edgeFinset.card : ℝ) =
      ((((Finset.univ : Finset (Fin n)) ×ˢ Finset.univ).filter (fun p => E_rem.Adj p.1 p.2)).card : ℝ) := by
    have h1 : 2 * E_rem.edgeFinset.card =
        (Finset.univ.filter (fun p : Fin n × Fin n => E_rem.Adj p.1 p.2)).card := by
      simpa using E_rem.two_mul_card_edgeFinset
    have h2 : ((Finset.univ : Finset (Fin n)) ×ˢ Finset.univ).filter (fun p => E_rem.Adj p.1 p.2) =
        Finset.univ.filter (fun p : Fin n × Fin n => E_rem.Adj p.1 p.2) := by
      rw [Finset.univ_product_univ]
    rw [h2]; exact_mod_cast h1
  have hA : (A.card : ℝ) < 4 * η * (n : ℝ) ^ 2 := by
    simpa [A] using hP.sum_nonUniforms_lt (G := G) (ε := η) Finset.univ_nonempty hη hPη
  have hB : (B.card : ℝ) ≤ β / 2 * (n : ℝ) ^ 2 := by
    simpa [B] using hP.card_biUnion_offDiag_le (ε := β) hβ hP'
  have hC : (C.card : ℝ) ≤ 4 * (β / 4) * (n : ℝ) ^ 2 := by
    simpa [C] using hP.card_interedges_sparsePairs_le (G := G) (ε := β / 4) (by positivity)
  have hcard : ((((Finset.univ : Finset (Fin n)) ×ˢ Finset.univ).filter (fun p => E_rem.Adj p.1 p.2)).card : ℝ) ≤
      (A.card : ℝ) + (B.card : ℝ) + (C.card : ℝ) := by
    have h1 : (((Finset.univ : Finset (Fin n)) ×ˢ Finset.univ).filter (fun p => E_rem.Adj p.1 p.2)).card ≤
        (A ∪ B ∪ C).card := Finset.card_le_card hsub
    have h2 : (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    have h3 : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le _ _
    exact_mod_cast (h1.trans (h2.trans (Nat.add_le_add_right h3 C.card)))
  have h4η : 4 * η * (n : ℝ) ^ 2 ≤ (β / 2) * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  linarith

/- ### Part 3: Copy count of `G_dense ⊔ E_rem` when `G_dense` is `H`-free -/

private lemma copyCount_sup_le_of_free {k n : ℕ} (hk : 2 ≤ k)
    (H : SimpleGraph (Fin k)) (G_dense E_rem : SimpleGraph (Fin n))
    (hfree : H.Free G_dense) :
    (G_dense ⊔ E_rem).copyCount H ≤ 2 * k ^ 2 * E_rem.edgeFinset.card * n ^ (k - 2) := by
  let T := G_dense ⊔ E_rem
  have h1 : T.copyCount H ≤ T.labelledCopyCount H := T.copyCount_le_labelledCopyCount
  -- Every labelled copy is an injective hom f : Fin k → Fin n that must map some edge of H into E_rem
  let S_hom : Finset (Fin k → Fin n) :=
    Finset.univ.filter fun f => Function.Injective f ∧ ∀ a b, H.Adj a b → T.Adj (f a) (f b)
  have hlab_le : T.labelledCopyCount H ≤ S_hom.card := by
    rw [SimpleGraph.labelledCopyCount]
    refine Finset.card_le_card_of_injOn (fun f : H.Copy T => (f : Fin k → Fin n)) ?_ ?_
    · intro f _
      simp only [Finset.mem_coe, S_hom, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨f.injective, fun a b hab => f.toHom.map_rel' hab⟩
    · intro f1 _ f2 _ h
      exact SimpleGraph.Copy.ext (congrFun h)
  let Pairs : Finset ((Fin k × Fin k) × (Fin n × Fin n)) :=
    (Finset.univ.filter fun p : Fin k × Fin k => H.Adj p.1 p.2) ×ˢ
    (Finset.univ.filter fun q : Fin n × Fin n => E_rem.Adj q.1 q.2)
  let Fiber (pq : (Fin k × Fin k) × (Fin n × Fin n)) : Finset (Fin k → Fin n) :=
    Finset.univ.filter fun f => f pq.1.1 = pq.2.1 ∧ f pq.1.2 = pq.2.2
  have hS_sub : S_hom ⊆ Pairs.biUnion Fiber := by
    intro f hf
    rcases (Finset.mem_filter.mp hf).2 with ⟨hfinj, hfadj⟩
    have hex : ∃ a b : Fin k, H.Adj a b ∧ E_rem.Adj (f a) (f b) := by
      by_contra hno
      push Not at hno
      apply hfree
      refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, hfinj⟩⟩
      rcases hfadj a b hab with hgd | her
      · exact hgd
      · exact (hno a b hab her).elim
    obtain ⟨a, b, hab, hrem⟩ := hex
    refine Finset.mem_biUnion.mpr ⟨((a, b), (f a, f b)), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrem⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩
  have hFib_card : ∀ pq ∈ Pairs, (Fiber pq).card ≤ n ^ (k - 2) := by
    intro pq hpq
    have hab : H.Adj pq.1.1 pq.1.2 := (Finset.mem_filter.mp (Finset.mem_product.mp hpq).1).2
    have hne : pq.1.1 ≠ pq.1.2 := H.ne_of_adj hab
    let Rest : Finset (Fin k) := (Finset.univ.erase pq.1.1).erase pq.1.2
    have hRest_card : Rest.card = k - 2 := by
      have h1 : pq.1.2 ∈ (Finset.univ : Finset (Fin k)).erase pq.1.1 :=
        Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
      rw [Finset.card_erase_of_mem h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    have hinj : (Fiber pq).card ≤ (Finset.univ : Finset (Rest → Fin n)).card := by
      refine Finset.card_le_card_of_injOn (fun f => fun x : Rest => f x.1) (fun _ _ => Finset.mem_univ _) ?_
      intro f1 hf1 f2 hf2 heq
      have h1 := (Finset.mem_filter.mp hf1).2
      have h2 := (Finset.mem_filter.mp hf2).2
      funext x
      by_cases hx1 : x = pq.1.1
      · rw [hx1, h1.1, h2.1]
      · by_cases hx2 : x = pq.1.2
        · rw [hx2, h1.2, h2.2]
        · have hxR : x ∈ Rest := Finset.mem_erase.mpr ⟨hx2, Finset.mem_erase.mpr ⟨hx1, Finset.mem_univ _⟩⟩
          exact congrFun heq ⟨x, hxR⟩
    simpa [Fintype.card_pi, hRest_card] using hinj
  have hPairs_card : Pairs.card ≤ 2 * k ^ 2 * E_rem.edgeFinset.card := by
    rw [Finset.card_product]
    have hH_le : (Finset.univ.filter fun p : Fin k × Fin k => H.Adj p.1 p.2).card ≤ k ^ 2 := by
      have := Finset.card_le_card (Finset.filter_subset (fun p : Fin k × Fin k => H.Adj p.1 p.2) Finset.univ)
      simpa [sq] using this
    have hE_eq : (Finset.univ.filter fun q : Fin n × Fin n => E_rem.Adj q.1 q.2).card = 2 * E_rem.edgeFinset.card := by
      simpa using E_rem.two_mul_card_edgeFinset.symm
    rw [hE_eq]
    have := Nat.mul_le_mul_right (2 * E_rem.edgeFinset.card) hH_le
    linarith
  calc T.copyCount H ≤ S_hom.card := h1.trans hlab_le
    _ ≤ (Pairs.biUnion Fiber).card := Finset.card_le_card hS_sub
    _ ≤ ∑ pq ∈ Pairs, (Fiber pq).card := Finset.card_biUnion_le
    _ ≤ ∑ _pq ∈ Pairs, n ^ (k - 2) := Finset.sum_le_sum hFib_card
    _ = Pairs.card * n ^ (k - 2) := by simp
    _ ≤ (2 * k ^ 2 * E_rem.edgeFinset.card) * n ^ (k - 2) := Nat.mul_le_mul_right _ hPairs_card

/- ### Part 4: Elementary binomial generating-function bound for sparse graphs -/

private lemma sum_choose_le_exp (N r : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∑ j ∈ Finset.range (r + 1), (N.choose j : ℝ)) ≤ t ^ (-(r : ℤ)) * Real.exp (t * (N : ℝ)) := by
  have h1 : t ^ r * ∑ j ∈ Finset.range (r + 1), (N.choose j : ℝ) ≤ (1 + t) ^ N := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ Finset.range (r + 1), t ^ r * (N.choose j : ℝ)
        ≤ ∑ j ∈ Finset.range (r + 1), t ^ j * (N.choose j : ℝ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hpow : t ^ r ≤ t ^ j := pow_le_pow_of_le_one ht0.le ht1 hjr
          exact mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
      _ ≤ ∑ j ∈ Finset.range (max (r + 1) (N + 1)), t ^ j * (N.choose j : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
            (fun _ _ _ => by positivity)
      _ = ∑ j ∈ Finset.range (N + 1), t ^ j * (N.choose j : ℝ) := by
          symm
          refine Finset.sum_subset (Finset.range_mono (le_max_right _ _)) ?_
          intro j _ hjN
          have hgt : N < j := by rw [Finset.mem_range] at hjN; omega
          simp [Nat.choose_eq_zero_of_lt hgt]
      _ = (t + 1) ^ N := by
          rw [add_pow]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ = (1 + t) ^ N := by ring
  have h2 : (1 + t) ^ N ≤ Real.exp (t * (N : ℝ)) := by
    calc (1 + t) ^ N ≤ (Real.exp t) ^ N := pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp t]) N
      _ = Real.exp ((N : ℝ) * t) := (Real.exp_nat_mul t N).symm
      _ = Real.exp (t * (N : ℝ)) := by ring_nf
  have htr : 0 < t ^ r := pow_pos ht0 r
  have h3 : (∑ j ∈ Finset.range (r + 1), (N.choose j : ℝ)) ≤ (t ^ r)⁻¹ * Real.exp (t * (N : ℝ)) := by
    rw [← div_eq_inv_mul, le_div_iff₀ htr]
    linarith
  simpa [zpow_neg, zpow_natCast] using h3

private lemma card_sparse_graphs_le (δ1 : ℝ) (hδ1 : 0 < δ1) :
    ∃ β0 : ℝ, 0 < β0 ∧ ∀ n : ℕ,
      (((Finset.univ : Finset (SimpleGraph (Fin n))).filter
        (fun E => (E.edgeFinset.card : ℝ) ≤ β0 * (n : ℝ) ^ 2)).card : ℝ) ≤
      (2 : ℝ) ^ (δ1 * (n : ℝ) ^ 2) := by
  let t : ℝ := min (δ1 / 4) 1
  have ht0 : 0 < t := lt_min (by positivity) (by norm_num)
  have ht1 : t ≤ 1 := min_le_right _ _
  have ht_le : t ≤ δ1 / 4 := min_le_left _ _
  have hlog_nn : 0 ≤ Real.log (1 / t) := Real.log_nonneg ((one_le_div ht0).mpr ht1)
  let β0 : ℝ := δ1 / (8 * (Real.log (1 / t) + 1))
  have hβ0 : 0 < β0 := by positivity
  refine ⟨β0, hβ0, fun n => ?_⟩
  let r : ℕ := Nat.floor (β0 * (n : ℝ) ^ 2)
  let TopE : Finset (Sym2 (Fin n)) := (⊤ : SimpleGraph (Fin n)).edgeFinset
  let N : ℕ := TopE.card
  have hN_le : (N : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    have h1 : N = n.choose 2 := by
      dsimp [N, TopE]
      have h2 := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)
      simpa using h2
    rw [h1, Nat.choose_two_right]
    have h3 : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    have h4 : (n * (n - 1) / 2 : ℕ) * 2 ≤ n * (n - 1) := Nat.div_mul_le_self _ 2
    have h5 : ((n * (n - 1) / 2 : ℕ) : ℝ) * 2 ≤ (n : ℝ) ^ 2 := by
      have : (n * (n - 1) / 2) * 2 ≤ n * n := h4.trans h3
      exact_mod_cast (by simpa [sq] using this : (n * (n - 1) / 2) * 2 ≤ n ^ 2)
    linarith
  have hcard_le : ((Finset.univ : Finset (SimpleGraph (Fin n))).filter
        (fun E => (E.edgeFinset.card : ℝ) ≤ β0 * (n : ℝ) ^ 2)).card ≤
      ∑ j ∈ Finset.range (r + 1), N.choose j := by
    let S := (Finset.univ : Finset (SimpleGraph (Fin n))).filter
      (fun E => (E.edgeFinset.card : ℝ) ≤ β0 * (n : ℝ) ^ 2)
    let SubE := (Finset.range (r + 1)).biUnion fun j => TopE.powersetCard j
    have hinj : S.card ≤ SubE.card := by
      refine Finset.card_le_card_of_injOn (fun E : SimpleGraph (Fin n) => E.edgeFinset) ?_ ?_
      · intro E hE
        have hEc : (E.edgeFinset.card : ℝ) ≤ β0 * (n : ℝ) ^ 2 := (Finset.mem_filter.mp hE).2
        have hEr : E.edgeFinset.card ≤ r := Nat.le_floor hEc
        refine Finset.mem_biUnion.mpr ⟨E.edgeFinset.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hEr), ?_⟩
        exact Finset.mem_powersetCard.mpr ⟨SimpleGraph.edgeFinset_mono le_top, rfl⟩
      · intro E1 _ E2 _ h; exact SimpleGraph.edgeFinset_inj.mp h
    calc S.card ≤ SubE.card := hinj
      _ ≤ ∑ j ∈ Finset.range (r + 1), (TopE.powersetCard j).card := Finset.card_biUnion_le
      _ = ∑ j ∈ Finset.range (r + 1), N.choose j := by
          refine Finset.sum_congr rfl fun j _ => Finset.card_powersetCard j TopE
  have hsum := sum_choose_le_exp N r ht0 ht1
  have hr_le : (r : ℝ) ≤ β0 * (n : ℝ) ^ 2 := Nat.floor_le (by positivity)
  have htz : t ^ (-(r : ℤ)) = Real.exp ((r : ℝ) * Real.log (1 / t)) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, ← one_div]
    calc (1 / t) ^ r = (Real.exp (Real.log (1 / t))) ^ r := by rw [Real.exp_log (div_pos one_pos ht0)]
      _ = Real.exp ((r : ℝ) * Real.log (1 / t)) := (Real.exp_nat_mul _ r).symm
  have hprod : t ^ (-(r : ℤ)) * Real.exp (t * (N : ℝ)) =
      Real.exp ((r : ℝ) * Real.log (1 / t) + t * (N : ℝ)) := by
    rw [htz, ← Real.exp_add]
  have hexp_le : (r : ℝ) * Real.log (1 / t) + t * (N : ℝ) ≤ (δ1 * (n : ℝ) ^ 2) * Real.log 2 := by
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hterm1 : (r : ℝ) * Real.log (1 / t) ≤ (δ1 / 8) * (n : ℝ) ^ 2 := by
      have hβlog : β0 * Real.log (1 / t) ≤ δ1 / 8 := by
        dsimp [β0]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      calc (r : ℝ) * Real.log (1 / t)
          ≤ (β0 * (n : ℝ) ^ 2) * Real.log (1 / t) := mul_le_mul_of_nonneg_right hr_le hlog_nn
        _ = (β0 * Real.log (1 / t)) * (n : ℝ) ^ 2 := by ring
        _ ≤ (δ1 / 8) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hβlog (sq_nonneg _)
    have hterm2 : t * (N : ℝ) ≤ (δ1 / 8) * (n : ℝ) ^ 2 := by
      calc t * (N : ℝ) ≤ (δ1 / 4) * ((n : ℝ) ^ 2 / 2) :=
            mul_le_mul ht_le hN_le (Nat.cast_nonneg N) (by positivity)
        _ = (δ1 / 8) * (n : ℝ) ^ 2 := by ring
    nlinarith [mul_nonneg hδ1.le (sq_nonneg (n : ℝ))]
  have h2pow : Real.exp ((δ1 * (n : ℝ) ^ 2) * Real.log 2) = (2 : ℝ) ^ (δ1 * (n : ℝ) ^ 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  have hcardR : (((Finset.univ : Finset (SimpleGraph (Fin n))).filter
        (fun E => (E.edgeFinset.card : ℝ) ≤ β0 * (n : ℝ) ^ 2)).card : ℝ) ≤
      ∑ j ∈ Finset.range (r + 1), (N.choose j : ℝ) := by exact_mod_cast hcard_le
  calc (((Finset.univ : Finset (SimpleGraph (Fin n))).filter
        (fun E => (E.edgeFinset.card : ℝ) ≤ β0 * (n : ℝ) ^ 2)).card : ℝ)
      ≤ ∑ j ∈ Finset.range (r + 1), (N.choose j : ℝ) := hcardR
    _ ≤ t ^ (-(r : ℤ)) * Real.exp (t * (N : ℝ)) := hsum
    _ = Real.exp ((r : ℝ) * Real.log (1 / t) + t * (N : ℝ)) := hprod
    _ ≤ Real.exp ((δ1 * (n : ℝ) ^ 2) * Real.log 2) := Real.exp_le_exp.mpr hexp_le
    _ = (2 : ℝ) ^ (δ1 * (n : ℝ) ^ 2) := h2pow

/- ### Part 5: Regularity container theorem `H1` -/

private def blowupGraph {n M : ℕ} (col : Fin n → Fin M) (R : SimpleGraph (Fin M)) :
    SimpleGraph (Fin n) where
  Adj u v := R.Adj (col u) (col v)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => R.loopless.irrefl (col u) h⟩

private lemma container_H1 {k : ℕ} (H : SimpleGraph (Fin k)) (hH : ¬ H.IsBipartite)
    (δ : ℝ) (hδ : 0 < δ) (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop,
      ∃ C : Finset (SimpleGraph (Fin n)),
        (C.card : ℝ) ≤ (2 : ℝ) ^ (δ * (n : ℝ) ^ 2) ∧
        (∀ T ∈ C, (T.copyCount H : ℝ) ≤ γ * (n : ℝ) ^ k) ∧
        ∀ G : SimpleGraph (Fin n), H.Free G → ∃ T ∈ C, G ≤ T := by
  have hk2 : 2 ≤ k := by
    by_contra hlt; push Not at hlt
    apply hH
    refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 2)) ?_⟩
    intro u v huv
    have : u = v := Fin.ext (by omega)
    exact (H.ne_of_adj huv this).elim
  obtain ⟨β0, hβ0_pos, hsparse⟩ := card_sparse_graphs_le (δ / 2) (by positivity)
  let β : ℝ := min (min β0 1) (γ / (2 * (k : ℝ) ^ 2))
  have hβ_pos : 0 < β := lt_min (lt_min hβ0_pos (by norm_num)) (by positivity)
  have hβ_le_β0 : β ≤ β0 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hβ_le_1 : β ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hβ_le_γ : 2 * (k : ℝ) ^ 2 * β ≤ γ := by
    have h1 : β ≤ γ / (2 * (k : ℝ) ^ 2) := min_le_right _ _
    have h2 : (0 : ℝ) < 2 * (k : ℝ) ^ 2 := by positivity
    have h3 := (le_div_iff₀ h2).mp h1
    linarith
  let d : ℝ := β / 4
  have hd_pos : 0 < d := by positivity
  have hd_le1 : d ≤ 1 := by dsimp [d]; linarith
  let η : ℝ := min (β / 8) ((d / 2) ^ k / (4 * (k : ℝ)))
  have hη_pos : 0 < η := lt_min (by positivity) (by positivity)
  have hη_le_β8 : η ≤ β / 8 := min_le_left _ _
  have hη_le_d2 : η ≤ d / 2 := by dsimp [d]; linarith
  have hη_lt_d : η < d := by linarith
  have hdη_ge : d / 2 ≤ d - η := by linarith
  have hη_small : 2 * (k : ℝ) * η ≤ (d - η) ^ k := by
    have h1 : η ≤ (d / 2) ^ k / (4 * (k : ℝ)) := min_le_right _ _
    have h2 : 4 * (k : ℝ) * η ≤ (d / 2) ^ k := by
      have hkpos : (0 : ℝ) < 4 * (k : ℝ) := by positivity
      have := (le_div_iff₀ hkpos).mp h1
      linarith
    have h3 : (d / 2) ^ k ≤ (d - η) ^ k := pow_le_pow_left₀ (by positivity) hdη_ge k
    have hkη : 0 ≤ (k : ℝ) * η := by positivity
    linarith
  let l : ℕ := Nat.ceil (4 / β) + 1
  have hl_ge : 4 / β ≤ (l : ℝ) := by
    have := Nat.le_ceil (4 / β)
    dsimp [l]; push_cast; linarith
  let M : ℕ := SzemerediRegularity.bound η l
  have hM_pos : 1 ≤ M := by
    have h1 : 7 ≤ initialBound η l := seven_le_initialBound η l
    have h2 : initialBound η l ≤ M := initialBound_le_bound η l
    omega
  have hM_Rpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Thresholds for large n
  let N1 : ℕ := max (max l 4) (Nat.ceil (4 * (k : ℝ) * (M : ℝ) / (d - η) ^ k) + 1)
  have hlog_ev : ∀ᶠ n : ℕ in atTop,
      (M : ℝ) ^ n * (2 : ℝ) ^ (M ^ 2) ≤ (2 : ℝ) ^ ((δ / 2) * (n : ℝ) ^ 2) := by
    let C0 : ℝ := Real.log (M : ℝ) / Real.log 2 + (M : ℝ) ^ 2
    obtain ⟨N2, hN2⟩ := exists_nat_ge (max 1 (2 * (|C0| + 1) / δ) + 1)
    filter_upwards [eventually_ge_atTop (max N2 1)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnN2 : N2 ≤ n := le_trans (le_max_left _ _) hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hn_big : 2 * (|C0| + 1) / δ ≤ (n : ℝ) := by
      have h1 : (N2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN2
      have h2 : 2 * (|C0| + 1) / δ ≤ max 1 (2 * (|C0| + 1) / δ) := le_max_right _ _
      linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hC0_le : (n : ℝ) * (Real.log (M : ℝ) / Real.log 2) + (M : ℝ) ^ 2 ≤ (δ / 2) * (n : ℝ) ^ 2 := by
      have h1 : (n : ℝ) * (Real.log (M : ℝ) / Real.log 2) + (M : ℝ) ^ 2 ≤ (n : ℝ) * (|C0| + 1) := by
        have hM2_le : (M : ℝ) ^ 2 ≤ (n : ℝ) * (M : ℝ) ^ 2 := by nlinarith
        have hC0_abs : Real.log (M : ℝ) / Real.log 2 + (M : ℝ) ^ 2 ≤ |C0| := le_abs_self C0
        nlinarith
      have h2 : 2 * (|C0| + 1) ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hn_big
      nlinarith
    have hMpow : (M : ℝ) ^ n = (2 : ℝ) ^ ((n : ℝ) * (Real.log (M : ℝ) / Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hmul : Real.log 2 * ((n : ℝ) * (Real.log (M : ℝ) / Real.log 2)) = (n : ℝ) * Real.log (M : ℝ) := by
        field_simp [hlog2.ne']
      rw [hmul, Real.exp_nat_mul, Real.exp_log hM_Rpos]
    have h2M2 : (2 : ℝ) ^ (M ^ 2) = (2 : ℝ) ^ ((M : ℝ) ^ 2) := by
      rw [← Real.rpow_natCast]; congr 1; push_cast; rfl
    rw [hMpow, h2M2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hC0_le
  filter_upwards [eventually_ge_atTop N1, hlog_ev] with n hnN1 hcard_log
  have hnl : l ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnN1
  have hn4 : 4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnN1
  have hn_pos : 0 < n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  have hns_big : 4 * (k : ℝ) * (M : ℝ) / (d - η) ^ k < (n : ℝ) := by
    have h1 : Nat.ceil (4 * (k : ℝ) * (M : ℝ) / (d - η) ^ k) + 1 ≤ n :=
      le_trans (le_max_right _ _) hnN1
    have h2 : 4 * (k : ℝ) * (M : ℝ) / (d - η) ^ k ≤ (Nat.ceil (4 * (k : ℝ) * (M : ℝ) / (d - η) ^ k) : ℝ) :=
      Nat.le_ceil _
    have h3 : (Nat.ceil (4 * (k : ℝ) * (M : ℝ) / (d - η) ^ k) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  -- Construct explicit finite container family C
  let Templates : Finset ((Fin n → Fin M) × SimpleGraph (Fin M)) :=
    Finset.univ.filter fun p => H.Free (blowupGraph p.1 p.2)
  let Sparse : Finset (SimpleGraph (Fin n)) :=
    Finset.univ.filter fun E => (E.edgeFinset.card : ℝ) ≤ β * (n : ℝ) ^ 2
  let C : Finset (SimpleGraph (Fin n)) :=
    (Templates ×ˢ Sparse).image fun p => blowupGraph p.1.1 p.1.2 ⊔ p.2
  refine ⟨C, ?_, ?_, ?_⟩
  · -- Cardinality bound
    have hT_le : (Templates.card : ℝ) ≤ (M : ℝ) ^ n * (2 : ℝ) ^ (M ^ 2) := by
      have h1 : Templates.card ≤ Fintype.card ((Fin n → Fin M) × SimpleGraph (Fin M)) := by
        simpa using Finset.card_le_card (Finset.subset_univ Templates)
      have hSG : Fintype.card (SimpleGraph (Fin M)) ≤ 2 ^ (M ^ 2) := by
        have hinj : (Finset.univ : Finset (SimpleGraph (Fin M))).card ≤
            (Finset.univ : Finset (Fin M × Fin M → Bool)).card := by
          refine Finset.card_le_card_of_injOn (fun R : SimpleGraph (Fin M) => fun p : Fin M × Fin M => decide (R.Adj p.1 p.2))
            (fun _ _ => Finset.mem_univ _) ?_
          intro R1 _ R2 _ h
          ext u v
          have h1 := congrFun h (u, v)
          simpa using h1
        simpa [Fintype.card_pi, sq] using hinj
      have hprod : Fintype.card ((Fin n → Fin M) × SimpleGraph (Fin M)) ≤ M ^ n * 2 ^ (M ^ 2) := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        exact Nat.mul_le_mul_left _ hSG
      exact_mod_cast (h1.trans hprod)
    have hSp_le : (Sparse.card : ℝ) ≤ (2 : ℝ) ^ ((δ / 2) * (n : ℝ) ^ 2) := by
      have hsub : Sparse ⊆ Finset.univ.filter fun E : SimpleGraph (Fin n) =>
          (E.edgeFinset.card : ℝ) ≤ β0 * (n : ℝ) ^ 2 := by
        intro E hE
        have h1 := (Finset.mem_filter.mp hE).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.trans ?_⟩
        exact mul_le_mul_of_nonneg_right hβ_le_β0 (sq_nonneg _)
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hsparse n)
    have hC_le : (C.card : ℝ) ≤ (Templates.card : ℝ) * (Sparse.card : ℝ) := by
      have h1 : C.card ≤ (Templates ×ˢ Sparse).card := Finset.card_image_le
      rw [Finset.card_product] at h1
      exact_mod_cast h1
    calc (C.card : ℝ) ≤ (Templates.card : ℝ) * (Sparse.card : ℝ) := hC_le
      _ ≤ ((M : ℝ) ^ n * (2 : ℝ) ^ (M ^ 2)) * (2 : ℝ) ^ ((δ / 2) * (n : ℝ) ^ 2) :=
          mul_le_mul hT_le hSp_le (Nat.cast_nonneg _) (by positivity)
      _ ≤ (2 : ℝ) ^ ((δ / 2) * (n : ℝ) ^ 2) * (2 : ℝ) ^ ((δ / 2) * (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard_log (by positivity)
      _ = (2 : ℝ) ^ (δ * (n : ℝ) ^ 2) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; ring
  · -- Copy count bound for every T ∈ C
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨⟨⟨col, R⟩, E_rem⟩, hmem, rfl⟩
    have hfree : H.Free (blowupGraph col R) := (Finset.mem_filter.mp (Finset.mem_product.mp hmem).1).2
    have hEcard : (E_rem.edgeFinset.card : ℝ) ≤ β * (n : ℝ) ^ 2 :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hmem).2).2
    have hcc := copyCount_sup_le_of_free hk2 H (blowupGraph col R) E_rem hfree
    have hccR : ((blowupGraph col R ⊔ E_rem).copyCount H : ℝ) ≤
        2 * (k : ℝ) ^ 2 * (E_rem.edgeFinset.card : ℝ) * (n : ℝ) ^ (k - 2) := by exact_mod_cast hcc
    have hpow : (n : ℝ) ^ 2 * (n : ℝ) ^ (k - 2) = (n : ℝ) ^ k := by
      rw [← pow_add, show 2 + (k - 2) = k by omega]
    calc ((blowupGraph col R ⊔ E_rem).copyCount H : ℝ)
        ≤ 2 * (k : ℝ) ^ 2 * (E_rem.edgeFinset.card : ℝ) * (n : ℝ) ^ (k - 2) := hccR
      _ ≤ 2 * (k : ℝ) ^ 2 * (β * (n : ℝ) ^ 2) * (n : ℝ) ^ (k - 2) := by gcongr
      _ = (2 * (k : ℝ) ^ 2 * β) * ((n : ℝ) ^ 2 * (n : ℝ) ^ (k - 2)) := by ring
      _ = (2 * (k : ℝ) ^ 2 * β) * (n : ℝ) ^ k := by rw [hpow]
      _ ≤ γ * (n : ℝ) ^ k := mul_le_mul_of_nonneg_right hβ_le_γ (by positivity)
  · -- Covering every H-free graph G
    intro G hGfree
    obtain ⟨P, hP_eq, hP_lo, hP_hi, hP_unif⟩ := szemeredi_regularity G hη_pos (by simpa using hnl)
    -- Index P.parts into Fin M
    let eP : P.parts ≃ Fin P.parts.card := Fintype.equivFinOfCardEq (Fintype.card_coe P.parts)
    let idx : P.parts → Fin M := fun U => ⟨(eP U).1, lt_of_lt_of_le (eP U).2 hP_hi⟩
    have hidx_inj : Function.Injective idx := by
      intro U1 U2 h
      apply eP.injective
      exact Fin.ext (congrArg (Fin.val : Fin M → ℕ) h)
    let partOf (v : Fin n) : P.parts :=
      ⟨Classical.choose (P.exists_mem (Finset.mem_univ v)),
       (Classical.choose_spec (P.exists_mem (Finset.mem_univ v))).1⟩
    have hmem_partOf : ∀ v : Fin n, v ∈ (partOf v).1 := fun v =>
      (Classical.choose_spec (P.exists_mem (Finset.mem_univ v))).2
    have hpartOf_unique : ∀ (v : Fin n) (U : Finset (Fin n)), U ∈ P.parts → v ∈ U → U = (partOf v).1 := by
      intro v U hU hv
      exact P.disjoint.elim hU (partOf v).2 (Finset.not_disjoint_iff.mpr ⟨v, hv, hmem_partOf v⟩)
    let col : Fin n → Fin M := fun v => idx (partOf v)
    let R : SimpleGraph (Fin M) :=
      { Adj := fun i j => ∃ (U V : P.parts), idx U = i ∧ idx V = j ∧ U ≠ V ∧
          G.IsUniform η U.1 V.1 ∧ d ≤ (G.edgeDensity U.1 V.1 : ℝ)
        symm := ⟨by
          rintro i j ⟨U, V, rfl, rfl, hne, hu, hd⟩
          exact ⟨V, U, rfl, rfl, hne.symm, hu.symm, by rwa [SimpleGraph.edgeDensity_comm]⟩⟩
        loopless := ⟨by
          rintro i ⟨U, V, hi1, hi2, hne, _, _⟩
          exact hne (hidx_inj (hi1.trans hi2.symm))⟩ }
    -- Prove blowupGraph col R is H-free via embedding_of_uniform_hom
    have hblow_free : H.Free (blowupGraph col R) := by
      intro ⟨f⟩
      let φ : Fin k → Finset (Fin n) := fun a => (partOf (f a)).1
      let s : ℝ := (n : ℝ) / (2 * (M : ℝ))
      have hs_pos : 0 < s := by positivity
      have hpart_card : ∀ a : Fin k, s ≤ ((φ a).card : ℝ) := by
        intro a
        have hPcard_pos : 0 < P.parts.card := (P.parts_nonempty Finset.univ_nonempty.ne_empty).card_pos
        have hPcard_le : P.parts.card ≤ n := by simpa using P.card_parts_le_card
        have haux : n < 2 * P.parts.card * (n / P.parts.card) := by
          have h1 : n % P.parts.card < P.parts.card := Nat.mod_lt n hPcard_pos
          have h2 : 1 ≤ n / P.parts.card := (Nat.one_le_div_iff hPcard_pos).mpr hPcard_le
          have h3 : P.parts.card ≤ P.parts.card * (n / P.parts.card) := by
            simpa using Nat.mul_le_mul_left P.parts.card h2
          have h4 := Nat.div_add_mod n P.parts.card
          nlinarith
        have hdiv_ge : (n : ℝ) / (2 * (P.parts.card : ℝ)) ≤ ((n / P.parts.card : ℕ) : ℝ) := by
          rw [div_le_iff₀ (by positivity)]
          have : (n : ℝ) ≤ (2 * (P.parts.card : ℝ)) * ((n / P.parts.card : ℕ) : ℝ) := by
            exact_mod_cast (by linarith : n ≤ 2 * P.parts.card * (n / P.parts.card))
          linarith
        have havg : (n / P.parts.card : ℕ) ≤ (φ a).card := by
          have := hP_eq.average_le_card_part (partOf (f a)).2
          simpa [φ] using this
        have hM_ge : (P.parts.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hP_hi
        calc s = (n : ℝ) / (2 * (M : ℝ)) := rfl
          _ ≤ (n : ℝ) / (2 * (P.parts.card : ℝ)) := by gcongr
          _ ≤ ((n / P.parts.card : ℕ) : ℝ) := hdiv_ge
          _ ≤ ((φ a).card : ℝ) := by exact_mod_cast havg
      have hpart_unif : ∀ a b : Fin k, H.Adj a b →
          G.IsUniform η (φ a) (φ b) ∧ d ≤ (G.edgeDensity (φ a) (φ b) : ℝ) := by
        intro a b hab
        rcases f.toHom.map_rel' hab with ⟨U, V, hU, hV, _, hu, hde⟩
        have hUeq : U = partOf (f a) := hidx_inj hU
        have hVeq : V = partOf (f b) := hidx_inj hV
        subst hUeq hVeq
        exact ⟨hu, hde⟩
      have hs_big : 2 * (k : ℝ) < (d - η) ^ k * s := by
        have h1 := (div_lt_iff₀ (pow_pos (sub_pos.mpr hη_lt_d) k)).mp hns_big
        dsimp [s]
        rw [mul_div_assoc', lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (M : ℝ))]
        linarith
      exact embedding_of_uniform_hom H G φ hη_pos hd_pos hη_lt_d hd_le1 hs_pos
        hpart_card hpart_unif hη_small hs_big hGfree
    -- Define sparse remainder E_rem
    let E_rem : SimpleGraph (Fin n) :=
      { Adj := fun u v => G.Adj u v ∧ ¬ (G.regularityReduced P η d).Adj u v
        symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
        loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩ }
    have hE_sparse : (E_rem.edgeFinset.card : ℝ) ≤ β * (n : ℝ) ^ 2 :=
      unreduced_edges_card_le G P hη_pos hβ_pos hη_le_β8 hP_eq hP_unif (hl_ge.trans (by exact_mod_cast hP_lo))
    refine ⟨blowupGraph col R ⊔ E_rem, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨((col, R), E_rem), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hblow_free⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by convert hE_sparse⟩⟩
    · intro u v huv
      by_cases hred : (G.regularityReduced P η d).Adj u v
      · left
        rcases hred with ⟨_, U, hU, V, hV, huU, hvV, hUV, hunif, hdens⟩
        have hUeq : U = (partOf u).1 := hpartOf_unique u U hU huU
        have hVeq : V = (partOf v).1 := hpartOf_unique v V hV hvV
        refine ⟨partOf u, partOf v, rfl, rfl, fun h => hUV (hUeq.trans ((congrArg Subtype.val h).trans hVeq.symm)), ?_, ?_⟩
        · rwa [← hUeq, ← hVeq]
        · rwa [← hUeq, ← hVeq]
      · right; exact ⟨huv, hred⟩

/- ### Part 6: Supersaturation (`H2`), bipartite lower bound (`H3`), and final theorem -/

private lemma incidence {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} (B : Finset β) (v : β → Finset α) (m k : ℕ) (hm : k ≤ m)
    (h : ∀ b ∈ B, (v b).card = k) :
    (∑ s ∈ (univ : Finset α).powersetCard m, (B.filter (fun b => v b ⊆ s)).card) =
      B.card * (Fintype.card α - k).choose (m - k) := by
  change (∑ s ∈ (univ : Finset α).powersetCard m, (B.bipartiteBelow (fun b s => v b ⊆ s) s).card) = _
  rw [← sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun b s => v b ⊆ s)]
  have hterm (b : β) (hb : b ∈ B) :
      (((univ : Finset α).powersetCard m).bipartiteAbove (fun b s => v b ⊆ s) b).card =
      (Fintype.card α - k).choose (m - k) := by
    rw [bipartiteAbove, card_filter_powersetCard_subset _ _ _ (subset_univ _) (by simpa [h b hb] using hm),
      h b hb, card_univ]
  rw [sum_congr rfl hterm]
  simp

set_option maxHeartbeats 1000000 in
private lemma sample {k n m : ℕ} (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n))
    (hm : 2 ≤ m) (hk : k ≤ m) :
    G.edgeFinset.card * (n - 2).choose (m - 2) ≤
      n.choose m * extremalNumber m H +
        m.choose 2 * (G.copyCount H * (n - k).choose (m - k)) := by
  let B := (univ : Finset G.Subgraph).filter (fun D => Nonempty (H ≃g D.coe))
  let S := (univ : Finset (Fin n)).powersetCard m
  let v (D : G.Subgraph) := D.verts.toFinset
  have hcard : B.card = G.copyCount H := by
    unfold copyCount
    apply congrArg Finset.card
    ext D
    simp [B]
  have hv (D : G.Subgraph) (hD : D ∈ B) : (v D).card = k := by
    obtain ⟨e⟩ := (mem_filter.mp hD).2
    simpa [v] using (Fintype.card_congr e.toEquiv).symm
  have hlocal (s : Finset (Fin n)) (hs : s ∈ S) :
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card ≤ extremalNumber m H +
        m.choose 2 * (B.filter (fun D => v D ⊆ s)).card := by
    let T := G.induce (s : Set (Fin n))
    have hms : Fintype.card (↥(s : Set (Fin n))) = m := by
      simpa using (mem_powersetCard.mp hs).2
    have he : (G.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card = T.edgeFinset.card := by
      have h := congrArg Finset.card (G.map_edgeFinset_induce (s := (s : Set (Fin n))))
      simp only [card_map] at h
      convert! h.symm using 1
      · congr 1
        ext e
        simp only [mem_filter, mem_inter, mem_sym2_iff, Set.mem_toFinset, Finset.mem_coe]
        apply and_congr_right
        intro _
        change (∀ a ∈ e.toFinset, a ∈ s) ↔ _
        simp only [Sym2.mem_toFinset]
      · apply congrArg Finset.card
        ext e
        simp [T]
    rw [he]
    by_cases free : H.Free T
    · have h := card_edgeFinset_le_extremalNumber free
      rw [hms] at h
      omega
    · obtain ⟨f⟩ : H ⊑ T := by simpa [SimpleGraph.Free] using free
      let g := (Copy.induce G (s : Set (Fin n))).comp f
      have inside : v g.toSubgraph ⊆ s := by
        intro a ha
        obtain ⟨b, -, rfl⟩ := Set.mem_toFinset.mp ha
        exact (f b).property
      have hpos : 1 ≤ (B.filter (fun D => v D ⊆ s)).card := card_pos.mpr
        ⟨g.toSubgraph, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ⟨g.isoToSubgraph⟩⟩, inside⟩⟩
      have hu := T.card_edgeFinset_le_card_choose_two
      rw [hms] at hu
      exact hu.trans (Nat.le_add_left_of_le (by simpa using Nat.mul_le_mul_left (m.choose 2) hpos))
  have bound := sum_le_sum hlocal
  have ecount := incidence G.edgeFinset (fun e => e.toFinset) m 2 hm
    (fun e he => G.card_toFinset_mem_edgeFinset ⟨e, he⟩)
  have bcount := incidence B v m k hk hv
  simp only [Fintype.card_fin] at ecount bcount
  simpa only [S, ecount, sum_add_distrib, sum_const, card_powersetCard, card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, ← mul_sum, bcount, hcard] using bound

private lemma normalize_sample {a b c u v w x y : ℝ} (hu : 0 < u) (hv : 0 < v)
    (_hw : 0 < w) (hx : 0 < x)
    (h : a * (u * v / w) ≤ u * b + v * (c * (u * y / x))) : a / w ≤ b / v + c * y / x := by
  apply le_of_mul_le_mul_left (a := u * v) ?_ (mul_pos hu hv)
  calc
    _ = a * (u * v / w) := by ring
    _ ≤ _ := h
    _ = _ := by field_simp

private lemma density_sample {k n m : ℕ} (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n))
    (hm : 2 ≤ m) (hk : k ≤ m) (hn : m ≤ n) :
    (G.edgeFinset.card : ℝ) / n.choose 2 ≤ (extremalNumber m H : ℝ) / m.choose 2 +
      (G.copyCount H : ℝ) * m.choose k / n.choose k := by
  have h := sample H G hm hk
  have c2 : (n.choose m : ℝ) * m.choose 2 = n.choose 2 * ((n - 2).choose (m - 2) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := n) hm
  have ck : (n.choose m : ℝ) * m.choose k = n.choose k * ((n - k).choose (m - k) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := n) hk
  have hn2 : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos (hm.trans hn)
  have hnk : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (hk.trans hn)
  have hnm : (0 : ℝ) < n.choose m := by exact_mod_cast Nat.choose_pos hn
  have hm2 : (0 : ℝ) < m.choose 2 := by exact_mod_cast Nat.choose_pos hm
  have heq : ((n - 2).choose (m - 2) : ℝ) = n.choose m * (m.choose 2 : ℝ) / n.choose 2 := by
    apply (eq_div_iff hn2.ne').mpr
    linarith
  have hkq : ((n - k).choose (m - k) : ℝ) = n.choose m * (m.choose k : ℝ) / n.choose k := by
    apply (eq_div_iff hnk.ne').mpr
    linarith
  have bound : (G.edgeFinset.card : ℝ) * ((n - 2).choose (m - 2) : ℝ) ≤
      (n.choose m : ℝ) * extremalNumber m H +
      m.choose 2 * ((G.copyCount H : ℝ) * ((n - k).choose (m - k) : ℝ)) := by exact_mod_cast h
  rw [heq, hkq] at bound
  exact normalize_sample hnm hm2 hn2 hnk bound

private lemma supersaturation_H2 {k : ℕ} (H : SimpleGraph (Fin k))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ γ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ T : SimpleGraph (Fin n), (T.copyCount H : ℝ) ≤ γ * (n : ℝ) ^ k →
        (T.edgeFinset.card : ℝ) ≤ extremalNumber n H + δ * (n : ℝ) ^ 2 := by
  obtain ⟨m, hm⟩ := eventually_atTop.mp ((tendsto_turanDensity H).eventually_lt_const
    (show turanDensity H < turanDensity H + δ / 2 by linarith))
  let M := max (max k 2) m
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hMk : k ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  let D : ℝ := (2 : ℝ) ^ k * k.factorial * M.choose k
  have hD : 0 < D := mul_pos (mul_pos (by positivity) (by exact_mod_cast Nat.factorial_pos k))
    (by exact_mod_cast Nat.choose_pos hMk)
  refine ⟨δ / 2 / D, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max M (2 * k))] with n hn
  intro G copies
  have hnM := (le_max_left M (2 * k)).trans hn
  have hn2 : 2 ≤ n := hM2.trans hnM
  have hπ : turanDensity H ≤ (extremalNumber n H : ℝ) / n.choose 2 :=
    (isGLB_turanDensity H).1 ⟨n, hn2, rfl⟩
  have h1 := (hm M (le_max_right _ _)).le.trans (add_le_add_left hπ (δ / 2))
  have twok := (le_max_right M (2 * k)).trans hn
  have hN : n ≤ 2 * (n + 1 - k) := by omega
  have hc : (n : ℝ) ^ k ≤ (2 : ℝ) ^ k * k.factorial * n.choose k := by
    exact_mod_cast (calc
      n ^ k ≤ (2 * (n + 1 - k)) ^ k := Nat.pow_le_pow_left hN k
      _ = 2 ^ k * (n + 1 - k) ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (k.factorial * n.choose k) := Nat.mul_le_mul_left _ (by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        exact n.pow_sub_le_descFactorial k)
      _ = _ := by ring)
  have hnck : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (hMk.trans hnM)
  have factor : (G.copyCount H : ℝ) * M.choose k / n.choose k ≤ δ / 2 := by
    apply (div_le_iff₀ hnck).mpr
    calc
      _ ≤ (δ / 2 / D) * ((2 : ℝ) ^ k * k.factorial * n.choose k) * M.choose k :=
        mul_le_mul_of_nonneg_right (copies.trans (mul_le_mul_of_nonneg_left hc (by positivity))) (by positivity)
      _ = (δ / 2 / D * D) * n.choose k := by dsimp [D]; ring
      _ = _ := by rw [div_mul_cancel₀ _ hD.ne']
  have b := (density_sample H G hM2 hMk hnM).trans (add_le_add h1 factor)
  have hx : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos hn2
  have hraw : (G.edgeFinset.card : ℝ) / n.choose 2 ≤ (extremalNumber n H : ℝ) / n.choose 2 + δ := by
    linarith
  have hh := (div_le_iff₀ hx).mp hraw
  rw [add_mul, div_mul_cancel₀ _ hx.ne'] at hh
  have hc2 : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow n 2
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_left hc2 hδ.le) _)

private lemma bipartite_lower_H3 {k : ℕ} (H : SimpleGraph (Fin k)) (hH : ¬ H.IsBipartite) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ 8 * extremalNumber n H := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  let a := n / 2
  let b := n - a
  let B := completeBipartiteGraph (Fin a) (Fin b)
  have hab : a + b = n := by dsimp [a, b]; omega
  have hB : B.IsBipartite := by
    refine ⟨Coloring.mk (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1)) ?_⟩
    rintro (v | v) (w | w) hadj <;> simp_all [B, completeBipartiteGraph]
  have hfree : H.Free B := fun ⟨f⟩ => hH (hB.of_hom f.toHom)
  have edges : B.edgeFinset.card = a * b := by
    have h := encard_edgeSet_completeBipartiteGraph (W₁ := Fin a) (W₂ := Fin b)
    change B.edgeSet.encard = _ at h
    rw [← coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard] at h
    simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h
    exact_mod_cast h
  have hle := card_edgeFinset_le_extremalNumber hfree
  rw [edges, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hab] at hle
  have h₁ : n ≤ 3 * a := by dsimp [a]; omega
  have h₂ : n ≤ 2 * b := by dsimp [a, b]; omega
  have hprod := Nat.mul_le_mul h₁ h₂
  have : n ^ 2 ≤ 8 * extremalNumber n H := by nlinarith
  exact_mod_cast this

private lemma count_cover {k n : ℕ} (H : SimpleGraph (Fin k))
    (C : Finset (SimpleGraph (Fin n)))
    (hc : ∀ G : SimpleGraph (Fin n), H.Free G → ∃ T ∈ C, G ≤ T) :
    Erdos59.numFree H n ≤ ∑ T ∈ C, 2 ^ T.edgeFinset.card := by
  let S : Set (SimpleGraph (Fin n)) := {G | H.Free G}
  change S.ncard ≤ _
  rw [Set.ncard_eq_toFinset_card']
  calc
    S.toFinset.card ≤ (C.biUnion fun T => T.edgeFinset.powerset).card := by
      apply Finset.card_le_card_of_injOn (fun G : SimpleGraph (Fin n) => G.edgeFinset)
      · intro G hG
        obtain ⟨T, hT, hl⟩ := hc G (Set.mem_toFinset.mp hG)
        exact Finset.mem_biUnion.mpr ⟨T, hT, Finset.mem_powerset.mpr (edgeFinset_mono hl)⟩
      · intro G _ G' _ h
        exact edgeFinset_inj.mp h
    _ ≤ _ := by simpa using Finset.card_biUnion_le (s := C) (t := fun T => T.edgeFinset.powerset)

private lemma erdos59_efr_proof :
    type_of% @Erdos59.erdos_59.variants.erdos_frankl_rodl := by
  intro k H hH ε hε
  let δ := ε / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨γ, hγ, hsup⟩ := supersaturation_H2 H δ hδ
  filter_upwards [container_H1 H hH δ hδ γ hγ, hsup, bipartite_lower_H3 H hH] with n hn hn' hn''
  obtain ⟨C, hcard, hfew, hcover⟩ := hn
  let M : ℝ := extremalNumber n H + δ * (n : ℝ) ^ 2
  have hpow (T : SimpleGraph (Fin n)) (hT : T ∈ C) :
      (2 : ℝ) ^ T.edgeFinset.card ≤ (2 : ℝ) ^ M := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hn' T (hfew T hT))
  calc
    (Erdos59.numFree H n : ℝ) ≤ ∑ T ∈ C, (2 : ℝ) ^ T.edgeFinset.card := by
      exact_mod_cast count_cover H C hcover
    _ ≤ ∑ _T ∈ C, (2 : ℝ) ^ M := Finset.sum_le_sum hpow
    _ = C.card * (2 : ℝ) ^ M := by simp
    _ ≤ (2 : ℝ) ^ (δ * (n : ℝ) ^ 2) * (2 : ℝ) ^ M := by gcongr
    _ = (2 : ℝ) ^ (δ * (n : ℝ) ^ 2 + M) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [M, δ]
      nlinarith [mul_le_mul_of_nonneg_left hn'' hε.le]

end

end Erdos59EFR

theorem OMA.solution : type_of% @Erdos59.erdos_59.variants.erdos_frankl_rodl :=
  Erdos59EFR.erdos59_efr_proof
