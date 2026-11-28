import OMAReductions.R_oeis_a004109_R1
import Mathlib

namespace OMA.Proof_oeis_a004109_R1_H2

open Finset
open scoped Classical BigOperators

private noncomputable def Reg (m : ℕ) : Finset (SimpleGraph (Fin (2 * m))) :=
  Finset.univ.filter fun G : SimpleGraph (Fin (2 * m)) =>
    ∀ v, (G.neighborFinset v).card = 3

private noncomputable def ConnReg (m : ℕ) : Finset (SimpleGraph (Fin (2 * m))) :=
  Finset.univ.filter fun G : SimpleGraph (Fin (2 * m)) =>
    G.Connected ∧ ∀ v, (G.neighborFinset v).card = 3

private noncomputable def DisconnReg (m : ℕ) : Finset (SimpleGraph (Fin (2 * m))) :=
  Finset.univ.filter fun G : SimpleGraph (Fin (2 * m)) =>
    ¬ G.Connected ∧ ∀ v, (G.neighborFinset v).card = 3

private lemma card_neighborFinset_eq {α : Type*} [Fintype α] (G : SimpleGraph α) (v : α) :
    (G.neighborFinset v).card = (Finset.univ.filter (fun w => G.Adj v w)).card := by
  apply Finset.card_bij (fun w _ => w)
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, (SimpleGraph.mem_neighborFinset G v w).mp hw⟩
  · intro _ _ _ _ h; exact h
  · intro w hw
    exact ⟨w, (SimpleGraph.mem_neighborFinset G v w).mpr (Finset.mem_filter.mp hw).2, rfl⟩

private lemma even_card_closed_of_three_regular {n : ℕ}
    (G : SimpleGraph (Fin (2 * n)))
    (hreg : ∀ v, (G.neighborFinset v).card = 3)
    (S : Finset (Fin (2 * n)))
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) :
    Even S.card := by
  let E : Finset (Fin (2 * n) × Fin (2 * n)) :=
    (S ×ˢ S).filter (fun p => G.Adj p.1 p.2)
  have hE_eq : E = S.biUnion (fun u => (G.neighborFinset u).image (fun v => (u, v))) := by
    ext ⟨u, v⟩
    simp only [E, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨hu, _⟩, huv⟩
      exact ⟨u, hu, v, huv, rfl⟩
    · rintro ⟨u', hu', v', huv', hpair⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      exact ⟨⟨hu', hclosed u' hu' v' huv'⟩, huv'⟩
  have hE_card : E.card = 3 * S.card := by
    rw [hE_eq, Finset.card_biUnion]
    · calc
        ∑ u ∈ S, ((G.neighborFinset u).image (fun v => (u, v))).card
          = ∑ u ∈ S, (G.neighborFinset u).card := by
              apply Finset.sum_congr rfl
              intro u _
              exact Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
        _ = ∑ _u ∈ S, 3 := Finset.sum_congr rfl (fun u _ => hreg u)
        _ = 3 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    · intro u₁ _ u₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp₁
      obtain ⟨_, _, hp⟩ := Finset.mem_image.mp hp₂
      exact hne (congrArg Prod.fst hp).symm
  let Elt : Finset (Fin (2 * n) × Fin (2 * n)) := E.filter (fun p => p.1 < p.2)
  let Egt : Finset (Fin (2 * n) × Fin (2 * n)) := E.filter (fun p => p.2 < p.1)
  have hdisj : Disjoint Elt Egt := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    exact lt_asymm h1 h2
  have hunion : E = Elt ∪ Egt := by
    ext p
    simp only [Elt, Egt, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
      have hne : p.1 ≠ p.2 := G.ne_of_adj hadj
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hp, hlt⟩
      · exact Or.inr ⟨hp, hgt⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hswap : Elt.card = Egt.card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      obtain ⟨hpE, hlt⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpSS, hadj⟩ := Finset.mem_filter.mp hpE
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpSS
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hadj.symm⟩, hlt⟩
    · intro p₁ _ p₂ _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro p hp
      obtain ⟨hpE, hgt⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpSS, hadj⟩ := Finset.mem_filter.mp hpE
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpSS
      refine ⟨(p.2, p.1), ?_, Prod.ext rfl rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hadj.symm⟩, hgt⟩
  have hE_even : E.card = 2 * Elt.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj, ← hswap]
    omega
  rw [Nat.even_iff]
  omega

private lemma exists_closed_small_even {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin (2 * n)))
    (hdis : ¬ G.Connected)
    (hreg : ∀ v, (G.neighborFinset v).card = 3) :
    ∃ i ∈ Finset.Icc 1 (n / 2), ∃ S : Finset (Fin (2 * n)),
      S.card = 2 * i ∧ (∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) := by
  let v₀ : Fin (2 * n) := ⟨0, by omega⟩
  have : Nonempty (Fin (2 * n)) := ⟨v₀⟩
  let C : Finset (Fin (2 * n)) := Finset.univ.filter (fun v => G.Reachable v₀ v)
  have hv₀ : v₀ ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ v₀, SimpleGraph.Reachable.refl v₀⟩
  have hC_pos : 0 < C.card := Finset.card_pos.mpr ⟨v₀, hv₀⟩
  have hC_lt : C.card < 2 * n := by
    by_contra! hge
    have hC_le : C.card ≤ 2 * n := by simpa [Fintype.card_fin] using Finset.card_le_univ C
    have hC_univ : C = Finset.univ := Finset.eq_univ_of_card C (by rw [Fintype.card_fin]; omega)
    apply hdis
    refine ⟨fun u w => ?_⟩
    have hu : G.Reachable v₀ u := by
      have : u ∈ C := hC_univ ▸ Finset.mem_univ u
      exact (Finset.mem_filter.mp this).2
    have hw : G.Reachable v₀ w := by
      have : w ∈ C := hC_univ ▸ Finset.mem_univ w
      exact (Finset.mem_filter.mp this).2
    exact hu.symm.trans hw
  have hC_closed : ∀ u ∈ C, ∀ v, G.Adj u v → v ∈ C := by
    intro u hu v huv
    have hru : G.Reachable v₀ u := (Finset.mem_filter.mp hu).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hru.trans huv.reachable⟩
  have hCc_closed : ∀ u ∈ Cᶜ, ∀ v, G.Adj u v → v ∈ Cᶜ := by
    intro u hu v huv
    rw [Finset.mem_compl] at hu ⊢
    intro hv
    exact hu (hC_closed v hv u huv.symm)
  have hCc_card : Cᶜ.card = 2 * n - C.card := by
    have := Finset.card_compl C
    rw [Fintype.card_fin] at this
    exact this
  let S : Finset (Fin (2 * n)) := if C.card ≤ n then C else Cᶜ
  have hS_closed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S := by
    by_cases hle : C.card ≤ n
    · simp only [S, hle, ↓reduceIte]; exact hC_closed
    · simp only [S, hle, ↓reduceIte]; exact hCc_closed
  have hS_pos : 0 < S.card := by
    by_cases hle : C.card ≤ n
    · simp only [S, hle, ↓reduceIte]; exact hC_pos
    · simp only [S, hle, ↓reduceIte]; omega
  have hS_le : S.card ≤ n := by
    by_cases hle : C.card ≤ n
    · dsimp only [S]; rw [if_pos hle]; exact hle
    · dsimp only [S]; rw [if_neg hle]; omega
  obtain ⟨i, hi⟩ := even_card_closed_of_three_regular G hreg S hS_closed
  have hi_card : S.card = 2 * i := by omega
  have hi_mem : i ∈ Finset.Icc 1 (n / 2) := by
    rw [Finset.mem_Icc]
    omega
  exact ⟨i, hi_mem, S, hi_card, hS_closed⟩

private noncomputable def reconstructGraph {n i : ℕ}
    (S : Finset (Fin (2 * n)))
    (hS : S.card = 2 * i) (hSc : Sᶜ.card = 2 * (n - i))
    (G₁ : SimpleGraph (Fin (2 * i)))
    (G₂ : SimpleGraph (Fin (2 * (n - i)))) : SimpleGraph (Fin (2 * n)) where
  Adj u v :=
    (∃ a b : Fin (2 * i), S.orderEmbOfFin hS a = u ∧ S.orderEmbOfFin hS b = v ∧ G₁.Adj a b) ∨
    (∃ a b : Fin (2 * (n - i)), Sᶜ.orderEmbOfFin hSc a = u ∧ Sᶜ.orderEmbOfFin hSc b = v ∧ G₂.Adj a b)
  symm := ⟨by
    rintro u v (⟨a, b, rfl, rfl, h⟩ | ⟨a, b, rfl, rfl, h⟩)
    · exact Or.inl ⟨b, a, rfl, rfl, h.symm⟩
    · exact Or.inr ⟨b, a, rfl, rfl, h.symm⟩⟩
  loopless := ⟨by
    rintro u (⟨a, b, ha, hb, h⟩ | ⟨a, b, ha, hb, h⟩)
    · have hab : a = b := (S.orderEmbOfFin hS).injective (ha.trans hb.symm)
      subst hab
      exact G₁.loopless.irrefl a h
    · have hab : a = b := (Sᶜ.orderEmbOfFin hSc).injective (ha.trans hb.symm)
      subst hab
      exact G₂.loopless.irrefl a h⟩

private lemma comap_three_regular {n m : ℕ}
    (G : SimpleGraph (Fin (2 * n)))
    (hreg : ∀ v, (G.neighborFinset v).card = 3)
    (T : Finset (Fin (2 * n))) (hT : T.card = 2 * m)
    (hclosed : ∀ u ∈ T, ∀ v, G.Adj u v → v ∈ T) :
    G.comap (T.orderEmbOfFin hT) ∈ Reg m := by
  rw [Reg, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun a => ?_⟩
  let e := T.orderEmbOfFin hT
  have he_mem : ∀ x : Fin (2 * m), e x ∈ T := fun x => Finset.orderEmbOfFin_mem T hT x
  have hbij : ((G.comap e).neighborFinset a).card = (G.neighborFinset (e a)).card := by
    apply Finset.card_bij (fun b _ => e b)
    · intro b hb
      rw [SimpleGraph.mem_neighborFinset] at hb ⊢
      exact hb
    · intro b₁ _ b₂ _ h
      exact e.injective h
    · intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      have hwT : w ∈ T := hclosed (e a) (he_mem a) w hw
      have hw_range : w ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin T hT]
        exact hwT
      obtain ⟨b, rfl⟩ := hw_range
      exact ⟨b, (SimpleGraph.mem_neighborFinset (G.comap e) a b).mpr hw, rfl⟩
  change ((G.comap e).neighborFinset a).card = 3
  rw [hbij, hreg (e a)]

private lemma reconstruct_comap_eq {n i : ℕ}
    (G : SimpleGraph (Fin (2 * n)))
    (S : Finset (Fin (2 * n)))
    (hS : S.card = 2 * i) (hSc : Sᶜ.card = 2 * (n - i))
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) :
    reconstructGraph S hS hSc
      (G.comap (S.orderEmbOfFin hS))
      (G.comap (Sᶜ.orderEmbOfFin hSc)) = G := by
  let e₁ := S.orderEmbOfFin hS
  let e₂ := Sᶜ.orderEmbOfFin hSc
  have hclosed_c : ∀ u ∈ Sᶜ, ∀ v, G.Adj u v → v ∈ Sᶜ := by
    intro u hu v huv
    rw [Finset.mem_compl] at hu ⊢
    intro hv
    exact hu (hclosed v hv u huv.symm)
  ext u v
  simp only [reconstructGraph, SimpleGraph.comap_adj]
  constructor
  · rintro (⟨a, b, rfl, rfl, h⟩ | ⟨a, b, rfl, rfl, h⟩) <;> exact h
  · intro huv
    by_cases hu : u ∈ S
    · have hv : v ∈ S := hclosed u hu v huv
      have hu_r : u ∈ Set.range e₁ := by rw [Finset.range_orderEmbOfFin S hS]; exact hu
      have hv_r : v ∈ Set.range e₁ := by rw [Finset.range_orderEmbOfFin S hS]; exact hv
      obtain ⟨a, rfl⟩ := hu_r
      obtain ⟨b, rfl⟩ := hv_r
      exact Or.inl ⟨a, b, rfl, rfl, huv⟩
    · have hu' : u ∈ Sᶜ := Finset.mem_compl.mpr hu
      have hv' : v ∈ Sᶜ := hclosed_c u hu' v huv
      have hu_r : u ∈ Set.range e₂ := by rw [Finset.range_orderEmbOfFin Sᶜ hSc]; exact hu'
      have hv_r : v ∈ Set.range e₂ := by rw [Finset.range_orderEmbOfFin Sᶜ hSc]; exact hv'
      obtain ⟨a, rfl⟩ := hu_r
      obtain ⟨b, rfl⟩ := hv_r
      exact Or.inr ⟨a, b, rfl, rfl, huv⟩

private lemma disconn_bound (n : ℕ) (hn : 0 < n) :
    (DisconnReg n).card ≤
      ∑ i ∈ Finset.Icc 1 (n / 2), (2 * n).choose (2 * i) * (Reg i).card * (Reg (n - i)).card := by
  let piece (i : ℕ) : Finset (SimpleGraph (Fin (2 * n))) :=
    if hi : i ≤ n then
      (((Finset.univ : Finset (Fin (2 * n))).powersetCard (2 * i)) ×ˢ (Reg i ×ˢ Reg (n - i))).image
        (fun p =>
          if hS : p.1.card = 2 * i then
            reconstructGraph p.1 hS (by
              have hc := Finset.card_compl p.1
              rw [Fintype.card_fin] at hc
              omega) p.2.1 p.2.2
          else ⊥)
    else ∅
  have hsub : DisconnReg n ⊆ (Finset.Icc 1 (n / 2)).biUnion piece := by
    intro G hG
    rw [DisconnReg, Finset.mem_filter] at hG
    obtain ⟨_, hdis, hreg⟩ := hG
    obtain ⟨i, hi_mem, S, hS, hclosed⟩ := exists_closed_small_even hn G hdis hreg
    have hi_le : i ≤ n := by
      have := (Finset.mem_Icc.mp hi_mem).2
      omega
    have hSc : Sᶜ.card = 2 * (n - i) := by
      have hc := Finset.card_compl S
      rw [Fintype.card_fin] at hc
      omega
    have hclosed_c : ∀ u ∈ Sᶜ, ∀ v, G.Adj u v → v ∈ Sᶜ := by
      intro u hu v huv
      rw [Finset.mem_compl] at hu ⊢
      intro hv
      exact hu (hclosed v hv u huv.symm)
    rw [Finset.mem_biUnion]
    refine ⟨i, hi_mem, ?_⟩
    simp only [piece, hi_le, ↓reduceDIte, Finset.mem_image]
    refine ⟨(S, (G.comap (S.orderEmbOfFin hS), G.comap (Sᶜ.orderEmbOfFin hSc))), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS⟩,
        Finset.mem_product.mpr ⟨comap_three_regular G hreg S hS hclosed,
          comap_three_regular G hreg Sᶜ hSc hclosed_c⟩⟩
    · simp only [hS, ↓reduceDIte]
      exact reconstruct_comap_eq G S hS hSc hclosed
  calc
    (DisconnReg n).card
      ≤ ((Finset.Icc 1 (n / 2)).biUnion piece).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.Icc 1 (n / 2), (piece i).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Finset.Icc 1 (n / 2),
          (2 * n).choose (2 * i) * (Reg i).card * (Reg (n - i)).card := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_le : i ≤ n := by
          have := (Finset.mem_Icc.mp hi).2
          omega
        simp only [piece, hi_le, ↓reduceDIte]
        calc
          _ ≤ (((Finset.univ : Finset (Fin (2 * n))).powersetCard (2 * i)) ×ˢ
                (Reg i ×ˢ Reg (n - i))).card := Finset.card_image_le
          _ = ((Finset.univ : Finset (Fin (2 * n))).powersetCard (2 * i)).card *
                ((Reg i).card * (Reg (n - i)).card) := by
              rw [Finset.card_product, Finset.card_product]
          _ = (2 * n).choose (2 * i) * (Reg i).card * (Reg (n - i)).card := by
              rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, mul_assoc]

private lemma a_eq_connReg (n : ℕ) : OMA.S_oeis_a004109.a n = (ConnReg n).card := by
  unfold OMA.S_oeis_a004109.a ConnReg
  apply Finset.card_bij (fun G _ => G)
  · intro G hG
    rw [Finset.mem_filter] at hG ⊢
    refine ⟨Finset.mem_univ G, hG.2.1, fun v => ?_⟩
    convert hG.2.2 v
  · intro _ _ _ _ h; exact h
  · intro G hG
    rw [Finset.mem_filter] at hG
    refine ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ G, hG.2.1, fun v => ?_⟩, rfl⟩
    convert hG.2.2 v

private lemma reg_card_eq_split (n : ℕ) :
    (Reg n).card = (ConnReg n).card + (DisconnReg n).card := by
  have hdisj : Disjoint (ConnReg n) (DisconnReg n) := by
    rw [Finset.disjoint_left]
    intro G h1 h2
    exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
  have hunion : Reg n = ConnReg n ∪ DisconnReg n := by
    ext G
    simp only [Reg, ConnReg, DisconnReg, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    by_cases h : G.Connected <;> simp [h]
  rw [hunion, Finset.card_union_of_disjoint hdisj]

end OMA.Proof_oeis_a004109_R1_H2

theorem OMA.solution : OMA.R_oeis_a004109_R1.H2 := by
  classical
  unfold OMA.R_oeis_a004109_R1.H2
  dsimp only
  have hReg (m : ℕ) :
      (Finset.univ.filter fun G : SimpleGraph (Fin (2 * m)) =>
        ∀ v, (G.neighborFinset v).card = 3).card =
      (OMA.Proof_oeis_a004109_R1_H2.Reg m).card := by
    unfold OMA.Proof_oeis_a004109_R1_H2.Reg
    apply Finset.card_bij (fun G _ => G)
    · intro G hG
      rw [Finset.mem_filter] at hG ⊢
      refine ⟨Finset.mem_univ G, fun v => ?_⟩
      convert hG.2 v
    · intro _ _ _ _ h; exact h
    · intro G hG
      rw [Finset.mem_filter] at hG
      refine ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ G, fun v => ?_⟩, rfl⟩
      convert hG.2 v
  constructor
  · intro n
    rw [OMA.Proof_oeis_a004109_R1_H2.a_eq_connReg, hReg,
      OMA.Proof_oeis_a004109_R1_H2.reg_card_eq_split]
    omega
  · intro n hn
    rw [OMA.Proof_oeis_a004109_R1_H2.a_eq_connReg]
    have hsplit := OMA.Proof_oeis_a004109_R1_H2.reg_card_eq_split n
    have hsub :
        (Finset.univ.filter fun G : SimpleGraph (Fin (2 * n)) =>
          ∀ v, (G.neighborFinset v).card = 3).card -
          (OMA.Proof_oeis_a004109_R1_H2.ConnReg n).card =
        (OMA.Proof_oeis_a004109_R1_H2.DisconnReg n).card := by
      rw [hReg n, hsplit]
      omega
    rw [hsub]
    calc
      (OMA.Proof_oeis_a004109_R1_H2.DisconnReg n).card
        ≤ ∑ i ∈ Finset.Icc 1 (n / 2),
            (2 * n).choose (2 * i) *
              (OMA.Proof_oeis_a004109_R1_H2.Reg i).card *
              (OMA.Proof_oeis_a004109_R1_H2.Reg (n - i)).card :=
          OMA.Proof_oeis_a004109_R1_H2.disconn_bound n hn
      _ = ∑ i ∈ Finset.Icc 1 (n / 2),
            (2 * n).choose (2 * i) *
              (Finset.univ.filter fun G : SimpleGraph (Fin (2 * i)) =>
                ∀ v, (G.neighborFinset v).card = 3).card *
              (Finset.univ.filter fun G : SimpleGraph (Fin (2 * (n - i))) =>
                ∀ v, (G.neighborFinset v).card = 3).card := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hReg i, hReg (n - i)]
