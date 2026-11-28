import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

open Finset SimpleGraph Filter
open scoped Classical
namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R2

/-- Classify each host as already settled, or exhibit a bounded regular partition with a large component or an exclusive near-quarter pair. -/
def H1 : Prop := ∀ α : ℝ, 0<α → ∀ᶠ H : ℕ in atTop, ∃ η > (0:ℝ), η ≤ (1/(H:ℝ))^2 ∧
    ∃ B : ℕ, ∀ᶠ m : ℕ in atTop,
    let V := Fin (4*m)
    ∀ (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj], (⊤ : SimpleGraph V).IsEdgeColouring c →
    ((∃ i, cycleGraph (2*m) ⊑ c i) ∨ ∃ (f : V → Fin 4) (σ : Equiv.Perm (Fin 3)),
      let W := fun j => univ.filter (fun v => f v = j)
      let U := W 0 ∪ W 1
      let dense := fun i (X Y : Finset V) => (1-α)*(X.card:ℝ)*Y.card ≤ ∑ x ∈ X, ((Y.filter ((c (σ i)).Adj x)).card:ℝ)
      (∀ j, (1-α)*m ≤ (W j).card) ∧ dense 0 (W 0) (W 1) ∧ dense 1 (W 2) U ∧ dense 2 (W 3) U) ∨
    ∃ P : Finpartition (univ : Finset V), P.IsEquipartition ∧ H*H ≤ P.parts.card ∧ P.parts.card ≤ B ∧
    let t := P.parts.card
    ∃ (p : Fin t ≃ P.parts) (R : Fin 3 → SimpleGraph (Fin t)),
    let k := ⌈(1/4+1/(H:ℝ))*t⌉₊
    let d := ⌈(1/(H:ℝ))*t⌉₊
    let e := t/H+3
    let cut := fun i (A D : Finset (Fin t)) => ∀ x ∈ A, ∀ y ∈ D, ∀ j, (R j).Adj x y → j=i
    (∀ i x y, (R i).Adj x y ↔ x≠y ∧ (∀ j, (c j).IsUniform η (p x) (p y)) ∧ 1/(H:ℝ) ≤ ((c i).edgeDensity (p x) (p y):ℝ)) ∧
    (∃ E : Finset (Fin t × Fin t), E.card < (d+1)^2 ∧ ∀ x y, x≠y → (x,y) ∉ E → ∃ i, (R i).Adj x y) ∧
    ((∃ i u, let C := univ.filter ((R i).Reachable u)
      t<C.card+k+6*d ∧ ∃ S T W : Finset (Fin t), C=S∪T∪W ∧ Disjoint S T ∧ Disjoint (S∪T) W ∧
      S.card=T.card ∧ S.card<k ∧ (∀ x∈W, ∀ y∈W, ¬(R i).Adj x y) ∧ (∀ x∈S, (W.filter ((R i).Adj x)).card≤1) ∧
      (W.Nonempty → ∃ j≠i, ∃ v∈W, W.card≤(W.filter ((R j).Reachable v)).card+3*d)) ∨ (∀ i u, (univ.filter ((R i).Reachable u)).card+t/4≤t) ∧ ∃ (F : Fin 4 → Finset (Fin t)) (σ : Equiv.Perm (Fin 3)),
      Monotone (fun j => (F j).card) ∧ Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      t≤(∑ j, (F j).card)+2*d ∧ 24*e≤(F 0).card ∧ t/4-8*e ≤ (F 1).card ∧ (F 2).card ≤ t/4+2*e ∧
      (F 0).card+(F 3).card<2*k+2*d ∧ (∀ i : Fin 3, cut (σ i) (F 3) (F i.castSucc)) ∧
      ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → cut (σ l) (F i.castSucc) (F j.castSucc))

/-- Finish the large-component case on a bounded regular partition. -/
def H2 : Prop := ∀ α : ℝ, 0<α → ∀ᶠ H : ℕ in atTop, ∀ η : ℝ, 0<η → η ≤ (1/(H:ℝ))^2 →
    ∀ B : ℕ, ∀ᶠ m : ℕ in atTop,
    let V := Fin (4*m)
    ∀ (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj], (⊤ : SimpleGraph V).IsEdgeColouring c →
    ∀ P : Finpartition (univ : Finset V), P.IsEquipartition → H*H ≤ P.parts.card → P.parts.card ≤ B →
    let t := P.parts.card
    ∀ (p : Fin t ≃ P.parts) (R : Fin 3 → SimpleGraph (Fin t)),
    let k := ⌈(1/4+1/(H:ℝ))*t⌉₊
    let d := ⌈(1/(H:ℝ))*t⌉₊
    (∀ i x y, (R i).Adj x y ↔ x≠y ∧ (∀ j, (c j).IsUniform η (p x) (p y)) ∧ 1/(H:ℝ) ≤ ((c i).edgeDensity (p x) (p y):ℝ)) →
    (∃ E : Finset (Fin t × Fin t), E.card < (d+1)^2 ∧ ∀ x y, x≠y → (x,y) ∉ E → ∃ i, (R i).Adj x y) →
    (∃ i u, let C := univ.filter ((R i).Reachable u)
      t<C.card+k+6*d ∧ ∃ S T W : Finset (Fin t), C=S∪T∪W ∧ Disjoint S T ∧ Disjoint (S∪T) W ∧
      S.card=T.card ∧ S.card<k ∧ (∀ x∈W, ∀ y∈W, ¬(R i).Adj x y) ∧ (∀ x∈S, (W.filter ((R i).Adj x)).card≤1) ∧
      (W.Nonempty → ∃ j≠i, ∃ v∈W, W.card≤(W.filter ((R j).Reachable v)).card+3*d)) →
    (∃ i, cycleGraph (2*m) ⊑ c i) ∨ ∃ (f : V → Fin 4) (σ : Equiv.Perm (Fin 3)),
      let W := fun j => univ.filter (fun v => f v = j)
      let U := W 0 ∪ W 1
      let dense := fun i (X Y : Finset V) => (1-α)*(X.card:ℝ)*Y.card ≤ ∑ x ∈ X, ((Y.filter ((c (σ i)).Adj x)).card:ℝ)
      (∀ j, (1-α)*m ≤ (W j).card) ∧ dense 0 (W 0) (W 1) ∧ dense 1 (W 2) U ∧ dense 2 (W 3) U

/-- Finish the four-block case with its six exclusive cuts and its two near-quarter middle classes. -/
def H3 : Prop := ∀ α : ℝ, 0<α → ∀ᶠ H : ℕ in atTop, ∀ η : ℝ, 0<η → η ≤ (1/(H:ℝ))^2 →
    ∀ B : ℕ, ∀ᶠ m : ℕ in atTop,
    let V := Fin (4*m)
    ∀ (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj], (⊤ : SimpleGraph V).IsEdgeColouring c →
    ∀ P : Finpartition (univ : Finset V), P.IsEquipartition → H*H ≤ P.parts.card → P.parts.card ≤ B →
    let t := P.parts.card
    ∀ (p : Fin t ≃ P.parts) (R : Fin 3 → SimpleGraph (Fin t)),
    let k := ⌈(1/4+1/(H:ℝ))*t⌉₊
    let d := ⌈(1/(H:ℝ))*t⌉₊
    let e := t/H+3
    let cut := fun i (A D : Finset (Fin t)) => ∀ x ∈ A, ∀ y ∈ D, ∀ j, (R j).Adj x y → j=i
    (∀ i x y, (R i).Adj x y ↔ x≠y ∧ (∀ j, (c j).IsUniform η (p x) (p y)) ∧ 1/(H:ℝ) ≤ ((c i).edgeDensity (p x) (p y):ℝ)) →
    (∃ E : Finset (Fin t × Fin t), E.card < (d+1)^2 ∧ ∀ x y, x≠y → (x,y) ∉ E → ∃ i, (R i).Adj x y) →
    ((∀ i u, (univ.filter ((R i).Reachable u)).card+t/4≤t) ∧ ∃ (F : Fin 4 → Finset (Fin t)) (σ : Equiv.Perm (Fin 3)),
      Monotone (fun j => (F j).card) ∧ Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      t≤(∑ j, (F j).card)+2*d ∧ 24*e≤(F 0).card ∧ t/4-8*e ≤ (F 1).card ∧ (F 2).card ≤ t/4+2*e ∧
      (F 0).card+(F 3).card<2*k+2*d ∧ (∀ i : Fin 3, cut (σ i) (F 3) (F i.castSucc)) ∧
      ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → cut (σ l) (F i.castSucc) (F j.castSucc)) →
    (∃ i, cycleGraph (2*m) ⊑ c i) ∨ ∃ (f : V → Fin 4) (σ : Equiv.Perm (Fin 3)),
      let W := fun j => univ.filter (fun v => f v = j)
      let U := W 0 ∪ W 1
      let dense := fun i (X Y : Finset V) => (1-α)*(X.card:ℝ)*Y.card ≤ ∑ x ∈ X, ((Y.filter ((c (σ i)).Adj x)).card:ℝ)
      (∀ j, (1-α)*m ≤ (W j).card) ∧ dense 0 (W 0) (W 1) ∧ dense 1 (W 2) U ∧ dense 2 (W 3) U
  
theorem main : H1 → H2 → H3 → OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2.H1 := by
  intro classification large quarters α ha
  obtain ⟨H,hc,hl,hq⟩ := ((classification α ha).and ((large α ha).and (quarters α ha))).exists
  obtain ⟨η,hη,prec,B,main⟩ := hc
  filter_upwards [main,hl η hη prec B,hq η hη prec B] with m hm lm qm
  intro c dec col
  rcases hm c col with done | ⟨P,hp,lo,hi,p,R,graph,missing,big | pair⟩
  · exact done
  · exact lm c col P hp lo hi p R graph missing big
  · exact qm c col P hp lo hi p R graph missing pair

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R2
