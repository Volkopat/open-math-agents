import OMAReductions.R_Erdos101_erdos_101_R1_H1_R1

/-! External centers of secants to a bounded-degree real plane curve.

First extract a fixed finite matching of endpoint pairs, simultaneously
realized by a positive fraction of the centers on genuine four-point lines.
The remaining task is to place many centers realizing this single matching on
a bounded-degree curve. Its sample size may be chosen as a function of the
degree before the incidence density is known.

Credit: @ubuwaits. -/

namespace OMA.R_Erdos101_erdos_101_R1_H1_R1_H2_R1

open EuclideanGeometry MvPolynomial
open scoped Classical

/-- Dense curve secants produce a common matching of any prescribed size
at least 25, for a positive fraction of the external centers. -/
def H1 : Prop :=
  ∀ d m : ℕ, 25 ≤ m → ∀ τ : ℝ, 0 < τ → ∃ C : ℕ, 0 < C ∧ ∃ N : ℕ,
    ∀ S T : Finset ℝ², N ≤ S.card → T ⊆ S → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ F : MvPolynomial (Fin 2) ℝ, F.totalDegree ≤ d →
      (∀ p ∈ T, eval (fun i => p i) F ≠ 0) → τ*S.card ≤ T.card →
      (∀ p ∈ T, ∃ A : Finset (AffineSubspace ℝ ℝ²), τ*S.card ≤ A.card ∧
        ∀ L ∈ A, p ∈ L ∧ L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
          2 ≤ (S.filter (fun x => x ∈ L ∧ eval (fun i => x i) F = 0)).card) →
      ∃ W : Finset (ℝ² × ℝ²), ∃ U ⊆ T, S.card ≤ C*U.card ∧
        W ⊆ S ×ˢ S ∧ W.card = m ∧ Set.InjOn Prod.fst (W : Set (ℝ² × ℝ²)) ∧
        Set.InjOn Prod.snd (W : Set (ℝ² × ℝ²)) ∧
        ∀ p ∈ U, ∃ q ∈ T, p ≠ q ∧ ∀ v ∈ W,
          eval (fun i => v.1 i) F = 0 ∧ eval (fun i => v.2 i) F = 0 ∧
          ∃ w ∈ S, eval (fun i => w i) F = 0 ∧ w ≠ v.1 ∧ w ≠ v.2 ∧
            w ∉ line[ℝ,p,q] ∧ w ∈ line[ℝ,p,v.1] ∧ w ∈ line[ℝ,q,v.2] ∧
            line[ℝ,p,v.1] ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
            line[ℝ,q,v.2] ∈ linesWithPointsFor 4 (S : Set ℝ²)

/-- For a sufficiently large fixed matching, many first centers with a
partner realizing the entire matching force bounded-degree curve capture. -/
def H2 : Prop :=
  ∀ d : ℕ, ∃ m : ℕ, 25 ≤ m ∧ ∀ C : ℕ, 0 < C → ∃ e : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ S T U : Finset ℝ², N ≤ S.card → T ⊆ S → U ⊆ T → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 → F.totalDegree ≤ d →
      (∀ p ∈ T, eval (fun i => p i) F ≠ 0) → S.card ≤ C*U.card →
      ∀ W : Finset (ℝ² × ℝ²), (W ⊆ S ×ˢ S ∧ W.card = m ∧ Set.InjOn Prod.fst (W : Set (ℝ² × ℝ²)) ∧
        Set.InjOn Prod.snd (W : Set (ℝ² × ℝ²)) ∧
        ∀ p ∈ U, ∃ q ∈ T, p ≠ q ∧ ∀ v ∈ W,
          eval (fun i => v.1 i) F = 0 ∧ eval (fun i => v.2 i) F = 0 ∧
          ∃ w ∈ S, eval (fun i => w i) F = 0 ∧ w ≠ v.1 ∧ w ≠ v.2 ∧
            w ∉ line[ℝ,p,q] ∧ w ∈ line[ℝ,p,v.1] ∧ w ∈ line[ℝ,q,v.2] ∧
            line[ℝ,p,v.1] ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
            line[ℝ,q,v.2] ∈ linesWithPointsFor 4 (S : Set ℝ²)) →
      ∃ G : MvPolynomial (Fin 2) ℝ, G ≠ 0 ∧ G.totalDegree ≤ e ∧
        c*S.card ≤ (T.filter (fun p => eval (fun i => p i) G = 0)).card

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R1_H1_R1.H2 := by
  intro sample capture d τ pos
  obtain ⟨m,hm,fixed⟩ := capture d
  obtain ⟨C,hC,N₁,extract⟩ := sample d m hm τ pos
  obtain ⟨e,c,hc,N₂,locus⟩ := fixed C hC
  refine ⟨e,c,hc,max N₁ N₂,?_⟩
  intro S T n sub cap F nz deg outside dense rich
  obtain ⟨W,U,ut,many,pattern⟩ := extract S T ((le_max_left ..).trans n) sub cap F deg outside dense rich
  exact locus S T U ((le_max_right ..).trans n) sub ut cap F nz deg outside many W pattern

end OMA.R_Erdos101_erdos_101_R1_H1_R1_H2_R1
