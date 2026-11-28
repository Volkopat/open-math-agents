import OMAReductions.R_Erdos89_erdos_89_R2

-- Reduction of Erdos89.erdos_89.R2.H2. Credit: @wispiANt
open Finset EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R2_H2_R1

/-- Size of a quadratic parametric piece in terms of distances in the ambient set. -/
def H1 : Prop :=
  ∀ (P T : Finset ℝ²) (u v w : ℝ²), T ⊆ P →
    (∀ x ∈ T, ∃ t : ℝ, ∀ i, x i = u i + v i*t + w i*t^2) →
    T.card ≤ 4*distinctDistances P+1

/-- Remaining packing estimate when every k quadratic parametric pieces cover less than half the union. -/
def H2 : Prop :=
  ∃ C : ℕ, ∀ (k : ℕ) (F : Finset (Finset ℝ²)), 0 < k →
    (F : Set (Finset ℝ²)).PairwiseDisjoint id →
    (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p 0+b*p 1=c) →
    ((F.biUnion id).card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
    (∀ G : Finset (Finset ℝ²), G.card ≤ k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ (Collinear ℝ (T : Set ℝ²) ∨ Cospherical (T : Set ℝ²))) →
      2*(G.biUnion id).card < (F.biUnion id).card) →
    (∀ G : Finset (Finset ℝ²), G.card ≤ k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ ∃ u v w : ℝ², ∀ x ∈ T, ∃ t : ℝ,
        ∀ i, x i = u i + v i*t + w i*t^2) →
      2*(G.biUnion id).card < (F.biUnion id).card) →
    (∀ T ∈ F, ∀ p ∈ T,
      let G := F.erase T
      ∀ B ⊆ G.biUnion id, (G.biUnion id).card ≤ 2*B.card →
      k*B.card < ∑ U ∈ G, ∑ x ∈ U.filter (· ∈ B),
        let s := (B.filter fun y => dist p y = dist p x).card
        let t := ((B \ U).filter fun y => dist p y = dist p x).card
        t*(t-1)/(s-2)) →
    (let S := F.biUnion id
      let W := fun x y : ℝ² => S.filter fun p => dist p y = dist p x
      ∀ G : ℝ² → Finset ℝ², (∀ x ∈ S, G x ⊆ S.erase x) →
        (∀ r ∈ S.offDiag, (∑ x ∈ S, ((G x).filter fun y => r ∈ (W x y).offDiag).card) ≤ k^2) →
        ∀ H : ℝ² → Finset ℝ², (∀ x ∈ S, H x ⊆ S.erase x \ G x) →
          (∀ x ∈ S, ∃ J : Finset (Finset ℝ²), J.card ≤ k ∧ H x ⊆ J.biUnion id ∧
            ∀ T ∈ J, Collinear ℝ (insert x (T : Set ℝ²))) →
          2*k*S.card^2 < ∑ x ∈ S, ∑ y ∈ (S.erase x \ G x) \ H x, if k < (W x y).card then (W x y).card else 0) →
    (let S := F.biUnion id
      let z := fun p : ℝ² => Complex.mk (p 0) (p 1)
      let E := S.offDiag
      let f := fun e t : ℝ² × ℝ² => (z t.2-z t.1)/(z e.2-z e.1)
      ∀ A : Finset ℂ, A.card ≤ k → k*S.card^3 <
        ∑ e ∈ E, (E.filter fun t => dist t.1 t.2 = dist e.1 e.2 ∧ f e t ∉ A).card) →
    F.card ≤ C * (distinctDistances (F.biUnion id)+1)

section Curves

/-- A circle contains at most four distinct points of a quadratic parametrization. -/
private theorem quadratic_fiber (s : Finset ℝ²) (p u v w : ℝ²) (r : ℝ)
    (hs : ∀ x ∈ s, ∃ t : ℝ, ∀ i, x i = u i + v i*t + w i*t^2)
    (hr : ∀ x ∈ s, dist x p = r) : s.card ≤ 4 := by
  classical
  let a := u 0 - p 0
  let b := u 1 - p 1
  let M := Polynomial.monomial (R := ℝ)
  let P : Polynomial ℝ := M 4 (w 0^2+w 1^2) + M 3 (2*(v 0*w 0+v 1*w 1)) +
    M 2 (v 0^2+v 1^2+2*(a*w 0+b*w 1)) + M 1 (2*(a*v 0+b*v 1)) + M 0 (a^2+b^2-r^2)
  by_cases hzero : P = 0
  · have h4 := congrArg (fun f : Polynomial ℝ => f.coeff 4) hzero
    have h2 := congrArg (fun f : Polynomial ℝ => f.coeff 2) hzero
    norm_num only [P,M,Polynomial.coeff_add,Polynomial.coeff_zero,Polynomial.coeff_monomial,
      if_pos, if_neg, zero_add, add_zero] at h4 h2
    have hw0 : w 0 = 0 := by nlinarith [sq_nonneg (w 1)]
    have hw1 : w 1 = 0 := by nlinarith [sq_nonneg (w 0)]
    rw [hw0,hw1] at h2
    have hv0 : v 0 = 0 := by nlinarith [sq_nonneg (v 1)]
    have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0)]
    have hsub : s ⊆ {u} := by
      intro x hx
      obtain ⟨t,ht⟩ := hs x hx
      apply mem_singleton.mpr
      ext i
      fin_cases i
      · simpa [hw0,hv0] using ht 0
      · simpa [hw1,hv1] using ht 1
    exact (card_le_card hsub).trans (by simp)
  have hdegree : P.natDegree ≤ 4 := by
    dsimp [P,M]
    repeat' apply Polynomial.natDegree_add_le_of_degree_le
    all_goals exact (Polynomial.natDegree_monomial_le ..).trans (by decide)
  choose t ht using hs
  let pars := s.attach.image (fun x => t x.1 x.2)
  have hinj : Function.Injective (fun x : {x // x ∈ s} => t x.1 x.2) := by
    intro x y he
    change t x.1 x.2 = t y.1 y.2 at he
    apply Subtype.ext
    ext i
    rw [ht x.1 x.2 i,ht y.1 y.2 i,he]
  have hroots : pars.val ⊆ P.roots := by
    intro z hz
    obtain ⟨x,_,rfl⟩ := mem_image.mp (show z ∈ pars from hz)
    apply (Polynomial.mem_roots hzero).2
    have he := congrArg (fun d : ℝ => d^2) (hr x.1 x.2)
    simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs] at he
    rw [ht x.1 x.2 0,ht x.1 x.2 1] at he
    simp only [Polynomial.IsRoot, P,M,Polynomial.eval_add,Polynomial.eval_monomial]
    dsimp [a,b]
    linear_combination he
  have hc : pars.card = s.card := by simp [pars,card_image_of_injective _ hinj]
  rw [← hc]
  exact (Polynomial.card_le_degree_of_subset_roots hroots).trans hdegree

/-- The quadratic piece estimate holds unconditionally. -/
theorem quadratic_piece : H1 := by
  intro P s u v w hsP hparam
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  have hmap : ∀ x ∈ s.erase p, dist x p ∈ distanceSet P := by
    intro x hx
    exact Finset.mem_image.mpr ⟨(x, p), Finset.mem_offDiag.mpr
      ⟨hsP (mem_of_mem_erase hx), hsP hp, ne_of_mem_erase hx⟩, rfl⟩
  have h := Finset.card_le_mul_card_image_of_maps_to hmap 4 (by
    intro r _
    apply quadratic_fiber _ p u v w r
    · intro x hx
      exact hparam x (mem_of_mem_erase (mem_filter.mp hx).1)
    · intro x hx
      exact (mem_filter.mp hx).2)
  change #(s.erase p) ≤ 4 * distinctDistances P at h
  rw [← card_erase_add_one hp]
  exact Nat.add_le_add_right h 1

end Curves

theorem main : H1 → H2 → OMA.R_Erdos89_erdos_89_R2.H2 := by
  classical
  rintro piece ⟨C,hard⟩
  refine ⟨max C 8, ?_⟩
  intro k F hk hdis blocks size spread pins bisectors rotations
  by_cases small : (∀ G : Finset (Finset ℝ²), G.card ≤ k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ ∃ u v w : ℝ², ∀ x ∈ T, ∃ t : ℝ,
        ∀ i, x i = u i + v i*t + w i*t^2) →
      2*(G.biUnion id).card < (F.biUnion id).card)
  · exact (hard k F hk hdis blocks size spread small pins bisectors rotations).trans
      (Nat.mul_le_mul_right _ (le_max_left C 8))
  push Not at small
  obtain ⟨G,hG,hpieces,hhalf⟩ := small
  let S := F.biUnion id
  let D := distinctDistances S
  have hcover : (G.biUnion id).card ≤ k*(4*D+1) := calc
    _ ≤ ∑ T ∈ G, T.card := card_biUnion_le
    _ ≤ ∑ _T ∈ G, (4*D+1) := by
      apply sum_le_sum
      intro T hT
      obtain ⟨hsub,u,v,w,hparam⟩ := hpieces T hT
      exact piece S T u v w hsub hparam
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (4*D+1) hG
  have hs : S.card = F.card*k := by
    dsimp [S]
    rw [card_biUnion hdis]
    calc
      _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => (blocks T hT).1
      _ = _ := by simp
  have hb : F.card ≤ 8*D+2 := by
    apply Nat.le_of_mul_le_mul_right _ hk
    calc
      _ = S.card := hs.symm
      _ ≤ 2*(G.biUnion id).card := hhalf
      _ ≤ 2*(k*(4*D+1)) := Nat.mul_le_mul_left _ hcover
      _ = _ := by ring
  exact hb.trans ((by omega : 8*D+2 ≤ 8*(D+1)).trans (Nat.mul_le_mul_right _ (le_max_right C 8)))

end OMA.R_Erdos89_erdos_89_R2_H2_R1
