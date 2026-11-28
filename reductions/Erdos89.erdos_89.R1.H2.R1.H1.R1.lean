import OMAReductions.R_Erdos89_erdos_89_R1_H2_R1

-- Reduction of Erdos89.erdos_89.R1.H2.R1.H1. Credit: @wispiANt
open Finset

namespace OMA.R_Erdos89_erdos_89_R1_H2_R1_H1_R1

/-- Cardinality of a rationally parametrized piece, measured using ambient norm values. -/
def H1 : Prop :=
  ∀ (d m : ℕ), 0 < d → ∀ (S T : Finset (ℤ × ℤ)), T ⊆ S →
    ∀ A B Q : Polynomial ℚ, A.natDegree ≤ m → B.natDegree ≤ m → Q.natDegree ≤ m →
    (∀ x ∈ T, ∃ t : ℚ, Q.eval t ≠ 0 ∧ (x.1:ℚ)*Q.eval t = A.eval t ∧
      (x.2:ℚ)*Q.eval t = B.eval t) →
    let norm := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    T.card ≤ (2*m)*(S.offDiag.image fun e => norm (e.1-e.2)).card+1

/-- Remaining packing estimate for families sparse on rational curves of bounded total degree. -/
def H2 : Prop :=
  ∃ C : ℕ, ∀ (d k : ℕ) (F : Finset (Finset (ℤ × ℤ))), 0 < d → Squarefree d → 0 < k →
    (F : Set (Finset (ℤ × ℤ))).PairwiseDisjoint id →
    (∀ T ∈ F, T.card = k ∧ ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p.1+b*p.2=c) →
    ((F.biUnion id).card : ℝ) ≤ Real.exp ((k : ℝ)^2) →
    (∀ G : Finset (Finset (ℤ × ℤ)), G.card ≤ k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ p ∈ T, a*p.1+b*p.2=c) →
      2*(G.biUnion id).card < (F.biUnion id).card) →
    (let S := F.biUnion id
     (∀ A : Finset (ℤ × ℤ), A ⊆ S → S.card ≤ 2*A.card → ∀ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) →
      let R := A.image (fun p : ℤ × ℤ => (a*p.1-(d:ℤ)*b*p.2, b*p.1+a*p.2))
      ∀ (g : ℤ) (o : ℤ × ℤ) (B : Finset (ℤ × ℤ)), 0 < g →
        B.image (fun z : ℤ × ℤ => (g*z.1+o.1,g*z.2+o.2)) = R →
        ∀ p ∈ B, ∀ t ∈ B, p.2 < t.2 →
        ∃ z ∈ B, ∃ u ∈ B, (d:ℤ)*(t.2-p.2)*k < (z.1-u.1)^2)) →
    (∀ (G : Finset (Finset (ℤ × ℤ))) (m : Finset (ℤ × ℤ) → ℕ),
      (∑ T ∈ G, max 1 (m T)) ≤ 2*k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ ∃ A B Q : Polynomial ℚ,
        A.natDegree ≤ m T ∧ B.natDegree ≤ m T ∧ Q.natDegree ≤ m T ∧
        ∀ x ∈ T, ∃ t : ℚ, Q.eval t ≠ 0 ∧ (x.1:ℚ)*Q.eval t = A.eval t ∧
          (x.2:ℚ)*Q.eval t = B.eval t) →
      2*(G.biUnion id).card < (F.biUnion id).card) →
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    F.card ≤ C * (((F.biUnion id).offDiag.image fun xy => q (xy.1-xy.2)).card+1)

section RationalCurves

/-- Clearing the denominator costs at most twice the parametrization degree.
A parameter for the pin witnesses nonvanishing on each nonzero shell. -/
private theorem rational_fiber (d : ℕ) (r : ℤ) (hr : r ≠ 0) (p : ℤ × ℤ)
    (s : Finset (ℤ × ℤ)) (A B Q : Polynomial ℚ) (m : ℕ)
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ m) (hQ : Q.natDegree ≤ m)
    (rep : ∀ x ∈ insert p s, ∃ t : ℚ, Q.eval t ≠ 0 ∧
      (x.1 : ℚ)*Q.eval t = A.eval t ∧ (x.2 : ℚ)*Q.eval t = B.eval t)
    (shell : ∀ x ∈ s, (x.1-p.1)^2+(d:ℤ)*(x.2-p.2)^2 = r) : s.card ≤ 2*m := by
  classical
  let X := A - Polynomial.C (p.1 : ℚ)*Q
  let Y := B - Polynomial.C (p.2 : ℚ)*Q
  let E := X^2 + Polynomial.C (d : ℚ)*Y^2 - Polynomial.C (r : ℚ)*Q^2
  have scale (c : ℚ) (P : Polynomial ℚ) : (Polynomial.C c * P).natDegree ≤ P.natDegree :=
    Polynomial.natDegree_mul_le.trans (by simp)
  have degXY (P : Polynomial ℚ) (hP : P.natDegree ≤ m) (c : ℚ) :
      (P - Polynomial.C c*Q).natDegree ≤ m :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hP ((scale c Q).trans hQ))
  have deg : E.natDegree ≤ 2*m := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · exact Polynomial.natDegree_pow_le_of_le 2 (degXY A hA _)
      · exact (scale _ _).trans (Polynomial.natDegree_pow_le_of_le 2 (degXY B hB _))
    · exact (scale _ _).trans (Polynomial.natDegree_pow_le_of_le 2 hQ)
  have ev (x : ℤ × ℤ) (t : ℚ) (hx : (x.1 : ℚ)*Q.eval t = A.eval t)
      (hy : (x.2 : ℚ)*Q.eval t = B.eval t) :
      E.eval t = (((x.1:ℚ)-p.1)^2+d*((x.2:ℚ)-p.2)^2-r)*(Q.eval t)^2 := by
    simp only [E,X,Y,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,← hx,← hy]
    ring
  have hne : E ≠ 0 := by
    obtain ⟨t,hq,hx,hy⟩ := rep p (mem_insert_self ..)
    intro he
    have h := ev p t hx hy
    rw [he] at h
    have hr' : (r:ℚ) ≠ 0 := by exact_mod_cast hr
    simp [hr',hq] at h
  choose t hq hx hy using fun x (h : x ∈ s) => rep x (mem_insert_of_mem h)
  let pars := s.attach.image (fun x => t x.1 x.2)
  have inj : Function.Injective (fun x : {x // x ∈ s} => t x.1 x.2) := by
    intro x y he
    change t x.1 x.2 = t y.1 y.2 at he
    have h₁ := hx x.1 x.2
    have h₂ := hy x.1 x.2
    rw [he, ← hx y.1 y.2] at h₁
    rw [he, ← hy y.1 y.2] at h₂
    apply Subtype.ext
    exact Prod.ext (by exact_mod_cast mul_right_cancel₀ (hq y.1 y.2) h₁)
      (by exact_mod_cast mul_right_cancel₀ (hq y.1 y.2) h₂)
  have roots : pars.val ⊆ E.roots := by
    intro z hz
    obtain ⟨x,_,rfl⟩ := mem_image.mp (show z ∈ pars from hz)
    apply (Polynomial.mem_roots hne).2
    change E.eval _ = 0
    rw [ev x.1 _ (hx x.1 x.2) (hy x.1 x.2)]
    have h : (((x.1.1:ℚ)-p.1)^2+d*((x.1.2:ℚ)-p.2)^2) = r := by
      exact_mod_cast shell x.1 x.2
    rw [h,sub_self,zero_mul]
  have hc : pars.card = s.card := by simp [pars,card_image_of_injective _ inj]
  rw [← hc]
  exact (Polynomial.card_le_degree_of_subset_roots roots).trans deg

/-- Each point except the pin belongs to a nonzero shell. -/
theorem rational_piece : H1 := by
  classical
  intro d m hd S T hsub A B Q hA hB hQ rep norm
  let D := S.offDiag.image fun e => norm (e.1-e.2)
  rcases T.eq_empty_or_nonempty with rfl | ⟨p,hp⟩
  · simp
  have hm : ∀ x ∈ T.erase p, norm (x-p) ∈ D := by
    intro x hx
    exact mem_image.mpr ⟨(x,p),mem_offDiag.mpr
      ⟨hsub (mem_of_mem_erase hx),hsub hp,ne_of_mem_erase hx⟩,rfl⟩
  have hc := card_le_mul_card_image_of_maps_to hm (2*m) (by
    intro r hr
    have hn : r ≠ 0 := by
      obtain ⟨⟨x,y⟩,he,rfl⟩ := mem_image.mp hr
      have hxy := (mem_offDiag.mp he).2.2
      intro hz
      change (x.1-y.1)^2+(d:ℤ)*(x.2-y.2)^2 = 0 at hz
      have hpos : (0:ℤ) < d := by exact_mod_cast hd
      have hs := mul_nonneg hpos.le (sq_nonneg (x.2-y.2))
      have hx : x.1-y.1 = 0 := by nlinarith [sq_nonneg (x.1-y.1)]
      rw [hx,zero_pow (by decide : 2 ≠ 0),zero_add] at hz
      have hy := (mul_eq_zero.mp hz).resolve_left hpos.ne'
      exact hxy (Prod.ext (sub_eq_zero.mp hx) (by nlinarith [sq_nonneg (x.2-y.2)]))
    apply rational_fiber d r hn p _ A B Q m hA hB hQ
    · intro x hx
      rcases mem_insert.mp hx with rfl|hx
      · exact rep _ hp
      · exact rep x (mem_of_mem_erase (mem_filter.mp hx).1)
    · intro x hx
      exact (mem_filter.mp hx).2)
  change (T.erase p).card ≤ (2*m)*D.card at hc
  rw [← card_erase_add_one hp]
  exact Nat.add_le_add_right hc 1

end RationalCurves

theorem main : H1 → H2 → OMA.R_Erdos89_erdos_89_R1_H2_R1.H1 := by
  classical
  rintro piece ⟨C,hard⟩
  refine ⟨max C 8, ?_⟩
  intro d k F hd hsq hk hdis blocks hcap hlines hwidth norm
  let S := F.biUnion id
  let D := (S.offDiag.image fun e => norm (e.1-e.2)).card
  by_cases small : (∀ (G : Finset (Finset (ℤ × ℤ))) (m : Finset (ℤ × ℤ) → ℕ),
      (∑ T ∈ G, max 1 (m T)) ≤ 2*k →
      (∀ T ∈ G, T ⊆ F.biUnion id ∧ ∃ A B Q : Polynomial ℚ,
        A.natDegree ≤ m T ∧ B.natDegree ≤ m T ∧ Q.natDegree ≤ m T ∧
        ∀ x ∈ T, ∃ t : ℚ, Q.eval t ≠ 0 ∧ (x.1:ℚ)*Q.eval t = A.eval t ∧
          (x.2:ℚ)*Q.eval t = B.eval t) →
      2*(G.biUnion id).card < (F.biUnion id).card)
  · exact (hard d k F hd hsq hk hdis blocks hcap hlines hwidth small).trans
      (Nat.mul_le_mul_right _ (le_max_left C 8))
  push Not at small
  obtain ⟨G,m,hbudget,hpieces,hhalf⟩ := small
  have hcover : (G.biUnion id).card ≤ (2*k)*(2*D+1) := calc
    _ ≤ ∑ T ∈ G, T.card := card_biUnion_le
    _ ≤ ∑ T ∈ G, max 1 (m T)*(2*D+1) := by
      apply sum_le_sum
      intro T hT
      obtain ⟨hs,A,B,Q,hA,hB,hQ,rep⟩ := hpieces T hT
      have he := piece d (m T) hd S T hs A B Q hA hB hQ rep
      change T.card ≤ (2*m T)*D+1 at he
      have hmul := Nat.mul_le_mul_right (2*D) (le_max_right 1 (m T))
      calc
        _ ≤ (2*m T)*D+1 := he
        _ = m T*(2*D)+1 := by ring
        _ ≤ max 1 (m T)*(2*D)+max 1 (m T) := Nat.add_le_add hmul (le_max_left ..)
        _ = _ := by ring
    _ = (∑ T ∈ G, max 1 (m T))*(2*D+1) := (sum_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hbudget
  have hs : S.card = F.card*k := by
    dsimp [S]
    rw [card_biUnion hdis]
    calc
      _ = ∑ _T ∈ F, k := sum_congr rfl fun T hT => (blocks T hT).1
      _ = _ := by simp
  have hb : F.card ≤ 8*D+4 := by
    apply Nat.le_of_mul_le_mul_right _ hk
    calc
      _ = S.card := hs.symm
      _ ≤ 2*(G.biUnion id).card := hhalf
      _ ≤ 2*((2*k)*(2*D+1)) := Nat.mul_le_mul_left _ hcover
      _ = _ := by ring
  exact hb.trans ((by omega : 8*D+4 ≤ 8*(D+1)).trans (Nat.mul_le_mul_right _ (le_max_right C 8)))

end OMA.R_Erdos89_erdos_89_R1_H2_R1_H1_R1
