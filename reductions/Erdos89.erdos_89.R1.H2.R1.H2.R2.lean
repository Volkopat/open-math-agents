import OMAReductions.R_Erdos89_erdos_89_R1_H2_R1

-- Reduction of Erdos89.erdos_89.R1.H2.R1.H2. Credit: @wispiANt
open Finset EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R1_H2_R1_H2_R2

/-- Exact-size lattice comparison on sets with three commensurable pinned squared-distance tables. -/
def H1 : Prop :=
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  ∀ (P T : Finset X), T ⊆ P →
    (∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T,
        (q.val 0-p.val 0)*(r.val 1-p.val 1) ≠ (q.val 1-p.val 1)*(r.val 0-p.val 0) ∧
        ∃ L : ℝ, 0 < L ∧ ∀ x ∈ T, ∀ o : X, o = p ∨ o = q ∨ o = r →
          ∃ n : ℚ, dist x o^2 = L*n) →
      ∃ a b c : ℤ, 0 < a ∧ b^2 < 4*a*c ∧ ∃ S : Finset (ℤ × ℤ),
        S.card = T.card ∧
        let q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
        (S.offDiag.image fun xy => q (xy.1 - xy.2)).card ≤ distinctDistances P

/-- Remaining extremal comparison in the absence of a dense subset with such a triangle. -/
def H2 : Prop :=
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  ∃ K : ℕ, 0 < K ∧ ∃ N₀ : ℕ, ∀ P : Finset X, N₀ ≤ P.card →
    (∀ T ⊆ P, P.card ≤ 2*T.card → ¬ (∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T,
        (q.val 0-p.val 0)*(r.val 1-p.val 1) ≠ (q.val 1-p.val 1)*(r.val 0-p.val 0) ∧
        ∃ L : ℝ, 0 < L ∧ ∀ x ∈ T, ∀ o : X, o = p ∨ o = q ∨ o = r →
          ∃ n : ℚ, dist x o^2 = L*n)) →
      ∃ a b c : ℤ, 0 < a ∧ b^2 < 4*a*c ∧ ∃ S : Finset (ℤ × ℤ),
        S.card ≤ P.card ∧ P.card ≤ K * S.card ∧
        let q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
        (S.offDiag.image fun xy => q (xy.1 - xy.2)).card ≤ distinctDistances P

section Charts

/-- Clear the denominators of finitely many rational multiples without changing the ratios. -/
private theorem common_table_unit (V : Finset ℝ) (L : ℝ)
    (rat : ∀ a ∈ V, ∃ r : ℚ, a = L*r) :
    ∃ m : ℕ, 0 < m ∧ ∀ a ∈ V, ∃ z : ℤ, (m:ℝ)*a = L*z := by
  classical
  induction V using Finset.induction_on with
  | empty => exact ⟨1,by decide,by simp⟩
  | @insert v V hv ih =>
    obtain ⟨m,hm,old⟩ := ih (fun a ha => rat a (mem_insert_of_mem ha))
    obtain ⟨r,hr⟩ := rat v (mem_insert_self ..)
    have hd : (r.den:ℝ)*(r:ℝ) = r.num := by
      exact_mod_cast (mul_comm (r.den:ℚ) r).trans (Rat.mul_den_eq_num r)
    refine ⟨m*r.den,Nat.mul_pos hm r.den_pos,fun a ha => ?_⟩
    rcases mem_insert.mp ha with rfl|ha
    · refine ⟨(m:ℤ)*r.num,?_⟩
      push_cast
      rw [hr,← hd]
      ring
    · obtain ⟨z,hz⟩ := old a ha
      refine ⟨(r.den:ℤ)*z,?_⟩
      push_cast
      linear_combination (r.den:ℝ)*hz


/-- The dual Gram form recovers squared length from the two dot products. -/
private theorem gram_recovery (e f g h u v : ℝ) :
    (g^2+h^2)*(2*(e*u+f*v))^2 + (-2)*(e*g+f*h)*(2*(e*u+f*v))*(2*(g*u+h*v)) +
      (e^2+f^2)*(2*(g*u+h*v))^2 = 4*(e*h-f*g)^2*(u^2+v^2) := by ring

private theorem pin_delta (x y p q : ℝ²) :
    (dist x p^2-dist x q^2)-(dist y p^2-dist y q^2) =
      2*((q 0-p 0)*(x 0-y 0)+(q 1-p 1)*(x 1-y 1)) := by
  simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  ring

/-- With three commensurable squared-distance tables, their differences give
integer coordinates. The table on the pin triangle gives the integral form. -/
private theorem three_pin_chart {X : Type*} [PseudoMetricSpace X] (v : X → ℝ²)
    (iso : ∀ x y, dist (v x) (v y) = dist x y) (T : Finset X) (p q r : X)
    (hq : q ∈ T) (hr : r ∈ T)
    (hn : (v q 0-v p 0)*(v r 1-v p 1) ≠ (v q 1-v p 1)*(v r 0-v p 0))
    (L : ℝ) (hL : 0 < L)
    (tab : ∀ x ∈ T, ∀ o : X, o = p ∨ o = q ∨ o = r → ∃ n : ℤ, dist x o^2 = L*n) :
    ∃ a b c : ℤ, 0 < a ∧ b^2 < 4*a*c ∧ ∃ F : X → ℤ × ℤ, ∃ K : ℝ, 0 < K ∧
      ∀ x ∈ T, ∀ y ∈ T,
        (((a*(F x-F y).1^2+b*(F x-F y).1*(F x-F y).2+c*(F x-F y).2^2 : ℤ) : ℝ)) =
          K*dist x y^2 := by
  let I := fun x o : X => ⌊dist x o^2/L⌋
  have val (x) (hx : x ∈ T) (o) (ho : o = p ∨ o = q ∨ o = r) :
      dist x o^2 = L*(I x o : ℝ) := by
    obtain ⟨n,hn⟩ := tab x hx o ho
    simp [I,hn,hL.ne']
  let a := I r p
  let c := I q p
  let b := I r q - a - c
  let e := v q 0-v p 0
  let f := v q 1-v p 1
  let g := v r 0-v p 0
  let h := v r 1-v p 1
  have ha : L*(a:ℝ) = g^2+h^2 := by
    rw [← val r hr p (Or.inl rfl), ← iso]
    simp [g,h,EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]
  have hc : L*(c:ℝ) = e^2+f^2 := by
    rw [← val q hq p (Or.inl rfl), ← iso]
    simp [e,f,EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]
  have hb : L*(b:ℝ) = -2*(e*g+f*h) := by
    dsimp [b]
    push_cast
    rw [mul_sub,mul_sub,ha,hc,← val r hr q (Or.inr (Or.inl rfl)),← iso]
    simp only [e,f,g,h,EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
    ring
  have hdet : 0 < (e*h-f*g)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hn)
  have discr : L^2*(4*(a:ℝ)*c-(b:ℝ)^2) = 4*(e*h-f*g)^2 := calc
    _ = 4*(L*(a:ℝ))*(L*(c:ℝ))-(L*(b:ℝ))^2 := by ring
    _ = _ := by rw [ha,hb,hc]; ring
  have hd : (b:ℝ)^2 < 4*(a:ℝ)*c := by
    have pos : 0 < L^2*(4*(a:ℝ)*c-(b:ℝ)^2) := by rw [discr]; positivity
    exact sub_pos.mp (pos_of_mul_pos_right pos (sq_nonneg _))
  have ha0 : (0:ℝ) < a := by
    have hn0 : 0 ≤ L*(a:ℝ) := by rw [ha]; positivity
    have hnon := nonneg_of_mul_nonneg_right hn0 hL
    exact lt_of_le_of_ne hnon (by intro he; rw [← he] at hd; nlinarith [sq_nonneg (b:ℝ)])
  let F := fun x : X => (I x p-I x q,I x p-I x r)
  refine ⟨a,b,c,by exact_mod_cast ha0,by exact_mod_cast hd,F,4*(e*h-f*g)^2/L^3,by positivity,?_⟩
  intro x hx y hy
  have delta (o) (ho : o = p ∨ o = q ∨ o = r) :
      L*(((I x p-I x o)-(I y p-I y o) : ℤ):ℝ) =
        2*((v o 0-v p 0)*(v x 0-v y 0)+(v o 1-v p 1)*(v x 1-v y 1)) := by
    push_cast
    simp only [mul_sub, ← val x hx p (Or.inl rfl), ← val x hx o ho,
      ← val y hy p (Or.inl rfl), ← val y hy o ho, ← iso]
    simpa only [mul_sub] using pin_delta (v x) (v y) (v p) (v o)
  let s : ℝ := ((F x-F y).1:ℤ)
  let t : ℝ := ((F x-F y).2:ℤ)
  have hs : L*s = _ := delta q (Or.inr (Or.inl rfl))
  have ht : L*t = _ := delta r (Or.inr (Or.inr rfl))
  push_cast
  change (a:ℝ)*s^2+b*s*t+c*t^2 = _
  rw [div_mul_eq_mul_div,eq_div_iff (pow_ne_zero _ hL.ne')]
  calc
    _ = (L*(a:ℝ))*(L*s)^2+(L*(b:ℝ))*(L*s)*(L*t)+(L*(c:ℝ))*(L*t)^2 := by ring
    _ = _ := by
      rw [ha,hb,hc,hs,ht,← iso,EuclideanSpace.dist_sq_eq,Fin.sum_univ_two]
      simp only [Real.dist_eq,sq_abs]
      exact gram_recovery e f g h (v x 0-v y 0) (v x 1-v y 1)

/-- The two integral coordinates preserve distinctness and the form-value budget. -/
theorem three_pin_model : H1 := by
  classical
  let X := {x : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (x i)}
  intro P T hsub htri
  obtain ⟨p,_,q,hq,r,hr,hn,L,hL,rep⟩ := htri
  let E := T ×ˢ ({p,q,r} : Finset X)
  let V := E.image fun e => dist e.1 e.2^2
  have rat : ∀ s ∈ V, ∃ n : ℚ, s = L*n := by
    intro s hs
    obtain ⟨⟨x,o⟩,h,rfl⟩ := mem_image.mp hs
    obtain ⟨hx,ho⟩ := mem_product.mp h
    exact rep x hx o (by simpa using ho)
  obtain ⟨m,hm,hint⟩ := common_table_unit V L rat
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have htable (x) (hx : x ∈ T) (o) (ho : o = p ∨ o = q ∨ o = r) :
      ∃ n : ℤ, dist x o^2 = (L/m)*n := by
    have hmem : (x,o) ∈ E := mem_product.mpr ⟨hx,by simpa using ho⟩
    obtain ⟨n,hn⟩ := hint _ (mem_image.mpr ⟨(x,o),hmem,rfl⟩)
    refine ⟨n,?_⟩
    rw [div_mul_eq_mul_div,eq_div_iff hm'.ne',mul_comm]
    exact hn
  obtain ⟨a,b,c,ha,hd,F,K,hK,he⟩ :=
    three_pin_chart (fun x : X => x.val) (fun _ _ => rfl) T p q r hq hr hn (L/m) (div_pos hL hm') htable
  have hinj : Set.InjOn F (T : Set X) := by
    intro x hx y hy hxy
    have h := he x hx y hy
    rw [hxy,sub_self] at h
    simp at h
    rcases h with h|h
    · exact (hK.ne' h).elim
    · exact dist_eq_zero.mp h
  refine ⟨a,b,c,ha,hd,T.image F,card_image_of_injOn hinj,?_⟩
  apply card_le_card_of_surjOn (fun z : ℝ => ⌊K*z^2⌋)
  intro n hn
  obtain ⟨⟨s,t⟩,hst,rfl⟩ := mem_image.mp hn
  obtain ⟨hs,ht,hne⟩ := mem_offDiag.mp hst
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hs
  obtain ⟨y,hy,rfl⟩ := mem_image.mp ht
  refine ⟨dist x y,mem_image.mpr ⟨(x,y),mem_offDiag.mpr
    ⟨hsub hx,hsub hy,fun h => hne (congrArg F h)⟩,rfl⟩,?_⟩
  change ⌊K*dist x y^2⌋ = _
  rw [← he x hx y hy,Int.floor_intCast]

end Charts

theorem main : H1 → H2 → OMA.R_Erdos89_erdos_89_R1_H2_R1.H2 := by
  classical
  rintro model ⟨K,hK,N,hard⟩
  let X := {x : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (x i)}
  refine ⟨max K 2,lt_of_lt_of_le hK (le_max_left ..),N,fun P hP => ?_⟩
  by_cases hs : ∀ T ⊆ P, P.card ≤ 2*T.card → ¬ (∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T,
        (q.val 0-p.val 0)*(r.val 1-p.val 1) ≠ (q.val 1-p.val 1)*(r.val 0-p.val 0) ∧
        ∃ L : ℝ, 0 < L ∧ ∀ x ∈ T, ∀ o : X, o = p ∨ o = q ∨ o = r →
          ∃ n : ℚ, dist x o^2 = L*n)
  · obtain ⟨a,b,c,ha,hd,S,hlo,hhi,hval⟩ := hard P hP hs
    exact ⟨a,b,c,ha,hd,S,hlo,hhi.trans (Nat.mul_le_mul_right _ (le_max_left ..)),hval⟩
  push Not at hs
  obtain ⟨T,hsub,hhalf,htri⟩ := hs
  obtain ⟨a,b,c,ha,hd,S,hcard,hval⟩ := model P T hsub htri
  refine ⟨a,b,c,ha,hd,S,hcard.le.trans (card_le_card hsub),?_,hval⟩
  rw [hcard]
  exact hhalf.trans (Nat.mul_le_mul_right _ (le_max_right ..))

end OMA.R_Erdos89_erdos_89_R1_H2_R1_H2_R2
