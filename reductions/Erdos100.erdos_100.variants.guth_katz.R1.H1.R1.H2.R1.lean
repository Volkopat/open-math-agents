import OMAReductions.R_Erdos100_erdos_100_variants_guth_katz_R1_H1_R1
import Mathlib.NumberTheory.Harmonic.Bounds

/-! The Elekes–Sharir motion lines reduce congruent segments to incidences. The two remaining statements count rich points for the Guth–Katz lines: the two-rich estimate and the estimate for multiplicity at least three. See Guth and Katz, Annals of Mathematics 181 (2015), Section 2. -/

namespace OMA.R_Erdos100_erdos_100_variants_guth_katz_R1_H1_R1_H2_R1
open Finset
open scoped Classical

private lemma scalar {a b c d : ℝ} (h : a*c+b*d=0) (hn : c ≠ 0 ∨ d ≠ 0) :
    ∃! z : ℝ, a+z*d=0 ∧ b-z*c=0 := by
  by_cases hd : d=0
  · have hc := hn.resolve_right (not_not_intro hd)
    subst d
    have ha : a=0 := (mul_eq_zero.mp (by simpa using h)).resolve_right hc
    refine ⟨b/c, ⟨by simp [ha], by field_simp <;> ring⟩, ?_⟩
    rintro y ⟨_,hy⟩
    apply (eq_div_iff hc).2
    linarith
  · refine ⟨-a/d, ⟨by field_simp; ring, ?_⟩, ?_⟩
    · field_simp
      linarith
    · rintro y ⟨hy,_⟩
      apply (eq_div_iff hd).2
      linarith

private lemma distance_sq (p q : (EuclideanSpace ℝ (Fin 2))) :
    dist p q ^ 2 = (q 0-p 0)^2+(q 1-p 1)^2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]
  ring

/-- Distinct displacements of equal length determine exactly one height at
which the two motion lines intersect. -/
theorem intersection {a b c d : (EuclideanSpace ℝ (Fin 2))} (hd : dist a b = dist c d)
    (hne : b-a ≠ d-c) :
    let lineAt (p q : (EuclideanSpace ℝ (Fin 2))) (z : ℝ) : ℝ × ℝ :=
      (p 0+q 0+z*(p 1-q 1), p 1+q 1+z*(q 0-p 0))
    ∃! z : ℝ, lineAt a c z = lineAt b d z := by
  intro lineAt
  have hsq := congrArg (fun x : ℝ => x^2) hd
  change dist a b^2 = dist c d^2 at hsq
  rw [distance_sq, distance_sq] at hsq
  let u := b 0-a 0
  let v := b 1-a 1
  let s := d 0-c 0
  let t := d 1-c 1
  have nd : u-s ≠ 0 ∨ v-t ≠ 0 := by
    by_contra! H
    apply hne
    ext i
    fin_cases i
    · exact sub_eq_zero.mp H.1
    · exact sub_eq_zero.mp H.2
  have orth : (u+s)*(u-s)+(v+t)*(v-t)=0 := by
    change u^2+v^2 = s^2+t^2 at hsq
    nlinarith
  have eqv (z : ℝ) : lineAt a c z = lineAt b d z ↔
      (u+s)+z*(v-t)=0 ∧ (v+t)-z*(u-s)=0 := by
    simp only [lineAt, Prod.mk.injEq, u,v,s,t]
    constructor <;> rintro ⟨hx,hy⟩ <;> constructor <;> linarith
  obtain ⟨z,hz,uniq⟩ := scalar orth nd
  exact ⟨z,(eqv z).mpr hz,fun y hy => uniq y ((eqv y).mp hy)⟩

/-- At a specified motion point, a given starting point has at most one image. -/
theorem fixed_source {p q r : (EuclideanSpace ℝ (Fin 2))} {z : ℝ} :
    let lineAt (p q : (EuclideanSpace ℝ (Fin 2))) (z : ℝ) : ℝ × ℝ :=
      (p 0+q 0+z*(p 1-q 1), p 1+q 1+z*(q 0-p 0))
    lineAt p q z=lineAt p r z → q=r := by
  intro lineAt h
  obtain ⟨hx,hy⟩ := Prod.mk.inj h
  dsimp [lineAt] at hx hy
  have h₁ : q 0-r 0 = z*(q 1-r 1) := by linarith
  have h₂ : q 1-r 1 = -z*(q 0-r 0) := by linarith
  have hz : 0<1+z^2 := by positivity
  have hh : (1+z^2)*(q 0-r 0)=0 := by
    calc _ = (q 0-r 0)+z*(z*(q 0-r 0)) := by ring
         _ = (q 0-r 0)-z*(q 1-r 1) := by rw [h₂]; ring
         _ = 0 := by linarith
  have he := (mul_eq_zero.mp hh).resolve_left hz.ne'
  ext i
  fin_cases i
  · exact sub_eq_zero.mp he
  · exact sub_eq_zero.mp (by simpa [he] using h₂)

private lemma multiplicity_le (A : Finset (EuclideanSpace ℝ (Fin 2))) (x : (ℝ × (ℝ × ℝ))) :
    let lineAt (p q : (EuclideanSpace ℝ (Fin 2))) (z : ℝ) : ℝ × ℝ :=
      (p 0+q 0+z*(p 1-q 1), p 1+q 1+z*(q 0-p 0))
    let linesThrough (A : Finset (EuclideanSpace ℝ (Fin 2))) (x : (ℝ × (ℝ × ℝ))) :=
      (A ×ˢ A).filter (fun e => lineAt e.1 e.2 x.1 = x.2)
    (linesThrough A x).card ≤ A.card := by
  intro lineAt linesThrough
  apply card_le_card_of_injOn Prod.fst
  · intro e he
    exact (mem_product.mp (mem_filter.mp he).1).1
  · rintro ⟨p,q⟩ hp ⟨s,t⟩ ht he
    change p=s at he
    subst s
    exact Prod.ext rfl (fixed_source ((mem_filter.mp hp).2.trans (mem_filter.mp ht).2.symm))

/-- A finite set of motion points carrying all the nontranslation configurations,
with at most r(r−1) ordered configurations charged to a point of multiplicity r. -/
private lemma charge (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    let lineAt (p q : (EuclideanSpace ℝ (Fin 2))) (z : ℝ) : ℝ × ℝ :=
      (p 0+q 0+z*(p 1-q 1), p 1+q 1+z*(q 0-p 0))
    let linesThrough (A : Finset (EuclideanSpace ℝ (Fin 2))) (x : (ℝ × (ℝ × ℝ))) :=
      (A ×ˢ A).filter (fun e => lineAt e.1 e.2 x.1 = x.2)
    let P := A.offDiag
    let E := (P ×ˢ P).filter (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧
      q.1.2-q.1.1 ≠ q.2.2-q.2.1 ∧ q.1.2-q.1.1 ≠ -(q.2.2-q.2.1))
    ∃ X : Finset (ℝ × (ℝ × ℝ)), E.card ≤ ∑ x ∈ X, (linesThrough A x).card*((linesThrough A x).card-1) := by
  classical
  intro lineAt linesThrough P E
  let height (q : ((EuclideanSpace ℝ (Fin 2))×(EuclideanSpace ℝ (Fin 2)))×((EuclideanSpace ℝ (Fin 2))×(EuclideanSpace ℝ (Fin 2)))) := Classical.epsilon
    (fun z : ℝ => lineAt q.1.1 q.2.1 z = lineAt q.1.2 q.2.2 z)
  let center (q : ((EuclideanSpace ℝ (Fin 2))×(EuclideanSpace ℝ (Fin 2)))×((EuclideanSpace ℝ (Fin 2))×(EuclideanSpace ℝ (Fin 2)))) : (ℝ × (ℝ × ℝ)) :=
    (height q, lineAt q.1.1 q.2.1 (height q))
  let X := E.image center
  refine ⟨X, ?_⟩
  have fibre (x : (ℝ × (ℝ × ℝ))) : (E.filter (fun q => center q=x)).card ≤
      (linesThrough A x).offDiag.card := by
    apply card_le_card_of_injOn (fun q => ((q.1.1,q.2.1),(q.1.2,q.2.2)))
    · intro q hq
      obtain ⟨hq,hx⟩ := mem_filter.mp hq
      obtain ⟨hp,h⟩ := mem_filter.mp hq
      obtain ⟨h₁,h₂⟩ := mem_product.mp hp
      obtain ⟨ha,hb,hab⟩ := mem_offDiag.mp h₁
      obtain ⟨hc,hd,_⟩ := mem_offDiag.mp h₂
      have inter : lineAt q.1.1 q.2.1 (height q) = lineAt q.1.2 q.2.2 (height q) :=
        Classical.epsilon_spec (intersection h.1 h.2.1).exists
      subst x
      apply mem_offDiag.mpr
      exact ⟨mem_filter.mpr ⟨mem_product.mpr ⟨ha,hc⟩,rfl⟩,
        mem_filter.mpr ⟨mem_product.mpr ⟨hb,hd⟩,inter.symm⟩,
        fun heq => hab (congrArg Prod.fst heq)⟩
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ _ ⟨⟨e,f⟩,⟨g,h⟩⟩ _ eq
      simpa only [Prod.mk.injEq, and_assoc, and_left_comm, and_comm] using eq
  calc E.card = ∑ x ∈ X, (E.filter (fun q => center q=x)).card :=
        card_eq_sum_card_fiberwise fun q hq => mem_image_of_mem center hq
       _ ≤ ∑ x ∈ X, (linesThrough A x).offDiag.card := sum_le_sum fun x _ => fibre x
       _ = _ := by simp only [offDiag_card,Nat.mul_sub,Nat.mul_one]



/-- Counting ordered pairs by how many objects pass through each point. -/
lemma layer_count {α : Type*} (X : Finset α) (r : α → ℕ) (N : ℕ)
    (hr : ∀ x ∈ X, r x ≤ N) :
    ∑ x ∈ X, r x*(r x-1) =
      ∑ k ∈ range (N+1), ((X.filter (fun x => k < r x)).card)*(k*2) := by
  classical
  have row (x) (hx : x ∈ X) :
      r x*(r x-1) = ∑ k ∈ range (N+1), (if k < r x then k*2 else 0) := by
    rw [← Finset.sum_range_id_mul_two, Finset.sum_mul, ← Finset.sum_filter]
    congr 1
    ext k
    simp only [mem_filter,mem_range]
    constructor
    · intro hk
      exact ⟨by have := hr x hx; omega, hk⟩
    · exact And.right
  calc _ = ∑ x ∈ X, ∑ k ∈ range (N+1), (if k < r x then k*2 else 0) := sum_congr rfl row
       _ = ∑ k ∈ range (N+1), ∑ x ∈ X, (if k < r x then k*2 else 0) := sum_comm
       _ = _ := by
         apply sum_congr rfl
         intro k _
         rw [← Finset.sum_filter]
         simp

/-- The harmonic loss in the Guth–Katz argument from a uniform rich-point
bound. The estimate concerns an arbitrary finite family of multiplicities. -/
theorem rich_energy {α : Type*} (X : Finset α) (r : α → ℕ) (N : ℕ) (K : ℝ)
    (hr : ∀ x ∈ X, r x ≤ N) (hK : 0 ≤ K)
    (rich : ∀ k, 0 < k → (((X.filter (fun x => k < r x)).card : ℝ) * (k:ℝ)^2) ≤ K) :
    (∑ x ∈ X, r x*(r x-1) : ℕ) ≤ (2*K)*(1+Real.log N) := by
  classical
  rw [layer_count X r N hr, Nat.cast_sum]
  have term (k : ℕ) : ((((X.filter (fun x => k < r x)).card)*(k*2) : ℕ) : ℝ) ≤
      (2*K)*(k:ℝ)⁻¹ := by
    by_cases hz : k=0
    · simp [hz]
    have hk : 0<(k:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hk).mpr
    push_cast
    nlinarith only [rich k (Nat.pos_of_ne_zero hz)]
  have hsum : ∑ k ∈ range (N+1), (k:ℝ)⁻¹ = harmonic N := by
    rw [sum_range_succ',harmonic]
    simp
  calc _ ≤ ∑ k ∈ range (N+1), (2*K)*(k:ℝ)⁻¹ := sum_le_sum fun k _ => term k
       _ = (2*K)*(harmonic N : ℝ) := by rw [← Finset.mul_sum,hsum]
       _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)

/-- The two-rich motion points from Theorem 2.10 in Guth and Katz. -/
def H1 : Prop := by
  classical
  let lineAt (p q : (EuclideanSpace ℝ (Fin 2))) (z : ℝ) : ℝ × ℝ :=
      (p 0+q 0+z*(p 1-q 1), p 1+q 1+z*(q 0-p 0))
  let linesThrough (A : Finset (EuclideanSpace ℝ (Fin 2))) (x : (ℝ × (ℝ × ℝ))) :=
      (A ×ˢ A).filter (fun e => lineAt e.1 e.2 x.1 = x.2)
  exact ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))) (X : Finset (ℝ × (ℝ × ℝ))), 2 ≤ A.card →
  (∀ x ∈ X, 2 ≤ (linesThrough A x).card) → (X.card:ℝ) ≤ C*(A.card:ℝ)^3

/-- The k-rich motion points for k at least three. -/
def H2 : Prop := by
  classical
  let lineAt (p q : (EuclideanSpace ℝ (Fin 2))) (z : ℝ) : ℝ × ℝ :=
      (p 0+q 0+z*(p 1-q 1), p 1+q 1+z*(q 0-p 0))
  let linesThrough (A : Finset (EuclideanSpace ℝ (Fin 2))) (x : (ℝ × (ℝ × ℝ))) :=
      (A ×ˢ A).filter (fun e => lineAt e.1 e.2 x.1 = x.2)
  exact ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))) (X : Finset (ℝ × (ℝ × ℝ))) (k : ℕ),
  2 ≤ A.card → 3 ≤ k → (∀ x ∈ X, k ≤ (linesThrough A x).card) →
  (X.card:ℝ)*(k:ℝ)^2 ≤ C*(A.card:ℝ)^3

theorem main : H1 → H2 → OMA.R_Erdos100_erdos_100_variants_guth_katz_R1_H1_R1.H2 := by
  classical
  rintro ⟨C,hC,two⟩ ⟨D,hD,many⟩
  let B := max C D
  have hB : 0 < B := lt_of_lt_of_le hC (le_max_left _ _)
  refine ⟨6*B,by positivity,?_⟩
  intro A hA
  dsimp only
  obtain ⟨X,hX⟩ := charge A
  let lineAt (p q : (EuclideanSpace ℝ (Fin 2))) (z : ℝ) : ℝ × ℝ :=
      (p 0+q 0+z*(p 1-q 1), p 1+q 1+z*(q 0-p 0))
  let linesThrough (A : Finset (EuclideanSpace ℝ (Fin 2))) (x : (ℝ × (ℝ × ℝ))) :=
      (A ×ˢ A).filter (fun e => lineAt e.1 e.2 x.1 = x.2)
  let r (x : (ℝ × (ℝ × ℝ))) := (linesThrough A x).card
  let size := (A.card:ℝ)^3
  have hs : 0 ≤ size := by dsimp [size]; positivity
  have rich (k : ℕ) (hk : 0<k) : ((X.filter (fun x => k<r x)).card:ℝ)*(k:ℝ)^2 ≤ B*size := by
    let Y := X.filter (fun x => k<r x)
    have hy : ∀ x ∈ Y, k+1 ≤ (linesThrough A x).card := fun x hx => (mem_filter.mp hx).2
    change (Y.card:ℝ)*(k:ℝ)^2 ≤ B*size
    by_cases one : k=1
    · subst k
      simpa using (two A Y hA hy).trans (mul_le_mul_of_nonneg_right (le_max_left C D) hs)
    · have m := many A Y (k+1) hA (by omega) hy
      calc _ ≤ (Y.card:ℝ)*((k+1:ℕ):ℝ)^2 := by gcongr <;> omega
           _ ≤ D*size := m
           _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hs
  have energy := rich_energy X r A.card (B*size) (fun x _ => multiplicity_le A x)
    (mul_nonneg hB.le hs) rich
  have hlog : (1/2:ℝ) ≤ Real.log A.card := by
    have h₂ : (2:ℝ) ≤ A.card := by exact_mod_cast hA
    exact (by linarith [Real.log_two_gt_d9] : (1/2:ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) h₂)
  have envelope : (2*(B*size))*(1+Real.log A.card) ≤ (6*B)*size*Real.log A.card := by
    nlinarith only [mul_nonneg (mul_nonneg hB.le hs) (sub_nonneg.mpr hlog)]
  exact (Nat.cast_le.mpr hX).trans (energy.trans envelope)

end OMA.R_Erdos100_erdos_100_variants_guth_katz_R1_H1_R1_H2_R1
