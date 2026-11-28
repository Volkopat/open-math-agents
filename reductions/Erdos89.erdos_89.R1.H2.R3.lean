import OMAReductions.R_Erdos89_erdos_89_R1

-- Reduction of Erdos89.erdos_89.R1.H2. Credit: @wispiANt
open Finset Filter EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R1_H2_R3

/-- The remaining squarefree diagonal estimate. For every dense subset and
assignment of occupied pins, any modulus compatible with the vertical progression
in each pin-column pair puts more than k pairs in some form-value residue.
Every nonempty family of realized gaps also exceeds the divisor budget.
The estimate is only required outside the polynomial and polylogarithmic coefficient ranges for
fixed exponent r and density parameter t₀, chosen uniformly in the configuration. -/
def H1 : Prop :=
  ∃ r t₀ C : ℕ, ∀ (d : ℕ) (S : Finset (ℤ × ℤ)) (k : ℕ), 0 < d → Squarefree d →
    0 < k → (S.card : ℝ) ≤ Real.exp ((k:ℝ)^2) →
    (d ≠ 1 ∨ ∀ (u : ℤ) (H : ℕ), (∀ z ∈ S, u ≤ z.1 ∧ z.1 < u+H) →
      (t₀:ℝ)*k*S.card < (H:ℝ)^2*(1+Real.log ((H:ℝ)+1))) →
    (∀ p ∈ S, ∀ W : ℕ, (∀ z ∈ S, (z.1-p.1).natAbs ≤ W) →
      (t₀:ℝ)*k*S.card < (W:ℝ)^2*(1+Real.log (2*W+1))^2) →
    (d ≠ 1 ∨ ∀ (A : Finset (ℕ × ℕ)) (H L : ℕ) (p : ℤ × ℤ) (s : ℤ), s ≠ 0 →
      A ⊆ range H ×ˢ range L → H*L ≤ t₀*A.card →
      (∀ z ∈ A, (p.1+s*z.1,p.2+s*z.2) ∈ S) →
      let K := 4*(t₀+1)
      let P := H/K+1
      let Q := L/K+1
      Set.ncard {n : ℕ | n < min S.card (P*Q) ∧ ∃ a b : ℕ, n=a^2+b^2} ≤
        (t₀+1)*(((range P ×ˢ range Q).image fun z => z.1^2+z.2^2).card+1) → 2*A.card < S.card) →
    (∀ p ∈ S, ∀ W : ℕ, (∀ z ∈ S, (z.1-p.1).natAbs ≤ W) →
      W^2 ≤ t₀*S.card → d^r < W^2 ∧ d^r < k^(5*r+1)) →
    (∀ T ⊆ S, S.card ≤ 2*T.card → ∀ (M : ℤ), 0 < M →
      ∀ (p : ℤ × ℤ → ℤ × ℤ) (t s : (ℤ × ℤ) × ℤ → ℤ),
      (∀ x ∈ T, let e := (p x,x.1)
        p x ∈ S ∧ s e ∣ x.2-(p x).2-t e ∧
        M ∣ (d:ℤ)*s e*(2*t e+s e) ∧ M ∣ 2*(d:ℤ)*(s e)^2) →
      ∃ r : ℤ, k < ((T.image fun x => (p x,x.1)).filter fun e =>
        ((e.2-e.1.1)^2+(d:ℤ)*(t e)^2) % M = r).card) →
    (∀ (A : Finset ℕ) (X : ℕ → Finset ℕ) (W : ℕ → ℕ),
      (∀ a ∈ A, X a ⊆ range (W a+1)) →
      (∀ a ∈ A, ∀ u ∈ X a, ∃ x ∈ S, ∃ y ∈ S,
        u = (x.1-y.1).natAbs ∧ a = d*(x.2-y.2).natAbs^2) →
      let mass := ∑ a ∈ A, (X a).card
      let cost := ∑ a ∈ A, ∑ b ∈ A, if a=b then (X a).card else
        let h := max a b-min a b
        min (min (X a).card (X b).card) (h.divisors.filter fun j =>
          j ≤ h/j ∧ h/j+j ≤ 2*W (min a b) ∧ h/j-j ≤ 2*W (max a b) ∧ j%2 = (h/j)%2).card
      0 < mass → k*mass^2 < S.card*cost) →
    let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
    S.card ≤ k*C*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1)

/-- The complementary finite estimate for minimizers without a binary quadratic
lattice model on any subset containing half the points. -/
def H2 : Prop :=
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  ∃ C : ℕ, ∀ (S : Finset X) (k : ℕ), 0 < k → (S.card : ℝ) ≤ Real.exp ((k:ℝ)^2) →
    distinctDistances S = minimalDistinctDistances X S.card →
    (∀ T ⊆ S, S.card ≤ 2*T.card → ¬ (∃ (f : X → ℤ × ℤ) (a b c : ℝ), ∀ x ∈ T, ∀ y ∈ T,
          dist x y^2 = a*(f x-f y).1^2+b*(f x-f y).1*(f x-f y).2+c*(f x-f y).2^2)) →
    S.card ≤ k*C*(distinctDistances S+1)

/-- Finite lower Landau–Ramanujan bound at the logarithmic scale of the reduction. -/
def H3 : Prop :=
  ∃ C : ℕ, ∀ X k : ℕ, 0 < k → (X:ℝ) ≤ Real.exp ((k:ℝ)^2) →
    ∀ B : Finset ℕ, (∀ n, n ∈ B ↔ 0 < n ∧ n < X ∧ ∃ a b : ℕ, n = a^2+b^2) →
      X ≤ k*C*(B.card+1)

section Shells

/-- On a line through the origin a nonzero quadratic level has at most two points. -/
private theorem line_shell (T : Finset (ℤ × ℤ)) (a b c r u v : ℝ) (hr : r ≠ 0)
    (huv : u ≠ 0 ∨ v ≠ 0)
    (line : ∀ x ∈ T, u*x.1+v*x.2 = 0)
    (shell : ∀ x ∈ T, a*x.1^2+b*x.1*x.2+c*x.2^2 = r) : T.card ≤ 2 := by
  classical
  have count (g : ℤ × ℤ → ℝ) (l : ℝ)
      (inj : Set.InjOn g (T : Set (ℤ × ℤ)))
      (he : ∀ x ∈ T, l*(g x)^2 = r) : T.card ≤ 2 := by
    rcases T.eq_empty_or_nonempty with rfl|⟨x,hx⟩
    · simp
    have hl : l ≠ 0 := by intro h; simpa [h,hr.symm] using he x hx
    have sub : T.image g ⊆ {g x,-g x} := by
      intro t ht
      obtain ⟨y,hy,rfl⟩ := mem_image.mp ht
      have hh := mul_left_cancel₀ hl ((he y hy).trans (he x hx).symm)
      simpa using sq_eq_sq_iff_eq_or_eq_neg.mp hh
    rw [← card_image_of_injOn inj]
    exact (card_le_card sub).trans (card_le_two ..)
  by_cases hv : v = 0
  · have hu := huv.resolve_right (not_not.mpr hv)
    have zero (x) (hx : x ∈ T) : (x.1:ℝ) = 0 := by
      have := line x hx
      simpa [hv,hu] using this
    refine count (fun x => x.2) c ?_ ?_
    · intro x hx y hy h
      change (x.2:ℝ) = y.2 at h
      exact Prod.ext (by exact_mod_cast (zero x hx).trans (zero y hy).symm) (by exact_mod_cast h)
    · intro x hx
      simpa [zero x hx] using shell x hx
  let t := -u/v
  have eqt (x) (hx : x ∈ T) : (x.2:ℝ) = t*x.1 := by
    dsimp [t]
    rw [div_mul_eq_mul_div,eq_div_iff hv]
    linarith [line x hx]
  refine count (fun x => x.1) (a+b*t+c*t^2) ?_ ?_
  · intro x hx y hy h
    change (x.1:ℝ) = y.1 at h
    have he : (x.2:ℝ) = y.2 := (eqt x hx).trans (by rw [h,← eqt y hy])
    exact Prod.ext (by exact_mod_cast h) (by exact_mod_cast he)
  · intro x hx
    have hh := shell x hx
    rw [eqt x hx] at hh
    linear_combination hh

/-- A second independent quadratic equation restricts a shell to two lines. -/
private theorem conic_shell (T : Finset (ℤ × ℤ)) (a b c r A B C : ℝ) (hr : r ≠ 0)
    (hn : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0)
    (hom : ∀ x ∈ T, A*x.1^2+B*x.1*x.2+C*x.2^2 = 0)
    (shell : ∀ x ∈ T, a*x.1^2+b*x.1*x.2+c*x.2^2 = r) : T.card ≤ 4 := by
  classical
  have split (u v U V : ℝ) (h₁ : u ≠ 0 ∨ v ≠ 0) (h₂ : U ≠ 0 ∨ V ≠ 0)
      (cover : ∀ x ∈ T, (u*x.1+v*x.2)*(U*x.1+V*x.2) = 0) : T.card ≤ 4 := by
    let L := T.filter fun x => u*x.1+v*x.2 = 0
    let M := T.filter fun x => U*x.1+V*x.2 = 0
    have sub : T ⊆ L ∪ M := by
      intro x hx
      rcases mul_eq_zero.mp (cover x hx) with h|h
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hx,h⟩)
    have bounds (u v : ℝ) (h : u ≠ 0 ∨ v ≠ 0) :
        (T.filter fun x => u*x.1+v*x.2 = 0).card ≤ 2 :=
      line_shell _ a b c r u v hr h (fun _ hx => (mem_filter.mp hx).2)
        (fun x hx => shell x (mem_filter.mp hx).1)
    exact (card_le_card sub).trans ((card_union_le L M).trans (Nat.add_le_add (bounds u v h₁) (bounds U V h₂)))
  by_cases hC : C = 0
  · apply split 1 0 A B (Or.inl one_ne_zero) (by tauto)
    intro x hx
    have he := hom x hx
    rw [hC] at he
    linear_combination he
  rcases T.eq_empty_or_nonempty with rfl|⟨o,ho⟩
  · simp
  have hx : (o.1:ℝ) ≠ 0 := by
    intro h
    have he := hom o ho
    simp [h,hC] at he
    have hz := shell o ho
    simp [h,he,hr.symm] at hz
  let t := (o.2:ℝ)/o.1
  have ht : t*(o.1:ℝ) = o.2 := div_mul_cancel₀ _ hx
  have root : A+B*t+C*t^2 = 0 := by
    apply (mul_eq_zero.mp (show (A+B*t+C*t^2)*(o.1:ℝ)^2 = 0 by
      calc
        _ = A*o.1^2 + B*o.1*(t*o.1) + C*(t*o.1)^2 := by ring
        _ = 0 := by rw [ht]; exact hom o ho)).resolve_right (pow_ne_zero _ hx)
  apply split (-t) 1 (B+C*t) C (Or.inr one_ne_zero) (Or.inr hC)
  intro x hx
  linear_combination hom x hx - (x.1:ℝ)^2*root

private theorem observe_value (f : ℝ →ₗ[ℚ] ℚ) (a b c : ℝ) (x y : ℤ) :
    f (a*x^2+b*x*y+c*y^2) = f a*x^2+f b*x*y+f c*y^2 := by
  have scale (r : ℝ) (v : ℤ) : f (r*v) = f r*v := by
    simpa [zsmul_eq_mul, mul_comm] using map_zsmul f v r
  rw [show a*x^2+b*x*y+c*y^2 = a*((x^2:ℤ):ℝ)+b*((x*y:ℤ):ℝ)+c*((y^2:ℤ):ℝ) by push_cast; ring]
  rw [map_add, map_add, scale, scale, scale]
  push_cast
  ring

/-- Without a common rational scale, each positive level of an oblique binary form
contains at most four integral vectors. No preferred lattice axes are required. -/
theorem oblique_shell (T : Finset (ℤ × ℤ)) (a b c r : ℝ) (hr : 0 < r)
    (incomm : ¬ ∃ L : ℝ, 0 < L ∧ ∃ A B C : ℚ, a=L*A ∧ b=L*B ∧ c=L*C)
    (hs : ∀ x ∈ T, a*x.1^2+b*x.1*x.2+c*x.2^2 = r) : T.card ≤ 4 := by
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero ℚ hr.ne'
  let g := fun x : ℝ => (f r:ℝ)*x-r*(f x:ℝ)
  have hfr : (f r:ℝ) ≠ 0 := by exact_mod_cast hf
  have hn : g a ≠ 0 ∨ g b ≠ 0 ∨ g c ≠ 0 := by
    by_contra! h
    have prop (x : ℝ) (hx : g x = 0) : x = r*((f x/f r : ℚ):ℝ) := by
      rw [Rat.cast_div,mul_div_assoc',eq_div_iff hfr]
      dsimp [g] at hx
      linarith
    exact incomm ⟨r,hr,_,_,_,prop a h.1,prop b h.2.1,prop c h.2.2⟩
  apply conic_shell T a b c r (g a) (g b) (g c) hr.ne' hn _ hs
  intro x hx
  have he := hs x hx
  have hq := congrArg f he
  rw [observe_value] at hq
  have he' : (f a:ℝ)*x.1^2+(f b:ℝ)*x.1*x.2+(f c:ℝ)*x.2^2 = (f r:ℝ) := by
    exact_mod_cast hq
  dsimp [g]
  linear_combination (f r:ℝ)*he - r*he'

/-- Three commensurable squared side lengths of a noncollinear lattice triangle
force a common rational scale for all three coefficients of the ambient form. -/
theorem triangle_forces_scale (a b c : ℝ) (i j k l : ℤ) (hn : i*l-j*k ≠ 0)
    (L : ℝ) (hL : 0 < L) (s t u : ℚ)
    (h₁ : a*i^2+b*i*j+c*j^2 = L*s)
    (h₂ : a*k^2+b*k*l+c*l^2 = L*t)
    (h₃ : a*((i:ℝ)-k)^2+b*(i-k)*(j-l)+c*((j:ℝ)-l)^2 = L*u) :
    ∃ M : ℝ, 0 < M ∧ ∃ A B C : ℚ, a=M*A ∧ b=M*B ∧ c=M*C := by
  have hdet : (i:ℝ)*l-j*k ≠ 0 := by exact_mod_cast hn
  refine ⟨L/((i:ℝ)*l-j*k)^2,by positivity,
    l^2*s-(j:ℚ)*l*(s+t-u)+j^2*t,
    -2*(k:ℚ)*l*s+((i:ℚ)*l+j*k)*(s+t-u)-2*i*j*t,
    k^2*s-(i:ℚ)*k*(s+t-u)+i^2*t,?_,?_,?_⟩ <;>
    push_cast <;> rw [div_mul_eq_mul_div,eq_div_iff (pow_ne_zero _ hdet)]
  · linear_combination ((l:ℝ)^2-j*l)*h₁ + ((j:ℝ)^2-j*l)*h₂ + ((j:ℝ)*l)*h₃
  · linear_combination (-2*(k:ℝ)*l+i*l+j*k)*h₁ + (-2*(i:ℝ)*j+i*l+j*k)*h₂ -
      ((i:ℝ)*l+j*k)*h₃
  · linear_combination ((k:ℝ)^2-i*k)*h₁ + ((i:ℝ)^2-i*k)*h₂ + ((i:ℝ)*k)*h₃


/-- From a single pin, count at most four targets per positive distance. -/
private theorem irrational_count {X : Type*} [MetricSpace X] (T : Finset X)
    (f : X → ℤ × ℤ) (a b c : ℝ)
    (incomm : ¬ ∃ L : ℝ, 0 < L ∧ ∃ A B C : ℚ, a=L*A ∧ b=L*B ∧ c=L*C)
    (chart : ∀ x ∈ T, ∀ y ∈ T, dist x y^2 = a*(f x-f y).1^2 +
      b*(f x-f y).1*(f x-f y).2+c*(f x-f y).2^2) :
    T.card ≤ 4*distinctDistances T+1 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl|⟨p,hp⟩
  · simp
  have inj : Set.InjOn f (T : Set X) := by
    intro x hx y hy e
    have he := chart x hx y hy
    rw [e,sub_self] at he
    simpa using he
  have hm : ∀ x ∈ T.erase p, dist x p ∈ distanceSet T :=
    fun x hx => mem_image.mpr ⟨(x,p),mem_offDiag.mpr ⟨mem_of_mem_erase hx,hp,ne_of_mem_erase hx⟩,rfl⟩
  have hc := card_le_mul_card_image_of_maps_to hm 4 (by
    intro r hr
    let U := (T.erase p).filter fun x => dist x p = r
    let g := fun x => f x-f p
    have pos : 0 < r := by
      obtain ⟨⟨x,y⟩,h,rfl⟩ := mem_image.mp hr
      exact dist_pos.mpr (mem_offDiag.mp h).2.2
    have hi : Set.InjOn g (U : Set X) := by
      intro x hx y hy h
      exact inj (mem_of_mem_erase (mem_filter.mp hx).1) (mem_of_mem_erase (mem_filter.mp hy).1)
        (sub_left_inj.mp h)
    change U.card ≤ 4
    rw [← card_image_of_injOn hi]
    apply oblique_shell _ a b c (r^2) (sq_pos_of_pos pos) incomm
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨hxt,hr⟩ := mem_filter.mp hx
    exact (chart x (mem_of_mem_erase hxt) p hp).symm.trans (congrArg (fun d : ℝ => d^2) hr))
  change (T.erase p).card ≤ 4*distinctDistances T at hc
  rw [← card_erase_add_one hp]
  exact Nat.add_le_add_right hc 1

end Shells

-- uses note #142812
-- uses note #142818
-- uses note #142820

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
private theorem three_pin_model :
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  ∀ (P T : Finset X), T ⊆ P →
    (∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T,
        (q.val 0-p.val 0)*(r.val 1-p.val 1) ≠ (q.val 1-p.val 1)*(r.val 0-p.val 0) ∧
        ∃ L : ℝ, 0 < L ∧ ∀ x ∈ T, ∀ o : X, o = p ∨ o = q ∨ o = r →
          ∃ n : ℚ, dist x o^2 = L*n) →
      ∃ a b c : ℤ, 0 < a ∧ b^2 < 4*a*c ∧ ∃ S : Finset (ℤ × ℤ),
        S.card = T.card ∧
        let q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
        (S.offDiag.image fun xy => q (xy.1 - xy.2)).card ≤ distinctDistances P := by
  classical
  let X := {x : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (x i)}
  intro _ P T hsub htri
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


/-- Three points with vanishing coordinate determinant lie on one affine line. -/
private theorem collinear_of_det (x y z : ℝ²) (hxy : x ≠ y)
    (h : (y 0-x 0)*(z 1-x 1) = (y 1-x 1)*(z 0-x 0)) :
    Collinear ℝ ({x,y,z} : Set ℝ²) := by
  apply (collinear_iff_of_mem (by simp : x ∈ ({x,y,z} : Set ℝ²))).2
  refine ⟨y-x,?_⟩
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with hmem|hmem|hmem <;> subst t
  · exact ⟨0,by simp⟩
  · exact ⟨1,by simp⟩
  by_cases hx : y 0-x 0 = 0
  · have hy : y 1-x 1 ≠ 0 := by
      intro he
      apply hxy
      ext i
      fin_cases i <;> simp_all <;> linarith
    refine ⟨(z 1-x 1)/(y 1-x 1),?_⟩
    ext i
    change z i = (z 1-x 1)/(y 1-x 1)*(y i-x i)+x i
    rcases (show i = 0 ∨ i = 1 by omega) with hi|hi <;> rw [hi]
    · rw [hx,mul_zero,zero_add]
      rw [hx,zero_mul] at h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hy)
    · field_simp
      ring
  · refine ⟨(z 0-x 0)/(y 0-x 0),?_⟩
    ext i
    change z i = (z 0-x 0)/(y 0-x 0)*(y i-x i)+x i
    rcases (show i = 0 ∨ i = 1 by omega) with hi|hi <;> rw [hi] <;> field_simp
    · ring
    · linear_combination h

/-- Without a noncollinear triangle, each pinned distance has at most two targets. -/
private theorem flat_count (T : Finset {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)})
    (flat : ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T,
      (y.val 0-x.val 0)*(z.val 1-x.val 1) = (y.val 1-x.val 1)*(z.val 0-x.val 0)) :
    T.card ≤ 2*distinctDistances T+1 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl|⟨p,hp⟩
  · simp
  have hm : ∀ x ∈ T.erase p, dist x p ∈ distanceSet T :=
    fun x hx => mem_image.mpr ⟨(x,p),mem_offDiag.mpr ⟨mem_of_mem_erase hx,hp,ne_of_mem_erase hx⟩,rfl⟩
  have hc := card_le_mul_card_image_of_maps_to hm 2 (by
    intro r _
    by_contra! h
    obtain ⟨x,hx,y,hy,z,hz,hxy,hxz,hyz⟩ := two_lt_card.mp h
    obtain ⟨hx,ex⟩ := mem_filter.mp hx
    obtain ⟨hy,ey⟩ := mem_filter.mp hy
    obtain ⟨hz,ez⟩ := mem_filter.mp hz
    let E : Set ℝ² := {v | dist v p.val = r}
    have sphere : Cospherical E := ⟨p.val,r,fun _ hv => hv⟩
    have ind := sphere.affineIndependent_of_mem_of_ne (show x.val ∈ E from ex)
      (show y.val ∈ E from ey) (show z.val ∈ E from ez)
      (Subtype.val_injective.ne hxy) (Subtype.val_injective.ne hxz) (Subtype.val_injective.ne hyz)
    apply (affineIndependent_iff_not_collinear_set.mp ind)
    exact collinear_of_det _ _ _ (Subtype.val_injective.ne hxy)
      (flat x (mem_of_mem_erase hx) y (mem_of_mem_erase hy) z (mem_of_mem_erase hz)))
  change (T.erase p).card ≤ 2*distinctDistances T at hc
  rw [← card_erase_add_one hp]
  exact Nat.add_le_add_right hc 1


/-- A single integral linear embedding works for every finite subset. It preserves
the entire set of form values on distinct pairs up to one common scaling. -/
private theorem squarefree_model (a b c : ℤ) (ha : 0 < a) (hdisc : b^2 < 4*a*c) :
    let values := fun (q : ℤ × ℤ → ℤ) (T : Finset (ℤ × ℤ)) => T.offDiag.image fun xy => q (xy.1-xy.2)
    ∃ d : ℕ, 0 < d ∧ Squarefree d ∧ ∃ F : ℤ × ℤ → ℤ × ℤ, Function.Injective F ∧
      ∀ S : Finset (ℤ × ℤ), (S.image F).card = S.card ∧
        values (fun z => z.1^2 + (d : ℤ)*z.2^2) (S.image F) =
          (values (fun z => a*z.1^2 + b*z.1*z.2 + c*z.2^2) S).image (4*a * ·) := by
  intro values
  have hp : 0 < 4*a*c - b^2 := by omega
  obtain ⟨d,r,hd,hr,he,hsq⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < (4*a*c-b^2).toNat by omega)
  have he' : (r : ℤ)^2 * d = 4*a*c - b^2 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Int.toNat_of_nonneg hp.le] using
      congrArg (fun n : ℕ => (n : ℤ)) he
  let F (p : ℤ × ℤ) : ℤ × ℤ := (2*a*p.1+b*p.2, (r:ℤ)*p.2)
  have hinj : Function.Injective F := by
    rintro ⟨x,y⟩ ⟨u,v⟩ h
    have hxy := congrArg Prod.fst h
    have hyv := congrArg Prod.snd h
    change (r:ℤ)*y = (r:ℤ)*v at hyv
    have : y = v := mul_left_cancel₀ (by exact_mod_cast hr.ne') hyv
    subst v
    change 2*a*x+b*y = 2*a*u+b*y at hxy
    exact Prod.ext (mul_left_cancel₀ (by positivity : 2*a ≠ 0) (add_right_cancel hxy)) rfl
  refine ⟨d, hd, hsq, F, hinj, fun S => ⟨Finset.card_image_of_injective _ hinj, ?_⟩⟩
  let Q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
  let D := fun z : ℤ × ℤ => z.1^2 + (d:ℤ)*z.2^2
  have hval (p t : ℤ × ℤ) : D (F p - F t) = 4*a*Q (p-t) := by
    dsimp [D, F, Q]
    linear_combination (p.2-t.2)^2 * he'
  have mem_values (q : ℤ × ℤ → ℤ) (T : Finset (ℤ × ℤ)) (w : ℤ) :
      w ∈ values q T ↔ ∃ p ∈ T, ∃ t ∈ T, p ≠ t ∧ q (p-t) = w := by
    constructor
    · intro h
      obtain ⟨⟨p,t⟩, hpt, hval⟩ := Finset.mem_image.mp h
      obtain ⟨hp, ht, hne⟩ := Finset.mem_offDiag.mp hpt
      exact ⟨p,hp,t,ht,hne,hval⟩
    · rintro ⟨p,hp,t,ht,hne,hval⟩
      exact Finset.mem_image.mpr ⟨(p,t), Finset.mem_offDiag.mpr ⟨hp,ht,hne⟩, hval⟩
  ext w
  change w ∈ values D (S.image F) ↔ w ∈ (values Q S).image _
  rw [mem_values, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, v, hv, hne, rfl⟩
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨_, (mem_values ..).mpr ⟨p,hp,t,ht,fun e => hne (congrArg F e),rfl⟩,
      (hval p t).symm⟩
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨p,hp,t,ht,hne,rfl⟩ := (mem_values ..).mp hw
    exact ⟨_,Finset.mem_image_of_mem F hp,_,Finset.mem_image_of_mem F ht,hinj.ne hne,hval p t⟩

/-- Exact divisibility test for the fixed divisor of a shifted quadratic progression. -/
theorem progression_modulus (M d t s : ℤ) :
    (∀ j : ℤ, M ∣ d*((t+s*j)^2-t^2)) ↔
      M ∣ d*s*(2*t+s) ∧ M ∣ 2*d*s^2 := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · convert h 1 using 1
      ring
    · have e : 2*d*s^2 = d*((t+s*1)^2-t^2) + d*((t+s*(-1))^2-t^2) := by ring
      rw [e]
      exact dvd_add (h 1) (h (-1))
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩ j
    obtain ⟨u,hu⟩ := (Int.even_mul_pred_self j).two_dvd
    refine ⟨a*j+b*u,?_⟩
    linear_combination j*ha + u*hb + d*s^2*hu

/-- Distinct pin-column pairs can occupy different vertical arithmetic
progressions, provided each progression fixes a residue of the form. -/
theorem shifted_pin_bound (d : ℕ) (hd : 0 < d) (S T : Finset (ℤ × ℤ))
    (p : ℤ × ℤ → ℤ × ℤ) (M : ℤ) (t s : (ℤ × ℤ) × ℤ → ℤ) (hsub : T ⊆ S) (k : ℕ)
    (pins : ∀ x ∈ T, let e := (p x,x.1)
      p x ∈ S ∧ s e ∣ x.2-(p x).2-t e ∧
      M ∣ (d:ℤ)*s e*(2*t e+s e) ∧ M ∣ 2*(d:ℤ)*(s e)^2)
    (hcap : ∀ r : ℤ, ((T.image fun x => (p x,x.1)).filter fun e =>
      ((e.2-e.1.1)^2+(d:ℤ)*(t e)^2) % M = r).card ≤ k) :
    let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
    T.card ≤ 2*k*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  intro q
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  let f := fun x : ℤ × ℤ => q (x-p x)
  let label := fun x : ℤ × ℤ => (p x,x.1)
  have hm : ∀ x ∈ T, f x ∈ insert 0 V := by
    intro x hx
    by_cases he : x=p x
    · have hz : x-p x=0 := sub_eq_zero.mpr he
      change q (x-p x) ∈ insert 0 V
      rw [hz]
      simp [q]
    · exact mem_insert_of_mem (mem_image.mpr ⟨(x,p x),mem_offDiag.mpr ⟨hsub hx,(pins x hx).1,he⟩,rfl⟩)
  have h := card_le_mul_card_image_of_maps_to hm (2*k) (by
    intro r _
    let U := T.filter fun x => f x=r
    let C := (T.image label).filter fun e => ((e.2-e.1.1)^2+(d:ℤ)*(t e)^2) % M = r % M
    let g := fun x : ℤ × ℤ => (label x,decide ((p x).2 ≤ x.2))
    have eqv (x) (hx : x ∈ U) : (x.1-(p x).1)^2+(d:ℤ)*(x.2-(p x).2)^2 = r := (mem_filter.mp hx).2
    have sub : U.image g ⊆ C ×ˢ (univ : Finset Bool) := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hx).1,?_⟩,mem_univ _⟩
      let e := label x
      change ((x.1-(p x).1)^2+(d:ℤ)*(t e)^2) % M = r % M
      obtain ⟨_,⟨j,hj⟩,h₁,h₂⟩ := pins x (mem_filter.mp hx).1
      have hv : x.2-(p x).2 = t e+s e*j := by change x.2-(p x).2-t e=s e*j at hj; omega
      obtain ⟨u,hu⟩ := (progression_modulus M d (t e) (s e)).2 ⟨h₁,h₂⟩ j
      have val : r = ((x.1-(p x).1)^2+(d:ℤ)*(t e)^2)+M*u := by
        rw [← eqv x hx,hv]
        linear_combination hu
      rw [val]
      simp
    have inj : Set.InjOn g (U : Set (ℤ × ℤ)) := by
      intro x hx y hy he
      have hl : label x=label y := congrArg Prod.fst he
      have ep : p x=p y := congrArg Prod.fst hl
      have ex : x.1=y.1 := congrArg Prod.snd hl
      have e := (eqv x hx).trans (eqv y hy).symm
      rw [ep,ex] at e
      have ey := sq_eq_sq_iff_eq_or_eq_neg.mp
        (mul_left_cancel₀ (by exact_mod_cast hd.ne' : (d:ℤ) ≠ 0) (add_left_cancel e))
      have sign := congrArg Prod.snd he
      simp [g,ep] at sign
      exact Prod.ext ex (by omega)
    have hc := card_le_card sub
    rw [card_image_of_injOn inj,card_product] at hc
    change U.card ≤ 2*k
    exact hc.trans (by simpa [mul_comm] using Nat.mul_le_mul_right 2 (hcap (r % M))))
  exact h.trans (Nat.mul_le_mul_left _ (card_insert_le ..))

/-- Targets may choose different pins. Vertical divisibility fixes the horizontal
square modulo d*m²; all pins draw values from the same set of pair values. -/
theorem assigned_pin_bound (d : ℕ) (hd : 0 < d) (S T : Finset (ℤ × ℤ))
    (p : ℤ × ℤ → ℤ × ℤ) (m : ℤ) (hsub : T ⊆ S) (k : ℕ)
    (pins : ∀ x ∈ T, p x ∈ S ∧ m ∣ x.2-(p x).2)
    (hcap : ∀ r : ℤ, ((T.image fun x => (p x,x.1)).filter fun e =>
      (e.2-e.1.1)^2 % ((d:ℤ)*m^2) = r).card ≤ k) :
    let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
    T.card ≤ 2*k*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  apply shifted_pin_bound d hd S T p ((d:ℤ)*m^2) (fun _ => 0) (fun _ => m) hsub k
  · intro x hx
    obtain ⟨hp,hm⟩ := pins x hx
    exact ⟨hp,by simpa using hm,⟨1,by ring⟩,⟨2,by ring⟩⟩
  · simpa using hcap

/-- Each pinned value fixes the horizontal square residue. Within each column its
targets are determined by the sign of their vertical displacement. -/
theorem residue_pin_bound (d : ℕ) (hd : 0 < d) (S T : Finset (ℤ × ℤ))
    (p : ℤ × ℤ) (hp : p ∈ S) (hsub : T ⊆ S) (k : ℕ)
    (hcap : ∀ r : ℤ, ((T.image Prod.fst).filter fun x => (x-p.1)^2 % (d:ℤ) = r).card ≤ k) :
    let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
    T.card ≤ 2*k*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  apply assigned_pin_bound d hd S T (fun _ => p) 1 hsub k (fun _ _ => ⟨hp,one_dvd _⟩)
  intro r
  let C := (T.image Prod.fst).filter fun x => (x-p.1)^2 % (d:ℤ) = r
  have sub : ((T.image fun x => (p,x.1)).filter fun e =>
      (e.2-e.1.1)^2 % ((d:ℤ)*1^2) = r) ⊆ C.image (fun x => (p,x)) := by
    intro z hz
    obtain ⟨hz,hr⟩ := mem_filter.mp hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨x.1,mem_filter.mpr ⟨mem_image_of_mem _ hx,by simpa using hr⟩,rfl⟩
  exact (card_le_card sub).trans (card_image_le.trans (hcap r))

-- uses note #91253
-- uses note #91254
-- uses note #91256
private lemma factor_of_collision (a b x y : ℕ) (hab : a < b) (he : x^2+a = y^2+b) :
    y < x ∧ b-a = (x-y)*(x+y) := by
  have hyx : y < x := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  refine ⟨hyx,?_⟩
  have ht := Nat.sub_add_cancel hyx.le
  have hs := Nat.sub_add_cancel hab.le
  nlinarith only [he,hs,congrArg (fun z : ℕ => z*(x+y)) ht]

/-- Exact divisor parametrization of the overlap of two shifted square sets
with complete horizontal gaps from zero through W. -/
private theorem overlap_exact (a b U V : ℕ) (hab : a < b) :
    let row := fun (a : ℕ) (X : Finset ℕ) => X.image fun x => x^2+a
    let factors := fun (h U V : ℕ) => h.divisors.filter fun j =>
      j ≤ h/j ∧ h/j+j ≤ 2*U ∧ h/j-j ≤ 2*V ∧ j%2 = (h/j)%2
    ((row a (range (U+1))) ∩ (row b (range (V+1)))).card = (factors (b-a) U V).card := by
  intro row factors
  let H := b-a
  have hH : 0 < H := Nat.sub_pos_of_lt hab
  let u (s : ℕ) := (H/s+s)/2
  let v (s : ℕ) := (H/s-s)/2
  have decode (s) (hs : s ∈ factors H U V) :
      u s ≤ U ∧ v s ≤ V ∧ u s-v s = s ∧ u s+v s = H/s ∧ (u s)^2+a = (v s)^2+b := by
    obtain ⟨hd,hle,hwidth,hheight,hpar⟩ := mem_filter.mp hs
    have hmul := Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    have hsub := Nat.sub_add_cancel hab.le
    have hdiff : u s = v s+s := by dsimp [u,v]; omega
    have hsum : u s+v s = H/s := by dsimp [u,v]; omega
    refine ⟨by dsimp [u]; omega,by dsimp [v]; omega,by omega,hsum,?_⟩
    rw [← hsum] at hmul
    change H+a=b at hsub
    nlinarith only [hmul,hsub,congrArg (fun z : ℕ => z*(u s+v s)) hdiff]
  let f (s : ℕ) := (u s)^2+a
  have himage : (factors H U V).image f = row a (range (U+1)) ∩ row b (range (V+1)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
      obtain ⟨hu,hv,_,_,he⟩ := decode s hs
      exact mem_inter.mpr ⟨mem_image.mpr ⟨_,mem_range.mpr (Nat.lt_succ_of_le hu),rfl⟩,
        mem_image.mpr ⟨_,mem_range.mpr (Nat.lt_succ_of_le hv),he.symm⟩⟩
    · intro hz
      obtain ⟨ha,hb⟩ := mem_inter.mp hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
      obtain ⟨y,hy,he⟩ := mem_image.mp hb
      obtain ⟨hlt,hm⟩ := factor_of_collision a b x y hab he.symm
      have hd : H/(x-y) = x+y := by
        change (b-a)/(x-y)=_
        rw [hm,Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hlt)]
      have hxW := mem_range.mp hx
      have hyW := mem_range.mp hy
      refine mem_image.mpr ⟨x-y,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨x+y,hm⟩,hH.ne'⟩,?_⟩,?_⟩
      · rw [hd]; omega
      · change ((H/(x-y)+(x-y))/2)^2+a=x^2+a
        rw [hd,show (x+y+(x-y))/2=x by omega]
  rw [← himage]
  apply card_image_of_injOn
  intro s hs t ht he
  obtain ⟨_,_,hds,_,hes⟩ := decode s hs
  obtain ⟨_,_,hdt,_,het⟩ := decode t ht
  change (u s)^2+a = (u t)^2+a at he
  have hu := Nat.pow_left_injective (by decide : 2 ≠ 0) (Nat.add_right_cancel he)
  have hv := Nat.pow_left_injective (by decide : 2 ≠ 0)
    (Nat.add_right_cancel (hes.symm.trans (he.trans het)))
  omega

/-- Deleting horizontal gaps can only decrease the overlap. -/
private theorem overlap_le (a b U V : ℕ) (hab : a < b) (X Y : Finset ℕ)
    (hx : X ⊆ range (U+1)) (hy : Y ⊆ range (V+1)) :
    let row := fun (a : ℕ) (X : Finset ℕ) => X.image fun x => x^2+a
    let factors := fun (h U V : ℕ) => h.divisors.filter fun j =>
      j ≤ h/j ∧ h/j+j ≤ 2*U ∧ h/j-j ≤ 2*V ∧ j%2 = (h/j)%2
    ((row a X) ∩ (row b Y)).card ≤ (factors (b-a) U V).card := by
  intro row factors
  rw [← overlap_exact a b U V hab]
  exact card_le_card (inter_subset_inter (image_mono _ hx) (image_mono _ hy))

private theorem count_row (a : ℕ) (X : Finset ℕ) :
    let row := fun (a : ℕ) (X : Finset ℕ) => X.image fun x => x^2+a
    (row a X).card = X.card := by
  intro row
  exact card_image_of_injective _ (fun _ _ he => Nat.pow_left_injective (by decide : 2 ≠ 0)
    (Nat.add_right_cancel he))

/-- Cauchy-Schwarz counts incidences of distinct values with rows.
The off-diagonal charges retain the parity and width of admissible factors. -/
private theorem union_bound (A : Finset ℕ) (X : ℕ → Finset ℕ) (W : ℕ → ℕ)
    (hW : ∀ a ∈ A, X a ⊆ range (W a+1)) :
    let row := fun (a : ℕ) (X : Finset ℕ) => X.image fun x => x^2+a
    let factors := fun (h U V : ℕ) => h.divisors.filter fun j =>
      j ≤ h/j ∧ h/j+j ≤ 2*U ∧ h/j-j ≤ 2*V ∧ j%2 = (h/j)%2
    (∑ a ∈ A, (X a).card)^2 ≤ (A.biUnion fun a => row a (X a)).card *
      ∑ a ∈ A, ∑ b ∈ A, if a=b then (X a).card else
        min (min (X a).card (X b).card) (factors (max a b-min a b) (W (min a b)) (W (max a b))).card := by
  intro row factors
  classical
  have hcount (a) : (row a (X a)).card = (X a).card := count_row a (X a)
  let F (a) := row a (X a)
  let U := A.biUnion F
  let ind (a z : ℕ) : ℕ := if z ∈ F a then 1 else 0
  have sub (a) (ha : a ∈ A) : F a ⊆ U := subset_biUnion_of_mem _ ha
  have mass : (∑ a ∈ A, (X a).card) = ∑ z ∈ U, ∑ a ∈ A, ind a z := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    have he : U.filter (fun z => z ∈ F a) = F a := by ext z; simp only [mem_filter]; exact
      ⟨fun h => h.2,fun h => ⟨sub a ha h,h⟩⟩
    simp only [ind,sum_boole,Nat.cast_id,he,F,hcount]
  have pair (a b) (ha : a ∈ A) : (∑ z ∈ U, ind a z * ind b z) = ((F a) ∩ (F b)).card := by
    have hi (z) : ind a z * ind b z = if z ∈ F a ∩ F b then 1 else 0 := by
      by_cases h : z ∈ F a <;> simp [ind,h]
    have he : U.filter (fun z => z ∈ F a ∩ F b) = F a ∩ F b := by
      ext z
      simp only [mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨sub a ha (mem_inter.mp h).1,h⟩⟩
    simp only [hi,sum_boole,Nat.cast_id,he]
  have energy : (∑ z ∈ U, (∑ a ∈ A, ind a z)^2) =
      ∑ a ∈ A, ∑ b ∈ A, ((F a) ∩ (F b)).card := by
    simp only [pow_two,sum_mul,mul_sum]
    rw [sum_comm (s := U) (t := A)]
    apply sum_congr rfl
    intro a ha
    rw [sum_comm]
    exact sum_congr rfl fun b _ => by simpa only [Nat.mul_comm] using pair a b ha
  rw [mass]
  apply sq_sum_le_card_mul_sum_sq.trans
  apply Nat.mul_le_mul_left
  rw [energy]
  apply sum_le_sum
  intro a ha
  apply sum_le_sum
  intro b hb
  split_ifs with he
  · subst b; simp [F,hcount]
  · apply le_min
    · apply le_min
      · simpa [F,hcount] using card_le_card (inter_subset_left (s₁ := F a) (s₂ := F b))
      · simpa [F,hcount] using card_le_card (inter_subset_right (s₁ := F a) (s₂ := F b))
    · rcases lt_or_gt_of_ne he with h|h
      · simpa only [F,max_eq_right h.le,min_eq_left h.le] using
          overlap_le a b (W a) (W b) h (X a) (X b) (hW a ha) (hW b hb)
      · simpa only [F,max_eq_left h.le,min_eq_right h.le,inter_comm] using
          overlap_le b a (W b) (W a) h (X b) (X a) (hW b hb) (hW a ha)

/-- The integer gaps can come from any pairs in S, including from a common pin.
The square of their total count is controlled by the distinct values times
a divisor sum that only uses row offsets, widths and row sizes. -/
theorem divisor_gap_bound (d : ℕ) (S : Finset (ℤ × ℤ))
    (A : Finset ℕ) (X : ℕ → Finset ℕ) (W : ℕ → ℕ)
    (width : ∀ a ∈ A, X a ⊆ range (W a+1))
    (realized : ∀ a ∈ A, ∀ u ∈ X a, ∃ x ∈ S, ∃ y ∈ S,
      u = (x.1-y.1).natAbs ∧ a = d*(x.2-y.2).natAbs^2) :
    let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
    let mass := ∑ a ∈ A, (X a).card
    let cost := ∑ a ∈ A, ∑ b ∈ A, if a=b then (X a).card else
        let h := max a b-min a b
        min (min (X a).card (X b).card) (h.divisors.filter fun j =>
          j ≤ h/j ∧ h/j+j ≤ 2*W (min a b) ∧ h/j-j ≤ 2*W (max a b) ∧ j%2 = (h/j)%2).card
    mass^2 ≤ ((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1)*cost := by
  classical
  intro q mass cost
  let U := A.biUnion fun a => (X a).image fun x => x^2+a
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  have sub : U.image (Nat.cast : ℕ → ℤ) ⊆ insert 0 V := by
    intro v hv
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hv
    obtain ⟨a,ha,hn⟩ := mem_biUnion.mp hn
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hn
    obtain ⟨x,hx,y,hy,rfl,rfl⟩ := realized a ha u hu
    by_cases he : x=y
    · simp [he]
    · apply mem_insert_of_mem
      refine mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hx,hy,he⟩,?_⟩
      simp [q]
  have card := card_le_card sub
  rw [card_image_of_injective _ Nat.cast_injective] at card
  exact (union_bound A X W width).trans
    (Nat.mul_le_mul_right cost (card.trans (card_insert_le ..)))

/-- Raising the divisor count to a fixed power costs at most a constant times n. -/
private theorem divisor_power_bound (k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, ∀ n : ℕ, 0 < n → n.divisors.card^k ≤ C*n := by
  classical
  let B := k^k
  refine ⟨B^(2^k),?_⟩
  intro n hn
  let P := n.primeFactors
  let f (p : ℕ) := if p < 2^k then B else 1
  have step (p : ℕ) (hp : p ∈ P) :
      (n.factorization p+1)^k ≤ f p*p^(n.factorization p) := by
    let a := n.factorization p
    change (a+1)^k ≤ f p*p^a
    by_cases small : p < 2^k
    · simp only [f,if_pos small]
      have hm := Nat.mod_lt a hk
      have he := Nat.mod_add_div a k
      have ha : a+1 ≤ k*(a/k+1) := by rw [Nat.mul_add_one]; omega
      have powle := Nat.pow_le_pow_left (show a/k+1 ≤ 2^(a/k) from (a/k).lt_two_pow_self) k
      calc
        _ ≤ (k*(a/k+1))^k := Nat.pow_le_pow_left ha k
        _ ≤ B*(2^(a/k))^k := by rw [mul_pow]; exact Nat.mul_le_mul_left _ powle
        _ ≤ B*p^a := by
          apply Nat.mul_le_mul_left
          rw [← pow_mul]
          exact (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self a k)).trans
            (Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _)
    · simp only [f,if_neg small,one_mul]
      calc
        _ ≤ (2^a)^k := Nat.pow_le_pow_left a.lt_two_pow_self k
        _ = (2^k)^a := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
        _ ≤ _ := Nat.pow_le_pow_left (by omega) a
  have size : (P.filter fun p => p < 2^k).card ≤ 2^k := by
    apply (card_le_card (show P.filter (fun p => p < 2^k) ⊆ range (2^k) from
      fun p hp => mem_range.mpr (mem_filter.mp hp).2)).trans
    simp
  have prod : (∏ p ∈ P, f p) ≤ B^(2^k) := by
    simp only [f,← prod_filter,prod_const]
    exact Nat.pow_le_pow_right (pow_pos hk _) size
  rw [Nat.card_divisors hn.ne',← prod_pow]
  calc
    _ ≤ ∏ p ∈ P, (f p * p^(n.factorization p)) := prod_le_prod' step
    _ = (∏ p ∈ P, f p)*n := by rw [prod_mul_distrib]; exact congrArg _ (Nat.prod_primeFactors_pow_factorization hn.ne').symm
    _ ≤ _ := Nat.mul_le_mul_right _ prod

/-- For a positive difference h of vertical squares, each pair of divisors
of d*h and h accounts for at most one repeated unsigned gap pair. -/
private theorem decode_collision (d : ℕ) (hd : 0 < d) (u v x y : ℕ) (hux : u < x)
    (eqv : u^2+d*v^2 = x^2+d*y^2) :
    let h := v^2-y^2
    0 < h ∧ d*h ≤ x^2 ∧ ∃ i ∈ (d*h).divisors, ∃ j ∈ h.divisors,
      (((d*h/i+i)/2,(h/j-j)/2),((d*h/i-i)/2,(h/j+j)/2)) = ((x,y),(u,v)) := by
  intro h
  have hv : y < v := by
    by_contra! hy
    have he := Nat.mul_le_mul_left d (Nat.pow_le_pow_left hy 2)
    have he' := Nat.pow_lt_pow_left hux (by decide : 2 ≠ 0)
    omega
  have hh : 0 < h := Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hv (by decide))
  have hy := Nat.sub_add_cancel (Nat.pow_le_pow_left hv.le 2)
  change h+y^2=v^2 at hy
  have factorV : h = (v-y)*(v+y) := by
    have he := Nat.sub_add_cancel hv.le
    nlinarith only [hy,congrArg (fun z : ℕ => z*(v+y)) he]
  have factorH : d*h = (x-u)*(x+u) := by
    have he := Nat.sub_add_cancel hux.le
    nlinarith only [eqv,congrArg (d*·) hy,congrArg (fun z : ℕ => z*(x+u)) he]
  refine ⟨hh,by nlinarith only [eqv,congrArg (d*·) hy,Nat.zero_le (u^2)],
    x-u,Nat.mem_divisors.mpr ⟨⟨_,factorH⟩,(Nat.mul_pos hd hh).ne'⟩,
    v-y,Nat.mem_divisors.mpr ⟨⟨_,factorV⟩,hh.ne'⟩,?_⟩
  have h₁ : d*h/(x-u)=x+u := by rw [factorH,Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hux)]
  have h₂ : h/(v-y)=v+y := by rw [factorV,Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hv)]
  rw [h₁,h₂]
  apply Prod.ext <;> apply Prod.ext <;> dsimp <;> omega

/-- Only W²/d positive differences of vertical squares can cause a repeat,
regardless of how high the selected rows extend. -/
theorem gap_repeat_bound (d W : ℕ) (hd : 0 < d) (T : Finset (ℕ × ℕ))
    (width : ∀ z ∈ T, z.1 ≤ W) :
    let q := fun z : ℕ × ℕ => z.1^2+d*z.2^2
    T.card ≤ (T.image q).card + ∑ h ∈ Icc 1 (W^2/d), (d*h).divisors.card*h.divisors.card := by
  classical
  intro q
  let E := T.filter fun z => ∃ w ∈ T, w.1 < z.1 ∧ q w=q z
  let F (h : ℕ) := ((d*h).divisors ×ˢ h.divisors).image fun ij =>
    ((d*h/ij.1+ij.1)/2,(h/ij.2-ij.2)/2)
  have sub : E ⊆ (Icc 1 (W^2/d)).biUnion F := by
    intro z hz
    obtain ⟨hzt,w,_,hw,he⟩ := mem_filter.mp hz
    obtain ⟨hh,hb,i,hi,j,hj,hij⟩ := decode_collision d hd w.1 w.2 z.1 z.2 hw he
    let h := w.2^2-z.2^2
    refine mem_biUnion.mpr ⟨h,mem_Icc.mpr ⟨hh,?_⟩,mem_image.mpr
      ⟨(i,j),mem_product.mpr ⟨hi,hj⟩,congrArg Prod.fst hij⟩⟩
    exact (Nat.le_div_iff_mul_le hd).mpr (by
      rw [Nat.mul_comm]; exact hb.trans (Nat.pow_le_pow_left (width z hzt) 2))
  have cost : E.card ≤ ∑ h ∈ Icc 1 (W^2/d), (d*h).divisors.card*h.divisors.card := by
    apply (card_le_card sub).trans (card_biUnion_le.trans ?_)
    exact sum_le_sum fun h _ => card_image_le.trans (le_of_eq (card_product ..))
  have inj : Set.InjOn q ((T \ E : Finset _) : Set _) := by
    intro z hz w hw e
    obtain ⟨hz,hnz⟩ := mem_sdiff.mp hz
    obtain ⟨hw,hnw⟩ := mem_sdiff.mp hw
    rcases lt_trichotomy z.1 w.1 with h|h|h
    · exact (hnw (mem_filter.mpr ⟨hw,z,hz,h,e⟩)).elim
    · apply Prod.ext h
      change z.1^2+d*z.2^2=w.1^2+d*w.2^2 at e
      rw [h] at e
      exact Nat.pow_left_injective (by decide : 2 ≠ 0)
        (Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel e))
    · exact (hnz (mem_filter.mpr ⟨hz,w,hw,h,e.symm⟩)).elim
  have good := card_le_card (image_mono q (sdiff_subset : T \ E ⊆ T))
  rw [card_image_of_injOn inj] at good
  have part := card_sdiff_add_card_eq_card (show E ⊆ T from filter_subset ..)
  omega

/-- Uniform in the coefficient and in the selected rows: the number lost
to repeated values is at most W²/t once d grows polynomially with W. -/
theorem polynomial_coefficient_gaps (r t : ℕ) : ∃ D₀ : ℕ, ∀ d W : ℕ,
    D₀ ≤ d → 0 < d → W^2 ≤ d^r → ∀ T : Finset (ℕ × ℕ), (∀ z ∈ T, z.1 ≤ W) →
    let q := fun z : ℕ × ℕ => z.1^2+d*z.2^2
    t*T.card ≤ t*(T.image q).card+W^2 := by
  classical
  let k := 2*r+1
  have hk : 0 < k := by dsimp [k]; omega
  obtain ⟨C,divisor⟩ := divisor_power_bound k hk
  refine ⟨t^k*C^2,?_⟩
  intro d W hd₀ hd hW T width q
  have bound (h : ℕ) (hh : h ∈ Icc 1 (W^2/d)) :
      t*((d*h).divisors.card*h.divisors.card) ≤ d := by
    obtain ⟨hhp,hhmax⟩ := mem_Icc.mp hh
    have hdh : d*h ≤ W^2 := by
      rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hd).mp hhmax
    have hh₁ : h ≤ d^r := (Nat.le_mul_of_pos_left _ hd).trans (hdh.trans hW)
    have hd₁ := hdh.trans hW
    suffices he : (t*((d*h).divisors.card*h.divisors.card))^k ≤ d^k by
      by_contra! hn
      exact (Nat.not_lt_of_ge he) (Nat.pow_lt_pow_left hn hk.ne')
    calc
      _ = t^k*((d*h).divisors.card^k*h.divisors.card^k) := by simp only [mul_pow]
      _ ≤ t^k*((C*(d*h))*(C*h)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul
        (divisor _ (Nat.mul_pos hd hhp)) (divisor _ hhp))
      _ ≤ t^k*((C*d^r)*(C*d^r)) := by gcongr
      _ = (t^k*C^2)*(d^r*d^r) := by ring
      _ ≤ d*(d^r*d^r) := Nat.mul_le_mul_right _ hd₀
      _ = d^k := by dsimp [k]; rw [show 2*r+1=r+r+1 by omega,pow_succ,pow_add]; ring
  have cost : t*(∑ h ∈ Icc 1 (W^2/d), (d*h).divisors.card*h.divisors.card) ≤ W^2 := by
    rw [mul_sum]
    exact (sum_le_sum bound).trans (by simpa using Nat.div_mul_le_self (W^2) d)
  have he := Nat.mul_le_mul_left t (gap_repeat_bound d W hd T width)
  rw [Nat.mul_add] at he
  exact he.trans (Nat.add_le_add_left cost _)

/-- At least half the points of a full L by L box give different values
as soon as L²≤d^r and d exceeds a threshold depending only on r. -/
theorem polynomial_coefficient_box (r : ℕ) : ∃ D₀ : ℕ, ∀ d L : ℕ,
    D₀ ≤ d → 0 < d → L^2 ≤ d^r →
    L^2 ≤ 2*(((range L) ×ˢ (range L)).image fun z => z.1^2+d*z.2^2).card := by
  obtain ⟨D₀,h⟩ := polynomial_coefficient_gaps r 2
  refine ⟨D₀,?_⟩
  intro d L h₀ hd hL
  have he := h d L h₀ hd hL ((range L) ×ˢ (range L)) (fun z hz =>
    (mem_range.mp (mem_product.mp hz).1).le)
  simp only [card_product,card_range] at he
  rw [← pow_two] at he
  omega


private theorem divisor_product_le (a b : ℕ) :
    (a*b).divisors.card ≤ a.divisors.card*b.divisors.card := by
  have sub : (a*b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun z => z.1*z.2) := by
    intro n hn
    obtain ⟨dv,hne⟩ := Nat.mem_divisors.mp hn
    obtain ⟨u,v,hu,hv,e⟩ := exists_dvd_and_dvd_of_dvd_mul dv
    exact mem_image.mpr ⟨(u,v),mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hu,left_ne_zero_of_mul hne⟩,
      Nat.mem_divisors.mpr ⟨hv,right_ne_zero_of_mul hne⟩⟩,e.symm⟩
  exact (card_le_card sub).trans (card_image_le.trans (le_of_eq (card_product ..)))

open ArithmeticFunction in
/-- Bounding the partial sums of ordered factorizations by iterating the
Dirichlet hyperbola identity and the harmonic sum estimate. -/
private theorem zeta_sum_bound (j N : ℕ) :
    (↑(∑ n ∈ Ioc 0 N, (ArithmeticFunction.zeta^(j+1)) n) : ℝ) ≤
      N*(1+Real.log (N+1))^j := by
  induction j generalizing N with
  | zero => simp only [Nat.zero_add,pow_one,sum_Ioc_zeta,pow_zero,mul_one,le_refl]
  | succ j ih =>
    let A := 1+Real.log ((N:ℝ)+1)
    have hA : 0 ≤ A := by dsimp [A]; linarith [Real.log_nonneg (show 1 ≤ (N:ℝ)+1 by simp)]
    rw [pow_succ',sum_Ioc_mul_eq_sum_sum]
    push_cast
    calc
      _ ≤ ∑ a ∈ Ioc 0 N, ((N:ℝ)/a)*A^j := by
        apply sum_le_sum
        intro a ha
        have ha' := (mem_Ioc.mp ha).1
        simp only [zeta_apply_ne ha'.ne',Nat.cast_one,one_mul]
        have e := ih (N/a)
        push_cast at e
        apply e.trans
        apply mul_le_mul
        · rw [le_div_iff₀ (by exact_mod_cast ha' : 0 < (a:ℝ))]
          exact_mod_cast Nat.div_mul_le_self N a
        · apply pow_le_pow_left₀ (by linarith [Real.log_nonneg (show 1 ≤ (↑(N/a):ℝ)+1 by simp)])
          dsimp [A]
          gcongr
          exact Nat.div_le_self .. 
        · exact pow_nonneg (by linarith [Real.log_nonneg (show 1 ≤ (↑(N/a):ℝ)+1 by simp)]) _
        · positivity
      _ = (N*A^j)*(∑ a ∈ Icc 1 N, (a:ℝ)⁻¹) := by
        rw [show Ioc 0 N = Icc 1 N from rfl,mul_sum]
        apply sum_congr rfl
        intro a _
        rw [div_eq_mul_inv]; ring
      _ ≤ (N*A^j)*A := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have e := harmonic_le_one_add_log N
        simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at e
        apply e.trans
        dsimp [A]
        by_cases h : N=0
        · simp [h]
        · exact add_le_add_right (Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)) (show (N:ℝ) ≤ N+1 by linarith)) 1
      _ = _ := by dsimp [A]; ring

open ArithmeticFunction in
private theorem divisor_square_mean (N : ℕ) :
    (↑(∑ n ∈ Ioc 0 N, n.divisors.card^2) : ℝ) ≤ N*(1+Real.log (N+1))^3 := by
  have z2 : ArithmeticFunction.zeta^2 = sigma 0 := by
    rw [pow_two,← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  have pt (n : ℕ) : n.divisors.card^2 ≤ (ArithmeticFunction.zeta^4) n := by
    rw [show (4:ℕ)=2+2 by decide,pow_add,z2,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (f := fun a b : ℕ => (sigma 0) a * (sigma 0) b)]
    calc
      _ = ∑ _a ∈ n.divisors, n.divisors.card := by simp [pow_two]
      _ ≤ _ := sum_le_sum fun a ha => by
        simp only [sigma_zero_apply]
        have hm := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
        simpa only [hm] using divisor_product_le a (n/a)
  exact (show (↑(∑ n ∈ Ioc 0 N, n.divisors.card^2) : ℝ) ≤
    ↑(∑ n ∈ Ioc 0 N, (ArithmeticFunction.zeta^4) n) by exact_mod_cast sum_le_sum fun n _ => pt n).trans
    (zeta_sum_bound 3 N)

private theorem pin_count {α γ : Type*} [DecidableEq γ] (B : Finset α)
    (D : Finset γ) (f : α → γ) (hf : ∀ x ∈ B, f x ∈ D) :
    B.card^2 ≤ D.card * (∑ x ∈ B, ∑ y ∈ B, if f y = f x then 1 else 0) := by
  classical
  let m (r : γ) := (B.filter fun y => f y = r).card
  have hsum : B.card = ∑ r ∈ D, m r := card_eq_sum_card_fiberwise hf
  have he : (∑ r ∈ D, m r ^ 2) = ∑ x ∈ B, m (f x) := by
    rw [← sum_fiberwise_of_maps_to hf (fun x => m (f x))]
    apply sum_congr rfl
    intro r _
    calc
      m r ^ 2 = ∑ _x ∈ B.filter (fun x => f x = r), m r := by simp [m,pow_two]
      _ = _ := sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]
  simp only [sum_boole, Nat.cast_id]
  change B.card^2 ≤ D.card * ∑ x ∈ B, m (f x)
  rw [← he, hsum]
  exact sq_sum_le_card_mul_sum_sq

private theorem collision_support_bound (d : ℕ) (hd : 0 < d) (T : Finset (ℕ × ℕ))
    (B : Finset ((ℕ × ℕ) × (ℕ × ℕ))) :
    let q := fun z : ℕ × ℕ => z.1^2+d*z.2^2
    (∀ z w : ℕ × ℕ, z ∈ T → w ∈ T → q w=q z → w.1<z.1 → (z,w) ∈ B) →
    T.card^2 ≤ (T.image q).card*(T.card+2*B.card) := by
  classical
  intro q low
  let E := (T ×ˢ T).filter fun z => q z.2=q z.1
  have sub : E ⊆ T.diag ∪ (B ∪ B.image Prod.swap) := by
    rintro ⟨z,w⟩ h
    obtain ⟨ht,e⟩ := mem_filter.mp h
    obtain ⟨hz,hw⟩ := mem_product.mp ht
    rcases lt_trichotomy z.1 w.1 with h|h|h
    · exact mem_union_right _ (mem_union_right _ (mem_image.mpr ⟨(w,z),low w z hw hz e.symm h,rfl⟩))
    · have he : z=w := by
        apply Prod.ext h
        change w.1^2+d*w.2^2=z.1^2+d*z.2^2 at e
        rw [h] at e
        exact Nat.pow_left_injective (by decide : 2 ≠ 0) (Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel e.symm))
      subst w
      exact mem_union_left _ (mem_diag.mpr ⟨hz,rfl⟩)
    · exact mem_union_right _ (mem_union_left _ (low z w hz hw e h))
  have ecard : E.card ≤ T.card+2*B.card := by
    have hu := (card_le_card sub).trans (card_union_le ..)
    have := card_union_le B (B.image Prod.swap)
    have := card_image_le (s := B) (f := Prod.swap)
    rw [diag_card] at hu
    omega
  have je : E.card = ∑ x ∈ T, ∑ y ∈ T, if q y=q x then 1 else 0 := by
    calc
      _ = ∑ z ∈ T ×ˢ T, (if q z.2=q z.1 then 1 else 0 : ℕ) := by simp [E]
      _ = _ := sum_product ..
  have he := pin_count T (T.image q) q (fun x hx => mem_image_of_mem _ hx)
  rw [← je] at he
  exact he.trans (Nat.mul_le_mul_left _ ecard)

/-- Second moment of the unsigned form values, counting both orders of
every unequal representation and the diagonal once. -/
theorem gap_collision_bound (d W : ℕ) (hd : 0 < d) (T : Finset (ℕ × ℕ))
    (width : ∀ z ∈ T, z.1 ≤ W) :
    let q := fun z : ℕ × ℕ => z.1^2+d*z.2^2
    T.card^2 ≤ (T.image q).card * (T.card+2*∑ h ∈ Ioc 0 (W^2/d),
      (d*h).divisors.card*h.divisors.card) := by
  classical
  intro q
  let F (h : ℕ) := ((d*h).divisors ×ˢ h.divisors).image fun ij =>
    (((d*h/ij.1+ij.1)/2,(h/ij.2-ij.2)/2),((d*h/ij.1-ij.1)/2,(h/ij.2+ij.2)/2))
  let B := (Ioc 0 (W^2/d)).biUnion F
  have low (z w : ℕ × ℕ) (hz : z ∈ T) (e : q w=q z) (hw : w.1<z.1) : (z,w) ∈ B := by
    obtain ⟨hh,hb,i,hi,j,hj,hij⟩ := decode_collision d hd w.1 w.2 z.1 z.2 hw e
    refine mem_biUnion.mpr ⟨_,mem_Ioc.mpr ⟨hh,?_⟩,mem_image.mpr ⟨(i,j),mem_product.mpr ⟨hi,hj⟩,hij⟩⟩
    exact (Nat.le_div_iff_mul_le hd).mpr (by
      rw [Nat.mul_comm]; exact hb.trans (Nat.pow_le_pow_left (width z hz) 2))
  have cost : B.card ≤ ∑ h ∈ Ioc 0 (W^2/d), (d*h).divisors.card*h.divisors.card :=
    card_biUnion_le.trans (sum_le_sum fun h _ => card_image_le.trans (le_of_eq (card_product ..)))
  exact (collision_support_bound d hd T B (fun z w hz _ => low z w hz)).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left 2 cost) _))

private theorem coefficient_absorption (r : ℕ) : ∃ C : ℕ, ∀ d k : ℕ, 0 < d →
    k^(5*r+1) ≤ d^r → k^5*d.divisors.card ≤ C*d := by
  obtain ⟨C,tau⟩ := divisor_power_bound (5*r+1) (by omega)
  refine ⟨C+1,?_⟩
  intro d k hd hk
  apply le_of_not_gt
  intro neg
  apply (not_le_of_gt (Nat.pow_lt_pow_left neg (by omega : 5*r+1 ≠ 0)))
  rw [mul_pow,mul_pow]
  have h : (k^5)^(5*r+1) ≤ (d^r)^5 := by
    rw [← pow_mul, Nat.mul_comm 5, pow_mul]
    exact Nat.pow_le_pow_left hk 5
  calc
    _ ≤ (d^r)^5 * (C*d) := Nat.mul_le_mul h (tau d hd)
    _ = C*d^(5*r+1) := by rw [pow_succ,← pow_mul,Nat.mul_comm r]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ ((Nat.le_succ C).trans
      (by simpa using Nat.pow_le_pow_right (by omega : 0 < C+1) (by omega : 1 ≤ 5*r+1)))

private theorem gap_sum_mean (d W : ℕ) (hd : 0 < d) :
    (↑(∑ h ∈ Ioc 0 (W^2/d), (d*h).divisors.card*h.divisors.card) : ℝ)*d ≤
      d.divisors.card*(W:ℝ)^2*(1+Real.log ((W:ℝ)^2+1))^3 := by
  let N := W^2/d
  have pt : (∑ h ∈ Ioc 0 N, (d*h).divisors.card*h.divisors.card) ≤
      d.divisors.card*(∑ h ∈ Ioc 0 N,h.divisors.card^2) := by
    rw [mul_sum]
    apply sum_le_sum
    intro h _
    simpa only [pow_two,mul_assoc] using Nat.mul_le_mul_right h.divisors.card (divisor_product_le d h)
  have hN : (N:ℝ)*d ≤ (W:ℝ)^2 := by exact_mod_cast Nat.div_mul_le_self (W^2) d
  have hN' : (N:ℝ) ≤ (W:ℝ)^2 := by exact_mod_cast Nat.div_le_self (W^2) d
  have logle : (1+Real.log ((N:ℝ)+1))^3 ≤ (1+Real.log ((W:ℝ)^2+1))^3 := by
    apply pow_le_pow_left₀ (by linarith [Real.log_nonneg (show 1 ≤ (N:ℝ)+1 by simp)])
    exact add_le_add_right (Real.log_le_log (by positivity) (add_le_add_left hN' 1)) 1
  have lm : 0 ≤ (1+Real.log ((W:ℝ)^2+1))^3 := by
    apply pow_nonneg
    linarith [Real.log_nonneg (show 1 ≤ (W:ℝ)^2+1 by nlinarith [sq_nonneg (W:ℝ)])]
  calc
    _ ≤ ((d.divisors.card:ℝ) * ↑(∑ h ∈ Ioc 0 N,h.divisors.card^2))*d := by exact_mod_cast Nat.mul_le_mul_right d pt
    _ ≤ ((d.divisors.card:ℝ) * (N*(1+Real.log ((N:ℝ)+1))^3))*d := by gcongr; exact divisor_square_mean N
    _ = (d.divisors.card:ℝ)*((N:ℝ)*d)*(1+Real.log ((N:ℝ)+1))^3 := by ring
    _ ≤ (d.divisors.card:ℝ)*((N:ℝ)*d)*(1+Real.log ((W:ℝ)^2+1))^3 := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by positivity)) lm

/-- A width bound and a size bound control the entire divisor collision budget. -/
private theorem polylog_gap_budget (r t : ℕ) : ∃ B : ℕ,
    ∀ d W n k : ℕ, 0 < d → 0 < k → (n:ℝ) ≤ Real.exp ((k:ℝ)^2) →
    W^2 ≤ t*n → k^(5*r+1) ≤ d^r →
    (∑ h ∈ Ioc 0 (W^2/d), (d*h).divisors.card*h.divisors.card) ≤ B*n*k := by
  obtain ⟨C,absorb⟩ := coefficient_absorption r
  refine ⟨C*t*(t+2)^3,?_⟩
  intro d W n k hd hk hn hW hscale
  have width : (W:ℝ)^2 ≤ t*(n:ℝ) := by exact_mod_cast hW
  have kk : 1 ≤ (k:ℝ)^2 := by exact_mod_cast (show 1 ≤ k^2 by simpa using Nat.pow_le_pow_left hk 2)
  have ex : 1 ≤ Real.exp ((k:ℝ)^2) := Real.one_le_exp (sq_nonneg _)
  have wlog : 1+Real.log ((W:ℝ)^2+1) ≤ (t+2:ℝ)*k^2 := by
    have h : (W:ℝ)^2+1 ≤ ((t:ℝ)+1)*Real.exp ((k:ℝ)^2) := by
      nlinarith only [width, mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg t),ex]
    have e := Real.log_le_log (by positivity) h
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',Real.log_exp] at e
    nlinarith [Real.log_le_sub_one_of_pos (show 0 < (t:ℝ)+1 by positivity),
      mul_le_mul_of_nonneg_left kk (Nat.cast_nonneg t)]
  let J := ∑ h ∈ Ioc 0 (W^2/d), (d*h).divisors.card*h.divisors.card
  have a : (k:ℝ)^5*d.divisors.card ≤ C*(d:ℝ) := by exact_mod_cast absorb d k hd hscale
  have e : (J:ℝ)*d ≤ ((C:ℝ)*t*((t:ℝ)+2)^3*n*k)*d := calc
    _ ≤ _ := gap_sum_mean d W hd
    _ ≤ (d.divisors.card:ℝ)*(t*(n:ℝ))*(((t:ℝ)+2)*k^2)^3 := by
      apply mul_le_mul _ _ (by apply pow_nonneg; linarith [Real.log_nonneg (show 1 ≤ (W:ℝ)^2+1 by nlinarith [sq_nonneg (W:ℝ)])]) (by positivity)
      · gcongr
      · exact pow_le_pow_left₀ (by linarith [Real.log_nonneg (show 1 ≤ (W:ℝ)^2+1 by nlinarith [sq_nonneg (W:ℝ)])]) wlog _
    _ = ((k:ℝ)^5*d.divisors.card)*(t*((t:ℝ)+2)^3*n*k) := by ring
    _ ≤ ((C:ℝ)*d)*(t*((t:ℝ)+2)^3*n*k) := by gcongr
    _ = _ := by ring
  have := le_of_mul_le_mul_right e (Nat.cast_pos.mpr hd)
  exact_mod_cast this

/-- A full box has at least L²/(C k) unsigned values as soon as
L² ≤ exp(k²) and d^r ≥ k^(5r+1). -/
theorem polylog_coefficient_box (r : ℕ) : ∃ C : ℕ, ∀ d L k : ℕ,
    0 < d → 0 < k → (L:ℝ)^2 ≤ Real.exp ((k:ℝ)^2) → k^(5*r+1) ≤ d^r →
    L^2 ≤ C*k*(((range L) ×ˢ (range L)).image fun z => z.1^2+d*z.2^2).card := by
  obtain ⟨B,budget⟩ := polylog_gap_budget r 1
  refine ⟨1+2*B,?_⟩
  intro d L k hd hk hsize scale
  by_cases hz : L=0
  · simp [hz]
  let T := (range L) ×ˢ (range L)
  let V := T.image fun z => z.1^2+d*z.2^2
  have tc : T.card=L^2 := by simp [T,pow_two]
  have e := gap_collision_bound d L hd T (fun z hz => (mem_range.mp (mem_product.mp hz).1).le)
  change T.card^2 ≤ V.card*(T.card+_) at e
  rw [tc] at e
  have bu := budget d L (L^2) k hd hk (by exact_mod_cast hsize) (by simp) scale
  have cost : L^2+2*(∑ h ∈ Ioc 0 (L^2/d), (d*h).divisors.card*h.divisors.card) ≤
      (1+2*B)*k*L^2 := by nlinarith only [bu,Nat.le_mul_of_pos_right (L^2) hk]
  apply Nat.le_of_mul_le_mul_right _ (show 0 < L^2 by positivity)
  calc
    _ = (L^2)^2 := by ring
    _ ≤ _ := e.trans (Nat.mul_le_mul_left _ cost)
    _ = _ := by dsimp [V,T]; ring

private theorem unsigned_subset_support (d : ℕ) (S A : Finset (ℤ × ℤ)) (p : ℤ × ℤ)
    (hp : p ∈ S) (sub : A ⊆ S) :
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    let T := A.image fun z => ((z.1-p.1).natAbs,(z.2-p.2).natAbs)
    A.card ≤ 4*T.card ∧ (T.image fun z => z.1^2+d*z.2^2).card ≤
      (S.offDiag.image fun xy => q (xy.1-xy.2)).card+1 := by
  classical
  intro q _
  let g := fun z : ℤ × ℤ => ((z.1-p.1).natAbs,(z.2-p.2).natAbs)
  let T := A.image g
  let f := fun z : ℕ × ℕ => z.1^2+d*z.2^2
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  let sign := fun z : ℤ × ℤ => (decide (p.1 ≤ z.1),decide (p.2 ≤ z.2))
  have nT : A.card ≤ 4*T.card := by
    have inj : Function.Injective (fun z => (g z,sign z)) := by
      intro x y he
      have h := congrArg Prod.fst he
      have hs := congrArg Prod.snd he
      simp [g,sign,Prod.mk.injEq] at h hs
      exact Prod.ext (by omega) (by omega)
    have sub : (A.image fun z => (g z,sign z)) ⊆ T ×ˢ (univ : Finset (Bool × Bool)) := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      exact mem_product.mpr ⟨mem_image_of_mem _ hx,mem_univ _⟩
    simpa [card_image_of_injective _ inj,Nat.mul_comm] using card_le_card sub
  have vals : (T.image f).card ≤ V.card+1 := by
    have sub : ((T.image f).image (Nat.cast : ℕ → ℤ)) ⊆ insert 0 V := by
      intro z hz
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hz
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hn
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
      by_cases h : x=p
      · simp [h,f,g]
      · exact mem_insert_of_mem (mem_image.mpr ⟨(x,p),mem_offDiag.mpr ⟨sub hx,hp,h⟩,by simp [f,g,q]⟩)
    exact (by simpa only [card_image_of_injective _ Nat.cast_injective] using card_le_card sub :
      (T.image f).card ≤ (insert 0 V).card).trans (card_insert_le ..)
  exact ⟨nT,vals⟩

private theorem unsigned_pin_support (d W : ℕ) (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ)
    (hp : p ∈ S) (width : ∀ z ∈ S, (z.1-p.1).natAbs ≤ W) :
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    ∃ T : Finset (ℕ × ℕ), S.card ≤ 4*T.card ∧ T.card ≤ S.card ∧
      (∀ z ∈ T, z.1 ≤ W) ∧
      (T.image fun z => z.1^2+d*z.2^2).card ≤ (S.offDiag.image fun xy => q (xy.1-xy.2)).card+1 := by
  classical
  intro q
  let g := fun z : ℤ × ℤ => ((z.1-p.1).natAbs,(z.2-p.2).natAbs)
  let T := S.image g
  obtain ⟨nT,vals⟩ := unsigned_subset_support d S S p hp (fun _ h => h)
  have cols : ∀ z ∈ T, z.1 ≤ W := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact width x hx
  exact ⟨T,nT,card_image_le,cols,vals⟩

/-- Uniform square-root logarithmic loss on horizontally dense strips in the
polylogarithmic coefficient regime. The vertical coordinates are unrestricted. -/
theorem polylog_coefficient_strip (r t : ℕ) : ∃ C : ℕ, ∀ (d W k : ℕ)
    (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ), 0 < d → 0 < k → p ∈ S →
    (S.card:ℝ) ≤ Real.exp ((k:ℝ)^2) → (∀ z ∈ S, (z.1-p.1).natAbs ≤ W) →
    W^2 ≤ t*S.card → k^(5*r+1) ≤ d^r →
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    S.card ≤ k*C*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨B,budget⟩ := polylog_gap_budget r t
  refine ⟨16*(1+2*B),?_⟩
  intro d W k S p hd hk hp hsize width dense scale q
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  obtain ⟨T,nT,upper,cols,vals⟩ := unsigned_pin_support d W S p hp width
  let f := fun z : ℕ × ℕ => z.1^2+d*z.2^2
  have he := gap_collision_bound d W hd T cols
  change T.card^2 ≤ (T.image f).card * _ at he
  have bu := budget d W S.card k hd hk hsize dense scale
  have cost : T.card+2*(∑ h ∈ Ioc 0 (W^2/d), (d*h).divisors.card*h.divisors.card) ≤
      S.card*k*(1+2*B) := by
    nlinarith only [upper,bu,Nat.le_mul_of_pos_right S.card hk]
  have fin : S.card*S.card ≤ S.card*(k*(16*(1+2*B))*(V.card+1)) := calc
    _ ≤ (4*T.card)^2 := by simpa only [pow_two] using Nat.pow_le_pow_left nT 2
    _ = 16*T.card^2 := by ring
    _ ≤ 16*((V.card+1)*(S.card*k*(1+2*B))) := Nat.mul_le_mul_left _ (he.trans (Nat.mul_le_mul vals cost))
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left fin (card_pos.mpr ⟨p,hp⟩)

/-- Charge each ordered collision with decreasing first coordinate to its
short-coordinate difference, short-coordinate sum, and long-coordinate difference. -/
private theorem short_factor_collision (d W : ℕ) (hd : 0 < d) (T : Finset (ℕ × ℕ))
    (width : ∀ z ∈ T, z.1 ≤ W) :
    let q := fun z : ℕ × ℕ => z.1^2+d*z.2^2
    T.card^2 ≤ (T.image q).card * (T.card+2*(∑ i ∈ Ioc 0 W, i.divisors.card)*
      (∑ b ∈ Ioc 0 (2*W), b.divisors.card)) := by
  classical
  intro q
  let F (ib : ℕ × ℕ) := (ib.1*ib.2).divisors.image fun j =>
    (((ib.2+ib.1)/2,(ib.1*ib.2/d/j-j)/2),((ib.2-ib.1)/2,(ib.1*ib.2/d/j+j)/2))
  let R := Ioc 0 W ×ˢ Ioc 0 (2*W)
  let B := R.biUnion F
  have low (z w : ℕ × ℕ) (hz : z ∈ T) (e : q w=q z) (hw : w.1<z.1) : (z,w) ∈ B := by
    let i := z.1-w.1
    let b := z.1+w.1
    let j := w.2-z.2
    have hv : z.2<w.2 := by
      by_contra! hn
      have h := Nat.mul_le_mul_left d (Nat.pow_le_pow_left hn 2)
      have h' := Nat.pow_lt_pow_left hw (by decide : 2 ≠ 0)
      dsimp [q] at e
      omega
    have ei := Nat.sub_add_cancel hw.le
    have ej := Nat.sub_add_cancel hv.le
    have fac : i*b=d*(j*(w.2+z.2)) := by
      dsimp [i,b,j,q] at *
      nlinarith only [e,congrArg (fun n : ℕ => n*(z.1+w.1)) ei,
        congrArg (fun n : ℕ => d*(n*(w.2+z.2))) ej]
    have hj : 0 < j := Nat.sub_pos_of_lt hv
    have div : i*b/d/j=w.2+z.2 := by
      rw [fac,Nat.mul_div_cancel_left _ hd,Nat.mul_div_cancel_left _ hj]
    have memj : j ∈ (i*b).divisors := by
      apply Nat.mem_divisors.mpr
      exact ⟨⟨d*(w.2+z.2),by rw [fac]; ring⟩,Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt hw) (by dsimp [b]; omega))⟩
    have wz := width z hz
    have ib : (i,b) ∈ R := mem_product.mpr ⟨mem_Ioc.mpr ⟨Nat.sub_pos_of_lt hw,by dsimp [i]; omega⟩,
      mem_Ioc.mpr ⟨by dsimp [b]; omega,by dsimp [b]; omega⟩⟩
    apply mem_biUnion.mpr
    refine ⟨(i,b),ib,mem_image.mpr ⟨j,memj,?_⟩⟩
    dsimp only
    rw [div]
    apply Prod.ext <;> apply Prod.ext <;> dsimp [i,b,j] <;> omega
  have cost : B.card ≤ (∑ i ∈ Ioc 0 W,i.divisors.card)*(∑ b ∈ Ioc 0 (2*W),b.divisors.card) := calc
    _ ≤ ∑ ib ∈ R, (ib.1*ib.2).divisors.card := card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le)
    _ ≤ ∑ ib ∈ R, ib.1.divisors.card*ib.2.divisors.card := sum_le_sum fun ib _ => divisor_product_le ..
    _ = _ := by simp [R,sum_product,sum_mul,mul_sum]; exact sum_comm
  simpa only [Nat.mul_assoc] using (collision_support_bound d hd T B (fun z w hz _ => low z w hz)).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left 2 cost) _))

open ArithmeticFunction in
private theorem divisor_first_mean (N : ℕ) :
    (↑(∑ i ∈ Ioc 0 N,i.divisors.card) : ℝ) ≤ N*(1+Real.log (N+1)) := by
  have e := zeta_sum_bound 1 N
  have z2 : ArithmeticFunction.zeta^2 = sigma 0 := by
    rw [pow_two,← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  simpa only [show 1+1=2 by decide,z2,sigma_zero_apply,pow_one] using e

/-- An unrestricted-height strip. The constant is independent of the positive
coefficient d. The width condition only involves the short-coordinate radius. -/
theorem narrow_strip (d W k t : ℕ) (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hd : 0 < d)
    (hk : 0 < k) (hp : p ∈ S) (width : ∀ z ∈ S, (z.1-p.1).natAbs ≤ W)
    (small : (W:ℝ)^2*(1+Real.log (2*W+1))^2 ≤ t*(k:ℝ)*S.card) :
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    S.card ≤ k*(16*(1+4*t))*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  intro q
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  obtain ⟨T,nT,upper,cols,vals⟩ := unsigned_pin_support d W S p hp width
  let f := fun z : ℕ × ℕ => z.1^2+d*z.2^2
  let a (N : ℕ) := ∑ i ∈ Ioc 0 N,i.divisors.card
  have he := short_factor_collision d W hd T cols
  change T.card^2 ≤ (T.image f).card*(T.card+2*a W*a (2*W)) at he
  let logW := 1+Real.log (2*(W:ℝ)+1)
  have lpos : 0 ≤ logW := by
    dsimp [logW]; linarith [Real.log_nonneg (show 1 ≤ 2*(W:ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) W])]
  have left : (a W:ℝ) ≤ W*logW := (divisor_first_mean W).trans (by
    dsimp [logW]; gcongr; nlinarith [Nat.cast_nonneg (α := ℝ) W])
  have right : (a (2*W):ℝ) ≤ (2*(W:ℝ))*logW := by simpa [logW,a] using divisor_first_mean (2*W)
  have budget : 2*a W*a (2*W) ≤ 4*t*k*S.card := by
    have e := mul_le_mul left right (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) lpos)
    change (W:ℝ)^2*logW^2 ≤ _ at small
    exact_mod_cast (show 2*(a W:ℝ)*a (2*W) ≤ 4*t*k*(S.card:ℝ) by nlinarith only [e,small])
  have cost : T.card+2*a W*a (2*W) ≤ S.card*k*(1+4*t) := by
    nlinarith only [budget,upper,Nat.le_mul_of_pos_right S.card hk]
  have fin : S.card*S.card ≤ S.card*(k*(16*(1+4*t))*(V.card+1)) := calc
    _ ≤ (4*T.card)^2 := by simpa only [pow_two] using Nat.pow_le_pow_left nT 2
    _ = 16*T.card^2 := by ring
    _ ≤ 16*((V.card+1)*(S.card*k*(1+4*t))) := Nat.mul_le_mul_left _ (he.trans (Nat.mul_le_mul vals cost))
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left fin (card_pos.mpr ⟨p,hp⟩)


/-- Dense H by L rectangles in the thin regime. Density and aspect ratio are
enough: the long-coordinate bound itself is unnecessary. -/
theorem elongated_rectangle (d H L k t : ℕ) (S : Finset (ℤ × ℤ)) (u : ℤ)
    (hd : 0 < d) (hk : 0 < k) (span : ∀ z ∈ S, u ≤ z.1 ∧ z.1 < u+H)
    (density : H*L ≤ t*S.card)
    (aspect : (H:ℝ)*(1+Real.log (2*H+1))^2 ≤ k*(L:ℝ)) :
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    S.card ≤ k*(16*(1+4*t))*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  intro q
  obtain eq | ⟨p,hp⟩ := S.eq_empty_or_nonempty
  · simp [eq]
  apply narrow_strip d H k t S p hd hk hp
  · intro z hz
    obtain ⟨hp₁,hp₂⟩ := span p hp
    obtain ⟨hz₁,hz₂⟩ := span z hz
    omega
  · have de : (H:ℝ)*L ≤ t*(S.card:ℝ) := by exact_mod_cast density
    nlinarith only [mul_le_mul_of_nonneg_left aspect (Nat.cast_nonneg H),
      mul_le_mul_of_nonneg_left de (Nat.cast_nonneg k)]


/-- The four-factor parametrization also appears in Cilleruelo, Sharir and Sheffer,
Lemma 2.3 of arXiv:1306.0242. Here the two differences are divided by their gcd. The sums are
multiples of the opposite reduced differences by a common factor s. -/
private theorem primitive_collision {x y u v : ℕ} (hx : u < x)
    (e : u^2+v^2=x^2+y^2) :
    ∃ a b g s : ℕ, 0<a ∧ 0<b ∧ 0<g ∧ 0<s ∧
      x-u=a*g ∧ v-y=b*g ∧ x+u=b*s ∧ v+y=a*s := by
  have hv : y<v := by
    by_contra! hn
    have h₁ := Nat.pow_le_pow_left hn 2
    have h₂ := Nat.pow_lt_pow_left hx (by decide : 2 ≠ 0)
    omega
  have eq : (x-u)*(x+u)=(v-y)*(v+y) := by
    nlinarith only [e,congrArg (fun n : ℕ => n*(x+u)) (Nat.sub_add_cancel hx.le),
      congrArg (fun n : ℕ => n*(v+y)) (Nat.sub_add_cancel hv.le)]
  let g := (x-u).gcd (v-y)
  obtain ⟨a,b,c,hi,hj⟩ := Nat.exists_coprime (x-u) (v-y)
  change x-u=a*g at hi
  change v-y=b*g at hj
  have ag : 0<a*g := hi ▸ Nat.sub_pos_of_lt hx
  have bg : 0<b*g := hj ▸ Nat.sub_pos_of_lt hv
  have ha := Nat.pos_of_ne_zero (left_ne_zero_of_mul ag.ne')
  have hg := Nat.pos_of_ne_zero (right_ne_zero_of_mul ag.ne')
  have hb := Nat.pos_of_ne_zero (left_ne_zero_of_mul bg.ne')
  have rel : a*(x+u)=b*(v+y) := by
    apply Nat.eq_of_mul_eq_mul_left hg
    rw [hi,hj] at eq
    nlinarith only [eq]
  have dvd := c.dvd_of_dvd_mul_left (show a ∣ b*(v+y) from ⟨_,rel.symm⟩)
  obtain ⟨s,hs⟩ := dvd
  have hh : x+u=b*s := by
    apply Nat.eq_of_mul_eq_mul_left ha
    rw [rel,hs]; ring
  exact ⟨a,b,g,s,ha,hb,hg,by by_contra! h; simp [show s=0 by omega] at hs; omega,hi,hj,hh,hs⟩

/-- When all long coordinates lie between D/2 and D, counting equal norms
requires just one harmonic sum in the short-coordinate radius. -/
private theorem far_collision (W D : ℕ) (T : Finset (ℕ × ℕ))
    (bounds : ∀ z ∈ T, z.1 ≤ W ∧ D ≤ 2*z.2 ∧ z.2 ≤ D) :
    let q := fun z : ℕ × ℕ => z.1^2+1*z.2^2
    T.card^2 ≤ (T.image q).card*(T.card+8*W*(∑ a ∈ Ioc 0 W,W/a)) := by
  classical
  intro q
  let R a := Ioc 0 (W/a) ×ˢ (Ioc 0 (2*W*a/D) ×ˢ Ioc 0 (2*D/a))
  let F a := (R a).image fun z =>
    let g := z.1
    let b := z.2.1
    let s := z.2.2
    (((b*s+a*g)/2,(a*s-b*g)/2),((b*s-a*g)/2,(a*s+b*g)/2))
  let B := (Ioc 0 W).biUnion F
  have low (z w : ℕ × ℕ) (hz : z∈T) (hw' : w∈T) (e : q w=q z) (hw : w.1<z.1) : (z,w) ∈ B := by
    obtain ⟨zw,zd,zD⟩ := bounds z hz
    obtain ⟨ww,wd,wD⟩ := bounds w hw'
    obtain ⟨a,b,g,s,ha,hb,hg,hs,hi,hj,hu,hv⟩ := primitive_collision hw (by simpa [q] using e)
    have hlong : D ≤ w.2+z.2 := by omega
    have posSum := Nat.mul_pos ha hs
    have posDiff := Nat.mul_pos hb hg
    have hD : 0<D := by omega
    have hshort : a*g ≤ W := by omega
    have h1 : a ≤ W := (Nat.le_mul_of_pos_right _ hg).trans hshort
    have h2 : g ≤ W/a := (Nat.le_div_iff_mul_le ha).mpr (by simpa [mul_comm] using hshort)
    have h3 : b ≤ 2*W*a/D := (Nat.le_div_iff_mul_le hD).mpr (by
      calc
        b*D ≤ b*(w.2+z.2) := Nat.mul_le_mul_left _ hlong
        _ = (z.1+w.1)*a := by rw [hu,hv]; ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega))
    have h4 : s ≤ 2*D/a := (Nat.le_div_iff_mul_le ha).mpr (by rw [Nat.mul_comm,← hv]; omega)
    refine mem_biUnion.mpr ⟨a,mem_Ioc.mpr ⟨ha,h1⟩,mem_image.mpr ⟨(g,b,s),
      mem_product.mpr ⟨mem_Ioc.mpr ⟨hg,h2⟩,mem_product.mpr ⟨mem_Ioc.mpr ⟨hb,h3⟩,mem_Ioc.mpr ⟨hs,h4⟩⟩⟩,?_⟩⟩
    dsimp only
    rw [← hu,← hv,← hi,← hj]
    apply Prod.ext <;> apply Prod.ext <;> dsimp <;> omega
  have cost : B.card ≤ 4*W*∑ a ∈ Ioc 0 W,W/a := by
    rw [mul_sum]
    apply card_biUnion_le.trans (sum_le_sum ?_)
    intro a h
    apply card_image_le.trans
    simp only [R,card_product,Nat.card_Ioc,Nat.sub_zero]
    have ha := (mem_Ioc.mp h).1
    have pair : (2*W*a/D)*(2*D/a) ≤ 4*W := by
      by_cases hD : D=0
      · simp [hD]
      apply Nat.le_of_mul_le_mul_right (c := D*a) _ (Nat.mul_pos (Nat.pos_of_ne_zero hD) ha)
      calc
        _ = ((2*W*a/D)*D)*((2*D/a)*a) := by ring
        _ ≤ (2*W*a)*(2*D) := Nat.mul_le_mul (Nat.div_mul_le_self ..) (Nat.div_mul_le_self ..)
        _ = _ := by ring
    simpa only [Nat.mul_comm (4*W)] using Nat.mul_le_mul_left (W/a) pair
  apply (collision_support_bound 1 (by decide) T B low).trans
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left ((Nat.mul_le_mul_left 2 cost).trans_eq (by ring)) _)

private theorem floor_sum_mean (W : ℕ) :
    (↑(∑ a ∈ Ioc 0 W,W/a):ℝ) ≤ W*(1+Real.log ((W:ℝ)+1)) := by
  have h := zeta_sum_bound 1 W
  rw [pow_succ',ArithmeticFunction.sum_Ioc_mul_eq_sum_sum] at h
  simp only [pow_one,ArithmeticFunction.sum_Ioc_zeta] at h
  have eq : (∑ a ∈ Ioc 0 W,ArithmeticFunction.zeta a*(W/a)) = ∑ a ∈ Ioc 0 W,W/a :=
    sum_congr rfl fun a ha => by rw [ArithmeticFunction.zeta_apply_ne (mem_Ioc.mp ha).1.ne',one_mul]
  rwa [eq] at h

/-- Choose one of the two extreme heights as the pin. At least half the set
has vertical displacement between half the diameter and the diameter. -/
private theorem far_half (S : Finset (ℤ × ℤ)) (hne : S.Nonempty) :
    ∃ p ∈ S, ∃ A ⊆ S, ∃ D : ℕ, S.card ≤ 2*A.card ∧
      ∀ z ∈ A, D ≤ 2*(z.2-p.2).natAbs ∧ (z.2-p.2).natAbs ≤ D := by
  classical
  obtain ⟨lo,hlo,minimal⟩ := S.exists_min_image Prod.snd hne
  obtain ⟨hi,hhi,maximal⟩ := S.exists_max_image Prod.snd hne
  let D := (hi.2-lo.2).natAbs
  let targets (p : ℤ × ℤ) := S.filter fun z => D ≤ 2*(z.2-p.2).natAbs
  have dis (z : ℤ × ℤ) (hz : z ∈ S) :
      (z.2-lo.2).natAbs+(z.2-hi.2).natAbs=D := by
    have a := minimal z hz
    have b := maximal z hz
    dsimp [D]; omega
  have cover : S ⊆ targets lo ∪ targets hi := by
    intro z hz
    have := dis z hz
    by_cases h : D ≤ 2*(z.2-lo.2).natAbs
    · exact mem_union_left _ (mem_filter.mpr ⟨hz,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hz,by omega⟩)
  have count := (card_le_card cover).trans (card_union_le ..)
  by_cases h : S.card ≤ 2*(targets lo).card
  · refine ⟨lo,hlo,targets lo,filter_subset ..,D,h,?_⟩
    intro z hz
    obtain ⟨hs,hg⟩ := mem_filter.mp hz
    exact ⟨hg,by have := dis z hs; omega⟩
  · refine ⟨hi,hhi,targets hi,filter_subset ..,D,by omega,?_⟩
    intro z hz
    obtain ⟨hs,hg⟩ := mem_filter.mp hz
    exact ⟨hg,by have := dis z hs; omega⟩

/-- Single-logarithm width estimate for squared Euclidean distances on an
integer strip. The vertical diameter may be arbitrary, including zero. -/
theorem euclidean_strip (H k t : ℕ) (S : Finset (ℤ × ℤ)) (u : ℤ)
    (hk : 0 < k) (span : ∀ z ∈ S, u ≤ z.1 ∧ z.1 < u+H)
    (small : (H:ℝ)^2*(1+Real.log ((H:ℝ)+1)) ≤ t*(k:ℝ)*S.card) :
    let q := fun z : ℤ × ℤ => z.1^2+z.2^2
    S.card ≤ k*(64*(1+8*t))*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  intro q
  obtain empty | ne := S.eq_empty_or_nonempty
  · simp [empty]
  obtain ⟨p,hp,A,sub,D,half,far⟩ := far_half S ne
  let g (z : ℤ × ℤ) := ((z.1-p.1).natAbs,(z.2-p.2).natAbs)
  let T := A.image g
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  let f := fun z : ℕ × ℕ => z.1^2+1*z.2^2
  obtain ⟨signs,vals⟩ := unsigned_subset_support 1 S A p hp sub
  change A.card ≤ 4*T.card at signs
  have vs : (T.image f).card ≤ V.card+1 := by simpa [T,g,f,V,q] using vals
  have he := far_collision H D T (by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    have h₁ := span w (sub hw)
    have h₂ := span p hp
    exact ⟨by dsimp [g]; omega,far w hw⟩)
  change T.card^2 ≤ (T.image f).card*(T.card+8*H*(∑ a ∈ Ioc 0 H,H/a)) at he
  have cost : 8*H*(∑ a ∈ Ioc 0 H,H/a) ≤ 8*t*k*S.card := by
    have h := mul_le_mul_of_nonneg_left (floor_sum_mean H) (Nat.cast_nonneg H : 0 ≤ (H:ℝ))
    exact_mod_cast (show 8*(H:ℝ)*(↑(∑ a ∈ Ioc 0 H,H/a):ℝ) ≤ 8*t*k*(S.card:ℝ) by nlinarith only [h,small])
  have nT : S.card ≤ 8*T.card := by omega
  have upper : T.card ≤ S.card := card_image_le.trans (card_le_card sub)
  have full : T.card+8*H*(∑ a ∈ Ioc 0 H,H/a) ≤ S.card*k*(1+8*t) := by
    nlinarith only [cost,upper,Nat.le_mul_of_pos_right S.card hk]
  have fin : S.card*S.card ≤ S.card*(k*(64*(1+8*t))*(V.card+1)) := calc
    _ ≤ (8*T.card)^2 := by simpa only [pow_two] using Nat.pow_le_pow_left nT 2
    _ = 64*T.card^2 := by ring
    _ ≤ 64*((V.card+1)*(S.card*k*(1+8*t))) := Nat.mul_le_mul_left _ (he.trans (Nat.mul_le_mul vs full))
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left fin (card_pos.mpr ne)

/-- A fixed-density rectangle needs only H(1+log(H+1)) ≤ kL. -/
theorem intermediate_rectangle (H L k t : ℕ) (S : Finset (ℤ × ℤ)) (u : ℤ)
    (hk : 0 < k) (span : ∀ z ∈ S, u ≤ z.1 ∧ z.1 < u+H)
    (density : H*L ≤ t*S.card) (aspect : (H:ℝ)*(1+Real.log ((H:ℝ)+1)) ≤ k*(L:ℝ)) :
    let q := fun z : ℤ × ℤ => z.1^2+z.2^2
    S.card ≤ k*(64*(1+8*t))*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  apply euclidean_strip H k t S u hk span
  have de : (H:ℝ)*L ≤ t*(S.card:ℝ) := by exact_mod_cast density
  nlinarith only [mul_le_mul_of_nonneg_left aspect (Nat.cast_nonneg H),
    mul_le_mul_of_nonneg_left de (Nat.cast_nonneg k)]

/-- Linear distinct-value bound with a constant independent of d and S.
Only the horizontal span is restricted; the selected heights can be arbitrary. -/
theorem polynomial_coefficient_strip (r t : ℕ) : ∃ B : ℕ,
    ∀ (d W : ℕ) (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ), 0 < d → p ∈ S →
    (∀ z ∈ S, (z.1-p.1).natAbs ≤ W) → W^2 ≤ d^r → W^2 ≤ t*S.card →
    let q := fun z : ℤ × ℤ => z.1^2+(d:ℤ)*z.2^2
    S.card ≤ B*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨D₀,hlarge⟩ := polynomial_coefficient_gaps r (8*(t+1))
  refine ⟨max 8 (4*(D₀^r+1)),?_⟩
  intro d W S p hd hp width scale dense q
  obtain ⟨T,nT,upper,cols,vals⟩ := unsigned_pin_support d W S p hp width
  let f := fun z : ℕ × ℕ => z.1^2+d*z.2^2
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  by_cases big : D₀ ≤ d
  · have e := hlarge d W big hd scale T cols
    change 8*(t+1)*T.card ≤ 8*(t+1)*(T.image f).card+W^2 at e
    have ey := Nat.mul_le_mul_left (8*(t+1)) vals
    have ex := Nat.mul_le_mul_left (t+1) nT
    have hl : (t+1)*S.card ≤ (t+1)*(8*(V.card+1)) := by nlinarith
    exact (Nat.le_of_mul_le_mul_left hl (by omega)).trans
      (Nat.mul_le_mul_right _ (le_max_left ..))
  · have hW : W ≤ D₀^r := (show W ≤ W^2 by nlinarith only [Nat.le_mul_self W]).trans
        (scale.trans (Nat.pow_le_pow_left (by omega) r))
    have small : T.card ≤ (W+1)*(T.image f).card := by
      have inj : Function.Injective (fun z : ℕ × ℕ => (z.1,f z)) := by
        intro x y he
        obtain ⟨ex,eqv⟩ := Prod.mk.inj he
        apply Prod.ext ex
        change x.1^2+d*x.2^2=y.1^2+d*y.2^2 at eqv
        rw [ex] at eqv
        exact Nat.pow_left_injective (by decide : 2 ≠ 0)
          (Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel eqv))
      have sub : (T.image fun z => (z.1,f z)) ⊆ range (W+1) ×ˢ T.image f := by
        intro z hz
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
        exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (cols x hx)),mem_image_of_mem _ hx⟩
      simpa [card_image_of_injective _ inj] using card_le_card sub
    calc
      _ ≤ 4*((W+1)*(T.image f).card) := nT.trans (Nat.mul_le_mul_left _ small)
      _ ≤ 4*((D₀^r+1)*(V.card+1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) vals)
      _ = 4*(D₀^r+1)*(V.card+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (le_max_right ..)

theorem rectangle_patch_multiple (A : Finset (ℕ × ℕ)) {H L K : ℕ} (v : (ℕ × ℕ))
    (hA : A ⊆ (range H ×ˢ range L)) (hdense : (2*H)*(2*L) < (K+1)*#A)
    (hx : K*v.1 ≤ H) (hy : K*v.2 ≤ L) :
    ∃ a ∈ A, ∃ j, 0 < j ∧ j ≤ K ∧ (a.1+j*v.1,a.2+j*v.2) ∈ A := by
  let shift (a v : ℕ × ℕ) (j : ℕ) := (a.1+j*v.1,a.2+j*v.2)
  let S := range (K+1) ×ˢ A
  let f (z : ℕ × (ℕ × ℕ)) := shift z.2 v z.1
  have hcard : #((range (2*H) ×ˢ range (2*L))) < #S := by simpa [S] using hdense
  have hmap : Set.MapsTo f S ((range (2*H) ×ˢ range (2*L) : Finset _) : Set _) := by
    rintro ⟨j,a⟩ hz
    obtain ⟨hj,ha⟩ := mem_product.mp hz
    have hj' : j ≤ K := Nat.le_of_lt_succ (mem_range.mp hj)
    obtain ⟨hax,hay⟩ := mem_product.mp (hA ha)
    have hax : a.1 < H := mem_range.mp hax
    have hay : a.2 < L := mem_range.mp hay
    have h₁ := (Nat.mul_le_mul_right v.1 hj').trans hx
    have h₂ := (Nat.mul_le_mul_right v.2 hj').trans hy
    apply mem_product.mpr
    simp only [mem_range]
    change a.1 + j*v.1 < 2*H ∧ a.2 + j*v.2 < 2*L
    omega
  obtain ⟨⟨i,a⟩,hia,⟨j,b⟩,hjb,hne,heq⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hcard hmap
  obtain ⟨hi,ha⟩ := mem_product.mp hia
  obtain ⟨hj,hb⟩ := mem_product.mp hjb
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  have he₁ : a.1 + i*v.1 = b.1 + j*v.1 := congrArg Prod.fst heq
  have he₂ : a.2 + i*v.2 = b.2 + j*v.2 := congrArg Prod.snd heq
  have step (p q : (ℕ × ℕ)) (u w : ℕ) (huw : u ≤ w)
      (h₁ : p.1 + u*v.1 = q.1 + w*v.1) (h₂ : p.2 + u*v.2 = q.2 + w*v.2) :
      shift q v (w-u) = p := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le huw
    simp only [Nat.add_sub_cancel_left, Nat.add_mul] at *
    apply Prod.ext <;> dsimp [shift] <;> omega
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ⟨b,hb,j-i,by omega,by omega, show shift b v (j-i) ∈ A from (step a b i j hij.le he₁ he₂) ▸ ha⟩
  · exact False.elim (hne (Prod.ext rfl (Prod.ext (Nat.add_right_cancel he₁) (Nat.add_right_cancel he₂))))
  · exact ⟨a,ha,i-j,by omega,by omega, show shift a v (i-j) ∈ A from (step b a j i hji.le he₁.symm he₂.symm) ▸ hb⟩

theorem square_patch_multiple (A : Finset (ℕ × ℕ)) {L K : ℕ} (v : (ℕ × ℕ))
    (hA : A ⊆ (range L ×ˢ range L)) (hdense : (2*L)^2 < (K+1)*#A)
    (hx : K*v.1 ≤ L) (hy : K*v.2 ≤ L) :
    ∃ a ∈ A, ∃ j, 0 < j ∧ j ≤ K ∧ (a.1+j*v.1,a.2+j*v.2) ∈ A :=
  rectangle_patch_multiple A v hA (by simpa only [pow_two] using hdense) hx hy

/-- The nonzero norm values of the smaller full rectangle are controlled by the
distances of any dense patch. No aspect-ratio hypothesis is needed. -/
theorem rectangle_spectrum_transfer (K H L : ℕ) (S : Finset (ℤ × ℤ)) (A : Finset (ℕ × ℕ))
    (p : ℤ × ℤ) (s : ℤ) (hs : s ≠ 0) (box : A ⊆ range H ×ˢ range L)
    (en : (2*H)*(2*L) < (K+1)*A.card)
    (sub : ∀ z ∈ A, (p.1+s*z.1,p.2+s*z.2) ∈ S) :
    let B := ((range (H/K+1)) ×ˢ range (L/K+1)).image fun z => z.1^2+z.2^2
    let q := fun z : ℤ × ℤ => z.1^2+z.2^2
    (B.erase 0).card ≤ K*(S.offDiag.image fun xy => q (xy.1-xy.2)).card := by
    classical
    intro B q
    let f (z : ℕ × ℕ) : ℤ × ℤ := (p.1+s*z.1,p.2+s*z.2)
    let V := S.offDiag.image fun xy => q (xy.1-xy.2)
    let hfun (zn : ℕ × ℤ) := (zn.2 / ((s*(zn.1:ℤ))^2)).toNat
    have inc : B.erase 0 ⊆ ((Icc 1 K ×ˢ V).image hfun) := by
      intro n hn
      obtain ⟨hn0,hnB⟩ := mem_erase.mp hn
      obtain ⟨⟨a,b⟩,hab,eqn⟩ := mem_image.mp hnB
      obtain ⟨ha,hb⟩ := mem_product.mp hab
      have hpos := Nat.pos_of_ne_zero hn0
      change a^2+b^2=n at eqn
      have ax : K*a ≤ H := (Nat.mul_le_mul_left K (Nat.le_of_lt_succ (mem_range.mp ha))).trans (Nat.mul_div_le ..)
      have by' : K*b ≤ L := (Nat.mul_le_mul_left K (Nat.le_of_lt_succ (mem_range.mp hb))).trans (Nat.mul_div_le ..)
      obtain ⟨u,hu,j,hj,hjK,hv⟩ := rectangle_patch_multiple A (a,b) box en ax by'
      let v : ℕ × ℕ := (u.1+j*a,u.2+j*b)
      have val : q (f v-f u)=(n:ℤ)*(s*(j:ℤ))^2 := by
        dsimp [q,f,v]; rw [← eqn]; push_cast; ring
      have den : (s*(j:ℤ))^2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hs (by exact_mod_cast hj.ne'))
      have ne : f v ≠ f u := by
        intro e
        rw [e,sub_self] at val
        exact (mul_ne_zero (by exact_mod_cast hpos.ne' : (n:ℤ) ≠ 0) den) (by simpa [q] using val.symm)
      have hval : q (f v-f u) ∈ V := mem_image.mpr ⟨(f v,f u),mem_offDiag.mpr ⟨sub v hv,sub u hu,ne⟩,rfl⟩
      exact mem_image.mpr ⟨(j,_),mem_product.mpr ⟨mem_Icc.mpr ⟨hj,hjK⟩,hval⟩,by
        change ((q (f v-f u))/((s*(j:ℤ))^2)).toNat = n
        rw [val,Int.mul_ediv_cancel _ den,Int.toNat_natCast]⟩
    simpa using (card_le_card inc).trans card_image_le

/-- Uniform passage from arithmetic coverage of a smaller rectangle to a dense patch
containing at least half the points. X is truncated at the actual cardinality. -/
theorem rectangle_coverage_bound (lr : H3) (t c : ℕ) : ∃ G : ℕ, ∀ (H L k : ℕ)
    (S : Finset (ℤ × ℤ)) (A : Finset (ℕ × ℕ)) (p : ℤ × ℤ) (s : ℤ),
    0 < k → (S.card:ℝ) ≤ Real.exp ((k:ℝ)^2) → s ≠ 0 →
    A ⊆ range H ×ˢ range L → H*L ≤ t*A.card →
    (∀ z ∈ A, (p.1+s*z.1,p.2+s*z.2) ∈ S) → S.card ≤ 2*A.card →
    let K := 4*(t+1)
    let P := H/K+1
    let Q := L/K+1
    let B := (range P ×ˢ range Q).image fun z => z.1^2+z.2^2
    let X := min S.card (P*Q)
    Set.ncard {n : ℕ | n < X ∧ ∃ a b : ℕ, n=a^2+b^2} ≤ c*(B.card+1) →
    let q := fun z : ℤ × ℤ => z.1^2+z.2^2
    S.card ≤ k*G*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨C,arith⟩ := lr
  let K := 4*(t+1)
  have hK : 0 < K := by dsimp [K]; omega
  refine ⟨2*K^2*C*(c+1)*(K+2),?_⟩
  intro H L k S A p s hk cap hs box dens sub half _ P Q B X coverage q
  let V := S.offDiag.image fun xy => q (xy.1-xy.2)
  by_cases empty : A.card=0
  · have hh : S.card=0 := by omega
    simp [hh]
  have en : (2*H)*(2*L)<(K+1)*A.card := by
    dsimp [K]; nlinarith only [dens,Nat.pos_of_ne_zero empty]
  have tr := rectangle_spectrum_transfer K H L S A p s hs box en sub
  change (B.erase 0).card ≤ K*V.card at tr
  have bc : B.card+1 ≤ (K+2)*(V.card+1) := by
    have h' := card_le_card (show B ⊆ insert 0 (B.erase 0) from fun z hz => by
      by_cases z0 : z=0 <;> simp_all)
    have h'' := card_insert_le 0 (B.erase 0)
    nlinarith only [h',h'',tr,Nat.zero_le V.card]
  let U := (range X).filter fun n => 0<n ∧ ∃ a b : ℕ, n=a^2+b^2
  have hx : (X:ℝ) ≤ Real.exp ((k:ℝ)^2) := (by exact_mod_cast min_le_left S.card (P*Q) : (X:ℝ) ≤ S.card).trans cap
  have hr := arith X k hk hx U (by intro n; simp [U,and_left_comm])
  have coverU : U.card ≤ c*(B.card+1) := by
    let Z := (range X).filter fun n => ∃ a b : ℕ, n=a^2+b^2
    have coe : (Z : Set ℕ) = {n : ℕ | n < X ∧ ∃ a b : ℕ, n=a^2+b^2} := by ext n; simp [Z]
    rw [← coe, Set.ncard_coe_finset] at coverage
    exact (card_le_card (show U ⊆ Z from fun n hn => mem_filter.mpr ⟨(mem_filter.mp hn).1,(mem_filter.mp hn).2.2⟩)).trans coverage
  have upper : S.card ≤ 2*K^2*X := by
    dsimp only [X]
    rcases le_total S.card (P*Q) with h|h
    · rw [min_eq_left h]; exact Nat.le_mul_of_pos_left _ (by positivity)
    · rw [min_eq_right h]
      have ac : A.card ≤ H*L := by simpa using card_le_card box
      have hhl := Nat.mul_le_mul (Nat.lt_mul_div_succ H hK).le (Nat.lt_mul_div_succ L hK).le
      change H*L ≤ (K*P)*(K*Q) at hhl
      calc
        _ ≤ 2*(H*L) := half.trans (Nat.mul_le_mul_left _ ac)
        _ ≤ 2*((K*P)*(K*Q)) := Nat.mul_le_mul_left _ hhl
        _ = _ := by ring
  have ub : U.card+1 ≤ (c+1)*((K+2)*(V.card+1)) := by
    have h := coverU.trans (Nat.mul_le_mul_left _ bc)
    nlinarith only [h,Nat.zero_le K,Nat.zero_le V.card,Nat.zero_le (K*V.card)]
  exact upper.trans ((Nat.mul_le_mul_left _ (hr.trans (Nat.mul_le_mul_left _ ub))).trans_eq (by ring))

/-- An occupied positive-density square patch with arbitrary nonzero integer
scale controls all the points when it contains at least half the configuration. -/
theorem square_patch_bound (lr : H3) (t : ℕ) : ∃ G : ℕ, ∀ (L k : ℕ)
    (S : Finset (ℤ × ℤ)) (A : Finset (ℕ × ℕ)) (p : ℤ × ℤ) (s : ℤ),
    0 < k → (S.card:ℝ) ≤ Real.exp ((k:ℝ)^2) → s ≠ 0 →
    A ⊆ range L ×ˢ range L → L^2 ≤ t*A.card →
    (∀ z ∈ A, (p.1+s*z.1,p.2+s*z.2) ∈ S) → S.card ≤ 2*A.card →
    let q := fun z : ℤ × ℤ => z.1^2+z.2^2
    S.card ≤ k*G*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨G,applyRect⟩ := rectangle_coverage_bound lr t (t+1)
  refine ⟨G,?_⟩
  intro L k S A p s hk cap hs box dens sub half q
  apply applyRect L L k S A p s hk cap hs box (by simpa only [pow_two] using dens) sub half
  
  let w := L/(4*(t+1))+1
  let B := (range w ×ˢ range w).image fun z => z.1^2+z.2^2
  have incl : {n : ℕ | n < min S.card (w*w) ∧ ∃ a b : ℕ, n=a^2+b^2} ⊆ (B : Set ℕ) := by
    rintro n ⟨hn,a,b,rfl⟩
    have hlt := lt_of_lt_of_le hn (min_le_right ..)
    have bound (z : ℕ) (hz : z^2 ≤ a^2+b^2) : z<w := by
      by_contra! h
      have := Nat.pow_le_pow_left h 2
      rw [← pow_two] at hlt
      omega
    exact mem_image.mpr ⟨(a,b),mem_product.mpr ⟨mem_range.mpr (bound a (by omega)),mem_range.mpr (bound b (by omega))⟩,rfl⟩
  have h := Set.ncard_le_ncard incl (finite_toSet B)
  rw [Set.ncard_coe_finset] at h
  exact h.trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega)))

/-- Put the short-coordinate bound at a common cutoff X. The factor four
absorbs the change from log(n+1) to log(X+1), including n below sqrt X. -/
private theorem small_coordinate_cutoff {a n X : ℕ} (hn : n<X)
    (h : 4*(a:ℝ)^2*(1+Real.sqrt (Real.log ((n:ℝ)+1))) ≤ n) :
    (a:ℝ)^2*(1+Real.sqrt (Real.log ((X:ℝ)+1))) < X := by
  let r (m : ℕ) := Real.sqrt (Real.log ((m:ℝ)+1))
  have rr (m : ℕ) : (r m)^2=Real.log ((m:ℝ)+1) := Real.sq_sqrt (Real.log_nonneg (by simp))
  have rp (m : ℕ) : 0 ≤ r m := Real.sqrt_nonneg _
  change 4*(a:ℝ)^2*(1+r n) ≤ n at h
  change (a:ℝ)^2*(1+r X) < X
  have hnX : (n:ℝ)<X := by exact_mod_cast hn
  by_cases close : (X:ℝ)+1 ≤ ((n:ℝ)+1)^2
  · have l := Real.log_le_log (by positivity) close
    rw [Real.log_pow] at l
    have hroot : r X ≤ 2*r n := by
      apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity)
      norm_num at l
      nlinarith only [l,rr X,rr n,sq_nonneg (r n)]
    nlinarith only [h,hnX,mul_le_mul_of_nonneg_left hroot (sq_nonneg (a:ℝ)),sq_nonneg (a:ℝ),
      mul_nonneg (sq_nonneg (a:ℝ)) (rp n)]
  · have l := Real.log_le_sub_one_of_pos (show 0<(X:ℝ)+1 by positivity)
    let s := Real.sqrt X
    have ss : s^2=(X:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    have sp : 0 ≤ s := Real.sqrt_nonneg _
    have one : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    have s1 : 1 ≤ s := by nlinarith only [one,ss,sp]
    have ns : (n:ℝ) ≤ s := by nlinarith only [close,ss,sp,Nat.cast_nonneg (α := ℝ) n]
    have rs : r X ≤ s := by nlinarith only [rr X,ss,l,rp X,sp]
    have aa : 4*(a:ℝ)^2 ≤ n := by nlinarith only [h,mul_nonneg (sq_nonneg (a:ℝ)) (rp n)]
    calc
      _ ≤ (a:ℝ)^2*(2*s) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ < _ := by nlinarith only [mul_le_mul_of_nonneg_right (aa.trans ns) sp,ss,one]

/-- A one-dimensional small-coordinate estimate, implied classically by the
corollary to Theorem 2 of Erdős and Hall (Discrete Mathematics 200, 1999, pp. 87–94), suffices for dense integer rectangles
of every aspect ratio. The analytic input is explicit. -/
theorem all_dense_rectangles_of_small_coordinate (lr : H3) (c t : ℕ)
    (native : ∃ N : ℕ, ∀ X ≥ N, Set.ncard {n : ℕ | n<X ∧ ∃ a b : ℕ, n=a^2+b^2} ≤
      c*(Set.ncard {n : ℕ | n<X ∧ ∃ a b : ℕ, n=a^2+b^2 ∧
          4*(a:ℝ)^2*(1+Real.sqrt (Real.log ((n:ℝ)+1))) ≤ n}+1)) :
    ∃ G : ℕ, ∀ (H L k : ℕ) (A : Finset (ℕ × ℕ)),
      0 < k → (A.card:ℝ) ≤ Real.exp ((k:ℝ)^2) → H ≤ L →
      A ⊆ range H ×ˢ range L → H*L ≤ t*A.card →
      let S := A.image fun z => ((z.1:ℤ),(z.2:ℤ))
      let q := fun z : ℤ × ℤ => z.1^2+z.2^2
      A.card ≤ k*G*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨N,native⟩ := native
  let C := max c N
  have arith (X : ℕ) : Set.ncard {n : ℕ | n<X ∧ ∃ a b : ℕ, n=a^2+b^2} ≤
      C*(Set.ncard {n : ℕ | n<X ∧ ∃ a b : ℕ, n=a^2+b^2 ∧
          (a:ℝ)^2*(1+Real.sqrt (Real.log ((X:ℝ)+1))) < X}+1) := by
    by_cases big : N ≤ X
    · apply (native X big).trans
      apply Nat.mul_le_mul (le_max_left ..) (Nat.add_le_add_right _ 1)
      apply Set.ncard_le_ncard
      · rintro n ⟨hn,a,b,e,h⟩
        exact ⟨hn,a,b,e,small_coordinate_cutoff hn h⟩
      · apply (finite_toSet (range X)).subset
        exact fun n hn => mem_range.mpr hn.1
    · have incl : {n : ℕ | n<X ∧ ∃ a b : ℕ, n=a^2+b^2} ⊆ (range X : Set ℕ) :=
        fun n hn => mem_range.mpr hn.1
      have u := Set.ncard_le_ncard incl (finite_toSet _)
      rw [Set.ncard_coe_finset,card_range] at u
      exact (u.trans (by dsimp [C]; omega : X ≤ C)).trans (Nat.le_mul_of_pos_right _ (by omega))
  let K := 4*(t+1)
  have hK : 0<K := by dsimp [K]; omega
  obtain ⟨G,rect⟩ := rectangle_coverage_bound lr t C
  let T := K^2*(K+4)
  refine ⟨max G (64*(1+8*T)),?_⟩
  intro H L k A hk cap hHL box dense S q
  have inj : Function.Injective (fun z : ℕ × ℕ => ((z.1:ℤ),(z.2:ℤ))) := by
    rintro ⟨a,b⟩ ⟨i,j⟩ e
    simpa using e
  have card : S.card=A.card := card_image_of_injective A inj
  let P := H/K+1
  let Q := L/K+1
  let X := min S.card (P*Q)
  let R := Real.sqrt (Real.log ((X:ℝ)+1))
  let B := (range P ×ˢ range Q).image fun z => z.1^2+z.2^2
  have xN : X ≤ S.card := min_le_left .. 
  have xPQ : X ≤ P*Q := min_le_right .. 
  have r0 : 0 ≤ R := Real.sqrt_nonneg _
  have fpos : 0 < 1+R := by linarith
  by_cases small : (X:ℝ) ≤ (P:ℝ)^2*(1+R)
  · have inc : {n : ℕ | n<X ∧ ∃ a b : ℕ, n=a^2+b^2 ∧ (a:ℝ)^2*(1+R)<X} ⊆ (B : Set ℕ) := by
      rintro n ⟨hn,a,b,e,h⟩
      have ha : a<P := by
        by_contra! h'
        have pw : (P:ℝ)^2 ≤ (a:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left h' 2
        linarith only [small,h,mul_le_mul_of_nonneg_right pw fpos.le]
      have pq : P ≤ Q := Nat.add_le_add_right (Nat.div_le_div_right hHL) 1
      have hb : b<Q := by
        by_contra! ge
        have h1 := Nat.pow_le_pow_left ge 2
        have h2 := Nat.mul_le_mul_right Q pq
        rw [← pow_two] at h2
        omega
      exact mem_image.mpr ⟨(a,b),mem_product.mpr ⟨mem_range.mpr ha,mem_range.mpr hb⟩,e.symm⟩
    have v := Set.ncard_le_ncard inc (finite_toSet B)
    rw [Set.ncard_coe_finset] at v
    have h := rect H L k S A (0,0) 1 hk (by rwa [card]) (by decide) box dense (by
      intro z hz; simpa [S] using mem_image_of_mem (fun z : ℕ × ℕ => ((z.1:ℤ),(z.2:ℤ))) hz) (by omega)
      ((arith X).trans (Nat.mul_le_mul_left C (Nat.add_le_add_right v 1)))
    rw [card] at h
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (le_max_left ..)))
  · have hH : H ≤ K*P := (Nat.lt_mul_div_succ H hK).le
    have hP : P ≤ X := by
      have p2 : (P:ℝ) ≤ (P:ℝ)^2 := by exact_mod_cast (show P ≤ P^2 by nlinarith only [Nat.le_mul_self P])
      exact_mod_cast (show (P:ℝ) ≤ X by nlinarith only [small,p2,mul_nonneg (sq_nonneg (P:ℝ)) r0])
    have hlog : Real.log ((H:ℝ)+1) ≤ (K:ℝ)+Real.log ((X:ℝ)+1) := by
      have h : (H:ℝ)+1 ≤ ((K:ℝ)+1)*((X:ℝ)+1) := by
        have h' := hH.trans (Nat.mul_le_mul_left K hP)
        exact_mod_cast (show H+1 ≤ (K+1)*(X+1) by nlinarith)
      have e := Real.log_le_log (by positivity) h
      rw [Real.log_mul (by positivity) (by positivity)] at e
      linarith [Real.log_le_sub_one_of_pos (show 0 < (K:ℝ)+1 by positivity)]
    have rr : R^2=Real.log ((X:ℝ)+1) := Real.sq_sqrt (Real.log_nonneg (by simp))
    have rk : R ≤ 2*k := by
      have ex : 1 ≤ Real.exp ((k:ℝ)^2) := Real.one_le_exp (sq_nonneg _)
      have xx : (X:ℝ) ≤ Real.exp ((k:ℝ)^2) := (by exact_mod_cast xN.trans card.le : (X:ℝ) ≤ A.card).trans cap
      have e := Real.log_le_log (by positivity : 0 < (X:ℝ)+1) (show (X:ℝ)+1 ≤ 2*Real.exp ((k:ℝ)^2) by linarith)
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp] at e
      have hk' : 1 ≤ (k:ℝ)^2 := by exact_mod_cast (show 1 ≤ k^2 by simpa using Nat.pow_le_pow_left hk 2)
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have lfactor : 1+Real.log ((H:ℝ)+1) ≤ (1+R)*((K:ℝ)+4)*k := by
      have k1 : 1 ≤ (k:ℝ) := by exact_mod_cast hk
      nlinarith only [hlog,rr,mul_le_mul_of_nonneg_right rk r0,
        mul_le_mul_of_nonneg_left k1 (Nat.cast_nonneg K),k1,
        mul_nonneg (mul_nonneg r0 (Nat.cast_nonneg K)) (Nat.cast_nonneg k),mul_nonneg r0 (Nat.cast_nonneg k)]
    have hh : (H:ℝ)^2 ≤ (K:ℝ)^2*P^2 := by exact_mod_cast (by simpa only [mul_pow] using Nat.pow_le_pow_left hH 2 : H^2 ≤ K^2*P^2)
    have bud : (H:ℝ)^2*(1+Real.log ((H:ℝ)+1)) ≤ T*(k:ℝ)*S.card := calc
      _ ≤ ((K:ℝ)^2*P^2)*((1+R)*(K+4)*k) := mul_le_mul hh lfactor (by linarith [Real.log_nonneg (show 1 ≤ (H:ℝ)+1 by simp)]) (by positivity)
      _ = ((K:ℝ)^2*(K+4)*k)*((P:ℝ)^2*(1+R)) := by ring
      _ ≤ ((K:ℝ)^2*(K+4)*k)*S.card := mul_le_mul_of_nonneg_left ((le_of_not_ge small).trans (by exact_mod_cast xN)) (by positivity)
      _ = _ := by dsimp [T]; push_cast; ring
    have bound := euclidean_strip H k T S 0 hk (by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      have x := mem_range.mp (mem_product.mp (box hw)).1
      simp only [zero_add]; exact ⟨by positivity,by exact_mod_cast x⟩) bud
    rw [card] at bound
    exact bound.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (le_max_right ..)))

/-- A bounded-aspect rectangle inside the square-patch case. -/
theorem bounded_aspect_rectangle (lr : H3) (r t : ℕ) : ∃ G : ℕ, ∀ (H L k : ℕ)
    (S : Finset (ℤ × ℤ)) (A : Finset (ℕ × ℕ)) (p : ℤ × ℤ) (s : ℤ),
    0 < k → (S.card:ℝ) ≤ Real.exp ((k:ℝ)^2) → s ≠ 0 →
    H ≤ L → L ≤ r*H → A ⊆ range H ×ˢ range L → H*L ≤ t*A.card →
    (∀ z ∈ A, (p.1+s*z.1,p.2+s*z.2) ∈ S) → S.card ≤ 2*A.card →
    let q := fun z : ℤ × ℤ => z.1^2+z.2^2
    S.card ≤ k*G*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  obtain ⟨G,bound⟩ := square_patch_bound lr (r*t)
  refine ⟨G,?_⟩
  intro H L k S A p s hk cap hs hHL ratio box dens sub half
  apply bound L k S A p s hk cap hs _ _ sub half
  · exact box.trans (product_subset_product (range_mono hHL) (by rfl))
  · nlinarith only [Nat.mul_le_mul_right L ratio,Nat.mul_le_mul_left r dens]

/-- Transfer the squarefree bound using the assigned pins, the divisor estimate,
or the remaining arithmetic hypothesis. -/
theorem integral_form_bound (arith : H1) (lr : H3) :
  ∃ C : ℕ, ∀ a b c : ℤ, 0 < a → b^2 < 4*a*c → ∀ (S : Finset (ℤ × ℤ)) (k : ℕ),
    0 < k → (S.card : ℝ) ≤ Real.exp ((k:ℝ)^2) →
    let q := fun v : ℤ × ℤ => a*v.1^2+b*v.1*v.2+c*v.2^2
    S.card ≤ k*C*((S.offDiag.image fun xy => q (xy.1-xy.2)).card+1) := by
  classical
  obtain ⟨r,t₀,C,hard⟩ := arith
  obtain ⟨B,strip⟩ := polynomial_coefficient_strip r t₀
  obtain ⟨P,poly⟩ := polylog_coefficient_strip r t₀
  obtain ⟨G,grid⟩ := rectangle_coverage_bound lr t₀ (t₀+1)
  let U := max (64*(1+8*t₀)) (max (16*(1+4*t₀)) (max G (max C (max B P))))
  refine ⟨max U 4,?_⟩
  intro a b c ha hdisc A k hk hsize Q
  let V := fun (q : ℤ × ℤ → ℤ) (T : Finset (ℤ × ℤ)) => T.offDiag.image fun xy => q (xy.1-xy.2)
  obtain ⟨d,hd,hsq,F,_,hF⟩ := squarefree_model a b c ha hdisc
  obtain ⟨hc,hv⟩ := hF A
  let S := A.image F
  let q := fun v : ℤ × ℤ => v.1^2+(d:ℤ)*v.2^2
  change S.card = A.card at hc
  change V q S = (V Q A).image (4*a * ·) at hv
  have hvals := congrArg Finset.card hv
  rw [card_image_of_injective _ (mul_right_injective₀ (by positivity : 4*a ≠ 0))] at hvals
  change A.card ≤ k*max U 4*((V Q A).card+1)
  rw [← hc,← hvals]
  by_cases thin : d ≠ 1 ∨ ∀ (u : ℤ) (H : ℕ), (∀ z ∈ S, u ≤ z.1 ∧ z.1 < u+H) →
      (t₀:ℝ)*k*S.card < (H:ℝ)^2*(1+Real.log ((H:ℝ)+1))
  swap
  · push Not at thin
    obtain ⟨eqd,u,H,span,small⟩ := thin
    subst d
    have h := euclidean_strip H k t₀ S u hk span small
    have sqeq : q = fun z : ℤ × ℤ => z.1^2+z.2^2 := by ext z; simp [q]
    rw [sqeq]
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left k (show 64*(1+8*t₀) ≤ max U 4 by dsimp [U]; omega)))
  by_cases wide : ∀ p ∈ S, ∀ W : ℕ, (∀ z ∈ S, (z.1-p.1).natAbs ≤ W) →
      (t₀:ℝ)*k*S.card < (W:ℝ)^2*(1+Real.log (2*W+1))^2
  swap
  · push Not at wide
    obtain ⟨p,hp,W,width,thin⟩ := wide
    have h := narrow_strip d W k t₀ S p hd hk hp width thin
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left k (show 16*(1+4*t₀) ≤ max U 4 by dsimp [U]; omega)))
  by_cases sparse : (d ≠ 1 ∨ ∀ (A : Finset (ℕ × ℕ)) (H L : ℕ) (p : ℤ × ℤ) (s : ℤ), s ≠ 0 →
      A ⊆ range H ×ˢ range L → H*L ≤ t₀*A.card →
      (∀ z ∈ A, (p.1+s*z.1,p.2+s*z.2) ∈ S) →
      let K := 4*(t₀+1)
      let P := H/K+1
      let Q := L/K+1
      Set.ncard {n : ℕ | n < min S.card (P*Q) ∧ ∃ a b : ℕ, n=a^2+b^2} ≤
        (t₀+1)*(((range P ×ˢ range Q).image fun z => z.1^2+z.2^2).card+1) → 2*A.card < S.card)
  swap
  · dsimp only at sparse
    push Not at sparse
    obtain ⟨eqd,A',H,L,p,s,hs,hA,dens,sub,cov,half⟩ := sparse
    subst d
    have h := grid H L k S A' p s hk (by rwa [hc]) hs hA dens sub half cov
    have sqeq : q = fun z : ℤ × ℤ => z.1^2+z.2^2 := by ext z; simp [q]
    rw [sqeq]
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left k (show G ≤ max U 4 by dsimp [U]; omega)))
  by_cases outside : ∀ p ∈ S, ∀ W : ℕ, (∀ z ∈ S, (z.1-p.1).natAbs ≤ W) →
      W^2 ≤ t₀*S.card → d^r < W^2 ∧ d^r < k^(5*r+1)
  swap
  · push Not at outside
    obtain ⟨p,hp,W,width,dense,scale⟩ := outside
    by_cases small : W^2 ≤ d^r
    · have h := strip d W S p hd hp width small dense
      exact h.trans (Nat.mul_le_mul_right _ (show B ≤ k*max U 4 by
        apply le_trans _ (Nat.le_mul_of_pos_left _ hk)
        dsimp [U]; omega))
    · have h := poly d W k S p hd hk hp (by rwa [hc]) width dense (by omega)
      exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left k (by dsimp [U]; omega : P ≤ max U 4)))
  by_cases heavy : ∀ T ⊆ S, S.card ≤ 2*T.card → ∀ (M : ℤ), 0 < M →
      ∀ (p : ℤ × ℤ → ℤ × ℤ) (t s : (ℤ × ℤ) × ℤ → ℤ),
      (∀ x ∈ T, let e := (p x,x.1)
        p x ∈ S ∧ s e ∣ x.2-(p x).2-t e ∧
        M ∣ (d:ℤ)*s e*(2*t e+s e) ∧ M ∣ 2*(d:ℤ)*(s e)^2) →
      ∃ r : ℤ, k < ((T.image fun x => (p x,x.1)).filter fun e =>
        ((e.2-e.1.1)^2+(d:ℤ)*(t e)^2) % M = r).card
  · by_cases costly : ∀ (A : Finset ℕ) (X : ℕ → Finset ℕ) (W : ℕ → ℕ),
      (∀ a ∈ A, X a ⊆ range (W a+1)) →
      (∀ a ∈ A, ∀ u ∈ X a, ∃ x ∈ S, ∃ y ∈ S,
        u = (x.1-y.1).natAbs ∧ a = d*(x.2-y.2).natAbs^2) →
      let mass := ∑ a ∈ A, (X a).card
      let cost := ∑ a ∈ A, ∑ b ∈ A, if a=b then (X a).card else
        let h := max a b-min a b
        min (min (X a).card (X b).card) (h.divisors.filter fun j =>
          j ≤ h/j ∧ h/j+j ≤ 2*W (min a b) ∧ h/j-j ≤ 2*W (max a b) ∧ j%2 = (h/j)%2).card
      0 < mass → k*mass^2 < S.card*cost
    · have h := hard d S k hd hsq hk (by rwa [hc]) thin wide sparse outside heavy costly
      exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left k (show C ≤ max U 4 by dsimp [U]; omega)))
    dsimp only at costly
    push Not at costly
    obtain ⟨A',X,W,width,pairs,pos,cheap⟩ := costly
    let mass := ∑ a ∈ A', (X a).card
    let cost := ∑ a ∈ A', ∑ b ∈ A', if a=b then (X a).card else
      let h := max a b-min a b
      min (min (X a).card (X b).card) (h.divisors.filter fun j =>
        j ≤ h/j ∧ h/j+j ≤ 2*W (min a b) ∧ h/j-j ≤ 2*W (max a b) ∧ j%2 = (h/j)%2).card
    change 0 < mass at pos
    change S.card*cost ≤ k*mass^2 at cheap
    have energy := divisor_gap_bound d S A' X W width pairs
    change mass^2 ≤ ((V q S).card+1)*cost at energy
    have hcpos : 0 < cost := by
      by_contra! he
      rw [show cost = 0 by omega,mul_zero] at energy
      exact (Nat.not_lt_of_ge energy) (pow_pos pos 2)
    apply Nat.le_of_mul_le_mul_right _ hcpos
    calc
      _ ≤ k*mass^2 := cheap
      _ ≤ k*(((V q S).card+1)*cost) := Nat.mul_le_mul_left _ energy
      _ = k*1*((V q S).card+1)*cost := by ring
      _ ≤ _ := by gcongr; omega
  push Not at heavy
  obtain ⟨T,hsub,half,M,_,p,t,s,pins,cap⟩ := heavy
  have h := shifted_pin_bound d hd S T p M t s hsub k pins cap
  calc
    _ ≤ 2*T.card := half
    _ ≤ 2*(2*k*((V q S).card+1)) := Nat.mul_le_mul_left _ h
    _ = k*4*((V q S).card+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left k (le_max_right ..))

/-- The common-scale estimate follows from the integral-form estimate. -/
theorem common_scale_bound (arith : H1) (lr : H3) :
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  ∃ C : ℕ, ∀ (T : Finset X) (k : ℕ), 0 < k → (T.card : ℝ) ≤ Real.exp ((k:ℝ)^2) →
    (∃ L : ℝ, 0 < L ∧ ∀ x ∈ T, ∀ y ∈ T, ∃ t : ℚ, dist x y^2 = L*t) →
    T.card ≤ k*C*(distinctDistances T+1) := by
  classical
  obtain ⟨C,bound⟩ := integral_form_bound arith lr
  refine ⟨max C 2,?_⟩
  intro T k hk hsize scale
  obtain ⟨L,hL,rat⟩ := scale
  by_cases tri : ∃ x ∈ T, ∃ y ∈ T, ∃ z ∈ T,
      (y.val 0-x.val 0)*(z.val 1-x.val 1) ≠ (y.val 1-x.val 1)*(z.val 0-x.val 0)
  · obtain ⟨p,hp,q,hq,r,hr,hn⟩ := tri
    obtain ⟨a,b,c,ha,hd,S,hcard,hvalues⟩ := three_pin_model T T (fun _ h => h)
      ⟨p,hp,q,hq,r,hr,hn,L,hL,by
        intro x hx o ho
        rcases ho with rfl|rfl|rfl
        exacts [rat x hx _ hp,rat x hx _ hq,rat x hx _ hr]⟩
    have h := bound a b c ha hd S k hk (by rwa [hcard])
    rw [← hcard]
    exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left k (le_max_left ..))
      (Nat.add_le_add_right hvalues 1))
  · push Not at tri
    calc
      _ ≤ 2*distinctDistances T+1 := flat_count T tri
      _ ≤ 1*2*(distinctDistances T+1) := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul hk (le_max_right ..))


theorem main : H1 → H2 → H3 → OMA.R_Erdos89_erdos_89_R1.H2 := by
  classical
  rintro arith ⟨H,hard⟩ lr
  obtain ⟨R,rational⟩ := common_scale_bound arith lr
  let C := max (2*R) (max H 8)
  let X := {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}
  let f (j : ℕ) : X := ⟨EuclideanSpace.single 0 (j : ℝ), by
    intro i
    by_cases h : i = 0
    · subst i
      simpa using (isIntegral_natCast (R := ℤ) (B := ℝ) j)
    · simpa [PiLp.single_apply, h] using (isIntegral_zero : IsIntegral ℤ (0:ℝ))⟩
  have : Infinite X := Infinite.of_injective f (by
    intro i j hij
    simpa [f] using congrArg (fun p : X => p.val 0) hij)


  apply Asymptotics.IsBigO.of_bound (4*((C:ℝ)+1))
  filter_upwards [eventually_ge_atTop (⌈Real.exp 1⌉₊+2)] with n hn
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hexp : Real.exp 1 ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈Real.exp 1⌉₊ ≤ n))
  have hlog : 1 ≤ Real.log (n:ℝ) := by simpa using Real.log_le_log (Real.exp_pos _) hexp
  let z := Real.sqrt (Real.log n)
  have hz : 1 ≤ z := by simpa [z] using Real.sqrt_le_sqrt hlog
  let k := ⌈z⌉₊
  have hceil : z ≤ (k:ℝ) := Nat.le_ceil _
  have hk : 0 < k := by exact_mod_cast (zero_lt_one.trans_le (hz.trans hceil))
  have hround : (k:ℝ) ≤ 2*z := by
    have h := Nat.ceil_lt_add_one (zero_le_one.trans hz)
    dsimp [k]; linarith
  have hcap : (n:ℝ) ≤ Real.exp ((k:ℝ)^2) := by
    rw [← Real.exp_log hnpos]
    apply Real.exp_le_exp.mpr
    have he : z^2 = Real.log n := Real.sq_sqrt (zero_le_one.trans hlog)
    nlinarith [mul_nonneg (sub_nonneg.mpr hceil) (by positivity : 0 ≤ (k:ℝ)+z)]
  obtain ⟨S₀,h₀⟩ := Infinite.exists_subset_card_eq X n
  obtain ⟨S,hS,hD⟩ := Nat.sInf_mem (show
    {d : ℕ | ∃ S : Finset X, S.card=n ∧ distinctDistances S=d}.Nonempty from ⟨_,S₀,h₀,rfl⟩)
  change distinctDistances S = minimalDistinctDistances X n at hD
  have hfb : S.card ≤ k*(C+1)*(distinctDistances S+1) := by
    by_cases hno : ∀ T ⊆ S, S.card ≤ 2*T.card → ¬ (∃ (f : X → ℤ × ℤ) (a b c : ℝ), ∀ x ∈ T, ∀ y ∈ T,
          dist x y^2 = a*(f x-f y).1^2+b*(f x-f y).1*(f x-f y).2+c*(f x-f y).2^2)
    · have hb := hard S k hk (hS ▸ hcap) (by simpa [hS] using hD) hno
      exact hb.trans (by dsimp [C]; gcongr; omega)
    push Not at hno
    obtain ⟨T,hsub,hhalf,f,a,b,c,chart⟩ := hno
    have mono : distinctDistances T ≤ distinctDistances S := by
      apply card_le_card
      intro r hr
      obtain ⟨⟨x,y⟩,h,rfl⟩ := mem_image.mp hr
      obtain ⟨hx,hy,hne⟩ := mem_offDiag.mp h
      exact mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hsub hx,hsub hy,hne⟩,rfl⟩
    by_cases scale : ∃ L : ℝ, 0 < L ∧ ∃ A B C : ℚ, a=L*A ∧ b=L*B ∧ c=L*C
    · obtain ⟨L,hL,A,B,C',rfl,rfl,rfl⟩ := scale
      have ht : (T.card:ℝ) ≤ Real.exp ((k:ℝ)^2) :=
        (by exact_mod_cast card_le_card hsub : (T.card:ℝ) ≤ S.card).trans (hS ▸ hcap)
      have hb := rational T k hk ht ⟨L,hL,fun x hx y hy => ?_⟩
      · calc
          _ ≤ 2*T.card := hhalf
          _ ≤ 2*(k*R*(distinctDistances T+1)) := Nat.mul_le_mul_left _ hb
          _ = k*(2*R)*(distinctDistances T+1) := by ring
          _ ≤ _ := by dsimp [C]; gcongr; omega
      · let w := f x-f y
        refine ⟨A*w.1^2+B*w.1*w.2+C'*w.2^2,?_⟩
        rw [chart x hx y hy]
        push_cast
        dsimp [w]
        ring
    · have he := irrational_count T f a b c scale chart
      calc
        _ ≤ 2*T.card := hhalf
        _ ≤ 2*(4*distinctDistances T+1) := Nat.mul_le_mul_left _ he
        _ ≤ 1*8*(distinctDistances S+1) := by omega
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega : 1 ≤ k) (by dsimp [C]; omega : 8 ≤ C+1))
  have hd : 0 < distinctDistances S := by
    obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (by omega : 1 < S.card)
    exact card_pos.mpr ⟨_,mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hx,hy,hxy⟩,rfl⟩⟩
  let D : ℝ := distinctDistances S
  have hd' : (1:ℝ) ≤ D := by dsimp [D]; exact_mod_cast (show 1 ≤ distinctDistances S from hd)
  rw [hS] at hfb
  have hh : (n:ℝ) ≤ (k:ℝ)*((C:ℝ)+1)*(D+1) := by dsimp [D]; exact_mod_cast hfb
  change ‖(n:ℝ)/z‖ ≤ 4*((C:ℝ)+1)*‖(minimalDistinctDistances X n : ℝ)‖
  rw [← hD,Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.norm_eq_abs,Nat.abs_cast,
    div_le_iff₀ (zero_lt_one.trans_le hz)]
  change (n:ℝ) ≤ 4*((C:ℝ)+1)*D*z
  calc
    _ ≤ _ := hh
    _ ≤ (2*z)*((C:ℝ)+1)*(2*D) := by gcongr; linarith
    _ = _ := by ring

end OMA.R_Erdos89_erdos_89_R1_H2_R3
