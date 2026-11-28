import OMAReductions.R_Erdos89_erdos_89_R1_H2_R1

-- Reduction of Erdos89.erdos_89.R1.H2.R1.H2. Credit: @wispiANt
open Finset EuclideanGeometry Filter Topology

namespace OMA.R_Erdos89_erdos_89_R1_H2_R1_H2_R1

/-- Comparison with lattice configurations measured by an arbitrary positive definite
real binary quadratic form. The lattice points have integer coordinates. -/
def H1 : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∃ N₀ : ℕ,
    ∀ P : Finset {p : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (p i)}, N₀ ≤ P.card →
      ∃ a b c : ℝ, 0 < a ∧ b^2 < 4*a*c ∧ ∃ S : Finset (ℤ × ℤ),
        S.card ≤ P.card ∧ P.card ≤ K * S.card ∧
        let q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
        (S.offDiag.image fun xy => q (xy.1 - xy.2)).card ≤ distinctDistances P

/-- Specialization on a fixed finite lattice configuration preserves its exact
number of values and positive definiteness. -/
def H2 : Prop :=
  ∀ (a b c : ℝ), 0 < a → b^2 < 4*a*c → ∀ S : Finset (ℤ × ℤ),
    ∃ A B C : ℤ, 0 < A ∧ B^2 < 4*A*C ∧
      let q := fun z : ℤ × ℤ => a*z.1^2 + b*z.1*z.2 + c*z.2^2
      let Q := fun z : ℤ × ℤ => A*z.1^2 + B*z.1*z.2 + C*z.2^2
      (S.offDiag.image fun xy => Q (xy.1 - xy.2)).card =
        (S.offDiag.image fun xy => q (xy.1 - xy.2)).card

section Specialization

/-- Rational-linear observations of the real line can converge pointwise to the identity. -/
private theorem rational_observations :
    ∃ f : ℕ → ℝ →ₗ[ℚ] ℚ, ∀ x : ℝ, Tendsto (fun n => (f n x : ℝ)) atTop (𝓝 x) := by
  classical
  let B := Module.Free.chooseBasis ℚ ℝ
  choose u _ _ hu using fun i => Real.exists_seq_rat_strictMono_tendsto (B i)
  refine ⟨fun n => B.constr ℚ (fun i => u i n), fun x => ?_⟩
  have h := tendsto_finsetSum (B.repr x).support (fun i _ =>
    (tendsto_const_nhds (x := ((B.repr x i : ℚ) : ℝ))).mul (hu i))
  have he := B.linearCombination_repr x
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Rat.smul_def] at he
  simpa only [Module.Basis.constr_apply, Finsupp.sum, smul_eq_mul, Rat.cast_sum,
    Rat.cast_mul, he] using h

private theorem clear_three (a b c : ℚ) :
    ∃ m A B C : ℤ, 0 < m ∧ (A : ℚ) = m*a ∧ (B : ℚ) = m*b ∧ (C : ℚ) = m*c := by
  refine ⟨(a.den:ℤ)*b.den*c.den, a.num*b.den*c.den, (a.den:ℤ)*b.num*c.den,
    (a.den:ℤ)*b.den*c.num, by positivity, ?_, ?_, ?_⟩ <;>
    push_cast <;> rw [← Rat.mul_den_eq_num] <;> ring

/-- Choose one observation preserving strict order on a finite set and positive definiteness. -/
private theorem select_observation (a b c : ℝ) (ha : 0 < a) (hd : b^2 < 4*a*c)
    (D : Finset ℝ) : ∃ f : ℝ →ₗ[ℚ] ℚ, 0 < f a ∧ (f b)^2 < 4*f a*f c ∧
      Set.InjOn f (D : Set ℝ) := by
  obtain ⟨f, hf⟩ := rational_observations
  have hpos := (hf a).eventually_const_lt ha
  have hdisc := ((hf b).pow 2).eventually_lt (((tendsto_const_nhds (x := (4:ℝ))).mul (hf a)).mul (hf c)) hd
  have horder : ∀ᶠ n in atTop, ∀ x ∈ D, ∀ y ∈ D, x < y → (f n x : ℝ) < f n y := by
    apply (eventually_all_finset D).2
    intro x _
    apply (eventually_all_finset D).2
    intro y _
    by_cases h : x < y
    · exact ((hf x).eventually_lt (hf y) h).mono fun _ hn _ => hn
    · exact Eventually.of_forall fun _ hxy => (h hxy).elim
  obtain ⟨n, hn, hdet, hlt⟩ := (hpos.and (hdisc.and horder)).exists
  refine ⟨f n, by exact_mod_cast hn, by exact_mod_cast hdet, ?_⟩
  intro x hx y hy he
  rcases lt_trichotomy x y with h|h|h
  · exact False.elim ((hlt x hx y hy h).ne (by rw [he]))
  · exact h
  · exact False.elim ((hlt y hy x hx h).ne (by rw [he]))

/-- Evaluation at integral coordinates commutes with any rational-linear observation. -/
private theorem observe_value (f : ℝ →ₗ[ℚ] ℚ) (a b c : ℝ) (x y : ℤ) :
    f (a*x^2+b*x*y+c*y^2) = f a*x^2+f b*x*y+f c*y^2 := by
  have scale (r : ℝ) (v : ℤ) : f (r*v) = f r*v := by
    simpa [zsmul_eq_mul, mul_comm] using map_zsmul f v r
  rw [show a*x^2+b*x*y+c*y^2 = a*((x^2:ℤ):ℝ)+b*((x*y:ℤ):ℝ)+c*((y^2:ℤ):ℝ) by push_cast; ring]
  rw [map_add, map_add, scale, scale, scale]
  push_cast
  ring

/-- All realized equalities and inequalities of form values survive the
specialization as equalities and distinctions, respectively. -/
theorem specialize_form : H2 := by
  classical
  intro a b c ha hd S
  let q := fun z : ℤ × ℤ => a*z.1^2+b*z.1*z.2+c*z.2^2
  let D := S.offDiag.image fun e => q (e.1-e.2)
  obtain ⟨f,hpos,hdisc,hinj⟩ := select_observation a b c ha hd D
  obtain ⟨m,A,B,C,hm,hA,hB,hC⟩ := clear_three (f a) (f b) (f c)
  have hm' : (0:ℚ) < m := by exact_mod_cast hm
  have hA' : (0:ℚ) < A := hA ▸ mul_pos hm' hpos
  have hD' : (B:ℚ)^2 < 4*(A:ℚ)*C := by
    rw [hA,hB,hC]
    nlinarith [mul_lt_mul_of_pos_left hdisc (sq_pos_of_pos hm')]
  refine ⟨A,B,C,by exact_mod_cast hA',by exact_mod_cast hD',?_⟩
  let Q := fun z : ℤ × ℤ => A*z.1^2+B*z.1*z.2+C*z.2^2
  have hval (z : ℤ × ℤ) : (Q z : ℚ) = m*f (q z) := by
    dsimp [Q,q]
    push_cast
    rw [hA,hB,hC,observe_value]
    ring
  let T := S.offDiag.image fun e => Q (e.1-e.2)
  have himage : T.image (fun z : ℤ => (z : ℚ)) = D.image (fun v => (m:ℚ)*f v) := by
    dsimp [T,D]
    simp only [image_image]
    exact image_congr fun e _ => hval (e.1-e.2)
  have hi : Set.InjOn (fun v => (m:ℚ)*f v) (D : Set ℝ) := by
    intro x hx y hy he
    exact hinj hx hy (mul_left_cancel₀ hm'.ne' he)
  change T.card = D.card
  calc
    _ = (T.image (fun z : ℤ => (z : ℚ))).card :=
      (card_image_of_injective _ Int.cast_injective).symm
    _ = _ := by rw [himage, card_image_of_injOn hi]

end Specialization

theorem main : H1 → H2 → OMA.R_Erdos89_erdos_89_R1_H2_R1.H2 := by
  rintro ⟨K,hK,N,h⟩ sp
  refine ⟨K,hK,N,fun P hP => ?_⟩
  obtain ⟨a,b,c,ha,hd,S,hsmall,hlarge,hbudget⟩ := h P hP
  obtain ⟨A,B,C,hpos,hdisc,he⟩ := sp a b c ha hd S
  exact ⟨A,B,C,hpos,hdisc,S,hsmall,hlarge,he.le.trans hbudget⟩

end OMA.R_Erdos89_erdos_89_R1_H2_R1_H2_R1
