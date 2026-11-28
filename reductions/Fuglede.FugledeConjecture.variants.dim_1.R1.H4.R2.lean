import OMAReductions.R_Fuglede_FugledeConjecture_variants_dim_1_R1

/-!
If the shared frequencies form an arithmetic progression modulo one, column
orthogonality of the square Fourier matrix gives a vanishing geometric sum.
Distinct sites in each tile therefore have phases differing by a nontrivial
p-th root of unity. The floor of the rescaled phase, reduced modulo p, colors
each translated reflected tile bijectively and gives one complement for all.

For three sites, even a single frequency difference suffices. Both its
character sum and the inverse character sum vanish. Eliminating the third
phase forces each nontrivial phase ratio to satisfy X² + X + 1 = 0.
-/

namespace OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H4_R2

/-- The zero color meets every translated reflected tile exactly once. -/
theorem sector {p : ℕ} (hp : 0 < p) (A : Finset (Finset ℤ)) (d : ℝ)
    (card : ∀ S ∈ A, S.card = p)
    (hd : ∀ S ∈ A, ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      ∃ z : ℤ, d * ((x : ℝ) - y) = z ∧ ¬(p : ℤ) ∣ z) : (∃ T : Set ℤ, ∀ S ∈ A, ∀ m : ℤ, ∃! q : {k // k ∈ S} × {t // t ∈ T}, q.1.1 + q.2.1 = m) := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  let color (t : ℤ) : ZMod p := (⌊d * (t : ℝ)⌋ : ℤ)
  refine ⟨{t | color t = 0}, ?_⟩
  intro S hS m
  let f (x : S) := color (m - x.val)
  have inj : Function.Injective f := by
    intro x y h
    by_contra hn
    obtain ⟨z,hz,hnd⟩ := hd S hS x x.property y y.property (fun h => hn (Subtype.ext h))
    have hr : d * ((m : ℝ) - x.val) = d * ((m : ℝ) - y.val) - z := by linarith
    change (↑⌊d * ((m-x.val : ℤ) : ℝ)⌋ : ZMod p) = ↑⌊d * ((m-y.val : ℤ) : ℝ)⌋ at h
    simp only [Int.cast_sub,hr,Int.floor_sub_intCast] at h
    exact hnd ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp (sub_eq_self.mp h))
  have bij := (Fintype.bijective_iff_injective_and_card f).2
    ⟨inj, by simpa using card S hS⟩
  obtain ⟨x,hx⟩ := bij.2 0
  refine ⟨(x, ⟨m-x.val,hx⟩), by simp, ?_⟩
  rintro ⟨y,t⟩ hy
  have ht : t.val = m - y.val := by change y.val+t.val=m at hy; omega
  have hfy : f y = 0 := by change color (m-y.val) = 0; rw [← ht]; exact t.property
  have he := inj (hfy.trans hx.symm)
  subst y
  exact Prod.ext rfl (Subtype.ext ht)

open scoped FourierTransform
private theorem phase_formula (t : ℝ) :
    (𝐞 t : ℂ) = Complex.exp ((t : ℂ) * (2 * Real.pi * Complex.I)) := by
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring
theorem phase_add (x y : ℝ) : (𝐞 x : ℂ) * (𝐞 y : ℂ) = (𝐞 (x+y) : ℂ) := by simp [phase_formula, add_mul, Complex.exp_add]
theorem phase_zero : (𝐞 0 : ℂ) = 1 := by simp
theorem phase_pow (x : ℝ) (n : ℕ) : (𝐞 x : ℂ) ^ n = (𝐞 (n * x) : ℂ) := by
  rw [phase_formula, phase_formula, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
theorem phase_eq_one (x : ℝ) : (𝐞 x : ℂ) = 1 ↔ ∃ z : ℤ, x = z := by
  rw [phase_formula, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨z,h⟩
    have hh : (x : ℂ) = z := mul_right_cancel₀ (by simp : 2*(Real.pi : ℂ)*Complex.I ≠ 0) h
    exact ⟨z, by exact_mod_cast hh⟩
  · rintro ⟨z,rfl⟩
    exact ⟨z,rfl⟩
theorem grid_of_geometric {p : ℕ} (hp : 0 < p) (t : ℝ)
    (hs : ∑ i : Fin p, (𝐞 ((i.val : ℝ)*t) : ℂ) = 0) :
    ∃ z : ℤ, p*t = z ∧ ¬(p : ℤ) ∣ z := by
  simp_rw [← phase_pow] at hs
  have hne : (𝐞 t : ℂ) ≠ 1 := by
    intro h
    simp [h, hp.ne'] at hs
  have hpow := geom_sum_mul ((𝐞 t : ℂ)) p
  rw [← Fin.sum_univ_eq_sum_range, hs, zero_mul] at hpow
  obtain ⟨z,hz⟩ := (phase_eq_one _).mp ((phase_pow _ _).symm.trans (by linear_combination -hpow))
  refine ⟨z,hz,?_⟩
  rintro ⟨k,rfl⟩
  apply hne
  apply (phase_eq_one _).mpr
  refine ⟨k,?_⟩
  push_cast at hz
  exact mul_left_cancel₀ (by exact_mod_cast hp.ne' : (p : ℝ) ≠ 0) hz

/-- Passing from rows to columns converts a progression of frequencies into a geometric sum. -/
theorem geometric_columns {p : ℕ} (hp : 0 < p) (d : ℝ) (S : Finset ℤ)
    (hcard : S.card = p)
    (rows : ∀ i j : Fin p, i ≠ j →
      ∑ k : S, (𝐞 (((i.val : ℝ)-j.val)*d*k.val) : ℂ) = 0)
    (x y : S) (hxy : x ≠ y) :
    ∑ i : Fin p, (𝐞 ((i.val : ℝ)*(d*((x.val : ℝ)-y.val))) : ℂ) = 0 := by
  classical
  let V : Matrix (Fin p) S ℂ := fun i k => (𝐞 ((i.val : ℝ)*d*k.val) : ℂ)
  let W : Matrix S (Fin p) ℂ := fun k i => (𝐞 (-((i.val : ℝ)*d*k.val)) : ℂ)
  have hdiag : V * W = (p : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) := by
    ext i j
    rw [Matrix.mul_apply]
    change (∑ k : S, (𝐞 _ : ℂ) * (𝐞 _ : ℂ)) = (p : ℂ) * (1 : Matrix (Fin p) (Fin p) ℂ) i j
    calc
      _ = ∑ k : S, (𝐞 (((i.val : ℝ)-j.val)*d*k.val) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [phase_add]
        exact congrArg (fun t : ℝ => (𝐞 t : ℂ)) (by ring)
      _ = _ := by
        by_cases hij : i = j
        · subst j; simp [hcard]
        · rw [rows i j hij]; simp [hij]
  have hpn : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hn : V * ((p : ℂ)⁻¹ • W) = 1 := by
    rw [Matrix.mul_smul, hdiag, smul_smul, inv_mul_cancel₀ hpn, one_smul]
  have hb := (Matrix.mul_eq_one_comm_of_card_eq (Fin p) S ℂ (by simpa using hcard.symm)).mp hn
  rw [Matrix.smul_mul] at hb
  have hz := congrArg (fun M : Matrix S S ℂ => M y x) hb
  change (p : ℂ)⁻¹ * (W*V) y x = (1 : Matrix S S ℂ) y x at hz
  rw [Matrix.one_apply_ne (Ne.symm hxy)] at hz
  have hg := (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hpn)
  rw [Matrix.mul_apply] at hg
  convert hg using 1
  apply Finset.sum_congr rfl
  intro i _
  change (𝐞 _ : ℂ) = (𝐞 _ : ℂ) * (𝐞 _ : ℂ)
  rw [phase_add]
  exact congrArg (fun t : ℝ => (𝐞 t : ℂ)) (by ring)

private theorem small_progression {p : ℕ} (hp : 0 < p) (hp2 : p ≤ 2)
    (Γ : Finset ℝ) (hcard : Γ.card = p) : (∃ (α δ : ℝ) (f : Fin p ≃ Γ) (n : Fin p → ℤ),
    ∀ i, (f i).val = α + (i.val : ℝ)*δ + n i) := by
  classical
  obtain ⟨f⟩ := Fintype.card_eq.mp (show Fintype.card (Fin p) = Fintype.card Γ by simpa using hcard.symm)
  interval_cases p
  · exact ⟨(f 0).val,0,f,fun _ => 0,by intro i; fin_cases i; simp⟩
  · refine ⟨(f 0).val,(f 1).val-(f 0).val,f,fun _ => 0,?_⟩
    intro i
    fin_cases i <;> simp

theorem progression_tiles {p : ℕ} (hp : 0 < p) (Γ : Finset ℝ)
    (A : Finset (Finset ℤ)) (hc :
      (∀ S ∈ A, S.card = p ∧ ∀ g ∈ Γ, ∀ h ∈ Γ, g ≠ h →
    ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I * (g-h) * (k : ℝ)) = 0))
    (hG : (∃ (α δ : ℝ) (f : Fin p ≃ Γ) (n : Fin p → ℤ),
    ∀ i, (f i).val = α + (i.val : ℝ)*δ + n i)) :
    (∃ T : Set ℤ, ∀ S ∈ A, ∀ m : ℤ, ∃! q : {k // k ∈ S} × {t // t ∈ T}, q.1.1 + q.2.1 = m) := by
  classical
  obtain ⟨a,d,f,n,hf⟩ := hG
  apply sector hp A ((p : ℝ)*d) (fun S hS => (hc S hS).1)
  intro S hS x hx y hy hxy
  have rows (i j : Fin p) (hij : i ≠ j) :
      ∑ k : S, (𝐞 (((i.val : ℝ)-j.val)*d*k.val) : ℂ) = 0 := by
    have hne : (f i).val ≠ (f j).val :=
      fun h => hij (f.injective (Subtype.ext h))
    have hsum := (hc S hS).2 _ (f i).property _ (f j).property hne
    calc
      _ = ∑ k ∈ S, (𝐞 (((i.val : ℝ)-j.val)*d*(k : ℝ)) : ℂ) := Finset.sum_attach _ _
      _ = ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I *
            ((f i).val-(f j).val) * (k : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k _
        let t : ℝ := ((i.val : ℝ)-j.val)*d*k
        have hn : (𝐞 ((((n i - n j) * k : ℤ) : ℝ)) : ℂ) = 1 := (phase_eq_one _).2 ⟨_,rfl⟩
        calc
          (𝐞 t : ℂ) = (𝐞 (t + (((n i-n j)*k : ℤ) : ℝ)) : ℂ) := by rw [← phase_add,hn,mul_one]
          _ = _ := by
            rw [hf i,hf j]
            simp only [phase_formula]; unfold t
            congr 1
            push_cast
            ring
      _ = 0 := hsum
  have h := geometric_columns hp d S (hc S hS).1 rows
    (⟨x,hx⟩ : S) ⟨y,hy⟩ (fun e => hxy (congrArg Subtype.val e))
  simpa only [mul_assoc] using grid_of_geometric hp _ h

private theorem third_site {S : Finset ℤ} {x y : ℤ} (hs : S.card = 3)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ z : ℤ, ∀ f : ℤ → ℂ, ∑ k ∈ S, f k = f x + f y + f z := by
  have hy' := Finset.mem_erase.mpr ⟨hxy.symm,hy⟩
  have h1 : ((S.erase x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem hy',Finset.card_erase_of_mem hx,hs]
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp h1
  refine ⟨z,fun f => ?_⟩
  rw [← Finset.sum_erase_add S f hx, ← Finset.sum_erase_add (S.erase x) f hy',hz]
  simp; ring

private theorem shift_sum {S : Finset ℤ} {g h : ℝ} (y : ℤ)
    (hs : ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I * (g-h) * (k : ℝ)) = 0) :
    ∑ k ∈ S, (𝐞 ((g-h)*((k : ℝ)-y)) : ℂ) = 0 := by
  calc
    _ = ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I * (g-h) * (k : ℝ)) *
        (𝐞 (-((g-h)*y)) : ℂ) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [phase_formula]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = 0 := by rw [← Finset.sum_mul, hs, zero_mul]

theorem triple_tiles (Γ : Finset ℝ) (A : Finset (Finset ℤ)) (hcard : Γ.card = 3)
    (hc :
      (∀ S ∈ A, S.card = 3 ∧ ∀ g ∈ Γ, ∀ h ∈ Γ, g ≠ h →
    ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I * (g-h) * (k : ℝ)) = 0)) : (∃ T : Set ℤ, ∀ S ∈ A, ∀ m : ℤ, ∃! q : {k // k ∈ S} × {t // t ∈ T}, q.1.1 + q.2.1 = m) := by
  obtain ⟨g,hg,h,hh,hgh⟩ := Finset.one_lt_card.mp (by omega : 1 < Γ.card)
  apply sector (by decide : 0 < 3) A (3*(g-h)) (fun S hS => (hc S hS).1)
  intro S hS x hx y hy hxy
  obtain ⟨z,hz⟩ := third_site (hc S hS).1 hx hy hxy
  let X := (𝐞 ((g-h)*((x : ℝ)-y)) : ℂ)
  let Z := (𝐞 ((g-h)*((z : ℝ)-y)) : ℂ)
  have pos := shift_sum y ((hc S hS).2 g hg h hh hgh)
  rw [hz] at pos
  have eq1 : X+1+Z=0 := by simpa [X,Z,phase_zero] using pos
  have neg := shift_sum y ((hc S hS).2 h hh g hg hgh.symm)
  rw [hz] at neg
  have inv (k : ℤ) : (𝐞 ((h-g)*((k : ℝ)-y)) : ℂ) = ((𝐞 ((g-h)*((k : ℝ)-y)) : ℂ))⁻¹ := by
    rw [show (h-g)*((k : ℝ)-y) = -((g-h)*((k : ℝ)-y)) by ring]
    simp [phase_formula,Complex.exp_neg]
  simp only [inv] at neg
  have eq2 : X⁻¹+1+Z⁻¹=0 := by simpa [X,Z,phase_zero] using neg
  have hX : X ≠ 0 := by simpa only [X, phase_formula] using (Complex.exp_ne_zero _)
  have hZ : Z ≠ 0 := by simpa only [Z, phase_formula] using (Complex.exp_ne_zero _)
  field_simp [hX,hZ] at eq2
  have hg3 : ∑ i : Fin 3, (𝐞 ((i.val : ℝ)*((g-h)*((x : ℝ)-y))) : ℂ) = 0 := by
    simp_rw [← phase_pow]
    change ∑ i : Fin 3, X^i.val = 0
    rw [Fin.sum_univ_three]
    change X^0 + X^1 + X^2 = 0
    linear_combination (X+1)*eq1-eq2
  simpa [mul_assoc] using grid_of_geometric (by decide : 0<3) _ hg3

/-- The remaining commensurate spectra lack any progression ordering modulo one. -/
def H1 : Prop := ∀ (p : ℕ), 0 < p → ∀ (Γ : Finset ℝ) (A : Finset (Finset ℤ)),
  Γ.card = p → (∀ S ∈ A, S.card = p ∧ ∀ g ∈ Γ, ∀ h ∈ Γ, g ≠ h →
    ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I * (g-h) * (k : ℝ)) = 0) →
  3 < p →
  ¬(∃ (α δ : ℝ) (f : Fin p ≃ Γ) (n : Fin p → ℤ),
    ∀ i, (f i).val = α + (i.val : ℝ)*δ + n i) →
  (∃ N : ℕ, 0 < N ∧ ∀ x ∈ Γ, ∀ y ∈ Γ, ∃ n : ℤ, (N : ℝ)*(x-y) = n) →
  (∃ T : Set ℤ, ∀ S ∈ A, ∀ m : ℤ, ∃! q : {k // k ∈ S} × {t // t ∈ T}, q.1.1 + q.2.1 = m)

/-- The remaining spectra have incommensurate differences and lack a progression ordering. -/
def H2 : Prop := ∀ (p : ℕ), 0 < p → ∀ (Γ : Finset ℝ) (A : Finset (Finset ℤ)),
  Γ.card = p → (∀ S ∈ A, S.card = p ∧ ∀ g ∈ Γ, ∀ h ∈ Γ, g ≠ h →
    ∑ k ∈ S, Complex.exp (2 * Real.pi * Complex.I * (g-h) * (k : ℝ)) = 0) →
  3 < p →
  ¬(∃ (α δ : ℝ) (f : Fin p ≃ Γ) (n : Fin p → ℤ),
    ∀ i, (f i).val = α + (i.val : ℝ)*δ + n i) →
  ¬(∃ N : ℕ, 0 < N ∧ ∀ x ∈ Γ, ∀ y ∈ Γ, ∃ n : ℤ, (N : ℝ)*(x-y) = n) →
  (∃ T : Set ℤ, ∀ S ∈ A, ∀ m : ℤ, ∃! q : {k // k ∈ S} × {t // t ∈ T}, q.1.1 + q.2.1 = m)

theorem main : H1 → H2 → OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1.H4 := by
  intro h1 h2 p hp Γ A hcard hc
  by_cases h3 : p = 3
  · rcases h3 with rfl; exact triple_tiles Γ A hcard hc
  by_cases hg : (∃ (α δ : ℝ) (f : Fin p ≃ Γ) (n : Fin p → ℤ),
    ∀ i, (f i).val = α + (i.val : ℝ)*δ + n i)
  · exact progression_tiles hp Γ A hc hg
  have hlarge : 3 < p := by
    by_contra! hs
    exact hg (small_progression hp (by omega) Γ hcard)
  by_cases hq : (∃ N : ℕ, 0 < N ∧ ∀ x ∈ Γ, ∀ y ∈ Γ, ∃ n : ℤ, (N : ℝ)*(x-y) = n)
  · exact h1 p hp Γ A hcard hc hlarge hg hq
  · exact h2 p hp Γ A hcard hc hlarge hg hq

end OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H4_R2
