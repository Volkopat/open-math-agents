import OMAReductions.R_Erdos89_erdos_89_R1

-- Reduction of Erdos89.erdos_89.R1.H2. Credit: @wispiANt
open Finset Filter EuclideanGeometry

namespace OMA.R_Erdos89_erdos_89_R1_H2_R2

/-- Bound a subset on which the two pinned distances satisfy one polynomial relation. -/
def H1 : Prop :=
  let X := {x : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (x i)}
  ∀ (S T : Finset X), T ⊆ S → ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    ∀ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 →
      (∀ x ∈ T, MvPolynomial.eval ![dist x p, dist x q] P = 0) →
      T.card ≤ 2*P.totalDegree*(distinctDistances S+1)

/-- Uniform finite estimate on minimizing configurations whose two-pin distance
pairs avoid every low-degree relation on half of their points. -/
def H2 : Prop :=
  let X := {x : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (x i)}
  ∃ C : ℕ, ∀ (S : Finset X) (k : ℕ), 0 < k → (S.card : ℝ) ≤ Real.exp ((k:ℝ)^2) →
    distinctDistances S = minimalDistinctDistances X S.card →
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ P : MvPolynomial (Fin 2) ℝ,
      P ≠ 0 → P.totalDegree ≤ k →
      2*(S.filter fun x => MvPolynomial.eval ![dist x p, dist x q] P = 0).card < S.card) →
    S.card ≤ k*C*(distinctDistances S+1)

section Pins

/-- Count the zeros on a two-coordinate grid, including the empty grid. -/
private theorem grid_zeros (W : Finset ℝ) (P : MvPolynomial (Fin 2) ℝ) (hP : P ≠ 0) :
    ((Fintype.piFinset fun _ : Fin 2 => W).filter
      (fun f => MvPolynomial.eval f P = 0)).card ≤ P.totalDegree*W.card := by
  classical
  rcases W.eq_empty_or_nonempty with rfl|hne
  · simp
  have h := MvPolynomial.schwartz_zippel_totalDegree hP W
  have hw : (0 : ℚ≥0) < W.card := by exact_mod_cast card_pos.mpr hne
  have h' := (div_le_div_iff₀ (pow_pos hw 2) hw).mp h
  rw [pow_two] at h'
  have hh := le_of_mul_le_mul_right (by simpa only [← mul_assoc] using h') hw
  exact_mod_cast hh

/-- Distinct planar pins recover each point up to at most two choices. -/
private theorem two_pin_fiber {X : Type*} (v : X → ℝ²) (hv : Function.Injective v)
    (T : Finset X) (p q : X) (hpq : p ≠ q) (a b : ℝ)
    (h₁ : ∀ x ∈ T, dist (v x) (v p) = a) (h₂ : ∀ x ∈ T, dist (v x) (v q) = b) :
    T.card ≤ 2 := by
  by_contra! h
  obtain ⟨x,hx,y,hy,z,hz,hxy,hxz,hyz⟩ := two_lt_card.mp h
  have hdim : Module.finrank ℝ ℝ² = 2 := finrank_euclideanSpace_fin
  rcases eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hdim (hv.ne hpq) (hv.ne hxy)
    (h₁ x hx) (h₁ y hy) (h₁ z hz) (h₂ x hx) (h₂ y hy) (h₂ z hz) with h|h
  · exact hxz (hv h.symm)
  · exact hyz (hv h.symm)

/-- The zero count and the fiber bound also apply when a target coincides with a pin. -/
theorem two_pin_bound : H1 := by
  classical
  let X := {x : ℝ² // ∀ i : Fin 2, IsIntegral ℤ (x i)}
  intro S T hsub p hp q hq hpq P hP zeros
  let W := insert 0 (distanceSet S)
  let f := fun x : X => ![dist x p, dist x q]
  let Z := (Fintype.piFinset fun _ : Fin 2 => W).filter (fun u => MvPolynomial.eval u P = 0)
  have radius (x c : X) (hx : x ∈ S) (hc : c ∈ S) : dist x c ∈ W := by
    by_cases h : x = c
    · simp [W,h]
    · exact mem_insert_of_mem (mem_image.mpr ⟨(x,c),mem_offDiag.mpr ⟨hx,hc,h⟩,rfl⟩)
  have hm : ∀ x ∈ T, f x ∈ Z := by
    intro x hx
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_,zeros x hx⟩
    intro i
    fin_cases i
    · exact radius x p (hsub hx) hp
    · exact radius x q (hsub hx) hq
  have hc := card_le_mul_card_image_of_maps_to hm 2 (by
    intro u _
    apply two_pin_fiber (fun x : X => x.val) Subtype.val_injective _ p q hpq (u 0) (u 1)
    · intro x hx
      exact congrFun (mem_filter.mp hx).2 0
    · intro x hx
      exact congrFun (mem_filter.mp hx).2 1)
  have hw : W.card ≤ distinctDistances S+1 := card_insert_le ..
  calc
    _ ≤ 2*Z.card := hc
    _ ≤ 2*(P.totalDegree*W.card) := Nat.mul_le_mul_left _ (grid_zeros W P hP)
    _ ≤ 2*(P.totalDegree*(distinctDistances S+1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hw)
    _ = _ := by ring

end Pins

theorem main : H1 → H2 → OMA.R_Erdos89_erdos_89_R1.H2 := by
  classical
  rintro bound ⟨C₀,hard⟩
  let C := max C₀ 4
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
    by_cases small : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ P : MvPolynomial (Fin 2) ℝ,
        P ≠ 0 → P.totalDegree ≤ k →
        2*(S.filter fun x => MvPolynomial.eval ![dist x p, dist x q] P = 0).card < S.card
    · have hh := hard S k hk (hS ▸ hcap) (by simpa [hS] using hD) small
      exact hh.trans (by dsimp [C]; gcongr; omega)
    push Not at small
    obtain ⟨p,hp,q,hq,hpq,P,hP,hdeg,hhalf⟩ := small
    let T := S.filter fun x => MvPolynomial.eval ![dist x p, dist x q] P = 0
    have he := bound S T (filter_subset ..) p hp q hq hpq P hP (fun _ h => (mem_filter.mp h).2)
    calc
      _ ≤ 2*T.card := hhalf
      _ ≤ 2*(2*P.totalDegree*(distinctDistances S+1)) := Nat.mul_le_mul_left _ he
      _ = P.totalDegree*4*(distinctDistances S+1) := by ring
      _ ≤ _ := by gcongr; dsimp [C]; omega
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

end OMA.R_Erdos89_erdos_89_R1_H2_R2
