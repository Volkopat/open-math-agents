import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1.R2 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1
-- Credit: @Pixelstorm44

/-!
# From prime cyclic groups to intervals

Cast an interval into a prime cyclic group of order between twice and four times its length.
Sums of two interval elements lie below the modulus. Consequently consecutive gaps of a
modular progression agree as integers, and reversing a decreasing progression supplies a
positive step. A popular-sum fiber also yields a centrally symmetric subset of at least squared density.
The only open input is a cyclic estimate for sets invariant under negation.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2

/-- A density estimate confined to prime cyclic groups. All progressions here are modular. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ (p : ℕ), p.Prime → 3 ≤ p → ∀ A : Finset (ZMod p),
      (∀ x ∈ A, -x ∈ A) →
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i < k, a + (i : ZMod p) * d ∈ A) →
        (A.card : ℝ) ≤ C * p * Real.exp (-c * (Real.log (Real.log p)) ^ (1 + η))

/-- A modular progression in a short interval lifts to a positive-step progression. -/
def H2 : Prop :=
  ∀ (k N p : ℕ), 2 ≤ k → 2 * N < p → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
    (∃ a d : ZMod p, d ≠ 0 ∧ ∀ i < k, a + (i : ZMod p) * d ∈ S.image (fun n : ℕ ↦ (n : ZMod p))) →
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- Two sums of representatives in the interval are equal if congruent modulo p. -/
lemma eq_of_cast_lt {p a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using congrArg ZMod.val h

theorem lift_progression : H2 := by
  classical
  intro k N p hk hp S hS
  rintro ⟨a, d, hd, hap⟩
  let x (i : ℕ) := (a + (i : ZMod p) * d).val
  have lift (i : ℕ) (hi : i < k) : x i ∈ S ∧ x i ≤ N ∧ (x i : ZMod p) = a + (i : ZMod p) * d := by
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (hap i hi)
    have hnN := (Finset.mem_Icc.mp (hS hn)).2
    have hx : x i = n := by
      dsimp [x]
      rw [← he]
      exact ZMod.val_natCast_of_lt (by omega)
    rw [hx]
    exact ⟨hn, hnN, he⟩
  have h0 := lift 0 (by omega)
  have h1 := lift 1 (by omega)
  have distinct : x 0 ≠ x 1 := by
    intro h
    have he : a + (0 : ZMod p) * d = a + 1 * d := by
      simpa only [Nat.cast_zero, Nat.cast_one] using h0.2.2.symm.trans ((congrArg (fun n : ℕ ↦ (n : ZMod p)) h).trans h1.2.2)
    exact hd (by simpa using he.symm)
  have step (i : ℕ) (hi : i + 1 < k) : x (i+1) + x 0 = x i + x 1 := by
    have hu := lift (i+1) hi
    have hv := lift i (by omega)
    apply eq_of_cast_lt (p := p) (by omega) (by omega)
    rw [Nat.cast_add, Nat.cast_add, hu.2.2, h0.2.2, hv.2.2, h1.2.2]
    push_cast
    ring
  by_cases hinc : x 0 < x 1
  · let g := x 1 - x 0
    have hg : g + x 0 = x 1 := Nat.sub_add_cancel hinc.le
    refine ⟨x 0, g, by dsimp [g]; omega, ?_⟩
    have formula (i : ℕ) (hi : i < k) : x 0 + i*g = x i := by
      induction i with
      | zero => simp
      | succ i ih =>
        rw [Nat.succ_mul]
        have := step i hi
        have := ih (by omega)
        omega
    intro i hi
    rw [formula i hi]
    exact (lift i hi).1
  · let g := x 0 - x 1
    have hg : g + x 1 = x 0 := Nat.sub_add_cancel (by omega)
    have formula (i : ℕ) (hi : i < k) : x i + i*g = x 0 := by
      induction i with
      | zero => simp
      | succ i ih =>
        rw [Nat.succ_mul]
        have := step i hi
        have := ih (by omega)
        omega
    refine ⟨x (k-1), g, by dsimp [g]; omega, ?_⟩
    intro i hi
    have hj : k-1-i < k := by omega
    have decomp : (k-1-i)*g + i*g = (k-1)*g := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    have hend := formula (k-1) (by omega)
    have hrev := formula (k-1-i) hj
    have he : x (k-1) + i*g = x (k-1-i) := by omega
    rw [he]
    exact (lift _ hj).1

/-- A popular sum gives a reflection-invariant subset retaining the square of the density. -/
lemma popular_reflection {p : ℕ} [NeZero p] (A : Finset (ZMod p)) :
    ∃ (t : ZMod p) (B : Finset (ZMod p)), B ⊆ A ∧
      (∀ x ∈ B, t-x ∈ B) ∧ A.card*A.card ≤ p*B.card := by
  classical
  let P := A ×ˢ A
  let sumPair (z : ZMod p × ZMod p) := z.1 + z.2
  let F (t : ZMod p) := P.filter fun z ↦ sumPair z = t
  obtain ⟨t, _, hmax⟩ := Finset.univ.exists_max_image (fun t ↦ (F t).card) Finset.univ_nonempty
  have hmass : A.card*A.card ≤ p*(F t).card := by
    calc
      A.card*A.card = P.card := (Finset.card_product _ _).symm
      _ = ∑ j ∈ (Finset.univ : Finset (ZMod p)), (F j).card :=
        Finset.card_eq_sum_card_fiberwise (f := sumPair) (fun _ _ ↦ Finset.mem_univ _)
      _ ≤ ∑ _j ∈ (Finset.univ : Finset (ZMod p)), (F t).card := Finset.sum_le_sum hmax
      _ = _ := by simp [ZMod.card]
  let B := (F t).image Prod.fst
  have spec {z : ZMod p × ZMod p} (hz : z ∈ F t) :
      z.1 ∈ A ∧ z.2 ∈ A ∧ z.1 + z.2 = t := by
    obtain ⟨h, he⟩ := Finset.mem_filter.mp hz
    obtain ⟨hl, hr⟩ := Finset.mem_product.mp h
    exact ⟨hl, hr, he⟩
  have card : B.card = (F t).card := by
    apply Finset.card_image_of_injOn
    intro z hz w hw he
    apply Prod.ext he
    exact add_left_cancel ((spec hz).2.2.trans (by rw [he]; exact (spec hw).2.2.symm))
  refine ⟨t, B, ?_, ?_, card.symm ▸ hmass⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact (spec hz).1
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hl, hr, he⟩ := spec hz
    refine Finset.mem_image.mpr ⟨(z.2,z.1), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hr,hl⟩, (add_comm _ _).trans he⟩, ?_⟩
    change z.2 = t-z.1
    rw [← he]
    abel

/-- On an odd prime group, translate the center of a popular reflection to zero.
Taking the square root of the density estimate halves the exponential coefficient. -/
lemma cyclic_of_symmetric (h : H1) (k : ℕ) (hk : 4 ≤ k) :
    ∃ K c η : ℝ, 0 < K ∧ 0 < c ∧ 0 < η ∧
      ∀ (p : ℕ), p.Prime → 3 ≤ p → ∀ A : Finset (ZMod p),
        (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i < k, a + (i : ZMod p) * d ∈ A) →
          (A.card : ℝ) ≤ K*p*Real.exp (-c*(Real.log (Real.log p))^(1+η)) := by
  classical
  obtain ⟨C,c,η,hC,hc,hη,estimate⟩ := h k hk
  refine ⟨Real.sqrt C,c/2,η,Real.sqrt_pos.mpr hC,by positivity,hη,?_⟩
  intro p hp hp3 A hfree
  let : Fact p.Prime := ⟨hp⟩
  have two_ne : (2 : ZMod p) ≠ 0 := by
    intro he
    have hh : ((2 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using he
    have := eq_of_cast_lt (by omega : 2 < p) (by omega : 0 < p) hh
    omega
  obtain ⟨t,B,hBA,hsym,hmass⟩ := popular_reflection A
  let u := t / 2
  have hcenter : u+u = t := by
    dsimp [u]
    field_simp
    ring
  let D := B.image fun x ↦ x-u
  have hD : D.card = B.card := by
    apply Finset.card_image_of_injective
    intro x y he
    change x-u = y-u at he
    simpa using congrArg (fun z ↦ z+u) he
  have hsD : ∀ x ∈ D, -x ∈ D := by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨t-b, hsym b hb, ?_⟩
    rw [← hcenter]
    abel
  have hfD : ¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i < k, a + (i : ZMod p)*d ∈ D := by
    rintro ⟨a,d,hd,hm⟩
    apply hfree
    refine ⟨a+u,d,hd,?_⟩
    intro i hi
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp (hm i hi)
    apply hBA
    convert hb using 1
    change b-u = a+ (i : ZMod p)*d at he
    rw [show a+u+(i : ZMod p)*d = (a+(i : ZMod p)*d)+u by abel, ← he]
    simp
  have hbound := estimate p hp hp3 D hsD hfD
  rw [hD] at hbound
  let L := (Real.log (Real.log (p : ℝ)))^(1+η)
  have hm : (A.card : ℝ)*(A.card : ℝ) ≤ (p : ℝ)*B.card := by exact_mod_cast hmass
  let E := Real.exp (-(c/2)*L)
  have hE : E*E = Real.exp (-c*L) := by
    dsimp [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : (A.card : ℝ)^2 ≤ (Real.sqrt C*p*E)^2 := by
    calc
      (A.card : ℝ)^2 ≤ (p : ℝ)*B.card := by simpa [pow_two] using hm
      _ ≤ (p : ℝ)*(C*p*Real.exp (-c*L)) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by rw [← hE, mul_pow, mul_pow, Real.sq_sqrt hC.le]; ring
  have hpos : 0 ≤ Real.sqrt C*p*E := mul_nonneg (by positivity) (Real.exp_pos _).le
  exact (sq_le_sq₀ (Nat.cast_nonneg _) hpos).mp hs

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H1 := by
  classical
  intro cyclic lift k hk
  obtain ⟨C, c, η, hC, hc, hη, hbound⟩ := cyclic_of_symmetric cyclic k hk
  refine ⟨4*C, c, η, by positivity, hc, hη, ?_⟩
  intro N S hN hS hfree
  obtain ⟨p, hprime, hp, hp'⟩ := Nat.exists_prime_lt_and_le_two_mul (2*N) (by omega)
  let A := S.image fun n : ℕ ↦ (n : ZMod p)
  have hinj : A.card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy he
    have h1 := (Finset.mem_Icc.mp (hS hx)).2
    have h2 := (Finset.mem_Icc.mp (hS hy)).2
    exact eq_of_cast_lt (by omega) (by omega) he
  have hA := hbound p hprime (by omega) A (fun h ↦ hfree (lift k N p (by omega) hp S hS h))
  rw [hinj] at hA
  have hn3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 1 ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (Real.exp_one_lt_three.le.trans hn3)
  have hNP : (N : ℝ) ≤ p := by exact_mod_cast (show N ≤ p by omega)
  have hlog' := Real.log_le_log (by linarith : 0 < (N : ℝ)) hNP
  have hll := Real.log_le_log (by linarith : 0 < Real.log (N : ℝ)) hlog'
  have hpow := Real.rpow_le_rpow (Real.log_nonneg hlog) hll (by linarith : 0 ≤ 1+η)
  have hfac := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hpow (by linarith : -c ≤ 0))
  have hp4 : (p : ℝ) ≤ 4 * N := by exact_mod_cast (show p ≤ 4*N by omega)
  calc
    (S.card : ℝ) ≤ _ := hA
    _ ≤ C * (4 * (N : ℝ)) * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp4 hC.le) hfac (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2
