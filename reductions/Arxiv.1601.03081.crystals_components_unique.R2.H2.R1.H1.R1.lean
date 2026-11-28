import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R2_H2_R1

/-! Classify the two coordinate pairs by Vieta descent. Order the resulting orbit indices
by monotonicity, and use consecutive squares to exclude square products of coefficients. -/

-- Reduction Arxiv.1601.03081.crystals_components_unique.R2.H2.R1.H1.R1 of step Arxiv.1601.03081.crystals_components_unique.R2.H2.R1.H1
-- Credit: @lettucrisp

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R2_H2_R1_H1_R1
theorem coefficient_bounds {q r t : ℕ} (hr : 1 < r) (ht : 0 < t)
    (h : r^2 + q*t^2 = q*r*t + 1) :
    t < r ∧ q ≤ r+1 ∧ (4 ≤ q ∨ (q = 3 ∧ r = 2 ∧ t = 1)) := by
  have htr : t < r := by
    by_contra! hn
    have := Nat.mul_le_mul_left (q*t) hn
    nlinarith [Nat.mul_self_le_mul_self (show 2 ≤ r by omega)]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show t+1 ≤ r by omega)
  have hu : q ≤ r+1 := by
    by_contra! hn
    have ha : r ≤ t*(d+1)+1 := by
      nlinarith [Nat.mul_le_mul_right d (show 1 ≤ t by omega)]
    have hb := Nat.mul_le_mul (show r+2 ≤ q by omega) (show r-1 ≤ t*(d+1) by omega)
    have hr' : r-1+1 = r := by omega
    nlinarith [congrArg (fun x : ℕ => (r+2)*x) hr', hd]
  refine ⟨htr, hu, ?_⟩
  by_cases hq : 4 ≤ q
  · exact Or.inl hq
  right
  have hb := Nat.mul_le_mul_right (t*(d+1)) (show q ≤ 3 by omega)
  have hsq := sq_nonneg ((t : ℤ) - (d+1 : ℕ))
  rw [hd] at h
  push_cast at hsq
  zify at hb h ht ⊢
  have he : (t : ℤ)*(d+1) ≤ 1 := by nlinarith
  have hd0 : d = 0 := by nlinarith [Nat.mul_le_mul_right d (show 1 ≤ t by omega)]
  subst d
  norm_num at *
  obtain rfl : t = 1 := by omega
  norm_num at *
  subst r
  norm_num at *
  omega

theorem collision_bounds {N q r t m Q R T k : ℕ}
    (hr : 1 < r) (ht : 0 < t) (hR : 1 < R) (hT : 0 < T)
    (h : r^2+q*t^2 = q*r*t+1) (H : R^2+Q*T^2 = Q*R*T+1)
    (hk : k+1 = 2*R*T) (hm : 3 ≤ m) (hlt : m < k)
    (hN : N = q*m*(m+1)) (hN' : N = Q*k*(k+1)) :
    4 ≤ Q ∧ Q < q ∧ q ≤ r+1 := by
  obtain ⟨_, hu, _⟩ := coefficient_bounds hr ht h
  have hQ : 4 ≤ Q := by
    obtain ⟨_, _, he⟩ := coefficient_bounds hR hT H
    rcases he with he | ⟨rfl,rfl,rfl⟩
    · exact he
    · omega
  refine ⟨hQ, ?_, hu⟩
  by_contra! hn
  have ha := Nat.mul_le_mul_right (m*(m+1)) hn
  have hb := Nat.mul_lt_mul_of_pos_left
    (show m*(m+1) < k*(k+1) by gcongr) (by omega : 0 < Q)
  nlinarith
section
variable (orbit : ℕ → ℕ → ℕ × ℕ)
  (base : ∀ d, orbit d 0 = (0,1))
  (step : ∀ d n, orbit d (n+1) = ((orbit d n).1+(orbit d n).2,
    (orbit d n).2+d*((orbit d n).1+(orbit d n).2)))
include base step
private theorem enumerate {d a b : ℕ} (hab : a ≤ b)
    (h : a^2+b^2 = (d+2)*a*b+1) :
    ∃ n, (orbit d n).1 = a ∧ (orbit d n).1 + (orbit d n).2 = b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases ha : a = 0
    · subst a
      simp at h
      exact ⟨0, by simp [base], by simp [base]; nlinarith⟩
    have hab' : a < b := by
      by_contra! hh
      obtain rfl : a = b := by omega
      nlinarith [Nat.zero_le (d*a*a)]
    have hprod : b ≤ (d+2)*a := by
      by_contra! hn
      have := Nat.mul_le_mul_right b (show (d+2)*a+1 ≤ b by omega)
      nlinarith [Nat.mul_self_le_mul_self (show 1 ≤ a by omega)]
    let c := (d+2)*a-b
    have hc : c+b = (d+2)*a := Nat.sub_add_cancel hprod
    have hcb : c*b+1 = a^2 := by nlinarith [congrArg (fun x : ℕ => x*b) hc]
    have hca : c ≤ a := by
      by_contra! hn
      have := Nat.mul_le_mul hn.le hab
      nlinarith
    have he : c^2+a^2 = (d+2)*c*a+1 := by
      nlinarith [congrArg (fun x : ℕ => x*c) hc]
    obtain ⟨n,hn,hs⟩ := ih a hab' hca he
    refine ⟨n+1, ?_, ?_⟩
    · simpa [step,base] using hs
    · simp only [step, hs]
      nlinarith

variable (cofactor : ℕ → ℕ → Bool → ℕ)
  (formula : ∀ d n e, cofactor d n e = 2*(2*(orbit d n).1+(orbit d n).2)*
    (if e then (orbit d n).1+(orbit d n).2 else (orbit d n).1)-1)
include formula

private theorem represented {d r t m : ℕ} (ht : t < r)
    (h : r^2+(d+4)*t^2 = (d+4)*r*t+1) (hm : m+1 = 2*r*t) :
    ∃ n e, m = cofactor d n e ∧ r = 2*(orbit d n).1 + (orbit d n).2 := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht.le
  have eqn : t^2+u^2 = (d+2)*t*u+1 := by nlinarith
  rcases le_total t u with htu | hut
  · obtain ⟨n,ha,hb⟩ := enumerate orbit base step htu eqn
    refine ⟨n,false,?_,by omega⟩
    simp only [formula, Bool.false_eq_true, ↓reduceIte]
    have hs : 2*(orbit d n).1 + (orbit d n).2 = t+u := by omega
    rw [hs, ha]
    omega
  · obtain ⟨n,ha,hb⟩ := enumerate orbit base step hut (by nlinarith)
    refine ⟨n,true,?_,by omega⟩
    simp only [formula, ↓reduceIte]
    rw [hb]
    have hs : 2*(orbit d n).1 + (orbit d n).2 = t+u := by omega
    rw [hs]
    omega

omit base step formula in
private theorem nonsquare {q Q m k : ℕ} (hpos : 0 < Q) (hQ : Q < q) (hu : q ≤ m+1)
    (h : q*m*(m+1) = Q*k*(k+1)) : ¬ IsSquare (q*Q) := by
  rintro ⟨s,hs⟩
  let A := q*(2*m+1)
  let B := s*(2*k+1)
  have he : A^2 + q*Q = B^2 + q*q := by
    dsimp [A,B]
    nlinarith only [congrArg (fun x : ℕ => 4*q*x) h,
      congrArg (fun x : ℕ => x*(2*k+1)^2) hs]
  have hlt : B < A := by
    by_contra! hn
    have := Nat.pow_le_pow_left hn 2
    have := Nat.mul_lt_mul_of_pos_left hQ (by omega : 0 < q)
    nlinarith
  have hg : A ≤ A^2-B^2 := by
    have := Nat.mul_le_mul_left A (show B+1 ≤ A by omega)
    have := Nat.mul_le_mul_right B hlt.le
    nlinarith [Nat.sub_add_cancel (Nat.pow_le_pow_left hlt.le 2)]
  have hsmall : q*q ≤ A := Nat.mul_le_mul_left _ (by omega)
  have : 0 < q*Q := Nat.mul_pos (by omega) hpos
  omega

omit formula in
private theorem orbit_parameter {d D : ℕ} (hd : D ≤ d) (n : ℕ) :
    (orbit D n).1 ≤ (orbit d n).1 ∧ (orbit D n).2 ≤ (orbit d n).2 := by
  induction n with
  | zero => simp [base]
  | succ n ih =>
    simp only [step]
    constructor <;> gcongr <;> omega

omit base formula in
private theorem orbit_time (d : ℕ) : Monotone (fun n => (orbit d n).1) ∧
    Monotone (fun n => (orbit d n).2) := by
  constructor <;> apply monotone_nat_of_le_succ <;> intro n <;> simp [step]

private theorem index_order {d D n j : ℕ} {e f : Bool} (hD : D ≤ d)
    (hlt : cofactor d n e < cofactor D j f) : n ≤ j := by
  by_contra! hn
  have h1 := (orbit_time orbit step d).1 (show j+1 ≤ n by omega)
  have h2 := (orbit_time orbit step d).2 (show j+1 ≤ n by omega)
  have hp := orbit_parameter orbit base step hD j
  simp only [step] at h1 h2
  have ha : (orbit D j).1 + (orbit D j).2 ≤ (orbit d n).1 := by omega
  have hr : 2*(orbit D j).1+(orbit D j).2 ≤ 2*(orbit d n).1+(orbit d n).2 := by omega
  have hle : cofactor D j f ≤ cofactor d n e := by
    cases f <;> cases e <;> simp only [formula, Bool.false_eq_true, ↓reduceIte] <;>
      apply Nat.sub_le_sub_right <;> gcongr <;> omega
  omega

omit formula in
private theorem orbit_zero (j : ℕ) : orbit 0 j = (j,1) := by
  induction j with
  | zero => exact base 0
  | succ j ih => simp [step, ih]

end

/-- Parabolic branch: the larger cofactor belongs to one of two explicit quadratics. -/
def H1 : Prop :=
  let orbit (d n : ℕ) := ((fun z : ℕ × ℕ => (z.1+z.2,z.2+d*(z.1+z.2)))^[n]) (0,1)
  let cofactor (d n : ℕ) (e : Bool) := let z := orbit d n
    2*(2*z.1+z.2)*(if e then z.1+z.2 else z.1)-1
  ∀ d n j : ℕ, ∀ e f : Bool, 0 < d → n ≤ j →
  ¬ IsSquare ((d+4)*4) →
  let m := cofactor d n e
  let k := 2*(2*j+1)*(if f then j+1 else j)-1
  let N := (d+4)*m*(m+1)
  m < k → (¬ m ∣ k) →
  (∀ p v : ℕ, p.Prime → p^v ∣ k → ¬ p ∣ m → p^v ≤ 2*(orbit d n).1+(orbit d n).2+1) →
  (∃ p l s : ℕ, p.Prime ∧ l.Prime ∧ s.Prime ∧ p ≠ l ∧ p ∣ k ∧ l ∣ k ∧
    s ≠ 2 ∧ s ∣ N ∧ ¬ s ∣ k) →
  N+1 ≠ (2*k+1)^2

/-- Hyperbolic branch: both cofactors come from indexed, increasing coefficient families. -/
def H2 : Prop :=
  let orbit (d n : ℕ) := ((fun z : ℕ × ℕ => (z.1+z.2,z.2+d*(z.1+z.2)))^[n]) (0,1)
  let cofactor (d n : ℕ) (e : Bool) := let z := orbit d n
    2*(2*z.1+z.2)*(if e then z.1+z.2 else z.1)-1
  ∀ d D n j : ℕ, ∀ e f : Bool, 0 < D → D < d → n ≤ j →
  ¬ IsSquare ((d+4)*(D+4)) →
  let m := cofactor d n e
  let k := cofactor D j f
  let N := (d+4)*m*(m+1)
  m < k → (¬ m ∣ k) →
  (∀ p v : ℕ, p.Prime → p^v ∣ k → ¬ p ∣ m → p^v ≤ 2*(orbit d n).1+(orbit d n).2+1) →
  (∃ p l s : ℕ, p.Prime ∧ l.Prime ∧ s.Prime ∧ p ≠ l ∧ p ∣ k ∧ l ∣ k ∧
    s ≠ 2 ∧ s ∣ N ∧ ¬ s ∣ k) →
  N ≠ (D+4)*k*(k+1)

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R2_H2_R1.H1 := by
  intro h1 h2 N q r t m Q R T k hr ht hR hT h H hm hk hm3 hmk hN hN' hdiv hpow hpr
  obtain ⟨h4,hQ,hu⟩ := collision_bounds hr ht hR hT h H hk hm3 hmk hN hN'
  have htr := (coefficient_bounds hr ht h).1
  have hTR := (coefficient_bounds hR hT H).1
  have hu' : q ≤ m+1 := by
    have := Nat.le_mul_of_pos_right (2*r) ht
    omega
  have hsq := nonsquare (by omega : 0 < Q) hQ hu' (hN.symm.trans hN')
  obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_le h4
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show 4 ≤ q by omega)
  rw [Nat.add_comm] at hD hd
  subst q
  subst Q
  let orbit (d n : ℕ) := ((fun z : ℕ × ℕ => (z.1+z.2,z.2+d*(z.1+z.2)))^[n]) (0,1)
  let cofactor (d n : ℕ) (e : Bool) := let z := orbit d n
    2*(2*z.1+z.2)*(if e then z.1+z.2 else z.1)-1
  have base (d : ℕ) : orbit d 0 = (0,1) := rfl
  have step (d n : ℕ) : orbit d (n+1) = ((orbit d n).1+(orbit d n).2,
      (orbit d n).2+d*((orbit d n).1+(orbit d n).2)) :=
    Function.iterate_succ_apply' _ _ _
  have formula (d n : ℕ) (e : Bool) : cofactor d n e = 2*(2*(orbit d n).1+(orbit d n).2)*
      (if e then (orbit d n).1+(orbit d n).2 else (orbit d n).1)-1 := rfl
  obtain ⟨n,e,hn,hrn⟩ := represented orbit base step cofactor formula htr h hm
  obtain ⟨j,f,hj,_⟩ := represented orbit base step cofactor formula hTR H hk
  subst m
  subst k
  have hij := index_order orbit base step cofactor formula (by omega : D ≤ d) hmk
  rw [hrn] at hpow
  subst N
  cases D with
  | zero =>
    have hz : cofactor 0 j f = 2*(2*j+1)*(if f then j+1 else j)-1 := by
      rw [formula, orbit_zero orbit base step]
    rw [hz] at hmk hdiv hpow hpr hN'
    have hnq := h1 d n j e f (by omega) hij hsq hmk hdiv hpow hpr
    apply hnq
    nlinarith only [hN']
  | succ D =>
    exact h2 d (D+1) n j e f (by omega) (by omega) hij hsq hmk hdiv hpow hpr hN'

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R2_H2_R1_H1_R1
