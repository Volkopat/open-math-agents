import OMAStatements.S_oeis_a275675

/-!
# A275675 via three squares and a mixed representation

After scaling away factors of four, the exponent-zero case follows from
Legendre's three-square theorem applied to five times the shifted input.
For the exceptional family, exponent one suffices given the mixed
representation in H2. The kernel checks the original conjecture through
one million, including the two small exceptions to the mixed form.
-/

namespace OMA.R_oeis_a275675_R1

/-- Cancel a factor of five without changing the parity of the valuations at primes 3 mod 4. -/
private theorem cancel_five_two_squares {n a b : ℕ} (h : 5*n = a^2+b^2) :
    ∃ x y : ℕ, n = x^2 + y^2 := by
  apply Nat.eq_sq_add_sq_iff.mpr
  have h5 := Nat.eq_sq_add_sq_iff.mp ⟨a,b,h⟩
  intro p hp hp4
  have pp := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨pp⟩
  have hn : n ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  have hprod : 5*n ≠ 0 := Nat.mul_ne_zero (by decide) hn
  have hmem : p ∈ (5*n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨pp,(Nat.dvd_of_mem_primeFactors hp).trans (dvd_mul_left n 5),hprod⟩
  have hcop : ¬ p ∣ 5 := by
    intro hd
    have he := (Nat.dvd_prime (by decide : Nat.Prime 5)).1 hd
    rcases he with rfl | rfl <;> norm_num at hp4
  simpa only [padicValNat.mul (by decide : 5 ≠ 0) hn, padicValNat.eq_zero_of_not_dvd hcop,
    zero_add] using h5 p hmem hp4

private theorem descend_five_squares {m u v w : ℕ} (h : 5*m=u^2+v^2+w^2) :
    ∃ x y z : ℕ, m=x^2+y^2+5*z^2 := by
  have hres : ∀ i j k : ZMod 5, i^2+j^2+k^2=0 → i=0 ∨ j=0 ∨ k=0 := by decide +kernel
  have hzero : (u:ZMod 5)^2 + (v:ZMod 5)^2 + (w:ZMod 5)^2 = 0 := by
    have hv := congrArg (fun n : ℕ => (n : ZMod 5)) h
    simpa [show (5 : ZMod 5) = 0 by decide] using hv.symm
  have hd := hres u v w hzero
  simp only [ZMod.natCast_eq_zero_iff] at hd
  have finish : ∀ a b c : ℕ, 5 ∣ c → 5*m = a^2+b^2+c^2 →
      ∃ x y z : ℕ, m=x^2+y^2+5*z^2 := by
    rintro a b c ⟨z,rfl⟩ heq
    have hz : (5*z)^2 = 5*(5*z^2) := by ring
    rw [hz] at heq
    have hle : 5*z^2 ≤ m := by omega
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hle
    have hpair : 5*d = a^2+b^2 := by omega
    obtain ⟨x,y,hxy⟩ := cancel_five_two_squares hpair
    exact ⟨x,y,z,by omega⟩
  rcases hd with hu | hv | hw
  · exact finish v w u hu (by simpa only [add_assoc, add_comm, add_left_comm] using h)
  · exact finish u w v hv (by simpa only [add_assoc, add_comm, add_left_comm] using h)
  · exact finish u v w hw h

private theorem five_mul_exception {m a b : ℕ} (h : 5*m = 4^a*(8*b+7)) :
    ∃ c : ℕ, m = 4^a*(8*c+3) := by
  induction a generalizing m with
  | zero =>
    simp only [pow_zero, one_mul] at h ⊢
    exact ⟨m / 8, by omega⟩
  | succ a ih =>
    rw [pow_succ', mul_assoc] at h
    obtain ⟨u, rfl⟩ : 4 ∣ m := by omega
    obtain ⟨c, hc⟩ := ih (m := u) (by omega)
    exact ⟨c, by rw [pow_succ', mul_assoc, hc]⟩

private theorem five_mul_avoids_three_squares_obstruction {m : ℕ}
    (h : ¬ ∃ a b : ℕ, m = 4^a*(8*b+3)) :
    ¬ ∃ a b : ℕ, 5*m = 4^a*(8*b+7) := by
  rintro ⟨a,b,hab⟩
  obtain ⟨c,hc⟩ := five_mul_exception hab
  exact h ⟨a,c,hc⟩

private theorem first_form_of_three_squares
    (legendre : ∀ n : ℕ, (¬ ∃ a b : ℕ, n=4^a*(8*b+7)) →
      ∃ u v w : ℕ, n = u^2+v^2+w^2)
    {m : ℕ} (hm : ¬ ∃ a b : ℕ, m=4^a*(8*b+3)) :
    ∃ x y z : ℕ, m=x^2+y^2+5*z^2 := by
  obtain ⟨u,v,w,h⟩ := legendre (5*m) (five_mul_avoids_three_squares_obstruction hm)
  exact descend_five_squares h

private theorem form_residue (m x y z : ℕ) :
    (x%m)^2 + (y%m)^2 + 5*(z%m)^2 ≡ x^2 + y^2 + 5*z^2 [MOD m] :=
  (((Nat.mod_modEq x m).pow 2).add ((Nat.mod_modEq y m).pow 2)).add
    (((Nat.mod_modEq z m).pow 2).mul_left 5)

/-- The exceptional family in H1 cannot be represented by the first form. -/
theorem first_form_obstruction (a b x y z : ℕ) :
    x^2 + y^2 + 5*z^2 ≠ 4^a*(8*b+3) := by
  induction a generalizing x y z with
  | zero =>
    intro h
    have hm : (x^2 + y^2 + 5*z^2) % 8 = 3 := by
      rw [h, pow_zero, one_mul]
      omega
    have hf : ∀ x y z : Fin 8, (x.val^2 + y.val^2 + 5*z.val^2) % 8 ≠ 3 := by
      decide +kernel
    exact hf ⟨x%8,by omega⟩ ⟨y%8,by omega⟩ ⟨z%8,by omega⟩
      ((form_residue 8 x y z).trans (show _ ≡ 3 [MOD 8] from hm))
  | succ a ih =>
    intro h
    rw [pow_succ' (4 : ℕ) a, mul_assoc] at h
    have hm : (x^2 + y^2 + 5*z^2) % 4 = 0 := by rw [h]; simp
    have hf : ∀ x y z : Fin 4, (x.val^2 + y.val^2 + 5*z.val^2) % 4 = 0 →
        x.val % 2 = 0 ∧ y.val % 2 = 0 ∧ z.val % 2 = 0 := by decide +kernel
    have hs := hf ⟨x%4,by omega⟩ ⟨y%4,by omega⟩ ⟨z%4,by omega⟩
      ((form_residue 4 x y z).trans (show _ ≡ 0 [MOD 4] from hm))
    obtain ⟨u,rfl⟩ : 2 ∣ x := by simp only at hs; omega
    obtain ⟨v,rfl⟩ : 2 ∣ y := by simp only at hs; omega
    obtain ⟨w,rfl⟩ : 2 ∣ z := by simp only at hs; omega
    have hscale : (2*u)^2 + (2*v)^2 + 5*(2*w)^2 = 4*(u^2 + v^2 + 5*w^2) := by ring
    rw [hscale] at h
    exact ih u v w (by omega)

/-- The exceptional mixed values really do require different representations. -/
theorem no_mixed_at_exceptions (t : ℕ) (ht : t = 35 ∨ t = 59) :
    ¬ ∃ x y z : ℕ, t = 2 + x^2 + y^2 + 5*z*(z+1) := by
  rintro ⟨x,y,z,h⟩
  have hx : x < 8 := by
    by_contra! hx
    have hb := Nat.pow_le_pow_left hx 2
    omega
  have hy : y < 8 := by
    by_contra! hy
    have hb := Nat.pow_le_pow_left hy 2
    omega
  have hz : z < 8 := by
    by_contra! hz
    have hb := Nat.mul_le_mul hz (show 9 ≤ z+1 by omega)
    rw [mul_assoc 5 z] at h
    omega
  have hf : ∀ x y z : Fin 8, let c := 2 + x.val^2 + y.val^2 + 5*z.val*(z.val+1)
      c ≠ 35 ∧ c ≠ 59 := by decide +kernel
  have hn := hf ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩
  dsimp only at hn
  omega

private theorem ordered_representation {n k x y z : ℕ}
    (h : n = 4^k * (1 + x^2 + y^2) + 5*z^2) :
    ∃ k x y z : ℕ, x ≤ y ∧ n = 4^k * (1 + x^2 + y^2) + 5*z^2 := by
  rcases le_total x y with hxy | hyx
  · exact ⟨k,x,y,z,hxy,h⟩
  · exact ⟨k,y,x,z,hyx,by rw [h]; ring⟩

private theorem union_bit (f : ℕ → ℕ) (l : List ℕ) (j : ℕ)
    (h : (l.foldr (fun i acc => f i ||| acc) 0).testBit j = true) :
    ∃ i, (f i).testBit j = true := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true] at h
    exact h.elim (fun ha => ⟨a,ha⟩) ih

private theorem shifted_bit {mask i j : ℕ} (h : (mask <<< i).testBit j = true) :
    ∃ v, j = i+v ∧ mask.testBit v = true := by
  rw [Nat.testBit_shiftLeft] at h
  by_cases hij : i ≤ j
  · exact ⟨j-i, by omega, by simpa [hij] using h⟩
  · simp [hij] at h

theorem representation_through_1000000 {n : ℕ} (hn : 0 < n) (hb : n ≤ 1000000) :
    ∃ k x y z : ℕ, x ≤ y ∧ n = 4^k * (1 + x^2 + y^2) + 5*z^2 := by
  let union := fun (f : ℕ → ℕ) (r : ℕ) => (List.range r).reverse.foldr (fun i acc => f i ||| acc) 0
  let shifts := fun (f : ℕ → ℕ) (r mask : ℕ) => union (fun i => mask <<< f i) r
  -- Bounding one square coordinate and z selects sufficient witnesses for the checked interval.
  let inner := fun (k : ℕ) =>
    let d := 4^k
    let r := (1000000 / d).sqrt + 1
    let shift := fun i : ℕ => d * i^2
    shifts shift (min r 256) (shifts shift r 1) <<< (d-1)
  let mask := shifts (fun z => 5*z^2) 128 (union inner 10)
  have cert : mask % 2^1000000 = 2^1000000 - 1 := by decide +kernel
  have hm := congrArg (fun m : ℕ => m.testBit (n-1)) cert
  have hj : n-1 < 1000000 := by omega
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, hj, decide_true, Bool.true_and] at hm
  obtain ⟨z,hz⟩ := union_bit _ _ _ hm
  obtain ⟨v,hv,h1⟩ := shifted_bit hz
  obtain ⟨k,hk⟩ := union_bit _ _ _ h1
  obtain ⟨w,hw,h2⟩ := shifted_bit hk
  obtain ⟨x,hx⟩ := union_bit _ _ _ h2
  obtain ⟨u,hu,h3⟩ := shifted_bit hx
  obtain ⟨y,hy⟩ := union_bit _ _ _ h3
  obtain ⟨o,ho,h4⟩ := shifted_bit hy
  have hz0 : o = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp h4
  have hd : 0 < (4:ℕ)^k := by positivity
  change n - 1 = 5*z^2+v at hv
  change v = 4^k-1+w at hw
  change w = 4^k*x^2+u at hu
  change u = 4^k*y^2+o at ho
  rcases le_total x y with hxy | hyx
  · exact ⟨k,x,y,z,hxy,by simp only [Nat.mul_add, Nat.mul_one]; omega⟩
  · exact ⟨k,y,x,z,hyx,by simp only [Nat.mul_add, Nat.mul_one]; omega⟩

theorem scale_representation (a m : ℕ)
    (h : ∃ k x y z : ℕ, x ≤ y ∧ m = 4^k * (1 + x^2 + y^2) + 5*z^2) :
    ∃ k x y z : ℕ, x ≤ y ∧ 4^a*m = 4^k * (1 + x^2 + y^2) + 5*z^2 := by
  obtain ⟨k,x,y,z,hxy,hm⟩ := h
  refine ⟨a+k,x,y,2^a*z,hxy,?_⟩
  have hp : (2^a : ℕ)^2 = 4^a := by rw [← pow_mul, Nat.mul_comm a 2, pow_mul]; rfl
  rw [hm, pow_add, mul_pow, hp]
  ring

/-- Every power-of-four multiple of a certified input also has a representation. -/
theorem small_scaled (a n : ℕ) (hn : 0 < n) (hb : n ≤ 1000000) :
    ∃ k x y z : ℕ, x ≤ y ∧ 4^a*n = 4^k * (1 + x^2 + y^2) + 5*z^2 :=
  scale_representation a n (representation_through_1000000 hn hb)

/-- Legendre's three-square theorem, in its natural-number representation direction. -/
def H1 : Prop := ∀ n : ℕ, (¬ ∃ a b : ℕ, n = 4^a * (8*b+7)) →
  ∃ u v w : ℕ, n = u^2 + v^2 + w^2

/-- The remaining large inputs to the mixed representation. -/
def H2 : Prop := ∀ t : ℕ, 249999 < t → (∃ a b : ℕ, t = 4^a * (8*b+3)) →
  ∃ x y z : ℕ, t = 2 + x^2 + y^2 + 5*z*(z+1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a275675.main := by
  intro h1 h2 n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hdiv : 4 ∣ n
    · obtain ⟨m,rfl⟩ := hdiv
      have hm : 0 < m := by omega
      simpa only [pow_one] using scale_representation 1 m (ih m (by omega) hm)
    by_cases hbad : ∃ a b : ℕ, n-1 = 4^a * (8*b+3)
    · obtain ⟨a,b,hab⟩ := hbad
      cases a with
      | zero =>
        simp at hab
        exact (hdiv ⟨2*b+1,by omega⟩).elim
      | succ a =>
        let t : ℕ := 4^a * (8*b+3)
        have hnEq : n = 4*t+1 := by
          rw [pow_succ', mul_assoc] at hab
          change n - 1 = 4*t at hab
          omega
        by_cases ht : t ≤ 249999
        · exact representation_through_1000000 hn (by omega)
        obtain ⟨x,y,z,ht⟩ := h2 t (by omega) ⟨a,b,rfl⟩
        apply ordered_representation (k := 1) (x := x) (y := y) (z := 2*z+1)
        rw [hnEq,ht]
        ring
    · obtain ⟨x,y,z,h⟩ := first_form_of_three_squares h1 hbad
      apply ordered_representation (k := 0) (x := x) (y := y) (z := z)
      simp only [pow_zero, one_mul]
      omega

end OMA.R_oeis_a275675_R1
