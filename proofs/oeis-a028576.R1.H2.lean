import OMAReductions.R_oeis_a028576_R1
import Mathlib

/-! Pairing odd factors reduces the binomial congruence to a sum of inverse squares. -/

open Finset

private def oddProd (n : ℕ) : ℕ := ∏ j ∈ range n, (2*j+1)

private theorem factorialSplit (n : ℕ) : (2*n).factorial = 2^n * n.factorial * oddProd n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ,
      ih, pow_succ, Nat.factorial_succ]
    simp only [oddProd, prod_range_succ]
    ring

private theorem binomialSplit (n : ℕ) :
    (2*(2*n)).choose (2*n) * oddProd n ^ 2 = (2*n).choose n * oddProd (2*n) := by
  let A := (2*(2*n)).choose (2*n)
  let B := (2*n).choose n
  have hA : A * ((2*n).factorial)^2 = (2*(2*n)).factorial := by
    simpa [A, two_mul, pow_two, mul_assoc] using Nat.add_choose_mul_factorial_mul_factorial (2*n) (2*n)
  have hB : B * (n.factorial)^2 = (2*n).factorial := by
    simpa [B, two_mul, pow_two, mul_assoc] using Nat.add_choose_mul_factorial_mul_factorial n n
  change A * oddProd n ^ 2 = B * oddProd (2*n)
  calc
    _ = _ := by
      have hapos : 0 < 2^(2*n) * n.factorial^2 := by positivity
      apply Nat.eq_of_mul_eq_mul_left hapos
      calc
        _ = A * ((2*n).factorial)^2 := by rw [factorialSplit n, show 2*n=n+n by omega, pow_add]; ring
        _ = (2*(2*n)).factorial := hA
        _ = _ := by rw [factorialSplit (2*n), ← hB]; ring

private theorem oddProdOdd (n : ℕ) : Odd (oddProd n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [oddProd, prod_range_succ]
    exact ih.mul ⟨n, by omega⟩

private theorem pairedShift {R : Type*} [CommRing R] (l : ℕ) (s : R) :
    (∏ j ∈ range (2*l), (2*(j : R)+1+s)) =
      ∏ j ∈ range l, ((2*(j : R)+1+s) * (4*(l : R)-(2*(j : R)+1)+s)) := by
  rw [two_mul l, prod_range_add]
  rw [← prod_range_reflect (fun j : ℕ => 2*((l+j : ℕ) : R)+1+s) l, ← prod_mul_distrib]
  apply prod_congr rfl
  intro j hj
  have h := mem_range.mp hj
  rw [show l+(l-1-j) = l+l-(j+1) by omega, Nat.cast_sub (by omega : j+1 ≤ l+l)]
  push_cast
  ring

private theorem splitShift {R : Type*} [CommRing R] (l : ℕ) :
    (∏ j ∈ range (4*l), (2*(j : R)+1)) =
      (∏ j ∈ range (2*l), (2*(j : R)+1)) *
        ∏ j ∈ range (2*l), (2*(j : R)+1+4*(l : R)) := by
  rw [show 4*l = 2*l+2*l by omega, prod_range_add]
  congr 1
  apply prod_congr rfl
  intro j _
  push_cast
  ring

private theorem pairedProduct {R : Type*} [CommRing R] (l : ℕ) :
    (∏ j ∈ range (4*l), (2*(j : R)+1)) =
      (∏ j ∈ range (2*l), (2*(j : R)+1)) *
        ∏ j ∈ range l,
          ((2*(j : R)+1) * (4*(l : R)-(2*(j : R)+1)) + 2*(4*(l : R))^2) := by
  rw [splitShift, pairedShift l (4*(l : R))]
  congr 1
  apply prod_congr rfl
  intro j _
  ring

private def oddUnit (s i : ℕ) : (ZMod (2^s))ˣ :=
  ZMod.unitOfCoprime (2*i+1) ((show Odd (2*i+1) from ⟨i, by omega⟩).coprime_two_right.pow_right _)

@[simp] private theorem coe_oddUnit (s i : ℕ) :
    (oddUnit s i : ZMod (2^s)) = 2*(i : ZMod (2^s))+1 := by
  simp [oddUnit]

private def oddEquiv (s : ℕ) : Fin (2^s) ≃ (ZMod (2^(s+1)))ˣ where
  toFun i := oddUnit (s+1) i
  invFun u := ⟨(u : ZMod (2^(s+1))).val / 2, by
    have h := ZMod.val_lt (u : ZMod (2^(s+1)))
    have h' : (u : ZMod (2^(s+1))).val < 2^s*2 := h
    omega⟩
  left_inv i := by
    apply Fin.ext
    change ((oddUnit (s+1) (i : ℕ) : ZMod (2^(s+1))).val / 2) = i
    rw [show (oddUnit (s+1) (i : ℕ) : ZMod (2^(s+1))) = ((2*(i : ℕ)+1 : ℕ) : ZMod (2^(s+1))) by simp,
      ZMod.val_natCast_of_lt]
    · omega
    · have hi := i.isLt
      rw [pow_succ]
      omega
  right_inv u := by
    have hcop := ZMod.val_coe_unit_coprime u
    have ho : Odd (u : ZMod (2^(s+1))).val := by
      rw [Nat.coprime_pow_right_iff (by omega : 0 < s+1)] at hcop
      exact hcop.odd_of_right
    have htwo := Nat.odd_iff.mp ho
    apply Units.ext
    change (oddUnit (s+1) ((u : ZMod (2^(s+1))).val/2) : ZMod (2^(s+1))) = u
    have h : 2*((u : ZMod (2^(s+1))).val/2)+1 = (u : ZMod (2^(s+1))).val := by omega
    simp [oddUnit, h, ZMod.natCast_val]

private theorem oddSquareSum {R : Type*} [CommRing R] (l : ℕ) :
    3 * (∑ j ∈ range l, (2*(j : R)+1)^2) = (l : R) * (4*(l : R)^2-1) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ]
    ring

private theorem sumBlocks {R : Type*} [AddCommMonoid R] {N : ℕ} (f : ℕ → R)
    (h : ∀ j, f (N+j) = f j) (k : ℕ) :
    (∑ j ∈ range (N*k), f j) = k • ∑ j ∈ range N, f j := by
  have h' (a j : ℕ) : f (N*a+j) = f j := by
    induction a with
    | zero => simp
    | succ a ih => rw [show N*(a+1)+j = N+(N*a+j) by ring, h, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, sum_range_add, ih, succ_nsmul]
    refine congrArg (_ + ·) (sum_congr rfl fun j _ => h' _ _)

private theorem invSquareSum (s d : ℕ) :
    (∑ j ∈ range (2^s*d), ((oddUnit s j)⁻¹ : ZMod (2^s))^2) = 0 := by
  cases s with
  | zero =>
    change _ = (0 : ZMod 1)
    exact Subsingleton.elim _ _
  | succ s =>
    classical
    let R := ZMod (2^(s+1))
    let f (j : ℕ) : R := ((oddUnit (s+1) j)⁻¹ : R)^2
    have hperiod (j : ℕ) : f (2^s+j) = f j := by
      have he : oddUnit (s+1) (2^s+j) = oddUnit (s+1) j := by
        apply Units.ext
        simp only [coe_oddUnit, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
        have hz : (2 : R)*2^s = 0 := by
          rw [← pow_succ']
          simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2^(s+1))
        linear_combination hz
      dsimp [f]
      rw [he]
    have hswap : (∑ j ∈ range (2^s), f j) = ∑ j ∈ range (2^s), (2*(j : R)+1)^2 := by
      rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
      let g (u : Rˣ) : R := (u : R)^2
      calc
        _ = ∑ u : Rˣ, g u⁻¹ := (oddEquiv s).sum_comp (fun u => g u⁻¹)
        _ = ∑ u : Rˣ, g u := Equiv.sum_comp (Equiv.inv Rˣ) g
        _ = _ := by
          rw [← (oddEquiv s).sum_comp g]
          apply sum_congr rfl
          intro j _
          simp [g, R, oddEquiv]
    change (∑ j ∈ range (2^(s+1)*d), f j) = 0
    rw [show 2^(s+1)*d = 2^s*(2*d) by rw [pow_succ]; ring, sumBlocks f hperiod, hswap, nsmul_eq_mul]
    have hthree : IsUnit (3 : R) := by
      have he : (oddUnit (s+1) 1 : R) = 3 := by norm_num [R]
      rw [← he]
      exact (oddUnit (s+1) 1).isUnit
    apply hthree.mul_left_cancel
    rw [mul_zero, mul_left_comm, oddSquareSum]
    have hz : (2 : R)*(2^s : ℕ) = 0 := by
      push_cast
      rw [← pow_succ']
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2^(s+1))
    calc
      _ = ((2 : R)*(2^s : ℕ)) * (d : R) * (4*((2^s : ℕ) : R)^2-1) := by
        push_cast
        ring
      _ = 0 := by rw [hz, zero_mul, zero_mul]

private theorem productPerturb {R : Type*} [CommRing R] (l : ℕ)
    (a : ℕ → Rˣ) {t : R} (ht : t*t=0) :
    (∏ j ∈ range l, ((a j : R)+t)) =
      (∏ j ∈ range l, (a j : R)) * (1+t*∑ j ∈ range l, (↑((a j)⁻¹) : R)) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [prod_range_succ, prod_range_succ, sum_range_succ, ih]
    have hunit : (a l : R) * (↑((a l)⁻¹) : R) = 1 := by simp
    generalize hA : ∏ j ∈ range l, (a j : R) = A
    generalize hS : ∑ j ∈ range l, (↑((a j)⁻¹) : R) = S
    linear_combination -A*t*hunit + A*S*ht

private theorem oddFactorCongruence (s d : ℕ) :
    (2 : ℤ)^(3*s+5) ∣ (oddProd (4*(2^s*d)) : ℤ) - (oddProd (2*(2^s*d)) : ℤ)^2 := by
  let m := 3*s+5
  let R := ZMod (2^m)
  let L := 2^s*d
  let x : R := (4 : R)*(L : R)
  let t : R := (↑(2^(2*s+5)*d^2 : ℕ) : R)
  let ρ : R →+* ZMod (2^s) := ZMod.castHom (pow_dvd_pow 2 (by dsimp [m]; omega)) _
  have hzero : ((2^m : ℕ) : R) = 0 := ZMod.natCast_self _
  have htmul : t * (↑(2^s : ℕ) : R) = 0 := by
    dsimp only [t]
    rw [← Nat.cast_mul, show 2^(2*s+5)*d^2*2^s = 2^m*d^2 by
      rw [mul_right_comm, ← pow_add]
      congr 2
      dsimp [m]
      omega, Nat.cast_mul, hzero, zero_mul]
  have htdiv : (2^s : ℕ) ∣ 2^(2*s+5)*d^2 :=
    dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) _
  have htt : t*t=0 := by
    obtain ⟨v, hv⟩ := htdiv
    conv_lhs =>
      enter [2]
      rw [show t = (↑(2^(2*s+5)*d^2 : ℕ) : R) by rfl, hv, Nat.cast_mul]
    rw [← mul_assoc, htmul, zero_mul]
  have ht : t = 2*x^2 := by
    have he : 2^(2*s+5)*d^2 = 2*(4*L)^2 := by
      dsimp [L]
      rw [pow_add, show 2*s = s*2 by omega, pow_mul]
      ring
    dsimp [t, x]
    rw [he, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul]
    rfl
  let u (j : ℕ) : Rˣ := oddUnit m j
  let v (j : ℕ) : Rˣ := oddUnit m (2*L-1-j)
  let a (j : ℕ) : Rˣ := u j * v j
  have hv (j : ℕ) (hj : j < L) : (v j : R) = x - (u j : R) := by
    simp only [v, u, coe_oddUnit, x]
    rw [show 2*L-1-j = 2*L-(j+1) by omega, Nat.cast_sub (by omega : j+1 ≤ 2*L)]
    push_cast
    ring
  have hx : ρ x = 0 := by
    have h : x = (↑(4 * (2^s*d) : ℕ) : R) := by
      dsimp [x,L]
      simpa only [Nat.cast_ofNat] using (Nat.cast_mul (α := R) 4 (2^s*d)).symm
    rw [h, map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (by
      refine ⟨4*d, ?_⟩
      ring)
  have hu (j : ℕ) : Units.map ρ.toMonoidHom (u j) = oddUnit s j := by
    apply Units.ext
    change ρ (u j : R) = (oddUnit s j : ZMod (2^s))
    simp only [u, coe_oddUnit, map_add, map_mul, map_ofNat, map_natCast, map_one]
  have hv' (j : ℕ) (hj : j < L) : Units.map ρ.toMonoidHom (v j) = -oddUnit s j := by
    apply Units.ext
    change ρ (v j : R) = -(oddUnit s j : ZMod (2^s))
    rw [hv j hj, map_sub, hx, zero_sub]
    exact congrArg (fun z : (ZMod (2^s))ˣ => -(z : ZMod (2^s))) (hu j)
  let z : R := ∑ j ∈ range L, (↑((a j)⁻¹) : R)
  have hz : ρ z = 0 := by
    dsimp only [z]
    rw [map_sum, ← neg_zero, ← invSquareSum s d, ← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    change ((Units.map ρ.toMonoidHom ((a j)⁻¹) : (ZMod (2^s))ˣ) : ZMod (2^s)) = _
    rw [map_inv, show a j = u j*v j from rfl, map_mul, hu, hv' j (mem_range.mp hj)]
    simp only [mul_inv_rev, inv_neg, Units.val_mul, Units.val_neg, neg_mul, pow_two,
      ZMod.inv_coe_unit]
  have htz : t*z=0 := by
    have hn : ((z.val : ℕ) : ZMod (2^s)) = 0 := by
      rw [ZMod.natCast_val]
      exact hz
    obtain ⟨e, he⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hn
    rw [← ZMod.natCast_zmod_val z, he, Nat.cast_mul, ← mul_assoc, htmul, zero_mul]
  have hpair : (∏ j ∈ range L, (a j : R)) = ∏ j ∈ range (2*L), (2*(j : R)+1) := by
    have h := pairedShift (R := R) L 0
    simp only [add_zero] at h
    rw [h]
    apply prod_congr rfl
    intro j hj
    rw [show a j = u j*v j from rfl, Units.val_mul, hv j (mem_range.mp hj)]
    simp only [u, coe_oddUnit, x]
  have hprod : (∏ j ∈ range (4*L), (2*(j : R)+1)) =
      (∏ j ∈ range (2*L), (2*(j : R)+1))^2 := by
    rw [pairedProduct, pow_two (∏ j ∈ range (2*L), (2*(j : R)+1))]
    apply congrArg ((∏ j ∈ range (2*L), (2*(j : R)+1)) * ·)
    calc
      _ = ∏ j ∈ range L, ((a j : R)+t) := by
        apply prod_congr rfl
        intro j hj
        rw [show a j = u j*v j from rfl, Units.val_mul, hv j (mem_range.mp hj), ht]
        simp [u, x]
      _ = ∏ j ∈ range L, (a j : R) := by
        rw [productPerturb L a htt]
        change _ * (1+t*z) = _
        rw [htz, add_zero, mul_one]
      _ = _ := hpair
  change ((↑(2^m : ℕ) : ℤ)) ∣ (oddProd (4*L) : ℤ) - (oddProd (2*L) : ℤ)^2
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Int.cast_sub, sub_eq_zero, Int.cast_pow, Int.cast_natCast, Int.cast_natCast]
  change ((oddProd (4*L) : ℕ) : R) = ((oddProd (2*L) : ℕ) : R)^2
  dsimp only [oddProd]
  change Nat.castRingHom R (∏ j ∈ range (4*L), (2*j+1)) =
    (Nat.castRingHom R (∏ j ∈ range (2*L), (2*j+1)))^2
  simp only [map_prod]
  have hc (n : ℕ) : Nat.castRingHom R n = (n : R) := rfl
  have hc' (j : ℕ) : ((2*j+1 : ℕ) : R) = 2*(j : R)+1 := by
    rw [Nat.cast_add, Nat.cast_mul (α := R) 2 j, Nat.cast_ofNat, Nat.cast_one]
  simpa only [hc, hc'] using hprod

private theorem oddSquareEight {n : ℕ} (h : Odd n) :
    (8 : ℤ) ∣ (n : ℤ)^2 - 1 := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨j, rfl⟩ := hk
    exact ⟨(j : ℤ)*(2*(j : ℤ)+1), by push_cast; ring⟩
  · obtain ⟨j, rfl⟩ := hk
    exact ⟨(2*(j : ℤ)+1)*((j : ℤ)+1), by push_cast; ring⟩

private theorem transportSquare {n e : ℕ} (hn : n ≠ 0)
    (h : (2 : ℤ)^e ∣ (oddProd (2*n) : ℤ)^2 - (oddProd n : ℤ)^4) :
    (2 : ℤ)^(e+2) ∣ ((2*(2*n)).choose (2*n) : ℤ)^2 - ((2*n).choose n : ℤ)^2 := by
  let A : ℤ := (2*(2*n)).choose (2*n)
  let B : ℤ := (2*n).choose n
  let P : ℤ := oddProd n
  let Q : ℤ := oddProd (2*n)
  have hbase : A*P^2=B*Q := by
    dsimp only [A, B, P, Q]
    exact_mod_cast binomialSplit n
  have hid : P^4*(A^2-B^2)=B^2*(Q^2-P^4) := by
    linear_combination (A*P^2+B*Q)*hbase
  have hB : (2 : ℤ) ∣ B := by
    dsimp only [B]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact_mod_cast (show 2 ∣ (2*(k+1)).choose (k+1) from Nat.two_dvd_centralBinom_succ k)
  obtain ⟨b,hb⟩ := hB
  obtain ⟨w,hw⟩ : (2 : ℤ)^e ∣ Q^2-P^4 := h
  have hlarge : (2 : ℤ)^(e+2) ∣ P^4*(A^2-B^2) := by
    rw [hid, hb, hw, pow_add]
    exact ⟨b^2*w, by ring⟩
  have hcast : ((2^(e+2) : ℕ) : ℤ) = (2 : ℤ)^(e+2) := by norm_cast
  rw [← hcast] at hlarge ⊢
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlarge
  push_cast at hzero
  have hc : IsUnit ((P : ZMod (2^(e+2)))^4) := by
    have hcop := (oddProdOdd n).coprime_two_right.pow_right (e+2)
    have hu := (ZMod.unitOfCoprime (oddProd n) hcop).isUnit
    simpa only [P, Int.cast_natCast, ZMod.coe_unitOfCoprime] using hu.pow 4
  apply hc.mul_left_cancel
  simpa only [Int.cast_sub, Int.cast_pow, mul_zero] using hzero

private theorem centralSquareCongruence (k d : ℕ) :
    let x := 2 ^ (k + 1) * d
    let y := 2 ^ k * d
    (2 : ℤ) ^ (3 * (k + 1) + 2) ∣
      ((2 * x).choose x : ℤ) ^ 2 - ((2 * y).choose y : ℤ) ^ 2 := by
  dsimp
  by_cases hd : d=0
  · simp [hd]
  cases k with
  | zero =>
    have h : (2 : ℤ)^3 ∣ (oddProd (2*d) : ℤ)^2 - (oddProd d : ℤ)^4 := by
      have h₁ := oddSquareEight (oddProdOdd (2*d))
      have h₂ := oddSquareEight ((oddProdOdd d).pow (n := 2))
      push_cast at h₂
      rw [← pow_mul] at h₂
      simpa only [sub_sub_sub_cancel_right, show (2 : ℤ)^3 = 8 by norm_num,
        show (2 : ℕ)*2=4 by decide] using dvd_sub h₁ h₂
    simpa using transportSquare hd h
  | succ k =>
    let L := 2^k*d
    have hdelta := oddFactorCongruence k d
    have hsum : (2 : ℤ) ∣ (oddProd (4*L) : ℤ) + (oddProd (2*L) : ℤ)^2 := by
      obtain ⟨a,ha⟩ := oddProdOdd (4*L)
      obtain ⟨b,hb⟩ := (oddProdOdd (2*L)).pow (n := 2)
      exact_mod_cast (show (2 : ℕ) ∣ oddProd (4*L) + oddProd (2*L)^2 from ⟨a+b+1, by omega⟩)
    have hdiv : (2 : ℤ)^(3*k+6) ∣ (oddProd (2*(2*L)) : ℤ)^2 - (oddProd (2*L) : ℤ)^4 := by
      have hp : (2 : ℤ)^(3*k+6) = (2 : ℤ)^(3*k+5)*2 := by rw [← pow_succ]
      rw [show 2*(2*L) = 4*L by omega, hp,
        show (oddProd (4*L) : ℤ)^2-(oddProd (2*L) : ℤ)^4 =
          ((oddProd (4*L) : ℤ)-(oddProd (2*L) : ℤ)^2) *
          ((oddProd (4*L) : ℤ)+(oddProd (2*L) : ℤ)^2) by ring]
      exact mul_dvd_mul hdelta hsum
    have hn : 2*L ≠ 0 := by dsimp [L]; positivity
    have res := transportSquare hn hdiv
    have hx : 2^(k+1+1)*d = 2*(2*L) := by dsimp [L]; rw [pow_succ, pow_succ]; ring
    have hy : 2^(k+1)*d = 2*L := by dsimp [L]; rw [pow_succ]; ring
    simpa only [Nat.succ_eq_add_one, hx, hy, show 3*(k+1+1)+2 = 3*k+6+2 by omega] using res

theorem OMA.solution : OMA.R_oeis_a028576_R1.H2 := centralSquareCongruence