import OMAReductions.R_mo_289554_R1
import Mathlib.NumberTheory.Pell

/-!
Dem'yanenko, “Sums of four cubes” (1966), Theorem 1.
https://www.mathnet.ru/eng/ivm2756

The nonexceptional residue classes are obtained from a finite orbit of a
quadratic unit. For the remaining residue classes, explicit representations
give initial points on indefinite quadratics, and Pell units extend them.
-/

open OMA.R_mo_289554_R1

private abbrev Quadruple := ℤ × ℤ × ℤ × ℤ

private def sumCubes (v : Quadruple) : ℤ :=
  v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3

private def combined {R : Type*} [CommRing R] (d : R) (p q : R × R) : R × R :=
  (p.1 * q.1 + d * p.2 * q.2, p.1 * q.2 + p.2 * q.1)

private theorem combined_one_left {R : Type*} [CommRing R] (d : R) (p : R × R) :
    combined d (1, 0) p = p := by
  ext <;> simp [combined]

private theorem combined_one_right {R : Type*} [CommRing R] (d : R) (p : R × R) :
    combined d p (1, 0) = p := by
  ext <;> simp [combined]

private theorem combined_assoc {R : Type*} [CommRing R] (d : R) (p q r : R × R) :
    combined d (combined d p q) r = combined d p (combined d q r) := by
  ext <;> dsimp [combined] <;> ring

private def walk {R : Type*} [CommRing R] (d : R) (u : R × R) : ℕ → R × R
  | 0 => (1, 0)
  | n + 1 => combined d (walk d u n) u

private theorem walk_add {R : Type*} [CommRing R] (d : R) (u : R × R) (n m : ℕ) :
    walk d u (n + m) = combined d (walk d u n) (walk d u m) := by
  induction m with
  | zero => simp [walk, combined_one_right]
  | succ m ih =>
      rw [Nat.add_succ, walk, walk, ih, combined_assoc]

private def quadNorm (d : ℤ) (p : ℤ × ℤ) : ℤ := p.1 ^ 2 - d * p.2 ^ 2

private theorem quadNorm_combined (d : ℤ) (p q : ℤ × ℤ) :
    quadNorm d (combined d p q) = quadNorm d p * quadNorm d q := by
  dsimp [quadNorm, combined]
  ring

private theorem quadNorm_walk (d : ℤ) (u : ℤ × ℤ) (hu : quadNorm d u = 1) (i : ℕ) :
    quadNorm d (walk d u i) = 1 := by
  induction i with
  | zero => simp [walk, quadNorm]
  | succ i ih => rw [walk, quadNorm_combined, ih, hu, one_mul]

private def unitZ : ℤ × ℤ := (-112488782561, -1923517596)

private def signedUnit {R : Type*} [CommRing R] : R × R :=
  (-112488782561, -1923517596)

private def residuePolynomial {R : Type*} [CommRing R] (v : R × R) : R :=
  (v.1 - 2 * v.2) ^ 3 + (163 * v.1 + 7563 * v.2) ^ 3 -
    (173 * v.1 + 7309 * v.2) ^ 3 + (89 * v.1 + 2693 * v.2) ^ 3

private abbrev M := ZMod 59814

private def residueList : ℕ → M × M → List ℕ
  | 0, _ => []
  | i + 1, p => (residuePolynomial p).val :: residueList i (combined 3420 p signedUnit)

private def residuesNeeded : List ℕ :=
  ((List.range 3323).map (fun i => 18 * i + 2)).filter (fun x => x != 33230)

private def coverageMask : List ℕ → ℕ
  | [] => 0
  | r :: rs => (2 ^ r) ||| coverageMask rs

private theorem coverageMask_spec (rs : List ℕ) (r : ℕ) :
    (coverageMask rs).testBit r = true ↔ r ∈ rs := by
  induction rs with
  | nil => simp [coverageMask]
  | cons x xs ih =>
      rw [coverageMask, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, ih, List.mem_cons]
      simp only [true_eq_decide_iff, eq_comm]

set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
private theorem verifiedResidues :
    coverageMask (residueList 3322 (1, 0)) = coverageMask residuesNeeded := by
  decide +kernel

set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
private theorem verifiedPeriod : walk (3420 : M) signedUnit 9966 = (1, 0) := by
  decide +kernel

private theorem residueList_spec (m : ℕ) (p : M × M) (r : ℕ)
    (hr : r ∈ residueList m p) :
    ∃ i < m, r = (residuePolynomial (combined 3420 p (walk 3420 signedUnit i))).val := by
  induction m generalizing p with
  | zero => simp [residueList] at hr
  | succ m ih =>
      rw [residueList, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨0, Nat.zero_lt_succ _, by simp [walk, combined_one_right]⟩
      · obtain ⟨i, hi, hri⟩ := ih _ hr
        refine ⟨i + 1, Nat.succ_lt_succ hi, hri.trans ?_⟩
        rw [walk, ← combined_assoc]
        congr 2
        ext <;> dsimp [combined] <;> ring

private theorem walk_cast (i : ℕ) :
    (((walk 3420 unitZ i).1 : M), ((walk 3420 unitZ i).2 : M)) =
      walk 3420 signedUnit i := by
  induction i with
  | zero => simp [walk]
  | succ i ih =>
      have h1 := congrArg Prod.fst ih
      have h2 := congrArg Prod.snd ih
      change (↑(walk 3420 unitZ i).1 : M) = (walk 3420 signedUnit i).1 at h1
      change (↑(walk 3420 unitZ i).2 : M) = (walk 3420 signedUnit i).2 at h2
      rw [walk, walk]
      simp only [unitZ, signedUnit] at h1 h2
      ext <;> dsimp [combined, unitZ, signedUnit] <;>
        push_cast <;> rw [h1, h2]

private theorem walk_mod_period (i t : ℕ) :
    walk (3420 : M) signedUnit (i + 9966 * t) = walk 3420 signedUnit i := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, walk_add, ih, verifiedPeriod, combined_one_right]

private theorem representation_poly (k a b : ℤ) :
    sumCubes (24 * k + 163 * a + 7563 * b, -(27 * k + 173 * a + 7309 * b),
      19 * k + 89 * a + 2693 * b, -(10 * k - a + 2 * b)) =
      residuePolynomial (a,b) - 59814 * k * quadNorm 3420 (a,b) := by
  dsimp [sumCubes, residuePolynomial, quadNorm]
  ring



private theorem exists_initial_residue (N : ℤ) (h18 : N % 18 = 2) (hne : N % 3323 ≠ 0) :
    ∃ i : ℕ, (N : M) = residuePolynomial (walk 3420 signedUnit i) := by
  let r := (N : M).val
  have hlt : r < 59814 := ZMod.val_lt _
  have hrem : (r : ℤ) = N % 59814 := ZMod.val_intCast _
  have hrem18 : r % 18 = 2 := by omega
  have hrne : r ≠ 33230 := by
    intro h
    rw [h] at hrem
    apply hne
    omega
  have hmem : r ∈ residuesNeeded := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨r / 18, List.mem_range.mpr (by omega), by omega⟩, ?_⟩
    simpa using hrne
  have hmemOrbit : r ∈ residueList 3322 (1, 0) := by
    apply (coverageMask_spec _ _).mp
    rw [verifiedResidues]
    exact (coverageMask_spec _ _).mpr hmem
  obtain ⟨i, -, hi⟩ := residueList_spec _ _ _ hmemOrbit
  rw [combined_one_left] at hi
  refine ⟨i, ?_⟩
  calc
    (N : M) = (r : M) := (ZMod.natCast_zmod_val _).symm
    _ = (((residuePolynomial (walk 3420 signedUnit i) : M).val : ℕ) : M) :=
      congrArg (fun x : ℕ => (x : M)) hi
    _ = _ := ZMod.natCast_zmod_val _

private theorem residuePolynomial_cast (i : ℕ) :
    ((residuePolynomial (walk 3420 unitZ i) : ℤ) : M) =
      residuePolynomial (walk 3420 signedUnit i) := by
  rw [← walk_cast]
  simp only [residuePolynomial, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat]

private def positiveUnit : ℤ × ℤ := (112488782561, 1923517596)

private theorem positiveWalk (i : ℕ) :
    0 < (walk 3420 positiveUnit i).1 ∧ 0 ≤ (walk 3420 positiveUnit i).2 := by
  induction i with
  | zero => simp [walk]
  | succ i ih =>
      obtain ⟨h1,h2⟩ := ih
      rw [walk]
      dsimp only [combined, positiveUnit] at *
      constructor <;> linarith

private theorem signedWalk (i : ℕ) :
    (walk 3420 unitZ i).1 = (-1 : ℤ) ^ i * (walk 3420 positiveUnit i).1 ∧
    (walk 3420 unitZ i).2 = (-1 : ℤ) ^ i * (walk 3420 positiveUnit i).2 := by
  induction i with
  | zero => simp [walk]
  | succ i ih =>
      obtain ⟨h1,h2⟩ := ih
      rw [walk, walk]
      simp only [unitZ, positiveUnit] at h1 h2
      constructor <;> dsimp only [combined, positiveUnit, unitZ] <;>
        rw [h1, h2, pow_succ (-1 : ℤ) i] <;> ring

private theorem signedWalk_abs_strict :
    StrictMono (fun i => |(walk 3420 unitZ i).1|) := by
  have h (i : ℕ) : |(walk 3420 unitZ i).1| = (walk 3420 positiveUnit i).1 := by
    rw [(signedWalk i).1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (positiveWalk i).1]
  apply strictMono_nat_of_lt_succ
  intro i
  rw [h, h, walk]
  obtain ⟨hp, hq⟩ := positiveWalk i
  dsimp only [combined, positiveUnit] at *
  linarith

private def polynomialTuple (k a b : ℤ) : Quadruple :=
  (24 * k + 163 * a + 7563 * b, -(27 * k + 173 * a + 7309 * b),
    19 * k + 89 * a + 2693 * b, -(10 * k - a + 2 * b))

private theorem polynomialTuple_A_eq {k a b l c d : ℤ}
    (h : polynomialTuple k a b = polynomialTuple l c d) : a = c := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun v : Quadruple => v.2.1) h
  have h3 := congrArg (fun v : Quadruple => v.2.2.1) h
  dsimp only [polynomialTuple] at h1 h2 h3
  linarith only [h1,h2,h3]

private theorem infinite_nonexceptional (N : ℤ) (h18 : N % 18 = 2) (hne : N % 3323 ≠ 0) :
    {v : Quadruple | sumCubes v = N}.Infinite := by
  obtain ⟨i, hi⟩ := exists_initial_residue N h18 hne
  let index (t : ℕ) := i + 9966 * t
  let coeff (t : ℕ) := walk 3420 unitZ (index t)
  let shift (t : ℕ) := (residuePolynomial (coeff t) - N) / 59814
  let family (t : ℕ) := polynomialTuple (shift t) (coeff t).1 (coeff t).2
  have hinj : Function.Injective family := by
    intro r s hrs
    have he := polynomialTuple_A_eq hrs
    have hin := signedWalk_abs_strict.injective (congrArg abs he)
    change i + 9966 * r = i + 9966 * s at hin
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨t, rfl⟩
  change sumCubes (family t) = N
  have hunit : quadNorm 3420 (coeff t) = 1 := quadNorm_walk _ _ (by decide) _
  have hmod : (N : M) = (↑(residuePolynomial (coeff t) : ℤ) : M) := by
    change (N : M) = ↑(residuePolynomial (walk 3420 unitZ (i + 9966 * t)) : ℤ)
    rw [residuePolynomial_cast, walk_mod_period]
    exact hi
  have hd : (59814 : ℤ) ∣ residuePolynomial (coeff t) - N :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 59814).mp hmod
  have hshift : 59814 * shift t = residuePolynomial (coeff t) - N := by
    have h := Int.emod_add_mul_ediv (residuePolynomial (coeff t) - N) 59814
    rw [Int.emod_eq_zero_of_dvd hd, zero_add] at h
    exact h
  change sumCubes (polynomialTuple (shift t) (coeff t).1 (coeff t).2) = N
  rw [polynomialTuple, representation_poly]
  have hc : ((coeff t).1, (coeff t).2) = coeff t := Prod.eta _
  rw [hc, hunit, mul_one, hshift]
  ring



private def evolve (step : ℤ × ℤ → ℤ × ℤ) (v : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => v
  | n + 1 => step (evolve step v n)

private def fromDifferences (p q u v : ℤ) : Quadruple :=
  ((p + u) / 2, (p - u) / 2, (q + v) / 2, (q - v) / 2)

private theorem differences_identity (p q u v : ℤ)
    (hu : u ≡ p [ZMOD 2]) (hv : v ≡ q [ZMOD 2]) :
    4 * sumCubes (fromDifferences p q u v) = p ^ 3 + q ^ 3 + 3 * (p * u ^ 2 + q * v ^ 2) := by
  change u % 2 = p % 2 at hu
  change v % 2 = q % 2 at hv
  have ha : 2 * ((p + u) / 2) = p + u := by omega
  have hb : 2 * ((p - u) / 2) = p - u := by omega
  have hc : 2 * ((q + v) / 2) = q + v := by omega
  have hd : 2 * ((q - v) / 2) = q - v := by omega
  have h : 8 * sumCubes (fromDifferences p q u v) =
      2 * (p ^ 3 + q ^ 3 + 3 * (p * u ^ 2 + q * v ^ 2)) := by
    calc
      _ = (2 * ((p + u) / 2)) ^ 3 + (2 * ((p - u) / 2)) ^ 3 +
          (2 * ((q + v) / 2)) ^ 3 + (2 * ((q - v) / 2)) ^ 3 := by
        dsimp [sumCubes, fromDifferences]
        ring
      _ = _ := by rw [ha, hb, hc, hd]; ring
  linarith only [h]

private theorem abs_difference_parity (x y : ℤ) : |x - y| ≡ x + y [ZMOD 2] := by
  change |x-y| % 2 = (x+y) % 2
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    omega
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    omega

private theorem infinite_oriented_seed (x y z t : ℤ) (hp : 0 < x + y) (hq : z + t < 0)
    (hn : ¬ IsSquare (-((x+y)*(z+t)))) (hne : x ≠ y ∨ z ≠ t) :
    {v : Quadruple | sumCubes v = sumCubes (x,y,z,t)}.Infinite := by
  let p := x + y
  let q := z + t
  let d := -(p*q)
  have hd : 0 < d := neg_pos.mpr (mul_neg_of_pos_of_neg hp hq)
  obtain ⟨u, hux, huy⟩ := Pell.Solution₁.exists_pos_of_not_isSquare hd hn
  let a := 1 + 2 * (d * u.y ^ 2)
  let b := 2 * (u.x * u.y)
  have ha : 1 < a := by
    have h : 0 < 2 * (d * u.y ^ 2) := by positivity
    dsimp [a]
    linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hax : a = (u*u).x := by
    rw [Pell.Solution₁.x_mul]
    dsimp [a]
    nlinarith only [u.prop]
  have hby : b = (u*u).y := by
    rw [Pell.Solution₁.y_mul]
    dsimp [b]
    ring
  have hab : a ^ 2 + p*q*b^2 = 1 := by
    have h := (u*u).prop
    rw [← hax, ← hby] at h
    dsimp [d] at h
    linear_combination h
  have ha2 : a ≡ 1 [ZMOD 2] := by change a % 2 = 1 % 2; dsimp [a]; omega
  have hb2 : b ≡ 0 [ZMOD 2] := by change b % 2 = 0 % 2; dsimp [b]; omega
  let step (w : ℤ × ℤ) : ℤ × ℤ :=
    (a*w.1 + ((-q)*b)*w.2, a*w.2 + (p*b)*w.1)
  let diffs (j : ℕ) := evolve step (|x-y|, |z-t|) j
  have hstep (j : ℕ) : diffs (j+1) = step (diffs j) := rfl
  have nonneg_at (j : ℕ) :
      0 ≤ (diffs j).1 ∧ 0 ≤ (diffs j).2 ∧ (0 < (diffs j).1 ∨ 0 < (diffs j).2) := by
    have hq' : 0 < -q := neg_pos.mpr hq
    have ha' : 0 < a := by omega
    induction j with
    | zero =>
        refine ⟨abs_nonneg _, abs_nonneg _, ?_⟩
        exact hne.imp (fun h => abs_pos.mpr (sub_ne_zero.mpr h))
          (fun h => abs_pos.mpr (sub_ne_zero.mpr h))
    | succ j ih =>
        obtain ⟨h1,h2,hnz⟩ := ih
        rw [hstep]
        dsimp only [step]
        refine ⟨by positivity, by positivity, Or.inl ?_⟩
        rcases hnz with hl | hr <;> positivity
  have strictFirst : StrictMono (fun j => (diffs j).1) := by
    apply strictMono_nat_of_lt_succ
    intro j
    obtain ⟨h1,h2,hnz⟩ := nonneg_at j
    have hq' : 0 < -q := neg_pos.mpr hq
    rw [hstep]
    dsimp only [step]
    rcases hnz with hl | hr
    · calc
        (diffs j).1 < a * (diffs j).1 := by
          simpa only [one_mul] using mul_lt_mul_of_pos_right ha hl
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · have hl : (diffs j).1 ≤ a * (diffs j).1 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ha.le h1
      exact hl.trans_lt (lt_add_of_pos_right _ (by positivity))
  have parity (j : ℕ) : (diffs j).1 ≡ p [ZMOD 2] ∧ (diffs j).2 ≡ q [ZMOD 2] := by
    induction j with
    | zero => exact ⟨abs_difference_parity _ _, abs_difference_parity _ _⟩
    | succ j ih =>
        rw [hstep]
        dsimp only [step]
        constructor
        · have h := (ha2.mul ih.1).add (((Int.ModEq.refl (-q)).mul hb2).mul ih.2)
          simpa only [one_mul, mul_zero, zero_mul, add_zero] using h
        · have h := (ha2.mul ih.2).add (((Int.ModEq.refl p).mul hb2).mul ih.1)
          simpa only [one_mul, mul_zero, zero_mul, add_zero] using h
  have preserved (j : ℕ) :
      p * (diffs j).1 ^ 2 + q * (diffs j).2 ^ 2 = p * |x-y| ^ 2 + q * |z-t| ^ 2 := by
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [hstep]
        calc
          _ = (a ^ 2 + p*q*b^2) * (p * (diffs j).1 ^ 2 + q * (diffs j).2 ^ 2) := by
            dsimp only [step]
            ring
          _ = _ := by rw [hab, one_mul, ih]
  let family (j : ℕ) := fromDifferences p q (diffs j).1 (diffs j).2
  have hx (j : ℕ) : 2 * (family j).1 = p + (diffs j).1 := by
    have h := (parity j).1
    change (diffs j).1 % 2 = p % 2 at h
    change 2 * ((p + (diffs j).1) / 2) = p + (diffs j).1
    omega
  have hinj : Function.Injective family := by
    intro j k h
    have heq := congrArg Prod.fst h
    apply strictFirst.injective
    change (diffs j).1 = (diffs k).1
    have hj := hx j
    have hk := hx k
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨j,rfl⟩
  change sumCubes (family j) = sumCubes (x,y,z,t)
  have h := differences_identity p q _ _ (parity j).1 (parity j).2
  rw [preserved] at h
  have hseed : 4 * sumCubes (x,y,z,t) =
      p ^ 3 + q ^ 3 + 3 * (p * |x-y| ^ 2 + q * |z-t| ^ 2) := by
    rw [sq_abs, sq_abs]
    dsimp [sumCubes, p, q]
    ring
  change 4 * sumCubes (family j) = _ at h
  linarith only [h, hseed]

private theorem infinite_from_seed (x y z t : ℤ)
    (hd : 0 < -((x+y)*(z+t))) (hn : ¬ IsSquare (-((x+y)*(z+t))))
    (hne : x ≠ y ∨ z ≠ t) :
    {v : Quadruple | sumCubes v = sumCubes (x,y,z,t)}.Infinite := by
  have hmul : (x+y)*(z+t) < 0 := neg_pos.mp hd
  rcases mul_neg_iff.mp hmul with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact infinite_oriented_seed x y z t h1 h2 hn hne
  · have hs : sumCubes (z,t,x,y) = sumCubes (x,y,z,t) := by dsimp [sumCubes]; ring
    rw [← hs]
    apply infinite_oriented_seed z t x y h2 h1
    · simpa only [mul_comm] using hn
    · exact hne.symm



private theorem positive_quadratic (a b c x : ℤ) (ha : 0 < a) (hd : b^2 < 4*a*c) :
    0 < a*x^2+b*x+c := by
  have he : 4*a*(a*x^2+b*x+c) = (2*a*x+b)^2 + (4*a*c-b^2) := by ring
  have hp : 0 < 4*a*(a*x^2+b*x+c) := by
    rw [he]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sub_pos.mpr hd)
  by_contra! h
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4*a) h)) hp

private theorem between_squares {D m : ℤ} (hm : 0 ≤ m) (hl : m^2 < D) (hu : D < (m+1)^2) :
    ¬ IsSquare D := by
  rintro ⟨z,hz⟩
  have hs : |z|^2 = D := by rw [sq_abs, pow_two, ← hz]
  rcases le_or_gt |z| m with hh | hh
  · have h := mul_self_le_mul_self (abs_nonneg z) hh
    nlinarith only [h, hs, hl]
  · have hh' : m+1 ≤ |z| := by omega
    have h := mul_self_le_mul_self (show 0 ≤ m+1 by omega) hh'
    nlinarith only [h, hs, hu]

private theorem first_square_gap {D m w : ℤ} (he : D = m^2-w^2)
    (hn : w ≠ 0) (hs : w^2 < 2*m-1) : 0 < D ∧ ¬ IsSquare D := by
  have hm : 0 ≤ m-1 := by have h := sq_nonneg w; omega
  have hl : (m-1)^2 < D := by nlinarith only [he, hs]
  have hu : D < (m-1+1)^2 := by
    nlinarith only [he, sq_pos_of_ne_zero hn]
  exact ⟨(sq_nonneg _).trans_lt hl, between_squares hm hl hu⟩

private theorem second_square_gap {D m w : ℤ} (he : D = m^2-w^2)
    (hl : 2*m-1 < w^2) (hu : w^2 < 4*m-4) : 0 < D ∧ ¬ IsSquare D := by
  have hm : 0 ≤ m-2 := by have h := sq_nonneg w; omega
  have hlo : (m-2)^2 < D := by nlinarith only [he, hu]
  have hup : D < (m-2+1)^2 := by nlinarith only [he, hl]
  exact ⟨(sq_nonneg _).trans_lt hlo, between_squares hm hlo hup⟩

private theorem linear_residue (m : ℕ) (s a b c r : ℤ) (hd : (a*s+b) % m = 0)
    (hc : (c : ZMod m) * (a : ZMod m) = 1) (hr : (a : ZMod m)*r+b = 0) :
    (s : ZMod m) = r := by
  have h : ((a*s+b : ℤ) : ZMod m) = 0 := by
    simpa only [Int.cast_zero] using
      (ZMod.intCast_eq_intCast_iff' (a*s+b) 0 m).mpr (by simpa using hd)
  push_cast at h
  have hmul : (a : ZMod m)*(s : ZMod m) = (a : ZMod m)*(r : ZMod m) :=
    add_right_cancel (h.trans hr.symm)
  have hscaled := congrArg (fun v : ZMod m => (c : ZMod m)*v) hmul
  simpa only [← mul_assoc, hc, one_mul] using hscaled
private theorem exceptional_zero (s : ℤ) :
    {v : Quadruple | sumCubes v = 54*s+2}.Infinite := by
  let x := 29484*s^2+2211*s+43
  let y := 9828*s^2+485*s+4
  let z := -(29484*s^2+2157*s+41)
  let t := -(9828*s^2+971*s+22)
  let m := 39312*s^2+2912*s+55
  let w := 216*s+8
  have hid : -((x+y)*(z+t)) = m^2-w^2 := by dsimp [x,y,z,t,m,w]; ring
  have hs : w^2 < 2*m-1 := by
    dsimp [w,m]
    nlinarith only [positive_quadratic 31968 2368 45 s (by decide) (by decide)]
  have hn : w ≠ 0 := by dsimp [w]; omega
  have ⟨hp,hns⟩ := first_square_gap hid hn hs
  have hxy : x ≠ y := by
    have hpos := positive_quadratic 19656 1726 39 s (by decide) (by decide)
    dsimp [x,y]
    intro h
    nlinarith only [h, hpos]
  have hsum : sumCubes (x,y,z,t) = 54*s+2 := by dsimp [sumCubes,x,y,z,t]; ring
  rw [← hsum]
  exact infinite_from_seed x y z t hp hns (Or.inl hxy)

private theorem exceptional_one (s : ℤ) (hd : (54*s+20)%3323 = 0) :
    {v : Quadruple | sumCubes v = 54*s+20}.Infinite := by
  let x := 3*s-11
  let y := s+2
  let z := -3*s+10
  let t := -s+7
  let m := |4*s-13|
  have hsr : (s : ZMod 3323) = 615 :=
    linear_residue 3323 s 54 20 800 615 hd (by decide) (by decide)
  have hs : s % 3323 = 615 := (ZMod.intCast_eq_intCast_iff' s 615 3323).mp hsr
  have hm : 9 ≤ m := by
    dsimp only [m]
    rcases le_total 0 (4*s-13) with h | h
    · rw [abs_of_nonneg h]
      omega
    · rw [abs_of_nonpos h]
      omega
  have hid : -((x+y)*(z+t)) = m^2-(4 : ℤ)^2 := by
    dsimp only [m,x,y,z,t]
    rw [sq_abs]
    ring
  have ⟨hp,hns⟩ := first_square_gap hid (by decide) (by omega)
  have hxy : x ≠ y := by dsimp [x,y]; omega
  have hsum : sumCubes (x,y,z,t) = 54*s+20 := by dsimp [sumCubes,x,y,z,t]; ring
  rw [← hsum]
  exact infinite_from_seed x y z t hp hns (Or.inl hxy)

private theorem exceptional_five (s : ℤ) (hd : (216*s+92)%3323 = 0) :
    {v : Quadruple | sumCubes v = 216*s+92}.Infinite := by
  let x := 3*s-164
  let y := -s+71
  let z := -3*s+160
  let t := s-35
  let m := |2*s-109|
  have hsr : (s : ZMod 3323) = 1538 :=
    linear_residue 3323 s 216 92 200 1538 hd (by decide) (by decide)
  have hs : s % 3323 = 1538 := (ZMod.intCast_eq_intCast_iff' s 1538 3323).mp hsr
  have hm : 129 ≤ m := by
    dsimp only [m]
    rcases le_total 0 (2*s-109) with h | h
    · rw [abs_of_nonneg h]
      omega
    · rw [abs_of_nonpos h]
      omega
  have hid : -((x+y)*(z+t)) = m^2-(16 : ℤ)^2 := by
    dsimp only [m,x,y,z,t]
    rw [sq_abs]
    ring
  have ⟨hp,hns⟩ := first_square_gap hid (by decide) (by omega)
  have hxy : x ≠ y := by dsimp [x,y]; omega
  have hsum : sumCubes (x,y,z,t) = 216*s+92 := by dsimp [sumCubes,x,y,z,t]; ring
  rw [← hsum]
  exact infinite_from_seed x y z t hp hns (Or.inl hxy)

private theorem exceptional_eleven (s : ℤ) :
    {v : Quadruple | sumCubes v = 216*s-16}.Infinite := by
  let x := 14742*s^2-2157*s+82
  let y := 4914*s^2-971*s+44
  let z := -(14742*s^2-2211*s+86)
  let t := -(4914*s^2-485*s+8)
  let m := 19656*s^2-2912*s+110
  let w := 216*s-16
  have hid : -((x+y)*(z+t)) = m^2-w^2 := by dsimp [x,y,z,t,m,w]; ring
  have hl : 2*m-1 < w^2 := by
    dsimp [m,w]
    by_cases h : 0 < s
    · have hh := mul_nonneg (show 0 ≤ s by omega) (show 0 ≤ s-1 by omega)
      nlinarith only [hh, h]
    · nlinarith only [sq_nonneg s, (show s ≤ 0 by omega)]
  have hu : w^2 < 4*m-4 := by
    dsimp [w,m]
    nlinarith only [positive_quadratic 31968 (-4736) 180 s (by decide) (by decide)]
  have ⟨hp,hns⟩ := second_square_gap hid hl hu
  have hxy : x ≠ y := by
    have hpos := positive_quadratic 9828 (-1186) 38 s (by decide) (by decide)
    dsimp [x,y]
    intro h
    nlinarith only [h,hpos]
  have hsum : sumCubes (x,y,z,t) = 216*s-16 := by dsimp [sumCubes,x,y,z,t]; ring
  rw [← hsum]
  exact infinite_from_seed x y z t hp hns (Or.inl hxy)

private theorem exceptional_two (s : ℤ) :
    {v : Quadruple | sumCubes v = 3323*(108*s+46)}.Infinite := by
  let x := 29484*s^2+25143*s+5731
  let y := 9828*s^2+8129*s+1802
  let z := -(29484*s^2+25089*s+5708)
  let t := -(9828*s^2+8615*s+2009)
  let m := 39312*s^2+33488*s+7625
  let w := 216*s+92
  have hid : -((x+y)*(z+t)) = m^2-w^2 := by dsimp [x,y,z,t,m,w]; ring
  have hs : w^2 < 2*m-1 := by
    dsimp [w,m]
    nlinarith only [positive_quadratic 31968 27232 6785 s (by decide) (by decide)]
  have hn : w ≠ 0 := by dsimp [w]; omega
  have ⟨hp,hns⟩ := first_square_gap hid hn hs
  have hxy : x ≠ y := by
    have hpos := positive_quadratic 19656 17014 3929 s (by decide) (by decide)
    dsimp [x,y]
    intro h
    nlinarith only [h,hpos]
  have hsum : sumCubes (x,y,z,t) = 3323*(108*s+46) := by
    dsimp [sumCubes,x,y,z,t]
    ring
  rw [← hsum]
  exact infinite_from_seed x y z t hp hns (Or.inl hxy)

private theorem last_residue (k : ℤ) (h0 : k%3 ≠ 0) (h1 : k%3 ≠ 1)
    (h5 : k%12 ≠ 5) (h11 : k%12 ≠ 11) : k%6 = 2 := by
  have h3 := Int.emod_emod_of_dvd k (show (3 : ℤ) ∣ 12 from ⟨4, rfl⟩)
  have h6 := Int.emod_emod_of_dvd k (show (6 : ℤ) ∣ 12 from ⟨2, rfl⟩)
  omega

private theorem infinite_exceptional (k : ℤ) (hD : (18*k+2)%3323 = 0) :
    {v : Quadruple | sumCubes v = 18*k+2}.Infinite := by
  have h3 := Int.emod_add_mul_ediv k 3
  have h12 := Int.emod_add_mul_ediv k 12
  by_cases h0 : k%3 = 0
  · have he : 18*k+2 = 54*(k/3)+2 := by linarith only [h0,h3]
    rw [he]
    exact exceptional_zero (k/3)
  by_cases h1 : k%3 = 1
  · have he : 18*k+2 = 54*(k/3)+20 := by linarith only [h1,h3]
    rw [he] at hD ⊢
    exact exceptional_one (k/3) hD
  by_cases h5 : k%12 = 5
  · have he : 18*k+2 = 216*(k/12)+92 := by linarith only [h5,h12]
    rw [he] at hD ⊢
    exact exceptional_five (k/12) hD
  by_cases h11 : k%12 = 11
  · have he : 18*k+2 = 216*(k/12+1)-16 := by linarith only [h11,h12]
    rw [he]
    exact exceptional_eleven (k/12+1)
  have h2 := last_residue k h0 h1 h5 h11
  have h6 := Int.emod_add_mul_ediv k 6
  have hform : 18*k+2 = 38+108*(k/6) := by linarith only [h2,h6]
  have h38 : (18*k+2) % 108 = 38 := by
    rw [hform, Int.add_mul_emod_self_left]
    decide
  let q := (18*k+2)/3323
  have hq : 18*k+2 = 3323*q := by
    have hd := Int.emod_add_mul_ediv (18*k+2) 3323
    rw [hD, zero_add] at hd
    exact hd.symm
  have hdiv : (3323*q + (-38)) % 108 = 0 := by
    rw [← hq]
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp h38
  have hc : (q : ZMod 108) = 46 :=
    linear_residue 108 q 3323 (-38) 95 46 hdiv (by decide) (by decide)
  have hcongr : q % 108 = 46 := (ZMod.intCast_eq_intCast_iff' q 46 108).mp hc
  have h108 := Int.emod_add_mul_ediv q 108
  have he : 18*k+2 = 3323*(108*(q/108)+46) := by linarith only [hq,hcongr,h108]
  rw [he]
  exact exceptional_two (q/108)

theorem OMA.solution : OMA.R_mo_289554_R1.H2 := by
  intro N hN
  change {v : Quadruple | sumCubes v = N}.Infinite
  by_cases hD : N % 3323 = 0
  · let k := N / 18
    have hNk : N = 18*k+2 := by
      have h := Int.emod_add_mul_ediv N 18
      rw [hN, add_comm] at h
      exact h.symm
    rw [hNk] at hD ⊢
    exact infinite_exceptional k hD
  · exact infinite_nonexceptional N hN hD
