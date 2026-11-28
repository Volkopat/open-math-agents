import OMAReductions.R_mo_289554_R1
import Mathlib.NumberTheory.Pell

/-!
The linear seeds for the nonzero residue classes are from the four-cubes
identities of Schinzel and Sierpiński, Acta Arith. 4 (1958), 20–30.
https://doi.org/10.4064/aa-4-1-20-30
See also Revoy, Sur les sommes de quatre cubes (1983), Section 1.
https://www.e-periodica.ch/cntmng?pid=ens-001%3A1983%3A29%3A%3A83

For a fixed target, seeds with opposite pair sums and nonsquare discriminant
give infinitely many distinct tuples by the positive Pell recurrence.
-/

open OMA.R_mo_289554_R1

private abbrev Quadruple := ℤ × ℤ × ℤ × ℤ

private def sumCubes (v : Quadruple) : ℤ :=
  v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3

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



private theorem infinitely_from (N a b c d : ℤ)
    (hs : sumCubes (a,b,c,d) = N)
    (hD : 0 < -((a+b)*(c+d)) ∧ ¬ IsSquare (-((a+b)*(c+d))))
    (hne : a ≠ b ∨ c ≠ d) :
    {v : Quadruple | sumCubes v = N}.Infinite := by
  rw [← hs]
  exact infinite_from_seed a b c d hD.1 hD.2 hne

private theorem three_apart (m : ℤ) (hm : 2 ≤ m) :
    0 < m*(m+3) ∧ ¬ IsSquare (m*(m+3)) := by
  refine ⟨mul_pos (by omega) (by omega), between_squares (m := m+1) (by omega) ?_ ?_⟩ <;>
    nlinarith only [hm]

private theorem five_apart (m : ℤ) (hm : 5 ≤ m) :
    0 < m*(m+5) ∧ ¬ IsSquare (m*(m+5)) := by
  refine ⟨mul_pos (by omega) (by omega), between_squares (m := m+2) (by omega) ?_ ?_⟩ <;>
    nlinarith only [hm]

private theorem abs_lower {x m : ℤ} (h : x ≤ -m ∨ m ≤ x) : m ≤ |x| := by
  rcases h with h | h
  · have he : -x ≤ |x| := neg_le_abs x
    omega
  · exact h.trans (le_abs_self x)

private theorem square_of_coprime_right {a b : ℤ} (hb : 0 ≤ b)
    (hc : IsCoprime a b) (h : IsSquare (a*b)) : IsSquare b := by
  obtain ⟨z, hz⟩ := h
  have he : b.natAbs*a.natAbs = z.natAbs ^ 2 := by
    simpa only [Int.natAbs_mul, pow_two, mul_comm] using congrArg Int.natAbs hz
  have hcop := (Int.isCoprime_iff_nat_coprime.mp hc).symm
  have hg : IsUnit (gcd b.natAbs a.natAbs) := by
    change IsUnit (Nat.gcd b.natAbs a.natAbs)
    exact Nat.isUnit_iff.mpr hcop
  obtain ⟨q,hq⟩ := exists_eq_pow_of_mul_eq_pow hg he
  have hsq : IsSquare b.natAbs := ⟨q, by simpa only [pow_two] using hq⟩
  rw [← Int.natAbs_of_nonneg hb]
  exact Int.isSquare_natCast_iff.mpr hsq

private theorem nonsquare_of_residue (v : ℤ) (m : ℕ) (r : ZMod m)
    (hv : (v : ZMod m) = r) (hr : ∀ x : ZMod m, x*x ≠ r) : ¬ IsSquare v := by
  rintro ⟨x,hx⟩
  apply hr (x : ZMod m)
  rw [← Int.cast_mul, ← hx, hv]

private theorem finite_seed (N a b c d : ℤ)
    (hs : sumCubes (a,b,c,d) = N)
    (hD : 0 < -((a+b)*(c+d)))
    (hn : ¬ IsSquare (-((a+b)*(c+d))))
    (hne : a ≠ b ∨ c ≠ d) :
    {v : Quadruple | sumCubes v = N}.Infinite :=
  infinitely_from N a b c d hs ⟨hD, hn⟩ hne

private theorem infinite_zero : {v : Quadruple | sumCubes v = 0}.Infinite := by
  let f : ℤ → Quadruple := fun n => (n,-n,0,0)
  have hf : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨n,rfl⟩
  change n^3 + (-n)^3 + 0^3 + 0^3 = 0
  ring

private theorem infinite_six_seed (w k t e : ℤ) (hw : w ≠ 0)
    (hgap : (3*w)^2 < 2*(3*k+t)-1)
    (he : 21*w^2-t^2-4*t*k = e) :
    {v : Quadruple | sumCubes v = 6*w*e}.Infinite := by
  let a := k+4*w
  let b := 2*k-w+t
  let c := -k+4*w
  let d := -2*k-w-t
  have hs : sumCubes (a,b,c,d) = 6*w*e := by
    calc
      _ = 6*w*(21*w^2-t^2-4*t*k) := by dsimp [sumCubes,a,b,c,d]; ring
      _ = _ := by rw [he]
  have hid : -((a+b)*(c+d)) = (3*k+t)^2-(3*w)^2 := by
    dsimp [a,b,c,d]
    ring
  have hd := first_square_gap hid (show 3*w ≠ 0 by omega) hgap
  have hn : a ≠ b ∨ c ≠ d := by
    by_contra! h
    dsimp [a,b,c,d] at h
    omega
  exact infinitely_from _ a b c d hs hd hn

private theorem infinite_six (r : ℤ) : {v : Quadruple | sumCubes v = 6*r}.Infinite := by
  by_cases hr0 : r = 0
  · simpa [hr0] using infinite_zero
  by_cases hodd : r%2 = 1
  · let k := (21*r^2-5)/8
    have hr : r%8 = 1 ∨ r%8 = 3 ∨ r%8 = 5 ∨ r%8 = 7 := by omega
    have hsq : r^2%8 = 1 := by
      rw [pow_two, Int.mul_emod]
      rcases hr with h|h|h|h <;> rw [h] <;> decide
    have hmod : (21*r^2-5)%8 = 0 := by
      rw [Int.sub_emod, Int.mul_emod 21 (r^2) 8, hsq]
      decide
    have hk : 8*k = 21*r^2-5 := by
      have h := Int.emod_add_mul_ediv (21*r^2-5) 8
      rw [hmod, zero_add] at h
      exact h
    have hsq' : 1 ≤ r^2 := by
      have h := sq_pos_of_ne_zero hr0
      omega
    have hgap : (3*r)^2 < 2*(3*k+2)-1 := by nlinarith only [hk,hsq']
    have he : 21*r^2-2^2-4*2*k = 1 := by linarith only [hk]
    simpa only [mul_one] using infinite_six_seed r k 2 1 hr0 hgap he
  · let u := -(r/2)
    let w := 2*u
    let k := 21*u^2
    have hw : w = -r := by dsimp [w,u]; omega
    have hw0 : w ≠ 0 := by omega
    have hk : 4*k = 21*w^2 := by dsimp only [k,w]; ring
    have hgap : (3*w)^2 < 2*(3*k+1)-1 := by nlinarith only [hk, sq_nonneg w]
    have he : 21*w^2-1^2-4*1*k = -1 := by linarith only [hk]
    have htarget : 6*w*(-1) = 6*r := by rw [hw]; ring
    simpa only [htarget] using infinite_six_seed w k 1 (-1) hw0 hgap he

private theorem infinite_six_three (r : ℤ) :
    {v : Quadruple | sumCubes v = 6*r+3}.Infinite := by
  let a := r
  let b := 2*r-5
  let c := -r+4
  let d := -2*r+4
  have hs : sumCubes (a,b,c,d) = 6*r+3 := by dsimp [sumCubes,a,b,c,d]; ring
  have hne : a ≠ b ∨ c ≠ d := by
    by_contra! h
    dsimp [a,b,c,d] at h
    omega
  have hid : -((a+b)*(c+d)) = (3*r-5)*(3*r-8) := by dsimp [a,b,c,d]; ring
  rcases (show r ≤ 1 ∨ r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with hr|hr|hr|hr
  · have hd : -((a+b)*(c+d)) = (5-3*r)*((5-3*r)+3) := by rw [hid]; ring
    exact infinitely_from _ a b c d hs (hd ▸ three_apart (5-3*r) (by omega)) hne
  · subst r
    exact finite_seed 15 (-10) (-7) 3 11 (by decide) (by decide) (by norm_num) (Or.inl (by decide))
  · subst r
    exact finite_seed 21 (-3) (-2) (-2) 4 (by decide) (by decide) (by norm_num) (Or.inl (by decide))
  · have hd : -((a+b)*(c+d)) = (3*r-8)*((3*r-8)+3) := by rw [hid]; ring
    exact infinitely_from _ a b c d hs (hd ▸ three_apart (3*r-8) (by omega)) hne

private theorem infinite_eighteen_one (r : ℤ) :
    {v : Quadruple | sumCubes v = 18*r+1}.Infinite := by
  let a := 2*r+14
  let b := 3*r+30
  let c := -2*r-23
  let d := -3*r-26
  have hs : sumCubes (a,b,c,d) = 18*r+1 := by dsimp [sumCubes,a,b,c,d]; ring
  have hne : a ≠ b ∨ c ≠ d := by
    by_contra! h
    dsimp [a,b,c,d] at h
    omega
  have hid : -((a+b)*(c+d)) = (5*r+44)*(5*r+49) := by dsimp [a,b,c,d]; ring
  rcases (show r ≤ -11 ∨ r = -10 ∨ r = -9 ∨ r = -8 ∨ -7 ≤ r by omega) with hr|hr|hr|hr|hr
  · have hd : -((a+b)*(c+d)) = (-5*r-49)*((-5*r-49)+5) := by rw [hid]; ring
    exact infinitely_from _ a b c d hs (hd ▸ five_apart (-5*r-49) (by omega)) hne
  · subst r
    exact finite_seed (-179) (-6) 0 (-3) 4 (by decide) (by decide) (by norm_num) (Or.inl (by decide))
  · subst r
    exact finite_seed (-161) (-6) (-2) (-1) 4 (by decide) (by decide) (by norm_num) (Or.inl (by decide))
  · subst r
    exact finite_seed (-143) (-5) (-3) 1 2 (by decide) (by decide) (by norm_num) (Or.inl (by decide))
  · have hd : -((a+b)*(c+d)) = (5*r+44)*((5*r+44)+5) := by rw [hid]; ring
    exact infinitely_from _ a b c d hs (hd ▸ five_apart (5*r+44) (by omega)) hne

private theorem infinite_eighteen_seven (r : ℤ) :
    {v : Quadruple | sumCubes v = 18*r+7}.Infinite := by
  let a := r+2
  let b := 6*r-1
  let c := 8*r-2
  let d := -9*r+2
  rcases lt_trichotomy 0 r with hr|hr|hr
  · have hs : sumCubes (a,c,b,d) = 18*r+7 := by dsimp [sumCubes,a,b,c,d]; ring
    have hid : -((a+c)*(b+d)) = (9*r)*(3*r-1) := by dsimp [a,b,c,d]; ring
    have hd : 0 < -((a+c)*(b+d)) := by rw [hid]; exact mul_pos (by omega) (by omega)
    have hcop : IsCoprime (9*r) (3*r-1) := ⟨r, -(3*r+1), by ring⟩
    have hcast : ((3*r-1 : ℤ) : ZMod 3) = -1 := by
      push_cast
      rw [show (3 : ZMod 3) = 0 by decide, zero_mul, zero_sub]
    have hbad := nonsquare_of_residue (3*r-1) 3 (-1) hcast (by decide)
    refine finite_seed _ a c b d hs hd (fun h => hbad (square_of_coprime_right (by omega) hcop (hid ▸ h))) ?_
    exact Or.inl (by dsimp [a,c]; omega)
  · subst r
    exact finite_seed 7 2 2 (-1) (-2) (by decide) (by decide) (by norm_num) (Or.inr (by decide))
  · have hs : sumCubes (a,b,c,d) = 18*r+7 := by dsimp [sumCubes,a,b,c,d]; ring
    have hid : -((a+b)*(c+d)) = (-r)*(-7*r-1) := by dsimp [a,b,c,d]; ring
    have hd : 0 < -((a+b)*(c+d)) := by rw [hid]; exact mul_pos (by omega) (by omega)
    have hcop : IsCoprime (-r) (-7*r-1) := ⟨7, -1, by ring⟩
    have hcast : ((-7*r-1 : ℤ) : ZMod 7) = -1 := by
      push_cast
      rw [show (7 : ZMod 7) = 0 by decide, neg_zero, zero_mul, zero_sub]
    have hbad := nonsquare_of_residue (-7*r-1) 7 (-1) hcast (by decide)
    refine finite_seed _ a b c d hs hd (fun h => hbad (square_of_coprime_right (by omega) hcop (hid ▸ h))) ?_
    exact Or.inl (by dsimp [a,b]; omega)

private theorem infinite_eighteen_eight (r : ℤ) :
    {v : Quadruple | sumCubes v = 18*r+8}.Infinite := by
  let a := r-5
  let b := 3*r-30
  let c := -r+14
  let d := -3*r+29
  let m := |4*r-39|
  have hs : sumCubes (a,b,c,d) = 18*r+8 := by dsimp [sumCubes,a,b,c,d]; ring
  have hn : a ≠ b := by dsimp [a,b]; omega
  by_cases hh : 9 ≤ m
  · have hid : -((a+b)*(c+d)) = m^2-(4 : ℤ)^2 := by
      dsimp [m,a,b,c,d]
      rw [sq_abs]
      ring
    have hd := first_square_gap hid (by decide) (by omega)
    exact infinitely_from _ a b c d hs hd (Or.inl hn)
  · have hr : r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 := by
      have hl : ¬ (4*r-39 ≤ -9 ∨ 9 ≤ 4*r-39) := fun h => hh (abs_lower h)
      omega
    rcases hr with hr | hr | hr | hr
    · subst r
      exact finite_seed 152 (-5) 3 5 5 (by decide) (by decide) (by norm_num) (Or.inl (by decide))
    · subst r
      exact finite_seed 170 (-3) (-3) 2 6 (by decide) (by decide) (by norm_num) (Or.inr (by decide))
    · subst r
      exact finite_seed 188 (-3) (-1) 0 6 (by decide) (by decide) (by norm_num) (Or.inl (by decide))
    · subst r
      exact finite_seed 206 (-2) (-1) (-1) 6 (by decide) (by decide) (by norm_num) (Or.inl (by decide))

private theorem quotient_form (N d r : ℤ) (h : N % d = r) : N = d*(N/d)+r := by
  have he := Int.emod_add_mul_ediv N d
  rw [h, add_comm] at he
  exact he.symm

theorem OMA.solution : OMA.R_mo_289554_R1.H1 := by
  intro N hN
  change {v : Quadruple | sumCubes v = N}.Infinite
  rcases hN with h|h|h|h
  · rcases (show N%6=0 ∨ N%6=3 by omega) with h0 | h3
    · rw [quotient_form N 6 0 h0, add_zero]
      exact infinite_six (N/6)
    · rw [quotient_form N 6 3 h3]
      exact infinite_six_three (N/6)
  · rw [quotient_form N 18 1 h]
    exact infinite_eighteen_one (N/18)
  · rw [quotient_form N 18 7 h]
    exact infinite_eighteen_seven (N/18)
  · rw [quotient_form N 18 8 h]
    exact infinite_eighteen_eight (N/18)
