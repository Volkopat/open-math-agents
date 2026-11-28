import OMAReductions.R_Erdos91_erdos_91_variants_eight_R1_H1_R1

/-!
# Classification of seven-point sets with at most three distances

We prove `OMA.R_Erdos91_erdos_91_variants_eight_R1_H1_R1.H1`: every 7-point planar set `B` with
`distinctDistances B ≤ 3` satisfies `distinctDistances B = 3` and is either cocircular with radius
`r ∉ distanceSet B` or a regular hexagon together with its centre.
-/

open Finset EuclideanGeometry InnerProductSpace

namespace Erdos91H1

/- ### Part 1: Computable `Frac`, `ℚ(√3)`, and `List`-based polynomial GCD engine -/

private def gcdAux : ℕ → ℕ → ℕ → ℕ
  | 0, a, _ => a
  | n + 1, a, b => if b == 0 then a else gcdAux n b (a % b)

private def fastGcd (a b : ℕ) : ℕ := gcdAux 64 a b

/-- Rational number `n / (dPred + 1)` with strictly positive denominator by construction. -/
private structure Frac where
  n : ℤ
  dPred : ℕ
  deriving DecidableEq

private def Frac.den (a : Frac) : ℕ := a.dPred + 1

private def Frac.mkNorm (n : ℤ) (d : ℕ) : Frac :=
  if n == 0 || d == 0 then ⟨0, 0⟩
  else
    let g := fastGcd n.natAbs d
    if g > 1 && n.natAbs % g == 0 && d % g == 0 then ⟨n / (g : ℤ), d / g - 1⟩
    else ⟨n, d - 1⟩

private def Frac.zero : Frac := ⟨0, 0⟩
private def Frac.one : Frac := ⟨1, 0⟩
private def Frac.ofInt (z : ℤ) : Frac := ⟨z, 0⟩

private def Frac.add (a b : Frac) : Frac :=
  if a.n == 0 then b else if b.n == 0 then a
  else Frac.mkNorm (a.n * (b.den : ℤ) + b.n * (a.den : ℤ)) (a.den * b.den)

private def Frac.sub (a b : Frac) : Frac :=
  if b.n == 0 then a
  else Frac.mkNorm (a.n * (b.den : ℤ) - b.n * (a.den : ℤ)) (a.den * b.den)

private def Frac.neg (a : Frac) : Frac := ⟨-a.n, a.dPred⟩

private def Frac.mul (a b : Frac) : Frac :=
  if a.n == 0 || b.n == 0 then Frac.zero
  else Frac.mkNorm (a.n * b.n) (a.den * b.den)

private def Frac.div (a b : Frac) : Frac :=
  if a.n == 0 then Frac.zero
  else if b.n < 0 then Frac.mkNorm (-(a.n * (b.den : ℤ))) (a.den * b.n.natAbs)
  else Frac.mkNorm (a.n * (b.den : ℤ)) (a.den * b.n.natAbs)

private noncomputable def Frac.toRat (a : Frac) : ℚ := (a.n : ℚ) / (a.den : ℚ)
private noncomputable def Frac.toReal (a : Frac) : ℝ := (a.n : ℝ) / (a.den : ℝ)

private lemma Frac.den_pos (a : Frac) : 0 < a.den := Nat.succ_pos a.dPred
private lemma Frac.den_ne_zero_real (a : Frac) : (a.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_pos.ne'

private lemma Frac.toReal_eq_toRat (a : Frac) : a.toReal = (a.toRat : ℝ) := by
  simp [Frac.toReal, Frac.toRat]

private lemma Frac.toReal_zero : Frac.zero.toReal = 0 := by simp [Frac.toReal, Frac.zero, Frac.den]
private lemma Frac.toReal_one : Frac.one.toReal = 1 := by simp [Frac.toReal, Frac.one, Frac.den]
private lemma Frac.toReal_ofInt (z : ℤ) : (Frac.ofInt z).toReal = (z : ℝ) := by
  simp [Frac.toReal, Frac.ofInt, Frac.den]

private lemma Frac.toReal_mkNorm (n : ℤ) (d : ℕ) :
    (Frac.mkNorm n d).toReal = (n : ℝ) / (d : ℝ) := by
  unfold Frac.mkNorm
  split_ifs with h0
  · simp only [Bool.or_eq_true, beq_iff_eq] at h0
    rcases h0 with rfl | rfl <;> simp [Frac.toReal, Frac.den]
  · simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h0
    dsimp only
    split_ifs with hg
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
      rcases hg with ⟨⟨hg1, hng⟩, hdg⟩
      set g := fastGcd n.natAbs d
      have hg0 : g ≠ 0 := by omega
      have hdg_dvd : g ∣ d := Nat.dvd_of_mod_eq_zero hdg
      have hdg_pos : 0 < d / g := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero h0.2) hdg_dvd) (by omega)
      have hng_dvd : (g : ℤ) ∣ n := by
        have : g ∣ n.natAbs := Nat.dvd_of_mod_eq_zero hng
        exact Int.natCast_dvd.mpr this
      have hden_eq : ((Frac.den ⟨n / (g : ℤ), d / g - 1⟩ : ℕ) : ℝ) = (d : ℝ) / (g : ℝ) := by
        simp only [Frac.den]
        have h1 : d / g - 1 + 1 = d / g := Nat.sub_add_cancel hdg_pos
        rw [h1]
        have h2 : (d / g) * g = d := Nat.div_mul_cancel hdg_dvd
        have h2r : ((d / g : ℕ) : ℝ) * (g : ℝ) = (d : ℝ) := by exact_mod_cast h2
        have hgr : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg0
        exact eq_div_of_mul_eq hgr h2r
      have hnum_eq : ((n / (g : ℤ) : ℤ) : ℝ) = (n : ℝ) / (g : ℝ) := by
        have h2 : (n / (g : ℤ)) * (g : ℤ) = n := Int.ediv_mul_cancel hng_dvd
        have h2r : ((n / (g : ℤ) : ℤ) : ℝ) * (g : ℝ) = (n : ℝ) := by exact_mod_cast h2
        have hgr : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg0
        exact eq_div_of_mul_eq hgr h2r
      simp only [Frac.toReal]
      rw [hnum_eq, hden_eq]
      have hgr : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg0
      field_simp [hgr]
    · have hd_pos : 0 < d := Nat.pos_of_ne_zero h0.2
      simp only [Frac.toReal, Frac.den, Nat.sub_add_cancel hd_pos]

private lemma Frac.toReal_add (a b : Frac) :
    (Frac.add a b).toReal = a.toReal + b.toReal := by
  unfold Frac.add
  split_ifs with ha hb
  · have ha0 : a.n = 0 := beq_iff_eq.mp ha
    simp [Frac.toReal, ha0]
  · have hb0 : b.n = 0 := beq_iff_eq.mp hb
    simp [Frac.toReal, hb0]
  · rw [Frac.toReal_mkNorm]
    simp only [Frac.toReal, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    have ha' := a.den_ne_zero_real
    have hb' := b.den_ne_zero_real
    field_simp [ha', hb']

private lemma Frac.toReal_sub (a b : Frac) :
    (Frac.sub a b).toReal = a.toReal - b.toReal := by
  unfold Frac.sub
  split_ifs with hb
  · have hb0 : b.n = 0 := beq_iff_eq.mp hb
    simp [Frac.toReal, hb0]
  · rw [Frac.toReal_mkNorm]
    simp only [Frac.toReal, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    have ha' := a.den_ne_zero_real
    have hb' := b.den_ne_zero_real
    field_simp [ha', hb']

private lemma Frac.toReal_neg (a : Frac) :
    (Frac.neg a).toReal = -a.toReal := by
  simp [Frac.neg, Frac.toReal, Frac.den, neg_div]

private lemma Frac.toReal_mul (a b : Frac) :
    (Frac.mul a b).toReal = a.toReal * b.toReal := by
  unfold Frac.mul
  split_ifs with h0
  · simp only [Bool.or_eq_true, beq_iff_eq] at h0
    rcases h0 with ha0 | hb0
    · simp [Frac.toReal, Frac.zero, Frac.den, ha0]
    · simp [Frac.toReal, Frac.zero, Frac.den, hb0]
  · rw [Frac.toReal_mkNorm]
    simp only [Frac.toReal, Int.cast_mul, Nat.cast_mul]
    ring

private structure Q3 where
  re : Frac
  im : Frac
  deriving DecidableEq

private def Q3.zero : Q3 := ⟨Frac.zero, Frac.zero⟩
private def Q3.one : Q3 := ⟨Frac.one, Frac.zero⟩
private def Q3.ofInt (z : ℤ) : Q3 := ⟨Frac.ofInt z, Frac.zero⟩
private def Q3.isZero (x : Q3) : Bool := x.re.n == 0 && x.im.n == 0
private def Q3.add (x y : Q3) : Q3 := ⟨Frac.add x.re y.re, Frac.add x.im y.im⟩
private def Q3.sub (x y : Q3) : Q3 := ⟨Frac.sub x.re y.re, Frac.sub x.im y.im⟩
private def Q3.neg (x : Q3) : Q3 := ⟨Frac.neg x.re, Frac.neg x.im⟩

private def Q3.mul (x y : Q3) : Q3 :=
  if x.im.n == 0 && y.im.n == 0 then ⟨Frac.mul x.re y.re, Frac.zero⟩
  else ⟨Frac.add (Frac.mul x.re y.re) (Frac.mul (Frac.ofInt 3) (Frac.mul x.im y.im)),
        Frac.add (Frac.mul x.re y.im) (Frac.mul x.im y.re)⟩

private def Q3.inv (x : Q3) : Q3 :=
  if x.im.n == 0 then ⟨Frac.div Frac.one x.re, Frac.zero⟩
  else
    let d := Frac.sub (Frac.mul x.re x.re) (Frac.mul (Frac.ofInt 3) (Frac.mul x.im x.im))
    ⟨Frac.div x.re d, Frac.div (Frac.neg x.im) d⟩

private def Q3.div (x y : Q3) : Q3 := Q3.mul x (Q3.inv y)

private noncomputable def Q3.toReal (s : ℝ) (x : Q3) : ℝ := x.re.toReal + x.im.toReal * s

private lemma Q3.toReal_zero (s : ℝ) : Q3.toReal s Q3.zero = 0 := by
  simp [Q3.toReal, Q3.zero, Frac.toReal_zero]
private lemma Q3.toReal_one (s : ℝ) : Q3.toReal s Q3.one = 1 := by
  simp [Q3.toReal, Q3.one, Frac.toReal_one, Frac.toReal_zero]
private lemma Q3.toReal_ofInt (s : ℝ) (z : ℤ) : Q3.toReal s (Q3.ofInt z) = (z : ℝ) := by
  simp [Q3.toReal, Q3.ofInt, Frac.toReal_ofInt, Frac.toReal_zero]
private lemma Q3.toReal_add (s : ℝ) (x y : Q3) :
    Q3.toReal s (Q3.add x y) = Q3.toReal s x + Q3.toReal s y := by
  simp only [Q3.toReal, Q3.add, Frac.toReal_add]; ring
private lemma Q3.toReal_sub (s : ℝ) (x y : Q3) :
    Q3.toReal s (Q3.sub x y) = Q3.toReal s x - Q3.toReal s y := by
  simp only [Q3.toReal, Q3.sub, Frac.toReal_sub]; ring
private lemma Q3.toReal_neg (s : ℝ) (x : Q3) :
    Q3.toReal s (Q3.neg x) = -Q3.toReal s x := by
  simp only [Q3.toReal, Q3.neg, Frac.toReal_neg]; ring

private lemma Q3.toReal_mul {s : ℝ} (hs : s ^ 2 = 3) (x y : Q3) :
    Q3.toReal s (Q3.mul x y) = Q3.toReal s x * Q3.toReal s y := by
  unfold Q3.mul
  split_ifs with h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hx0 : x.im.toReal = 0 := by simp [Frac.toReal, h.1]
    have hy0 : y.im.toReal = 0 := by simp [Frac.toReal, h.2]
    simp only [Q3.toReal, Frac.toReal_mul, Frac.toReal_zero, hx0, hy0, zero_mul, add_zero]
  · simp only [Q3.toReal, Frac.toReal_add, Frac.toReal_mul, Frac.toReal_ofInt, Int.cast_ofNat]
    linear_combination -x.im.toReal * y.im.toReal * hs

private lemma Q3.toReal_eq_zero_of_isZero (s : ℝ) {x : Q3} (hx : x.isZero = true) :
    Q3.toReal s x = 0 := by
  simp only [Q3.isZero, Bool.and_eq_true, beq_iff_eq] at hx
  simp [Q3.toReal, Frac.toReal, hx.1, hx.2]

private lemma Q3.toReal_ne_zero_of_not_isZero {s : ℝ} (hs : s ^ 2 = 3) {x : Q3}
    (hx : x.isZero = false) : Q3.toReal s x ≠ 0 := by
  intro h0
  simp only [Q3.isZero, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hx
  rw [Q3.toReal, Frac.toReal_eq_toRat, Frac.toReal_eq_toRat] at h0
  by_cases him : x.im.n = 0
  · have hre : x.re.n ≠ 0 := hx.resolve_right (not_not.mpr him)
    have him0 : x.im.toRat = 0 := by simp [Frac.toRat, him]
    rw [him0, Rat.cast_zero, zero_mul, add_zero] at h0
    have hre0 : x.re.toRat = 0 := Rat.cast_eq_zero.mp h0
    simp only [Frac.toRat, div_eq_zero_iff, Int.cast_eq_zero, Nat.cast_eq_zero] at hre0
    exact hre (hre0.resolve_right x.re.den_pos.ne')
  · have him_ne : x.im.toRat ≠ 0 := by
      simp only [Frac.toRat, ne_eq, div_eq_zero_iff, Int.cast_eq_zero, Nat.cast_eq_zero, not_or]
      exact ⟨him, x.im.den_pos.ne'⟩
    have him_ne_r : (x.im.toRat : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr him_ne
    have hs_eq : s = -((x.re.toRat / x.im.toRat : ℚ) : ℝ) := by
      push_cast
      field_simp [him_ne_r]
      linarith
    have hirr : Irrational (Real.sqrt 3) := irrational_sqrt_ofNat_iff.mpr (by
      intro hsq
      rcases hsq with ⟨k, hk⟩
      have : k ≤ 2 := by nlinarith
      interval_cases k <;> omega)
    apply hirr
    rcases le_total 0 s with hpos | hneg
    · refine ⟨-(x.re.toRat / x.im.toRat), ?_⟩
      rw [Rat.cast_neg, ← hs_eq, ← Real.sqrt_sq hpos, hs]
    · refine ⟨x.re.toRat / x.im.toRat, ?_⟩
      have hneg' : 0 ≤ -s := by linarith
      have : ((x.re.toRat / x.im.toRat : ℚ) : ℝ) = -s := by linarith
      rw [this, ← Real.sqrt_sq hneg', neg_sq, hs]

private abbrev Poly3 := List Q3

private def pTrim : Poly3 → Poly3
  | [] => []
  | a :: l =>
    match pTrim l with
    | [] => if a.isZero then [] else [a]
    | l' => a :: l'

private def pAddAux : Poly3 → Poly3 → Poly3
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => Q3.add a b :: pAddAux p q

private def pAdd (p q : Poly3) : Poly3 := pTrim (pAddAux p q)
private def pNeg (p : Poly3) : Poly3 := p.map Q3.neg
private def pSub (p q : Poly3) : Poly3 := pAdd p (pNeg q)

private def pMulAux : Poly3 → Poly3 → Poly3
  | [], _ => []
  | a :: p, q => pAddAux (q.map (Q3.mul a)) (Q3.zero :: pMulAux p q)

private def pMul (p q : Poly3) : Poly3 := pTrim (pMulAux p q)

private def pLead : Poly3 → Q3
  | [] => Q3.zero
  | [a] => a
  | _ :: l => pLead l

private def pShift (n : ℕ) (p : Poly3) : Poly3 := List.replicate n Q3.zero ++ p

private def pDivStep (p d : Poly3) : Poly3 × Poly3 :=
  if p.length < d.length then ([], p)
  else
    let c := Q3.div (pLead p) (pLead d)
    let k := p.length - d.length
    let qTerm := pShift k [c]
    (qTerm, pSub p (pMul qTerm d))

private def pDivModAux : ℕ → Poly3 → Poly3 → Poly3 × Poly3
  | 0, p, _ => ([], p)
  | n + 1, p, d =>
    if p.length < d.length || d.isEmpty then ([], p)
    else
      let (q1, r1) := pDivStep p d
      let (q2, r2) := pDivModAux n r1 d
      (pAdd q1 q2, r2)

private def pDivMod (p d : Poly3) : Poly3 × Poly3 := pDivModAux (p.length + 1) p d
private def pMod (p d : Poly3) : Poly3 := (pDivMod p d).2

private def pGcdAux : ℕ → Poly3 → Poly3 → Poly3
  | 0, p, _ => p
  | n + 1, p, q =>
    if q.isEmpty then p
    else pGcdAux n q (pMod p q)

private def pGcd (p q : Poly3) : Poly3 := pGcdAux (p.length + q.length + 2) (pTrim p) (pTrim q)

private def pStripAux : ℕ → Poly3 → Poly3 → Poly3
  | 0, g, _ => g
  | n + 1, g, bad =>
    if g.length ≤ 1 then g
    else
      let d := pGcd g bad
      if d.length ≤ 1 then g
      else
        let (q, r) := pDivMod g d
        if r.isEmpty && (pDivMod bad d).2.isEmpty then pStripAux n q bad else g

private def pStrip (g bad : Poly3) : Poly3 := pStripAux 8 (pTrim g) (pTrim bad)

private noncomputable def pEval (s t : ℝ) : Poly3 → ℝ
  | [] => 0
  | a :: l => Q3.toReal s a + t * pEval s t l

private lemma pEval_trim (s t : ℝ) (p : Poly3) : pEval s t (pTrim p) = pEval s t p := by
  induction p with
  | nil => rfl
  | cons a l ih =>
    dsimp only [pTrim]
    cases h : pTrim l with
    | nil =>
      have hl : pEval s t l = 0 := by rw [← ih, h]; rfl
      cases ha : a.isZero
      · simp [pEval, hl]
      · simp [pEval, hl, Q3.toReal_eq_zero_of_isZero s ha]
    | cons b l' =>
      simp only [pEval, ← ih, h]

private lemma pEval_addAux (s t : ℝ) (p q : Poly3) :
    pEval s t (pAddAux p q) = pEval s t p + pEval s t q := by
  induction p generalizing q with
  | nil => simp [pAddAux, pEval]
  | cons a p ih =>
    cases q with
    | nil => simp [pAddAux, pEval]
    | cons b q => simp only [pAddAux, pEval, ih, Q3.toReal_add]; ring

private lemma pEval_add (s t : ℝ) (p q : Poly3) :
    pEval s t (pAdd p q) = pEval s t p + pEval s t q := by
  rw [pAdd, pEval_trim, pEval_addAux]

private lemma pEval_neg (s t : ℝ) (p : Poly3) :
    pEval s t (pNeg p) = -pEval s t p := by
  induction p with
  | nil => simp [pNeg, pEval]
  | cons a p ih =>
    dsimp only [pNeg] at ih ⊢
    simp only [List.map_cons, pEval, ih, Q3.toReal_neg]
    ring

private lemma pEval_sub (s t : ℝ) (p q : Poly3) :
    pEval s t (pSub p q) = pEval s t p - pEval s t q := by
  rw [pSub, pEval_add, pEval_neg]; ring

private lemma pEval_map_mul {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) (c : Q3) (p : Poly3) :
    pEval s t (p.map (Q3.mul c)) = Q3.toReal s c * pEval s t p := by
  induction p with
  | nil => simp [pEval]
  | cons a p ih => simp only [List.map_cons, pEval, ih, Q3.toReal_mul hs]; ring

private lemma pEval_mulAux {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) (p q : Poly3) :
    pEval s t (pMulAux p q) = pEval s t p * pEval s t q := by
  induction p with
  | nil => simp [pMulAux, pEval]
  | cons a p ih =>
    simp only [pMulAux, pEval_addAux, pEval_map_mul hs, pEval, Q3.toReal_zero, zero_add, ih]; ring

private lemma pEval_mul {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) (p q : Poly3) :
    pEval s t (pMul p q) = pEval s t p * pEval s t q := by
  rw [pMul, pEval_trim, pEval_mulAux hs]

private lemma pEval_divModAux {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) (n : ℕ) (p d : Poly3) :
    pEval s t p = pEval s t (pDivModAux n p d).1 * pEval s t d + pEval s t (pDivModAux n p d).2 := by
  induction n generalizing p with
  | zero => simp [pDivModAux, pEval]
  | succ n ih =>
    dsimp only [pDivModAux]
    split_ifs with h
    · simp [pEval]
    · dsimp only [pDivStep]
      split_ifs with hlt
      · dsimp only
        rw [pEval_add, pEval, zero_add]
        exact ih p
      · dsimp only
        have ih' := ih (pSub p (pMul (pShift (p.length - d.length) [Q3.div (pLead p) (pLead d)]) d))
        rw [pEval_sub, pEval_mul hs] at ih'
        rw [pEval_add]
        linarith

private lemma pEval_divMod {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) (p d : Poly3) :
    pEval s t p = pEval s t (pDivMod p d).1 * pEval s t d + pEval s t (pDivMod p d).2 :=
  pEval_divModAux hs t (p.length + 1) p d

private lemma pEval_gcdAux_eq_zero {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) (n : ℕ) (p q : Poly3)
    (hp : pEval s t p = 0) (hq : pEval s t q = 0) :
    pEval s t (pGcdAux n p q) = 0 := by
  induction n generalizing p q with
  | zero => exact hp
  | succ n ih =>
    dsimp only [pGcdAux]
    split_ifs with hq0
    · exact hp
    · apply ih q (pMod p q) hq
      have hdm := pEval_divMod hs t p q
      dsimp only [pMod]
      rw [hp, hq, mul_zero, zero_add] at hdm
      exact hdm.symm

private lemma pEval_gcd_eq_zero {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) (p q : Poly3)
    (hp : pEval s t p = 0) (hq : pEval s t q = 0) :
    pEval s t (pGcd p q) = 0 :=
  pEval_gcdAux_eq_zero hs t _ (pTrim p) (pTrim q) (by rwa [pEval_trim]) (by rwa [pEval_trim])

private lemma pEval_div_of_dvd {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) {g d : Poly3}
    (hg : pEval s t g = 0) (hd_ne : pEval s t d ≠ 0) (hr : (pDivMod g d).2.isEmpty = true) :
    pEval s t (pDivMod g d).1 = 0 := by
  have hdm := pEval_divMod hs t g d
  have hr0 : (pDivMod g d).2 = [] := List.isEmpty_iff.mp hr
  rw [hr0, pEval, add_zero, hg] at hdm
  exact (mul_eq_zero.mp hdm.symm).resolve_right hd_ne

private lemma pEval_stripAux_eq_zero {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) (n : ℕ) (g bad : Poly3)
    (hg : pEval s t g = 0) (hbad : pEval s t bad ≠ 0) :
    pEval s t (pStripAux n g bad) = 0 := by
  induction n generalizing g with
  | zero => exact hg
  | succ n ih =>
    dsimp only [pStripAux]
    split_ifs with h1 h2 h3
    · exact hg
    · exact hg
    · rcases Bool.and_eq_true_iff.mp h3 with ⟨hr1, hr2⟩
      apply ih
      have hd_ne : pEval s t (pGcd g bad) ≠ 0 := by
        intro hd0
        have hdm := pEval_divMod hs t bad (pGcd g bad)
        have hr2' : (pDivMod bad (pGcd g bad)).2 = [] := List.isEmpty_iff.mp hr2
        rw [hr2', pEval, add_zero, hd0, mul_zero] at hdm
        exact hbad hdm
      exact pEval_div_of_dvd hs t hg hd_ne hr1
    · exact hg

private lemma pEval_strip_eq_zero {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) (g bad : Poly3)
    (hg : pEval s t g = 0) (hbad : pEval s t bad ≠ 0) :
    pEval s t (pStrip g bad) = 0 :=
  pEval_stripAux_eq_zero hs t 8 (pTrim g) (pTrim bad)
    (by rwa [pEval_trim]) (by rwa [pEval_trim])

private def isNonzeroConst (g : Poly3) : Bool :=
  match g with
  | [c] => !c.isZero
  | _ => false

private lemma pEval_ne_zero_of_isNonzeroConst {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) {g : Poly3}
    (h : isNonzeroConst g = true) : pEval s t g ≠ 0 := by
  cases g with
  | nil => simp [isNonzeroConst] at h
  | cons c l =>
    cases l with
    | nil =>
      simp only [isNonzeroConst, Bool.not_eq_true'] at h
      simp only [pEval, mul_zero, add_zero]
      exact Q3.toReal_ne_zero_of_not_isZero hs h
    | cons _ _ => simp [isNonzeroConst] at h

private def isLinearRoot (r : Q3) (g : Poly3) : Bool :=
  match g with
  | [c0, c1] => !c1.isZero && (Q3.add c0 (Q3.mul c1 r)).isZero
  | _ => false

private lemma eq_of_isLinearRoot {s : ℝ} (hs : s ^ 2 = 3) {t : ℝ} {r : Q3} {g : Poly3}
    (hlin : isLinearRoot r g = true) (h0 : pEval s t g = 0) : t = Q3.toReal s r := by
  cases g with
  | nil => simp [isLinearRoot] at hlin
  | cons c0 l =>
    cases l with
    | nil => simp [isLinearRoot] at hlin
    | cons c1 l2 =>
      cases l2 with
      | nil =>
        simp only [isLinearRoot, Bool.and_eq_true, Bool.not_eq_true'] at hlin
        have hc1 : Q3.toReal s c1 ≠ 0 := Q3.toReal_ne_zero_of_not_isZero hs hlin.1
        have hsum : Q3.toReal s c0 + Q3.toReal s c1 * Q3.toReal s r = 0 := by
          have := Q3.toReal_eq_zero_of_isZero s hlin.2
          rwa [Q3.toReal_add, Q3.toReal_mul hs] at this
        simp only [pEval, mul_zero, add_zero] at h0
        have hdiff : Q3.toReal s c1 * (t - Q3.toReal s r) = 0 := by linarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hc1)
      | cons _ _ => simp [isLinearRoot] at hlin

private def pick3 {α : Type} (P0 P1 P2 : α) (i : Fin 3) : α :=
  match i with
  | 0 => P0
  | 1 => P1
  | 2 => P2

private def evalQ (A B h x y : Poly3) : Poly3 :=
  pAdd (pSub (pMul B (pMul x x)) (pMul h (pMul x y))) (pMul A (pMul y y))

private def allWords : List (Fin 3 × Fin 3 × Fin 3 × Fin 3) :=
  (List.finRange 3).flatMap fun a =>
    (List.finRange 3).flatMap fun b =>
      (List.finRange 3).flatMap fun c =>
        (List.finRange 3).map fun d => (a, b, c, d)

private lemma mem_allWords (w : Fin 3 × Fin 3 × Fin 3 × Fin 3) : w ∈ allWords := by
  rcases w with ⟨a, b, c, d⟩
  simp [allWords]

private def wordX (P0 P1 P2 : Poly3) (iA : Fin 3) (w : Fin 3 × Fin 3 × Fin 3 × Fin 3) : Poly3 :=
  pSub (pAdd (pick3 P0 P1 P2 iA) (pick3 P0 P1 P2 w.2.1)) (pick3 P0 P1 P2 w.2.2.1)

private def wordY (P0 P1 P2 : Poly3) (iB : Fin 3) (w : Fin 3 × Fin 3 × Fin 3 × Fin 3) : Poly3 :=
  pSub (pAdd (pick3 P0 P1 P2 iB) (pick3 P0 P1 P2 w.2.1)) (pick3 P0 P1 P2 w.2.2.2)

private def wordG (P0 P1 P2 : Poly3) (iA iB iC : Fin 3) (w : Fin 3 × Fin 3 × Fin 3 × Fin 3) :
    Poly3 × Poly3 × Poly3 :=
  let A := pick3 P0 P1 P2 iA
  let B := pick3 P0 P1 P2 iB
  let C := pick3 P0 P1 P2 iC
  let h := pSub (pAdd A B) C
  let D := pSub (pMul [Q3.ofInt 4] (pMul A B)) (pMul h h)
  let bad := pMul D (pMul P0 (pMul P1 (pMul P2
    (pMul (pSub P0 P1) (pMul (pSub P0 P2) (pSub P1 P2))))))
  let o := pick3 P0 P1 P2 w.1
  let u := pick3 P0 P1 P2 w.2.1
  let x := wordX P0 P1 P2 iA w
  let y := wordY P0 P1 P2 iB w
  let e1 := pSub (evalQ A B h x y) (pMul D u)
  let e2 := pSub (evalQ A B h (pSub x A) (pSub y B)) (pMul D o)
  (x, y, pStrip (pGcd e1 e2) bad)

private def pairPoly (P0 P1 P2 : Poly3) (A B h D x1 y1 x2 y2 : Poly3) : Poly3 :=
  let s := evalQ A B h (pSub x1 x2) (pSub y1 y2)
  pMul (pSub s (pMul D P0)) (pMul (pSub s (pMul D P1)) (pSub s (pMul D P2)))

private def checkPairAux {α : Type} (skipFirst : α → Bool) (F : α → α → Bool) : List α → Bool
  | [] => true
  | x :: rest => (skipFirst x || rest.all (fun y => F x y)) && checkPairAux skipFirst F rest

private lemma checkPairAux_sound {α : Type} (skipFirst : α → Bool) (F : α → α → Bool) (L : List α)
    (h : checkPairAux skipFirst F L = true) {a b : α} (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b)
    (hsa : skipFirst a = false) (hsb : skipFirst b = false) :
    F a b = true ∨ F b a = true := by
  induction L with
  | nil => simp at ha
  | cons x rest ih =>
    simp only [checkPairAux, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · rcases h.1 with hsk | hall
      · rw [hsa] at hsk; cases hsk
      · exact Or.inl (hall b hb')
    · rcases h.1 with hsk | hall
      · rw [hsb] at hsk; cases hsk
      · exact Or.inr (hall a ha')
    · exact ih h.2 ha' hb'

private def checkTriplesList {α : Type} (pairKill : α → α → Bool) (F : α → α → α → Bool) :
    List α → Bool
  | [] => true
  | x :: rest =>
    checkPairAux (fun y => pairKill x y) (fun y z => pairKill x z || pairKill y z || F x y z) rest &&
    checkTriplesList pairKill F rest

private lemma checkTriplesList_sound {α : Type} (pairKill : α → α → Bool) (F : α → α → α → Bool)
    (L : List α) (h : checkTriplesList pairKill F L = true) {a b c : α}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpk : ∀ u v, (u = a ∨ u = b ∨ u = c) → (v = a ∨ v = b ∨ v = c) → u ≠ v → pairKill u v = false) :
    F a b c = true ∨ F a c b = true ∨ F b a c = true ∨
    F b c a = true ∨ F c a b = true ∨ F c b a = true := by
  induction L with
  | nil => simp at ha
  | cons x rest ih =>
    simp only [checkTriplesList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have hb' : b ∈ rest := (List.mem_cons.mp hb).resolve_left hab.symm
      have hc' : c ∈ rest := (List.mem_cons.mp hc).resolve_left hac.symm
      rcases checkPairAux_sound _ _ rest h.1 hb' hc' hbc
        (hpk a b (Or.inl rfl) (Or.inr (Or.inl rfl)) hab)
        (hpk a c (Or.inl rfl) (Or.inr (Or.inr rfl)) hac) with h1 | h1
      · rw [hpk a c (Or.inl rfl) (Or.inr (Or.inr rfl)) hac,
            hpk b c (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hbc] at h1
        simp only [Bool.false_or] at h1; exact Or.inl h1
      · rw [hpk a b (Or.inl rfl) (Or.inr (Or.inl rfl)) hab,
            hpk c b (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hbc.symm] at h1
        simp only [Bool.false_or] at h1; exact Or.inr (Or.inl h1)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · have hc' : c ∈ rest := (List.mem_cons.mp hc).resolve_left hbc.symm
        rcases checkPairAux_sound _ _ rest h.1 ha' hc' hac
          (hpk b a (Or.inr (Or.inl rfl)) (Or.inl rfl) hab.symm)
          (hpk b c (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hbc) with h1 | h1
        · rw [hpk b c (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hbc,
              hpk a c (Or.inl rfl) (Or.inr (Or.inr rfl)) hac] at h1
          simp only [Bool.false_or] at h1; exact Or.inr (Or.inr (Or.inl h1))
        · rw [hpk b a (Or.inr (Or.inl rfl)) (Or.inl rfl) hab.symm,
              hpk c a (Or.inr (Or.inr rfl)) (Or.inl rfl) hac.symm] at h1
          simp only [Bool.false_or] at h1; exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
      · rcases List.mem_cons.mp hc with rfl | hc'
        · rcases checkPairAux_sound _ _ rest h.1 ha' hb' hab
            (hpk c a (Or.inr (Or.inr rfl)) (Or.inl rfl) hac.symm)
            (hpk c b (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hbc.symm) with h1 | h1
          · rw [hpk c b (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hbc.symm,
                hpk a b (Or.inl rfl) (Or.inr (Or.inl rfl)) hab] at h1
            simp only [Bool.false_or] at h1; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
          · rw [hpk c a (Or.inr (Or.inr rfl)) (Or.inl rfl) hac.symm,
                hpk b a (Or.inr (Or.inl rfl)) (Or.inl rfl) hab.symm] at h1
            simp only [Bool.false_or] at h1; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
        · exact ih h.2 ha' hb' hc'

private def pairKill (P0 P1 P2 A B h D : Poly3)
    (p1 p2 : (Fin 3 × Fin 3 × Fin 3 × Fin 3) × Poly3 × Poly3 × Poly3) : Bool :=
  let g0 := pGcd p1.2.2.2 p2.2.2.2
  if isNonzeroConst g0 then true
  else isNonzeroConst (pGcd g0 (pairPoly P0 P1 P2 A B h D p1.2.1 p1.2.2.1 p2.2.1 p2.2.2.1))

private def tripleCheck (P0 P1 P2 A B h D bad : Poly3)
    (ok : (Fin 3 × Fin 3 × Fin 3 × Fin 3) → (Fin 3 × Fin 3 × Fin 3 × Fin 3) →
      (Fin 3 × Fin 3 × Fin 3 × Fin 3) → Poly3 → Bool)
    (p1 p2 p3 : (Fin 3 × Fin 3 × Fin 3 × Fin 3) × Poly3 × Poly3 × Poly3) : Bool :=
  let g0 := pGcd (pGcd p1.2.2.2 p2.2.2.2) p3.2.2.2
  if isNonzeroConst g0 then true
  else
    let g1 := pGcd g0 (pairPoly P0 P1 P2 A B h D p1.2.1 p1.2.2.1 p2.2.1 p2.2.2.1)
    if isNonzeroConst g1 then true
    else
      let g2 := pGcd g1 (pairPoly P0 P1 P2 A B h D p1.2.1 p1.2.2.1 p3.2.1 p3.2.2.1)
      if isNonzeroConst g2 then true
      else
        let g3 := pGcd g2 (pairPoly P0 P1 P2 A B h D p2.2.1 p2.2.2.1 p3.2.1 p3.2.2.1)
        if isNonzeroConst g3 then true
        else
          let g4 := pStrip g3 bad
          isNonzeroConst g4 || ok p1.1 p2.1 p3.1 g4

private def checkSeed (P0 P1 P2 : Poly3) (iA iB iC : Fin 3)
    (ok : (Fin 3 × Fin 3 × Fin 3 × Fin 3) → (Fin 3 × Fin 3 × Fin 3 × Fin 3) →
      (Fin 3 × Fin 3 × Fin 3 × Fin 3) → Poly3 → Bool) : Bool :=
  let A := pick3 P0 P1 P2 iA
  let B := pick3 P0 P1 P2 iB
  let C := pick3 P0 P1 P2 iC
  let h := pSub (pAdd A B) C
  let D := pSub (pMul [Q3.ofInt 4] (pMul A B)) (pMul h h)
  let bad := pMul D (pMul P0 (pMul P1 (pMul P2
    (pMul (pSub P0 P1) (pMul (pSub P0 P2) (pSub P1 P2))))))
  let pts := allWords.filterMap fun w =>
    let r := wordG P0 P1 P2 iA iB iC w
    if isNonzeroConst r.2.2 then none else some (w, r)
  checkTriplesList (pairKill P0 P1 P2 A B h D) (tripleCheck P0 P1 P2 A B h D bad ok) pts

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private lemma seed_001_ok :
    checkSeed [Q3.one] [Q3.ofInt 3] [Q3.zero, Q3.one] 0 0 1
      (fun w1 w2 w3 g => isLinearRoot (Q3.ofInt 4) g &&
        ((w1.1 == 0 && w2.1 == 0 && w3.1 == 0) || (w1.2.1 == 0 && w2.2.1 == 0 && w3.2.1 == 0))) = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private lemma seed_111_ok :
    checkSeed [Q3.one] [Q3.ofInt 3] [Q3.zero, Q3.one] 1 1 1
      (fun w1 w2 w3 g => isLinearRoot (Q3.ofInt 4) g &&
        (w1.1 == 0 && w2.1 == 0 && w3.1 == 0)) = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private lemma seed_112_ok :
    checkSeed [Q3.one] [Q3.zero, Q3.one] [Q3.zero, Q3.ofInt 4, Q3.ofInt (-1)] 1 1 2
      (fun _ _ _ _ => false) = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private lemma seed_011_ok :
    checkSeed [Q3.one] [⟨Frac.ofInt 2, Frac.one⟩] [Q3.zero, Q3.one] 0 1 1
      (fun _ _ _ _ => false) = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private lemma seed_012_ok :
    checkSeed [Q3.one, Q3.ofInt (-1), Q3.one] [Q3.ofInt 3] [Q3.one, Q3.ofInt 2, Q3.one] 0 1 2
      (fun w1 w2 w3 g => (isLinearRoot Q3.one g || isLinearRoot ⟨⟨1, 1⟩, Frac.zero⟩ g) &&
        (w1.1 == 0 && w2.1 == 0 && w3.1 == 0)) = true := by
  decide

private lemma wordG_fst (P0 P1 P2 : Poly3) (iA iB iC : Fin 3) (w : Fin 3 × Fin 3 × Fin 3 × Fin 3) :
    (wordG P0 P1 P2 iA iB iC w).1 = wordX P0 P1 P2 iA w := rfl

private lemma wordG_snd_fst (P0 P1 P2 : Poly3) (iA iB iC : Fin 3) (w : Fin 3 × Fin 3 × Fin 3 × Fin 3) :
    (wordG P0 P1 P2 iA iB iC w).2.1 = wordY P0 P1 P2 iB w := rfl

private lemma wordG_snd_snd (P0 P1 P2 : Poly3) (iA iB iC : Fin 3) (w : Fin 3 × Fin 3 × Fin 3 × Fin 3) :
    (wordG P0 P1 P2 iA iB iC w).2.2 =
      let A := pick3 P0 P1 P2 iA
      let B := pick3 P0 P1 P2 iB
      let C := pick3 P0 P1 P2 iC
      let h := pSub (pAdd A B) C
      let D := pSub (pMul [Q3.ofInt 4] (pMul A B)) (pMul h h)
      let bad := pMul D (pMul P0 (pMul P1 (pMul P2
        (pMul (pSub P0 P1) (pMul (pSub P0 P2) (pSub P1 P2))))))
      let o := pick3 P0 P1 P2 w.1
      let u := pick3 P0 P1 P2 w.2.1
      let x := wordX P0 P1 P2 iA w
      let y := wordY P0 P1 P2 iB w
      pStrip (pGcd (pSub (evalQ A B h x y) (pMul D u))
                   (pSub (evalQ A B h (pSub x A) (pSub y B)) (pMul D o))) bad := rfl

private lemma checkSeed_sound (P0 P1 P2 : Poly3) (iA iB iC : Fin 3)
    (ok : (Fin 3 × Fin 3 × Fin 3 × Fin 3) → (Fin 3 × Fin 3 × Fin 3 × Fin 3) →
      (Fin 3 × Fin 3 × Fin 3 × Fin 3) → Poly3 → Bool)
    (hcheck : checkSeed P0 P1 P2 iA iB iC ok = true)
    {s t : ℝ} (hs : s ^ 2 = 3)
    (hbad : pEval s t (
      let A := pick3 P0 P1 P2 iA
      let B := pick3 P0 P1 P2 iB
      let C := pick3 P0 P1 P2 iC
      let h := pSub (pAdd A B) C
      let D := pSub (pMul [Q3.ofInt 4] (pMul A B)) (pMul h h)
      pMul D (pMul P0 (pMul P1 (pMul P2
        (pMul (pSub P0 P1) (pMul (pSub P0 P2) (pSub P1 P2))))))) ≠ 0)
    (w1 w2 w3 : Fin 3 × Fin 3 × Fin 3 × Fin 3)
    (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h23 : w2 ≠ w3)
    (hword : ∀ w, w = w1 ∨ w = w2 ∨ w = w3 →
      let A := pick3 P0 P1 P2 iA
      let B := pick3 P0 P1 P2 iB
      let C := pick3 P0 P1 P2 iC
      let h := pSub (pAdd A B) C
      let D := pSub (pMul [Q3.ofInt 4] (pMul A B)) (pMul h h)
      let o := pick3 P0 P1 P2 w.1
      let u := pick3 P0 P1 P2 w.2.1
      let x := wordX P0 P1 P2 iA w
      let y := wordY P0 P1 P2 iB w
      pEval s t (pSub (evalQ A B h x y) (pMul D u)) = 0 ∧
      pEval s t (pSub (evalQ A B h (pSub x A) (pSub y B)) (pMul D o)) = 0)
    (hpair : ∀ wa wb, (wa = w1 ∨ wa = w2 ∨ wa = w3) → (wb = w1 ∨ wb = w2 ∨ wb = w3) → wa ≠ wb →
      let A := pick3 P0 P1 P2 iA
      let B := pick3 P0 P1 P2 iB
      let C := pick3 P0 P1 P2 iC
      let h := pSub (pAdd A B) C
      let D := pSub (pMul [Q3.ofInt 4] (pMul A B)) (pMul h h)
      pEval s t (pairPoly P0 P1 P2 A B h D
        (wordX P0 P1 P2 iA wa) (wordY P0 P1 P2 iB wa)
        (wordX P0 P1 P2 iA wb) (wordY P0 P1 P2 iB wb)) = 0) :
    ∃ g : Poly3, pEval s t g = 0 ∧
      (ok w1 w2 w3 g = true ∨ ok w1 w3 w2 g = true ∨ ok w2 w1 w3 g = true ∨
       ok w2 w3 w1 g = true ∨ ok w3 w1 w2 g = true ∨ ok w3 w2 w1 g = true) := by
  let A := pick3 P0 P1 P2 iA
  let B := pick3 P0 P1 P2 iB
  let C := pick3 P0 P1 P2 iC
  let h := pSub (pAdd A B) C
  let D := pSub (pMul [Q3.ofInt 4] (pMul A B)) (pMul h h)
  let bad := pMul D (pMul P0 (pMul P1 (pMul P2
    (pMul (pSub P0 P1) (pMul (pSub P0 P2) (pSub P1 P2))))))
  let pts := allWords.filterMap fun w =>
    let r := wordG P0 P1 P2 iA iB iC w
    if isNonzeroConst r.2.2 then none else some (w, r)
  have hwg0 : ∀ w, w = w1 ∨ w = w2 ∨ w = w3 → pEval s t (wordG P0 P1 P2 iA iB iC w).2.2 = 0 := by
    intro w hw
    obtain ⟨he1, he2⟩ := hword w hw
    rw [wordG_snd_snd]
    exact pEval_strip_eq_zero hs t _ bad (pEval_gcd_eq_zero hs t _ _ he1 he2) hbad
  have hnc_false : ∀ g : Poly3, pEval s t g = 0 → isNonzeroConst g = false := by
    intro g hg
    cases hc : isNonzeroConst g
    · rfl
    · exact absurd hg (pEval_ne_zero_of_isNonzeroConst hs t hc)
  have hmem_pts : ∀ w, w = w1 ∨ w = w2 ∨ w = w3 → (w, wordG P0 P1 P2 iA iB iC w) ∈ pts := by
    intro w hw
    apply List.mem_filterMap.mpr
    refine ⟨w, mem_allWords w, ?_⟩
    simp [hnc_false _ (hwg0 w hw)]
  let p1 := (w1, wordG P0 P1 P2 iA iB iC w1)
  let p2 := (w2, wordG P0 P1 P2 iA iB iC w2)
  let p3 := (w3, wordG P0 P1 P2 iA iB iC w3)
  have hp12 : p1 ≠ p2 := fun h => h12 (congrArg Prod.fst h)
  have hp13 : p1 ≠ p3 := fun h => h13 (congrArg Prod.fst h)
  have hp23 : p2 ≠ p3 := fun h => h23 (congrArg Prod.fst h)
  have hpk_false : ∀ pa pb, (pa = p1 ∨ pa = p2 ∨ pa = p3) → (pb = p1 ∨ pb = p2 ∨ pb = p3) →
      pa ≠ pb → pairKill P0 P1 P2 A B h D pa pb = false := by
    intro pa pb hpa hpb hne
    have hwa : pa.1 = w1 ∨ pa.1 = w2 ∨ pa.1 = w3 := by
      rcases hpa with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have hwb : pb.1 = w1 ∨ pb.1 = w2 ∨ pb.1 = w3 := by
      rcases hpb with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have hwne : pa.1 ≠ pb.1 := by
      rcases hpa with rfl | rfl | rfl <;> rcases hpb with rfl | rfl | rfl <;>
        first | exact absurd rfl hne | exact h12 | exact h13 | exact h23 |
          exact h12.symm | exact h13.symm | exact h23.symm
    have hga : pEval s t pa.2.2.2 = 0 := by
      rcases hpa with rfl | rfl | rfl
      · exact hwg0 w1 (Or.inl rfl)
      · exact hwg0 w2 (Or.inr (Or.inl rfl))
      · exact hwg0 w3 (Or.inr (Or.inr rfl))
    have hgb : pEval s t pb.2.2.2 = 0 := by
      rcases hpb with rfl | rfl | rfl
      · exact hwg0 w1 (Or.inl rfl)
      · exact hwg0 w2 (Or.inr (Or.inl rfl))
      · exact hwg0 w3 (Or.inr (Or.inr rfl))
    have hpa1 : pa.2.1 = wordX P0 P1 P2 iA pa.1 := by rcases hpa with rfl | rfl | rfl <;> rfl
    have hpa2 : pa.2.2.1 = wordY P0 P1 P2 iB pa.1 := by rcases hpa with rfl | rfl | rfl <;> rfl
    have hpb1 : pb.2.1 = wordX P0 P1 P2 iA pb.1 := by rcases hpb with rfl | rfl | rfl <;> rfl
    have hpb2 : pb.2.2.1 = wordY P0 P1 P2 iB pb.1 := by rcases hpb with rfl | rfl | rfl <;> rfl
    have hg0 : pEval s t (pGcd pa.2.2.2 pb.2.2.2) = 0 := pEval_gcd_eq_zero hs t _ _ hga hgb
    have hpab : pEval s t (pairPoly P0 P1 P2 A B h D pa.2.1 pa.2.2.1 pb.2.1 pb.2.2.1) = 0 := by
      rw [hpa1, hpa2, hpb1, hpb2]; exact hpair pa.1 pb.1 hwa hwb hwne
    have hg1 := pEval_gcd_eq_zero hs t _ _ hg0 hpab
    dsimp only [pairKill]
    rw [hnc_false _ hg0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hnc_false _ hg1
  have htrip := checkTriplesList_sound (pairKill P0 P1 P2 A B h D)
    (tripleCheck P0 P1 P2 A B h D bad ok) pts hcheck
    (hmem_pts w1 (Or.inl rfl)) (hmem_pts w2 (Or.inr (Or.inl rfl)))
    (hmem_pts w3 (Or.inr (Or.inr rfl))) hp12 hp13 hp23 hpk_false
  have hstep : ∀ pa pb pc : (Fin 3 × Fin 3 × Fin 3 × Fin 3) × Poly3 × Poly3 × Poly3,
      (pa.1 = w1 ∨ pa.1 = w2 ∨ pa.1 = w3) →
      (pb.1 = w1 ∨ pb.1 = w2 ∨ pb.1 = w3) →
      (pc.1 = w1 ∨ pc.1 = w2 ∨ pc.1 = w3) →
      pa.1 ≠ pb.1 → pa.1 ≠ pc.1 → pb.1 ≠ pc.1 →
      pa.2 = wordG P0 P1 P2 iA iB iC pa.1 →
      pb.2 = wordG P0 P1 P2 iA iB iC pb.1 →
      pc.2 = wordG P0 P1 P2 iA iB iC pc.1 →
      tripleCheck P0 P1 P2 A B h D bad ok pa pb pc = true →
      ∃ g : Poly3, pEval s t g = 0 ∧ ok pa.1 pb.1 pc.1 g = true := by
    intro pa pb pc ha hb hc hab hac hbc hpa hpb hpc htc
    dsimp only [tripleCheck] at htc
    have hga : pEval s t pa.2.2.2 = 0 := by rw [hpa]; exact hwg0 pa.1 ha
    have hgb : pEval s t pb.2.2.2 = 0 := by rw [hpb]; exact hwg0 pb.1 hb
    have hgc : pEval s t pc.2.2.2 = 0 := by rw [hpc]; exact hwg0 pc.1 hc
    have hg0 : pEval s t (pGcd (pGcd pa.2.2.2 pb.2.2.2) pc.2.2.2) = 0 :=
      pEval_gcd_eq_zero hs t _ _ (pEval_gcd_eq_zero hs t _ _ hga hgb) hgc
    have hpab : pEval s t (pairPoly P0 P1 P2 A B h D pa.2.1 pa.2.2.1 pb.2.1 pb.2.2.1) = 0 := by
      rw [hpa, hpb, wordG_fst, wordG_snd_fst, wordG_fst, wordG_snd_fst]
      exact hpair pa.1 pb.1 ha hb hab
    have hpac : pEval s t (pairPoly P0 P1 P2 A B h D pa.2.1 pa.2.2.1 pc.2.1 pc.2.2.1) = 0 := by
      rw [hpa, hpc, wordG_fst, wordG_snd_fst, wordG_fst, wordG_snd_fst]
      exact hpair pa.1 pc.1 ha hc hac
    have hpbc : pEval s t (pairPoly P0 P1 P2 A B h D pb.2.1 pb.2.2.1 pc.2.1 pc.2.2.1) = 0 := by
      rw [hpb, hpc, wordG_fst, wordG_snd_fst, wordG_fst, wordG_snd_fst]
      exact hpair pb.1 pc.1 hb hc hbc
    have hg1 := pEval_gcd_eq_zero hs t _ _ hg0 hpab
    have hg2 := pEval_gcd_eq_zero hs t _ _ hg1 hpac
    have hg3 := pEval_gcd_eq_zero hs t _ _ hg2 hpbc
    have hg4 := pEval_strip_eq_zero hs t _ bad hg3 hbad
    rw [hnc_false _ hg0] at htc; simp only [Bool.false_eq_true, ↓reduceIte] at htc
    rw [hnc_false _ hg1] at htc; simp only [Bool.false_eq_true, ↓reduceIte] at htc
    rw [hnc_false _ hg2] at htc; simp only [Bool.false_eq_true, ↓reduceIte] at htc
    rw [hnc_false _ hg3] at htc; simp only [Bool.false_eq_true, ↓reduceIte] at htc
    rw [hnc_false _ hg4] at htc; simp only [Bool.false_or] at htc
    exact ⟨_, hg4, htc⟩
  rcases htrip with h | h | h | h | h | h
  · obtain ⟨g, hg, hok⟩ := hstep p1 p2 p3 (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      h12 h13 h23 rfl rfl rfl h
    exact ⟨g, hg, Or.inl hok⟩
  · obtain ⟨g, hg, hok⟩ := hstep p1 p3 p2 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      h13 h12 h23.symm rfl rfl rfl h
    exact ⟨g, hg, Or.inr (Or.inl hok)⟩
  · obtain ⟨g, hg, hok⟩ := hstep p2 p1 p3 (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl))
      h12.symm h23 h13 rfl rfl rfl h
    exact ⟨g, hg, Or.inr (Or.inr (Or.inl hok))⟩
  · obtain ⟨g, hg, hok⟩ := hstep p2 p3 p1 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl)
      h23 h12.symm h13.symm rfl rfl rfl h
    exact ⟨g, hg, Or.inr (Or.inr (Or.inr (Or.inl hok)))⟩
  · obtain ⟨g, hg, hok⟩ := hstep p3 p1 p2 (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl))
      h13.symm h23.symm h12 rfl rfl rfl h
    exact ⟨g, hg, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hok))))⟩
  · obtain ⟨g, hg, hok⟩ := hstep p3 p2 p1 (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inl rfl)
      h23.symm h13.symm h12.symm rfl rfl rfl h
    exact ⟨g, hg, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hok))))⟩

/- ### Part 2: Elementary 2D Euclidean identities -/

open scoped Classical

private lemma dist_sq_coords (p q : ℝ²) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [PiLp.sub_apply]

private lemma norm_sq_coords (p : ℝ²) :
    ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private lemma pair_dist_mem {A : Finset ℝ²} {p q : ℝ²} (hp : p ∈ A) (hq : q ∈ A) (h : p ≠ q) :
    dist p q ∈ distanceSet A :=
  mem_image.mpr ⟨(p, q), mem_offDiag.mpr ⟨hp, hq, h⟩, rfl⟩

/-- Gram determinant identity for three points on the unit circle. -/
private lemma unit_circle_gram (u₀ u₁ u₂ : ℝ²)
    (h0 : (u₀ 0) ^ 2 + (u₀ 1) ^ 2 = 1)
    (h1 : (u₁ 0) ^ 2 + (u₁ 1) ^ 2 = 1)
    (h2 : (u₂ 0) ^ 2 + (u₂ 1) ^ 2 = 1) :
    let A := dist u₁ u₀ ^ 2
    let B := dist u₂ u₀ ^ 2
    let C := dist u₂ u₁ ^ 2
    A * B * C = 4 * A * B - (A + B - C) ^ 2 := by
  dsimp only
  rw [dist_sq_coords, dist_sq_coords, dist_sq_coords]
  set x0 := u₀ 0; set y0 := u₀ 1
  set x1 := u₁ 0; set y1 := u₁ 1
  set x2 := u₂ 0; set y2 := u₂ 1
  set a1 := x0 * x1 + y0 * y1
  set b1 := -y0 * x1 + x0 * y1
  set a2 := x0 * x2 + y0 * y2
  set b2 := -y0 * x2 + x0 * y2
  have ha1 : a1 ^ 2 + b1 ^ 2 = 1 := by linear_combination (x1 ^ 2 + y1 ^ 2) * h0 + h1
  have ha2 : a2 ^ 2 + b2 ^ 2 = 1 := by linear_combination (x2 ^ 2 + y2 ^ 2) * h0 + h2
  have hA : (x1 - x0) ^ 2 + (y1 - y0) ^ 2 = 2 - 2 * a1 := by linear_combination h0 + h1
  have hB : (x2 - x0) ^ 2 + (y2 - y0) ^ 2 = 2 - 2 * a2 := by linear_combination h0 + h2
  have hC : (x2 - x1) ^ 2 + (y2 - y1) ^ 2 = 2 - 2 * (a1 * a2 + b1 * b2) := by
    linear_combination h1 + h2 + 2 * (x1 * x2 + y1 * y2) * h0
  rw [hA, hB, hC]
  linear_combination 4 * (1 - a2 ^ 2) * ha1 + 4 * b1 ^ 2 * ha2

/-- Trilateration identities in `ℝ²` relative to `u₀, u₁, u₂` on the unit circle. -/
private lemma trilateration_identities (u₀ u₁ u₂ q₁ q₂ : ℝ²)
    (h0 : (u₀ 0) ^ 2 + (u₀ 1) ^ 2 = 1)
    (h1 : (u₁ 0) ^ 2 + (u₁ 1) ^ 2 = 1)
    (h2 : (u₂ 0) ^ 2 + (u₂ 1) ^ 2 = 1) :
    let A := dist u₁ u₀ ^ 2
    let B := dist u₂ u₀ ^ 2
    let C := dist u₂ u₁ ^ 2
    let h := A + B - C
    let D := 4 * A * B - h ^ 2
    let x1 := A + dist u₀ q₁ ^ 2 - dist u₁ q₁ ^ 2
    let y1 := B + dist u₀ q₁ ^ 2 - dist u₂ q₁ ^ 2
    let x2 := A + dist u₀ q₂ ^ 2 - dist u₁ q₂ ^ 2
    let y2 := B + dist u₀ q₂ ^ 2 - dist u₂ q₂ ^ 2
    (B * x1 ^ 2 - h * x1 * y1 + A * y1 ^ 2 = D * dist u₀ q₁ ^ 2) ∧
    (B * (x1 - A) ^ 2 - h * (x1 - A) * (y1 - B) + A * (y1 - B) ^ 2 = D * ((q₁ 0) ^ 2 + (q₁ 1) ^ 2)) ∧
    (B * (x1 - x2) ^ 2 - h * (x1 - x2) * (y1 - y2) + A * (y1 - y2) ^ 2 = D * dist q₁ q₂ ^ 2) := by
  dsimp only
  simp only [dist_sq_coords]
  refine ⟨by ring, ?_, by ring⟩
  have hx1 : ((u₁ 0 - u₀ 0) ^ 2 + (u₁ 1 - u₀ 1) ^ 2 + ((u₀ 0 - q₁ 0) ^ 2 + (u₀ 1 - q₁ 1) ^ 2) -
      ((u₁ 0 - q₁ 0) ^ 2 + (u₁ 1 - q₁ 1) ^ 2)) - ((u₁ 0 - u₀ 0) ^ 2 + (u₁ 1 - u₀ 1) ^ 2) =
      2 * ((u₁ 0 - u₀ 0) * q₁ 0 + (u₁ 1 - u₀ 1) * q₁ 1) := by
    linear_combination h0 - h1
  have hy1 : ((u₂ 0 - u₀ 0) ^ 2 + (u₂ 1 - u₀ 1) ^ 2 + ((u₀ 0 - q₁ 0) ^ 2 + (u₀ 1 - q₁ 1) ^ 2) -
      ((u₂ 0 - q₁ 0) ^ 2 + (u₂ 1 - q₁ 1) ^ 2)) - ((u₂ 0 - u₀ 0) ^ 2 + (u₂ 1 - u₀ 1) ^ 2) =
      2 * ((u₂ 0 - u₀ 0) * q₁ 0 + (u₂ 1 - u₀ 1) * q₁ 1) := by
    linear_combination h0 - h2
  rw [hx1, hy1]
  ring

/-- Two circles with distinct centres intersect in at most two points. -/
private lemma inter_two_circles_le_two (p q : ℝ²) (r d : ℝ) (hpq : p ≠ q) (W : Finset ℝ²)
    (hW : ∀ w ∈ W, dist p w = r ∧ dist q w = d) : W.card ≤ 2 := by
  by_contra hgt
  have hlt : 2 < W.card := by omega
  obtain ⟨w1, hw1, w2, hw2, w3, hw3, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
  set dx := q 0 - p 0
  set dy := q 1 - p 1
  have hd_pos : 0 < dx ^ 2 + dy ^ 2 := by
    have hne : dist p q ≠ 0 := dist_ne_zero.mpr hpq
    have hsq : 0 < dist p q ^ 2 := sq_pos_of_ne_zero hne
    rw [dist_sq_coords] at hsq
    nlinarith
  have hdot : ∀ w ∈ W, 2 * (dx * (w 0 - p 0) + dy * (w 1 - p 1)) = r ^ 2 + dx ^ 2 + dy ^ 2 - d ^ 2 := by
    intro w hw
    obtain ⟨h1, h2⟩ := hW w hw
    have h1' : (p 0 - w 0) ^ 2 + (p 1 - w 1) ^ 2 = r ^ 2 := by rw [← dist_sq_coords, h1]
    have h2' : (q 0 - w 0) ^ 2 + (q 1 - w 1) ^ 2 = d ^ 2 := by rw [← dist_sq_coords, h2]
    linear_combination h1' - h2'
  have hcross_sq : ∀ w ∈ W,
      (2 * (-dy * (w 0 - p 0) + dx * (w 1 - p 1))) ^ 2 =
      4 * (dx ^ 2 + dy ^ 2) * r ^ 2 - (r ^ 2 + dx ^ 2 + dy ^ 2 - d ^ 2) ^ 2 := by
    intro w hw
    have hd1 := hdot w hw
    have h1' : (p 0 - w 0) ^ 2 + (p 1 - w 1) ^ 2 = r ^ 2 := by rw [← dist_sq_coords, (hW w hw).1]
    linear_combination 4 * (dx ^ 2 + dy ^ 2) * h1' - (2 * (dx * (w 0 - p 0) + dy * (w 1 - p 1)) +
      (r ^ 2 + dx ^ 2 + dy ^ 2 - d ^ 2)) * hd1
  have hinj : ∀ a ∈ W, ∀ b ∈ W,
      -dy * (a 0 - p 0) + dx * (a 1 - p 1) = -dy * (b 0 - p 0) + dx * (b 1 - p 1) → a = b := by
    intro a ha b hb hcr
    have hdt : dx * (a 0 - b 0) + dy * (a 1 - b 1) = 0 := by
      have := hdot a ha; have := hdot b hb; linarith
    have hcr' : -dy * (a 0 - b 0) + dx * (a 1 - b 1) = 0 := by linarith
    have hnorm : (dx ^ 2 + dy ^ 2) * ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2) = 0 := by
      linear_combination (dx * (a 0 - b 0) + dy * (a 1 - b 1)) * hdt +
        (-dy * (a 0 - b 0) + dx * (a 1 - b 1)) * hcr'
    have hab0 : (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 = 0 :=
      (mul_eq_zero.mp hnorm).resolve_left hd_pos.ne'
    have h0 : a 0 = b 0 := by nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]
    have h1 : a 1 = b 1 := by nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]
    ext i
    fin_cases i
    · exact h0
    · exact h1
  set t1 := -dy * (w1 0 - p 0) + dx * (w1 1 - p 1)
  set t2 := -dy * (w2 0 - p 0) + dx * (w2 1 - p 1)
  set t3 := -dy * (w3 0 - p 0) + dx * (w3 1 - p 1)
  have hsq12 : t1 ^ 2 = t2 ^ 2 := by
    have := hcross_sq w1 hw1; have := hcross_sq w2 hw2; linarith
  have hsq13 : t1 ^ 2 = t3 ^ 2 := by
    have := hcross_sq w1 hw1; have := hcross_sq w3 hw3; linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq12 with h | h
  · exact h12 (hinj w1 hw1 w2 hw2 h)
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq13 with h' | h'
    · exact h13 (hinj w1 hw1 w3 hw3 h')
    · exact h23 (hinj w2 hw2 w3 hw3 (by linarith))

/-- On a circle of radius `r`, two points at distance `2r` are antipodal. -/
private lemma antipodal_of_dist_two_mul {c x y : ℝ²} {r : ℝ}
    (hx : dist c x = r) (hy : dist c y = r) (hxy : dist x y = 2 * r) :
    y = (2 : ℝ) • c - x := by
  have hx' : (c 0 - x 0) ^ 2 + (c 1 - x 1) ^ 2 = r ^ 2 := by rw [← dist_sq_coords, hx]
  have hy' : (c 0 - y 0) ^ 2 + (c 1 - y 1) ^ 2 = r ^ 2 := by rw [← dist_sq_coords, hy]
  have hxy' : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = 4 * r ^ 2 := by
    rw [← dist_sq_coords, hxy]; ring
  have hsum : (x 0 + y 0 - 2 * c 0) ^ 2 + (x 1 + y 1 - 2 * c 1) ^ 2 = 0 := by
    linear_combination 2 * hx' + 2 * hy' - hxy'
  have h0 : x 0 + y 0 - 2 * c 0 = 0 := by
    nlinarith [sq_nonneg (x 0 + y 0 - 2 * c 0), sq_nonneg (x 1 + y 1 - 2 * c 1)]
  have h1 : x 1 + y 1 - 2 * c 1 = 0 := by
    nlinarith [sq_nonneg (x 0 + y 0 - 2 * c 0), sq_nonneg (x 1 + y 1 - 2 * c 1)]
  ext i
  fin_cases i
  · change y 0 = ((2 : ℝ) • c - x) 0
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; linarith
  · change y 1 = ((2 : ℝ) • c - x) 1
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; linarith

/-- Given a center `c ∈ B` with all 6 other points on `C(c, r)` and palette `{r^2, 3r^2, 4r^2}`,
deduce `distinctDistances B = 3` and `∑ x ∈ B.erase c, (x - c) = 0`. -/
private lemma wheel_of_center_and_palette {B : Finset ℝ²} (hB : B.card = 7)
    {c : ℝ²} {r : ℝ} (hc : c ∈ B) (hr : 0 < r)
    (hRad : ∀ x ∈ B.erase c, dist c x = r)
    (hPal : ∀ d ∈ distanceSet B, d ^ 2 = r ^ 2 ∨ d ^ 2 = 3 * r ^ 2 ∨ d ^ 2 = 4 * r ^ 2) :
    distinctDistances B = 3 ∧ (∑ x ∈ B.erase c, (x - c)) = 0 := by
  let W := B.erase c
  have hW : W.card = 6 := by rw [card_erase_of_mem hc, hB]
  let S : Finset ℝ := {r, Real.sqrt 3 * r, 2 * r}
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h12 : r ≠ Real.sqrt 3 * r := by
    intro h; have hsq := congrArg (· ^ 2) h
    rw [mul_pow, hsqrt3_sq] at hsq; nlinarith
  have h13 : r ≠ 2 * r := by linarith
  have h23 : Real.sqrt 3 * r ≠ 2 * r := by
    intro h; have hsq := congrArg (· ^ 2) h
    rw [mul_pow, hsqrt3_sq] at hsq; nlinarith
  have hScard : S.card = 3 := by simp [S, h12, h13, h23]
  have hDist_sub : distanceSet B ⊆ S := by
    intro d hd
    have hd_nn : 0 ≤ d := by
      obtain ⟨⟨u, v⟩, _, rfl⟩ := mem_image.mp hd; exact dist_nonneg
    rcases hPal d hd with h | h | h
    · have : d = r := by nlinarith
      simp [S, this]
    · have : d = Real.sqrt 3 * r := by
        have hsq : d ^ 2 = (Real.sqrt 3 * r) ^ 2 := by rw [mul_pow, hsqrt3_sq]; exact h
        nlinarith [mul_pos hsqrt3_pos hr]
      simp [S, this]
    · have : d = 2 * r := by nlinarith
      simp [S, this]
  have h_antipode_and_sat : ∀ x ∈ W,
      (2 : ℝ) • c - x ∈ W ∧
      ((W.erase x).filter (fun y => dist x y = r)).card = 2 ∧
      ((W.erase x).filter (fun y => dist x y = Real.sqrt 3 * r)).card = 2 ∧
      ((W.erase x).filter (fun y => dist x y = 2 * r)).card = 1 := by
    intro x hx
    have hxc : x ≠ c := (mem_erase.mp hx).1
    let W' := W.erase x
    have hW' : W'.card = 5 := by rw [card_erase_of_mem hx, hW]
    have hmaps : ∀ y ∈ W', dist x y ∈ S := by
      intro y hy
      exact hDist_sub (pair_dist_mem (erase_subset _ _ hx) (erase_subset _ _ (erase_subset _ _ hy))
        (mem_erase.mp hy).1.symm)
    have hf1 : (W'.filter (fun y => dist x y = r)).card ≤ 2 :=
      inter_two_circles_le_two c x r r hxc.symm _ fun y hy =>
        ⟨hRad y (erase_subset _ _ (mem_filter.mp hy).1), (mem_filter.mp hy).2⟩
    have hf2 : (W'.filter (fun y => dist x y = Real.sqrt 3 * r)).card ≤ 2 :=
      inter_two_circles_le_two c x r (Real.sqrt 3 * r) hxc.symm _ fun y hy =>
        ⟨hRad y (erase_subset _ _ (mem_filter.mp hy).1), (mem_filter.mp hy).2⟩
    have hf3_sub : W'.filter (fun y => dist x y = 2 * r) ⊆ {(2 : ℝ) • c - x} := by
      intro y hy
      rw [mem_singleton]
      exact antipodal_of_dist_two_mul (hRad x hx) (hRad y (erase_subset _ _ (mem_filter.mp hy).1))
        (mem_filter.mp hy).2
    have hf3 : (W'.filter (fun y => dist x y = 2 * r)).card ≤ 1 :=
      (card_le_card hf3_sub).trans (by simp)
    have hsum : (W'.filter (fun y => dist x y = r)).card +
        (W'.filter (fun y => dist x y = Real.sqrt 3 * r)).card +
        (W'.filter (fun y => dist x y = 2 * r)).card = 5 := by
      have hfib := card_eq_sum_card_fiberwise hmaps
      rw [hW'] at hfib
      dsimp only [S] at hfib
      rw [sum_insert (by simp [h12, h13]), sum_insert (by simp [h23]), sum_singleton] at hfib
      omega
    have he1 : (W'.filter (fun y => dist x y = r)).card = 2 := by omega
    have he2 : (W'.filter (fun y => dist x y = Real.sqrt 3 * r)).card = 2 := by omega
    have he3 : (W'.filter (fun y => dist x y = 2 * r)).card = 1 := by omega
    have hne3 : (W'.filter (fun y => dist x y = 2 * r)).Nonempty := card_pos.mp (by omega)
    obtain ⟨y, hy⟩ := hne3
    have hy_eq : y = (2 : ℝ) • c - x := mem_singleton.mp (hf3_sub hy)
    have hyW : (2 : ℝ) • c - x ∈ W := hy_eq ▸ erase_subset _ _ (mem_filter.mp hy).1
    exact ⟨hyW, he1, he2, he3⟩
  have hDD : distinctDistances B = 3 := by
    change (distanceSet B).card = 3
    obtain ⟨x, hx⟩ : W.Nonempty := card_pos.mp (by omega)
    obtain ⟨_, he1, he2, he3⟩ := h_antipode_and_sat x hx
    have hS_sub : S ⊆ distanceSet B := by
      intro d hd
      simp only [S, mem_insert, mem_singleton] at hd
      rcases hd with h | h | h
      · rw [h]
        obtain ⟨y, hy⟩ := card_pos.mp (show 0 < ((W.erase x).filter (fun y => dist x y = r)).card by rw [he1]; omega)
        rw [← (mem_filter.mp hy).2]
        exact pair_dist_mem (erase_subset _ _ hx) (erase_subset _ _ (erase_subset _ _ (mem_filter.mp hy).1))
          (mem_erase.mp (mem_filter.mp hy).1).1.symm
      · rw [h]
        obtain ⟨y, hy⟩ := card_pos.mp (show 0 < ((W.erase x).filter (fun y => dist x y = Real.sqrt 3 * r)).card by rw [he2]; omega)
        rw [← (mem_filter.mp hy).2]
        exact pair_dist_mem (erase_subset _ _ hx) (erase_subset _ _ (erase_subset _ _ (mem_filter.mp hy).1))
          (mem_erase.mp (mem_filter.mp hy).1).1.symm
      · rw [h]
        obtain ⟨y, hy⟩ := card_pos.mp (show 0 < ((W.erase x).filter (fun y => dist x y = 2 * r)).card by rw [he3]; omega)
        rw [← (mem_filter.mp hy).2]
        exact pair_dist_mem (erase_subset _ _ hx) (erase_subset _ _ (erase_subset _ _ (mem_filter.mp hy).1))
          (mem_erase.mp (mem_filter.mp hy).1).1.symm
    have hEq : distanceSet B = S := Subset.antisymm hDist_sub hS_sub
    rw [hEq, hScard]
  have hBal : ∑ x ∈ W, (x - c) = 0 := by
    have hbij : ∑ x ∈ W, (x - c) = ∑ x ∈ W, (((2 : ℝ) • c - x) - c) := by
      refine Finset.sum_bij (fun x _ => (2 : ℝ) • c - x) ?_ ?_ ?_ ?_
      · intro x hx; exact (h_antipode_and_sat x hx).1
      · intro a _ b _ hab
        have : a = (2 : ℝ) • c - ((2 : ℝ) • c - a) := by abel
        rw [this, hab]; abel
      · intro y hy
        refine ⟨(2 : ℝ) • c - y, (h_antipode_and_sat y hy).1, ?_⟩
        abel
      · intro x _; abel
    have hneg : ∑ x ∈ W, (((2 : ℝ) • c - x) - c) = -(∑ x ∈ W, (x - c)) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun x _ => ?_
      ext i
      simp only [PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hneg] at hbij
    ext i
    have hi := congrArg (fun v : ℝ² => v i) hbij
    simp only [PiLp.neg_apply, PiLp.zero_apply] at hi ⊢
    linarith
  exact ⟨hDD, hBal⟩

/- ### Part 3: Branch 1 (some vertex has at least 3 neighbors at the same distance) -/

private lemma pEval_evalQ {s : ℝ} (hs : s ^ 2 = 3) (t : ℝ) (A B h x y : Poly3) :
    pEval s t (evalQ A B h x y) =
    pEval s t B * pEval s t x ^ 2 - pEval s t h * pEval s t x * pEval s t y +
    pEval s t A * pEval s t y ^ 2 := by
  simp only [evalQ, pEval_add, pEval_sub, pEval_mul hs]
  ring

set_option maxHeartbeats 800000 in
/-- Bridge from geometric normalized points `(u₀, u₁, u₂, q₁, q₂, q₃)` to `checkSeed_sound`. -/
private lemma run_seed_geom
    (u₀ u₁ u₂ q₁ q₂ q₃ : ℝ²)
    (hu0 : (u₀ 0) ^ 2 + (u₀ 1) ^ 2 = 1)
    (hu1 : (u₁ 0) ^ 2 + (u₁ 1) ^ 2 = 1)
    (hu2 : (u₂ 0) ^ 2 + (u₂ 1) ^ 2 = 1)
    (hu01 : u₀ ≠ u₁) (hu02 : u₀ ≠ u₂) (hu12 : u₁ ≠ u₂)
    (hq12 : q₁ ≠ q₂) (hq13 : q₁ ≠ q₃) (hq23 : q₂ ≠ q₃)
    (d0 d1 d2 : ℝ) (hd0 : 0 < d0) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hd01 : d0 ≠ d1) (hd02 : d0 ≠ d2) (hd12 : d1 ≠ d2)
    (iA iB iC : Fin 3)
    (hA : dist u₁ u₀ ^ 2 = pick3 d0 d1 d2 iA)
    (hB : dist u₂ u₀ ^ 2 = pick3 d0 d1 d2 iB)
    (hC : dist u₂ u₁ ^ 2 = pick3 d0 d1 d2 iC)
    (w1 w2 w3 : Fin 3 × Fin 3 × Fin 3 × Fin 3)
    (hw1 : (q₁ 0) ^ 2 + (q₁ 1) ^ 2 = pick3 d0 d1 d2 w1.1 ∧
           dist u₀ q₁ ^ 2 = pick3 d0 d1 d2 w1.2.1 ∧
           dist u₁ q₁ ^ 2 = pick3 d0 d1 d2 w1.2.2.1 ∧
           dist u₂ q₁ ^ 2 = pick3 d0 d1 d2 w1.2.2.2)
    (hw2 : (q₂ 0) ^ 2 + (q₂ 1) ^ 2 = pick3 d0 d1 d2 w2.1 ∧
           dist u₀ q₂ ^ 2 = pick3 d0 d1 d2 w2.2.1 ∧
           dist u₁ q₂ ^ 2 = pick3 d0 d1 d2 w2.2.2.1 ∧
           dist u₂ q₂ ^ 2 = pick3 d0 d1 d2 w2.2.2.2)
    (hw3 : (q₃ 0) ^ 2 + (q₃ 1) ^ 2 = pick3 d0 d1 d2 w3.1 ∧
           dist u₀ q₃ ^ 2 = pick3 d0 d1 d2 w3.2.1 ∧
           dist u₁ q₃ ^ 2 = pick3 d0 d1 d2 w3.2.2.1 ∧
           dist u₂ q₃ ^ 2 = pick3 d0 d1 d2 w3.2.2.2)
    (hp12 : dist q₁ q₂ ^ 2 = d0 ∨ dist q₁ q₂ ^ 2 = d1 ∨ dist q₁ q₂ ^ 2 = d2)
    (hp13 : dist q₁ q₃ ^ 2 = d0 ∨ dist q₁ q₃ ^ 2 = d1 ∨ dist q₁ q₃ ^ 2 = d2)
    (hp23 : dist q₂ q₃ ^ 2 = d0 ∨ dist q₂ q₃ ^ 2 = d1 ∨ dist q₂ q₃ ^ 2 = d2)
    (P0 P1 P2 : Poly3) (ok : (Fin 3 × Fin 3 × Fin 3 × Fin 3) → (Fin 3 × Fin 3 × Fin 3 × Fin 3) →
      (Fin 3 × Fin 3 × Fin 3 × Fin 3) → Poly3 → Bool)
    (hcheck : checkSeed P0 P1 P2 iA iB iC ok = true)
    (s t lam : ℝ) (hs : s ^ 2 = 3) (hlam : 0 < lam)
    (hP0 : pEval s t P0 = lam * d0) (hP1 : pEval s t P1 = lam * d1) (hP2 : pEval s t P2 = lam * d2) :
    ∃ g : Poly3, pEval s t g = 0 ∧
      (ok w1 w2 w3 g = true ∨ ok w1 w3 w2 g = true ∨ ok w2 w1 w3 g = true ∨
       ok w2 w3 w1 g = true ∨ ok w3 w1 w2 g = true ∨ ok w3 w2 w1 g = true) := by
  have hAr : 0 < dist u₁ u₀ ^ 2 := sq_pos_of_ne_zero (dist_ne_zero.mpr hu01.symm)
  have hBr : 0 < dist u₂ u₀ ^ 2 := sq_pos_of_ne_zero (dist_ne_zero.mpr hu02.symm)
  have hCr : 0 < dist u₂ u₁ ^ 2 := sq_pos_of_ne_zero (dist_ne_zero.mpr hu12.symm)
  have hD_pos : 0 < 4 * dist u₁ u₀ ^ 2 * dist u₂ u₀ ^ 2 -
      (dist u₁ u₀ ^ 2 + dist u₂ u₀ ^ 2 - dist u₂ u₁ ^ 2) ^ 2 := by
    rw [← unit_circle_gram u₀ u₁ u₂ hu0 hu1 hu2]
    exact mul_pos (mul_pos hAr hBr) hCr
  have hpick : ∀ i : Fin 3, pEval s t (pick3 P0 P1 P2 i) = lam * pick3 d0 d1 d2 i := by
    intro i; fin_cases i <;> simp [pick3, hP0, hP1, hP2]
  have hA' : pEval s t (pick3 P0 P1 P2 iA) = lam * dist u₁ u₀ ^ 2 := by rw [hpick, hA]
  have hB' : pEval s t (pick3 P0 P1 P2 iB) = lam * dist u₂ u₀ ^ 2 := by rw [hpick, hB]
  have hC' : pEval s t (pick3 P0 P1 P2 iC) = lam * dist u₂ u₁ ^ 2 := by rw [hpick, hC]
  have h_eval : pEval s t (pSub (pAdd (pick3 P0 P1 P2 iA) (pick3 P0 P1 P2 iB)) (pick3 P0 P1 P2 iC)) =
      lam * (dist u₁ u₀ ^ 2 + dist u₂ u₀ ^ 2 - dist u₂ u₁ ^ 2) := by
    rw [pEval_sub, pEval_add, hA', hB', hC']; ring
  have hD_eval : pEval s t (pSub (pMul [Q3.ofInt 4] (pMul (pick3 P0 P1 P2 iA) (pick3 P0 P1 P2 iB)))
      (pMul (pSub (pAdd (pick3 P0 P1 P2 iA) (pick3 P0 P1 P2 iB)) (pick3 P0 P1 P2 iC))
            (pSub (pAdd (pick3 P0 P1 P2 iA) (pick3 P0 P1 P2 iB)) (pick3 P0 P1 P2 iC)))) =
      lam ^ 2 * (4 * dist u₁ u₀ ^ 2 * dist u₂ u₀ ^ 2 -
        (dist u₁ u₀ ^ 2 + dist u₂ u₀ ^ 2 - dist u₂ u₁ ^ 2) ^ 2) := by
    rw [pEval_sub, pEval_mul hs, pEval_mul hs, pEval_mul hs, h_eval, hA', hB']
    simp only [pEval, Q3.toReal_ofInt, mul_zero, add_zero, Int.cast_ofNat]
    ring
  have hbad : pEval s t (
      let A := pick3 P0 P1 P2 iA
      let B := pick3 P0 P1 P2 iB
      let C := pick3 P0 P1 P2 iC
      let h := pSub (pAdd A B) C
      let D := pSub (pMul [Q3.ofInt 4] (pMul A B)) (pMul h h)
      pMul D (pMul P0 (pMul P1 (pMul P2
        (pMul (pSub P0 P1) (pMul (pSub P0 P2) (pSub P1 P2))))))) ≠ 0 := by
    dsimp only
    simp only [pEval_mul hs, pEval_sub, hD_eval, hP0, hP1, hP2]
    have hlam0 : lam ≠ 0 := hlam.ne'
    have hD0 : lam ^ 2 * (4 * dist u₁ u₀ ^ 2 * dist u₂ u₀ ^ 2 -
        (dist u₁ u₀ ^ 2 + dist u₂ u₀ ^ 2 - dist u₂ u₁ ^ 2) ^ 2) ≠ 0 :=
      (mul_pos (sq_pos_of_pos hlam) hD_pos).ne'
    exact mul_ne_zero hD0 (mul_ne_zero (mul_ne_zero hlam0 hd0.ne')
      (mul_ne_zero (mul_ne_zero hlam0 hd1.ne') (mul_ne_zero (mul_ne_zero hlam0 hd2.ne')
        (mul_ne_zero (sub_ne_zero.mpr (fun h => hd01 (mul_left_cancel₀ hlam0 h)))
          (mul_ne_zero (sub_ne_zero.mpr (fun h => hd02 (mul_left_cancel₀ hlam0 h)))
            (sub_ne_zero.mpr (fun h => hd12 (mul_left_cancel₀ hlam0 h))))))))
  have hword_ne : ∀ (qa qb : ℝ²) (wa wb : Fin 3 × Fin 3 × Fin 3 × Fin 3), qa ≠ qb →
      (dist u₀ qa ^ 2 = pick3 d0 d1 d2 wa.2.1 ∧ dist u₁ qa ^ 2 = pick3 d0 d1 d2 wa.2.2.1 ∧
       dist u₂ qa ^ 2 = pick3 d0 d1 d2 wa.2.2.2) →
      (dist u₀ qb ^ 2 = pick3 d0 d1 d2 wb.2.1 ∧ dist u₁ qb ^ 2 = pick3 d0 d1 d2 wb.2.2.1 ∧
       dist u₂ qb ^ 2 = pick3 d0 d1 d2 wb.2.2.2) → wa ≠ wb := by
    intro qa qb wa wb hne ha hb heq
    subst heq
    have htri := (trilateration_identities u₀ u₁ u₂ qa qb hu0 hu1 hu2).2.2
    rw [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2] at htri
    have hzero : (4 * dist u₁ u₀ ^ 2 * dist u₂ u₀ ^ 2 -
        (dist u₁ u₀ ^ 2 + dist u₂ u₀ ^ 2 - dist u₂ u₁ ^ 2) ^ 2) * dist qa qb ^ 2 = 0 := by
      linarith
    have hdist0 : dist qa qb ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left hD_pos.ne'
    exact hne (dist_eq_zero.mp (sq_eq_zero_iff.mp hdist0))
  have h12 : w1 ≠ w2 := hword_ne q₁ q₂ w1 w2 hq12 ⟨hw1.2.1, hw1.2.2.1, hw1.2.2.2⟩ ⟨hw2.2.1, hw2.2.2.1, hw2.2.2.2⟩
  have h13 : w1 ≠ w3 := hword_ne q₁ q₃ w1 w3 hq13 ⟨hw1.2.1, hw1.2.2.1, hw1.2.2.2⟩ ⟨hw3.2.1, hw3.2.2.1, hw3.2.2.2⟩
  have h23 : w2 ≠ w3 := hword_ne q₂ q₃ w2 w3 hq23 ⟨hw2.2.1, hw2.2.2.1, hw2.2.2.2⟩ ⟨hw3.2.1, hw3.2.2.1, hw3.2.2.2⟩
  have hword_one : ∀ (q : ℝ²) (w : Fin 3 × Fin 3 × Fin 3 × Fin 3),
      ((q 0) ^ 2 + (q 1) ^ 2 = pick3 d0 d1 d2 w.1 ∧
       dist u₀ q ^ 2 = pick3 d0 d1 d2 w.2.1 ∧
       dist u₁ q ^ 2 = pick3 d0 d1 d2 w.2.2.1 ∧
       dist u₂ q ^ 2 = pick3 d0 d1 d2 w.2.2.2) →
      let A := pick3 P0 P1 P2 iA
      let B := pick3 P0 P1 P2 iB
      let C := pick3 P0 P1 P2 iC
      let h := pSub (pAdd A B) C
      let D := pSub (pMul [Q3.ofInt 4] (pMul A B)) (pMul h h)
      let o := pick3 P0 P1 P2 w.1
      let u := pick3 P0 P1 P2 w.2.1
      let x := wordX P0 P1 P2 iA w
      let y := wordY P0 P1 P2 iB w
      pEval s t (pSub (evalQ A B h x y) (pMul D u)) = 0 ∧
      pEval s t (pSub (evalQ A B h (pSub x A) (pSub y B)) (pMul D o)) = 0 := by
    intro q w hqw
    dsimp only [wordX, wordY]
    obtain ⟨ht1, ht2, _⟩ := trilateration_identities u₀ u₁ u₂ q q hu0 hu1 hu2
    constructor
    · simp only [pEval_sub, pEval_evalQ hs, pEval_mul hs, pEval_add, hA', hB', h_eval, hD_eval,
        hpick, ← hqw.2.1, ← hqw.2.2.1, ← hqw.2.2.2]
      linear_combination lam ^ 3 * ht1
    · simp only [pEval_sub, pEval_evalQ hs, pEval_mul hs, pEval_add, hA', hB', h_eval, hD_eval,
        hpick, ← hqw.1, ← hqw.2.1, ← hqw.2.2.1, ← hqw.2.2.2]
      linear_combination lam ^ 3 * ht2
  have hpair_one : ∀ (qa qb : ℝ²) (wa wb : Fin 3 × Fin 3 × Fin 3 × Fin 3),
      (dist u₀ qa ^ 2 = pick3 d0 d1 d2 wa.2.1 ∧ dist u₁ qa ^ 2 = pick3 d0 d1 d2 wa.2.2.1 ∧
       dist u₂ qa ^ 2 = pick3 d0 d1 d2 wa.2.2.2) →
      (dist u₀ qb ^ 2 = pick3 d0 d1 d2 wb.2.1 ∧ dist u₁ qb ^ 2 = pick3 d0 d1 d2 wb.2.2.1 ∧
       dist u₂ qb ^ 2 = pick3 d0 d1 d2 wb.2.2.2) →
      (dist qa qb ^ 2 = d0 ∨ dist qa qb ^ 2 = d1 ∨ dist qa qb ^ 2 = d2) →
      let A := pick3 P0 P1 P2 iA
      let B := pick3 P0 P1 P2 iB
      let C := pick3 P0 P1 P2 iC
      let h := pSub (pAdd A B) C
      let D := pSub (pMul [Q3.ofInt 4] (pMul A B)) (pMul h h)
      pEval s t (pairPoly P0 P1 P2 A B h D
        (wordX P0 P1 P2 iA wa) (wordY P0 P1 P2 iB wa)
        (wordX P0 P1 P2 iA wb) (wordY P0 P1 P2 iB wb)) = 0 := by
    intro qa qb wa wb ha hb hdist
    dsimp only [pairPoly, wordX, wordY]
    have ht3 := (trilateration_identities u₀ u₁ u₂ qa qb hu0 hu1 hu2).2.2
    have hs_eq : pEval s t (evalQ (pick3 P0 P1 P2 iA) (pick3 P0 P1 P2 iB)
        (pSub (pAdd (pick3 P0 P1 P2 iA) (pick3 P0 P1 P2 iB)) (pick3 P0 P1 P2 iC))
        (pSub (pSub (pAdd (pick3 P0 P1 P2 iA) (pick3 P0 P1 P2 wa.2.1)) (pick3 P0 P1 P2 wa.2.2.1))
              (pSub (pAdd (pick3 P0 P1 P2 iA) (pick3 P0 P1 P2 wb.2.1)) (pick3 P0 P1 P2 wb.2.2.1)))
        (pSub (pSub (pAdd (pick3 P0 P1 P2 iB) (pick3 P0 P1 P2 wa.2.1)) (pick3 P0 P1 P2 wa.2.2.2))
              (pSub (pAdd (pick3 P0 P1 P2 iB) (pick3 P0 P1 P2 wb.2.1)) (pick3 P0 P1 P2 wb.2.2.2)))) =
        lam ^ 3 * ((4 * dist u₁ u₀ ^ 2 * dist u₂ u₀ ^ 2 -
          (dist u₁ u₀ ^ 2 + dist u₂ u₀ ^ 2 - dist u₂ u₁ ^ 2) ^ 2) * dist qa qb ^ 2) := by
      simp only [pEval_evalQ hs, pEval_sub, pEval_add, hA', hB', h_eval, hpick,
        ← ha.1, ← ha.2.1, ← ha.2.2, ← hb.1, ← hb.2.1, ← hb.2.2]
      linear_combination lam ^ 3 * ht3
    simp only [pEval_mul hs, pEval_sub, hs_eq, hD_eval, hP0, hP1, hP2]
    rcases hdist with h | h | h <;> rw [h] <;> ring
  apply checkSeed_sound P0 P1 P2 iA iB iC ok hcheck hs hbad w1 w2 w3 h12 h13 h23
  · intro w hw
    rcases hw with h | h | h
    · rw [h]; exact hword_one q₁ w1 hw1
    · rw [h]; exact hword_one q₂ w2 hw2
    · rw [h]; exact hword_one q₃ w3 hw3
  · intro wa wb hwa hwb hne
    rcases hwa with ha | ha | ha <;> rcases hwb with hb | hb | hb
    · exact absurd (ha.trans hb.symm) hne
    · rw [ha, hb]; exact hpair_one q₁ q₂ w1 w2 ⟨hw1.2.1, hw1.2.2.1, hw1.2.2.2⟩ ⟨hw2.2.1, hw2.2.2.1, hw2.2.2.2⟩ hp12
    · rw [ha, hb]; exact hpair_one q₁ q₃ w1 w3 ⟨hw1.2.1, hw1.2.2.1, hw1.2.2.2⟩ ⟨hw3.2.1, hw3.2.2.1, hw3.2.2.2⟩ hp13
    · rw [ha, hb]; exact hpair_one q₂ q₁ w2 w1 ⟨hw2.2.1, hw2.2.2.1, hw2.2.2.2⟩ ⟨hw1.2.1, hw1.2.2.1, hw1.2.2.2⟩
        (by rw [dist_comm]; exact hp12)
    · exact absurd (ha.trans hb.symm) hne
    · rw [ha, hb]; exact hpair_one q₂ q₃ w2 w3 ⟨hw2.2.1, hw2.2.2.1, hw2.2.2.2⟩ ⟨hw3.2.1, hw3.2.2.1, hw3.2.2.2⟩ hp23
    · rw [ha, hb]; exact hpair_one q₃ q₁ w3 w1 ⟨hw3.2.1, hw3.2.2.1, hw3.2.2.2⟩ ⟨hw1.2.1, hw1.2.2.1, hw1.2.2.2⟩
        (by rw [dist_comm]; exact hp13)
    · rw [ha, hb]; exact hpair_one q₃ q₂ w3 w2 ⟨hw3.2.1, hw3.2.2.1, hw3.2.2.2⟩ ⟨hw2.2.1, hw2.2.2.1, hw2.2.2.2⟩
        (by rw [dist_comm]; exact hp23)
    · exact absurd (ha.trans hb.symm) hne

/-- Pad a subset of `(0, ∞)` of size ≤ 3 containing `1` to three distinct positive reals `(1, a, b)`. -/
private lemma pad_palette {S : Finset ℝ} (hS : S.card ≤ 3) (h1 : (1 : ℝ) ∈ S)
    (hpos : ∀ x ∈ S, 0 < x) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ (1 : ℝ) ≠ a ∧ (1 : ℝ) ≠ b ∧ a ≠ b ∧
      ∀ x ∈ S, x = 1 ∨ x = a ∨ x = b := by
  let S' := S.erase 1
  have hS' : S'.card ≤ 2 := by rw [card_erase_of_mem h1]; omega
  rcases Nat.lt_or_eq_of_le hS' with hlt | heq2
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h0 | h1'
    · have hemp : S' = ∅ := card_eq_zero.mp (by omega)
      refine ⟨2, 3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exfalso
        have : x ∈ S' := mem_erase.mpr ⟨hx1, hx⟩
        rw [hemp] at this; exact notMem_empty x this
    · obtain ⟨a, ha⟩ := card_eq_one.mp h1'
      have haS : a ∈ S := erase_subset _ _ (ha ▸ mem_singleton_self a)
      have ha_ne1 : a ≠ 1 := (mem_erase.mp (ha ▸ mem_singleton_self a)).1
      refine ⟨a, a + 2, hpos a haS, by linarith [hpos a haS], ha_ne1.symm,
        by linarith [hpos a haS], by linarith, ?_⟩
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · have hx' : x ∈ S' := mem_erase.mpr ⟨hx1, hx⟩
        rw [ha, mem_singleton] at hx'
        exact Or.inr (Or.inl hx')
  · obtain ⟨a, b, hab, hS'eq⟩ := card_eq_two.mp heq2
    have haS : a ∈ S := erase_subset _ _ (hS'eq ▸ mem_insert_self a {b})
    have hbS : b ∈ S := erase_subset _ _ (hS'eq ▸ mem_insert_of_mem (mem_singleton_self b))
    have ha1 : a ≠ 1 := (mem_erase.mp (hS'eq ▸ mem_insert_self a {b})).1
    have hb1 : b ≠ 1 := (mem_erase.mp (hS'eq ▸ mem_insert_of_mem (mem_singleton_self b))).1
    refine ⟨a, b, hpos a haS, hpos b hbS, ha1.symm, hb1.symm, hab, ?_⟩
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · have hx' : x ∈ S' := mem_erase.mpr ⟨hx1, hx⟩
      rw [hS'eq, mem_insert, mem_singleton] at hx'
      exact Or.inr hx'

private lemma three_of_three {α : Type*} {u₀ u₁ u₂ v₀ v₁ v₂ v : α}
    (hv01 : v₀ ≠ v₁) (hv02 : v₀ ≠ v₂) (hv12 : v₁ ≠ v₂)
    (h0 : v₀ = u₀ ∨ v₀ = u₁ ∨ v₀ = u₂)
    (h1 : v₁ = u₀ ∨ v₁ = u₁ ∨ v₁ = u₂)
    (h2 : v₂ = u₀ ∨ v₂ = u₁ ∨ v₂ = u₂)
    (hv : v = u₀ ∨ v = u₁ ∨ v = u₂) (hne : v ≠ v₀) : v = v₁ ∨ v = v₂ := by
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl <;>
    first | exact absurd rfl hv01 | exact absurd rfl hv02 | exact absurd rfl hv12 |
      (rcases hv with rfl | rfl | rfl <;> tauto)

set_option maxHeartbeats 800000 in
private lemma canonical_six_cases_core
    (u₀ u₁ u₂ q₁ q₂ q₃ : ℝ²) (hq12 : q₁ ≠ q₂) (hq13 : q₁ ≠ q₃) (hq23 : q₂ ≠ q₃)
    (a b : ℝ) (v₀ v₁ v₂ : ℝ²) (a' b' : ℝ)
    (hv0 : (v₀ 0) ^ 2 + (v₀ 1) ^ 2 = 1) (hv1 : (v₁ 0) ^ 2 + (v₁ 1) ^ 2 = 1) (hv2 : (v₂ 0) ^ 2 + (v₂ 1) ^ 2 = 1)
    (hv01 : v₀ ≠ v₁) (hv02 : v₀ ≠ v₂) (hv12 : v₁ ≠ v₂)
    (ha' : 0 < a') (hb' : 0 < b') (h1a' : (1 : ℝ) ≠ a') (h1b' : (1 : ℝ) ≠ b') (hab' : a' ≠ b')
    (hswap : (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a))
    (hv0m : v₀ = u₀ ∨ v₀ = u₁ ∨ v₀ = u₂)
    (hv1m : v₁ = u₀ ∨ v₁ = u₁ ∨ v₁ = u₂)
    (hv2m : v₂ = u₀ ∨ v₂ = u₁ ∨ v₂ = u₂)
    (hqm' : ∀ q, q = q₁ ∨ q = q₂ ∨ q = q₃ →
      ((q 0) ^ 2 + (q 1) ^ 2 = 1 ∨ (q 0) ^ 2 + (q 1) ^ 2 = a' ∨ (q 0) ^ 2 + (q 1) ^ 2 = b') ∧
      (dist v₀ q ^ 2 = 1 ∨ dist v₀ q ^ 2 = a' ∨ dist v₀ q ^ 2 = b') ∧
      (dist v₁ q ^ 2 = 1 ∨ dist v₁ q ^ 2 = a' ∨ dist v₁ q ^ 2 = b') ∧
      (dist v₂ q ^ 2 = 1 ∨ dist v₂ q ^ 2 = a' ∨ dist v₂ q ^ 2 = b'))
    (hp12' : dist q₁ q₂ ^ 2 = 1 ∨ dist q₁ q₂ ^ 2 = a' ∨ dist q₁ q₂ ^ 2 = b')
    (hp13' : dist q₁ q₃ ^ 2 = 1 ∨ dist q₁ q₃ ^ 2 = a' ∨ dist q₁ q₃ ^ 2 = b')
    (hp23' : dist q₂ q₃ ^ 2 = 1 ∨ dist q₂ q₃ ^ 2 = a' ∨ dist q₂ q₃ ^ 2 = b')
    (iA iB iC : Fin 3)
    (hAv : dist v₁ v₀ ^ 2 = pick3 1 a' b' iA)
    (hBv : dist v₂ v₀ ^ 2 = pick3 1 a' b' iB)
    (hCv : dist v₂ v₁ ^ 2 = pick3 1 a' b' iC)
    (hpat : (iA = 0 ∧ iB = 0 ∧ iC = 0) ∨ (iA = 0 ∧ iB = 0 ∧ iC = 1) ∨
      (iA = 1 ∧ iB = 1 ∧ iC = 1) ∨ (iA = 1 ∧ iB = 1 ∧ iC = 2) ∨
      (iA = 0 ∧ iB = 1 ∧ iC = 1) ∨ (iA = 0 ∧ iB = 1 ∧ iC = 2)) :
    ((a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3)) ∧
    (((q₁ 0) ^ 2 + (q₁ 1) ^ 2 = 1 ∧ (q₂ 0) ^ 2 + (q₂ 1) ^ 2 = 1 ∧ (q₃ 0) ^ 2 + (q₃ 1) ^ 2 = 1) ∨
     (∃ u, (u = u₀ ∨ u = u₁ ∨ u = u₂) ∧
       (∀ v, (v = u₀ ∨ v = u₁ ∨ v = u₂) → v ≠ u → dist u v ^ 2 = 1) ∧
       dist u q₁ ^ 2 = 1 ∧ dist u q₂ ^ 2 = 1 ∧ dist u q₃ ^ 2 = 1)) := by
  have htoIdx' : ∀ x : ℝ, x = 1 ∨ x = a' ∨ x = b' → ∃ i : Fin 3, x = pick3 1 a' b' i := by
    intro x hx; rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have mkW : ∀ q, q = q₁ ∨ q = q₂ ∨ q = q₃ → ∃ w : Fin 3 × Fin 3 × Fin 3 × Fin 3,
      (q 0) ^ 2 + (q 1) ^ 2 = pick3 1 a' b' w.1 ∧
      dist v₀ q ^ 2 = pick3 1 a' b' w.2.1 ∧
      dist v₁ q ^ 2 = pick3 1 a' b' w.2.2.1 ∧
      dist v₂ q ^ 2 = pick3 1 a' b' w.2.2.2 := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hqm' q hq
    obtain ⟨i1, hi1⟩ := htoIdx' _ h1
    obtain ⟨i2, hi2⟩ := htoIdx' _ h2
    obtain ⟨i3, hi3⟩ := htoIdx' _ h3
    obtain ⟨i4, hi4⟩ := htoIdx' _ h4
    exact ⟨(i1, i2, i3, i4), hi1, hi2, hi3, hi4⟩
  obtain ⟨w1, hw1⟩ := mkW q₁ (Or.inl rfl)
  obtain ⟨w2, hw2⟩ := mkW q₂ (Or.inr (Or.inl rfl))
  obtain ⟨w3, hw3⟩ := mkW q₃ (Or.inr (Or.inr rfl))
  have hgram := unit_circle_gram v₀ v₁ v₂ hv0 hv1 hv2
  dsimp only at hgram
  rw [hAv, hBv, hCv] at hgram
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpal_back : (a' = 3 ∧ b' = 4) ∨ (a' = 4 ∧ b' = 3) → (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) := by
    intro h
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
  rcases hpat with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
                   ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- (0, 0, 0): 1 = 3, impossible
    simp only [pick3] at hgram; linarith only [hgram]
  · -- (0, 0, 1): a' = 3
    simp only [pick3] at hgram
    have ha3 : a' = 3 := by nlinarith only [hgram, ha']
    obtain ⟨g, hg0, hok⟩ := run_seed_geom v₀ v₁ v₂ q₁ q₂ q₃ hv0 hv1 hv2 hv01 hv02 hv12
      hq12 hq13 hq23 1 a' b' zero_lt_one ha' hb' h1a' h1b' hab' 0 0 1 hAv hBv hCv
      w1 w2 w3 hw1 hw2 hw3 hp12' hp13' hp23'
      [Q3.one] [Q3.ofInt 3] [Q3.zero, Q3.one] _ seed_001_ok (Real.sqrt 3) b' 1 hsqrt3 zero_lt_one
      (by simp [pEval, Q3.toReal_one])
      (by simp [pEval, Q3.toReal_ofInt, ha3])
      (by simp [pEval, Q3.toReal_zero, Q3.toReal_one])
    have hok' : isLinearRoot (Q3.ofInt 4) g = true ∧
        ((w1.1 = 0 ∧ w2.1 = 0 ∧ w3.1 = 0) ∨ (w1.2.1 = 0 ∧ w2.2.1 = 0 ∧ w3.2.1 = 0)) := by
      rcases hok with h | h | h | h | h | h <;>
      · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
        refine ⟨h.1, ?_⟩
        rcases h.2 with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
        · exact Or.inl ⟨by assumption, by assumption, by assumption⟩
        · exact Or.inr ⟨by assumption, by assumption, by assumption⟩
    have hb4 : b' = 4 := by
      have := eq_of_isLinearRoot hsqrt3 hok'.1 hg0
      simpa [Q3.toReal_ofInt] using this
    refine ⟨hpal_back (Or.inl ⟨ha3, hb4⟩), ?_⟩
    rcases hok'.2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨by rw [hw1.1, h1]; rfl, by rw [hw2.1, h2]; rfl, by rw [hw3.1, h3]; rfl⟩
    · refine Or.inr ⟨v₀, hv0m, ?_,
        by rw [hw1.2.1, h1]; rfl, by rw [hw2.2.1, h2]; rfl, by rw [hw3.2.1, h3]; rfl⟩
      intro v hv hne
      rcases three_of_three hv01 hv02 hv12 hv0m hv1m hv2m hv hne with rfl | rfl
      · rw [dist_comm]; exact hAv
      · rw [dist_comm]; exact hBv
  · -- (1, 1, 1): a' = 3
    simp only [pick3] at hgram
    have ha3 : a' = 3 := by
      have hmul : a' ^ 2 * (a' - 3) = 0 := by linarith only [hgram]
      linarith only [(mul_eq_zero.mp hmul).resolve_left (sq_pos_of_pos ha').ne']
    obtain ⟨g, hg0, hok⟩ := run_seed_geom v₀ v₁ v₂ q₁ q₂ q₃ hv0 hv1 hv2 hv01 hv02 hv12
      hq12 hq13 hq23 1 a' b' zero_lt_one ha' hb' h1a' h1b' hab' 1 1 1 hAv hBv hCv
      w1 w2 w3 hw1 hw2 hw3 hp12' hp13' hp23'
      [Q3.one] [Q3.ofInt 3] [Q3.zero, Q3.one] _ seed_111_ok (Real.sqrt 3) b' 1 hsqrt3 zero_lt_one
      (by simp [pEval, Q3.toReal_one])
      (by simp [pEval, Q3.toReal_ofInt, ha3])
      (by simp [pEval, Q3.toReal_zero, Q3.toReal_one])
    have hok' : isLinearRoot (Q3.ofInt 4) g = true ∧ (w1.1 = 0 ∧ w2.1 = 0 ∧ w3.1 = 0) := by
      rcases hok with h | h | h | h | h | h <;>
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨h0, ⟨h1, h2⟩, h3⟩
        exact ⟨h0, by assumption, by assumption, by assumption⟩
    have hb4 : b' = 4 := by
      have := eq_of_isLinearRoot hsqrt3 hok'.1 hg0
      simpa [Q3.toReal_ofInt] using this
    exact ⟨hpal_back (Or.inl ⟨ha3, hb4⟩),
      Or.inl ⟨by rw [hw1.1, hok'.2.1]; rfl, by rw [hw2.1, hok'.2.2.1]; rfl, by rw [hw3.1, hok'.2.2.2]; rfl⟩⟩
  · -- (1, 1, 2): b' = 4a' - a'^2, impossible
    simp only [pick3] at hgram
    have hb_eq : b' = 4 * a' - a' ^ 2 := by
      have hmul : b' * (b' - (4 * a' - a' ^ 2)) = 0 := by linarith only [hgram]
      linarith only [(mul_eq_zero.mp hmul).resolve_left hb'.ne']
    obtain ⟨g, _, hok⟩ := run_seed_geom v₀ v₁ v₂ q₁ q₂ q₃ hv0 hv1 hv2 hv01 hv02 hv12
      hq12 hq13 hq23 1 a' b' zero_lt_one ha' hb' h1a' h1b' hab' 1 1 2 hAv hBv hCv
      w1 w2 w3 hw1 hw2 hw3 hp12' hp13' hp23'
      [Q3.one] [Q3.zero, Q3.one] [Q3.zero, Q3.ofInt 4, Q3.ofInt (-1)] _ seed_112_ok
      (Real.sqrt 3) a' 1 hsqrt3 zero_lt_one
      (by simp [pEval, Q3.toReal_one])
      (by simp [pEval, Q3.toReal_zero, Q3.toReal_one])
      (by simp [pEval, Q3.toReal_zero, Q3.toReal_ofInt]; linarith only [hb_eq])
    simp at hok
  · -- (0, 1, 1): (a' - 2)^2 = 3, impossible
    simp only [pick3] at hgram
    have hs' : (a' - 2) ^ 2 = 3 := by nlinarith only [hgram]
    obtain ⟨g, _, hok⟩ := run_seed_geom v₀ v₁ v₂ q₁ q₂ q₃ hv0 hv1 hv2 hv01 hv02 hv12
      hq12 hq13 hq23 1 a' b' zero_lt_one ha' hb' h1a' h1b' hab' 0 1 1 hAv hBv hCv
      w1 w2 w3 hw1 hw2 hw3 hp12' hp13' hp23'
      [Q3.one] [⟨Frac.ofInt 2, Frac.one⟩] [Q3.zero, Q3.one] _ seed_011_ok
      (a' - 2) b' 1 hs' zero_lt_one
      (by simp [pEval, Q3.toReal_one])
      (by simp [pEval, Q3.toReal, Frac.toReal_ofInt, Frac.toReal_one])
      (by simp [pEval, Q3.toReal_zero, Q3.toReal_one])
    simp at hok
  · -- (0, 1, 2): a'^2 + b'^2 - a'b' - 2a' - 2b' + 1 = 0
    simp only [pick3] at hgram
    set t := (b' - 1) / a'
    set lam := 3 / a'
    have hlam : 0 < lam := div_pos (by norm_num) ha'
    have hP0_eq : pEval (Real.sqrt 3) t [Q3.one, Q3.ofInt (-1), Q3.one] = lam * 1 := by
      simp only [pEval, Q3.toReal_one, Q3.toReal_ofInt, mul_zero, add_zero, Int.cast_neg,
        Int.cast_one, t, lam]
      field_simp [ha'.ne']
      nlinarith only [hgram]
    have hP1_eq : pEval (Real.sqrt 3) t [Q3.ofInt 3] = lam * a' := by
      simp only [pEval, Q3.toReal_ofInt, mul_zero, add_zero, Int.cast_ofNat, lam]
      field_simp [ha'.ne']
    have hP2_eq : pEval (Real.sqrt 3) t [Q3.one, Q3.ofInt 2, Q3.one] = lam * b' := by
      simp only [pEval, Q3.toReal_one, Q3.toReal_ofInt, mul_zero, add_zero, Int.cast_ofNat, t, lam]
      field_simp [ha'.ne']
      nlinarith only [hgram]
    obtain ⟨g, hg0, hok⟩ := run_seed_geom v₀ v₁ v₂ q₁ q₂ q₃ hv0 hv1 hv2 hv01 hv02 hv12
      hq12 hq13 hq23 1 a' b' zero_lt_one ha' hb' h1a' h1b' hab' 0 1 2 hAv hBv hCv
      w1 w2 w3 hw1 hw2 hw3 hp12' hp13' hp23'
      [Q3.one, Q3.ofInt (-1), Q3.one] [Q3.ofInt 3] [Q3.one, Q3.ofInt 2, Q3.one] _ seed_012_ok
      (Real.sqrt 3) t lam hsqrt3 hlam hP0_eq hP1_eq hP2_eq
    have hok' : (isLinearRoot Q3.one g = true ∨ isLinearRoot ⟨⟨1, 1⟩, Frac.zero⟩ g = true) ∧
        (w1.1 = 0 ∧ w2.1 = 0 ∧ w3.1 = 0) := by
      rcases hok with h | h | h | h | h | h <;>
      · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with ⟨h0, ⟨h1, h2⟩, h3⟩
        exact ⟨h0, by assumption, by assumption, by assumption⟩
    have hab_val : (a' = 3 ∧ b' = 4) ∨ (a' = 4 ∧ b' = 3) := by
      rcases hok'.1 with h1 | h2
      · have ht1 : t = 1 := by
          simpa [Q3.toReal_one] using eq_of_isLinearRoot hsqrt3 h1 hg0
        have hb_eq : b' = a' + 1 := by
          have := (div_eq_iff ha'.ne').mp ht1; linarith only [this]
        rw [hb_eq] at hgram
        have hmul : a' * (a' - 3) = 0 := by linarith only [hgram]
        have ha3 : a' = 3 := by linarith only [(mul_eq_zero.mp hmul).resolve_left ha'.ne']
        exact Or.inl ⟨ha3, by linarith only [hb_eq, ha3]⟩
      · have ht2 : t = 1 / 2 := by
          have h2' := eq_of_isLinearRoot hsqrt3 h2 hg0
          have hval : Q3.toReal (Real.sqrt 3) ⟨⟨1, 1⟩, Frac.zero⟩ = 1 / 2 := by
            unfold Q3.toReal Frac.toReal Frac.den Frac.zero
            norm_num
          exact h2'.trans hval
        have ha_eq : a' = 2 * b' - 2 := by
          have := (div_eq_iff ha'.ne').mp ht2; linarith only [this]
        rw [ha_eq] at hgram
        have hmul : (b' - 1) * (b' - 3) = 0 := by linarith only [hgram]
        have hb3 : b' = 3 := by
          linarith only [(mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h1b'.symm)]
        exact Or.inr ⟨by linarith only [ha_eq, hb3], hb3⟩
    exact ⟨hpal_back hab_val,
      Or.inl ⟨by rw [hw1.1, hok'.2.1]; rfl, by rw [hw2.1, hok'.2.2.1]; rfl, by rw [hw3.1, hok'.2.2.2]; rfl⟩⟩

set_option maxHeartbeats 800000 in
/-- Canonical 6-case dispatch for normalized points `(u₀, u₁, u₂)` on the unit circle and 3 extra
points `(q₁, q₂, q₃)` with squared distances in `{1, a, b}`. -/
private lemma canonical_six_cases
    (u₀ u₁ u₂ q₁ q₂ q₃ : ℝ²)
    (hu0 : (u₀ 0) ^ 2 + (u₀ 1) ^ 2 = 1)
    (hu1 : (u₁ 0) ^ 2 + (u₁ 1) ^ 2 = 1)
    (hu2 : (u₂ 0) ^ 2 + (u₂ 1) ^ 2 = 1)
    (hu01 : u₀ ≠ u₁) (hu02 : u₀ ≠ u₂) (hu12 : u₁ ≠ u₂)
    (hq12 : q₁ ≠ q₂) (hq13 : q₁ ≠ q₃) (hq23 : q₂ ≠ q₃)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h1a : (1 : ℝ) ≠ a) (h1b : (1 : ℝ) ≠ b) (hab : a ≠ b)
    (hA_mem : dist u₁ u₀ ^ 2 = 1 ∨ dist u₁ u₀ ^ 2 = a ∨ dist u₁ u₀ ^ 2 = b)
    (hB_mem : dist u₂ u₀ ^ 2 = 1 ∨ dist u₂ u₀ ^ 2 = a ∨ dist u₂ u₀ ^ 2 = b)
    (hC_mem : dist u₂ u₁ ^ 2 = 1 ∨ dist u₂ u₁ ^ 2 = a ∨ dist u₂ u₁ ^ 2 = b)
    (hq_mem : ∀ q, q = q₁ ∨ q = q₂ ∨ q = q₃ →
      ((q 0) ^ 2 + (q 1) ^ 2 = 1 ∨ (q 0) ^ 2 + (q 1) ^ 2 = a ∨ (q 0) ^ 2 + (q 1) ^ 2 = b) ∧
      (dist u₀ q ^ 2 = 1 ∨ dist u₀ q ^ 2 = a ∨ dist u₀ q ^ 2 = b) ∧
      (dist u₁ q ^ 2 = 1 ∨ dist u₁ q ^ 2 = a ∨ dist u₁ q ^ 2 = b) ∧
      (dist u₂ q ^ 2 = 1 ∨ dist u₂ q ^ 2 = a ∨ dist u₂ q ^ 2 = b))
    (hp12 : dist q₁ q₂ ^ 2 = 1 ∨ dist q₁ q₂ ^ 2 = a ∨ dist q₁ q₂ ^ 2 = b)
    (hp13 : dist q₁ q₃ ^ 2 = 1 ∨ dist q₁ q₃ ^ 2 = a ∨ dist q₁ q₃ ^ 2 = b)
    (hp23 : dist q₂ q₃ ^ 2 = 1 ∨ dist q₂ q₃ ^ 2 = a ∨ dist q₂ q₃ ^ 2 = b) :
    ((a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3)) ∧
    (((q₁ 0) ^ 2 + (q₁ 1) ^ 2 = 1 ∧ (q₂ 0) ^ 2 + (q₂ 1) ^ 2 = 1 ∧ (q₃ 0) ^ 2 + (q₃ 1) ^ 2 = 1) ∨
     (∃ u, (u = u₀ ∨ u = u₁ ∨ u = u₂) ∧
       (∀ v, (v = u₀ ∨ v = u₁ ∨ v = u₂) → v ≠ u → dist u v ^ 2 = 1) ∧
       dist u q₁ ^ 2 = 1 ∧ dist u q₂ ^ 2 = 1 ∧ dist u q₃ ^ 2 = 1)) := by
  have toIdx : ∀ x : ℝ, x = 1 ∨ x = a ∨ x = b → ∃ i : Fin 3, x = pick3 1 a b i := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  let hcanon := canonical_six_cases_core u₀ u₁ u₂ q₁ q₂ q₃ hq12 hq13 hq23 a b
  obtain ⟨iA, hA⟩ := toIdx _ hA_mem
  obtain ⟨iB, hB⟩ := toIdx _ hB_mem
  obtain ⟨iC, hC⟩ := toIdx _ hC_mem
  have hqm_swap : ∀ (v₀ v₁ v₂ : ℝ²) (a' b' : ℝ),
      ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) →
      (v₀ = u₀ ∨ v₀ = u₁ ∨ v₀ = u₂) →
      (v₁ = u₀ ∨ v₁ = u₁ ∨ v₁ = u₂) →
      (v₂ = u₀ ∨ v₂ = u₁ ∨ v₂ = u₂) →
      (∀ q, q = q₁ ∨ q = q₂ ∨ q = q₃ →
        ((q 0) ^ 2 + (q 1) ^ 2 = 1 ∨ (q 0) ^ 2 + (q 1) ^ 2 = a' ∨ (q 0) ^ 2 + (q 1) ^ 2 = b') ∧
        (dist v₀ q ^ 2 = 1 ∨ dist v₀ q ^ 2 = a' ∨ dist v₀ q ^ 2 = b') ∧
        (dist v₁ q ^ 2 = 1 ∨ dist v₁ q ^ 2 = a' ∨ dist v₁ q ^ 2 = b') ∧
        (dist v₂ q ^ 2 = 1 ∨ dist v₂ q ^ 2 = a' ∨ dist v₂ q ^ 2 = b')) := by
    clear hcanon
    intro v₀ v₁ v₂ a' b' hsw hv0m hv1m hv2m q hq
    obtain ⟨h0, h1, h2, h3⟩ := hq_mem q hq
    have hmem : ∀ x, (x = 1 ∨ x = a ∨ x = b) → (x = 1 ∨ x = a' ∨ x = b') := by
      intro x hx
      rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hx
      · rcases hx with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
    refine ⟨hmem _ h0, ?_, ?_, ?_⟩
    · rcases hv0m with rfl | rfl | rfl <;> exact hmem _ (by assumption)
    · rcases hv1m with rfl | rfl | rfl <;> exact hmem _ (by assumption)
    · rcases hv2m with rfl | rfl | rfl <;> exact hmem _ (by assumption)
  have hmem_ab : ∀ x, (x = 1 ∨ x = a ∨ x = b) → (x = 1 ∨ x = b ∨ x = a) :=
    fun _ h => h.elim Or.inl (fun h' => h'.elim (Or.inr ∘ Or.inr) (Or.inr ∘ Or.inl))
  fin_cases iA <;> fin_cases iB <;> fin_cases iC
  · exact hcanon u₀ u₁ u₂ a b hu0 hu1 hu2 hu01 hu02 hu12 ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      hp12 hp13 hp23 0 0 0 hA hB hC (by decide)
  · exact hcanon u₀ u₁ u₂ a b hu0 hu1 hu2 hu01 hu02 hu12 ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      hp12 hp13 hp23 0 0 1 hA hB hC (by decide)
  · exact hcanon u₀ u₁ u₂ b a hu0 hu1 hu2 hu01 hu02 hu12 hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 0 0 1 hA hB hC (by decide)
  · exact hcanon u₁ u₀ u₂ a b hu1 hu0 hu2 hu01.symm hu12 hu02 ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)))
      hp12 hp13 hp23 0 0 1 (by rw [dist_comm]; exact hA) hC hB (by decide)
  · exact hcanon u₀ u₁ u₂ a b hu0 hu1 hu2 hu01 hu02 hu12 ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      hp12 hp13 hp23 0 1 1 hA hB hC (by decide)
  · exact hcanon u₀ u₁ u₂ a b hu0 hu1 hu2 hu01 hu02 hu12 ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      hp12 hp13 hp23 0 1 2 hA hB hC (by decide)
  · exact hcanon u₁ u₀ u₂ b a hu1 hu0 hu2 hu01.symm hu12 hu02 hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 0 0 1 (by rw [dist_comm]; exact hA) hC hB (by decide)
  · exact hcanon u₀ u₁ u₂ b a hu0 hu1 hu2 hu01 hu02 hu12 hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 0 1 2 hA hB hC (by decide)
  · exact hcanon u₀ u₁ u₂ b a hu0 hu1 hu2 hu01 hu02 hu12 hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 0 1 1 hA hB hC (by decide)
  · exact hcanon u₂ u₀ u₁ a b hu2 hu0 hu1 hu02.symm hu12.symm hu01 ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl)))
      hp12 hp13 hp23 0 0 1 (by rw [dist_comm]; exact hB) (by rw [dist_comm]; exact hC) hA (by decide)
  · exact hcanon u₀ u₂ u₁ a b hu0 hu2 hu1 hu02 hu01 hu12.symm ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)))
      hp12 hp13 hp23 0 1 1 hB hA (by rw [dist_comm]; exact hC) (by decide)
  · exact hcanon u₀ u₂ u₁ a b hu0 hu2 hu1 hu02 hu01 hu12.symm ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)))
      hp12 hp13 hp23 0 1 2 hB hA (by rw [dist_comm]; exact hC) (by decide)
  · exact hcanon u₁ u₂ u₀ a b hu1 hu2 hu0 hu12 hu01.symm hu02.symm ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl)
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl))
      hp12 hp13 hp23 0 1 1 hC (by rw [dist_comm]; exact hA) (by rw [dist_comm]; exact hB) (by decide)
  · exact hcanon u₀ u₁ u₂ a b hu0 hu1 hu2 hu01 hu02 hu12 ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      hp12 hp13 hp23 1 1 1 hA hB hC (by decide)
  · exact hcanon u₀ u₁ u₂ a b hu0 hu1 hu2 hu01 hu02 hu12 ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      hp12 hp13 hp23 1 1 2 hA hB hC (by decide)
  · exact hcanon u₁ u₂ u₀ a b hu1 hu2 hu0 hu12 hu01.symm hu02.symm ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl)
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl))
      hp12 hp13 hp23 0 1 2 hC (by rw [dist_comm]; exact hA) (by rw [dist_comm]; exact hB) (by decide)
  · exact hcanon u₁ u₀ u₂ a b hu1 hu0 hu2 hu01.symm hu12 hu02 ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)))
      hp12 hp13 hp23 1 1 2 (by rw [dist_comm]; exact hA) hC hB (by decide)
  · exact hcanon u₂ u₀ u₁ b a hu2 hu0 hu1 hu02.symm hu12.symm hu01 hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 1 1 2 (by rw [dist_comm]; exact hB) (by rw [dist_comm]; exact hC) hA (by decide)
  · exact hcanon u₂ u₀ u₁ b a hu2 hu0 hu1 hu02.symm hu12.symm hu01 hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 0 0 1 (by rw [dist_comm]; exact hB) (by rw [dist_comm]; exact hC) hA (by decide)
  · exact hcanon u₀ u₂ u₁ b a hu0 hu2 hu1 hu02 hu01 hu12.symm hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 0 1 2 hB hA (by rw [dist_comm]; exact hC) (by decide)
  · exact hcanon u₀ u₂ u₁ b a hu0 hu2 hu1 hu02 hu01 hu12.symm hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 0 1 1 hB hA (by rw [dist_comm]; exact hC) (by decide)
  · exact hcanon u₁ u₂ u₀ b a hu1 hu2 hu0 hu12 hu01.symm hu02.symm hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl)
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 0 1 2 hC (by rw [dist_comm]; exact hA) (by rw [dist_comm]; exact hB) (by decide)
  · exact hcanon u₂ u₀ u₁ a b hu2 hu0 hu1 hu02.symm hu12.symm hu01 ha hb h1a h1b hab (Or.inl ⟨rfl, rfl⟩)
      (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl))
      (hqm_swap _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl)))
      hp12 hp13 hp23 1 1 2 (by rw [dist_comm]; exact hB) (by rw [dist_comm]; exact hC) hA (by decide)
  · exact hcanon u₁ u₀ u₂ b a hu1 hu0 hu2 hu01.symm hu12 hu02 hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 1 1 2 (by rw [dist_comm]; exact hA) hC hB (by decide)
  · exact hcanon u₁ u₂ u₀ b a hu1 hu2 hu0 hu12 hu01.symm hu02.symm hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl)
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 0 1 1 hC (by rw [dist_comm]; exact hA) (by rw [dist_comm]; exact hB) (by decide)
  · exact hcanon u₀ u₁ u₂ b a hu0 hu1 hu2 hu01 hu02 hu12 hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 1 1 2 hA hB hC (by decide)
  · exact hcanon u₀ u₁ u₂ b a hu0 hu1 hu2 hu01 hu02 hu12 hb ha h1b h1a hab.symm (Or.inr ⟨rfl, rfl⟩)
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (hqm_swap _ _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))
      (hmem_ab _ hp12) (hmem_ab _ hp13) (hmem_ab _ hp23) 1 1 1 hA hB hC (by decide)

/-- Branch 1: if some `O ∈ B` has ≥ 3 neighbors at distance `r`, then `B` is the regular hexagon
with its centre of radius `r`. -/
private lemma branch_three_spokes {B : Finset ℝ²} (hB : B.card = 7) (hD : distinctDistances B ≤ 3)
    {O : ℝ²} (hO : O ∈ B) {r : ℝ}
    (h3 : 3 ≤ ((B.erase O).filter (fun x => dist O x = r)).card) :
    ∃ (c : ℝ²), c ∈ B ∧ 0 < r ∧ (∀ x ∈ B.erase c, dist c x = r) ∧
      ∀ d ∈ distanceSet B, d ^ 2 = r ^ 2 ∨ d ^ 2 = 3 * r ^ 2 ∨ d ^ 2 = 4 * r ^ 2 := by
  obtain ⟨P₀, hP₀f, P₁, hP₁f, P₂, hP₂f, hP01, hP02, hP12⟩ :=
    Finset.two_lt_card.mp (show 2 < ((B.erase O).filter (fun x => dist O x = r)).card by omega)
  have hP₀e := (mem_filter.mp hP₀f).1
  have hP₁e := (mem_filter.mp hP₁f).1
  have hP₂e := (mem_filter.mp hP₂f).1
  have hdP₀ : dist O P₀ = r := (mem_filter.mp hP₀f).2
  have hdP₁ : dist O P₁ = r := (mem_filter.mp hP₁f).2
  have hdP₂ : dist O P₂ = r := (mem_filter.mp hP₂f).2
  have hP₀B : P₀ ∈ B := erase_subset _ _ hP₀e
  have hP₁B : P₁ ∈ B := erase_subset _ _ hP₁e
  have hP₂B : P₂ ∈ B := erase_subset _ _ hP₂e
  have hOP₀ : P₀ ≠ O := (mem_erase.mp hP₀e).1
  have hOP₁ : P₁ ≠ O := (mem_erase.mp hP₁e).1
  have hOP₂ : P₂ ≠ O := (mem_erase.mp hP₂e).1
  have hr : 0 < r := hdP₀ ▸ dist_pos.mpr hOP₀.symm
  let R := (((B.erase O).erase P₀).erase P₁).erase P₂
  have hR_card : R.card = 3 := by
    have h1 : (B.erase O).card = 6 := by rw [card_erase_of_mem hO, hB]
    have h2 : ((B.erase O).erase P₀).card = 5 := by rw [card_erase_of_mem hP₀e, h1]
    have hP1m : P₁ ∈ (B.erase O).erase P₀ := mem_erase.mpr ⟨hP01.symm, hP₁e⟩
    have h3' : (((B.erase O).erase P₀).erase P₁).card = 4 := by rw [card_erase_of_mem hP1m, h2]
    have hP2m : P₂ ∈ ((B.erase O).erase P₀).erase P₁ :=
      mem_erase.mpr ⟨hP12.symm, mem_erase.mpr ⟨hP02.symm, hP₂e⟩⟩
    rw [card_erase_of_mem hP2m, h3']
  obtain ⟨Q₁, hQ₁R, Q₂, hQ₂R, Q₃, hQ₃R, hQ12, hQ13, hQ23⟩ :=
    Finset.two_lt_card.mp (show 2 < R.card by omega)
  have hR_eq : {Q₁, Q₂, Q₃} = R := by
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · rw [hR_card]; simp [hQ12, hQ13, hQ23]
  have hB_mem : ∀ x ∈ B, x = O ∨ x = P₀ ∨ x = P₁ ∨ x = P₂ ∨ x = Q₁ ∨ x = Q₂ ∨ x = Q₃ := by
    intro x hx
    by_cases h0 : x = O; · exact Or.inl h0
    by_cases h1 : x = P₀; · exact Or.inr (Or.inl h1)
    by_cases h2 : x = P₁; · exact Or.inr (Or.inr (Or.inl h2))
    by_cases h3' : x = P₂; · exact Or.inr (Or.inr (Or.inr (Or.inl h3')))
    have hxR : x ∈ R := mem_erase.mpr ⟨h3', mem_erase.mpr ⟨h2, mem_erase.mpr ⟨h1, mem_erase.mpr ⟨h0, hx⟩⟩⟩⟩
    rw [← hR_eq, mem_insert, mem_insert, mem_singleton] at hxR
    tauto
  let normPt (x : ℝ²) : ℝ² := (r⁻¹ : ℝ) • (x - O)
  have hdist_norm : ∀ x y : ℝ², dist (normPt x) (normPt y) ^ 2 = (dist x y / r) ^ 2 := by
    intro x y
    simp only [normPt, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    ring
  have hnorm_sq : ∀ x : ℝ², (normPt x 0) ^ 2 + (normPt x 1) ^ 2 = (dist O x / r) ^ 2 := by
    intro x
    rw [← norm_sq_coords, show ‖normPt x‖ = dist (normPt x) (normPt O) by
      simp [normPt, dist_eq_norm]]
    rw [hdist_norm, dist_comm]
  let S := (distanceSet B).image (fun d => (d / r) ^ 2)
  have hScard : S.card ≤ 3 := card_image_le.trans hD
  have h1S : (1 : ℝ) ∈ S := by
    apply mem_image.mpr
    refine ⟨r, hdP₀ ▸ pair_dist_mem hO hP₀B hOP₀.symm, ?_⟩
    rw [div_self hr.ne', one_pow]
  have hSpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hx
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := mem_image.mp hd
    have hne := (mem_offDiag.mp hpq).2.2
    exact sq_pos_of_pos (div_pos (dist_pos.mpr hne) hr)
  obtain ⟨a, b, ha, hb, h1a, h1b, hab, hSmem⟩ := pad_palette hScard h1S hSpos
  have hpair_norm : ∀ x y : ℝ², x ∈ B → y ∈ B → x ≠ y →
      dist (normPt x) (normPt y) ^ 2 = 1 ∨ dist (normPt x) (normPt y) ^ 2 = a ∨
      dist (normPt x) (normPt y) ^ 2 = b := by
    intro x y hx hy hne
    rw [hdist_norm]
    exact hSmem _ (mem_image.mpr ⟨dist x y, pair_dist_mem hx hy hne, rfl⟩)
  have hinj_norm : ∀ x y : ℝ², x ≠ y → normPt x ≠ normPt y := by
    intro x y hne heq
    have h0 : dist (normPt x) (normPt y) ^ 2 = 0 := by rw [heq, dist_self]; ring
    rw [hdist_norm] at h0
    have hd0 : dist x y = 0 := by
      have := sq_eq_zero_iff.mp h0
      exact (div_eq_zero_iff.mp this).resolve_right hr.ne'
    exact hne (dist_eq_zero.mp hd0)
  have hQ_props : ∀ Q, Q ∈ R → Q ∈ B ∧ Q ≠ O ∧ Q ≠ P₀ ∧ Q ≠ P₁ ∧ Q ≠ P₂ := by
    intro Q hQ
    have h1 := mem_erase.mp hQ
    have h2 := mem_erase.mp h1.2
    have h3' := mem_erase.mp h2.2
    have h4 := mem_erase.mp h3'.2
    exact ⟨h4.2, h4.1, h3'.1, h2.1, h1.1⟩
  obtain ⟨hQ1B, hQ1O, hQ1P0, hQ1P1, hQ1P2⟩ := hQ_props Q₁ hQ₁R
  obtain ⟨hQ2B, hQ2O, hQ2P0, hQ2P1, hQ2P2⟩ := hQ_props Q₂ hQ₂R
  obtain ⟨hQ3B, hQ3O, hQ3P0, hQ3P1, hQ3P2⟩ := hQ_props Q₃ hQ₃R
  have hres := canonical_six_cases
    (normPt P₀) (normPt P₁) (normPt P₂) (normPt Q₁) (normPt Q₂) (normPt Q₃)
    (by rw [hnorm_sq, hdP₀, div_self hr.ne', one_pow])
    (by rw [hnorm_sq, hdP₁, div_self hr.ne', one_pow])
    (by rw [hnorm_sq, hdP₂, div_self hr.ne', one_pow])
    (hinj_norm _ _ hP01) (hinj_norm _ _ hP02) (hinj_norm _ _ hP12)
    (hinj_norm _ _ hQ12) (hinj_norm _ _ hQ13) (hinj_norm _ _ hQ23)
    a b ha hb h1a h1b hab
    (hpair_norm _ _ hP₁B hP₀B hP01.symm)
    (hpair_norm _ _ hP₂B hP₀B hP02.symm)
    (hpair_norm _ _ hP₂B hP₁B hP12.symm)
    (by
      intro q hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨by rw [hnorm_sq]; exact hSmem _ (mem_image.mpr ⟨dist O Q₁, pair_dist_mem hO hQ1B hQ1O.symm, rfl⟩),
          hpair_norm _ _ hP₀B hQ1B hQ1P0.symm, hpair_norm _ _ hP₁B hQ1B hQ1P1.symm, hpair_norm _ _ hP₂B hQ1B hQ1P2.symm⟩
      · exact ⟨by rw [hnorm_sq]; exact hSmem _ (mem_image.mpr ⟨dist O Q₂, pair_dist_mem hO hQ2B hQ2O.symm, rfl⟩),
          hpair_norm _ _ hP₀B hQ2B hQ2P0.symm, hpair_norm _ _ hP₁B hQ2B hQ2P1.symm, hpair_norm _ _ hP₂B hQ2B hQ2P2.symm⟩
      · exact ⟨by rw [hnorm_sq]; exact hSmem _ (mem_image.mpr ⟨dist O Q₃, pair_dist_mem hO hQ3B hQ3O.symm, rfl⟩),
          hpair_norm _ _ hP₀B hQ3B hQ3P0.symm, hpair_norm _ _ hP₁B hQ3B hQ3P1.symm, hpair_norm _ _ hP₂B hQ3B hQ3P2.symm⟩)
    (hpair_norm _ _ hQ1B hQ2B hQ12) (hpair_norm _ _ hQ1B hQ3B hQ13) (hpair_norm _ _ hQ2B hQ3B hQ23)
  have hPal : ∀ d ∈ distanceSet B, d ^ 2 = r ^ 2 ∨ d ^ 2 = 3 * r ^ 2 ∨ d ^ 2 = 4 * r ^ 2 := by
    intro d hd
    have hmem := hSmem _ (mem_image.mpr ⟨d, hd, rfl⟩)
    rcases hres.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rcases hmem with h | h | h
      · left; rw [div_pow, div_eq_iff (sq_pos_of_pos hr).ne'] at h; linarith
      · right; rw [div_pow, div_eq_iff (sq_pos_of_pos hr).ne'] at h; first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
      · right; rw [div_pow, div_eq_iff (sq_pos_of_pos hr).ne'] at h; first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
  have hdist_of_one : ∀ x y : ℝ², dist (normPt x) (normPt y) ^ 2 = 1 → dist x y = r := by
    intro x y h
    rw [hdist_norm, div_pow, div_eq_iff (sq_pos_of_pos hr).ne'] at h
    nlinarith [dist_nonneg (x := x) (y := y)]
  rcases hres.2 with ⟨h1, h2, h3'⟩ | ⟨u, hum, huv, hq1', hq2', hq3'⟩
  · refine ⟨O, hO, hr, ?_, hPal⟩
    intro x hx
    have hxB := erase_subset _ _ hx
    have hxO := (mem_erase.mp hx).1
    rcases hB_mem x hxB with h | h | h | h | h | h | h
    · exact absurd h hxO
    · rw [h]; exact hdP₀
    · rw [h]; exact hdP₁
    · rw [h]; exact hdP₂
    · rw [h]
      rw [hnorm_sq, div_pow, div_eq_iff (sq_pos_of_pos hr).ne'] at h1
      nlinarith [dist_nonneg (x := O) (y := Q₁)]
    · rw [h]
      rw [hnorm_sq, div_pow, div_eq_iff (sq_pos_of_pos hr).ne'] at h2
      nlinarith [dist_nonneg (x := O) (y := Q₂)]
    · rw [h]
      rw [hnorm_sq, div_pow, div_eq_iff (sq_pos_of_pos hr).ne'] at h3'
      nlinarith [dist_nonneg (x := O) (y := Q₃)]
  · rcases hum with rfl | rfl | rfl
    · refine ⟨P₀, hP₀B, hr, ?_, hPal⟩
      intro x hx
      rcases hB_mem x (erase_subset _ _ hx) with h | h | h | h | h | h | h
      · rw [h, dist_comm]; exact hdP₀
      · exact absurd h (mem_erase.mp hx).1
      · rw [h]; exact hdist_of_one _ _ (huv (normPt P₁) (Or.inr (Or.inl rfl)) (hinj_norm _ _ hP01.symm))
      · rw [h]; exact hdist_of_one _ _ (huv (normPt P₂) (Or.inr (Or.inr rfl)) (hinj_norm _ _ hP02.symm))
      · rw [h]; exact hdist_of_one _ _ hq1'
      · rw [h]; exact hdist_of_one _ _ hq2'
      · rw [h]; exact hdist_of_one _ _ hq3'
    · refine ⟨P₁, hP₁B, hr, ?_, hPal⟩
      intro x hx
      rcases hB_mem x (erase_subset _ _ hx) with h | h | h | h | h | h | h
      · rw [h, dist_comm]; exact hdP₁
      · rw [h]; exact hdist_of_one _ _ (huv (normPt P₀) (Or.inl rfl) (hinj_norm _ _ hP01))
      · exact absurd h (mem_erase.mp hx).1
      · rw [h]; exact hdist_of_one _ _ (huv (normPt P₂) (Or.inr (Or.inr rfl)) (hinj_norm _ _ hP12.symm))
      · rw [h]; exact hdist_of_one _ _ hq1'
      · rw [h]; exact hdist_of_one _ _ hq2'
      · rw [h]; exact hdist_of_one _ _ hq3'
    · refine ⟨P₂, hP₂B, hr, ?_, hPal⟩
      intro x hx
      rcases hB_mem x (erase_subset _ _ hx) with h | h | h | h | h | h | h
      · rw [h, dist_comm]; exact hdP₂
      · rw [h]; exact hdist_of_one _ _ (huv (normPt P₀) (Or.inl rfl) (hinj_norm _ _ hP02))
      · rw [h]; exact hdist_of_one _ _ (huv (normPt P₁) (Or.inr (Or.inl rfl)) (hinj_norm _ _ hP12))
      · exact absurd h (mem_erase.mp hx).1
      · rw [h]; exact hdist_of_one _ _ hq1'
      · rw [h]; exact hdist_of_one _ _ hq2'
      · rw [h]; exact hdist_of_one _ _ hq3'

/- ### Part 4: Branch 2 (every distance fibre has size ≤ 2) and main theorem -/

private lemma branch_two_fibres {B : Finset ℝ²} (hB : B.card = 7) (hD : distinctDistances B ≤ 3)
    (h2 : ∀ O ∈ B, ∀ d : ℝ, ((B.erase O).filter (fun x => dist O x = d)).card ≤ 2) :
    distinctDistances B = 3 ∧
      ∃ (c : ℝ²) (r : ℝ), 0 < r ∧ (∀ x ∈ B, dist c x = r) ∧ r ∉ distanceSet B := by
  let T := distanceSet B
  obtain ⟨x₀, hx₀⟩ : B.Nonempty := card_pos.mp (by omega)
  have hmaps : ∀ x ∈ B, ∀ y ∈ B.erase x, dist x y ∈ T := fun x hx y hy =>
    pair_dist_mem hx (erase_subset _ _ hy) (mem_erase.mp hy).1.symm
  have hT_card : T.card = 3 := by
    have h6 : (B.erase x₀).card = 6 := by rw [card_erase_of_mem hx₀, hB]
    have hfib := card_eq_sum_card_fiberwise (hmaps x₀ hx₀)
    have hle : ∑ d ∈ T, ((B.erase x₀).filter (fun y => dist x₀ y = d)).card ≤ ∑ _d ∈ T, 2 :=
      sum_le_sum fun d _ => h2 x₀ hx₀ d
    simp only [sum_const, smul_eq_mul] at hle
    have hD' : T.card ≤ 3 := hD
    omega
  have hsat : ∀ x ∈ B, ∀ d ∈ T, ((B.erase x).filter (fun y => dist x y = d)).card = 2 := by
    intro x hx d hd
    by_contra hne
    have h6 : (B.erase x).card = 6 := by rw [card_erase_of_mem hx, hB]
    have hlt := sum_lt_sum (fun e _ => h2 x hx e) ⟨d, hd, lt_of_le_of_ne (h2 x hx d) hne⟩
    rw [← card_eq_sum_card_fiberwise (hmaps x hx)] at hlt
    simp only [sum_const, smul_eq_mul, h6, hT_card] at hlt
    omega
  let K : ℝ := 2 * ∑ d ∈ T, d ^ 2
  have hsum_sq : ∀ x ∈ B, ∑ y ∈ B, dist x y ^ 2 = K := by
    intro x hx
    have h1 : ∑ y ∈ B, dist x y ^ 2 = ∑ y ∈ B.erase x, dist x y ^ 2 := by
      rw [← add_sum_erase _ _ hx, dist_self, zero_pow two_ne_zero, zero_add]
    rw [h1, ← sum_fiberwise_of_maps_to (hmaps x hx)]
    calc ∑ d ∈ T, ∑ y ∈ (B.erase x).filter (fun y => dist x y = d), dist x y ^ 2
        = ∑ d ∈ T, ∑ _y ∈ (B.erase x).filter (fun y => dist x y = d), d ^ 2 :=
          sum_congr rfl fun d _ => sum_congr rfl fun y hy => by rw [(mem_filter.mp hy).2]
      _ = ∑ d ∈ T, 2 * d ^ 2 :=
          sum_congr rfl fun d hd => by simp [hsat x hx d hd]
      _ = K := by rw [← mul_sum]
  have hK_pos : 0 < K := by
    obtain ⟨y₀, hy₀⟩ : (B.erase x₀).Nonempty := card_pos.mp (by rw [card_erase_of_mem hx₀, hB]; omega)
    have hne : x₀ ≠ y₀ := (mem_erase.mp hy₀).1.symm
    have hpos : 0 < dist x₀ y₀ ^ 2 := sq_pos_of_pos (dist_pos.mpr hne)
    rw [← hsum_sq x₀ hx₀]
    exact lt_of_lt_of_le hpos (single_le_sum (fun y _ => sq_nonneg (dist x₀ y)) (erase_subset _ _ hy₀))
  let c : ℝ² := ((7 : ℝ)⁻¹) • ∑ y ∈ B, y
  have hbal : ∑ y ∈ B, (y - c) = 0 := by
    rw [sum_sub_distrib, sum_const, hB, ← Nat.cast_smul_eq_nsmul ℝ 7 c]
    ext i
    simp only [c, Nat.cast_ofNat, PiLp.sub_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul]
    ring
  let S0 : ℝ := ∑ y ∈ B, dist c y ^ 2
  have hdist_expand : ∀ x ∈ B, 7 * dist c x ^ 2 + S0 = K := by
    intro x hx
    have hterm : ∀ y ∈ B, dist x y ^ 2 = dist c x ^ 2 + dist c y ^ 2 - 2 * inner ℝ (x - c) (y - c) := by
      intro y _
      rw [dist_eq_norm, show x - y = (x - c) - (y - c) by abel, norm_sub_sq_real,
          ← dist_eq_norm, ← dist_eq_norm, dist_comm c x, dist_comm c y]
      ring
    have h := hsum_sq x hx
    rw [sum_congr rfl hterm, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← inner_sum, hbal,
        inner_zero_right, mul_zero, sub_zero, sum_const, hB, nsmul_eq_mul] at h
    exact h
  have hS0 : 2 * S0 = K := by
    have hsum7 := sum_congr rfl hdist_expand
    rw [sum_add_distrib, ← mul_sum, sum_const, sum_const, hB, nsmul_eq_mul, nsmul_eq_mul] at hsum7
    change 7 * S0 + 7 * S0 = 7 * K at hsum7
    linarith
  let r : ℝ := Real.sqrt (K / 14)
  have hr : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr_sq : r ^ 2 = K / 14 := Real.sq_sqrt (by linarith)
  have hRad : ∀ x ∈ B, dist c x = r := by
    intro x hx
    have hsq : dist c x ^ 2 = r ^ 2 := by linarith [hdist_expand x hx, hS0, hr_sq]
    nlinarith [dist_nonneg (x := c) (y := x)]
  have hr_not_mem : r ∉ T := by
    intro hrT
    have hc_not_B : c ∉ B := by
      intro hcB
      have := hRad c hcB
      rw [dist_self] at this
      linarith
    let B' := insert c (B.erase x₀)
    have hB'_card : B'.card = 7 := by
      rw [card_insert_of_notMem (fun h => hc_not_B (erase_subset _ _ h)), card_erase_of_mem hx₀, hB]
    have hB'_sub : distanceSet B' ⊆ T := by
      intro d hd
      obtain ⟨⟨p, q⟩, hpq, rfl⟩ := mem_image.mp hd
      obtain ⟨hp, hq, hne⟩ := mem_offDiag.mp hpq
      rcases mem_insert.mp hp with rfl | hp' <;> rcases mem_insert.mp hq with rfl | hq'
      · exact absurd rfl hne
      · rw [hRad q (erase_subset _ _ hq')]; exact hrT
      · rw [dist_comm, hRad p (erase_subset _ _ hp')]; exact hrT
      · exact pair_dist_mem (erase_subset _ _ hp') (erase_subset _ _ hq') hne
    have hB'_D : distinctDistances B' ≤ 3 := (card_le_card hB'_sub).trans hT_card.le
    have hc_B' : c ∈ B' := mem_insert_self c _
    have hB'_erase_c : B'.erase c = B.erase x₀ :=
      erase_insert (fun h => hc_not_B (erase_subset _ _ h))
    have h3 : 3 ≤ ((B'.erase c).filter (fun x => dist c x = r)).card := by
      rw [hB'_erase_c, filter_true_of_mem (fun x hx => hRad x (erase_subset _ _ hx)),
          card_erase_of_mem hx₀, hB]
      omega
    obtain ⟨c', hc', _, hRad', hPal'⟩ := branch_three_spokes hB'_card hB'_D hc_B' h3
    obtain ⟨hDD', _⟩ := wheel_of_center_and_palette hB'_card hc' hr hRad' hPal'
    have hEq : distanceSet B' = T := eq_of_subset_of_card_le hB'_sub (by rw [hT_card]; exact hDD'.ge)
    have hPalB : ∀ d ∈ T, d ^ 2 = r ^ 2 ∨ d ^ 2 = 3 * r ^ 2 ∨ d ^ 2 = 4 * r ^ 2 := by
      intro d hd; exact hPal' d (hEq.symm ▸ hd)
    let S3 : Finset ℝ := {r, Real.sqrt 3 * r, 2 * r}
    have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h12 : r ≠ Real.sqrt 3 * r := by
      intro h; have hsq := congrArg (· ^ 2) h
      rw [mul_pow, hsqrt3_sq] at hsq; nlinarith
    have h13 : r ≠ 2 * r := by linarith
    have h23 : Real.sqrt 3 * r ≠ 2 * r := by
      intro h; have hsq := congrArg (· ^ 2) h
      rw [mul_pow, hsqrt3_sq] at hsq; nlinarith
    have hmaps3 : ∀ y ∈ B.erase x₀, dist x₀ y ∈ S3 := by
      intro y hy
      have hd := hmaps x₀ hx₀ y hy
      rcases hPalB _ hd with h | h | h
      · have : dist x₀ y = r := by nlinarith [dist_nonneg (x := x₀) (y := y)]
        simp [S3, this]
      · have : dist x₀ y = Real.sqrt 3 * r := by
          have hsq : dist x₀ y ^ 2 = (Real.sqrt 3 * r) ^ 2 := by rw [mul_pow, hsqrt3_sq]; exact h
          nlinarith [dist_nonneg (x := x₀) (y := y), mul_pos hsqrt3_pos hr]
        simp [S3, this]
      · have : dist x₀ y = 2 * r := by nlinarith [dist_nonneg (x := x₀) (y := y)]
        simp [S3, this]
    have hcx₀ : c ≠ x₀ := fun h => hc_not_B (h ▸ hx₀)
    have hf1 : ((B.erase x₀).filter (fun y => dist x₀ y = r)).card ≤ 2 :=
      inter_two_circles_le_two c x₀ r r hcx₀ _ fun y hy =>
        ⟨hRad y (erase_subset _ _ (mem_filter.mp hy).1), (mem_filter.mp hy).2⟩
    have hf2 : ((B.erase x₀).filter (fun y => dist x₀ y = Real.sqrt 3 * r)).card ≤ 2 :=
      inter_two_circles_le_two c x₀ r (Real.sqrt 3 * r) hcx₀ _ fun y hy =>
        ⟨hRad y (erase_subset _ _ (mem_filter.mp hy).1), (mem_filter.mp hy).2⟩
    have hf3 : ((B.erase x₀).filter (fun y => dist x₀ y = 2 * r)).card ≤ 1 := by
      refine (card_le_card (t := {(2 : ℝ) • c - x₀}) ?_).trans (by simp)
      intro y hy
      rw [mem_singleton]
      exact antipodal_of_dist_two_mul (hRad x₀ hx₀) (hRad y (erase_subset _ _ (mem_filter.mp hy).1))
        (mem_filter.mp hy).2
    have hfib := card_eq_sum_card_fiberwise hmaps3
    rw [card_erase_of_mem hx₀, hB] at hfib
    dsimp only [S3] at hfib
    rw [sum_insert (by simp [h12, h13]), sum_insert (by simp [h23]), sum_singleton] at hfib
    omega
  exact ⟨hT_card, c, r, hr, hRad, hr_not_mem⟩

end Erdos91H1

theorem OMA.solution : OMA.R_Erdos91_erdos_91_variants_eight_R1_H1_R1.H1 := by
  intro B hB hD
  by_cases h3 : ∃ O ∈ B, ∃ r : ℝ, 3 ≤ ((B.erase O).filter (fun x => dist O x = r)).card
  · obtain ⟨O, hO, r, hcard⟩ := h3
    obtain ⟨c, hc, hr, hRad, hPal⟩ := Erdos91H1.branch_three_spokes hB hD hO hcard
    obtain ⟨hDD, hBal⟩ := Erdos91H1.wheel_of_center_and_palette hB hc hr hRad hPal
    exact ⟨hDD, Or.inr ⟨c, r, hc, hr, hRad, hBal, hPal⟩⟩
  · push Not at h3
    have h2 : ∀ O ∈ B, ∀ d : ℝ, ((B.erase O).filter (fun x => dist O x = d)).card ≤ 2 := by
      intro O hO d; have := h3 O hO d; omega
    obtain ⟨hDD, hcirc⟩ := Erdos91H1.branch_two_fibres hB hD h2
    exact ⟨hDD, Or.inl hcirc⟩
