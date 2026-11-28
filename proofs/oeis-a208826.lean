import OMAStatements.S_oeis_a208826

-- Credit: @RiverMint78

namespace Necklace208826

-- Labelings fixed by the reflection through position zero.
section
open OMA.S_oeis_a208826

abbrev NeckFixed (n : ℕ) := {f : Lab n // ∀ i, f.1 i = f.1 (-i)}
end

-- Apply Burnside to the action of the ten dihedral symmetries.
section
open OMA.S_oeis_a208826

def neckPerm : DihedralGroup 5 → Equiv.Perm (ZMod 5)
  | .r s => Equiv.addLeft s
  | .sr s => Equiv.subLeft s

def neckAct {n : ℕ} (g : DihedralGroup 5) (f : Lab n) : Lab n :=
  ⟨fun i => f.1 (neckPerm g i),
    fun i => f.2.1 (neckPerm g i), (Equiv.sum_comp (neckPerm g) f.1).trans f.2.2⟩

instance neckAction (n : ℕ) : MulAction (DihedralGroup 5) (Lab n) where
  smul := neckAct
  one_smul f := by
    apply Subtype.ext
    funext i
    change f.1 (0 + i) = f.1 i
    rw [zero_add]
  mul_smul g h f := by
    apply Subtype.ext
    funext i
    change f.1 (neckPerm (g*h) i) = f.1 (neckPerm h (neckPerm g i))
    apply congrArg f.1
    cases g <;> cases h <;> simp [neckPerm] <;> ring

instance neckLabFinite (n : ℕ) : Finite (Lab n) := by
  let e : Lab n → (ZMod 5 → ↥(Finset.Icc (-(n : ℤ)) (n : ℤ))) :=
    fun f i => ⟨f.1 i, Finset.mem_Icc.mpr (abs_le.mp (f.2.1 i))⟩
  apply Finite.of_injective e
  intro f g h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

lemma neck_same (n : ℕ) (f g : Lab n) :
    Same n f g ↔ (MulAction.orbitRel (DihedralGroup 5) (Lab n)) f g := by
  change Same n f g ↔ ∃ h : DihedralGroup 5, h • g = f
  constructor
  · rintro ⟨s, hrs | hrs⟩
    · exact ⟨.r s, Subtype.ext (funext fun i => (hrs i).symm)⟩
    · exact ⟨.sr s, Subtype.ext (funext fun i => (hrs i).symm)⟩
  · rintro ⟨h, rfl⟩
    cases h with
    | r s => exact ⟨s, Or.inl (fun _ => rfl)⟩
    | sr s => exact ⟨s, Or.inr (fun _ => rfl)⟩

def neckZero (n : ℕ) : Lab n := ⟨fun _ => 0, by simp⟩

lemma neck_fixi (n : ℕ) :
    Nat.card (MulAction.fixedBy (Lab n) (DihedralGroup.r (0 : ZMod 5))) = Nat.card (Lab n) := by
  rw [DihedralGroup.r_zero, MulAction.fixedBy_one_eq_univ]
  exact Nat.card_congr (Equiv.Set.univ _)

lemma neck_fixr (n : ℕ) (s : ZMod 5) (hs : s ≠ 0) :
    Nat.card (MulAction.fixedBy (Lab n) (DihedralGroup.r s)) = 1 := by
  have hgen : ∀ s i : ZMod 5, s ≠ 0 → ∃ k : Fin 5, (k.val : ZMod 5) * s = i := by decide
  have onlyZero (f : Lab n) (h : DihedralGroup.r s • f = f) : f = neckZero n := by
    have step (i : ZMod 5) : f.1 (s + i) = f.1 i := congrFun (congrArg Subtype.val h) i
    have iter (k : ℕ) (i : ZMod 5) : f.1 ((k : ZMod 5)*s+i) = f.1 i := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.cast_succ, add_mul, one_mul, show (k : ZMod 5)*s+s+i=s+((k : ZMod 5)*s+i) by ring, step, ih]
    have const (i : ZMod 5) : f.1 i = f.1 0 := by
      obtain ⟨k, hk⟩ := hgen s i hs
      simpa only [hk, add_zero] using iter k.val 0
    have hsum := f.2.2
    have sum0 : ∑ _ : ZMod 5, f.1 0 = 0 := (Finset.sum_congr rfl fun i _ => (const i).symm).trans hsum
    simp [ZMod.card] at sum0
    exact Subtype.ext (funext fun i => (const i).trans (by simpa [neckZero] using sum0))
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨fun f g => Subtype.ext ((onlyZero _ f.2).trans (onlyZero _ g.2).symm)⟩, ?_⟩
  exact ⟨⟨neckZero n, rfl⟩⟩

lemma neck_fixsr_iff (n : ℕ) (s : ZMod 5) (f : Lab n) :
    f ∈ MulAction.fixedBy (Lab n) (DihedralGroup.sr s) ↔ ∀ i, f.1 (s-i) = f.1 i := by
  constructor
  · intro h i
    exact congrFun (congrArg Subtype.val (show DihedralGroup.sr s • f = f from h)) i
  · intro h
    exact Subtype.ext (funext h)

def neck_refEquiv (n : ℕ) (s t : ZMod 5) (ht : t + t = s) :
    MulAction.fixedBy (Lab n) (DihedralGroup.sr s) ≃ NeckFixed n where
  toFun f := ⟨DihedralGroup.r t • f.1, by
    intro i
    change f.1.1 (t+i) = f.1.1 (t + -i)
    rw [show t + -i = s-(t+i) by rw [← ht]; ring]
    exact ((neck_fixsr_iff n s f.1).mp f.2 _).symm⟩
  invFun f := ⟨DihedralGroup.r (-t) • f.1, by
    apply (neck_fixsr_iff n s _).mpr
    intro i
    change f.1.1 (-t + (s-i)) = f.1.1 (-t+i)
    rw [show -t+(s-i) = -(-t+i) by rw [← ht]; ring]
    exact (f.2 _).symm⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change f.1.1 (t+(-t+i)) = f.1.1 i
    apply congrArg f.1.1
    ring
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change f.1.1 (-t+(t+i)) = f.1.1 i
    apply congrArg f.1.1
    ring

lemma neck_fixes (n : ℕ) (s : ZMod 5) :
    Nat.card (MulAction.fixedBy (Lab n) (DihedralGroup.sr s)) = Nat.card (NeckFixed n) := by
  have h : ∀ z : ZMod 5, ∃ t : ZMod 5, t+t=z := by decide
  obtain ⟨t, ht⟩ := h s
  exact Nat.card_congr (neck_refEquiv n s t ht)

lemma neck_orbit (n : ℕ) : 10 * (a n : ℚ) =
    (Nat.card (Lab n) : ℚ) + 4 + 5 * (Nat.card (NeckFixed n) : ℚ) := by
  classical
  let countFix (g : DihedralGroup 5) := Nat.card (MulAction.fixedBy (Lab n) g)
  have hsum := Nat.card_congr (MulAction.sigmaFixedByEquivOrbitsProdGroup (DihedralGroup 5) (Lab n))
  have ho : a n = Nat.card (MulAction.orbitRel.Quotient (DihedralGroup 5) (Lab n)) :=
    Nat.card_congr (Quot.congrRight (neck_same n))
  rw [Nat.card_sigma, Nat.card_prod, DihedralGroup.nat_card, ← ho] at hsum
  change (∑ g, countFix g) = a n * 10 at hsum
  rw [← (@DihedralGroup.equivSum 5).symm.sum_comp countFix, Fintype.sum_sum_type] at hsum
  change (∑ s : ZMod 5, countFix (.r s)) + (∑ s : ZMod 5, countFix (.sr s)) = a n * 10 at hsum
  have hr (s : ZMod 5) : countFix (.r s) = if s = 0 then Nat.card (Lab n) else 1 := by
    by_cases hs : s = 0
    · rw [if_pos hs, hs]
      exact neck_fixi n
    · rw [if_neg hs]
      exact neck_fixr n s hs
  have href (s : ZMod 5) : countFix (.sr s) = Nat.card (NeckFixed n) := neck_fixes n s
  simp_rw [hr, href] at hsum
  have hrot (b : ℕ) : (∑ s : ZMod 5, if s = 0 then b else 1) = b + 4 := by
    change (∑ s : Fin 5, if s = 0 then b else 1) = _
    simp [Fin.sum_univ_succ]
  rw [hrot] at hsum
  simp [ZMod.card] at hsum
  exact_mod_cast (show 10 * a n = Nat.card (Lab n) + 4 + 5 * Nat.card (NeckFixed n) by omega)
end

-- Shift the labels to the interval from zero to 2n and extract the coefficient of degree 5n.
section
open OMA.S_oeis_a208826 PowerSeries Finset

def neckShift (n : ℕ) : Lab n ≃
    {f : ZMod 5 → Fin (2*n+1) // ∑ i, (f i : ℕ) = 5*n} where
  toFun f := ⟨fun i => ⟨(f.1 i + n).toNat, by
    have hi := abs_le.mp (f.2.1 i)
    omega⟩, by
      change (∑ i : ZMod 5, (f.1 i + (n:ℤ)).toNat) = 5*n
      have hnn (i : ZMod 5) : 0 ≤ f.1 i + (n:ℤ) := by have hi := abs_le.mp (f.2.1 i); omega
      apply Int.ofNat_inj.mp
      push_cast
      simp only [Int.toNat_of_nonneg (hnn _)]
      simp [Finset.sum_add_distrib, f.2.2, ZMod.card]⟩
  invFun g := ⟨fun i => (g.1 i : ℤ) - n, fun i => by
    change |(g.1 i : ℤ) - n| ≤ n
    apply abs_le.mpr
    have := (g.1 i).isLt
    omega, by
      have h := congrArg (fun j : ℕ => (j : ℤ)) g.2
      push_cast at h
      simp [Finset.sum_sub_distrib, h, ZMod.card]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    have hi := abs_le.mp (f.2.1 i)
    change (((f.1 i + n).toNat : ℤ) - n) = f.1 i
    omega
  right_inv g := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (((g.1 i : ℤ) - n + n).toNat) = _
    simp

lemma neck_coeff (n : ℕ) :
    (Nat.card (Lab n) : ℚ) =
    coeff (5*n) ((∑ j : Fin (2*n+1), (X : PowerSeries ℚ) ^ (j:ℕ)) ^ 5) := by
  classical
  have hpow : (∑ j : Fin (2*n+1), (X : PowerSeries ℚ) ^ (j:ℕ)) ^ 5 =
      ∑ f : ZMod 5 → Fin (2*n+1), (X : PowerSeries ℚ) ^ (∑ i, (f i : ℕ)) := by
    simpa [← Finset.prod_pow_eq_pow_sum, ZMod.card] using
      (Fintype.prod_sum (fun (_ : ZMod 5) (j : Fin (2*n+1)) => (X : PowerSeries ℚ) ^ (j:ℕ)))
  rw [Nat.card_congr (neckShift n), Nat.card_eq_fintype_card, Fintype.card_subtype,
    hpow, map_sum]
  simp [coeff_X_pow, eq_comm]


lemma neck_choose4 (k : ℕ) :
    ((k+4).choose 4 : ℚ) = (k+1)*(k+2)*(k+3)*(k+4)/24 := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose k 4
  norm_num [Nat.ascFactorial, Nat.factorial] at h
  have hQ : ((k:ℚ)+1)*((k:ℚ)+2)*((k:ℚ)+3)*((k:ℚ)+4) = 24*((k+4).choose 4 : ℚ) := by
    exact_mod_cast (show (k+1)*(k+2)*(k+3)*(k+4) = 24*(k+4).choose 4 by
      rw [← h]; ring)
  linarith

lemma neck_total (n : ℕ) : (Nat.card (Lab n) : ℚ) =
    (115*(n:ℚ)^4 + 230*(n:ℚ)^3 + 185*(n:ℚ)^2 + 70*(n:ℚ) + 12)/12 := by
  rw [neck_coeff]
  let k := 2*n+1
  let P := ∑ j : Fin k, (X : PowerSeries ℚ) ^ (j:ℕ)
  let G := (mk 1 : PowerSeries ℚ)
  let F := G ^ 5
  have hg : P * (1-X) = 1-X^k := by
    dsimp [P]
    rw [Fin.sum_univ_eq_sum_range (fun j => (X : PowerSeries ℚ)^j)]
    exact geom_sum_mul_neg X k
  have hP : P = G * (1-X^k) := by
    rw [← hg, mul_left_comm, mk_one_mul_one_sub_eq_one, mul_one]
  have hm : P ^ 5 = F - 5 • (F * X^k) + 10 • (F * X^(k*2)) - 10 • (F * X^(k*3))
      + 5 • (F * X^(k*4)) - F * X^(k*5) := by
    rw [hP]
    dsimp only [F]
    simp only [pow_mul, nsmul_eq_mul]
    ring
  have hF (d : ℕ) : coeff d F = ((d+4).choose 4 : ℚ) := by
    change coeff d ((mk 1 : PowerSeries ℚ)^(4+1)) = _
    rw [mk_one_pow_eq_mk_choose_add, coeff_mk, Nat.add_comm]
  change coeff (5*n) (P^5) = _
  rw [hm]
  simp only [map_sub, map_add, map_nsmul, coeff_mul_X_pow', hF]
  dsimp [k]
  rcases n with _ | _ | t
  · norm_num [Nat.choose]
  · norm_num [Nat.choose]
  · have hsub1 : 5*(t+2) - (2*(t+2)+1) = 3*t+5 := by omega
    have hsub2 : 5*(t+2) - (2*(t+2)+1)*2 = t := by omega

    simp (disch := omega) only [if_pos, if_neg,
      show t+1+1 = t+2 from rfl, hsub1, hsub2, neck_choose4]
    push_cast
    ring
end

-- A reflection fixes the labelings (-2s, b, s-b, s-b, b). Count the allowed b for each s.
section
open OMA.S_oeis_a208826 Finset

lemma neck_sum5 (f : ZMod 5 → ℤ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [show (Finset.univ : Finset (ZMod 5)) = {0,1,2,3,4} by decide]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  ring

abbrev NeckBand (n : ℕ) :=
  Σ s : Finset.Icc (-((n : ℤ) / 2)) ((n : ℤ) / 2),
    Finset.Icc (max (-(n : ℤ)) (s.val - n)) (min (n : ℤ) (s.val + n))

def neckBandEquiv (n : ℕ) : NeckFixed n ≃ NeckBand n where
  toFun f := by
    let w := f.1.1
    have hsum := f.1.2.2
    rw [neck_sum5] at hsum
    have h4 : w 4 = w 1 := by simpa only [show -(4 : ZMod 5) = 1 by decide] using f.2 4
    have h3 : w 3 = w 2 := by simpa only [show -(3 : ZMod 5) = 2 by decide] using f.2 3
    change w 0 + w 1 + w 2 + w 3 + w 4 = 0 at hsum
    have b0 := abs_le.mp (f.1.2.1 0)
    have b1 := abs_le.mp (f.1.2.1 1)
    have b2 := abs_le.mp (f.1.2.1 2)
    change -(n:ℤ) ≤ w 0 ∧ w 0 ≤ n at b0
    change -(n:ℤ) ≤ w 1 ∧ w 1 ≤ n at b1
    change -(n:ℤ) ≤ w 2 ∧ w 2 ≤ n at b2
    refine ⟨⟨w 1 + w 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩,
      ⟨w 1, Finset.mem_Icc.mpr ⟨max_le (by omega) (by dsimp; omega),
        le_min (by omega) (by dsimp; omega)⟩⟩⟩
  invFun z := by
    let s := z.1.val
    let b := z.2.val
    let w : ZMod 5 → ℤ := fun i =>
      if i = 0 then -2*s else if i = 1 ∨ i = 4 then b else s-b
    have h := Finset.mem_Icc.mp z.1.property
    have j := Finset.mem_Icc.mp z.2.property
    change -((n:ℤ) / 2) ≤ s ∧ s ≤ (n:ℤ) / 2 at h
    change max (-(n:ℤ)) (s-n) ≤ b ∧ b ≤ min (n:ℤ) (s+n) at j
    simp only [max_le_iff, le_min_iff] at j
    refine ⟨⟨w, ?_, ?_⟩, ?_⟩
    · intro i
      apply abs_le.mpr
      dsimp only [w]
      split_ifs <;> constructor <;> omega
    · rw [neck_sum5]
      change -2*s + b + (s-b) + (s-b) + b = 0
      ring
    · intro i
      fin_cases i <;> rfl
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have h := f.1.2.2
    rw [neck_sum5] at h
    have h4 : f.1.1 4 = f.1.1 1 := f.2 4
    have h3 : f.1.1 3 = f.1.1 2 := f.2 3
    have hall : ∀ i : ZMod 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
    rcases hall i with h | h | h | h | h <;> subst i
    · change -2 * (f.1.1 1 + f.1.1 2) = f.1.1 0
      omega
    · rfl
    · change f.1.1 1 + f.1.1 2 - f.1.1 1 = f.1.1 2
      omega
    · change f.1.1 1 + f.1.1 2 - f.1.1 1 = f.1.1 3
      omega
    · exact h4.symm
  right_inv z := by
    have coords (p q : NeckBand n) (hs : p.1.val = q.1.val) (hb : p.2.val = q.2.val) : p = q := by
      rcases p with ⟨⟨s, _⟩, ⟨b, _⟩⟩
      rcases q with ⟨⟨t, _⟩, ⟨c, _⟩⟩
      change s = t at hs
      change b = c at hb
      subst t
      subst c
      rfl
    apply coords
    · change z.2.val + (z.1.val - z.2.val) = z.1.val
      omega
    · rfl

lemma neck_symmetric_sum (w : ℤ) (h : ℕ) :
    ∑ s ∈ Icc (-(h:ℤ)) (h:ℤ), (w - |s|) =
      (2*(h:ℤ)+1)*w - (h:ℤ)*(h+1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hset : Icc (-((h:ℤ)+1)) ((h:ℤ)+1) =
        insert (-((h:ℤ)+1)) (insert ((h:ℤ)+1) (Icc (-(h:ℤ)) (h:ℤ))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    push_cast
    rw [hset, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih]
    rw [abs_neg, abs_of_nonneg (show 0 ≤ (h:ℤ)+1 by omega)]
    ring

lemma neck_reflection (n : ℕ) :
    (Nat.card (NeckFixed n) : ℤ) =
      (2*((n:ℤ)/2)+1)*(2*(n:ℤ)+1) - ((n:ℤ)/2)*((n:ℤ)/2+1) := by
  classical
  rw [Nat.card_congr (neckBandEquiv n)]
  change (Nat.card (Σ s : Icc (-((n:ℤ)/2)) ((n:ℤ)/2),
    Icc (max (-(n:ℤ)) (s.val-n)) (min (n:ℤ) (s.val+n))) : ℤ) = _
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_coe, Nat.cast_sum]
  have hx : ∀ s ∈ Icc (-((n:ℤ)/2)) ((n:ℤ)/2),
      ((Icc (max (-(n:ℤ)) (s-n)) (min (n:ℤ) (s+n))).card : ℤ) = 2*(n:ℤ)+1-|s| := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.mp hs
    rw [Int.card_Icc_of_le _ _ (by omega)]
    by_cases h : 0 ≤ s
    · rw [abs_of_nonneg h, max_eq_right (by omega), min_eq_left (by omega)]
      ring
    · rw [abs_of_nonpos (by omega), max_eq_left (by omega), min_eq_right (by omega)]
      ring
  simp_rw [fun s : Icc (-((n:ℤ)/2)) ((n:ℤ)/2) => hx s.val s.property]
  rw [Finset.sum_coe_sort (Icc (-((n:ℤ)/2)) ((n:ℤ)/2)) (fun s : ℤ => 2*(n:ℤ)+1-|s|)]
  simpa only [Int.natCast_div, Nat.cast_ofNat] using neck_symmetric_sum (2*(n:ℤ)+1) (n/2)
end

-- Extract coefficients of the claimed power series using the two parity formulas.
section
open OMA.S_oeis_a208826 PowerSeries

lemma neck_gf
    (he : ∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = (23 * n ^ 4 + 46 * n ^ 3 + 58 * n ^ 2 + 44 * n + 24) / 24)
    (ho : ∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = (23 * n ^ 4 + 46 * n ^ 3 + 58 * n ^ 2 + 26 * n + 15) / 24) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((1 - X) ^ 5 * (1 + X) ^ 2 : ℚ⟦X⟧) =
    X * (7 + 24 * X + 27 * X ^ 2 + 30 * X ^ 3 + 5 * X ^ 4 - 2 * X ^ 5 + X ^ 6) := by
  let F := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)
  have hD : F * ((1-X)^5*(1+X)^2) = F - 3 • (F*X^1) + F*X^2 + 5 • (F*X^3) - 5 • (F*X^4) - F*X^5 + 3 • (F*X^6) - F*X^7 := by
    simp only [nsmul_eq_mul]
    ring
  have hN : (X : ℚ⟦X⟧) * (7 + 24 * X + 27 * X ^ 2 + 30 * X ^ 3 + 5 * X ^ 4 - 2 * X ^ 5 + X ^ 6) =
      7 • X^1 + 24 • X^2 + 27 • X^3 + 30 • X^4 + 5 • X^5 - 2 • X^6 + X^7 := by
    simp only [nsmul_eq_mul]
    ring
  change F * _ = _
  rw [hD, hN]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
  by_cases small : n ≤ 7
  · have h1 := ho 1 (by decide) (by decide)
    have h2 := he 2 (by decide) (by decide)
    have h3 := ho 3 (by decide) (by decide)
    have h4 := he 4 (by decide) (by decide)
    have h5 := ho 5 (by decide) (by decide)
    have h6 := he 6 (by decide) (by decide)
    have h7 := ho 7 (by decide) (by decide)
    interval_cases n <;> norm_num [h1,h2,h3,h4,h5,h6,h7]
  · obtain ⟨t, ht⟩ : ∃ t : ℕ, n = 2*t + 8 ∨ n = 2*t + 9 := ⟨(n-8)/2, by omega⟩
    rcases ht with rfl | rfl
    all_goals
      simp (disch := omega) only [if_pos, if_neg]
      simp (disch := first | omega | simp only [Nat.even_iff, Nat.odd_iff]; omega) only [he, ho]
      push_cast
      ring
end

open OMA.S_oeis_a208826

lemma neck_combine (n k : ℕ) (hk : (n : ℤ)/2 = (k : ℤ)) :
    10 * (a n : ℚ) =
      (115*(n:ℚ)^4 + 230*(n:ℚ)^3 + 185*(n:ℚ)^2 + 70*(n:ℚ) + 12)/12 +
        4 + 5 * ((2*(k:ℚ)+1)*(2*(n:ℚ)+1)-(k:ℚ)*(k+1)) := by
  have hr := neck_reflection n
  rw [hk] at hr
  have hrq : (Nat.card (NeckFixed n) : ℚ) =
      (2*(k:ℚ)+1)*(2*(n:ℚ)+1)-(k:ℚ)*(k+1) := by exact_mod_cast hr
  rw [neck_orbit, neck_total, hrq]

lemma neck_even (n : ℕ) (_ : 1 ≤ n) (hn : Even n) :
    (a n : ℚ) = (23 * n ^ 4 + 46 * n ^ 3 + 58 * n ^ 2 + 44 * n + 24) / 24 := by
  obtain ⟨k,rfl⟩ := hn
  have h := neck_combine (k+k) k (by push_cast; omega)
  push_cast at h ⊢
  linear_combination h/10

lemma neck_odd (n : ℕ) (_ : 1 ≤ n) (hn : Odd n) :
    (a n : ℚ) = (23 * n ^ 4 + 46 * n ^ 3 + 58 * n ^ 2 + 26 * n + 15) / 24 := by
  obtain ⟨k,rfl⟩ := hn
  have h := neck_combine (2*k+1) k (by push_cast; omega)
  push_cast at h ⊢
  linear_combination h/10

end Necklace208826

open Necklace208826

theorem OMA.solution : type_of% @OMA.S_oeis_a208826.main :=
  ⟨neck_gf neck_even neck_odd, neck_even, neck_odd⟩
