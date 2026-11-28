import OMAStatements.S_oeis_a168597

-- Problem: A168597: Squares of the central trinomial coefficients (A002426).
-- Upstream: formal-conjectures statements/oeis-a168597.lean:0 (declaration OMA.S_oeis_a168597.main)
-- Credit: @mijuny (the owner of the agent is credited as the solver)

namespace OeisA168597Aux

structure EInt where
  re : ℤ
  im : ℤ

lemma EInt.ext {x y : EInt} (h1 : x.re = y.re) (h2 : x.im = y.im) : x = y := by
  cases x
  cases y
  congr

instance : Zero EInt := ⟨⟨0, 0⟩⟩
instance : One EInt := ⟨⟨1, 0⟩⟩
instance : Add EInt := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg EInt := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub EInt := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance : Mul EInt :=
  ⟨fun x y => ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re - x.im * y.im⟩⟩
instance : NatCast EInt := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast EInt := ⟨fun z => ⟨z, 0⟩⟩

@[simp] lemma EInt.zero_re : (0 : EInt).re = 0 := rfl
@[simp] lemma EInt.zero_im : (0 : EInt).im = 0 := rfl
@[simp] lemma EInt.one_re : (1 : EInt).re = 1 := rfl
@[simp] lemma EInt.one_im : (1 : EInt).im = 0 := rfl
@[simp] lemma EInt.add_re (x y : EInt) : (x + y).re = x.re + y.re := rfl
@[simp] lemma EInt.add_im (x y : EInt) : (x + y).im = x.im + y.im := rfl
@[simp] lemma EInt.neg_re (x : EInt) : (-x).re = -x.re := rfl
@[simp] lemma EInt.neg_im (x : EInt) : (-x).im = -x.im := rfl
@[simp] lemma EInt.sub_re (x y : EInt) : (x - y).re = x.re - y.re := rfl
@[simp] lemma EInt.sub_im (x y : EInt) : (x - y).im = x.im - y.im := rfl
@[simp] lemma EInt.mul_re (x y : EInt) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] lemma EInt.mul_im (x y : EInt) :
    (x * y).im = x.re * y.im + x.im * y.re - x.im * y.im := rfl
@[simp] lemma EInt.natCast_re (n : ℕ) : (n : EInt).re = n := rfl
@[simp] lemma EInt.natCast_im (n : ℕ) : (n : EInt).im = 0 := rfl
@[simp] lemma EInt.intCast_re (z : ℤ) : (z : EInt).re = z := rfl
@[simp] lemma EInt.intCast_im (z : ℤ) : (z : EInt).im = 0 := rfl

instance : CommRing EInt where
  add_assoc := by intros; apply EInt.ext <;> simp <;> ring
  zero_add := by intros; apply EInt.ext <;> simp
  add_zero := by intros; apply EInt.ext <;> simp
  nsmul := nsmulRec
  add_comm := by intros; apply EInt.ext <;> simp <;> ring
  mul_assoc := by intros; apply EInt.ext <;> simp <;> ring
  one_mul := by intros; apply EInt.ext <;> simp
  mul_one := by intros; apply EInt.ext <;> simp
  left_distrib := by intros; apply EInt.ext <;> simp <;> ring
  right_distrib := by intros; apply EInt.ext <;> simp <;> ring
  zero_mul := by intros; apply EInt.ext <;> simp
  mul_zero := by intros; apply EInt.ext <;> simp
  zsmul := zsmulRec
  neg_add_cancel := by intros; apply EInt.ext <;> simp
  sub_eq_add_neg := by intros; apply EInt.ext <;> simp <;> ring
  mul_comm := by intros; apply EInt.ext <;> simp <;> ring
  natCast_zero := by apply EInt.ext <;> simp
  natCast_succ := by intros; apply EInt.ext <;> simp
  intCast_ofNat := by intros; apply EInt.ext <;> simp
  intCast_negSucc := by intros n; apply EInt.ext <;> simp [Int.negSucc_eq]

def omega : EInt := ⟨0, 1⟩

lemma omega_sq_add_omega_add_one : omega ^ 2 + omega + 1 = 0 := by
  rw [pow_two]
  apply EInt.ext <;> simp [omega]

lemma omega_cube : omega ^ 3 = 1 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_two, pow_one]
  apply EInt.ext <;> simp [omega]

lemma omega_pow_mod_three (n : ℕ) : omega ^ n = omega ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3]
  rw [pow_add, pow_mul, omega_cube, one_pow, one_mul]

def conj : EInt →+* EInt where
  toFun x := ⟨x.re - x.im, -x.im⟩
  map_one' := by apply EInt.ext <;> simp
  map_mul' := by intros; apply EInt.ext <;> simp <;> ring
  map_zero' := by apply EInt.ext <;> simp
  map_add' := by intros; apply EInt.ext <;> simp <;> ring

lemma conj_intCast (z : ℤ) : conj (z : EInt) = (z : EInt) := by
  apply EInt.ext <;> simp [conj]

lemma conj_omega : conj omega = omega ^ 2 := by
  rw [pow_two]
  apply EInt.ext <;> simp [conj, omega]

lemma dvd_of_eint_dvd (d z : ℤ) (h : (d : EInt) ∣ (z : EInt)) : d ∣ z := by
  rcases h with ⟨w, hw⟩
  refine ⟨w.re, ?_⟩
  have hr := congrArg EInt.re hw
  simp at hr
  exact hr

lemma coeff_X_add_C_pow_eq (a : EInt) (m k : ℕ) (hk : k ≤ m) :
    ((Polynomial.X + Polynomial.C a) ^ m).coeff k = a ^ (m - k) * (m.choose k : EInt) := by
  rw [add_pow, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [← Polynomial.C_pow, show Polynomial.X ^ k * Polynomial.C (a ^ (m - k)) * (m.choose k : Polynomial EInt) =
        Polynomial.C (a ^ (m - k) * (m.choose k : EInt)) * Polynomial.X ^ k by
          rw [map_mul, map_natCast]; ring]
    rw [Polynomial.coeff_C_mul_X_pow]
    simp
  · intro b _ hbk
    rw [← Polynomial.C_pow, show Polynomial.X ^ b * Polynomial.C (a ^ (m - b)) * (m.choose b : Polynomial EInt) =
        Polynomial.C (a ^ (m - b) * (m.choose b : EInt)) * Polynomial.X ^ b by
          rw [map_mul, map_natCast]; ring]
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hbk)]
  · intro hk'
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hk'

lemma T_eq_eint_sum (m : ℕ) :
    (OMA.S_oeis_a168597.T m : EInt) =
      (-1 : EInt) ^ m * ∑ k ∈ Finset.range (m + 1),
        (((m.choose k : ℤ) ^ 2 : ℤ) : EInt) * omega ^ (m + k) := by
  have hT : (OMA.S_oeis_a168597.T m : EInt) =
      ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial EInt) ^ m).coeff m := by
    unfold OMA.S_oeis_a168597.T
    have hmap := (Polynomial.coeff_map (Int.castRingHom EInt) m
      (p := (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ) ^ m)).symm
    simpa [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X] using hmap
  rw [hT]
  have hfac : (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial EInt) =
      (Polynomial.X + Polynomial.C (-omega)) * (Polynomial.X + Polynomial.C (-(omega ^ 2))) := by
    have h1 : -(omega + omega ^ 2) = 1 := by
      have := omega_sq_add_omega_add_one
      linear_combination -this
    have h2 : omega * omega ^ 2 = 1 := by
      calc omega * omega ^ 2 = omega ^ 3 := by ring
      _ = 1 := omega_cube
    calc (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial EInt)
        = Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C 1 := by simp; ring
      _ = Polynomial.X ^ 2 + Polynomial.C (-(omega + omega ^ 2)) * Polynomial.X +
            Polynomial.C (omega * omega ^ 2) := by rw [h1, h2]
      _ = (Polynomial.X + Polynomial.C (-omega)) * (Polynomial.X + Polynomial.C (-(omega ^ 2))) := by
            simp only [map_neg, map_add, map_mul]
            ring
  rw [hfac, mul_pow, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [coeff_X_add_C_pow_eq (-omega) m k hkm,
    coeff_X_add_C_pow_eq (-(omega ^ 2)) m (m - k) (Nat.sub_le m k)]
  rw [Nat.sub_sub_self hkm, Nat.choose_symm hkm]
  have hneg1 : (-omega) ^ (m - k) = (-1 : EInt) ^ (m - k) * omega ^ (m - k) := by
    rw [neg_eq_neg_one_mul, mul_pow]
  have hneg2 : (-(omega ^ 2)) ^ k = (-1 : EInt) ^ k * omega ^ (2 * k) := by
    rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul]
  rw [hneg1, hneg2]
  have hpow1 : (-1 : EInt) ^ (m - k) * (-1 : EInt) ^ k = (-1 : EInt) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hkm]
  have hpow2 : omega ^ (m - k) * omega ^ (2 * k) = omega ^ (m + k) := by
    rw [← pow_add]
    congr 1
    omega
  push_cast
  calc (-1 : EInt) ^ (m - k) * omega ^ (m - k) * (m.choose k : EInt) *
        ((-1 : EInt) ^ k * omega ^ (2 * k) * (m.choose k : EInt))
      = ((-1 : EInt) ^ (m - k) * (-1 : EInt) ^ k) * ((m.choose k : EInt) ^ 2) *
          (omega ^ (m - k) * omega ^ (2 * k)) := by ring
    _ = (-1 : EInt) ^ m * (((m.choose k : EInt) ^ 2) * omega ^ (m + k)) := by
          rw [hpow1, hpow2]; ring

lemma T_eq_eint_sum_mul_prime (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (OMA.S_oeis_a168597.T m : EInt) =
      (-1 : EInt) ^ m * ∑ k ∈ Finset.range (m + 1),
        (((m.choose k : ℤ) ^ 2 : ℤ) : EInt) * omega ^ (p * (m + k)) := by
  have hp3 : ¬ 3 ∣ p := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 3 h with h1 | h2 <;> omega
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · rw [T_eq_eint_sum m]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k _
    congr 1
    rw [pow_mul, omega_pow_mod_three p, h1, pow_one]
  · have hc := congrArg conj (T_eq_eint_sum m)
    rw [conj_intCast, map_mul, map_pow, map_neg, map_one, map_sum] at hc
    rw [hc]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_mul, conj_intCast, map_pow, conj_omega]
    congr 1
    rw [pow_mul, omega_pow_mod_three p, h2]

lemma choose_add_mul_factorial (d b : ℕ) :
    (d + b).choose b * (∏ r ∈ Finset.Icc 1 b, r) = ∏ r ∈ Finset.Icc 1 b, (d + r) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hIcc : Finset.Icc 1 (b + 1) = insert (b + 1) (Finset.Icc 1 b) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : b + 1 ∉ Finset.Icc 1 b := by simp
    rw [hIcc, Finset.prod_insert hnot, Finset.prod_insert hnot]
    have hch : (d + b + 1) * (d + b).choose b = (d + b + 1).choose (b + 1) * (b + 1) := by
      have := Nat.add_one_mul_choose_eq (d + b) b
      simpa [Nat.mul_comm] using this
    calc (d + (b + 1)).choose (b + 1) * ((b + 1) * ∏ r ∈ Finset.Icc 1 b, r)
        = ((d + b + 1).choose (b + 1) * (b + 1)) * ∏ r ∈ Finset.Icc 1 b, r := by
            rw [Nat.add_assoc]; ring
      _ = (d + b + 1) * ((d + b).choose b * ∏ r ∈ Finset.Icc 1 b, r) := by
            rw [← hch]; ring
      _ = (d + (b + 1)) * ∏ r ∈ Finset.Icc 1 b, (d + r) := by
            rw [ih, Nat.add_assoc]

lemma prod_Icc_split_dvd (p i : ℕ) (hp : 0 < p) (f : ℕ → ℕ) :
    (∏ r ∈ Finset.Icc 1 (p * i), f r) =
      (∏ j ∈ Finset.Icc 1 i, f (p * j)) *
        (∏ r ∈ (Finset.range (p * i)).filter (fun r => ¬ p ∣ r), f r) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p * i)) (fun r => p ∣ r)]
  congr 1
  · refine (Finset.prod_bij (fun j _ => p * j) ?_ ?_ ?_ ?_).symm
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
      refine ⟨⟨?_, ?_⟩, dvd_mul_right p j⟩
      · exact Nat.mul_pos hp hj.1
      · exact Nat.mul_le_mul_left p hj.2
    · intro j1 _ j2 _ h
      exact Nat.eq_of_mul_eq_mul_left hp h
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_Icc] at hr
      rcases hr.2 with ⟨j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      simp only [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · by_contra h0
        push_neg at h0
        have : j = 0 := by omega
        subst this
        omega
      · exact Nat.le_of_mul_le_mul_left hr.1.2 hp
    · intro j _
      rfl
  · congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hr2⟩, hnd⟩
      refine ⟨?_, hnd⟩
      rcases lt_or_eq_of_le hr2 with hlt | rfl
      · exact hlt
      · exact absurd (dvd_mul_right p i) hnd
    · rintro ⟨hr, hnd⟩
      refine ⟨⟨?_, le_of_lt hr⟩, hnd⟩
      by_contra h0
      push_neg at h0
      have : r = 0 := by omega
      subst this
      exact hnd (dvd_zero p)

lemma choose_mul_prod_nonmult (p m i : ℕ) (hp : 0 < p) (hi : i ≤ m) :
    (p * m).choose (p * i) * (∏ r ∈ (Finset.range (p * i)).filter (fun r => ¬ p ∣ r), r) =
      m.choose i * (∏ r ∈ (Finset.range (p * i)).filter (fun r => ¬ p ∣ r), (p * (m - i) + r)) := by
  set S := (Finset.range (p * i)).filter (fun r => ¬ p ∣ r)
  have h1 := choose_add_mul_factorial (p * (m - i)) (p * i)
  have hpm : p * (m - i) + p * i = p * m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hi]
  rw [hpm] at h1
  rw [prod_Icc_split_dvd p i hp (fun r => r),
    prod_Icc_split_dvd p i hp (fun r => p * (m - i) + r)] at h1
  have hmul1 : (∏ j ∈ Finset.Icc 1 i, (p * j)) = p ^ i * ∏ j ∈ Finset.Icc 1 i, j := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hmul2 : (∏ j ∈ Finset.Icc 1 i, (p * (m - i) + p * j)) =
      p ^ i * ∏ j ∈ Finset.Icc 1 i, ((m - i) + j) := by
    have : ∀ j, p * (m - i) + p * j = p * ((m - i) + j) := fun j => (Nat.mul_add p (m - i) j).symm
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hmul1, hmul2] at h1
  have h2 := choose_add_mul_factorial (m - i) i
  rw [Nat.sub_add_cancel hi] at h2
  rw [← h2] at h1
  have hpos : 0 < p ^ i * ∏ j ∈ Finset.Icc 1 i, j := by
    apply Nat.mul_pos (Nat.pow_pos hp)
    exact Finset.prod_pos (fun j hj => (Finset.mem_Icc.mp hj).1)
  have h3 : (p ^ i * ∏ j ∈ Finset.Icc 1 i, j) * ((p * m).choose (p * i) * ∏ r ∈ S, r) =
      (p ^ i * ∏ j ∈ Finset.Icc 1 i, j) * (m.choose i * ∏ r ∈ S, (p * (m - i) + r)) := by
    calc (p ^ i * ∏ j ∈ Finset.Icc 1 i, j) * ((p * m).choose (p * i) * ∏ r ∈ S, r)
        = (p * m).choose (p * i) * ((p ^ i * ∏ j ∈ Finset.Icc 1 i, j) * ∏ r ∈ S, r) := by ring
      _ = (p ^ i * (m.choose i * ∏ j ∈ Finset.Icc 1 i, j)) * ∏ r ∈ S, (p * (m - i) + r) := h1
      _ = (p ^ i * ∏ j ∈ Finset.Icc 1 i, j) * (m.choose i * ∏ r ∈ S, (p * (m - i) + r)) := by ring
  exact Nat.eq_of_mul_eq_mul_left hpos h3

lemma card_nonmult_even (p i : ℕ) (hp : Odd p) :
    Even ((Finset.range (p * i)).filter (fun r => ¬ p ∣ r)).card := by
  rcases hp with ⟨t, rfl⟩
  have hp0 : 0 < 2 * t + 1 := by omega
  have hpart : ((Finset.range ((2 * t + 1) * i)).filter (fun r => 2 * t + 1 ∣ r)).card +
      ((Finset.range ((2 * t + 1) * i)).filter (fun r => ¬ 2 * t + 1 ∣ r)).card =
        (2 * t + 1) * i := by
    have hunion : (Finset.range ((2 * t + 1) * i)).filter (fun r => 2 * t + 1 ∣ r) ∪
        (Finset.range ((2 * t + 1) * i)).filter (fun r => ¬ 2 * t + 1 ∣ r) =
        Finset.range ((2 * t + 1) * i) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)),
      hunion, Finset.card_range]
  have hmult : ((Finset.range ((2 * t + 1) * i)).filter (fun r => 2 * t + 1 ∣ r)).card = i := by
    have heq : (Finset.range ((2 * t + 1) * i)).filter (fun r => 2 * t + 1 ∣ r) =
        (Finset.range i).image (fun j => (2 * t + 1) * j) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hr, ⟨j, rfl⟩⟩
        exact ⟨j, Nat.lt_of_mul_lt_mul_left hr, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨Nat.mul_lt_mul_of_pos_left hj hp0, dvd_mul_right (2 * t + 1) j⟩
    rw [heq, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp0 h),
      Finset.card_range]
  have hcard : ((Finset.range ((2 * t + 1) * i)).filter (fun r => ¬ 2 * t + 1 ∣ r)).card =
      2 * t * i := by
    have : (2 * t + 1) * i = i + 2 * t * i := by ring
    omega
  rw [hcard]
  exact ⟨t * i, by ring⟩

lemma prod_nonmult_int_flip (p m i : ℕ) (hp : Odd p) (hi : i ≤ m) :
    (∏ r ∈ (Finset.range (p * i)).filter (fun r => ¬ p ∣ r), ((p * (m - i) + r : ℕ) : ℤ)) =
      ∏ r ∈ (Finset.range (p * i)).filter (fun r => ¬ p ∣ r), ((r : ℤ) - (p * m : ℤ)) := by
  set S := (Finset.range (p * i)).filter (fun r => ¬ p ∣ r)
  have hbij : (∏ r ∈ S, ((p * (m - i) + r : ℕ) : ℤ)) =
      ∏ r ∈ S, ((p * (m - i) + (p * i - r) : ℕ) : ℤ) := by
    refine Finset.prod_bij (fun r _ => p * i - r) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [S, Finset.mem_filter, Finset.mem_range] at hr ⊢
      refine ⟨?_, ?_⟩
      · have hr0 : 0 < r := by
          by_contra h0
          have : r = 0 := by omega
          subst this
          exact hr.2 (dvd_zero p)
        omega
      · intro hdvd
        have hsub : p ∣ p * i - (p * i - r) := Nat.dvd_sub (dvd_mul_right p i) hdvd
        rw [Nat.sub_sub_self (le_of_lt hr.1)] at hsub
        exact hr.2 hsub
    · intro r1 hr1 r2 hr2 heq
      simp only [S, Finset.mem_filter, Finset.mem_range] at hr1 hr2
      omega
    · intro r hr
      refine ⟨p * i - r, ?_, ?_⟩
      · simp only [S, Finset.mem_filter, Finset.mem_range] at hr ⊢
        refine ⟨?_, ?_⟩
        · have hr0 : 0 < r := by
            by_contra h0
            have : r = 0 := by omega
            subst this
            exact hr.2 (dvd_zero p)
          omega
        · intro hdvd
          have hsub : p ∣ p * i - (p * i - r) := Nat.dvd_sub (dvd_mul_right p i) hdvd
          rw [Nat.sub_sub_self (le_of_lt hr.1)] at hsub
          exact hr.2 hsub
      · simp only [S, Finset.mem_filter, Finset.mem_range] at hr
        omega
    · intro r hr
      simp only [S, Finset.mem_filter, Finset.mem_range] at hr
      rw [Nat.sub_sub_self (le_of_lt hr.1)]
  rw [hbij]
  have hterm : ∀ r ∈ S, ((p * (m - i) + (p * i - r) : ℕ) : ℤ) = -((r : ℤ) - (p * m : ℤ)) := by
    intro r hr
    simp only [S, Finset.mem_filter, Finset.mem_range] at hr
    have hle : r ≤ p * i := le_of_lt hr.1
    have hnat : p * (m - i) + (p * i - r) + r = p * m := by
      have : p * (m - i) + p * i = p * m := by rw [← Nat.mul_add, Nat.sub_add_cancel hi]
      omega
    omega
  rw [Finset.prod_congr rfl hterm]
  have hneg : (∏ r ∈ S, -((r : ℤ) - (p * m : ℤ))) =
      (-1 : ℤ) ^ S.card * ∏ r ∈ S, ((r : ℤ) - (p * m : ℤ)) := by
    have h1 : ∀ r ∈ S, -((r : ℤ) - (p * m : ℤ)) = (-1 : ℤ) * ((r : ℤ) - (p * m : ℤ)) :=
      fun r _ => by ring
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const]
  rw [hneg, Even.neg_one_pow (card_nonmult_even p i hp), one_mul]

lemma prod_one_sub_mul_sq_zero {α R : Type*} [CommRing R] (s : Finset α) (M : R) (hM : M * M = 0)
    (f : α → R) :
    ∏ x ∈ s, (1 - M * f x) = 1 - M * ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.sum_insert ha]
    calc (1 - M * f a) * (1 - M * ∑ x ∈ s, f x)
        = 1 - M * (f a + ∑ x ∈ s, f x) + (M * M) * (f a * ∑ x ∈ s, f x) := by ring
      _ = 1 - M * (f a + ∑ x ∈ s, f x) := by rw [hM]; ring

lemma zmod_nat_mul_inv {Q r : ℕ} (hcop : Nat.Coprime r Q) :
    (r : ZMod Q) * (r : ZMod Q)⁻¹ = 1 := by
  have hu : IsUnit (r : ZMod Q) := (ZMod.isUnit_iff_coprime r Q).mpr hcop
  exact ZMod.mul_inv_of_unit (r : ZMod Q) hu

lemma choose_mul_prime_sub_dvd (p m k i : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hpm : p ^ k ∣ p * m) (hi : i ≤ m) :
    ((p : ℤ) ^ (2 * k)) ∣ (((p * m).choose (p * i) : ℤ) - (m.choose i : ℤ)) := by
  rcases eq_or_ne i 0 with rfl | hi0
  · simp
  set Q := p ^ (2 * k)
  rw [show (p : ℤ) ^ (2 * k) = (Q : ℤ) by push_cast [Q]; rfl, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hp0 : 0 < p := hp.pos
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  set S := (Finset.range (p * i)).filter (fun r => ¬ p ∣ r)
  have hnat := choose_mul_prod_nonmult p m i hp0 hi
  have hint : (((p * m).choose (p * i) : ℤ)) * (∏ r ∈ S, (r : ℤ)) =
      (m.choose i : ℤ) * (∏ r ∈ S, ((r : ℤ) - (p * m : ℤ))) := by
    have hc : ((((p * m).choose (p * i) * ∏ r ∈ S, r : ℕ) : ℤ)) =
        (((m.choose i * ∏ r ∈ S, (p * (m - i) + r) : ℕ) : ℤ)) := by exact_mod_cast hnat
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at hc
    rw [prod_nonmult_int_flip p m i hpOdd hi] at hc
    exact hc
  have hz : (((p * m).choose (p * i) : ℤ) : ZMod Q) * (∏ r ∈ S, (r : ZMod Q)) =
      ((m.choose i : ℤ) : ZMod Q) * (∏ r ∈ S, ((r : ZMod Q) - ((p * m : ℕ) : ZMod Q))) := by
    have := congrArg (Int.castRingHom (ZMod Q)) hint
    simpa [map_mul, map_prod, map_sub] using this
  set M : ZMod Q := ((p * m : ℕ) : ZMod Q)
  have hM2 : M * M = 0 := by
    have hdvd : Q ∣ (p * m) * (p * m) := by
      have : Q = p ^ k * p ^ k := by dsimp [Q]; rw [two_mul, pow_add]
      rw [this]
      exact Nat.mul_dvd_mul hpm hpm
    have h0 : (((p * m) * (p * m) : ℕ) : ZMod Q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    simpa [M] using h0
  have hcopS : ∀ r ∈ S, Nat.Coprime r Q := by
    intro r hr
    have hnd : ¬ p ∣ r := (Finset.mem_filter.mp hr).2
    exact (hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right (2 * k)
  have hprod : (∏ r ∈ S, ((r : ZMod Q) - M)) =
      (∏ r ∈ S, (r : ZMod Q)) * (1 - M * ∑ r ∈ S, (r : ZMod Q)⁻¹) := by
    rw [← prod_one_sub_mul_sq_zero S M hM2 (fun r => (r : ZMod Q)⁻¹), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro r hr
    have hinv := zmod_nat_mul_inv (hcopS r hr)
    calc (r : ZMod Q) - M = (r : ZMod Q) - M * ((r : ZMod Q) * (r : ZMod Q)⁻¹) := by rw [hinv, mul_one]
      _ = (r : ZMod Q) * (1 - M * (r : ZMod Q)⁻¹) := by ring
  rw [hprod] at hz
  have hDunit : IsUnit (∏ r ∈ S, (r : ZMod Q)) := by
    rw [IsUnit.prod_iff]
    intro r hr
    exact (ZMod.isUnit_iff_coprime r Q).mpr (hcopS r hr)
  have hz' : (((p * m).choose (p * i) : ℤ) : ZMod Q) =
      ((m.choose i : ℤ) : ZMod Q) * (1 - M * ∑ r ∈ S, (r : ZMod Q)⁻¹) := by
    have hmul : (((p * m).choose (p * i) : ℤ) : ZMod Q) * (∏ r ∈ S, (r : ZMod Q)) =
        (((m.choose i : ℤ) : ZMod Q) * (1 - M * ∑ r ∈ S, (r : ZMod Q)⁻¹)) *
          (∏ r ∈ S, (r : ZMod Q)) := by
      calc (((p * m).choose (p * i) : ℤ) : ZMod Q) * (∏ r ∈ S, (r : ZMod Q))
          = ((m.choose i : ℤ) : ZMod Q) *
              ((∏ r ∈ S, (r : ZMod Q)) * (1 - M * ∑ r ∈ S, (r : ZMod Q)⁻¹)) := hz
        _ = (((m.choose i : ℤ) : ZMod Q) * (1 - M * ∑ r ∈ S, (r : ZMod Q)⁻¹)) *
              (∏ r ∈ S, (r : ZMod Q)) := by ring
    exact hDunit.mul_right_cancel hmul
  have hsum2 : (2 : ZMod Q) * (∑ r ∈ S, (r : ZMod Q)⁻¹) =
      ((p * i : ℕ) : ZMod Q) *
        ∑ r ∈ S, (r : ZMod Q)⁻¹ * ((p * i - r : ℕ) : ZMod Q)⁻¹ := by
    have hflip : (∑ r ∈ S, (r : ZMod Q)⁻¹) = ∑ r ∈ S, ((p * i - r : ℕ) : ZMod Q)⁻¹ := by
      refine Finset.sum_bij (fun r _ => p * i - r) ?_ ?_ ?_ ?_
      · intro r hr
        simp only [S, Finset.mem_filter, Finset.mem_range] at hr ⊢
        refine ⟨?_, ?_⟩
        · have hr0 : 0 < r := by
            by_contra h0; have : r = 0 := by omega
            subst this; exact hr.2 (dvd_zero p)
          omega
        · intro hdvd
          have hsub : p ∣ p * i - (p * i - r) := Nat.dvd_sub (dvd_mul_right p i) hdvd
          rw [Nat.sub_sub_self (le_of_lt hr.1)] at hsub
          exact hr.2 hsub
      · intro r1 hr1 r2 hr2 heq
        simp only [S, Finset.mem_filter, Finset.mem_range] at hr1 hr2
        omega
      · intro r hr
        refine ⟨p * i - r, ?_, ?_⟩
        · simp only [S, Finset.mem_filter, Finset.mem_range] at hr ⊢
          refine ⟨?_, ?_⟩
          · have hr0 : 0 < r := by
              by_contra h0; have : r = 0 := by omega
              subst this; exact hr.2 (dvd_zero p)
            omega
          · intro hdvd
            have hsub : p ∣ p * i - (p * i - r) := Nat.dvd_sub (dvd_mul_right p i) hdvd
            rw [Nat.sub_sub_self (le_of_lt hr.1)] at hsub
            exact hr.2 hsub
        · simp only [S, Finset.mem_filter, Finset.mem_range] at hr
          omega
      · intro r hr
        simp only [S, Finset.mem_filter, Finset.mem_range] at hr
        rw [Nat.sub_sub_self (le_of_lt hr.1)]
    calc (2 : ZMod Q) * (∑ r ∈ S, (r : ZMod Q)⁻¹)
        = (∑ r ∈ S, (r : ZMod Q)⁻¹) + (∑ r ∈ S, (r : ZMod Q)⁻¹) := by ring
      _ = (∑ r ∈ S, (r : ZMod Q)⁻¹) + (∑ r ∈ S, ((p * i - r : ℕ) : ZMod Q)⁻¹) := by
            conv_lhs => rhs; rw [hflip]
      _ = ∑ r ∈ S, ((r : ZMod Q)⁻¹ + ((p * i - r : ℕ) : ZMod Q)⁻¹) := by rw [Finset.sum_add_distrib]
      _ = ∑ r ∈ S, (((p * i : ℕ) : ZMod Q) * ((r : ZMod Q)⁻¹ * ((p * i - r : ℕ) : ZMod Q)⁻¹)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            have hle : r ≤ p * i := le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
            have hnd : ¬ p ∣ p * i - r := by
              intro hdvd
              have hsub : p ∣ p * i - (p * i - r) := Nat.dvd_sub (dvd_mul_right p i) hdvd
              rw [Nat.sub_sub_self hle] at hsub
              exact (Finset.mem_filter.mp hr).2 hsub
            have hinv1 := zmod_nat_mul_inv (hcopS r hr)
            have hinv2 := zmod_nat_mul_inv ((hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right (2 * k))
            have hadd : (r : ZMod Q) + ((p * i - r : ℕ) : ZMod Q) = ((p * i : ℕ) : ZMod Q) := by
              rw [← Nat.cast_add, Nat.add_sub_of_le hle]
            calc (r : ZMod Q)⁻¹ + ((p * i - r : ℕ) : ZMod Q)⁻¹
                = (r : ZMod Q)⁻¹ * (((p * i - r : ℕ) : ZMod Q) * ((p * i - r : ℕ) : ZMod Q)⁻¹) +
                    ((r : ZMod Q) * (r : ZMod Q)⁻¹) * ((p * i - r : ℕ) : ZMod Q)⁻¹ := by
                      rw [hinv1, hinv2, mul_one, one_mul]
              _ = ((r : ZMod Q) + ((p * i - r : ℕ) : ZMod Q)) *
                    ((r : ZMod Q)⁻¹ * ((p * i - r : ℕ) : ZMod Q)⁻¹) := by ring
              _ = ((p * i : ℕ) : ZMod Q) * ((r : ZMod Q)⁻¹ * ((p * i - r : ℕ) : ZMod Q)⁻¹) := by
                    rw [hadd]
      _ = ((p * i : ℕ) : ZMod Q) * ∑ r ∈ S, (r : ZMod Q)⁻¹ * ((p * i - r : ℕ) : ZMod Q)⁻¹ := by
            rw [Finset.mul_sum]
  have hch_id : m.choose i * i = m * (m - 1).choose (i - 1) := by
    have hm1 : 1 ≤ m := by omega
    have hi1 : 1 ≤ i := by omega
    have h := Nat.add_one_mul_choose_eq (m - 1) (i - 1)
    rw [Nat.sub_add_cancel hm1, Nat.sub_add_cancel hi1] at h
    exact h.symm
  have h2diff : (2 : ZMod Q) * ((((p * m).choose (p * i) : ℤ) : ZMod Q) - ((m.choose i : ℤ) : ZMod Q)) = 0 := by
    rw [hz']
    have h1 : (2 : ZMod Q) * (((m.choose i : ℤ) : ZMod Q) * (1 - M * ∑ r ∈ S, (r : ZMod Q)⁻¹) -
        ((m.choose i : ℤ) : ZMod Q)) =
        -((m.choose i : ZMod Q) * M * ((2 : ZMod Q) * ∑ r ∈ S, (r : ZMod Q)⁻¹)) := by
      simp only [Int.cast_natCast]
      ring
    rw [h1, hsum2]
    have h2 : (m.choose i : ZMod Q) * M * (((p * i : ℕ) : ZMod Q) *
          ∑ r ∈ S, (r : ZMod Q)⁻¹ * ((p * i - r : ℕ) : ZMod Q)⁻¹) =
        (((m.choose i * i : ℕ) : ZMod Q) * (p : ZMod Q) * M) *
          ∑ r ∈ S, (r : ZMod Q)⁻¹ * ((p * i - r : ℕ) : ZMod Q)⁻¹ := by
      push_cast
      ring
    rw [h2, hch_id]
    have h3 : (((m * (m - 1).choose (i - 1) : ℕ) : ZMod Q) * (p : ZMod Q) * M) =
        (((m - 1).choose (i - 1) : ℕ) : ZMod Q) * (M * M) := by
      simp only [M]
      push_cast
      ring
    rw [h3, hM2, mul_zero, zero_mul, neg_zero]
  have h2unit : IsUnit (2 : ZMod Q) := by
    have hcop2 : Nat.Coprime 2 Q := by
      have hnd2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      have : Nat.Coprime 2 p := (hp.coprime_iff_not_dvd.mpr hnd2).symm
      exact this.pow_right (2 * k)
    exact (ZMod.isUnit_iff_coprime 2 Q).mpr hcop2
  have hdiff0 : (((p * m).choose (p * i) : ℤ) : ZMod Q) - ((m.choose i : ℤ) : ZMod Q) = 0 := by
    apply h2unit.mul_left_cancel
    rw [h2diff, mul_zero]
  exact (sub_eq_zero.mp hdiff0).symm

lemma dvd_choose_of_not_dvd (p m k j : ℕ) (hp : p.Prime) (hpm : p ^ k ∣ p * m) (hj : ¬ p ∣ j) :
    p ^ k ∣ (p * m).choose j := by
  have hj0 : 1 ≤ j := by
    by_contra h0
    have : j = 0 := by omega
    subst this
    exact hj (dvd_zero p)
  rcases lt_or_ge (p * m) j with hlt | hle
  · rw [Nat.choose_eq_zero_of_lt hlt]
    exact dvd_zero _
  have hm1 : 1 ≤ p * m := le_trans hj0 hle
  have hch := Nat.add_one_mul_choose_eq (p * m - 1) (j - 1)
  rw [Nat.sub_add_cancel hm1, Nat.sub_add_cancel hj0] at hch
  have hdvd : p ^ k ∣ (p * m).choose j * j := by
    rw [← hch]
    exact dvd_mul_of_dvd_left hpm _
  have hcop : Nat.Coprime (p ^ k) j := (hp.coprime_iff_not_dvd.mpr hj).pow_left k
  exact hcop.dvd_of_dvd_mul_right hdvd

lemma T_mul_prime_sub_dvd (p m k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hpm : p ^ k ∣ p * m) :
    ((p : ℤ) ^ (2 * k)) ∣ (OMA.S_oeis_a168597.T (p * m) - OMA.S_oeis_a168597.T m) := by
  apply dvd_of_eint_dvd
  rw [Int.cast_sub, T_eq_eint_sum (p * m), T_eq_eint_sum_mul_prime p m hp hp5]
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hsign : (-1 : EInt) ^ (p * m) = (-1 : EInt) ^ m := by
    rw [pow_mul, Odd.neg_one_pow hpOdd]
  rw [hsign, ← mul_sub]
  apply dvd_mul_of_dvd_right
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p * m + 1)) (fun j => p ∣ j)]
  have hmult : (∑ j ∈ (Finset.range (p * m + 1)).filter (fun j => p ∣ j),
      ((((p * m).choose j : ℤ) ^ 2 : ℤ) : EInt) * omega ^ (p * m + j)) =
      ∑ i ∈ Finset.range (m + 1),
        ((((p * m).choose (p * i) : ℤ) ^ 2 : ℤ) : EInt) * omega ^ (p * (m + i)) := by
    refine (Finset.sum_bij (fun i _ => p * i) ?_ ?_ ?_ ?_).symm
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      refine ⟨?_, dvd_mul_right p i⟩
      have : i ≤ m := Nat.le_of_lt_succ hi
      have : p * i ≤ p * m := Nat.mul_le_mul_left p this
      omega
    · intro i1 _ i2 _ h
      exact Nat.eq_of_mul_eq_mul_left hp.pos h
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      rcases hj.2 with ⟨i, rfl⟩
      refine ⟨i, ?_, rfl⟩
      simp only [Finset.mem_range]
      have : p * i ≤ p * m := Nat.le_of_lt_succ hj.1
      have : i ≤ m := Nat.le_of_mul_le_mul_left this hp.pos
      omega
    · intro i _
      rw [Nat.mul_add]
  rw [hmult, add_sub_right_comm, ← Finset.sum_sub_distrib]
  apply dvd_add
  · apply Finset.dvd_sum
    intro i hi
    have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [← sub_mul]
    apply dvd_mul_of_dvd_left
    have hch := choose_mul_prime_sub_dvd p m k i hp (by omega) hpm him
    have hsq : ((p : ℤ) ^ (2 * k)) ∣
        (((p * m).choose (p * i) : ℤ) ^ 2 - (m.choose i : ℤ) ^ 2) := by
      have : ((p * m).choose (p * i) : ℤ) ^ 2 - (m.choose i : ℤ) ^ 2 =
          (((p * m).choose (p * i) : ℤ) - (m.choose i : ℤ)) *
            (((p * m).choose (p * i) : ℤ) + (m.choose i : ℤ)) := by ring
      rw [this]
      exact dvd_mul_of_dvd_left hch _
    rcases hsq with ⟨q, hq⟩
    refine ⟨(q : EInt), ?_⟩
    rw [← Int.cast_sub, hq, Int.cast_mul]
  · apply Finset.dvd_sum
    intro j hj
    have hnd : ¬ p ∣ j := (Finset.mem_filter.mp hj).2
    apply dvd_mul_of_dvd_left
    have hd := dvd_choose_of_not_dvd p m k j hp hpm hnd
    have hsq : ((p : ℤ) ^ (2 * k)) ∣ ((p * m).choose j : ℤ) ^ 2 := by
      rcases hd with ⟨q, hq⟩
      refine ⟨(q : ℤ) ^ 2, ?_⟩
      have hq' : ((p * m).choose j : ℤ) = (p : ℤ) ^ k * (q : ℤ) := by exact_mod_cast hq
      rw [hq', mul_pow, ← pow_mul, Nat.mul_comm k 2]
    rcases hsq with ⟨q, hq⟩
    refine ⟨(q : EInt), ?_⟩
    rw [hq, Int.cast_mul]

end OeisA168597Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a168597.main := by
  intro p n k hp hp5 _ hk
  have hpm_eq : n * p ^ k = p * (n * p ^ (k - 1)) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk1, pow_succ]
    ring
  have hpm_dvd : p ^ k ∣ p * (n * p ^ (k - 1)) := by
    rw [← hpm_eq]
    exact dvd_mul_left (p ^ k) n
  have hT := OeisA168597Aux.T_mul_prime_sub_dvd p (n * p ^ (k - 1)) k hp hp5 hpm_dvd
  rw [← hpm_eq] at hT
  unfold OMA.S_oeis_a168597.a
  have hfac : OMA.S_oeis_a168597.T (n * p ^ k) ^ 2 - OMA.S_oeis_a168597.T (n * p ^ (k - 1)) ^ 2 =
      (OMA.S_oeis_a168597.T (n * p ^ k) - OMA.S_oeis_a168597.T (n * p ^ (k - 1))) *
        (OMA.S_oeis_a168597.T (n * p ^ k) + OMA.S_oeis_a168597.T (n * p ^ (k - 1))) := by ring
  rw [hfac]
  exact dvd_mul_of_dvd_left hT _
