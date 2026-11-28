import OMAReductions.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1

open Finset Polynomial

namespace Erdos494H1

/-- Elementary symmetric polynomial `e_k(S, f)` as the `k`-th coefficient of
`∏ a ∈ S, (1 + C (f a) * X)`. -/
private noncomputable def genPoly {α R : Type*} [CommRing R] (S : Finset α) (f : α → R) :
    Polynomial R :=
  ∏ a ∈ S, (1 + Polynomial.C (f a) * Polynomial.X)

private lemma coeff_genPoly_zero {α R : Type*} [CommRing R] (S : Finset α) (f : α → R) :
    (genPoly S f).coeff 0 = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [genPoly]
  | insert a s ha ih =>
    rw [genPoly, Finset.prod_insert ha, ← genPoly, Polynomial.mul_coeff_zero]
    simp [ih]

private lemma coeff_genPoly_eq_powersetCard {α R : Type*} [CommRing R] [DecidableEq α]
    (S : Finset α) (f : α → R) :
    ∀ k, (genPoly S f).coeff k = ∑ T ∈ S.powersetCard k, ∏ a ∈ T, f a := by
  induction S using Finset.induction_on with
  | empty =>
    intro k
    cases k with
    | zero => simp [genPoly]
    | succ k =>
      have hem : (∅ : Finset α).powersetCard (k + 1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [genPoly, Polynomial.coeff_one, hem]
  | insert a s ha ih =>
    intro k
    rw [genPoly, Finset.prod_insert ha, ← genPoly]
    have hmul : ((1 + Polynomial.C (f a) * Polynomial.X) * genPoly s f).coeff k =
        (genPoly s f).coeff k +
          if k = 0 then 0 else f a * (genPoly s f).coeff (k - 1) := by
      rw [add_mul, one_mul, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul]
      cases k with
      | zero => simp [Polynomial.coeff_X_mul_zero]
      | succ m => simp [Polynomial.coeff_X_mul]
    rw [hmul]
    cases k with
    | zero =>
      simp [ih 0]
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [Finset.powersetCard_succ_insert ha, Finset.sum_union]
      · rw [Finset.sum_image]
        · rw [ih (m + 1), ih m]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T hT
          have haT : a ∉ T := fun h => ha ((Finset.mem_powersetCard.mp hT).1 h)
          rw [Finset.prod_insert haT]
        · intro T₁ hT₁ T₂ hT₂ h
          have ha1 : a ∉ T₁ := fun h1 => ha ((Finset.mem_powersetCard.mp hT₁).1 h1)
          have ha2 : a ∉ T₂ := fun h2 => ha ((Finset.mem_powersetCard.mp hT₂).1 h2)
          have := congrArg (fun u => u.erase a) h
          simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      · rw [Finset.disjoint_left]
        intro T hT hT'
        rcases Finset.mem_image.mp hT' with ⟨U, _, rfl⟩
        exact ha ((Finset.mem_powersetCard.mp hT).1 (Finset.mem_insert_self a U))

private lemma coeff_genPoly_erase {α R : Type*} [CommRing R] [DecidableEq α]
    (S : Finset α) (f : α → R) {a : α} (ha : a ∈ S) :
    ∀ m, (genPoly (S.erase a) f).coeff m =
      ∑ j ∈ Finset.range (m + 1), (-1 : R) ^ j * (f a) ^ j * (genPoly S f).coeff (m - j) := by
  have hprod : genPoly S f = (1 + Polynomial.C (f a) * Polynomial.X) * genPoly (S.erase a) f := by
    rw [genPoly, genPoly, ← Finset.mul_prod_erase S _ ha]
  intro m
  induction m with
  | zero =>
    simp [coeff_genPoly_zero]
  | succ m ih =>
    have hstep : (genPoly S f).coeff (m + 1) =
        (genPoly (S.erase a) f).coeff (m + 1) + f a * (genPoly (S.erase a) f).coeff m := by
      rw [hprod, add_mul, one_mul, Polynomial.coeff_add, mul_assoc,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
    have hcur : (genPoly (S.erase a) f).coeff (m + 1) =
        (genPoly S f).coeff (m + 1) - f a * (genPoly (S.erase a) f).coeff m :=
      eq_sub_of_add_eq hstep.symm
    rw [hcur, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero]
    rw [add_comm _ ((genPoly S f).coeff (m + 1)), sub_eq_add_neg, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ, pow_succ, Nat.succ_sub_succ]
    ring

private lemma derivative_genPoly {α R : Type*} [CommRing R] [DecidableEq α]
    (S : Finset α) (f : α → R) :
    Polynomial.derivative (genPoly S f) =
      ∑ a ∈ S, Polynomial.C (f a) * genPoly (S.erase a) f := by
  induction S using Finset.induction_on with
  | empty => simp [genPoly]
  | insert a s ha ih =>
    rw [genPoly, Finset.prod_insert ha, ← genPoly, Polynomial.derivative_mul, ih,
      Finset.sum_insert ha, Finset.erase_insert ha]
    have hd : Polynomial.derivative (1 + Polynomial.C (f a) * Polynomial.X) = Polynomial.C (f a) := by
      simp
    rw [hd, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := fun h => ha (h ▸ hb)
    have her : (insert a s).erase b = insert a (s.erase b) := Finset.erase_insert_of_ne hba.symm
    have ha' : a ∉ s.erase b := fun h => ha (Finset.mem_of_mem_erase h)
    rw [her]
    dsimp only [genPoly]
    rw [Finset.prod_insert ha']
    ring

/-- Newton's identities for `genPoly S f` in any commutative ring `R`. -/
private lemma newton_identity {α R : Type*} [CommRing R] [DecidableEq α]
    (S : Finset α) (f : α → R) (k : ℕ) (hk : 1 ≤ k) :
    (k : R) * (genPoly S f).coeff k =
      ∑ j ∈ Finset.Icc 1 k, (-1 : R) ^ (j - 1) *
        (∑ a ∈ S, (f a) ^ j) * (genPoly S f).coeff (k - j) := by
  have hderiv := derivative_genPoly S f
  have hcoeff_deriv : (k : R) * (genPoly S f).coeff k =
      (Polynomial.derivative (genPoly S f)).coeff (k - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp [Polynomial.coeff_derivative, mul_comm]
  rw [hcoeff_deriv, hderiv, Polynomial.finsetSum_coeff]
  have hterm : ∀ a ∈ S, (Polynomial.C (f a) * genPoly (S.erase a) f).coeff (k - 1) =
      ∑ j ∈ Finset.Icc 1 k, (-1 : R) ^ (j - 1) * (f a) ^ j * (genPoly S f).coeff (k - j) := by
    intro a ha
    rw [Polynomial.coeff_C_mul, coeff_genPoly_erase S f ha (k - 1), Finset.mul_sum]
    refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j₁ _ j₂ _ h; omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j _
      have hsub : k - 1 - j = k - (j + 1) := by omega
      rw [Nat.add_sub_cancel, hsub, pow_succ]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.sum_mul]

/-- If two finite sets `A, B ⊆ ℂ` of the same cardinality have identical power sums for all `r ≥ 1`,
then `A = B`. -/
private lemma eq_of_power_sums_eq (A B : Finset ℂ) (hcard : A.card = B.card)
    (hpow : ∀ r : ℕ, 1 ≤ r → ∑ a ∈ A, a ^ r = ∑ b ∈ B, b ^ r) : A = B := by
  have hcoeff : ∀ k : ℕ, (genPoly A id).coeff k = (genPoly B id).coeff k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => rw [coeff_genPoly_zero, coeff_genPoly_zero]
      | succ m =>
        have hA := newton_identity A id (m + 1) (by omega)
        have hB := newton_identity B id (m + 1) (by omega)
        have hrhs : ∑ j ∈ Finset.Icc 1 (m + 1), (-1 : ℂ) ^ (j - 1) *
              (∑ a ∈ A, a ^ j) * (genPoly A id).coeff (m + 1 - j) =
            ∑ j ∈ Finset.Icc 1 (m + 1), (-1 : ℂ) ^ (j - 1) *
              (∑ b ∈ B, b ^ j) * (genPoly B id).coeff (m + 1 - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
          rw [hpow j hj1, ih (m + 1 - j) (by omega)]
        have heq : ((m + 1 : ℕ) : ℂ) * (genPoly A id).coeff (m + 1) =
            ((m + 1 : ℕ) : ℂ) * (genPoly B id).coeff (m + 1) := by
          simpa [id] using hA.trans (hrhs.trans hB.symm)
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (by omega)) heq
  have hpoly : genPoly A id = genPoly B id := Polynomial.ext hcoeff
  have hsub : ∀ X Y : Finset ℂ, genPoly X id = genPoly Y id →
      ∀ x ∈ X, x ≠ 0 → x ∈ Y := by
    intro X Y hXY x hx hx0
    have hev : (genPoly X id).eval (-x⁻¹) = 0 := by
      rw [genPoly, Polynomial.eval_prod]
      exact Finset.prod_eq_zero hx (by simp [hx0])
    rw [hXY, genPoly, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hev
    rcases hev with ⟨y, hy, hy0⟩
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, id] at hy0
    have hyx : y = x := by
      have h1 : y * (-x⁻¹) = -1 := eq_neg_of_add_eq_zero_right hy0
      have h2 : y * x⁻¹ = 1 := by linear_combination -h1
      calc y = y * x⁻¹ * x := by rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one]
        _ = 1 * x := by rw [h2]
        _ = x := one_mul x
    exact hyx ▸ hy
  have hnonzero : A.erase 0 = B.erase 0 := by
    ext x
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨hx0, hxA⟩; exact ⟨hx0, hsub A B hpoly x hxA hx0⟩
    · rintro ⟨hx0, hxB⟩; exact ⟨hx0, hsub B A hpoly.symm x hxB hx0⟩
  by_cases h0A : (0 : ℂ) ∈ A
  · have h0B : (0 : ℂ) ∈ B := by
      by_contra h0B
      have h1 : (A.erase 0).card + 1 = A.card := Finset.card_erase_add_one h0A
      have h2 : (B.erase 0).card = B.card := by rw [Finset.erase_eq_of_notMem h0B]
      rw [hnonzero, h2, hcard] at h1
      omega
    rw [← Finset.insert_erase h0A, ← Finset.insert_erase h0B, hnonzero]
  · have h0B : (0 : ℂ) ∉ B := by
      intro h0B
      have h1 : (A.erase 0).card = A.card := by rw [Finset.erase_eq_of_notMem h0A]
      have h2 : (B.erase 0).card + 1 = B.card := Finset.card_erase_add_one h0B
      rw [← hnonzero, h1, hcard] at h2
      omega
    rw [← Finset.erase_eq_of_notMem h0A, ← Finset.erase_eq_of_notMem h0B, hnonzero]

/-- Truncated exponential polynomial `∑_{m=0}^r (c^m / m!) * Y^m ∈ ℂ[Y]`. -/
private noncomputable def truncExp (r : ℕ) (c : ℂ) : Polynomial ℂ :=
  ∑ m ∈ Finset.range (r + 1), Polynomial.C (c ^ m / (m.factorial : ℂ)) * Polynomial.X ^ m

private lemma coeff_truncExp (r : ℕ) (c : ℂ) {m : ℕ} (hm : m ≤ r) :
    (truncExp r c).coeff m = c ^ m / (m.factorial : ℂ) := by
  rw [truncExp, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
  · intro j _ hjm
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hjm.symm, mul_zero]
  · intro hm'
    exact absurd (Finset.mem_range.mpr (by omega)) hm'

private lemma coeff_truncExp_mul (r : ℕ) (c₁ c₂ : ℂ) {m : ℕ} (hm : m ≤ r) :
    (truncExp r c₁ * truncExp r c₂).coeff m = (truncExp r (c₁ + c₂)).coeff m := by
  rw [Polynomial.coeff_mul, coeff_truncExp r (c₁ + c₂) hm,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => (truncExp r c₁).coeff a * (truncExp r c₂).coeff b)]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (truncExp r c₁).coeff j * (truncExp r c₂).coeff (m - j) =
        ((m.choose j : ℂ) * c₁ ^ j * c₂ ^ (m - j)) / (m.factorial : ℂ) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [coeff_truncExp r c₁ (hjm.trans hm), coeff_truncExp r c₂ (by omega)]
    have hfac : (m.choose j : ℂ) * (j.factorial : ℂ) * ((m - j).factorial : ℂ) = (m.factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjm
    have hfj : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hfmj : ((m - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - j))
    have hfm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    field_simp [hfj, hfmj, hfm]
    linear_combination c₁ ^ j * c₂ ^ (m - j) * hfac.symm
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, add_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma coeff_prod_truncExp (r : ℕ) (T : Finset ℂ) :
    ∀ m ≤ r, (∏ a ∈ T, truncExp r a).coeff m = (∑ a ∈ T, a) ^ m / (m.factorial : ℂ) := by
  induction T using Finset.induction_on with
  | empty =>
    intro m hm
    cases m with
    | zero => simp
    | succ m => simp [Polynomial.coeff_one, zero_pow (Nat.succ_ne_zero m)]
  | insert a s ha ih =>
    intro m hm
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => (truncExp r a).coeff x * (∏ b ∈ s, truncExp r b).coeff y)]
    have h1 : ∑ j ∈ Finset.range (m + 1),
        (truncExp r a).coeff j * (∏ b ∈ s, truncExp r b).coeff (m - j) =
        ∑ j ∈ Finset.range (m + 1),
          (truncExp r a).coeff j * (truncExp r (∑ b ∈ s, b)).coeff (m - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [ih (m - j) (by omega), ← coeff_truncExp r _ (by omega)]
    rw [h1, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => (truncExp r a).coeff x * (truncExp r (∑ b ∈ s, b)).coeff y),
      ← Polynomial.coeff_mul, coeff_truncExp_mul r a (∑ b ∈ s, b) hm, coeff_truncExp r _ hm]

private lemma coeff_pow_truncExp (r : ℕ) (a : ℂ) (j : ℕ) :
    ∀ m ≤ r, ((truncExp r a) ^ j).coeff m = ((j : ℂ) * a) ^ m / (m.factorial : ℂ) := by
  induction j with
  | zero =>
    intro m _
    cases m with
    | zero => simp
    | succ m => simp [Polynomial.coeff_one, zero_pow (Nat.succ_ne_zero m)]
  | succ j ih =>
    intro m hm
    rw [pow_succ, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => ((truncExp r a) ^ j).coeff x * (truncExp r a).coeff y)]
    have h1 : ∑ l ∈ Finset.range (m + 1),
        ((truncExp r a) ^ j).coeff l * (truncExp r a).coeff (m - l) =
        ∑ l ∈ Finset.range (m + 1),
          (truncExp r ((j : ℂ) * a)).coeff l * (truncExp r a).coeff (m - l) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlm : l ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      rw [ih l (hlm.trans hm), ← coeff_truncExp r _ (hlm.trans hm)]
    rw [h1, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => (truncExp r ((j : ℂ) * a)).coeff x * (truncExp r a).coeff y),
      ← Polynomial.coeff_mul, coeff_truncExp_mul r ((j : ℂ) * a) a hm, coeff_truncExp r _ hm]
    push_cast
    ring_nf

private lemma coeff_one_add_X_pow (n m : ℕ) :
    ((1 + Polynomial.X : Polynomial ℂ) ^ n).coeff m = (Nat.choose n m : ℂ) := by
  induction n generalizing m with
  | zero =>
    cases m <;> simp [Polynomial.coeff_one]
  | succ n ih =>
    rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add]
    cases m with
    | zero => simp [Polynomial.coeff_mul_X_zero, ih 0]
    | succ m =>
      rw [Polynomial.coeff_mul_X]
      simp only [Nat.choose_succ_succ, Nat.cast_add, ih (m + 1), ih m, add_comm]

/-- Pure polynomial identity driving the explicit closed form for the degree-`r` difference. -/
private lemma coeff_binom_power_recurrence (n r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    let F : ℕ → ℂ := fun m =>
      ∑ i ∈ Finset.Icc 1 m, (-1 : ℂ) ^ (i - 1) * (Nat.choose n (m - i) : ℂ) * (i : ℂ) ^ (r - 1)
    (k : ℂ) * F k =
      ∑ j ∈ Finset.Icc 1 k, (-1 : ℂ) ^ (j - 1) * (Nat.choose n (k - j) : ℂ) * (j : ℂ) ^ r +
      (n : ℂ) * ∑ j ∈ Finset.Icc 1 k, (-1 : ℂ) ^ (j - 1) * F (k - j) := by
  intro F
  let f : Polynomial ℂ :=
    ∑ i ∈ Finset.Icc 1 k, Polynomial.C ((-1 : ℂ) ^ (i - 1) * (i : ℂ) ^ (r - 1)) * Polynomial.X ^ i
  let G : Polynomial ℂ := (1 + Polynomial.X) ^ n * f
  let H : Polynomial ℂ :=
    Polynomial.X * Polynomial.derivative G -
      (1 + Polynomial.X) ^ n * (Polynomial.X * Polynomial.derivative f)
  have hF_coeff : ∀ m ≤ k, G.coeff m = F m := by
    intro m hm
    dsimp only [G, f, F]
    rw [Finset.mul_sum, Polynomial.finset_sum_coeff]
    have hterm : ∀ i ∈ Finset.Icc 1 k,
        ((1 + Polynomial.X) ^ n *
          (Polynomial.C ((-1 : ℂ) ^ (i - 1) * (i : ℂ) ^ (r - 1)) * Polynomial.X ^ i)).coeff m =
        if i ≤ m then (-1 : ℂ) ^ (i - 1) * (Nat.choose n (m - i) : ℂ) * (i : ℂ) ^ (r - 1) else 0 := by
      intro i _
      rw [← mul_assoc, mul_comm ((1 + Polynomial.X) ^ n), mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_mul_X_pow']
      split_ifs with him
      · rw [coeff_one_add_X_pow]
        ring
      · simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hH_rel : (1 + Polynomial.X) * H = Polynomial.C (n : ℂ) * Polynomial.X * G := by
    dsimp only [H, G]
    have hprod : (1 + Polynomial.X : Polynomial ℂ) *
        Polynomial.derivative ((1 + Polynomial.X : Polynomial ℂ) ^ n) =
        Polynomial.C (n : ℂ) * (1 + Polynomial.X) ^ n := by
      cases n with
      | zero => simp
      | succ n' =>
        rw [Polynomial.derivative_pow, Polynomial.derivative_add, Polynomial.derivative_one,
          Polynomial.derivative_X, zero_add, mul_one]
        simp only [Polynomial.C_eq_natCast, Nat.add_sub_cancel]
        rw [pow_succ]
        ring
    rw [Polynomial.derivative_mul]
    calc (1 + Polynomial.X) * (Polynomial.X *
            (Polynomial.derivative ((1 + Polynomial.X) ^ n) * f +
              (1 + Polynomial.X) ^ n * Polynomial.derivative f) -
            (1 + Polynomial.X) ^ n * (Polynomial.X * Polynomial.derivative f))
        = Polynomial.X * ((1 + Polynomial.X) * Polynomial.derivative ((1 + Polynomial.X) ^ n)) * f := by
          ring
      _ = Polynomial.X * (Polynomial.C (n : ℂ) * (1 + Polynomial.X) ^ n) * f := by rw [hprod]
      _ = Polynomial.C (n : ℂ) * Polynomial.X * ((1 + Polynomial.X) ^ n * f) := by ring
  have hH_coeff : ∀ m ≤ k, H.coeff m =
      (n : ℂ) * ∑ j ∈ Finset.Icc 1 m, (-1 : ℂ) ^ (j - 1) * F (m - j) := by
    intro m hm
    induction m with
    | zero =>
      simp [H, Polynomial.coeff_X_mul_zero]
    | succ m ih =>
      have hrel := congrArg (fun P => P.coeff (m + 1)) hH_rel
      rw [add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
        mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul] at hrel
      have hcur : H.coeff (m + 1) = (n : ℂ) * G.coeff m - H.coeff m :=
        eq_sub_of_add_eq hrel
      rw [hcur, hF_coeff m (by omega), ih (by omega)]
      have hsplit : Finset.Icc 1 (m + 1) = insert 1 ((Finset.Icc 1 m).image (fun j => j + 1)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_image]
        constructor
        · intro ⟨hx1, hxm⟩
          by_cases h1 : x = 1
          · exact Or.inl h1
          · exact Or.inr ⟨x - 1, ⟨by omega, by omega⟩, by omega⟩
        · rintro (rfl | ⟨y, ⟨hy1, hym⟩, rfl⟩) <;> omega
      rw [hsplit, Finset.sum_insert (by simp), Finset.sum_image (by intro a _ b _ h; exact Nat.succ.inj h)]
      simp only [Nat.sub_self, pow_zero, one_mul, Nat.add_sub_cancel]
      rw [mul_add, sub_eq_add_neg, ← mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      simp only [Nat.succ_sub_succ, Nat.sub_zero, Nat.succ_eq_add_one]
      rw [pow_succ, add_comm j' 1]
      ring
  have hH_k := hH_coeff k le_rfl
  have hLHS : (Polynomial.X * Polynomial.derivative G).coeff k = (k : ℂ) * F k := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, hF_coeff (m + 1) le_rfl, mul_comm]
    push_cast
    rfl
  have hRHS1 : ((1 + Polynomial.X) ^ n * (Polynomial.X * Polynomial.derivative f)).coeff k =
      ∑ j ∈ Finset.Icc 1 k, (-1 : ℂ) ^ (j - 1) * (Nat.choose n (k - j) : ℂ) * (j : ℂ) ^ r := by
    have hdf : Polynomial.X * Polynomial.derivative f =
        ∑ j ∈ Finset.Icc 1 k, Polynomial.C ((-1 : ℂ) ^ (j - 1) * (j : ℂ) ^ r) * Polynomial.X ^ j := by
      dsimp only [f]
      rw [Polynomial.derivative_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      rw [Polynomial.derivative_C_mul_X_pow]
      have hpow : (j : ℂ) ^ (r - 1) * (j : ℂ) = (j : ℂ) ^ r := by
        obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
        simp [pow_succ]
      have hX : Polynomial.X * Polynomial.X ^ (j - 1) = (Polynomial.X : Polynomial ℂ) ^ j := by
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        simp [pow_succ, mul_comm]
      calc Polynomial.X * (Polynomial.C ((-1 : ℂ) ^ (j - 1) * (j : ℂ) ^ (r - 1) * (j : ℂ)) *
              Polynomial.X ^ (j - 1))
          = Polynomial.C ((-1 : ℂ) ^ (j - 1) * ((j : ℂ) ^ (r - 1) * (j : ℂ))) *
              (Polynomial.X * Polynomial.X ^ (j - 1)) := by ring
        _ = Polynomial.C ((-1 : ℂ) ^ (j - 1) * (j : ℂ) ^ r) * Polynomial.X ^ j := by rw [hpow, hX]
    rw [hdf, Finset.mul_sum, Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
    rw [← mul_assoc, mul_comm ((1 + Polynomial.X) ^ n), mul_assoc, Polynomial.coeff_C_mul,
      Polynomial.coeff_mul_X_pow', if_pos hjk]
    rw [coeff_one_add_X_pow]
    ring
  have hsub_eq : H.coeff k = (Polynomial.X * Polynomial.derivative G).coeff k -
      ((1 + Polynomial.X) ^ n * (Polynomial.X * Polynomial.derivative f)).coeff k :=
    Polynomial.coeff_sub _ _ k
  rw [hLHS, hRHS1] at hsub_eq
  linear_combination hH_k - hsub_eq

end Erdos494H1

theorem OMA.solution : OMA.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1.H1 := by
  intro s n hs hsn hnot
  unfold Erdos494.Erdos494Unique at hnot
  push_neg at hnot
  rcases hnot with ⟨A, B, hAcard, hBcard, hsum, hAB⟩
  have hex : ∃ r : ℕ, 1 ≤ r ∧ ∑ a ∈ A, a ^ r ≠ ∑ b ∈ B, b ^ r := by
    by_contra hall
    push_neg at hall
    exact hAB (Erdos494H1.eq_of_power_sums_eq A B (hAcard.trans hBcard.symm) hall)
  classical
  let r := Nat.find hex
  have hr_spec : 1 ≤ r ∧ ∑ a ∈ A, a ^ r ≠ ∑ b ∈ B, b ^ r := Nat.find_spec hex
  have hr1 : 1 ≤ r := hr_spec.1
  have hr_ne : ∑ a ∈ A, a ^ r ≠ ∑ b ∈ B, b ^ r := hr_spec.2
  have hlt : ∀ m < r, ∑ a ∈ A, a ^ m = ∑ b ∈ B, b ^ m := by
    intro m hm
    cases m with
    | zero => simp [hAcard, hBcard]
    | succ m' =>
      by_contra hne
      exact Nat.find_min hex hm ⟨by omega, hne⟩
  let eA := Erdos494H1.genPoly A (Erdos494H1.truncExp r)
  let eB := Erdos494H1.genPoly B (Erdos494H1.truncExp r)
  have heA0 : ∀ k, (eA.coeff k).coeff 0 = (Nat.choose n k : ℂ) := by
    intro k
    rw [Erdos494H1.coeff_genPoly_eq_powersetCard, Polynomial.finset_sum_coeff]
    have h1 : ∀ T ∈ A.powersetCard k, (∏ a ∈ T, Erdos494H1.truncExp r a).coeff 0 = 1 := by
      intro T _
      rw [Erdos494H1.coeff_prod_truncExp r T 0 (Nat.zero_le r)]
      simp
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_powersetCard, hAcard, nsmul_eq_mul, mul_one]
  have heB0 : ∀ k, (eB.coeff k).coeff 0 = (Nat.choose n k : ℂ) := by
    intro k
    rw [Erdos494H1.coeff_genPoly_eq_powersetCard, Polynomial.finset_sum_coeff]
    have h1 : ∀ T ∈ B.powersetCard k, (∏ b ∈ T, Erdos494H1.truncExp r b).coeff 0 = 1 := by
      intro T _
      rw [Erdos494H1.coeff_prod_truncExp r T 0 (Nat.zero_le r)]
      simp
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_powersetCard, hBcard, nsmul_eq_mul, mul_one]
  have hp_coeff : ∀ (S : Finset ℂ) (j m : ℕ), m ≤ r →
      (∑ a ∈ S, (Erdos494H1.truncExp r a) ^ j).coeff m =
        (j : ℂ) ^ m / (m.factorial : ℂ) * ∑ a ∈ S, a ^ m := by
    intro S j m hm
    rw [Polynomial.finset_sum_coeff, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Erdos494H1.coeff_pow_truncExp r a j m hm, mul_pow]
    ring
  have he_lt : ∀ k m, m < r → (eA.coeff k).coeff m = (eB.coeff k).coeff m := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m hm
      cases k with
      | zero => rw [Erdos494H1.coeff_genPoly_zero, Erdos494H1.coeff_genPoly_zero]
      | succ k' =>
        have hA := congrArg (fun P => P.coeff m)
          (Erdos494H1.newton_identity A (Erdos494H1.truncExp r) (k' + 1) (by omega))
        have hB := congrArg (fun P => P.coeff m)
          (Erdos494H1.newton_identity B (Erdos494H1.truncExp r) (k' + 1) (by omega))
        simp only [Polynomial.coeff_natCast_mul, Polynomial.finset_sum_coeff] at hA hB
        have hrhs : ∑ j ∈ Finset.Icc 1 (k' + 1),
              ((-1 : Polynomial ℂ) ^ (j - 1) * (∑ a ∈ A, (Erdos494H1.truncExp r a) ^ j) *
                eA.coeff (k' + 1 - j)).coeff m =
            ∑ j ∈ Finset.Icc 1 (k' + 1),
              ((-1 : Polynomial ℂ) ^ (j - 1) * (∑ b ∈ B, (Erdos494H1.truncExp r b) ^ j) *
                eB.coeff (k' + 1 - j)).coeff m := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
          have hsign : (-1 : Polynomial ℂ) ^ (j - 1) = Polynomial.C ((-1 : ℂ) ^ (j - 1)) := by
            simp
          rw [hsign, mul_assoc, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
          congr 1
          rw [Polynomial.coeff_mul, Polynomial.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y =>
              (∑ a ∈ A, (Erdos494H1.truncExp r a) ^ j).coeff x * (eA.coeff (k' + 1 - j)).coeff y),
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y =>
              (∑ b ∈ B, (Erdos494H1.truncExp r b) ^ j).coeff x * (eB.coeff (k' + 1 - j)).coeff y)]
          apply Finset.sum_congr rfl
          intro l hl
          have hlm : l ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          have hp1 : l < r := by omega
          have hp2 : m - l < r := by omega
          rw [hp_coeff A j l hp1.le, hp_coeff B j l hp1.le, hlt l hp1,
            ih (k' + 1 - j) (by omega) (m - l) hp2]
        have heq : ((k' + 1 : ℕ) : ℂ) * (eA.coeff (k' + 1)).coeff m =
            ((k' + 1 : ℕ) : ℂ) * (eB.coeff (k' + 1)).coeff m :=
          hA.trans (hrhs.trans hB.symm)
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (by omega)) heq
  let Δ : ℂ := (∑ a ∈ A, a ^ r - ∑ b ∈ B, b ^ r) / (r.factorial : ℂ)
  have hΔ_ne : Δ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hr_ne) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r))
  let F : ℕ → ℂ := fun m =>
    ∑ i ∈ Finset.Icc 1 m, (-1 : ℂ) ^ (i - 1) * (Nat.choose n (m - i) : ℂ) * (i : ℂ) ^ (r - 1)
  have hdiff : ∀ k : ℕ, (eA.coeff k).coeff r - (eB.coeff k).coeff r = Δ * F k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero =>
        rw [Erdos494H1.coeff_genPoly_zero, Erdos494H1.coeff_genPoly_zero]
        simp [F]
      | succ k' =>
        have hA := congrArg (fun P => P.coeff r)
          (Erdos494H1.newton_identity A (Erdos494H1.truncExp r) (k' + 1) (by omega))
        have hB := congrArg (fun P => P.coeff r)
          (Erdos494H1.newton_identity B (Erdos494H1.truncExp r) (k' + 1) (by omega))
        simp only [Polynomial.coeff_natCast_mul, Polynomial.finset_sum_coeff] at hA hB
        have hsub_term : ∀ j ∈ Finset.Icc 1 (k' + 1),
            ((-1 : Polynomial ℂ) ^ (j - 1) * (∑ a ∈ A, (Erdos494H1.truncExp r a) ^ j) *
              eA.coeff (k' + 1 - j)).coeff r -
            ((-1 : Polynomial ℂ) ^ (j - 1) * (∑ b ∈ B, (Erdos494H1.truncExp r b) ^ j) *
              eB.coeff (k' + 1 - j)).coeff r =
            Δ * ((-1 : ℂ) ^ (j - 1) * (Nat.choose n (k' + 1 - j) : ℂ) * (j : ℂ) ^ r +
              (n : ℂ) * ((-1 : ℂ) ^ (j - 1) * F (k' + 1 - j))) := by
          intro j hj
          have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
          have hsign : (-1 : Polynomial ℂ) ^ (j - 1) = Polynomial.C ((-1 : ℂ) ^ (j - 1)) := by
            simp
          rw [hsign, mul_assoc, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
            Polynomial.coeff_mul, Polynomial.coeff_mul, ← mul_sub, ← Finset.sum_sub_distrib,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y =>
              (∑ a ∈ A, (Erdos494H1.truncExp r a) ^ j).coeff x * (eA.coeff (k' + 1 - j)).coeff y -
              (∑ b ∈ B, (Erdos494H1.truncExp r b) ^ j).coeff x * (eB.coeff (k' + 1 - j)).coeff y)]
          have hmid : ∀ m ∈ Finset.range (r + 1), m ≠ 0 → m ≠ r →
              (∑ a ∈ A, (Erdos494H1.truncExp r a) ^ j).coeff m * (eA.coeff (k' + 1 - j)).coeff (r - m) -
              (∑ b ∈ B, (Erdos494H1.truncExp r b) ^ j).coeff m * (eB.coeff (k' + 1 - j)).coeff (r - m) = 0 := by
            intro m hm hm0 hmr
            have hm_lt : m < r := by
              have := Finset.mem_range.mp hm; omega
            have hrm_lt : r - m < r := by omega
            rw [hp_coeff A j m hm_lt.le, hp_coeff B j m hm_lt.le, hlt m hm_lt,
              he_lt (k' + 1 - j) (r - m) hrm_lt, sub_self]
          have hsum_two : ∑ m ∈ Finset.range (r + 1),
              ((∑ a ∈ A, (Erdos494H1.truncExp r a) ^ j).coeff m * (eA.coeff (k' + 1 - j)).coeff (r - m) -
               (∑ b ∈ B, (Erdos494H1.truncExp r b) ^ j).coeff m * (eB.coeff (k' + 1 - j)).coeff (r - m)) =
              ((∑ a ∈ A, (Erdos494H1.truncExp r a) ^ j).coeff 0 * (eA.coeff (k' + 1 - j)).coeff r -
               (∑ b ∈ B, (Erdos494H1.truncExp r b) ^ j).coeff 0 * (eB.coeff (k' + 1 - j)).coeff r) +
              ((∑ a ∈ A, (Erdos494H1.truncExp r a) ^ j).coeff r * (eA.coeff (k' + 1 - j)).coeff 0 -
               (∑ b ∈ B, (Erdos494H1.truncExp r b) ^ j).coeff r * (eB.coeff (k' + 1 - j)).coeff 0) := by
            have hsub0r : ({0, r} : Finset ℕ) ⊆ Finset.range (r + 1) := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
            rw [← Finset.sum_subset hsub0r]
            · rw [Finset.sum_pair (by omega : 0 ≠ r)]
              simp
            · intro m hm hnot
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
              exact hmid m hm hnot.1 hnot.2
          rw [hsum_two, hp_coeff A j 0 (Nat.zero_le r), hp_coeff B j 0 (Nat.zero_le r),
            hp_coeff A j r le_rfl, hp_coeff B j r le_rfl, heA0, heB0]
          simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
            Finset.sum_const, hAcard, hBcard, nsmul_eq_mul, mul_one]
          have hih := ih (k' + 1 - j) (by omega)
          dsimp only [Δ]
          linear_combination (-1 : ℂ) ^ (j - 1) * (n : ℂ) * hih
        have hstep : ((k' + 1 : ℕ) : ℂ) * ((eA.coeff (k' + 1)).coeff r - (eB.coeff (k' + 1)).coeff r) =
            Δ * (∑ j ∈ Finset.Icc 1 (k' + 1), (-1 : ℂ) ^ (j - 1) * (Nat.choose n (k' + 1 - j) : ℂ) * (j : ℂ) ^ r +
              (n : ℂ) * ∑ j ∈ Finset.Icc 1 (k' + 1), (-1 : ℂ) ^ (j - 1) * F (k' + 1 - j)) := by
          calc ((k' + 1 : ℕ) : ℂ) * ((eA.coeff (k' + 1)).coeff r - (eB.coeff (k' + 1)).coeff r)
              = ((k' + 1 : ℕ) : ℂ) * (eA.coeff (k' + 1)).coeff r -
                ((k' + 1 : ℕ) : ℂ) * (eB.coeff (k' + 1)).coeff r := by ring
            _ = ∑ j ∈ Finset.Icc 1 (k' + 1),
                  (((-1 : Polynomial ℂ) ^ (j - 1) * (∑ a ∈ A, (Erdos494H1.truncExp r a) ^ j) *
                    eA.coeff (k' + 1 - j)).coeff r -
                   ((-1 : Polynomial ℂ) ^ (j - 1) * (∑ b ∈ B, (Erdos494H1.truncExp r b) ^ j) *
                    eB.coeff (k' + 1 - j)).coeff r) := by
                  rw [hA, hB, Finset.sum_sub_distrib]
            _ = ∑ j ∈ Finset.Icc 1 (k' + 1),
                  Δ * ((-1 : ℂ) ^ (j - 1) * (Nat.choose n (k' + 1 - j) : ℂ) * (j : ℂ) ^ r +
                    (n : ℂ) * ((-1 : ℂ) ^ (j - 1) * F (k' + 1 - j))) :=
                  Finset.sum_congr rfl hsub_term
            _ = Δ * (∑ j ∈ Finset.Icc 1 (k' + 1), (-1 : ℂ) ^ (j - 1) * (Nat.choose n (k' + 1 - j) : ℂ) * (j : ℂ) ^ r +
                  (n : ℂ) * ∑ j ∈ Finset.Icc 1 (k' + 1), (-1 : ℂ) ^ (j - 1) * F (k' + 1 - j)) := by
                  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        have hrec := Erdos494H1.coeff_binom_power_recurrence n r (k' + 1) hr1 (by omega)
        dsimp only at hrec
        have hstep' : ((k' + 1 : ℕ) : ℂ) * ((eA.coeff (k' + 1)).coeff r - (eB.coeff (k' + 1)).coeff r) =
            ((k' + 1 : ℕ) : ℂ) * (Δ * F (k' + 1)) := by
          rw [hstep, ← hrec]
          ring
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (by omega)) hstep'
  have hes_eq : (eA.coeff s).coeff r = (eB.coeff s).coeff r := by
    have hpow_eq : ∀ S : Finset ℂ, (Erdos494H1.genPoly S (Erdos494H1.truncExp r) |>.coeff s).coeff r =
        ((Erdos494.sumMultiset S s).map (fun z : ℂ => z ^ r)).sum / (r.factorial : ℂ) := by
      intro S
      rw [Erdos494H1.coeff_genPoly_eq_powersetCard, Polynomial.finset_sum_coeff]
      have h1 : ∀ T ∈ S.powersetCard s,
          (∏ a ∈ T, Erdos494H1.truncExp r a).coeff r = (∑ a ∈ T, a) ^ r / (r.factorial : ℂ) :=
        fun T _ => Erdos494H1.coeff_prod_truncExp r T r le_rfl
      rw [Finset.sum_congr rfl h1, ← Finset.sum_div]
      congr 1
      unfold Erdos494.sumMultiset
      rw [Multiset.map_map]
      rfl
    rw [hpow_eq A, hpow_eq B, hsum]
  have hFs0 : F s = 0 := by
    have h1 := hdiff s
    rw [hes_eq, sub_self] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hΔ_ne
  refine ⟨r, hr1, ?_⟩
  have hcast : ((∑ i ∈ Finset.Icc 1 s,
      (-1 : ℤ) ^ (i - 1) * (Nat.choose n (s - i) : ℤ) * (i : ℤ) ^ (r - 1) : ℤ) : ℂ) = 0 := by
    push_cast
    exact hFs0
  exact Int.cast_eq_zero.mp hcast
