import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2_H2_R1

/-! # Truncated logarithmic derivative criterion in `(ZMod p)[X]` (H2)

We prove `OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2_H2_R1.H2`:
an identity of truncated geometric sums modulo `X ^ (p - 1)` in `(ZMod p)[X]`
forces the Bernoulli-weighted even moments of its exponents to vanish modulo `p`.

The proof works completely inside `(ZMod p)[X]`:
1. Using `sum_bernoulli`, strong induction shows that for `r < p - 1`, `p` does not
   divide `(bernoulli r).den`, and the reduced Bernoulli numbers `b r : ZMod p`
   satisfy the same binomial recurrence modulo `p`.
2. We define the truncated exponential `E k` and truncated Bernoulli generating
   polynomial `B k` up to degree `p - 2`, verifying `E k * E l ≡ E (k + l)`,
   `B k * (E k - 1) ≡ C k * X` modulo `X ^ (p - 1)`, and `(E k)' ≡ C k * E k`
   modulo `X ^ (p - 2)`.
3. Substituting `X ↦ E 1 - 1` into the hypothesis, taking the logarithmic derivative
   using truncated polynomial inverses modulo `X ^ (p - 1)`, and extracting the
   coefficient of `X ^ (2 * (j + 1))` (with `2 ≤ 2 * (j + 1) < p - 2`) yields
   the claimed vanishing.
-/

namespace RegularPrimesH2

open Polynomial Finset

section RationalReduction

variable (p : ℕ) [Fact p.Prime]

/-- A rational number is `p`-integral if it can be written with a denominator not divisible by `p`. -/
private def PInt (q : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ q = (a : ℚ) / (b : ℚ)

/-- Reduction of a rational number to `ZMod p`. -/
private noncomputable def red (q : ℚ) : ZMod p :=
  (q.num : ZMod p) * (q.den : ZMod p)⁻¹

omit [Fact p.Prime] in
private lemma p_not_dvd_den_of_PInt {q : ℚ} (hq : PInt p q) : ¬ p ∣ q.den := by
  obtain ⟨a, b, hpb, hab⟩ := hq
  have hb0 : b ≠ 0 := fun h => hpb (h ▸ dvd_zero p)
  have hqb : q * (b : ℚ) = (a : ℚ) := by
    rw [hab]
    exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hb0)
  have hmul : (q.num : ℤ) * (b : ℤ) = a * (q.den : ℤ) := by
    have hq' : (q.num : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) := by
      calc
        (q.num : ℚ) * (b : ℚ) = (q * (q.den : ℚ)) * (b : ℚ) := by rw [Rat.mul_den_eq_num]
        _ = (q * (b : ℚ)) * (q.den : ℚ) := by ring
        _ = (a : ℚ) * (q.den : ℚ) := by rw [hqb]
    exact_mod_cast hq'
  have hdvd_int : (q.den : ℤ) ∣ (q.num : ℤ) * (b : ℤ) := ⟨a, by linarith⟩
  have hdvd_nat : q.den ∣ q.num.natAbs * b := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd_int
    simpa [Int.natAbs_mul] using h
  have hdvd_b : q.den ∣ b := q.reduced.symm.dvd_of_dvd_mul_left hdvd_nat
  exact fun hpd => hpb (dvd_trans hpd hdvd_b)

private lemma red_eq_div_of_eq {q : ℚ} {a : ℤ} {b : ℕ} (hpb : ¬ p ∣ b)
    (hab : q = (a : ℚ) / (b : ℚ)) :
    red p q = (a : ZMod p) * (b : ZMod p)⁻¹ := by
  have hp : p.Prime := Fact.out
  have hb0 : b ≠ 0 := fun h => hpb (h ▸ dvd_zero p)
  have hpd : ¬ p ∣ q.den := p_not_dvd_den_of_PInt p ⟨a, b, hpb, hab⟩
  have hb_ne : (b : ZMod p) ≠ 0 := fun h => hpb ((ZMod.natCast_eq_zero_iff b p).mp h)
  have hd_ne : (q.den : ZMod p) ≠ 0 := fun h => hpd ((ZMod.natCast_eq_zero_iff q.den p).mp h)
  have hqb : q * (b : ℚ) = (a : ℚ) := by
    rw [hab]
    exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hb0)
  have hmul : (q.num : ℤ) * (b : ℤ) = a * (q.den : ℤ) := by
    have hq' : (q.num : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) := by
      calc
        (q.num : ℚ) * (b : ℚ) = (q * (q.den : ℚ)) * (b : ℚ) := by rw [Rat.mul_den_eq_num]
        _ = (q * (b : ℚ)) * (q.den : ℚ) := by ring
        _ = (a : ℚ) * (q.den : ℚ) := by rw [hqb]
    exact_mod_cast hq'
  have hmod : (q.num : ZMod p) * (b : ZMod p) = (a : ZMod p) * (q.den : ZMod p) := by
    have := congrArg (Int.cast (R := ZMod p)) hmul
    simpa using this
  unfold red
  calc
    (q.num : ZMod p) * (q.den : ZMod p)⁻¹
        = ((q.num : ZMod p) * (b : ZMod p)) * ((b : ZMod p)⁻¹ * (q.den : ZMod p)⁻¹) := by
          field_simp [hb_ne, hd_ne]
    _ = ((a : ZMod p) * (q.den : ZMod p)) * ((b : ZMod p)⁻¹ * (q.den : ZMod p)⁻¹) := by rw [hmod]
    _ = (a : ZMod p) * (b : ZMod p)⁻¹ := by
          field_simp [hb_ne, hd_ne]

private lemma pInt_natCast (n : ℕ) : PInt p (n : ℚ) :=
  ⟨n, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩

private lemma pInt_zero : PInt p 0 := by
  simpa using pInt_natCast p 0

private lemma pInt_add {q₁ q₂ : ℚ} (h₁ : PInt p q₁) (h₂ : PInt p q₂) : PInt p (q₁ + q₂) := by
  obtain ⟨a₁, b₁, hb₁, rfl⟩ := h₁
  obtain ⟨a₂, b₂, hb₂, rfl⟩ := h₂
  have hb₁0 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr fun h => hb₁ (h ▸ dvd_zero p)
  have hb₂0 : (b₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr fun h => hb₂ (h ▸ dvd_zero p)
  have hp : p.Prime := Fact.out
  refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, fun hdvd => ?_, ?_⟩
  · rcases hp.dvd_mul.mp hdvd with h | h
    · exact hb₁ h
    · exact hb₂ h
  · push_cast
    field_simp [hb₁0, hb₂0]

private lemma pInt_mul {q₁ q₂ : ℚ} (h₁ : PInt p q₁) (h₂ : PInt p q₂) : PInt p (q₁ * q₂) := by
  obtain ⟨a₁, b₁, hb₁, rfl⟩ := h₁
  obtain ⟨a₂, b₂, hb₂, rfl⟩ := h₂
  have hp : p.Prime := Fact.out
  refine ⟨a₁ * a₂, b₁ * b₂, fun hdvd => ?_, ?_⟩
  · rcases hp.dvd_mul.mp hdvd with h | h
    · exact hb₁ h
    · exact hb₂ h
  · push_cast
    ring

omit [Fact p.Prime] in
private lemma pInt_neg {q : ℚ} (h : PInt p q) : PInt p (-q) := by
  obtain ⟨a, b, hb, rfl⟩ := h
  exact ⟨-a, b, hb, by push_cast; ring⟩

private lemma pInt_div_nat {q : ℚ} {d : ℕ} (hq : PInt p q) (hpd : ¬ p ∣ d) :
    PInt p (q / (d : ℚ)) := by
  obtain ⟨a, b, hb, rfl⟩ := hq
  have hp : p.Prime := Fact.out
  refine ⟨a, b * d, fun hdvd => ?_, ?_⟩
  · rcases hp.dvd_mul.mp hdvd with h | h
    · exact hb h
    · exact hpd h
  · push_cast
    rw [div_div]

private lemma pInt_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, PInt p (f i)) : PInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pInt_zero p
  | @insert a s has ih =>
    rw [Finset.sum_insert has]
    exact pInt_add p (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma red_natCast (n : ℕ) : red p (n : ℚ) = (n : ZMod p) := by
  have h := red_eq_div_of_eq p (q := (n : ℚ)) (a := (n : ℤ)) (b := 1)
    (Fact.out : p.Prime).not_dvd_one (by simp)
  simpa using h

private lemma red_add {q₁ q₂ : ℚ} (h₁ : PInt p q₁) (h₂ : PInt p q₂) :
    red p (q₁ + q₂) = red p q₁ + red p q₂ := by
  obtain ⟨a₁, b₁, hb₁, rfl⟩ := h₁
  obtain ⟨a₂, b₂, hb₂, rfl⟩ := h₂
  have hp : p.Prime := Fact.out
  have hb₁0 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr fun h => hb₁ (h ▸ dvd_zero p)
  have hb₂0 : (b₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr fun h => hb₂ (h ▸ dvd_zero p)
  have hb₁z : (b₁ : ZMod p) ≠ 0 := fun h => hb₁ ((ZMod.natCast_eq_zero_iff b₁ p).mp h)
  have hb₂z : (b₂ : ZMod p) ≠ 0 := fun h => hb₂ ((ZMod.natCast_eq_zero_iff b₂ p).mp h)
  have hpb12 : ¬ p ∣ b₁ * b₂ := fun hd => (hp.dvd_mul.mp hd).elim hb₁ hb₂
  rw [red_eq_div_of_eq p hb₁ rfl, red_eq_div_of_eq p hb₂ rfl,
    red_eq_div_of_eq p hpb12 (a := a₁ * b₂ + a₂ * b₁) (by push_cast; field_simp [hb₁0, hb₂0])]
  push_cast
  field_simp [hb₁z, hb₂z]

private lemma red_mul {q₁ q₂ : ℚ} (h₁ : PInt p q₁) (h₂ : PInt p q₂) :
    red p (q₁ * q₂) = red p q₁ * red p q₂ := by
  obtain ⟨a₁, b₁, hb₁, rfl⟩ := h₁
  obtain ⟨a₂, b₂, hb₂, rfl⟩ := h₂
  have hp : p.Prime := Fact.out
  have hpb12 : ¬ p ∣ b₁ * b₂ := fun hd => (hp.dvd_mul.mp hd).elim hb₁ hb₂
  rw [red_eq_div_of_eq p hb₁ rfl, red_eq_div_of_eq p hb₂ rfl,
    red_eq_div_of_eq p hpb12 (a := a₁ * a₂) (by push_cast; ring)]
  push_cast
  ring

private lemma red_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, PInt p (f i)) :
    red p (∑ i ∈ s, f i) = ∑ i ∈ s, red p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using red_natCast p 0
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has,
      red_add p (hf a (Finset.mem_insert_self a s))
        (pInt_sum p s f fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private lemma bernoulli_pInt : ∀ r : ℕ, r < p - 1 → PInt p (_root_.bernoulli r) := by
  have hp : p.Prime := Fact.out
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    cases r with
    | zero =>
      rw [_root_.bernoulli_zero]
      exact pInt_natCast p 1
    | succ r =>
      have hsum := _root_.sum_bernoulli (r + 2)
      rw [if_neg (by omega), Finset.sum_range_succ, Nat.choose_succ_self_right] at hsum
      have hr2_ne : ((r + 2 : ℕ) : ℚ) ≠ 0 := by positivity
      have hbeq : _root_.bernoulli (r + 1) =
          -(∑ i ∈ Finset.range (r + 1), (((r + 2).choose i : ℕ) : ℚ) * _root_.bernoulli i) /
            ((r + 2 : ℕ) : ℚ) := by
        apply eq_div_of_mul_eq hr2_ne
        linarith
      rw [hbeq]
      have hpd : ¬ p ∣ r + 2 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      refine pInt_div_nat p (pInt_neg p (pInt_sum p _ _ fun i hi => ?_)) hpd
      have hi' : i < r + 1 := Finset.mem_range.mp hi
      exact pInt_mul p (pInt_natCast p _) (ih i hi' (by omega))

private lemma sum_bernoulli_mod {r : ℕ} (hr : r < p - 1) :
    ∑ i ∈ Finset.range (r + 1), (((r + 1).choose i : ℕ) : ZMod p) * red p (_root_.bernoulli i) =
      if r = 0 then 1 else 0 := by
  have h1 := _root_.sum_bernoulli (r + 1)
  have h2 : red p (∑ i ∈ Finset.range (r + 1), (((r + 1).choose i : ℕ) : ℚ) * _root_.bernoulli i) =
      red p (if r + 1 = 1 then 1 else 0) := congrArg (red p) h1
  rw [red_sum p _ _ fun i hi => pInt_mul p (pInt_natCast p _)
      (bernoulli_pInt p i (by have := Finset.mem_range.mp hi; omega))] at h2
  have h3 : ∀ i ∈ Finset.range (r + 1),
      red p ((((r + 1).choose i : ℕ) : ℚ) * _root_.bernoulli i) =
        (((r + 1).choose i : ℕ) : ZMod p) * red p (_root_.bernoulli i) := by
    intro i hi
    rw [red_mul p (pInt_natCast p _)
        (bernoulli_pInt p i (by have := Finset.mem_range.mp hi; omega)), red_natCast]
  rw [Finset.sum_congr rfl h3] at h2
  rw [h2]
  by_cases hr0 : r = 0
  · subst hr0
    simpa using red_natCast p 1
  · have : r + 1 ≠ 1 := by omega
    simp only [hr0, this, ↓reduceIte]
    simpa using red_natCast p 0

end RationalReduction

section TruncatedPoly

variable (p : ℕ) [Fact p.Prime]

private lemma factorial_ne_zero_zmod {r : ℕ} (hr : r < p) : (r.factorial : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro h
  have hdvd : p ∣ r.factorial := (ZMod.natCast_eq_zero_iff _ _).mp h
  have hle : p ≤ r := (hp.dvd_factorial).mp hdvd
  omega

private lemma inv_factorial_mul_inv_factorial {r i : ℕ} (hr : r < p) (hi : i ≤ r) :
    (i.factorial : ZMod p)⁻¹ * ((r - i).factorial : ZMod p)⁻¹ =
      (r.choose i : ZMod p) * (r.factorial : ZMod p)⁻¹ := by
  have h1 : (i.factorial : ZMod p) ≠ 0 := factorial_ne_zero_zmod p (by omega)
  have h2 : ((r - i).factorial : ZMod p) ≠ 0 := factorial_ne_zero_zmod p (by omega)
  have h3 : (r.factorial : ZMod p) ≠ 0 := factorial_ne_zero_zmod p hr
  have hch : r.choose i * i.factorial * (r - i).factorial = r.factorial :=
    Nat.choose_mul_factorial_mul_factorial hi
  have hchz : (r.choose i : ZMod p) * (i.factorial : ZMod p) * ((r - i).factorial : ZMod p) =
      (r.factorial : ZMod p) := by
    simpa using congrArg (Nat.cast (R := ZMod p)) hch
  field_simp [h1, h2, h3]
  linear_combination -hchz

/-- Truncated exponential polynomial up to degree `p - 2`. -/
private noncomputable def E (k : ZMod p) : (ZMod p)[X] :=
  ∑ r ∈ Finset.range (p - 1), C (k ^ r * (r.factorial : ZMod p)⁻¹) * X ^ r

/-- Truncated Bernoulli generating polynomial up to degree `p - 2`. -/
private noncomputable def B (k : ZMod p) : (ZMod p)[X] :=
  ∑ r ∈ Finset.range (p - 1), C (red p (_root_.bernoulli r) * k ^ r * (r.factorial : ZMod p)⁻¹) * X ^ r

private lemma coeff_E (k : ZMod p) (r : ℕ) :
    (E p k).coeff r = if r < p - 1 then k ^ r * (r.factorial : ZMod p)⁻¹ else 0 := by
  unfold E
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hr : r < p - 1
  · rw [if_pos hr, Finset.sum_eq_single r]
    · simp
    · intro b _ hbr
      simp [hbr.symm]
    · intro hnot
      exact absurd (Finset.mem_range.mpr hr) hnot
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro b hb
    have hbr : r ≠ b := by
      have := Finset.mem_range.mp hb
      omega
    simp [hbr]

private lemma coeff_B (k : ZMod p) (r : ℕ) :
    (B p k).coeff r =
      if r < p - 1 then red p (_root_.bernoulli r) * k ^ r * (r.factorial : ZMod p)⁻¹ else 0 := by
  unfold B
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hr : r < p - 1
  · rw [if_pos hr, Finset.sum_eq_single r]
    · simp
    · intro b _ hbr
      simp [hbr.symm]
    · intro hnot
      exact absurd (Finset.mem_range.mpr hr) hnot
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro b hb
    have hbr : r ≠ b := by
      have := Finset.mem_range.mp hb
      omega
    simp [hbr]

private lemma E_zero_eq_one (hp : 2 ≤ p) : E p 0 = 1 := by
  ext r
  rw [coeff_E, Polynomial.coeff_one]
  cases r with
  | zero =>
    have h0 : 0 < p - 1 := by omega
    simp [h0]
  | succ r =>
    by_cases hr : r + 1 < p - 1
    · simp [hr]
    · simp [hr]

private lemma E_mul_E_mod (k l : ZMod p) :
    (X : (ZMod p)[X]) ^ (p - 1) ∣ E p k * E p l - E p (k + l) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro r hr
  rw [Polynomial.coeff_sub, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    coeff_E, if_pos hr]
  have hsum :
      ∑ i ∈ Finset.range (r + 1), (E p k).coeff i * (E p l).coeff (r - i) =
        (k + l) ^ r * (r.factorial : ZMod p)⁻¹ := by
    have hterm : ∀ i ∈ Finset.range (r + 1),
        (E p k).coeff i * (E p l).coeff (r - i) =
          (k ^ i * l ^ (r - i) * (r.choose i : ZMod p)) * (r.factorial : ZMod p)⁻¹ := by
      intro i hi
      have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [coeff_E, coeff_E, if_pos (by omega), if_pos (by omega)]
      have hfac := inv_factorial_mul_inv_factorial p (by omega : r < p) hir
      calc
        k ^ i * (i.factorial : ZMod p)⁻¹ * (l ^ (r - i) * ((r - i).factorial : ZMod p)⁻¹)
            = k ^ i * l ^ (r - i) * ((i.factorial : ZMod p)⁻¹ * ((r - i).factorial : ZMod p)⁻¹) := by
              ring
        _ = k ^ i * l ^ (r - i) * ((r.choose i : ZMod p) * (r.factorial : ZMod p)⁻¹) := by
              rw [hfac]
        _ = (k ^ i * l ^ (r - i) * (r.choose i : ZMod p)) * (r.factorial : ZMod p)⁻¹ := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← add_pow]
  rw [hsum, sub_self]

private lemma E_one_pow_mod (hp : 2 ≤ p) (t : ℕ) :
    (X : (ZMod p)[X]) ^ (p - 1) ∣ E p 1 ^ t - E p (t : ZMod p) := by
  induction t with
  | zero =>
    simp [E_zero_eq_one p hp]
  | succ t ih =>
    have h1 : (X : (ZMod p)[X]) ^ (p - 1) ∣ (E p 1 ^ t - E p (t : ZMod p)) * E p 1 :=
      dvd_mul_of_dvd_left ih _
    have h2 : (X : (ZMod p)[X]) ^ (p - 1) ∣ E p (t : ZMod p) * E p 1 - E p ((t : ZMod p) + 1) :=
      E_mul_E_mod p (t : ZMod p) 1
    have hsum := dvd_add h1 h2
    have heq : (E p 1 ^ t - E p (t : ZMod p)) * E p 1 +
        (E p (t : ZMod p) * E p 1 - E p ((t : ZMod p) + 1)) =
        E p 1 ^ (t + 1) - E p ((t + 1 : ℕ) : ZMod p) := by
      push_cast
      rw [pow_succ]
      ring
    rwa [heq] at hsum

private lemma derivative_E_mod (k : ZMod p) :
    (X : (ZMod p)[X]) ^ (p - 2) ∣ (E p k).derivative - C k * E p k := by
  rw [Polynomial.X_pow_dvd_iff]
  intro r hr
  have hr1 : r + 1 < p - 1 := by omega
  have hr0 : r < p - 1 := by omega
  rw [Polynomial.coeff_sub, Polynomial.coeff_derivative, Polynomial.coeff_C_mul,
    coeff_E, coeff_E, if_pos hr1, if_pos hr0]
  have hne : ((r + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have hdvd := (ZMod.natCast_eq_zero_iff (r + 1) p).mp h
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  have hfac : ((r + 1).factorial : ZMod p) = ((r + 1 : ℕ) : ZMod p) * (r.factorial : ZMod p) := by
    rw [Nat.factorial_succ]
    push_cast
    rfl
  have hrfac : (r.factorial : ZMod p) ≠ 0 := factorial_ne_zero_zmod p (by omega)
  rw [hfac, pow_succ]
  push_cast at hne ⊢
  field_simp [hne, hrfac]
  ring

private lemma B_mul_E_sub_one_mod (hp : 3 ≤ p) (k : ZMod p) :
    (X : (ZMod p)[X]) ^ (p - 1) ∣ B p k * (E p k - 1) - C k * X := by
  rw [Polynomial.X_pow_dvd_iff]
  intro r hr
  rw [Polynomial.coeff_sub, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_C_mul, Polynomial.coeff_X]
  cases r with
  | zero =>
    have h0 : 0 < p - 1 := by omega
    simp [coeff_E, h0]
  | succ r =>
    rw [Finset.sum_range_succ]
    have hlast : (E p k - 1).coeff 0 = 0 := by
      have h0 : 0 < p - 1 := by omega
      simp [coeff_E, h0]
    rw [Nat.sub_self, hlast, mul_zero, add_zero]
    have hterm : ∀ i ∈ Finset.range (r + 1),
        (B p k).coeff i * (E p k - 1).coeff (r + 1 - i) =
          (k ^ (r + 1) * ((r + 1).factorial : ZMod p)⁻¹) *
            ((((r + 1).choose i : ℕ) : ZMod p) * red p (_root_.bernoulli i)) := by
      intro i hi
      have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hpos : r + 1 - i ≠ 0 := by omega
      have hsub_lt : r + 1 - i < p - 1 := by omega
      rw [coeff_B, if_pos (by omega), Polynomial.coeff_sub, coeff_E, if_pos hsub_lt,
        Polynomial.coeff_one, if_neg hpos, sub_zero]
      have hfac := inv_factorial_mul_inv_factorial p (by omega : r + 1 < p) (by omega : i ≤ r + 1)
      have hpow : k ^ i * k ^ (r + 1 - i) = k ^ (r + 1) := by
        rw [← pow_add, Nat.add_sub_of_le (by omega)]
      calc
        red p (_root_.bernoulli i) * k ^ i * (i.factorial : ZMod p)⁻¹ *
            (k ^ (r + 1 - i) * ((r + 1 - i).factorial : ZMod p)⁻¹)
            = red p (_root_.bernoulli i) * (k ^ i * k ^ (r + 1 - i)) *
                ((i.factorial : ZMod p)⁻¹ * ((r + 1 - i).factorial : ZMod p)⁻¹) := by ring
        _ = red p (_root_.bernoulli i) * k ^ (r + 1) *
              (((r + 1).choose i : ZMod p) * ((r + 1).factorial : ZMod p)⁻¹) := by
              rw [hpow, hfac]
        _ = (k ^ (r + 1) * ((r + 1).factorial : ZMod p)⁻¹) *
              ((((r + 1).choose i : ℕ) : ZMod p) * red p (_root_.bernoulli i)) := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_bernoulli_mod p (by omega)]
    cases r with
    | zero => simp
    | succ r => simp

private lemma B_mul_E_mod (hp : 3 ≤ p) (k : ZMod p) :
    (X : (ZMod p)[X]) ^ (p - 1) ∣ B p k * E p k - (B p k + C k * X) := by
  have h := B_mul_E_sub_one_mod p hp k
  have heq : B p k * (E p k - 1) - C k * X = B p k * E p k - (B p k + C k * X) := by ring
  rwa [heq] at h

/-- Truncated polynomial inverse modulo `X ^ M` for a polynomial with nonzero constant term. -/
private noncomputable def invMod (g : (ZMod p)[X]) (M : ℕ) : (ZMod p)[X] :=
  let u := 1 - C (g.coeff 0)⁻¹ * g
  C (g.coeff 0)⁻¹ * ∑ i ∈ Finset.range M, u ^ i

private lemma mul_invMod_mod {g : (ZMod p)[X]} (hg : g.coeff 0 ≠ 0) (M : ℕ) :
    (X : (ZMod p)[X]) ^ M ∣ g * invMod p g M - 1 := by
  let u : (ZMod p)[X] := 1 - C (g.coeff 0)⁻¹ * g
  have hu0 : u.coeff 0 = 0 := by
    simp [u, hg]
  have hXu : (X : (ZMod p)[X]) ∣ u := Polynomial.X_dvd_iff.mpr hu0
  have hXM : (X : (ZMod p)[X]) ^ M ∣ u ^ M := pow_dvd_pow_of_dvd hXu M
  have hgeom : (1 - u) * ∑ i ∈ Finset.range M, u ^ i = 1 - u ^ M := by
    have h := geom_sum_mul_neg u M
    linear_combination h
  have h1u : 1 - u = C (g.coeff 0)⁻¹ * g := by simp [u]
  have hprod : g * invMod p g M - 1 = -(u ^ M) := by
    unfold invMod
    calc
      g * (C (g.coeff 0)⁻¹ * ∑ i ∈ Finset.range M, u ^ i) - 1
          = (C (g.coeff 0)⁻¹ * g) * ∑ i ∈ Finset.range M, u ^ i - 1 := by ring
      _ = (1 - u) * ∑ i ∈ Finset.range M, u ^ i - 1 := by rw [← h1u]
      _ = (1 - u ^ M) - 1 := by rw [hgeom]
      _ = -(u ^ M) := by ring
  rw [hprod]
  exact dvd_neg.mpr hXM

private lemma dvd_derivative_of_X_pow_dvd {M : ℕ} {P : (ZMod p)[X]}
    (h : (X : (ZMod p)[X]) ^ (M + 1) ∣ P) :
    (X : (ZMod p)[X]) ^ M ∣ P.derivative := by
  rw [Polynomial.X_pow_dvd_iff] at h ⊢
  intro r hr
  rw [Polynomial.coeff_derivative, h (r + 1) (by omega), zero_mul]

private lemma dvd_of_X_mul_dvd {M : ℕ} {P : (ZMod p)[X]}
    (h : (X : (ZMod p)[X]) ^ (M + 1) ∣ X * P) :
    (X : (ZMod p)[X]) ^ M ∣ P := by
  rw [Polynomial.X_pow_dvd_iff] at h ⊢
  intro r hr
  have h1 := h (r + 1) (by omega)
  rwa [Polynomial.coeff_X_mul] at h1

private lemma log_deriv_prod_mod {ι : Type*} [DecidableEq ι] (M : ℕ) (S : Finset ι)
    (Q R : ι → (ZMod p)[X]) (w : ι → ℕ)
    (hQR : ∀ a ∈ S, (X : (ZMod p)[X]) ^ M ∣ Q a * R a - 1) :
    (X : (ZMod p)[X]) ^ M ∣
      (∏ a ∈ S, Q a ^ w a).derivative -
        (∏ a ∈ S, Q a ^ w a) * ∑ a ∈ S, C (w a : ZMod p) * (Q a).derivative * R a := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S has ih =>
    have hQa : (X : (ZMod p)[X]) ^ M ∣ Q a * R a - 1 := hQR a (Finset.mem_insert_self a S)
    have ih' := ih fun b hb => hQR b (Finset.mem_insert_of_mem hb)
    rw [Finset.prod_insert has, Finset.sum_insert has, Polynomial.derivative_mul,
      Polynomial.derivative_pow]
    set P := ∏ b ∈ S, Q b ^ w b
    set L := ∑ b ∈ S, C (w b : ZMod p) * (Q b).derivative * R b
    have hpow_term :
        (X : (ZMod p)[X]) ^ M ∣
          C (w a : ZMod p) * Q a ^ (w a - 1) * (Q a).derivative -
            Q a ^ w a * (C (w a : ZMod p) * (Q a).derivative * R a) := by
      cases hw : w a with
      | zero => simp
      | succ k =>
        have heq : C ((k + 1 : ℕ) : ZMod p) * Q a ^ k * (Q a).derivative -
            Q a ^ (k + 1) * (C ((k + 1 : ℕ) : ZMod p) * (Q a).derivative * R a) =
            -(C ((k + 1 : ℕ) : ZMod p) * Q a ^ k * (Q a).derivative * (Q a * R a - 1)) := by
          rw [pow_succ]
          ring
        rw [Nat.succ_sub_one, heq]
        exact dvd_neg.mpr (dvd_mul_of_dvd_right hQa _)
    have h1 := dvd_mul_of_dvd_left hpow_term P
    have h2 := dvd_mul_of_dvd_right ih' (Q a ^ w a)
    have hsum := dvd_add h1 h2
    have heq :
        (C (w a : ZMod p) * Q a ^ (w a - 1) * (Q a).derivative -
            Q a ^ w a * (C (w a : ZMod p) * (Q a).derivative * R a)) * P +
          Q a ^ w a * (P.derivative - P * L) =
        C (w a : ZMod p) * Q a ^ (w a - 1) * (Q a).derivative * P +
            Q a ^ w a * P.derivative -
          Q a ^ w a * P * (C (w a : ZMod p) * (Q a).derivative * R a + L) := by
      ring
    rwa [heq] at hsum

end TruncatedPoly

theorem main_H2 : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2_H2_R1.H2 := by
  intro p hp
  dsimp only
  set m := (p - 3) / 2
  intro e s c hc hdiv j
  have hp_prime : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by
    have hj := j.isLt
    omega
  have hp_odd : p % 2 = 1 := by
    rcases hp_prime.eq_two_or_odd with rfl | hodd
    · omega
    · exact hodd
  have hN_eq : p - 1 = (p - 2) + 1 := by omega
  -- Step 1: Substitute X ↦ E 1 - 1 into hdiv
  let Q : Fin m → (ZMod p)[X] := fun a => ∑ i ∈ Finset.range (a.val + 2), E p 1 ^ i
  let F : (ZMod p)[X] := ∏ a : Fin m, Q a ^ (2 * (e a).val)
  let F₀ : (ZMod p)[X] :=
    ∏ a : Fin m, (∑ i ∈ Finset.range (a.val + 2), (1 + (X : (ZMod p)[X])) ^ i) ^ (2 * (e a).val)
  have hcomp_F₀ : F₀.comp (E p 1 - 1) = F := by
    dsimp [F₀, F, Q]
    rw [Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro a _
    rw [Polynomial.pow_comp, Polynomial.sum_comp]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.one_comp, Polynomial.X_comp,
      add_sub_cancel]
  have hX_dvd_E1 : (X : (ZMod p)[X]) ∣ E p 1 - 1 := by
    rw [Polynomial.X_dvd_iff]
    have h0 : 0 < p - 1 := by omega
    simp [coeff_E, h0]
  have hdiv_sub : (X : (ZMod p)[X]) ^ (p - 1) ∣ F - C c * E p 1 ^ s := by
    obtain ⟨H, hH⟩ := hdiv
    have h1 := congrArg (fun P => P.comp (E p 1 - 1)) hH
    rw [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.add_comp, Polynomial.one_comp, Polynomial.X_comp, add_sub_cancel,
      Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, hcomp_F₀] at h1
    rw [h1]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hX_dvd_E1 (p - 1)) _
  have hdiv_Es : (X : (ZMod p)[X]) ^ (p - 1) ∣ F - C c * E p (s : ZMod p) := by
    have h1 := dvd_mul_of_dvd_right (E_one_pow_mod p (by omega) s) (C c)
    have hsum := dvd_add hdiv_sub h1
    have heq : (F - C c * E p 1 ^ s) + C c * (E p 1 ^ s - E p (s : ZMod p)) =
        F - C c * E p (s : ZMod p) := by ring
    rwa [heq] at hsum
  -- Step 2: Differentiate to get X ^ (p - 2) ∣ F.derivative - C s * F
  have hF_deriv_Es : (X : (ZMod p)[X]) ^ (p - 2) ∣ F.derivative - C c * (E p (s : ZMod p)).derivative := by
    have h1 := dvd_derivative_of_X_pow_dvd p (hN_eq ▸ hdiv_Es)
    simpa [Polynomial.derivative_sub, Polynomial.derivative_C_mul] using h1
  have hF_deriv_F : (X : (ZMod p)[X]) ^ (p - 2) ∣ F.derivative - C (s : ZMod p) * F := by
    have h1 := dvd_mul_of_dvd_right (derivative_E_mod p (s : ZMod p)) (C c)
    have h2 : (X : (ZMod p)[X]) ^ (p - 2) ∣ F - C c * E p (s : ZMod p) :=
      dvd_trans (pow_dvd_pow X (by omega : p - 2 ≤ p - 1)) hdiv_Es
    have h3 := dvd_mul_of_dvd_right h2 (C (s : ZMod p))
    have hcomb := dvd_sub (dvd_add hF_deriv_Es h1) h3
    have heq : (F.derivative - C c * (E p (s : ZMod p)).derivative +
        C c * ((E p (s : ZMod p)).derivative - C (s : ZMod p) * E p (s : ZMod p))) -
        C (s : ZMod p) * (F - C c * E p (s : ZMod p)) =
        F.derivative - C (s : ZMod p) * F := by ring
    rwa [heq] at hcomb
  -- Step 3: Logarithmic derivative of F using truncated inverses R a := invMod (Q a) (p - 1)
  have hE1_c0 : (E p 1).coeff 0 = 1 := by
    have h0 : 0 < p - 1 := by omega
    simp [coeff_E, h0]
  have hE1_pow_c0 : ∀ i : ℕ, (E p 1 ^ i).coeff 0 = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, Polynomial.mul_coeff_zero, ih, hE1_c0, mul_one]
  have hQa_c0 : ∀ a : Fin m, (Q a).coeff 0 = ((a.val + 2 : ℕ) : ZMod p) := by
    intro a
    dsimp [Q]
    rw [Polynomial.finsetSum_coeff]
    simp [hE1_pow_c0]
  have hka_ne : ∀ a : Fin m, ((a.val + 2 : ℕ) : ZMod p) ≠ 0 := by
    intro a h
    have hdvd := (ZMod.natCast_eq_zero_iff (a.val + 2) p).mp h
    have hle := Nat.le_of_dvd (by omega) hdvd
    have ha := a.isLt
    omega
  let R : Fin m → (ZMod p)[X] := fun a => invMod p (Q a) (p - 1)
  have hQR : ∀ a : Fin m, (X : (ZMod p)[X]) ^ (p - 1) ∣ Q a * R a - 1 := fun a =>
    mul_invMod_mod p (by rw [hQa_c0 a]; exact hka_ne a) (p - 1)
  have hQR2 : ∀ a : Fin m, (X : (ZMod p)[X]) ^ (p - 2) ∣ Q a * R a - 1 := fun a =>
    dvd_trans (pow_dvd_pow X (by omega : p - 2 ≤ p - 1)) (hQR a)
  let L : (ZMod p)[X] :=
    ∑ a : Fin m, C ((2 * (e a).val : ℕ) : ZMod p) * (Q a).derivative * R a
  have hlogF : (X : (ZMod p)[X]) ^ (p - 2) ∣ F.derivative - F * L :=
    log_deriv_prod_mod p (p - 2) Finset.univ Q R (fun a => 2 * (e a).val) fun a _ => hQR2 a
  have hF_c0 : F.coeff 0 = c := by
    have h0 : (F - C c * E p (s : ZMod p)).coeff 0 = 0 :=
      Polynomial.X_pow_dvd_iff.mp hdiv_Es 0 (by omega)
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_E, if_pos (by omega)] at h0
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, mul_one] at h0
    exact sub_eq_zero.mp h0
  have hL_mod : (X : (ZMod p)[X]) ^ (p - 2) ∣ L - C (s : ZMod p) := by
    have hFL : (X : (ZMod p)[X]) ^ (p - 2) ∣ F * (L - C (s : ZMod p)) := by
      have hsub := dvd_sub hF_deriv_F hlogF
      have heq : (F.derivative - C (s : ZMod p) * F) - (F.derivative - F * L) =
          F * (L - C (s : ZMod p)) := by ring
      rwa [heq] at hsub
    have hFinv := mul_invMod_mod p (by rw [hF_c0]; exact hc) (p - 2)
    have h1 := dvd_mul_of_dvd_right hFL (invMod p F (p - 2))
    have h2 := dvd_mul_of_dvd_left hFinv (L - C (s : ZMod p))
    have hcomb := dvd_sub h1 h2
    have heq : invMod p F (p - 2) * (F * (L - C (s : ZMod p))) -
        (F * invMod p F (p - 2) - 1) * (L - C (s : ZMod p)) = L - C (s : ZMod p) := by ring
    rwa [heq] at hcomb
  -- Step 4: Identify X * (Q a)' * R a ≡ (B k_a + C k_a * X) - (B 1 + X) [mod X ^ (p - 2)]
  have hQa_log : ∀ a : Fin m,
      (X : (ZMod p)[X]) ^ (p - 2) ∣
        X * (Q a).derivative * R a -
          ((B p ((a.val + 2 : ℕ) : ZMod p) + C ((a.val + 2 : ℕ) : ZMod p) * X) -
            (B p 1 + X)) := by
    intro a
    set ka : ZMod p := ((a.val + 2 : ℕ) : ZMod p)
    have hQa_geom : Q a * (E p 1 - 1) = E p 1 ^ (a.val + 2) - 1 := by
      dsimp [Q]
      exact geom_sum_mul (E p 1) (a.val + 2)
    have hQa_Eka : (X : (ZMod p)[X]) ^ (p - 1) ∣ Q a * (E p 1 - 1) - (E p ka - 1) := by
      rw [hQa_geom]
      have h := E_one_pow_mod p (by omega) (a.val + 2)
      have heq : E p 1 ^ (a.val + 2) - 1 - (E p ka - 1) = E p 1 ^ (a.val + 2) - E p ka := by ring
      rwa [heq]
    -- Relate C ka * R a * B 1 to B ka mod X ^ (p - 2)
    have hRB_mod : (X : (ZMod p)[X]) ^ (p - 2) ∣ C ka * R a * B p 1 - B p ka := by
      apply dvd_of_X_mul_dvd p
      rw [← hN_eq]
      have h1 := dvd_mul_of_dvd_right hQa_Eka (R a * B p 1 * B p ka)
      have h2 := dvd_mul_of_dvd_right (hQR a) (B p 1 * (E p 1 - 1) * B p ka)
      have h3 := dvd_mul_of_dvd_right (B_mul_E_sub_one_mod p (by omega) 1) (B p ka)
      have h4 := dvd_mul_of_dvd_right (B_mul_E_sub_one_mod p (by omega) ka) (R a * B p 1)
      have hcomb := dvd_sub (dvd_add h4 h1) (dvd_add h2 h3)
      have heq :
          R a * B p 1 * (B p ka * (E p ka - 1) - C ka * X) +
            R a * B p 1 * B p ka * (Q a * (E p 1 - 1) - (E p ka - 1)) -
            (B p 1 * (E p 1 - 1) * B p ka * (Q a * R a - 1) +
              B p ka * (B p 1 * (E p 1 - 1) - C 1 * X)) =
            -(X * (C ka * R a * B p 1 - B p ka)) := by
        simp only [map_one, one_mul]
        ring
      rw [heq] at hcomb
      exact dvd_neg.mp hcomb
    -- Differentiate Q a * (E 1 - 1) ≡ E ka - 1 [mod X ^ (p - 1)]
    have hdiff : (X : (ZMod p)[X]) ^ (p - 2) ∣
        (Q a).derivative * (E p 1 - 1) + Q a * E p 1 - C ka * E p ka := by
      have hd1 : (X : (ZMod p)[X]) ^ (p - 2) ∣
          (Q a).derivative * (E p 1 - 1) + Q a * (E p 1).derivative - (E p ka).derivative := by
        have h := dvd_derivative_of_X_pow_dvd p (hN_eq ▸ hQa_Eka)
        simpa [Polynomial.derivative_sub, Polynomial.derivative_mul] using h
      have hd2 := dvd_mul_of_dvd_right (derivative_E_mod p 1) (Q a)
      have hd3 := derivative_E_mod p ka
      have hcomb := dvd_add (dvd_sub hd1 hd2) hd3
      have heq :
          ((Q a).derivative * (E p 1 - 1) + Q a * (E p 1).derivative - (E p ka).derivative -
            Q a * ((E p 1).derivative - C 1 * E p 1)) +
            ((E p ka).derivative - C ka * E p ka) =
          (Q a).derivative * (E p 1 - 1) + Q a * E p 1 - C ka * E p ka := by
        simp only [map_one, one_mul]
        ring
      rwa [heq] at hcomb
    -- Multiply hdiff by R a * B 1 and simplify each of the three terms mod X ^ (p - 2)
    have ht1 : (X : (ZMod p)[X]) ^ (p - 2) ∣
        (Q a).derivative * (E p 1 - 1) * (R a * B p 1) - X * (Q a).derivative * R a := by
      have h := dvd_trans (pow_dvd_pow X (by omega : p - 2 ≤ p - 1))
        (B_mul_E_sub_one_mod p (by omega) 1)
      have hm := dvd_mul_of_dvd_right h ((Q a).derivative * R a)
      have heq : (Q a).derivative * R a * (B p 1 * (E p 1 - 1) - C 1 * X) =
          (Q a).derivative * (E p 1 - 1) * (R a * B p 1) - X * (Q a).derivative * R a := by
        simp only [map_one, one_mul]
        ring
      rwa [heq] at hm
    have ht2 : (X : (ZMod p)[X]) ^ (p - 2) ∣
        Q a * E p 1 * (R a * B p 1) - (B p 1 + X) := by
      have h1 := dvd_mul_of_dvd_left (hQR2 a) (E p 1 * B p 1)
      have h2 := dvd_trans (pow_dvd_pow X (by omega : p - 2 ≤ p - 1))
        (B_mul_E_mod p (by omega) 1)
      have hsum := dvd_add h1 h2
      have heq : (Q a * R a - 1) * (E p 1 * B p 1) + (B p 1 * E p 1 - (B p 1 + C 1 * X)) =
          Q a * E p 1 * (R a * B p 1) - (B p 1 + X) := by
        simp only [map_one, one_mul]
        ring
      rwa [heq] at hsum
    have ht3 : (X : (ZMod p)[X]) ^ (p - 2) ∣
        C ka * E p ka * (R a * B p 1) - (B p ka + C ka * X) := by
      have h1 := dvd_mul_of_dvd_left hRB_mod (E p ka)
      have h2 := dvd_trans (pow_dvd_pow X (by omega : p - 2 ≤ p - 1))
        (B_mul_E_mod p (by omega) ka)
      have hsum := dvd_add h1 h2
      have heq : (C ka * R a * B p 1 - B p ka) * E p ka +
          (B p ka * E p ka - (B p ka + C ka * X)) =
          C ka * E p ka * (R a * B p 1) - (B p ka + C ka * X) := by ring
      rwa [heq] at hsum
    have hdiff_mul := dvd_mul_of_dvd_left hdiff (R a * B p 1)
    have hcomb := dvd_sub (dvd_add hdiff_mul ht3) (dvd_add ht1 ht2)
    have heq :
        (((Q a).derivative * (E p 1 - 1) + Q a * E p 1 - C ka * E p ka) * (R a * B p 1) +
          (C ka * E p ka * (R a * B p 1) - (B p ka + C ka * X))) -
          (((Q a).derivative * (E p 1 - 1) * (R a * B p 1) - X * (Q a).derivative * R a) +
            (Q a * E p 1 * (R a * B p 1) - (B p 1 + X))) =
        X * (Q a).derivative * R a - ((B p ka + C ka * X) - (B p 1 + X)) := by ring
    rwa [heq] at hcomb
  -- Step 5: Combine and extract the coefficient of X ^ (2 * (j.val + 1))
  let S_poly : (ZMod p)[X] :=
    ∑ a : Fin m, C ((2 * (e a).val : ℕ) : ZMod p) *
      ((B p ((a.val + 2 : ℕ) : ZMod p) + C ((a.val + 2 : ℕ) : ZMod p) * X) - (B p 1 + X))
  have hS_mod : (X : (ZMod p)[X]) ^ (p - 2) ∣ S_poly - C (s : ZMod p) * X := by
    have hXL : (X : (ZMod p)[X]) ^ (p - 2) ∣ X * L - C (s : ZMod p) * X := by
      have h := dvd_mul_of_dvd_right hL_mod X
      have heq : X * (L - C (s : ZMod p)) = X * L - C (s : ZMod p) * X := by ring
      rwa [heq] at h
    have hXL_S : (X : (ZMod p)[X]) ^ (p - 2) ∣ X * L - S_poly := by
      have hsum_eq : X * L - S_poly =
          ∑ a : Fin m, C ((2 * (e a).val : ℕ) : ZMod p) *
            (X * (Q a).derivative * R a -
              ((B p ((a.val + 2 : ℕ) : ZMod p) + C ((a.val + 2 : ℕ) : ZMod p) * X) -
                (B p 1 + X))) := by
        dsimp [L, S_poly]
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      rw [hsum_eq]
      exact Finset.dvd_sum fun a _ => dvd_mul_of_dvd_right (hQa_log a) _
    have hsub := dvd_sub hXL hXL_S
    have heq : (X * L - C (s : ZMod p) * X) - (X * L - S_poly) = S_poly - C (s : ZMod p) * X := by
      ring
    rwa [heq] at hsub
  set n := 2 * (j.val + 1)
  have hn_ge2 : 2 ≤ n := by omega
  have hn_lt : n < p - 2 := by
    have hj := j.isLt
    omega
  have hn_lt1 : n < p - 1 := by omega
  have hcoeff0 : (S_poly - C (s : ZMod p) * X).coeff n = 0 :=
    Polynomial.X_pow_dvd_iff.mp hS_mod n hn_lt
  have hX_coeff : ∀ z : ZMod p, (C z * (X : (ZMod p)[X])).coeff n = 0 := by
    intro z
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X, if_neg (by omega), mul_zero]
  have hX1_coeff : (X : (ZMod p)[X]).coeff n = 0 := by
    rw [Polynomial.coeff_X, if_neg (by omega)]
  rw [Polynomial.coeff_sub, hX_coeff, sub_zero] at hcoeff0
  have hS_coeff :
      S_poly.coeff n =
        ((2 : ZMod p) * (n.factorial : ZMod p)⁻¹ * red p (_root_.bernoulli n)) *
          ∑ a : Fin m, ((e a).val : ZMod p) *
            (((((a.val + 2 : ℕ) : ZMod p) ^ 2) ^ (j.val + 1)) - 1) := by
    dsimp [S_poly]
    rw [Polynomial.finsetSum_coeff, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_add,
      hX_coeff, hX1_coeff, add_zero, add_zero, coeff_B, coeff_B, if_pos hn_lt1, if_pos hn_lt1,
      one_pow, mul_one]
    have hpow : (((a.val + 2 : ℕ) : ZMod p) ^ n) =
        ((((a.val + 2 : ℕ) : ZMod p) ^ 2) ^ (j.val + 1)) := by
      rw [← pow_mul]
    rw [hpow]
    push_cast
    ring
  rw [hS_coeff] at hcoeff0
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have hle := Nat.le_of_dvd (by decide) hdvd
    omega
  have hfac_ne : (n.factorial : ZMod p)⁻¹ ≠ 0 :=
    inv_ne_zero (factorial_ne_zero_zmod p (by omega))
  have hden_ne : ((_root_.bernoulli n).den : ZMod p) ≠ 0 := by
    have hpd := p_not_dvd_den_of_PInt p (bernoulli_pInt p n hn_lt1)
    exact fun h => hpd ((ZMod.natCast_eq_zero_iff _ p).mp h)
  have hden_inv_ne : ((_root_.bernoulli n).den : ZMod p)⁻¹ ≠ 0 := inv_ne_zero hden_ne
  unfold red at hcoeff0
  have hfactor :
      ((2 : ZMod p) * (n.factorial : ZMod p)⁻¹ * ((_root_.bernoulli n).den : ZMod p)⁻¹) *
        (((_root_.bernoulli n).num : ZMod p) *
          ∑ a : Fin m, ((e a).val : ZMod p) *
            (((((a.val + 2 : ℕ) : ZMod p) ^ 2) ^ (j.val + 1)) - 1)) = 0 := by
    linear_combination hcoeff0
  have hpref_ne :
      (2 : ZMod p) * (n.factorial : ZMod p)⁻¹ * ((_root_.bernoulli n).den : ZMod p)⁻¹ ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2_ne hfac_ne) hden_inv_ne
  exact (mul_eq_zero.mp hfactor).resolve_left hpref_ne

end RegularPrimesH2

theorem OMA.solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2_H2_R1.H2 := by
  exact RegularPrimesH2.main_H2
