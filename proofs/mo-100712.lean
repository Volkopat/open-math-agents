import OMAStatements.S_mo_100712
import Mathlib

/- Peter Mueller gave the coefficient induction in his answer to MathOverflow 100712. -/

namespace OMA.P100712

variable {K : Type*} [Field K]

/-- `(q)_n` over an arbitrary field. -/
def poch (q : K) (n : ℕ) : K := ∏ i ∈ Finset.range n, (1 - q ^ (i + 1))

lemma poch_succ (q : K) (n : ℕ) : poch q (n + 1) = poch q n * (1 - q ^ (n + 1)) := by
  simp [poch, Finset.prod_range_succ]

lemma one_sub_ne (q : K) (hq : ∀ n : ℕ, q ^ (n + 1) ≠ 1) (n : ℕ) : 1 - q ^ (n + 1) ≠ 0 :=
  sub_ne_zero.mpr (hq n).symm

lemma poch_ne_zero (q : K) (hq : ∀ n : ℕ, q ^ (n + 1) ≠ 1) (n : ℕ) : poch q n ≠ 0 := by
  unfold poch
  rw [Finset.prod_ne_zero_iff]
  intro i _
  exact one_sub_ne q hq i

/-- The summand after removing the common power of `q`. -/
def h (q : K) (d : ℕ) (p : ℕ × ℕ) : K :=
  q ^ (p.1 * (d + p.1)) / (poch q p.1 * poch q p.2 * poch q (d + p.1))

lemma stepA (q : K) (hq : ∀ n : ℕ, q ^ (n + 1) ≠ 1) (d r s : ℕ) :
    q ^ s * (1 - q ^ (r + 1)) * h q d (r + 1, s) = q ^ (r + s + d + 1) * h q (d + 1) (r, s) := by
  have e : d + 1 + r = d + (r + 1) := by omega
  have h1 := poch_ne_zero q hq r
  have h2 := poch_ne_zero q hq s
  have h3 := poch_ne_zero q hq (d + (r + 1))
  have h4 := one_sub_ne q hq r
  simp only [h]
  rw [e, poch_succ]
  field_simp
  ring

lemma stepB (q : K) (hq : ∀ n : ℕ, q ^ (n + 1) ≠ 1) (d r s : ℕ) :
    (1 - q ^ (s + 1)) * h q d (r, s + 1) = h q d (r, s) := by
  have h1 := poch_ne_zero q hq r
  have h2 := poch_ne_zero q hq s
  have h3 := poch_ne_zero q hq (d + r)
  have h4 := one_sub_ne q hq s
  simp only [h]
  rw [poch_succ]
  field_simp

lemma key (q : K) (hq : ∀ n : ℕ, q ^ (n + 1) ≠ 1) (a : ℕ) : ∀ d : ℕ,
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal a, h q d p = 1 / (poch q a * poch q (a + d)) := by
  induction a with
  | zero =>
    intro d
    simp [h, poch]
  | succ a ih =>
    intro d
    have hA := ih (d + 1)
    have hB := ih d
    have hne := one_sub_ne q hq a
    have hne2 := one_sub_ne q hq (a + d)
    have hPa := poch_ne_zero q hq a
    have hPad := poch_ne_zero q hq (a + d)
    have hS1 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (a + 1), q ^ p.2 * (1 - q ^ p.1) * h q d p
        = q ^ (a + d + 1) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal a, h q (d + 1) p := by
      rw [Finset.Nat.sum_antidiagonal_succ, Finset.mul_sum]
      simp only [pow_zero, sub_self, mul_zero, zero_mul, zero_add]
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [stepA q hq, hp']
    have hS2 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (a + 1), (1 - q ^ p.2) * h q d p
        = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal a, h q d p := by
      rw [Finset.Nat.sum_antidiagonal_succ']
      simp only [pow_zero, sub_self, zero_mul, zero_add]
      apply Finset.sum_congr rfl
      intro p _
      rw [stepB q hq]
    have hsplit : (1 - q ^ (a + 1)) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (a + 1), h q d p
        = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (a + 1), q ^ p.2 * (1 - q ^ p.1) * h q d p
          + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (a + 1), (1 - q ^ p.2) * h q d p := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [← hp']
      ring
    rw [hS1, hS2, hA, hB] at hsplit
    apply mul_left_cancel₀ hne
    rw [hsplit]
    have e1 : a + (d + 1) = a + d + 1 := by omega
    have e2 : a + 1 + d = a + d + 1 := by omega
    rw [e1, e2, poch_succ q (a + d), poch_succ q a]
    field_simp
    ring

lemma coef_le (q : K) (hq : ∀ n : ℕ, q ^ (n + 1) ≠ 1) (a d : ℕ) :
    ∑ᶠ (p : ℕ × ℕ × ℕ) (_ : p.1 + p.2.1 = a ∧ p.2.1 + p.2.2 = a + d),
        q ^ (p.1 ^ 2 + p.1 * p.2.1 + p.2.1 ^ 2 + p.2.1 * p.2.2 + p.2.2 ^ 2) /
          (poch q p.1 * poch q p.2.1 * poch q p.2.2)
      = q ^ (a ^ 2 + (a + d) ^ 2 - a * (a + d)) / (poch q a * poch q (a + d)) := by
  have hbij : Set.BijOn (fun x : ℕ × ℕ => ((x.1, x.2, d + x.1) : ℕ × ℕ × ℕ))
      (↑(Finset.HasAntidiagonal.antidiagonal a) : Set (ℕ × ℕ))
      {p : ℕ × ℕ × ℕ | p.1 + p.2.1 = a ∧ p.2.1 + p.2.2 = a + d} := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hx' : x.1 + x.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_coe.mp hx)
      simp only [Set.mem_ofPred_eq]
      omega
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext hxy.1 hxy.2.1
    · rintro ⟨r, s, t⟩ ⟨h1, h2⟩
      simp only at h1 h2
      refine ⟨(r, s), Finset.mem_coe.mpr (Finset.HasAntidiagonal.mem_antidiagonal.mpr h1), ?_⟩
      have : d + r = t := by omega
      simp only [this]
  have hE : ∀ r s : ℕ, (r + s) ^ 2 + (r + s + d) ^ 2 - (r + s) * (r + s + d)
      = (r + s) ^ 2 + (r + s + d) * d := by
    intro r s
    apply Nat.sub_eq_of_eq_add
    ring
  calc ∑ᶠ (p : ℕ × ℕ × ℕ) (_ : p.1 + p.2.1 = a ∧ p.2.1 + p.2.2 = a + d),
        q ^ (p.1 ^ 2 + p.1 * p.2.1 + p.2.1 ^ 2 + p.2.1 * p.2.2 + p.2.2 ^ 2) /
          (poch q p.1 * poch q p.2.1 * poch q p.2.2)
      = ∑ᶠ p ∈ {p : ℕ × ℕ × ℕ | p.1 + p.2.1 = a ∧ p.2.1 + p.2.2 = a + d},
        q ^ (p.1 ^ 2 + p.1 * p.2.1 + p.2.1 ^ 2 + p.2.1 * p.2.2 + p.2.2 ^ 2) /
          (poch q p.1 * poch q p.2.1 * poch q p.2.2) := rfl
    _ = ∑ᶠ x ∈ (↑(Finset.HasAntidiagonal.antidiagonal a) : Set (ℕ × ℕ)),
        q ^ (x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2 + x.2 * (d + x.1) + (d + x.1) ^ 2) /
          (poch q x.1 * poch q x.2 * poch q (d + x.1)) :=
        (finsum_mem_eq_of_bijOn _ hbij (fun x _ => rfl)).symm
    _ = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal a,
        q ^ (x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2 + x.2 * (d + x.1) + (d + x.1) ^ 2) /
          (poch q x.1 * poch q x.2 * poch q (d + x.1)) := finsum_mem_coe_finset _ _
    _ = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal a,
        q ^ (a ^ 2 + (a + d) ^ 2 - a * (a + d)) * h q d x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        rw [← hx', hE]
        simp only [h]
        rw [mul_div_assoc', ← pow_add]
        congr 2
        ring
    _ = q ^ (a ^ 2 + (a + d) ^ 2 - a * (a + d)) / (poch q a * poch q (a + d)) := by
        rw [← Finset.mul_sum, key q hq a d, mul_one_div]

lemma coef_ge (q : K) (hq : ∀ n : ℕ, q ^ (n + 1) ≠ 1) (b d : ℕ) :
    ∑ᶠ (p : ℕ × ℕ × ℕ) (_ : p.1 + p.2.1 = b + d ∧ p.2.1 + p.2.2 = b),
        q ^ (p.1 ^ 2 + p.1 * p.2.1 + p.2.1 ^ 2 + p.2.1 * p.2.2 + p.2.2 ^ 2) /
          (poch q p.1 * poch q p.2.1 * poch q p.2.2)
      = q ^ ((b + d) ^ 2 + b ^ 2 - (b + d) * b) / (poch q (b + d) * poch q b) := by
  have hbij : Set.BijOn (fun x : ℕ × ℕ => ((d + x.1, x.2, x.1) : ℕ × ℕ × ℕ))
      (↑(Finset.HasAntidiagonal.antidiagonal b) : Set (ℕ × ℕ))
      {p : ℕ × ℕ × ℕ | p.1 + p.2.1 = b + d ∧ p.2.1 + p.2.2 = b} := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hx' : x.1 + x.2 = b := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_coe.mp hx)
      simp only [Set.mem_ofPred_eq]
      omega
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext hxy.2.2 hxy.2.1
    · rintro ⟨r, s, t⟩ ⟨h1, h2⟩
      simp only at h1 h2
      refine ⟨(t, s), Finset.mem_coe.mpr (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)), ?_⟩
      have : d + t = r := by omega
      simp only [this]
  have hE : ∀ r s : ℕ, (r + s + d) ^ 2 + (r + s) ^ 2 - (r + s + d) * (r + s)
      = (r + s) ^ 2 + (r + s + d) * d := by
    intro r s
    apply Nat.sub_eq_of_eq_add
    ring
  calc ∑ᶠ (p : ℕ × ℕ × ℕ) (_ : p.1 + p.2.1 = b + d ∧ p.2.1 + p.2.2 = b),
        q ^ (p.1 ^ 2 + p.1 * p.2.1 + p.2.1 ^ 2 + p.2.1 * p.2.2 + p.2.2 ^ 2) /
          (poch q p.1 * poch q p.2.1 * poch q p.2.2)
      = ∑ᶠ p ∈ {p : ℕ × ℕ × ℕ | p.1 + p.2.1 = b + d ∧ p.2.1 + p.2.2 = b},
        q ^ (p.1 ^ 2 + p.1 * p.2.1 + p.2.1 ^ 2 + p.2.1 * p.2.2 + p.2.2 ^ 2) /
          (poch q p.1 * poch q p.2.1 * poch q p.2.2) := rfl
    _ = ∑ᶠ x ∈ (↑(Finset.HasAntidiagonal.antidiagonal b) : Set (ℕ × ℕ)),
        q ^ ((d + x.1) ^ 2 + (d + x.1) * x.2 + x.2 ^ 2 + x.2 * x.1 + x.1 ^ 2) /
          (poch q (d + x.1) * poch q x.2 * poch q x.1) :=
        (finsum_mem_eq_of_bijOn _ hbij (fun x _ => rfl)).symm
    _ = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal b,
        q ^ ((d + x.1) ^ 2 + (d + x.1) * x.2 + x.2 ^ 2 + x.2 * x.1 + x.1 ^ 2) /
          (poch q (d + x.1) * poch q x.2 * poch q x.1) := finsum_mem_coe_finset _ _
    _ = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal b,
        q ^ ((b + d) ^ 2 + b ^ 2 - (b + d) * b) * h q d x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        rw [← hx', hE]
        simp only [h]
        rw [mul_div_assoc', ← pow_add]
        congr 1
        · congr 1
          ring
        · ring
    _ = q ^ ((b + d) ^ 2 + b ^ 2 - (b + d) * b) / (poch q (b + d) * poch q b) := by
        rw [← Finset.mul_sum, key q hq b d, mul_one_div, mul_comm (poch q b)]

lemma X_pow_ne_one (n : ℕ) : (RatFunc.X : RatFunc ℚ) ^ (n + 1) ≠ 1 := by
  intro hX
  have h2 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ (n + 1))
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) 1 := by
    rw [map_pow, RatFunc.algebraMap_X, map_one]
    exact hX
  have h3 := RatFunc.algebraMap_injective ℚ h2
  have h4 := congrArg Polynomial.natDegree h3
  simp at h4

lemma qPoch_eq (n : ℕ) : OMA.S_mo_100712.qPoch n = poch (RatFunc.X : RatFunc ℚ) n := rfl

end OMA.P100712

theorem OMA.solution : type_of% @OMA.S_mo_100712.main := by
  intro a b
  simp only [OMA.P100712.qPoch_eq]
  rcases le_total a b with hab | hab
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    exact OMA.P100712.coef_le _ OMA.P100712.X_pow_ne_one a d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    exact OMA.P100712.coef_ge _ OMA.P100712.X_pow_ne_one b d
