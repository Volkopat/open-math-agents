import OMAStatements.S_oeis_a326602
import Mathlib

namespace OMA.P_oeis_a326602

-- 1. Hockey-stick identity: ∑_{j=0}^k C(t + j, j) = C(t + 1 + k, k)
private lemma sum_choose_add (t k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), Nat.choose (t + j) j = Nat.choose (t + 1 + k) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show t + 1 + (k + 1) = (t + 1 + k) + 1 by omega,
      Nat.choose_succ_succ, show t + (k + 1) = t + 1 + k by omega]

-- 2. Explicit power series for 1 / (1 + X^d)^(t + 1)
private def invPowSeries (d t : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun r =>
    if d ∣ r then (-1 : ℤ) ^ (r / d) * (Nat.choose (t + r / d) (r / d) : ℤ) else 0

private lemma invPowSeries_zero_mul (d : ℕ) (hd : 0 < d) :
    invPowSeries d 0 * (1 + PowerSeries.X ^ d) = 1 := by
  ext m
  rw [mul_add, mul_one, map_add, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i j => PowerSeries.coeff i (invPowSeries d 0) * PowerSeries.coeff j (PowerSeries.X ^ d))]
  have hXd : ∀ j, PowerSeries.coeff j ((PowerSeries.X : PowerSeries ℤ) ^ d) = if j = d then 1 else 0 := by
    intro j
    rw [PowerSeries.coeff_X_pow]
  simp only [hXd, mul_ite, mul_one, mul_zero]
  by_cases hmd : m < d
  · have hsum0 : ∑ i ∈ Finset.range (m + 1), (if m - i = d then PowerSeries.coeff i (invPowSeries d 0) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      simp [show m - i ≠ d by omega]
    rw [hsum0, add_zero, PowerSeries.coeff_one]
    cases m with
    | zero => simp [invPowSeries]
    | succ m =>
      have hnd : ¬(d ∣ m + 1) := fun h => by
        have := Nat.le_of_dvd (Nat.succ_pos m) h; omega
      simp [invPowSeries, hnd]
  · push Not at hmd
    have hmem : m - d ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have hsum1 : ∑ i ∈ Finset.range (m + 1), (if m - i = d then PowerSeries.coeff i (invPowSeries d 0) else 0) =
        PowerSeries.coeff (m - d) (invPowSeries d 0) := by
      rw [Finset.sum_eq_single (m - d)]
      · simp [show m - (m - d) = d by omega]
      · intro i hi hne
        have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        simp [show m - i ≠ d by omega]
      · intro h; exact absurd hmem h
    rw [hsum1, PowerSeries.coeff_one, if_neg (by omega : m ≠ 0)]
    simp only [invPowSeries, PowerSeries.coeff_mk, zero_add, Nat.choose_self, Nat.cast_one, mul_one]
    by_cases hdvd : d ∣ m
    · obtain ⟨q, rfl⟩ := hdvd
      cases q with
      | zero => simp at hmd; omega
      | succ q =>
        have hsub : d * (q + 1) - d = d * q := by simp [Nat.mul_succ]
        rw [hsub]
        simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_right _ hd, pow_succ]
        ring
    · have hnd : ¬(d ∣ m - d) := by
        intro ⟨q, hq⟩
        apply hdvd
        exact ⟨q + 1, by rw [Nat.mul_succ]; omega⟩
      simp [hdvd, hnd]

private lemma invPowSeries_succ (d t : ℕ) (hd : 0 < d) :
    invPowSeries d (t + 1) = invPowSeries d t * invPowSeries d 0 := by
  ext m
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i j => PowerSeries.coeff i (invPowSeries d t) * PowerSeries.coeff j (invPowSeries d 0))]
  simp only [invPowSeries, PowerSeries.coeff_mk, zero_add, Nat.choose_self, Nat.cast_one, mul_one]
  by_cases hdvd : d ∣ m
  · obtain ⟨q, rfl⟩ := hdvd
    simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_right _ hd]
    -- Only i = d * j for j ∈ range (q + 1) are nonzero!
    have hsub : (Finset.range (q + 1)).image (fun j => d * j) ⊆ Finset.range (d * q + 1) := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      have hjq : j ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact Finset.mem_range.mpr (by nlinarith)
    have hsum : ∑ i ∈ Finset.range (d * q + 1),
          (if d ∣ i then (-1 : ℤ) ^ (i / d) * (Nat.choose (t + i / d) (i / d) : ℤ) else 0) *
          (if d ∣ d * q - i then (-1 : ℤ) ^ ((d * q - i) / d) else 0) =
        ∑ j ∈ Finset.range (q + 1), (-1 : ℤ) ^ q * (Nat.choose (t + j) j : ℤ) := by
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hd hab)]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjq : j ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hdiff : d * q - d * j = d * (q - j) := (Nat.mul_sub_left_distrib d q j).symm
        rw [hdiff]
        simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_right _ hd]
        have hpow : (-1 : ℤ) ^ j * (-1 : ℤ) ^ (q - j) = (-1 : ℤ) ^ q := by
          rw [← pow_add, Nat.add_sub_of_le hjq]
        calc (-1 : ℤ) ^ j * (Nat.choose (t + j) j : ℤ) * (-1 : ℤ) ^ (q - j)
            = ((-1 : ℤ) ^ j * (-1 : ℤ) ^ (q - j)) * (Nat.choose (t + j) j : ℤ) := by ring
          _ = (-1 : ℤ) ^ q * (Nat.choose (t + j) j : ℤ) := by rw [hpow]
      · intro i hi hni
        have him : i ≤ d * q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hnd : ¬(d ∣ i) := by
          intro ⟨j, hj⟩
          apply hni
          refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr ?_, hj.symm⟩
          have : j ≤ q := Nat.le_of_mul_le_mul_left (hj ▸ him) hd
          omega
        simp [hnd]
    rw [hsum, ← Finset.mul_sum, ← Nat.cast_sum, sum_choose_add]
  · simp only [hdvd, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases h1 : d ∣ i
    · have h2 : ¬(d ∣ m - i) := by
        intro ⟨q2, hq2⟩; obtain ⟨q1, hq1⟩ := h1
        apply hdvd; exact ⟨q1 + q2, by rw [mul_add]; omega⟩
      simp [h1, h2]
    · simp [h1]

-- 3. Trinomial symmetry and central binomial evenness
private lemma choose_add_mul_fact (x y : ℕ) :
    Nat.choose (x + y) x * (Nat.factorial x * Nat.factorial y) = Nat.factorial (x + y) := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right x y)
  rw [Nat.add_sub_cancel_left, mul_assoc] at h
  exact h

private lemma trinom_symm (a b c : ℕ) :
    Nat.choose (a + b) a * Nat.choose (a + b + c) c =
    Nat.choose (a + c) a * Nat.choose (a + c + b) b := by
  have h1 := choose_add_mul_fact a b
  have h2 : Nat.choose (a + b + c) c * (Nat.factorial c * Nat.factorial (a + b)) =
      Nat.factorial (a + b + c) := by
    simpa [add_comm] using choose_add_mul_fact c (a + b)
  have h3 := choose_add_mul_fact a c
  have h4 : Nat.choose (a + c + b) b * (Nat.factorial b * Nat.factorial (a + c)) =
      Nat.factorial (a + c + b) := by
    simpa [add_comm] using choose_add_mul_fact b (a + c)
  have hpos : 0 < Nat.factorial a * Nat.factorial b * Nat.factorial c := by positivity
  have hL : (Nat.choose (a + b) a * Nat.choose (a + b + c) c) *
      (Nat.factorial a * Nat.factorial b * Nat.factorial c) = Nat.factorial (a + b + c) := by
    calc (Nat.choose (a + b) a * Nat.choose (a + b + c) c) *
          (Nat.factorial a * Nat.factorial b * Nat.factorial c)
        = Nat.choose (a + b + c) c * (Nat.factorial c * (Nat.choose (a + b) a * (Nat.factorial a * Nat.factorial b))) := by ring
      _ = Nat.choose (a + b + c) c * (Nat.factorial c * Nat.factorial (a + b)) := by rw [h1]
      _ = Nat.factorial (a + b + c) := h2
  have hR : (Nat.choose (a + c) a * Nat.choose (a + c + b) b) *
      (Nat.factorial a * Nat.factorial b * Nat.factorial c) = Nat.factorial (a + b + c) := by
    calc (Nat.choose (a + c) a * Nat.choose (a + c + b) b) *
          (Nat.factorial a * Nat.factorial b * Nat.factorial c)
        = Nat.choose (a + c + b) b * (Nat.factorial b * (Nat.choose (a + c) a * (Nat.factorial a * Nat.factorial c))) := by ring
      _ = Nat.choose (a + c + b) b * (Nat.factorial b * Nat.factorial (a + c)) := by rw [h3]
      _ = Nat.factorial (a + c + b) := h4
      _ = Nat.factorial (a + b + c) := by rw [show a + c + b = a + b + c by omega]
  exact Nat.eq_of_mul_eq_mul_right hpos (hL.trans hR.symm)

private lemma trinom_diag_even (a b : ℕ) (hb : 0 < b) :
    2 ∣ Nat.choose (a + b) a * Nat.choose (a + b + b) b := by
  have h1 : Nat.choose (a + b) a * Nat.choose (a + b + b) b =
      Nat.choose (a + 2 * b) a * Nat.choose (2 * b) b := by
    have hL : (Nat.choose (a + b) a * Nat.choose (a + b + b) b) *
        (Nat.factorial a * Nat.factorial b * Nat.factorial b) = Nat.factorial (a + 2 * b) := by
      have ha1 := choose_add_mul_fact a b
      have ha2 : Nat.choose (a + b + b) b * (Nat.factorial b * Nat.factorial (a + b)) =
          Nat.factorial (a + b + b) := by
        simpa [add_comm] using choose_add_mul_fact b (a + b)
      calc (Nat.choose (a + b) a * Nat.choose (a + b + b) b) *
            (Nat.factorial a * Nat.factorial b * Nat.factorial b)
          = Nat.choose (a + b + b) b * (Nat.factorial b * (Nat.choose (a + b) a * (Nat.factorial a * Nat.factorial b))) := by ring
        _ = Nat.choose (a + b + b) b * (Nat.factorial b * Nat.factorial (a + b)) := by rw [ha1]
        _ = Nat.factorial (a + b + b) := ha2
        _ = Nat.factorial (a + 2 * b) := by rw [show a + b + b = a + 2 * b by omega]
    have hR : (Nat.choose (a + 2 * b) a * Nat.choose (2 * b) b) *
        (Nat.factorial a * Nat.factorial b * Nat.factorial b) = Nat.factorial (a + 2 * b) := by
      have hb1 : Nat.choose (2 * b) b * (Nat.factorial b * Nat.factorial b) = Nat.factorial (2 * b) := by
        simpa [two_mul] using choose_add_mul_fact b b
      have hb2 := choose_add_mul_fact a (2 * b)
      calc (Nat.choose (a + 2 * b) a * Nat.choose (2 * b) b) *
            (Nat.factorial a * Nat.factorial b * Nat.factorial b)
          = Nat.choose (a + 2 * b) a * (Nat.factorial a * (Nat.choose (2 * b) b * (Nat.factorial b * Nat.factorial b))) := by ring
        _ = Nat.choose (a + 2 * b) a * (Nat.factorial a * Nat.factorial (2 * b)) := by rw [hb1]
        _ = Nat.factorial (a + 2 * b) := hb2
    have hpos : 0 < Nat.factorial a * Nat.factorial b * Nat.factorial b := by positivity
    exact Nat.eq_of_mul_eq_mul_right hpos (hL.trans hR.symm)
  rw [h1]
  have h2b : 2 ∣ Nat.choose (2 * b) b := by
    cases b with
    | zero => omega
    | succ b =>
      have hsym : Nat.choose (2 * b + 1) (b + 1) = Nat.choose (2 * b + 1) b := by
        rw [← Nat.choose_symm (by omega : b ≤ 2 * b + 1), show 2 * b + 1 - b = b + 1 by omega]
      have h2 : Nat.choose (2 * (b + 1)) (b + 1) = 2 * Nat.choose (2 * b + 1) b := by
        rw [show 2 * (b + 1) = (2 * b + 1) + 1 by omega, Nat.choose_succ_succ, hsym, ← two_mul]
      exact ⟨Nat.choose (2 * b + 1) b, h2⟩
  exact dvd_mul_of_dvd_right h2b _

-- 4. Symmetric double sum in ZMod 2 collapses to the diagonal!
private lemma sum_symm_zmod2 {S : Finset ℕ} (f : ℕ → ℕ → ZMod 2)
    (hsymm : ∀ b c, f b c = f c b) :
    ∑ b ∈ S, ∑ c ∈ S, f b c = ∑ b ∈ S, f b b := by
  have hchar : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [← Finset.sum_product']
  have hpart : S ×ˢ S =
      ((S ×ˢ S).filter (fun p => p.1 = p.2)) ∪
      (((S ×ˢ S).filter (fun p => p.1 < p.2)) ∪ ((S ×ˢ S).filter (fun p => p.2 < p.1))) := by
    ext ⟨b, c⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · intro h
      rcases lt_trichotomy b c with hlt | heq | hgt
      · exact Or.inr (Or.inl ⟨h, hlt⟩)
      · exact Or.inl ⟨h, heq⟩
      · exact Or.inr (Or.inr ⟨h, hgt⟩)
    · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hd1 : Disjoint ((S ×ˢ S).filter (fun p => p.1 = p.2))
      (((S ×ˢ S).filter (fun p => p.1 < p.2)) ∪ ((S ×ˢ S).filter (fun p => p.2 < p.1))) := by
    rw [Finset.disjoint_left]
    intro ⟨b, c⟩ h1 h2
    simp only [Finset.mem_filter, Finset.mem_union] at h1 h2
    rcases h2 with ⟨_, hlt⟩ | ⟨_, hgt⟩ <;> omega
  have hd2 : Disjoint ((S ×ˢ S).filter (fun p => p.1 < p.2))
      ((S ×ˢ S).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    intro ⟨b, c⟩ h1 h2
    simp only [Finset.mem_filter] at h1 h2; omega
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2]
  have hswap : ∑ p ∈ (S ×ˢ S).filter (fun p => p.2 < p.1), f p.1 p.2 =
      ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 < p.2), f p.1 p.2 := by
    refine Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
    · intro ⟨b, c⟩ h; simp only [Finset.mem_filter, Finset.mem_product] at h ⊢; exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · intro ⟨b, c⟩ h; simp only [Finset.mem_filter, Finset.mem_product] at h ⊢; exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · intro ⟨b, c⟩ _; rfl
    · intro ⟨b, c⟩ _; rfl
    · intro ⟨b, c⟩ _; exact hsymm b c
  rw [hswap, hchar, add_zero]
  refine Finset.sum_nbij' (fun p => p.1) (fun b => (b, b)) ?_ ?_ ?_ ?_ ?_
  · intro ⟨b, c⟩ h; simp only [Finset.mem_filter, Finset.mem_product] at h; exact h.1.1
  · intro b hb; simp [hb]
  · intro ⟨b, c⟩ h; simp only [Finset.mem_filter] at h; exact Prod.ext rfl h.2
  · intro b _; rfl
  · intro ⟨b, c⟩ h; simp only [Finset.mem_filter] at h; rw [h.2]

private def exp3 (a b c : ℕ) : ℕ :=
  2 * a ^ 2 + 2 * a * (b + c) + 2 * b * c + b + c

private theorem main_proved :
    ∀ (a : ℕ → ℤ) (U : ℕ → PowerSeries ℤ),
      (∀ n : ℕ, U n * (1 + PowerSeries.X ^ (2 * n + 1)) = 1) →
      (∀ k : ℕ,
        a k =
          ∑ n ∈ Finset.range (2 * k + 1),
            PowerSeries.coeff (2 * k)
              ((PowerSeries.X ^ (2 * n) + PowerSeries.X) ^ n * U n ^ (n + 1))) →
      ∀ n : ℕ, Odd (a n) ↔ IsSquare n := by
  intro a U hU ha k
  -- Identify U n ^ (n + 1) = invPowSeries (2 * n + 1) n
  have hU_eq : ∀ n : ℕ, U n = invPowSeries (2 * n + 1) 0 := by
    intro n
    have h1 := invPowSeries_zero_mul (2 * n + 1) (by omega)
    calc U n = U n * ((1 + PowerSeries.X ^ (2 * n + 1)) * invPowSeries (2 * n + 1) 0) := by
            rw [mul_comm (1 + PowerSeries.X ^ (2 * n + 1)), h1, mul_one]
      _ = (U n * (1 + PowerSeries.X ^ (2 * n + 1))) * invPowSeries (2 * n + 1) 0 := by ring
      _ = invPowSeries (2 * n + 1) 0 := by rw [hU n, one_mul]
  have hUpow : ∀ n t : ℕ, U n ^ (t + 1) = invPowSeries (2 * n + 1) t := by
    intro n t
    induction t with
    | zero => simp [hU_eq n]
    | succ t iht =>
      rw [pow_succ, iht, hU_eq n, invPowSeries_succ (2 * n + 1) t (by omega)]
  -- Expand coeff m ((X^(2*n) + X)^n * U n ^ (n + 1))!
  set m := 2 * k
  have hterm : ∀ n : ℕ,
      PowerSeries.coeff m ((PowerSeries.X ^ (2 * n) + PowerSeries.X) ^ n * U n ^ (n + 1)) =
      ∑ j ∈ Finset.range (n + 1),
        ∑ c ∈ Finset.range (m + 1),
          if exp3 j (n - j) c = m then
            (-1 : ℤ) ^ c * (Nat.choose n j : ℤ) * (Nat.choose (n + c) c : ℤ)
          else 0 := by
    intro n
    rw [hUpow n n, add_pow, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : (PowerSeries.X ^ (2 * n) : PowerSeries ℤ) ^ j * PowerSeries.X ^ (n - j) *
        (Nat.choose n j : PowerSeries ℤ) =
        PowerSeries.C (Nat.choose n j : ℤ) * PowerSeries.X ^ (2 * n * j + (n - j)) := by
      rw [← pow_mul, ← pow_add, show (Nat.choose n j : PowerSeries ℤ) = PowerSeries.C (Nat.choose n j : ℤ) by
        rw [map_natCast]]
      ring
    rw [hpow, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    split_ifs with hle
    · simp only [invPowSeries, PowerSeries.coeff_mk]
      by_cases hdvd : (2 * n + 1) ∣ (m - (2 * n * j + (n - j)))
      · obtain ⟨c0, hc0⟩ := hdvd
        have hc0_le : c0 ≤ m := by
          have : c0 ≤ (2 * n + 1) * c0 := Nat.le_mul_of_pos_left c0 (by omega)
          omega
        have hexp_eq : ∀ c, exp3 j (n - j) c = m ↔ c = c0 := by
          intro c
          have h1 : exp3 j (n - j) c = 2 * n * j + (n - j) + (2 * n + 1) * c := by
            have : j + (n - j) = n := Nat.add_sub_cancel' hjn
            simp only [exp3]
            zify [hjn]
            ring
          rw [h1]
          constructor
          · intro h
            have : (2 * n + 1) * c = (2 * n + 1) * c0 := by omega
            exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n + 1) this
          · intro h; subst h; omega
        rw [Finset.sum_eq_single c0]
        · simp only [(hexp_eq c0).mpr rfl, ↓reduceIte, hc0, dvd_mul_right,
            Nat.mul_div_right _ (by omega : 0 < 2 * n + 1)]
          ring
        · intro c _ hne; simp [(hexp_eq c).not.mpr hne]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · simp only [hdvd, ↓reduceIte, mul_zero]
        symm
        refine Finset.sum_eq_zero fun c _ => ?_
        have hne : exp3 j (n - j) c ≠ m := by
          intro h
          have h1 : exp3 j (n - j) c = 2 * n * j + (n - j) + (2 * n + 1) * c := by
            simp only [exp3]; zify [hjn]; ring
          apply hdvd; exact ⟨c, by omega⟩
        simp [hne]
    · simp only [mul_zero]
      symm
      refine Finset.sum_eq_zero fun c _ => ?_
      have hne : exp3 j (n - j) c ≠ m := by
        intro h
        have h1 : exp3 j (n - j) c = 2 * n * j + (n - j) + (2 * n + 1) * c := by
          simp only [exp3]; zify [hjn]; ring
        omega
      simp [hne]
  -- Cast a k to ZMod 2!
  have ha_z2 : ((a k : ℤ) : ZMod 2) =
      ∑ x ∈ Finset.range (m + 1),
        ∑ b ∈ Finset.range (m + 1),
          ∑ c ∈ Finset.range (m + 1),
            if exp3 x b c = m then
              ((Nat.choose (x + b) x * Nat.choose (x + b + c) c : ℕ) : ZMod 2)
            else 0 := by
    rw [ha k]
    change ((∑ n ∈ Finset.range (m + 1),
      PowerSeries.coeff m ((PowerSeries.X ^ (2 * n) + PowerSeries.X) ^ n * U n ^ (n + 1)) : ℤ) : ZMod 2) = _
    rw [Int.cast_sum]
    rw [Finset.sum_congr rfl (fun n _ => by rw [hterm n])]
    -- Reindex (n, j) with j ≤ n ≤ m to (x, b) with x + b ≤ m (x = j, b = n - j)
    have hreidx : ∀ n ∈ Finset.range (m + 1),
        ((∑ j ∈ Finset.range (n + 1),
            ∑ c ∈ Finset.range (m + 1),
              if exp3 j (n - j) c = m then
                (-1 : ℤ) ^ c * (Nat.choose n j : ℤ) * (Nat.choose (n + c) c : ℤ)
              else 0 : ℤ) : ZMod 2) =
        ∑ j ∈ Finset.range (n + 1),
          ∑ c ∈ Finset.range (m + 1),
            if exp3 j (n - j) c = m then
              ((Nat.choose n j * Nat.choose (n + c) c : ℕ) : ZMod 2)
            else 0 := by
      intro n _
      simp only [Int.cast_sum, apply_ite (Int.cast : ℤ → ZMod 2), Int.cast_zero, Int.cast_mul,
        Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.cast_mul]
      have hm1 : (-1 : ZMod 2) = 1 := by decide
      simp only [hm1, one_pow, one_mul]
    rw [Finset.sum_congr rfl hreidx]
    -- Collapse double sum over n ∈ range (m+1), j ∈ range (n+1) to x ∈ range (m+1), b ∈ range (m+1)
    let g : ℕ → ℕ → ZMod 2 := fun x b =>
      ∑ c ∈ Finset.range (m + 1),
        if exp3 x b c = m then
          ((Nat.choose (x + b) x * Nat.choose (x + b + c) c : ℕ) : ZMod 2)
        else 0
    have hzero_big : ∀ x b, m < x + b → g x b = 0 := by
      intro x b hxb
      refine Finset.sum_eq_zero fun c _ => ?_
      have hne : exp3 x b c ≠ m := by
        simp only [exp3]
        have hx2 : x ≤ 2 * x ^ 2 := by nlinarith
        omega
      simp [hne]
    calc (∑ n ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ c ∈ Finset.range (m + 1),
              (if exp3 j (n - j) c = m then
                ((Nat.choose n j * Nat.choose (n + c) c : ℕ) : ZMod 2)
              else 0))
        = ∑ n ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), g j (n - j) := by
          refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j hj => ?_
          have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          simp only [g, Nat.add_sub_cancel' hjn]
      _ = ∑ p ∈ (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter (fun p => p.1 + p.2 ≤ m),
            g p.1 p.2 := by
          rw [Finset.sum_sigma']
          refine Finset.sum_nbij' (fun p => (p.2, p.1 - p.2)) (fun q => ⟨q.1 + q.2, q.1⟩)
            ?_ ?_ ?_ ?_ ?_
          · intro ⟨n, j⟩ h
            simp only [Finset.mem_sigma, Finset.mem_range] at h
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            omega
          · intro ⟨x, b⟩ h
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
            simp only [Finset.mem_sigma, Finset.mem_range]
            omega
          · intro ⟨n, j⟩ h
            simp only [Finset.mem_sigma, Finset.mem_range] at h
            exact Sigma.ext (by dsimp only; omega) (heq_of_eq rfl)
          · intro ⟨x, b⟩ _
            dsimp only
            exact Prod.ext rfl (by omega)
          · intro ⟨n, j⟩ _; rfl
      _ = ∑ p ∈ Finset.range (m + 1) ×ˢ Finset.range (m + 1), g p.1 p.2 := by
          refine Finset.sum_subset (Finset.filter_subset _ _) fun ⟨x, b⟩ _ hnot => ?_
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, not_and, not_le] at hnot
          exact hzero_big x b (by
            by_contra hle; push Not at hle
            exact absurd hle (by
              have := hnot ⟨Finset.mem_range.mp (Finset.mem_product.mp ‹_›).1,
                Finset.mem_range.mp (Finset.mem_product.mp ‹_›).2⟩; omega))
      _ = ∑ x ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), g x b := Finset.sum_product' _ _ _
  -- Collapse the (b, c) double sum to diagonal b = c, then b = 0!
  have hdiag : ∀ x ∈ Finset.range (m + 1),
      (∑ b ∈ Finset.range (m + 1), ∑ c ∈ Finset.range (m + 1),
        if exp3 x b c = m then
          ((Nat.choose (x + b) x * Nat.choose (x + b + c) c : ℕ) : ZMod 2)
        else 0) =
      if 2 * x ^ 2 = m then (1 : ZMod 2) else 0 := by
    intro x _
    rw [sum_symm_zmod2]
    · rw [Finset.sum_eq_single 0]
      · simp [exp3]
      · intro b _ hb0
        have h2dvd := trinom_diag_even x b (Nat.pos_of_ne_zero hb0)
        have hz : ((Nat.choose (x + b) x * Nat.choose (x + b + b) b : ℕ) : ZMod 2) = 0 :=
          (ZMod.natCast_eq_zero_iff _ 2).mpr h2dvd
        simp [hz]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h
    · intro b c
      have he : exp3 x b c = exp3 x c b := by simp only [exp3]; ring
      rw [he, trinom_symm x b c]
  rw [Finset.sum_congr rfl hdiag] at ha_z2
  -- Evaluate ∑_{x ≤ 2k} (if 2*x^2 = 2*k then 1 else 0) in ZMod 2!
  have hodd_iff : Odd (a k) ↔ ((a k : ℤ) : ZMod 2) = 1 := by
    constructor
    · rintro ⟨r, hr⟩
      rw [hr]; push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul, zero_add]
    · intro h
      have hne0 : ((a k : ℤ) : ZMod 2) ≠ 0 := by rw [h]; decide
      have hndvd : ¬((2 : ℤ) ∣ a k) := fun hd => hne0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hd)
      have hmod : a k % 2 = 1 := by omega
      exact ⟨a k / 2, by omega⟩
  rw [hodd_iff, ha_z2]
  constructor
  · intro h1
    by_contra hnsq
    have hsum0 : (∑ x ∈ Finset.range (m + 1), if 2 * x ^ 2 = m then (1 : ZMod 2) else 0) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      have hne : 2 * x ^ 2 ≠ m := by
        intro heq; apply hnsq; refine ⟨x, ?_⟩
        have hm : m = 2 * k := rfl
        nlinarith
      simp [hne]
    rw [hsum0] at h1
    exact absurd h1 (by decide)
  · rintro ⟨r, hr⟩
    have hm : m = 2 * k := rfl
    have hrm : r ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by nlinarith)
    rw [Finset.sum_eq_single r]
    · simp [m, hr, sq]
    · intro x _ hxr
      have hne : 2 * x ^ 2 ≠ m := by
        intro heq
        have : x ^ 2 = r ^ 2 := by nlinarith
        exact hxr (by nlinarith)
      simp [hne]
    · intro h; exact absurd hrm h

end OMA.P_oeis_a326602

theorem OMA.solution : type_of% @OMA.S_oeis_a326602.main :=
  OMA.P_oeis_a326602.main_proved
