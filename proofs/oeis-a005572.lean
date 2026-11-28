import OMAStatements.S_oeis_a005572
import Mathlib

namespace A005572

open Finset PowerSeries OMA.S_oeis_a005572

lemma a_succ_succ (n : ℕ) :
    a (n + 2) = 4 * a (n + 1) + ∑ i ∈ range (n + 1), a i * a (n - i) := by
  rw [a]
  congr 1
  exact Finset.sum_attach (range (n + 1)) (fun i => a i * a (n - i))

lemma alg_key {R : Type*} [CommRing R] (x d e c g : R) (hd : d = 1 - 2 * x) (hde : e * d = 1)
    (hc : c ^ 2 * (x * e) + 1 = c) (hg : g = e * c ^ 2) :
    g = 1 + x * (4 * g) + x ^ 2 * (g * g) := by
  subst hd
  have hXG : x * g = c - 1 := by rw [hg]; linear_combination hc
  have hDG : (1 - 2 * x) * g = c ^ 2 := by rw [hg]; linear_combination c ^ 2 * hde
  have hX : x * c ^ 2 = (1 - 2 * x) * (c - 1) := by
    linear_combination (1 - 2 * x) * hXG - x * hDG
  have h3 : (1 - 2 * x) * (c ^ 2 + 2 * c - 2) = c ^ 2 := by linear_combination (-2) * hX
  have h4 : g = c ^ 2 + 2 * c - 2 := by
    linear_combination e * (hDG - h3) - (g - (c ^ 2 + 2 * c - 2)) * hde
  linear_combination h4 - (4 + x * g + c - 1) * hXG

lemma uniq (F : PowerSeries ℚ) (hF : F = 1 + X * (4 * F) + X ^ 2 * (F * F)) :
    ∀ n, coeff n F = (a n : ℚ) := by
  have h4 : (4 : PowerSeries ℚ) = C (4 : ℚ) :=
    (map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm
  have h0 : coeff 0 F = 1 := by
    have h := congrArg (coeff 0) hF
    simp at h
    simpa using h
  have h1 : coeff 1 F = 4 := by
    have h := congrArg (coeff 1) hF
    rw [map_add, map_add, h4, coeff_one, coeff_succ_X_mul, coeff_C_mul, h0,
      coeff_X_pow_mul'] at h
    simpa using h
  have hn : ∀ n, coeff (n + 2) F =
      4 * coeff (n + 1) F + ∑ p ∈ antidiagonal n, coeff p.1 F * coeff p.2 F := by
    intro n
    have h := congrArg (coeff (n + 2)) hF
    rw [map_add, map_add, h4, coeff_succ_X_mul, coeff_C_mul, coeff_X_pow_mul, coeff_mul,
      coeff_one, if_neg (by omega)] at h
    rw [h]
    ring
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [h0]; simp [a]
    | 1, _ => rw [h1]; simp [a]
    | n + 2, ih =>
      have hs : ∑ p ∈ antidiagonal n, coeff p.1 F * coeff p.2 F =
          ∑ k ∈ range (n + 1), (a k : ℚ) * (a (n - k) : ℚ) := by
        rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => (a i : ℚ) * (a j : ℚ)) n]
        apply Finset.sum_congr rfl
        intro p hp
        have hp1 : p.1 + p.2 = n := by simpa using hp
        rw [ih p.1 (by omega), ih p.2 (by omega)]
      rw [hn n, a_succ_succ, ih (n + 1) (by omega), hs]
      push_cast
      rfl

lemma catalan_eq : catalanGF ^ 2 * X + 1 = catalanGF := by
  have h := congrArg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  simpa [catalanGF] using h

lemma den_inv : denominator⁻¹ * denominator = 1 := by
  apply PowerSeries.inv_mul_cancel
  simp [denominator]

lemma hasSubst_inner : HasSubst innerSeries := by
  apply HasSubst.of_constantCoeff_zero'
  simp [innerSeries]

lemma comp_eq :
    catalanComposition ^ 2 * (X * denominator⁻¹) + 1 = catalanComposition := by
  have h := congrArg (fun f => f.subst innerSeries) catalan_eq
  rw [subst_add hasSubst_inner, subst_mul hasSubst_inner, subst_pow hasSubst_inner,
    subst_X hasSubst_inner] at h
  have h1 : (1 : PowerSeries ℚ).subst innerSeries = (1 : PowerSeries ℚ) := by
    rw [← coe_substAlgHom hasSubst_inner]
    exact map_one _
  rw [h1] at h
  exact h

lemma gf_eq : generatingSeries = denominator⁻¹ * catalanComposition ^ 2 := by
  have hG := alg_key (X : PowerSeries ℚ) denominator denominator⁻¹ catalanComposition
    (denominator⁻¹ * catalanComposition ^ 2) rfl den_inv comp_eq rfl
  ext n
  rw [uniq _ hG n]
  simp [generatingSeries]

lemma sym_even (f : ℕ → ℕ) (m : ℕ) :
    Even (∑ i ∈ range (2 * m + 2), f i * f (2 * m + 1 - i)) := by
  have e : 2 * m + 2 = (m + 1) + (m + 1) := by ring
  rw [e, Finset.sum_range_add]
  have h2 : ∑ x ∈ range (m + 1), f (m + 1 + x) * f (2 * m + 1 - (m + 1 + x)) =
      ∑ x ∈ range (m + 1), f x * f (2 * m + 1 - x) := by
    rw [← Finset.sum_range_reflect (fun x => f x * f (2 * m + 1 - x)) (m + 1)]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Finset.mem_range.mp hx
    have e1 : m + 1 - 1 - x = m - x := by omega
    have e2 : 2 * m + 1 - (m + 1 + x) = m - x := by omega
    have e3 : 2 * m + 1 - (m - x) = m + 1 + x := by omega
    simp only [e1, e2, e3]
    ring
  rw [h2]
  exact ⟨_, rfl⟩

lemma sym_odd (f : ℕ → ℕ) (m : ℕ) :
    ∑ i ∈ range (2 * m + 1), f i * f (2 * m - i) =
      2 * ∑ i ∈ range m, f i * f (2 * m - i) + f m * f m := by
  have e : 2 * m + 1 = m + (m + 1) := by ring
  rw [e, Finset.sum_range_add, Finset.sum_range_succ']
  have h2 : ∑ x ∈ range m, f (m + (x + 1)) * f (2 * m - (m + (x + 1))) =
      ∑ x ∈ range m, f x * f (2 * m - x) := by
    rw [← Finset.sum_range_reflect (fun x => f x * f (2 * m - x)) m]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Finset.mem_range.mp hx
    have e2 : 2 * m - (m + (x + 1)) = m - 1 - x := by omega
    have e3 : 2 * m - (m - 1 - x) = m + (x + 1) := by omega
    simp only [e2, e3]
    ring
  rw [h2]
  have e4 : 2 * m - (m + 0) = m := by omega
  rw [e4, Nat.add_zero]
  ring

lemma parity : ∀ n, (a n % 2 = 1 ↔ ∃ k : ℕ, n = 2 * (2 ^ k - 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      constructor
      · intro _
        exact ⟨0, by norm_num⟩
      · intro _
        simp [a]
    | 1, _ =>
      constructor
      · intro h
        simp [a] at h
      · rintro ⟨k, hk⟩
        omega
    | n + 2, ih =>
      rw [a_succ_succ]
      rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
      · rw [sym_odd a m]
        have h1 : ∀ x s q : ℕ, (4 * x + (2 * s + q)) % 2 = q % 2 := by
          intro x s q
          omega
        have h2 : (a m * a m) % 2 = 1 ↔ a m % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one (a m) with h | h <;> simp [Nat.mul_mod, h]
        rw [h1, h2, ih m (by omega)]
        constructor
        · rintro ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
          have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          omega
        · rintro ⟨k, hk⟩
          rcases k with _ | k
          · simp at hk
          · refine ⟨k, ?_⟩
            have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
            have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
            omega
      · have hE : Even (∑ i ∈ range (2 * m + 1 + 1), a i * a (2 * m + 1 - i)) :=
          sym_even a m
        obtain ⟨r, hr⟩ := hE
        constructor
        · intro h
          omega
        · rintro ⟨k, hk⟩
          omega

end A005572

theorem OMA.solution : type_of% @OMA.S_oeis_a005572.main := by
  refine ⟨A005572.gf_eq, ?_⟩
  intro n
  rw [← A005572.parity n, Nat.even_iff]
  omega
