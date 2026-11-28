import OMAStatements.S_oeis_a392387
import Mathlib
open Polynomial Complex

namespace W

lemma deg0 {N : ℕ} (hN : 0 < N) {μ : ℂ} (hμ : IsPrimitiveRoot μ N) (P : ℚ[X])
    (h0 : aeval μ P = 0) (hd : P.degree < (N.totient : WithBot ℕ)) : P = 0 := by
  by_contra hne
  have hdv := minpoly.dvd ℚ μ h0
  rw [← cyclotomic_eq_minpoly_rat hμ hN] at hdv
  have := natDegree_le_of_dvd hdv hne
  rw [natDegree_cyclotomic] at this
  have h2 := (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hd
  omega

lemma bridge (x : ℝ) (M a : ℕ) (ha : a ≤ M) :
    cexp (↑x * I) ^ (M + a) + cexp (↑x * I) ^ (M - a) = 2 * cexp (↑x * I) ^ M * ↑(Real.cos (a * x)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [show a + m - a = m by omega, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  rw [Complex.ofReal_cos, show ∀ E z : ℂ, 2 * E * Complex.cos z = E * (2 * Complex.cos z) from fun _ _ => by ring,
    Complex.two_cos, mul_add, ← Complex.exp_add, ← Complex.exp_add]
  push_cast
  congr 1 <;> congr 1 <;> ring

lemma primRoot (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (cexp (↑(2 * Real.pi / N) * I)) N := by
  convert Complex.isPrimitiveRoot_exp N hN using 2
  push_cast; ring

lemma tot4 (h : ℕ) (hp : (2*h+1).Prime) : Nat.totient (4 * (2*h+1)) = 4 * h := by
  have h3 : (2*h+1) ≠ 2 := by omega
  have hc : Nat.Coprime 4 (2*h+1) := by
    have : Nat.Coprime 2 (2*h+1) := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm h3)
    simpa using this.pow_left 2
  rw [Nat.totient_mul hc, Nat.totient_prime hp, show Nat.totient 4 = 2 by decide]
  omega

lemma tot2 (h : ℕ) (hp : (2*h+1).Prime) : Nat.totient (2 * (2*h+1)) = 2 * h := by
  have h3 : (2*h+1) ≠ 2 := by omega
  have hc : Nat.Coprime 2 (2*h+1) := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm h3)
  rw [Nat.totient_mul hc, Nat.totient_prime hp, Nat.totient_two]
  omega

lemma indepE (h : ℕ) (hp : (2*h+1).Prime) (q : Fin h → ℤ)
    (hs : ∑ i : Fin h, (q i : ℝ) * Real.cos (((2*(i:ℕ)+1 : ℕ) : ℝ) * (2 * Real.pi / ((4*(2*h+1) : ℕ) : ℝ))) = 0) :
    ∀ i, q i = 0 := by
  set N := 4*(2*h+1) with hNdef
  set x : ℝ := 2 * Real.pi / (N : ℝ)
  set ζ := cexp (↑x * I)
  have hζ : IsPrimitiveRoot ζ N := primRoot N (by omega)
  set M := 2*h - 1
  let P : ℚ[X] := ∑ i : Fin h, C ((q i : ℚ)) * (X^(M + (2*(i:ℕ)+1)) + X^(M - (2*(i:ℕ)+1)))
  have hcoeff : ∀ m, P.coeff m = ∑ i : Fin h, (q i : ℚ) *
      ((if m = M + (2*(i:ℕ)+1) then 1 else 0) + (if m = M - (2*(i:ℕ)+1) then 1 else 0)) := by
    intro m; simp [P, coeff_X_pow]
  have hev : aeval ζ P = 0 := by
    have : aeval ζ P = ∑ i : Fin h, (q i : ℂ) * (ζ^(M + (2*(i:ℕ)+1)) + ζ^(M - (2*(i:ℕ)+1))) := by
      simp [P]
    rw [this]
    have : ∀ i : Fin h, (q i : ℂ) * (ζ^(M + (2*(i:ℕ)+1)) + ζ^(M - (2*(i:ℕ)+1))) =
        2 * ζ^M * (((q i : ℝ) * Real.cos (((2*(i:ℕ)+1 : ℕ) : ℝ) * x) : ℝ) : ℂ) := by
      intro i
      rw [bridge x M _ (by have := i.isLt; omega)]
      push_cast; ring
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.mul_sum, ← Complex.ofReal_sum]
    simp only [x, N] at hs ⊢
    rw [hs]; simp
  have hP : P = 0 := by
    apply deg0 (by omega) hζ P hev
    rw [tot4 h hp, Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro i _
    have := i.isLt
    have hm' : 4 * h ≤ m := by exact_mod_cast hm
    rw [if_neg (by omega), if_neg (by omega)]; simp
  intro i₀
  have := congrArg (fun P => P.coeff (M + (2*(i₀:ℕ)+1))) hP
  simp only [hcoeff, coeff_zero] at this
  rw [Finset.sum_eq_single i₀] at this
  · have h0 := i₀.isLt
    rw [if_pos rfl, if_neg (by omega)] at this
    simpa using this
  · intro i _ hne
    have : (i:ℕ) ≠ i₀ := fun e => hne (Fin.ext e)
    rw [if_neg (by omega), if_neg (by omega)]; simp
  · simp


lemma negOnePow_sq (n : ℕ) : ((-1 : ℚ)^n) * (-1)^n = 1 := by
  rw [← mul_pow]; simp

lemma L (a b : ℕ) : (-1:ℚ)^(a+b) * (-1)^a = (-1)^b := by
  rw [pow_add, mul_comm, ← mul_assoc, negOnePow_sq, one_mul]

lemma L2 (a b : ℕ) (hab : b ≤ a) : (-1:ℚ)^(a - b) * (-1)^a = (-1)^b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [show b + c - b = c by omega, add_comm, mul_comm, L]

lemma indepO (h : ℕ) (hp : (2*h+1).Prime) (d : Fin h → ℤ) (e : ℤ) :
    ((e : ℝ) + ∑ i : Fin h, (d i : ℝ) * Real.cos ((((i:ℕ)+1 : ℕ) : ℝ) * (2 * Real.pi / ((2*(2*h+1) : ℕ) : ℝ))) = 0)
      ↔ ∀ i, d i = 2 * e * (-1)^((i:ℕ)+1) := by
  set N := 2*(2*h+1) with hNdef
  set x : ℝ := 2 * Real.pi / (N : ℝ)
  set ω := cexp (↑x * I)
  have hω : IsPrimitiveRoot ω N := primRoot N (by omega)
  let P : ℚ[X] := C (2 * (e : ℚ)) * X^h +
    ∑ i : Fin h, C ((d i : ℚ)) * (X^(h + ((i:ℕ)+1)) + X^(h - ((i:ℕ)+1)))
  have hcoeff : ∀ m, P.coeff m = (if m = h then 2 * (e : ℚ) else 0) + ∑ i : Fin h, (d i : ℚ) *
      ((if m = h + ((i:ℕ)+1) then 1 else 0) + (if m = h - ((i:ℕ)+1) then 1 else 0)) := by
    intro m; simp only [P, coeff_add, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    congr 1; split_ifs <;> simp
  have hc1 : ∀ i : Fin h, P.coeff (h + ((i:ℕ)+1)) = d i := by
    intro i₀; rw [hcoeff, if_neg (by omega), Finset.sum_eq_single i₀]
    · rw [if_pos rfl, if_neg (by omega)]; simp
    · intro i _ hne
      have : (i:ℕ) ≠ i₀ := fun e => hne (Fin.ext e)
      rw [if_neg (by omega), if_neg (by omega)]; simp
    · simp
  have hc2 : ∀ i : Fin h, P.coeff (h - ((i:ℕ)+1)) = d i := by
    intro i₀; have := i₀.isLt; rw [hcoeff, if_neg (by omega), Finset.sum_eq_single i₀]
    · rw [if_pos rfl, if_neg (by omega)]; simp
    · intro i _ hne
      have : (i:ℕ) ≠ i₀ := fun e => hne (Fin.ext e)
      have := i.isLt
      rw [if_neg (by omega), if_neg (by omega)]; simp
    · simp
  have hc3 : P.coeff h = 2 * e := by
    rw [hcoeff, if_pos rfl, Finset.sum_eq_zero]; · simp
    intro i _; have := i.isLt; rw [if_neg (by omega), if_neg (by omega)]; simp
  have hc4 : ∀ m, 2*h < m → P.coeff m = 0 := by
    intro m hm; rw [hcoeff, if_neg (by omega), Finset.sum_eq_zero]; · simp
    intro i _; have := i.isLt; rw [if_neg (by omega), if_neg (by omega)]; simp
  let Q : ℚ[X] := ∑ k ∈ Finset.range (2*h+1), C ((-1 : ℚ)^k) * X^k
  have hQc : ∀ m, Q.coeff m = if m < 2*h+1 then (-1 : ℚ)^m else 0 := by
    intro m; simp only [Q, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]; simp [Finset.mem_range]
  have hQ : aeval ω Q = 0 := by
    have : aeval ω Q = ∑ k ∈ Finset.range (2*h+1), (-ω)^k := by
      simp only [Q, map_sum, map_mul, aeval_C, aeval_X, map_pow, map_neg, map_one]
      exact Finset.sum_congr rfl fun k _ => (neg_pow ω k).symm
    rw [this]
    have hpow : ω ^ (2*h+1) = -1 := by
      have h2 := hω.pow_of_dvd (show 2*h+1 ≠ 0 by omega) (show 2*h+1 ∣ N from ⟨2, by rw [hNdef]; ring⟩)
      rw [show N / (2*h+1) = 2 by simp [N]] at h2
      exact h2.eq_neg_one_of_two_right
    have hne : -ω - 1 ≠ 0 := by
      intro h0
      have : ω = -1 := by linear_combination -h0
      have h1 : ω ^ 2 = 1 := by rw [this]; norm_num
      have := (hω.pow_eq_one_iff_dvd 2).mp h1
      have := Nat.le_of_dvd (by norm_num) this
      rw [hNdef] at this
      have := hp.two_le
      omega
    have hg := geom_sum_mul (-ω) (2*h+1)
    rw [neg_pow, hpow, pow_succ, pow_mul] at hg
    simp at hg
    rcases hg with hg | hg
    · exact hg
    · exact absurd hg hne
  have hev : aeval ω P = 2 * ω^h * ((((e : ℝ) + ∑ i : Fin h, (d i : ℝ) *
      Real.cos ((((i:ℕ)+1 : ℕ) : ℝ) * x)) : ℝ) : ℂ) := by
    have : aeval ω P = 2 * (e:ℂ) * ω^h +
        ∑ i : Fin h, (d i : ℂ) * (ω^(h + ((i:ℕ)+1)) + ω^(h - ((i:ℕ)+1))) := by
      simp [P]
    rw [this]
    have : ∀ i : Fin h, (d i : ℂ) * (ω^(h + ((i:ℕ)+1)) + ω^(h - ((i:ℕ)+1))) =
        2 * ω^h * (((d i : ℝ) * Real.cos ((((i:ℕ)+1 : ℕ) : ℝ) * x) : ℝ) : ℂ) := by
      intro i
      rw [bridge x h _ (by have := i.isLt; omega)]
      push_cast; ring
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.mul_sum]
    push_cast; ring
  have hω0 : (2 : ℂ) * ω^h ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _))
  constructor
  · intro hs
    have hP0 : aeval ω P = 0 := by
      rw [hev]; simp only [x, N] at hs ⊢; rw [hs]; simp
    set c := P.coeff (2*h)
    have hR : P - C c * Q = 0 := by
      apply deg0 (by omega) hω _ (by simp [hP0, hQ])
      rw [tot2 h hp, Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      have hm' : 2 * h ≤ m := by exact_mod_cast hm
      rw [coeff_sub, coeff_C_mul, hQc]
      rcases Nat.eq_or_lt_of_le hm' with h1 | h1
      · subst h1; rw [if_pos (by omega)]
        simp [c, pow_mul]
      · rw [hc4 m h1, if_neg (by omega)]; simp
    have hPQ : P = C c * Q := sub_eq_zero.mp hR
    have e1 : (2 * e : ℚ) = c * (-1)^h := by
      rw [← hc3, hPQ, coeff_C_mul, hQc, if_pos (by omega)]
    intro i
    have e2 : (d i : ℚ) = c * (-1)^(h + ((i:ℕ)+1)) := by
      rw [← hc1, hPQ, coeff_C_mul, hQc, if_pos (by have := i.isLt; omega)]
    have : (d i : ℚ) = 2 * e * (-1)^((i:ℕ)+1) := by
      rw [e2, e1, pow_add]; ring
    exact_mod_cast this
  · intro hd
    have hPQ : P = C (2 * (e:ℚ) * (-1)^h) * Q := by
      ext m
      rw [coeff_C_mul, hQc]
      rcases lt_trichotomy m h with h1 | h1 | h1
      · obtain ⟨i, hi⟩ : ∃ i : Fin h, m = h - ((i:ℕ)+1) := ⟨⟨h - 1 - m, by omega⟩, by simp; omega⟩
        rw [hi, hc2, hd i, if_pos (by omega)]
        have : (-1:ℚ)^h * (-1)^(h - ((i:ℕ)+1)) = (-1)^((i:ℕ)+1) := by
          rw [mul_comm]; exact L2 _ _ (by omega)
        push_cast
        linear_combination (-(2*(e:ℚ))) * this
      · subst h1; rw [hc3, if_pos (by omega)]
        rw [mul_assoc, negOnePow_sq, mul_one]
      · rcases le_or_gt m (2*h) with h2 | h2
        · obtain ⟨i, hi⟩ : ∃ i : Fin h, m = h + ((i:ℕ)+1) := ⟨⟨m - h - 1, by omega⟩, by simp; omega⟩
          rw [hi, hc1, hd i, if_pos (by omega)]
          have : (-1:ℚ)^h * (-1)^(h + ((i:ℕ)+1)) = (-1)^((i:ℕ)+1) := by
            rw [mul_comm]; exact L _ _
          push_cast
          linear_combination (-(2*(e:ℚ))) * this
        · rw [hc4 m h2, if_neg (by omega)]; simp
    have hP0 : aeval ω P = 0 := by rw [hPQ]; simp [hQ]
    rw [hev] at hP0
    have := (mul_eq_zero.mp hP0).resolve_left hω0
    simp only [x, N] at this
    exact_mod_cast this

def sgn : Fin 4 → ℤ := ![1, 1, -1, -1]
def dd (s : Finset (Fin 4)) : ℤ := ∑ k ∈ s, sgn k

abbrev T (h : ℕ) := Fin h × Fin 4 ⊕ Fin 2
abbrev Dat (h : ℕ) := (Fin h → Finset (Fin 4)) × Finset (Fin 2)

def toFin {h : ℕ} (x : Dat h) : Finset (T h) :=
  (Finset.univ.filter (fun ik : Fin h × Fin 4 => ik.2 ∈ x.1 ik.1)).disjSum x.2

lemma mem_toFin {h : ℕ} (x : Dat h) (y : T h) :
    y ∈ toFin x ↔ Sum.elim (fun ik : Fin h × Fin 4 => ik.2 ∈ x.1 ik.1) (fun b => b ∈ x.2) y := by
  rcases y with ik | b <;> simp [toFin]

lemma sum_toFin {h : ℕ} {M : Type*} [AddCommMonoid M] (x : Dat h) (w : T h → M) :
    ∑ y ∈ toFin x, w y = ∑ i, ∑ k ∈ x.1 i, w (Sum.inl (i, k)) + ∑ b ∈ x.2, w (Sum.inr b) := by
  rw [toFin, Finset.sum_disjSum]
  congr 1
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter]; congr 1; ext k; simp

lemma card_toFin {h : ℕ} (x : Dat h) :
    (toFin x).card = ∑ i, (x.1 i).card + x.2.card := by
  rw [Finset.card_eq_sum_ones, sum_toFin]; simp

lemma countLemma (h : ℕ) (φ : T h → ℕ) (hinj : Function.Injective φ)
    (hrange : ∀ y, φ y ∈ Finset.Icc 1 (4*h+2)) (P : Finset ℕ → Prop) [DecidablePred P] :
    ((Finset.Icc 1 (4*h+2)).powerset.filter P).card =
      (Finset.univ.filter (fun x : Dat h => P ((toFin x).image φ))).card := by
  have hsurj : ∀ n ∈ Finset.Icc 1 (4*h+2), ∃ y, φ y = n := by
    have hsub : Finset.univ.image φ ⊆ Finset.Icc 1 (4*h+2) := by
      intro n hn; simp only [Finset.mem_image] at hn; obtain ⟨y, _, rfl⟩ := hn; exact hrange y
    have hcard : (Finset.Icc 1 (4*h+2)).card ≤ (Finset.univ.image φ).card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]; simp; omega
    have := Finset.eq_of_subset_of_card_le hsub hcard
    intro n hn; rw [← this] at hn; simpa using hn
  let j : Finset ℕ → Dat h := fun K =>
    (fun i => Finset.univ.filter (fun k => φ (Sum.inl (i,k)) ∈ K),
      Finset.univ.filter (fun b => φ (Sum.inr b) ∈ K))
  have hmemj : ∀ K y, y ∈ toFin (j K) ↔ φ y ∈ K := by
    intro K y; rcases y with ik | b <;> simp [toFin, j]
  have hright : ∀ K ⊆ Finset.Icc 1 (4*h+2), (toFin (j K)).image φ = K := by
    intro K hK; ext n; simp only [Finset.mem_image, hmemj]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hn; obtain ⟨y, rfl⟩ := hsurj n (hK hn); exact ⟨y, hn, rfl⟩
  symm
  refine Finset.card_nbij' (fun x => (toFin x).image φ) j ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq]
    refine ⟨?_, hx⟩
    intro n hn; simp only [Finset.mem_image] at hn; obtain ⟨y, _, rfl⟩ := hn; exact hrange y
  · intro K hK
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hK
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [hright K hK.1]; exact hK.2
  · intro x _
    simp only [j]
    ext i k <;> simp [hinj.mem_finset_image, mem_toFin]
  · intro K hK
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hK
    exact hright K hK.1

def del : Fin 2 → ℤ := ![1, -1]
def ee (z : Finset (Fin 2)) : ℤ := ∑ b ∈ z, del b
lemma dd_even : ∀ s : Finset (Fin 4), dd s = 0 → s.card % 2 = 0 := by decide
lemma dd_card : (Finset.univ.filter (fun s : Finset (Fin 4) => dd s = 0)).card = 6 := by decide
lemma dd_two : ∀ s : Finset (Fin 4), dd s = 2 ↔ s = {0,1} := by decide
lemma dd_mtwo : ∀ s : Finset (Fin 4), dd s = -2 ↔ s = {2,3} := by decide
lemma ee_cases : ∀ z : Finset (Fin 2), (ee z = 0 ∧ z.card % 2 = 0) ∨ (ee z = 1 ∧ z = {0}) ∨ (ee z = -1 ∧ z = {1}) := by decide
lemma z_card : (Finset.univ.filter (fun z : Finset (Fin 2) => z.card % 2 = 0)).card = 2 := by decide

lemma sumW {h : ℕ} (φ : T h → ℕ) (hinj : Function.Injective φ) (f : ℕ → ℝ) (v : Fin h → ℝ)
    (u : Fin 2 → ℝ) (hw : ∀ i k, f (φ (Sum.inl (i, k))) = sgn k * v i)
    (hu : ∀ b, f (φ (Sum.inr b)) = u b) (x : Dat h) :
    ∑ n ∈ (toFin x).image φ, f n = ∑ i, (dd (x.1 i) : ℝ) * v i + ∑ b ∈ x.2, u b := by
  rw [Finset.sum_image (fun a _ b _ hab => hinj hab), sum_toFin]
  simp only [hw, hu, dd]
  push_cast
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]

def φe (h : ℕ) : T h → ℕ
  | .inl (i, k) => if k = 0 then (if (i:ℕ) = 0 then 4*h+2 else i) else if k = 1 then 4*h+1-i
      else if k = 2 then 2*h - i else 2*h+1+i
  | .inr b => if b = 0 then h else 3*h+1

def φo (h : ℕ) : T h → ℕ
  | .inl (i, k) => if k = 0 then i+1 else if k = 1 then 4*h+1-i
      else if k = 2 then 2*h - i else 2*h+2+i
  | .inr b => if b = 0 then 4*h+2 else 2*h+1

lemma φe_inj (h : ℕ) : Function.Injective (φe h) := by
  rintro (⟨i, k⟩ | b) (⟨i', k'⟩ | b') hxy
  · have := i.isLt; have := i'.isLt
    fin_cases k <;> fin_cases k' <;> simp [φe, Fin.ext_iff] at hxy ⊢ <;> (try split_ifs at hxy) <;> omega
  · have := i.isLt
    fin_cases k <;> fin_cases b' <;> simp [φe, Fin.ext_iff] at hxy ⊢ <;> (try split_ifs at hxy) <;> omega
  · have := i'.isLt
    fin_cases k' <;> fin_cases b <;> simp [φe, Fin.ext_iff] at hxy ⊢ <;> (try split_ifs at hxy) <;> omega
  · fin_cases b <;> fin_cases b' <;> simp [φe] at hxy ⊢ <;> omega

lemma φo_inj (h : ℕ) : Function.Injective (φo h) := by
  rintro (⟨i, k⟩ | b) (⟨i', k'⟩ | b') hxy
  · have := i.isLt; have := i'.isLt
    fin_cases k <;> fin_cases k' <;> simp [φo, Fin.ext_iff] at hxy ⊢ <;> omega
  · have := i.isLt
    fin_cases k <;> fin_cases b' <;> simp [φo, Fin.ext_iff] at hxy ⊢ <;> omega
  · have := i'.isLt
    fin_cases k' <;> fin_cases b <;> simp [φo, Fin.ext_iff] at hxy ⊢ <;> omega
  · fin_cases b <;> fin_cases b' <;> simp [φo] at hxy ⊢ <;> omega

lemma φe_range (h : ℕ) (h1 : 1 ≤ h) : ∀ y, φe h y ∈ Finset.Icc 1 (4*h+2) := by
  rintro (⟨i, k⟩ | b)
  · have := i.isLt
    fin_cases k <;> simp [φe] <;> (try split_ifs) <;> omega
  · fin_cases b <;> simp [φe] <;> omega

lemma φo_range (h : ℕ) : ∀ y, φo h y ∈ Finset.Icc 1 (4*h+2) := by
  rintro (⟨i, k⟩ | b)
  · have := i.isLt
    fin_cases k <;> simp [φo] <;> omega
  · fin_cases b <;> simp [φo] <;> omega

noncomputable def fe (h : ℕ) (n : ℕ) : ℝ := Real.cos ((2 * (n:ℝ) + 1) * Real.pi / ((2 * (2*h+1) : ℕ) : ℝ))
noncomputable def fo (h : ℕ) (n : ℕ) : ℝ := Real.cos ((2 * (n:ℝ) + 0) * Real.pi / ((2 * (2*h+1) : ℕ) : ℝ))
noncomputable def ve (h : ℕ) (i : Fin h) : ℝ :=
  Real.cos (((2*(i:ℕ)+1 : ℕ) : ℝ) * (2 * Real.pi / ((4*(2*h+1) : ℕ) : ℝ)))
noncomputable def vo (h : ℕ) (i : Fin h) : ℝ :=
  Real.cos ((((i:ℕ)+1 : ℕ) : ℝ) * (2 * Real.pi / ((2*(2*h+1) : ℕ) : ℝ)))

lemma we (h : ℕ) (i : Fin h) (k : Fin 4) : fe h (φe h (Sum.inl (i, k))) = sgn k * ve h i := by
  have hi := i.isLt
  have hpos : (0:ℝ) < 2 * h + 1 := by positivity
  fin_cases k
  · by_cases h0 : (i:ℕ) = 0
    · simp [φe, fe, ve, sgn, h0]
      conv_rhs => rw [← Real.cos_add_two_pi]
      congr 1; push_cast; field_simp; ring
    · simp [φe, fe, ve, sgn, h0]
      congr 1; field_simp; ring
  · simp [φe, fe, ve, sgn]
    rw [Nat.cast_sub (by omega)]
    conv_rhs => rw [← Real.cos_two_pi_sub]
    congr 1; push_cast; field_simp; ring
  · simp [φe, fe, ve, sgn]
    rw [Nat.cast_sub (by omega)]
    conv_rhs => rw [← Real.cos_pi_sub]
    congr 1; push_cast; field_simp; ring
  · simp [φe, fe, ve, sgn]
    conv_rhs => rw [← Real.cos_add_pi]
    congr 1; push_cast; field_simp; ring

lemma ue (h : ℕ) (b : Fin 2) : fe h (φe h (Sum.inr b)) = 0 := by
  have hpos : (0:ℝ) < 2 * h + 1 := by positivity
  fin_cases b
  · simp [φe, fe]
    rw [show (2 * (h:ℝ) + 1) * Real.pi / (2 * (2 * h + 1)) = Real.pi / 2 by field_simp]
    simp
  · simp [φe, fe]
    rw [show (2 * (3 * (h:ℝ) + 1) + 1) * Real.pi / (2 * (2 * h + 1)) = Real.pi / 2 + Real.pi by
      field_simp; ring]
    rw [Real.cos_add_pi]; simp

lemma wo (h : ℕ) (i : Fin h) (k : Fin 4) : fo h (φo h (Sum.inl (i, k))) = sgn k * vo h i := by
  have hi := i.isLt
  have hpos : (0:ℝ) < 2 * h + 1 := by positivity
  fin_cases k
  · simp [φo, fo, vo, sgn]
    congr 1; field_simp
  · simp [φo, fo, vo, sgn]
    rw [Nat.cast_sub (by omega)]
    conv_rhs => rw [← Real.cos_two_pi_sub]
    congr 1; push_cast; field_simp; ring
  · simp [φo, fo, vo, sgn]
    rw [Nat.cast_sub (by omega)]
    conv_rhs => rw [← Real.cos_pi_sub]
    congr 1; push_cast; field_simp; ring
  · simp [φo, fo, vo, sgn]
    conv_rhs => rw [← Real.cos_add_pi]
    congr 1; push_cast; field_simp; ring

lemma uo (h : ℕ) (b : Fin 2) : fo h (φo h (Sum.inr b)) = (del b : ℝ) := by
  have hpos : (0:ℝ) < 2 * h + 1 := by positivity
  fin_cases b
  · simp [φo, fo, del]
    rw [show 2 * (4 * (h:ℝ) + 2) * Real.pi / (2 * (2 * h + 1)) = 2 * Real.pi by
      field_simp; ring]
    simp
  · simp [φo, fo, del]
    rw [show 2 * (2 * (h:ℝ) + 1) * Real.pi / (2 * (2 * h + 1)) = Real.pi by
      field_simp]
    simp


def xA (h : ℕ) : Dat h := (fun i => if Even (i:ℕ) then {2,3} else {0,1}, {0})
def xB (h : ℕ) : Dat h := (fun i => if Even (i:ℕ) then {0,1} else {2,3}, {1})

lemma sum_even_of {h : ℕ} (s : Fin h → Finset (Fin 4)) (hs : ∀ i, (s i).card % 2 = 0) :
    (∑ i, (s i).card) % 2 = 0 := by
  have : 2 ∣ ∑ i, (s i).card := Finset.dvd_sum (fun i _ => Nat.dvd_of_mod_eq_zero (hs i))
  omega

lemma ee_real (z : Finset (Fin 2)) : ∑ b ∈ z, (del b : ℝ) = ((ee z : ℤ) : ℝ) := by
  simp [ee]

lemma oddChar (h : ℕ) (hp : (2*h+1).Prime) (x : Dat h) :
    ((∑ i, (x.1 i).card + x.2.card) % 2 = 1 ∧
      ∑ i, (dd (x.1 i) : ℝ) * vo h i + ∑ b ∈ x.2, (del b : ℝ) = 0) ↔ x = xA h ∨ x = xB h := by
  have key := indepO h hp (fun i => dd (x.1 i)) (ee x.2)
  simp only [vo] at *
  rw [ee_real]
  constructor
  · rintro ⟨hpar, hs⟩
    have hd := key.mp (by linarith)
    rcases ee_cases x.2 with ⟨he, hz⟩ | ⟨he, hz⟩ | ⟨he, hz⟩
    · exfalso
      have : ∀ i, (x.1 i).card % 2 = 0 := fun i => dd_even _ (by simpa [he] using hd i)
      have := sum_even_of _ this
      omega
    · left
      refine Prod.ext (funext fun i => ?_) hz
      have := hd i; rw [he] at this
      simp only [xA]
      split_ifs with hi
      · exact (dd_mtwo _).mp (by rw [this, (Even.add_one hi).neg_one_pow]; norm_num)
      · exact (dd_two _).mp (by rw [this, (Nat.not_even_iff_odd.mp hi).add_one.neg_one_pow]; norm_num)
    · right
      refine Prod.ext (funext fun i => ?_) hz
      have := hd i; rw [he] at this
      simp only [xB]
      split_ifs with hi
      · exact (dd_two _).mp (by rw [this, (Even.add_one hi).neg_one_pow]; norm_num)
      · exact (dd_mtwo _).mp (by rw [this, (Nat.not_even_iff_odd.mp hi).add_one.neg_one_pow]; norm_num)
  · have hc : ∀ i : Fin h, ∀ (s t : Finset (Fin 4)), s.card = 2 → t.card = 2 →
        (if Even (i:ℕ) then s else t).card = 2 := by
      intro i s t hs ht; split_ifs <;> assumption
    rintro (rfl | rfl)
    · refine ⟨?_, ?_⟩
      · simp only [xA]
        rw [Finset.sum_congr rfl (fun i _ => hc i _ _ (by decide) (by decide))]
        simp
      · have : ∀ i : Fin h, dd ((xA h).1 i) = 2 * ee (xA h).2 * (-1)^((i:ℕ)+1) := by
          intro i
          simp only [xA, show ee {0} = 1 by decide]
          split_ifs with hi
          · rw [(Even.add_one hi).neg_one_pow]; decide
          · rw [(Nat.not_even_iff_odd.mp hi).add_one.neg_one_pow]; decide
        have := key.mpr this
        linarith
    · refine ⟨?_, ?_⟩
      · simp only [xB]
        rw [Finset.sum_congr rfl (fun i _ => hc i _ _ (by decide) (by decide))]
        simp
      · have : ∀ i : Fin h, dd ((xB h).1 i) = 2 * ee (xB h).2 * (-1)^((i:ℕ)+1) := by
          intro i
          simp only [xB, show ee {1} = -1 by decide]
          split_ifs with hi
          · rw [(Even.add_one hi).neg_one_pow]; decide
          · rw [(Nat.not_even_iff_odd.mp hi).add_one.neg_one_pow]; decide
        have := key.mpr this
        linarith

lemma evenChar (h : ℕ) (hp : (2*h+1).Prime) (x : Dat h) :
    ((∑ i, (x.1 i).card + x.2.card) % 2 = 0 ∧
      ∑ i, (dd (x.1 i) : ℝ) * ve h i + ∑ b ∈ x.2, (0 : ℝ) = 0) ↔
      (∀ i, dd (x.1 i) = 0) ∧ x.2.card % 2 = 0 := by
  constructor
  · rintro ⟨hpar, hs⟩
    have hd := indepE h hp (fun i => dd (x.1 i)) (by simpa [ve] using hs)
    refine ⟨hd, ?_⟩
    have := sum_even_of _ (fun i => dd_even _ (hd i))
    omega
  · rintro ⟨hd, hz⟩
    refine ⟨?_, by simp [hd]⟩
    have := sum_even_of _ (fun i => dd_even _ (hd i))
    omega

end W

namespace OMA.A392387Proof
open OMA.S_oeis_a392387 W

theorem main_proof : ∀ p : ℕ, p.Prime → p % 2 = 1 →
    zeroEnergyCount (2 * p) = 2 * (6 ^ ((p - 1) / 2) + 1) := by
  intro p hp hodd
  obtain ⟨h, rfl⟩ : ∃ h, p = 2*h+1 := ⟨p/2, by omega⟩
  have h1 : 1 ≤ h := by have := hp.two_le; omega
  rw [show (2*h+1-1)/2 = h by omega]
  classical
  unfold zeroEnergyCount
  have hI : Finset.Icc 1 (2*(2*h+1)) = Finset.Icc 1 (4*h+2) := by congr 1; ring
  rw [hI]
  set S := (Finset.Icc 1 (4*h+2)).powerset
  have hsplit : S.filter (fun K => (∑ j ∈ K, Real.cos
      ((2 * ((j : ℕ) : ℝ) + (if K.card % 2 = 0 then 1 else 0)) * Real.pi / ((2*(2*h+1) : ℕ) : ℝ))) = 0) =
      S.filter (fun K => K.card % 2 = 1 ∧ ∑ j ∈ K, fo h j = 0) ∪
      S.filter (fun K => K.card % 2 = 0 ∧ ∑ j ∈ K, fe h j = 0) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_union]
    rcases Nat.mod_two_eq_zero_or_one K.card with hc | hc <;> simp [hc, fo, fe]
  rw [hsplit, Finset.card_union_of_disjoint]
  swap
  · rw [Finset.disjoint_filter]; intro K _ h1 h2; omega
  rw [countLemma h (φo h) (φo_inj h) (φo_range h), countLemma h (φe h) (φe_inj h) (φe_range h h1)]
  have hodd' : (Finset.univ.filter (fun x : Dat h => ((toFin x).image (φo h)).card % 2 = 1 ∧
      ∑ j ∈ (toFin x).image (φo h), fo h j = 0)) = {xA h, xB h} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    rw [Finset.card_image_of_injective _ (φo_inj h), card_toFin,
      sumW (φo h) (φo_inj h) (fo h) (vo h) (fun b => (del b : ℝ)) (wo h) (uo h)]
    exact oddChar h hp x
  have heven' : (Finset.univ.filter (fun x : Dat h => ((toFin x).image (φe h)).card % 2 = 0 ∧
      ∑ j ∈ (toFin x).image (φe h), fe h j = 0)) =
      (Fintype.piFinset fun _ => Finset.univ.filter (fun s : Finset (Fin 4) => dd s = 0)) ×ˢ
        (Finset.univ.filter (fun z : Finset (Fin 2) => z.card % 2 = 0)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Fintype.mem_piFinset]
    rw [Finset.card_image_of_injective _ (φe_inj h), card_toFin,
      sumW (φe h) (φe_inj h) (fe h) (ve h) (fun _ => (0 : ℝ)) (we h) (ue h)]
    exact evenChar h hp x
  rw [hodd', heven', Finset.card_product, Fintype.card_piFinset, z_card]
  have hne : xA h ≠ xB h := by
    intro e; have := congrArg Prod.snd e; simp [xA, xB] at this
  rw [Finset.card_pair hne]
  simp [dd_card]
  ring

end OMA.A392387Proof

open OMA.A392387Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a392387.main := main_proof
