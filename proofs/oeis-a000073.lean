import OMAStatements.S_oeis_a000073
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.NumberTheory.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open Polynomial

namespace BalaTribonacci

def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n

noncomputable def cubic (R : Type*) [Ring R] : R[X] := X ^ 3 - X ^ 2 - X - 1

def f {R : Type*} [Ring R] (u : R) := u ^ 3 - u ^ 2 - u - 1

def slope {R : Type*} [Ring R] (u : R) := 3 * u ^ 2 - 2 * u - 1

@[simp] theorem map_f {R S : Type*} [Ring R] [Ring S] (π : R →+* S) (u : R) :
    π (f u) = f (π u) := by simp [f]

@[simp] theorem map_slope {R S : Type*} [Ring R] [Ring S] (π : R →+* S) (u : R) :
    π (slope u) = slope (π u) := by
  simp only [slope, map_sub, map_mul, map_pow, map_one]
  rw [show π 3 = 3 from map_natCast π 3, show π 2 = 2 from map_natCast π 2]

theorem cubic_lift {R K : Type*} [CommRing R] [Field K]
    (π : R →+* K) (p : ℕ) (surj : Function.Surjective π)
    (ker : ∀ v : R, π v = 0 ↔ (p : R) ∣ v)
    (z : K) (root : f z = 0) (simple : slope z ≠ 0) :
    ∀ m : ℕ, ∃ u : R, π u = z ∧ (p : R) ^ (m + 1) ∣ f u := by
  have pzero : π (p : R) = 0 := (ker _).2 dvd_rfl
  intro m
  induction m with
  | zero =>
    obtain ⟨u, hu⟩ := surj z
    exact ⟨u, hu, by simpa using (ker (f u)).1 (by simp [hu, root])⟩
  | succ m ih =>
    obtain ⟨u, hu, b, hb⟩ := ih
    obtain ⟨v, hv⟩ := surj (-π b / slope z)
    have hz : π (b + v * slope u) = 0 := by
      rw [map_add, map_mul, map_slope, hu, hv, div_mul_cancel₀ _ simple]
      exact add_neg_cancel _
    obtain ⟨w, hw⟩ := (ker _).1 hz
    let a : R := (p : R) ^ (m + 1)
    let u' := u + a * v
    have mapu : π u' = z := by simp [u', a, pow_succ, pzero, hu]
    refine ⟨u', mapu, ?_⟩
    have first : (p : R) ^ (m + 1 + 1) ∣ f u + a * v * slope u := by
      change f u = a * b at hb
      rw [hb, mul_assoc, ← mul_add, hw, pow_succ]
      exact ⟨w, by simp [a, mul_assoc]⟩
    have second : (p : R) ^ (m + 1 + 1) ∣ a ^ 2 * (v ^ 2 * (3 * u - 1 + a * v)) := by
      apply dvd_trans _ (dvd_mul_right _ _)
      rw [show m + 1 + 1 = m + 2 from rfl, show a ^ 2 = (p : R) ^ ((m + 1) * 2) by simp [a, pow_mul]]
      exact pow_dvd_pow _ (by omega)
    have expand : f u' = (f u + a * v * slope u) + a ^ 2 * (v ^ 2 * (3 * u - 1 + a * v)) := by
      dsimp [u', f, slope]
      ring
    rw [expand]
    exact dvd_add first second

theorem unit_of_nonzero_reduction {R K : Type*} [CommRing R] [Field K]
    (π : R →+* K) (p k : ℕ) (surj : Function.Surjective π)
    (ker : ∀ v : R, π v = 0 ↔ (p : R) ∣ v)
    (nil : (p : R) ^ k = 0) (u : R) (hu : π u ≠ 0) : IsUnit u := by
  obtain ⟨v, hv⟩ := surj (π u)⁻¹
  have hz : π (1 - u * v) = 0 := by simp [hv, hu]
  obtain ⟨w, hw⟩ := (ker _).1 hz
  have hn : IsNilpotent (1 - u * v) := ⟨k, by rw [hw, mul_pow, nil, zero_mul]⟩
  exact isUnit_of_mul_isUnit_left (by simpa using hn.isUnit_one_sub)

theorem third_root {R : Type*} [CommRing R] (x y : R)
    (hx : f x = 0) (hy : f y = 0) (hxy : IsUnit (x - y)) :
    let z := 1 - x - y
    f z = 0 ∧ x + y + z = 1 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 3 ∧
      slope y = (y - x) * (y - z) ∧ ∀ w, f w = (w - x) * (w - y) * (w - z) := by
  dsimp
  have h0 : (x - y) * (x ^ 2 + x * y + y ^ 2 - x - y - 1) = 0 := by
    dsimp [f] at hx hy
    linear_combination hx - hy
  have h1 : x ^ 2 + x * y + y ^ 2 - x - y - 1 = 0 :=
    (IsUnit.mul_right_eq_zero hxy).1 h0
  refine ⟨?_, by ring, ?_, ?_, ?_⟩
  · dsimp [f] at hx hy ⊢
    linear_combination hx + (1 - 2 * x - y) * h1
  · linear_combination 2 * h1
  · unfold slope
    linear_combination h1
  · intro w
    dsimp [f] at hx ⊢
    linear_combination hx + (w - x) * h1

def traceSequence : ℕ → ℕ
  | 0 => 3
  | 1 => 1
  | 2 => 3
  | n + 3 => traceSequence (n + 2) + traceSequence (n + 1) + traceSequence n

theorem power_sum {R : Type*} [CommRing R] (x y z : R)
    (hx : f x = 0) (hy : f y = 0) (hz : f z = 0)
    (hs : x + y + z = 1) (hs2 : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
    ∀ m : ℕ, x ^ m + y ^ m + z ^ m = (traceSequence m : R) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => norm_num [traceSequence]
    | 1 => simpa [traceSequence] using hs
    | 2 => simpa [traceSequence] using hs2
    | m + 3 =>
      rw [traceSequence, Nat.cast_add, Nat.cast_add, ← ih (m + 2) (by omega),
        ← ih (m + 1) (by omega), ← ih m (by omega)]
      dsimp [f] at hx hy hz
      linear_combination x ^ m * hx + y ^ m * hy + z ^ m * hz

section CubicAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem tail_degree (R : Type*) [CommRing R] [Nontrivial R] :
    ((X : R[X]) ^ 2 + X + 1).degree ≤ 2 := by
  refine (degree_add_le _ _).trans (max_le ?_ ?_)
  · refine (degree_add_le _ _).trans (max_le ?_ ?_)
    · simp [degree_X_pow]
    · simpa only [degree_X] using (show (1 : WithBot ℕ) ≤ 2 by norm_num)
  · simpa only [degree_one] using (show (0 : WithBot ℕ) ≤ 2 by norm_num)

private theorem cubic_form (R : Type*) [CommRing R] :
    cubic R = X ^ 3 - (X ^ 2 + X + 1) := by unfold cubic; ring

theorem cubic_degree (R : Type*) [CommRing R] [Nontrivial R] :
    (cubic R).degree = 3 := by
  rw [cubic_form, degree_sub_eq_left_of_degree_lt]
  · simp [degree_X_pow]
  · rw [degree_X_pow]
    exact (tail_degree R).trans_lt (by norm_num)

theorem cubic_natDegree (R : Type*) [CommRing R] [Nontrivial R] :
    (cubic R).natDegree = 3 :=
  natDegree_eq_of_degree_eq_some (cubic_degree R)

theorem cubic_monic (R : Type*) [CommRing R] [Nontrivial R] : (cubic R).Monic := by
  rw [cubic_form]
  apply monic_X_pow_sub
  exact (tail_degree R).trans_lt (by norm_num)

@[simp] theorem eval₂_cubic (ρ : R →+* S) (x : S) :
    (cubic R).eval₂ ρ x = f x := by simp [cubic, f]

@[simp] theorem map_cubic (ρ : R →+* S) : (cubic R).map ρ = cubic S := by
  simp [cubic]

abbrev CubicAlg (R : Type*) [CommRing R] := AdjoinRoot (cubic R)

noncomputable def root (R : Type*) [CommRing R] : CubicAlg R := AdjoinRoot.root (cubic R)

@[simp] theorem f_root (R : Type*) [CommRing R] : f (root R) = 0 := by
  unfold root
  simpa only [eval₂_cubic] using AdjoinRoot.eval₂_root (cubic R)

noncomputable def reduction (ρ : R →+* S) : CubicAlg R →+* CubicAlg S :=
  AdjoinRoot.lift ((AdjoinRoot.of (cubic S)).comp ρ) (root S) (by simp)

@[simp] theorem reduction_root (ρ : R →+* S) : reduction ρ (root R) = root S :=
  AdjoinRoot.lift_root _

theorem reduction_mk (ρ : R →+* S) (g : R[X]) :
    reduction ρ (AdjoinRoot.mk (cubic R) g) = AdjoinRoot.mk (cubic S) (g.map ρ) := by
  rw [reduction, AdjoinRoot.lift_mk, ← eval₂_map]
  exact AdjoinRoot.aeval_eq _

theorem reduction_surj (ρ : R →+* S) (surj : Function.Surjective ρ) :
    Function.Surjective (reduction ρ) := by
  intro v
  obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective v
  obtain ⟨g, rfl⟩ := map_surjective ρ surj h
  exact ⟨AdjoinRoot.mk _ g, reduction_mk ρ g⟩

theorem reduction_ker [Nontrivial R] [Nontrivial S] (ρ : R →+* S) (p : ℕ)
    (ker : ∀ v : R, ρ v = 0 ↔ (p : R) ∣ v) (v : CubicAlg R) :
    reduction ρ v = 0 ↔ (p : CubicAlg R) ∣ v := by
  constructor
  · intro hz
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective v
    let q := g %ₘ cubic R
    have repr : AdjoinRoot.mk (cubic R) q = AdjoinRoot.mk (cubic R) g := by
      simpa only [q, AdjoinRoot.modByMonicHom_mk] using
        AdjoinRoot.mk_leftInverse (cubic_monic R) (AdjoinRoot.mk (cubic R) g)
    have small : (q.map ρ).degree < (cubic S).degree := by
      rw [cubic_degree S, ← cubic_degree R]
      exact degree_map_le.trans_lt (degree_modByMonic_lt _ (cubic_monic R))
    have eq : q.map ρ = 0 := by
      rw [← repr, reduction_mk] at hz
      have hm := congrArg (AdjoinRoot.modByMonicHom (cubic_monic S)) hz
      simpa only [AdjoinRoot.modByMonicHom_mk, map_zero,
        (modByMonic_eq_self_iff (cubic_monic S)).2 small] using hm
    have hdiv : C (p : R) ∣ q := by
      apply (C_dvd_iff_dvd_coeff _ _).2
      intro j
      apply (ker _).1
      rw [← coeff_map, eq, coeff_zero]
    rw [← repr]
    obtain ⟨a, ha⟩ := hdiv
    exact ⟨AdjoinRoot.mk (cubic R) a, by rw [ha, map_mul, AdjoinRoot.mk_C, map_natCast]⟩
  · rintro ⟨w, rfl⟩
    have hzero : ρ (p : R) = 0 := (ker _).2 dvd_rfl
    have ps : (p : S) = 0 := by simpa only [map_natCast] using hzero
    have pt : (p : CubicAlg S) = 0 := by
      rw [← map_natCast (AdjoinRoot.of (cubic S)), ps, map_zero]
    rw [map_mul, map_natCast, pt, zero_mul]

variable [Nontrivial R]

noncomputable def coeffTwo : CubicAlg R →ₗ[R] R :=
  (lcoeff R 2).comp (AdjoinRoot.modByMonicHom (cubic_monic R))

theorem coeffTwo_mk {g : R[X]} (hg : g.degree < 3) :
    coeffTwo (AdjoinRoot.mk (cubic R) g) = g.coeff 2 := by
  unfold coeffTwo
  rw [LinearMap.comp_apply, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (cubic_monic R)).2 (by rwa [cubic_degree R])]
  rfl

@[simp] theorem coeffTwo_scalar (r : R) : coeffTwo (AdjoinRoot.of (cubic R) r) = 0 := by
  rw [← AdjoinRoot.mk_C, coeffTwo_mk (degree_C_le.trans_lt (by norm_num))]
  simp

theorem coeffTwo_power :
    ∀ m, coeffTwo (root R ^ m) = (tribonacci m : R) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => simpa [tribonacci] using (coeffTwo_scalar (1 : R))
    | 1 =>
      rw [pow_one, root, ← AdjoinRoot.mk_X, coeffTwo_mk (by rw [degree_X]; norm_num)]
      simp [tribonacci, coeff_X]
    | 2 =>
      rw [root, ← AdjoinRoot.mk_X, ← map_pow,
        coeffTwo_mk (by rw [degree_X_pow]; norm_num)]
      simp [tribonacci, coeff_X_pow]
    | m + 3 =>
      have hroot := f_root R
      have step : root R ^ (m + 3) =
          root R ^ (m + 2) + root R ^ (m + 1) + root R ^ m := by
        unfold f at hroot
        linear_combination root R ^ m * hroot
      rw [step, map_add, map_add, ih (m + 2) (by omega), ih (m + 1) (by omega),
        ih m (by omega), tribonacci, Nat.cast_add, Nat.cast_add]

end CubicAlgebra

section Frobenius

variable (p : ℕ) [Fact p.Prime]

theorem irreducible_cubic (noRoot : ∀ x : ZMod p, f x ≠ 0) :
    Irreducible (cubic (ZMod p)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [cubic_natDegree]
    simp
  · intro x
    change (cubic (ZMod p)).eval x ≠ 0
    simpa [cubic, f] using noRoot x

theorem frobenius_roots (noRoot : ∀ x : ZMod p, f x ≠ 0) :
    letI : Fact (Irreducible (cubic (ZMod p))) := ⟨irreducible_cubic p noRoot⟩
    let x := root (ZMod p)
    f (x ^ p) = 0 ∧ slope (x ^ p) ≠ 0 ∧ x ≠ x ^ p ∧
      1 - x - x ^ p = x ^ (p ^ 2) := by
  letI : Fact (Irreducible (cubic (ZMod p))) := ⟨irreducible_cubic p noRoot⟩
  let K := CubicAlg (ZMod p)
  letI : Field K := AdjoinRoot.instField
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  let pb : PowerBasis (ZMod p) K := AdjoinRoot.powerBasis' (cubic_monic (ZMod p))
  letI : Fintype K := Fintype.ofEquiv (Fin pb.dim → ZMod p) pb.basis.equivFun.symm
  have size : Fintype.card K = p ^ 3 := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), pb.finrank, ZMod.card]
    rw [show pb.dim = 3 from cubic_natDegree _]
  let x : K := root (ZMod p)
  let φ : K →+* K := frobenius K p
  let y := φ x
  let w := φ y
  have yp : y = x ^ p := rfl
  have wp : w = x ^ (p ^ 2) := by rw [show w = y ^ p from rfl, yp, ← pow_mul, pow_two]
  have goesBack : φ w = x := by
    change w ^ p = x
    rw [wp, ← pow_mul, ← pow_succ, ← size]
    exact FiniteField.pow_card _
  have hx : f x = 0 := f_root _
  have hy : f y = 0 := by simp [y, ← map_f, hx]
  have hw : f w = 0 := by simp [w, ← map_f, hy]
  have yx : y ≠ x := by
    intro eq
    have bot := (Subfield.mem_bot_iff_pow_eq_self K p).2 (yp.symm.trans eq)
    obtain ⟨a, ha⟩ := (mem_bot_iff_intCast p K).1 bot
    let i : ZMod p →+* K := ZMod.castHom dvd_rfl K
    have e : i (a : ZMod p) = x := by simpa only [map_intCast] using ha
    apply noRoot (a : ZMod p)
    apply i.injective
    rw [map_f, e, hx, map_zero]
  have wx : w ≠ x := by
    intro h
    exact yx ((congrArg φ h).symm.trans goesBack)
  have wy : w ≠ y := fun h => yx (φ.injective h)
  obtain ⟨_, _, _, slope_eq, factor⟩ :=
    third_root x y hx hy (isUnit_iff_ne_zero.2 (sub_ne_zero.2 yx.symm))
  have eq : w = 1 - x - y := by
    rw [factor w] at hw
    exact sub_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left
      (mul_ne_zero (sub_ne_zero.2 wx) (sub_ne_zero.2 wy)))
  have hs : slope y ≠ 0 := by
    rw [slope_eq, ← eq]
    exact mul_ne_zero (sub_ne_zero.2 yx) (sub_ne_zero.2 wy.symm)
  change f (x ^ p) = 0 ∧ slope (x ^ p) ≠ 0 ∧ x ≠ x ^ p ∧
    1 - x - x ^ p = x ^ (p ^ 2)
  rw [← yp, ← wp]
  exact ⟨hy, hs, yx.symm, eq.symm⟩

end Frobenius

theorem main (p n k : ℕ) (prime : p.Prime) (_ : 0 < n) (positive : 0 < k)
    (noRoot : ∀ x : ZMod p, x ^ 3 - x ^ 2 - x - 1 ≠ 0) :
    Nat.ModEq (p ^ k)
      (tribonacci (n * p ^ (k + 1)) + tribonacci (n * p ^ k) + tribonacci (n * p ^ (k - 1))) 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  haveI : Fact p.Prime := ⟨prime⟩
  haveI : Fact (Irreducible (cubic (ZMod p))) := ⟨irreducible_cubic p noRoot⟩
  haveI : NeZero (p ^ (j + 1)) := ⟨pow_ne_zero _ prime.ne_zero⟩
  haveI : Fact (1 < p ^ (j + 1)) := ⟨one_lt_pow₀ prime.one_lt (by omega)⟩
  let B := ZMod (p ^ (j + 1))
  let A := CubicAlg B
  let K := CubicAlg (ZMod p)
  letI : Field K := AdjoinRoot.instField
  let ρ : B →+* ZMod p := ZMod.castHom (m := p) (dvd_pow_self p (by omega)) (ZMod p)
  let π : A →+* K := reduction ρ
  have surj : Function.Surjective π := by
    apply reduction_surj
    intro u
    obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective u
    exact ⟨(b : B), map_natCast ρ b⟩
  have ker : ∀ v : A, π v = 0 ↔ (p : A) ∣ v := by
    apply reduction_ker
    intro v
    obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective v
    rw [map_natCast, CharP.cast_eq_zero_iff (ZMod p) p]
    constructor
    · intro div
      exact Nat.cast_dvd_cast div
    · rintro ⟨c, hc⟩
      have e := congrArg ρ hc
      simpa only [map_natCast, map_mul, ZMod.natCast_self, zero_mul,
        CharP.cast_eq_zero_iff (ZMod p) p] using e
  have vanish : (p : A) ^ (j + 1) = 0 := by
    rw [← Nat.cast_pow, ← map_natCast (AdjoinRoot.of (cubic B)), ZMod.natCast_self, map_zero]
  let x : A := root B
  let xbar : K := root (ZMod p)
  have πx : π x = xbar := reduction_root ρ
  have hx : f x = 0 := f_root B
  obtain ⟨hybar, hslope, hdistinct, hzbar⟩ := frobenius_roots p noRoot
  obtain ⟨y, πy, hdiv⟩ := cubic_lift π p surj ker (xbar ^ p) hybar hslope j
  have hy : f y = 0 := by simpa only [vanish, zero_dvd_iff] using hdiv
  let z := 1 - x - y
  have πz : π z = xbar ^ (p ^ 2) := by simpa only [z, map_sub, map_one, πx, πy] using hzbar
  have hunit : IsUnit (x - y) := by
    apply unit_of_nonzero_reduction π p (j + 1) surj ker vanish
    simpa only [map_sub, πx, πy, sub_ne_zero] using hdistinct
  obtain ⟨hz, hsum, hsquare, _, _⟩ := third_root x y hx hy hunit
  have liftPower (u v : A) (h : π u = π v) : u ^ (p ^ j) = v ^ (p ^ j) := by
    have h0 : (p : A) ∣ u - v := (ker _).1 (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp (by simpa only [vanish, zero_dvd_iff] using dvd_sub_pow_of_dvd_sub h0 j)
  have ey := liftPower y (x ^ p) (by rw [πy, map_pow, πx])
  have ez := liftPower z (x ^ (p ^ 2)) (by rw [πz, map_pow, πx])
  have reindex (a : A) (i : ℕ) (e : a ^ (p ^ j) = (x ^ (p ^ i)) ^ (p ^ j)) :
      a ^ (n * p ^ j) = x ^ (n * p ^ (i + j)) := by
    calc
      a ^ (n * p ^ j) = (a ^ (p ^ j)) ^ n := by rw [← pow_mul, mul_comm n]
      _ = ((x ^ (p ^ i)) ^ (p ^ j)) ^ n := congrArg (fun t : A => t ^ n) e
      _ = (x ^ (p ^ (i + j))) ^ n := by
        exact congrArg (fun t : A => t ^ n) <|
          (pow_mul x (p ^ i) (p ^ j)).symm.trans
            (congrArg (fun l : ℕ => x ^ l) (pow_add p i j).symm)
      _ = x ^ (n * p ^ (i + j)) := by rw [← pow_mul, mul_comm n]
  have powY : y ^ (n * p ^ j) = x ^ (n * p ^ (j + 1)) := by
    simpa only [Nat.add_comm 1 j] using reindex y 1 (by simpa only [pow_one] using ey)
  have powZ : z ^ (n * p ^ j) = x ^ (n * p ^ (j + 1 + 1)) := by
    simpa only [show 2 + j = j + 1 + 1 by omega] using reindex z 2 ez
  have scalar := power_sum x y z hx hy hz hsum hsquare (n * p ^ j)
  rw [powY, powZ] at scalar
  have coeff := congrArg (coeffTwo (R := B)) scalar
  have scalar_zero (m : ℕ) : coeffTwo (R := B) (m : A) = 0 := by
    rw [← map_natCast (AdjoinRoot.of (cubic B)), coeffTwo_scalar]
  have take (m : ℕ) : coeffTwo (R := B) (x ^ m) = (tribonacci m : B) :=
    coeffTwo_power (R := B) m
  rw [map_add, map_add, take, take, take, scalar_zero] at coeff
  apply Nat.modEq_zero_iff_dvd.2
  apply (CharP.cast_eq_zero_iff (ZMod (p ^ (j + 1))) (p ^ (j + 1)) _).1
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add]
  linear_combination coeff

end BalaTribonacci

private theorem tribonacci_agrees : ∀ m, OMA.S_oeis_a000073.tribonacci m = BalaTribonacci.tribonacci m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 | 1 | 2 => rfl
    | a + 3 =>
      rw [OMA.S_oeis_a000073.tribonacci, BalaTribonacci.tribonacci,
        ih (a + 2) (by omega), ih (a + 1) (by omega), ih a (by omega)]

theorem OMA.solution : type_of% @OMA.S_oeis_a000073.main := by
  simpa only [tribonacci_agrees] using BalaTribonacci.main
