import OMAReductions.R_oeis_a000330_R1

/-!
Local solubility for generalized polygonal pyramidal numbers.

Credit: @grp06
Source conjecture: https://oeis.org/A000330/internal
Registered reduction: https://lefttosolve.com/p/oeis-a000330.R1.H1
The generalized polygonal pyramidal definition is from the formal statement
credited to @Heart-galaxy.
-/

namespace OMA
namespace A000330Local

open OMA.S_oeis_a000330

private def cubic {R : Type*} [CommRing R] (A B C x : R) : R :=
  A * x ^ 3 + B * x ^ 2 + C * x

private def slope {R : Type*} [CommRing R] (A B C x : R) : R :=
  3 * A * x ^ 2 + 2 * B * x + C

private theorem cast_cubic (m : ℕ) (A B C x : ℤ) :
    (↑(cubic A B C x) : ZMod m) = cubic (↑A) (↑B) (↑C) (↑x) := by
  simp [cubic]

private theorem cast_slope (m : ℕ) (A B C x : ℤ) :
    (↑(slope A B C x) : ZMod m) = slope (↑A) (↑B) (↑C) (↑x) := by
  simp [slope]

private theorem cubicTaylor (A B C x h : ℤ) :
    cubic A B C (x + h) - cubic A B C x =
      h * slope A B C x + h ^ 2 * (3 * A * x + B + A * h) := by
  unfold cubic slope
  ring

private theorem sixValue (r : ℕ) (x : ℤ) :
    6 * generalizedPolygonalPyramidal r x = cubic ((r : ℤ) - 2) 3 (5 - (r : ℤ)) x := by
  let A : ℤ := (r : ℤ) - 2
  have hnum :
      x * (x + 1) * (A * x - ((r : ℤ) - 5)) =
        A * (x ^ 3 - x) + 3 * x * (x + 1) := by
    dsimp [A]
    ring
  have hd : (6 : ℤ) ∣ x * (x + 1) * (A * x - ((r : ℤ) - 5)) := by
    rw [hnum]
    change ((6 : ℕ) : ℤ) ∣ A * (x ^ 3 - x) + 3 * x * (x + 1)
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).mp
    have h (y : ZMod 6) : y ^ 3 - y = 0 ∧ 3 * y * (y + 1) = 0 := by
      fin_cases y <;> exact ⟨rfl, rfl⟩
    simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_one,
      Int.cast_ofNat, (h (x : ZMod 6)).1, (h (x : ZMod 6)).2, mul_zero, add_zero]
  unfold generalizedPolygonalPyramidal
  change 6 * (x * (x + 1) * (A * x - ((r : ℤ) - 5)) / 6) = _
  rw [Int.mul_ediv_cancel' hd, hnum]
  dsimp [cubic, A]
  ring

private theorem cast_nat_self (p : ℕ) : ((p : ℤ) : ZMod p) = 0 := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_refl _)

private theorem cast_prime_pow {p k : ℕ} (hk : k ≠ 0) :
    (↑((p : ℤ) ^ k) : ZMod p) = 0 := by
  rw [Int.cast_pow, cast_nat_self, zero_pow hk]

private theorem intCoprime_of_nat {p d : ℕ} (h : p.Coprime d) :
    IsCoprime (p : ℤ) (d : ℤ) := by
  exact h.isCoprime

-- The numerator scale is s*d. Moving the regular input by s*p^k*t
-- cancels s before the next digit of the error is computed modulo p.
private theorem liftDigits {p : ℕ} (hp : p.Prime) (F : ℤ → ℤ)
    (s d A B C z b c : ℤ) (hs : s ≠ 0) (hd : IsCoprime (p : ℤ) d)
    (hscale : ∀ x, s * d * F x = cubic A B C x)
    (hbase : ∃ a : ℤ, (p : ℤ) ∣ F a + F b + F c - z ∧
      (↑(slope A B C a) : ZMod p) ≠ 0) :
    ∀ k : ℕ, 0 < k → ∃ a : ℤ, (p : ℤ) ^ k ∣ F a + F b + F c - z ∧
      (↑(slope A B C a) : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro k
  induction k with
  | zero =>
    intro hz
    omega
  | succ k ih =>
    intro _
    by_cases hk : k = 0
    · simpa [hk] using hbase
    obtain ⟨a, ⟨e, he⟩, ha⟩ := ih (by omega)
    let D : ZMod p := ↑(slope A B C a)
    obtain ⟨t, ht⟩ := ZMod.intCast_surjective (n := p) (-(d : ZMod p) * (e : ZMod p) / D)
    have hD : D ≠ 0 := ha
    have hcancel : (t : ZMod p) * D = -(d : ZMod p) * (e : ZMod p) := by
      rw [ht, div_mul_cancel₀ _ hD]
    let h : ℤ := s * (p : ℤ) ^ k * t
    let R : ℤ := 3 * A * a + B + A * h
    have hh : (h : ZMod p) = 0 := by
      simp only [h, Int.cast_mul, cast_prime_pow hk, mul_zero, zero_mul]
    have htaylor :
        d * (F (a + h) - F a) =
          (p : ℤ) ^ k * (t * slope A B C a + s * (p : ℤ) ^ k * t ^ 2 * R) := by
      apply mul_left_cancel₀ hs
      calc
        s * (d * (F (a + h) - F a)) = cubic A B C (a + h) - cubic A B C a := by
          rw [← hscale, ← hscale]
          ring
        _ = _ := by rw [cubicTaylor]; dsimp [R, h]; ring
    have hnext :
        d * (F (a + h) + F b + F c - z) =
          (p : ℤ) ^ k * (d * e + t * slope A B C a + s * (p : ℤ) ^ k * t ^ 2 * R) := by
      calc
        _ = d * (F a + F b + F c - z) + d * (F (a + h) - F a) := by ring
        _ = _ := by rw [he, htaylor]; ring
    have hdiv : (p : ℤ) ∣ d * e + t * slope A B C a + s * (p : ℤ) ^ k * t ^ 2 * R := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
      simp only [Int.cast_add, Int.cast_mul, cast_prime_pow hk, mul_zero, zero_mul, add_zero]
      change (d : ZMod p) * (e : ZMod p) + (t : ZMod p) * D = 0
      rw [hcancel]
      ring
    have hcop : IsCoprime ((p : ℤ) ^ (k + 1)) d := hd.pow_left
    refine ⟨a + h, hcop.dvd_of_dvd_mul_left ?_, ?_⟩
    · rw [hnext, pow_succ]
      obtain ⟨q, hq⟩ := hdiv
      refine ⟨q, ?_⟩
      rw [hq]
      ring
    · rw [cast_slope, Int.cast_add, hh, add_zero, ← cast_slope]
      exact ha

-- The input period m² includes the extra prime factor needed at 2 and 3.
-- Squaring the moduli preserves coprimality for the coordinatewise CRT.
private def LocalAt (F : ℤ → ℤ) (z : ℤ) (m : ℕ) : Prop :=
  (∀ x y : ℤ, x ≡ y [ZMOD ((m : ℤ) ^ 2)] → F x ≡ F y [ZMOD (m : ℤ)]) ∧
  ∃ a b c : ℤ, z ≡ F a + F b + F c [ZMOD (m : ℤ)]

private theorem primeLocal {p : ℕ} (hp : p.Prime) (F : ℤ → ℤ) (s d A B C z : ℤ)
    (hs : s ≠ 0) (hsp : s ∣ (p : ℤ)) (hd : IsCoprime (p : ℤ) d)
    (hscale : ∀ x, s * d * F x = cubic A B C x)
    (hbase : ∃ a b c : ℤ, (p : ℤ) ∣ F a + F b + F c - z ∧
      (↑(slope A B C a) : ZMod p) ≠ 0) {k : ℕ} (hk : 0 < k) :
    LocalAt F z (p ^ k) := by
  constructor
  · intro x y hxy
    simp only [Nat.cast_pow] at hxy ⊢
    have hpow : s ∣ (p : ℤ) ^ k := hsp.trans (dvd_pow_self _ hk.ne')
    have hmod : x ≡ y [ZMOD s * (p : ℤ) ^ k] :=
      hxy.of_dvd (by simpa [pow_two] using mul_dvd_mul_right hpow ((p : ℤ) ^ k))
    have hP :
        cubic A B C x ≡ cubic A B C y [ZMOD s * (p : ℤ) ^ k] := by
      unfold cubic
      exact (((hmod.pow 3).mul_left A).add ((hmod.pow 2).mul_left B)).add (hmod.mul_left C)
    simp only [← hscale, mul_assoc] at hP
    have hD := hP.mul_left_cancel' hs
    apply Int.modEq_of_dvd
    have hcop : IsCoprime ((p : ℤ) ^ k) d := hd.pow_left
    apply hcop.dvd_of_dvd_mul_left
    simpa only [mul_sub] using hD.dvd
  · obtain ⟨a, b, c, h₁, h₂⟩ := hbase
    obtain ⟨a', ha', _⟩ := liftDigits hp F s d A B C z b c hs hd hscale ⟨a, h₁, h₂⟩ k hk
    exact ⟨a', b, c, Int.modEq_of_dvd (by simpa only [Nat.cast_pow] using ha')⟩

open Finset
open scoped Pointwise

private theorem threeSumOfCard {p : ℕ} (hp : p.Prime) (S : Finset (ZMod p))
    (hne : S.Nonempty) (hcard : p ≤ 3 * S.card - 2) (z : ZMod p) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a + b + c = z := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hne' : (S + S).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x + x, Finset.mem_add.mpr ⟨x, hx, x, hx, rfl⟩⟩
  have h₁ := ZMod.cauchy_davenport hp hne hne
  have h₂ := ZMod.cauchy_davenport hp hne' hne
  have hs : 0 < S.card := Finset.card_pos.mpr hne
  have h₃ : p ≤ (S + S).card + S.card - 1 := by
    by_cases hle : p ≤ S.card + S.card - 1
    · rw [min_eq_left hle] at h₁
      omega
    · rw [min_eq_right (by omega : S.card + S.card - 1 ≤ p)] at h₁
      omega
  have h₄ : p ≤ (S + S + S).card := by simpa only [min_eq_left h₃] using h₂
  have hfull : S + S + S = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa [ZMod.card] using h₄)
  have hz : z ∈ S + S + S := by rw [hfull]; exact Finset.mem_univ _
  obtain ⟨u, hu, c, hc, huc⟩ := Finset.mem_add.mp hz
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hu
  refine ⟨a, ha, b, hb, c, hc, ?_⟩
  rw [hab]
  exact huc

private def depressed {K : Type*} [CommRing K] (d x : K) : K := x ^ 3 + d * x

private theorem depressed_fiber_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (d y : K) : (Finset.univ.filter (fun x => depressed d x = y)).card ≤ 3 := by
  let Q : Polynomial K := Polynomial.C d * Polynomial.X - Polynomial.C y
  let P : Polynomial K := Polynomial.X ^ 3 + Q
  have hQ : Q.natDegree ≤ 1 := by
    apply Polynomial.natDegree_sub_le_of_le (m := 1) (n := 1)
    · exact Polynomial.natDegree_C_mul_le _ _ |>.trans Polynomial.natDegree_X_le
    · simp [Polynomial.natDegree_C]
  have hP : P.natDegree = 3 := by
    have hX : ((Polynomial.X : Polynomial K) ^ 3).natDegree = 3 :=
      Polynomial.natDegree_X_pow 3
    have hlt : Q.natDegree < ((Polynomial.X : Polynomial K) ^ 3).natDegree := by omega
    exact (Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt).trans hX
  have hP0 : P ≠ 0 := by
    intro he
    simp [he] at hP
  calc
    _ ≤ P.roots.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
      change P.eval x = 0
      simpa [P, Q, depressed, sub_eq_add_neg, add_assoc] using sub_eq_zero.mpr hx.2
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ 3 := hP ▸ Polynomial.card_roots' P

private theorem depressed_critical_factor {K : Type*} [CommRing K] {d u : K}
    (hu : 3 * u ^ 2 + d = 0) (x : K) :
    depressed d x - depressed d u = (x - u) ^ 2 * (x + 2 * u) := by
  unfold depressed
  linear_combination (x - u) * hu

private theorem depressed_critical_fiber {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d u : K} (hu : 3 * u ^ 2 + d = 0) :
    Finset.univ.filter (fun x => depressed d x = depressed d u) = {u, -(2 * u)} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  rw [← sub_eq_zero, depressed_critical_factor hu, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0),
    sub_eq_zero, add_eq_zero_iff_eq_neg]

private theorem depressed_no_two {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (d : K) (hreg : ∀ x : K, 3 * x ^ 2 + d ≠ 0) (y : K) :
    (Finset.univ.filter (fun x => depressed d x = y)).card ≠ 2 := by
  intro hc
  obtain ⟨a, b, hab, hf⟩ := Finset.card_eq_two.mp hc
  have ha : depressed d a = y := by
    have : a ∈ Finset.univ.filter (fun x => depressed d x = y) := by rw [hf]; simp
    exact (Finset.mem_filter.mp this).2
  have hb : depressed d b = y := by
    have : b ∈ Finset.univ.filter (fun x => depressed d x = y) := by rw [hf]; simp
    exact (Finset.mem_filter.mp this).2
  have hprod : (a - b) * (a ^ 2 + a * b + b ^ 2 + d) = 0 := by
    unfold depressed at ha hb
    linear_combination ha - hb
  have hd : a ^ 2 + a * b + b ^ 2 + d = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab)
  have hthird : depressed d (-a-b) = y := by
    unfold depressed at ha ⊢
    linear_combination ha + (-2*a-b) * hd
  have hm : -a-b ∈ Finset.univ.filter (fun x => depressed d x = y) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hthird⟩
  rw [hf] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · apply hreg a
    linear_combination hd - (a-b) * hm
  · apply hreg b
    linear_combination hd - (b-a) * hm

private theorem depressed_card {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (h3 : (3 : ZMod p) ≠ 0)
    (d : ZMod p) :
    p ≤ 3 * (Finset.univ.image (depressed d)).card - 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let S : Finset (ZMod p) := Finset.univ.image (depressed d)
  let N (y : ZMod p) : ℕ := (Finset.univ.filter (fun x => depressed d x = y)).card
  have hN (y : ZMod p) : N y ≤ 3 := depressed_fiber_le d y
  have hsum : ∑ y ∈ S, N y = p := by
    symm
    simpa only [Finset.card_univ, ZMod.card] using
      (Finset.card_eq_sum_card_image (s := Finset.univ) (depressed d))
  let deficit (y : ZMod p) : ℕ := 3 - N y
  have hcount : p + (∑ y ∈ S, deficit y) = 3 * S.card := by
    calc
      p + (∑ y ∈ S, deficit y) = (∑ y ∈ S, N y) + (∑ y ∈ S, deficit y) :=
        congrArg (fun t => t + (∑ y ∈ S, deficit y)) hsum.symm
      _ = ∑ y ∈ S, (N y + deficit y) := Finset.sum_add_distrib.symm
      _ = ∑ _y ∈ S, (3 : ℕ) := by
        apply Finset.sum_congr rfl
        intro y _
        have hy := hN y
        dsimp [deficit]
        omega
      _ = _ := by simp [mul_comm]
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.dvd_prime hp).mp hdvd
    omega
  -- A deficient image leaves room for at most one missing point among its fibers.
  change p ≤ 3 * S.card - 2
  by_contra! hsmall
  have hdef : (∑ y ∈ S, deficit y) ≤ 1 := by omega
  by_cases hd : d = 0
  · have hp2 : p % 3 = 2 := by omega
    have hsurj : Function.Surjective (depressed d) := by
      intro y
      by_cases hy : y = 0
      · exact ⟨0, by simp [hy, depressed]⟩
      let j := (2 * p - 1) / 3
      have hj : j * 3 = (p - 1) * 2 + 1 := by dsimp [j]; omega
      refine ⟨y ^ j, ?_⟩
      rw [depressed, hd, zero_mul, add_zero, ← pow_mul, hj, pow_add, pow_mul,
        ZMod.pow_card_sub_one_eq_one hy]
      simp
    have hS : S = Finset.univ := by
      ext y
      obtain ⟨x, rfl⟩ := hsurj y
      exact iff_of_true (Finset.mem_image_of_mem _ (Finset.mem_univ x)) (Finset.mem_univ _)
    have hcard : S.card = p := by simp [hS, ZMod.card]
    omega
  -- Distinct opposite critical points give two different two-element fibers.
  by_cases hcrit : ∃ u : ZMod p, 3 * u ^ 2 + d = 0
  · obtain ⟨u, hu⟩ := hcrit
    have hu0 : u ≠ 0 := by
      intro h
      apply hd
      simpa [h] using hu
    have hnu : 3 * (-u) ^ 2 + d = 0 := by linear_combination hu
    have hpair {v : ZMod p} (hv : v ≠ 0) (hv' : 3 * v ^ 2 + d = 0) :
        deficit (depressed d v) = 1 := by
      have hvn : v ≠ -(2 * v) := by
        intro he
        have hz : 3 * v = 0 := by linear_combination he
        exact (mul_ne_zero h3 hv) hz
      have hc : N (depressed d v) = 2 := by
        dsimp [N]
        rw [depressed_critical_fiber hv']
        exact Finset.card_pair_eq_two_iff.mpr hvn
      simp [deficit, hc]
    have huv : depressed d u ≠ depressed d (-u) := by
      intro he
      have H := depressed_critical_factor hu (-u)
      rw [he, sub_self] at H
      have hleft : -u - u ≠ 0 := by
        rw [show -u - u = -(2*u) by ring]
        exact neg_ne_zero.mpr (mul_ne_zero h2 hu0)
      have hright : -u + 2*u ≠ 0 := by
        rwa [show -u + 2*u = u by ring]
      exact (mul_ne_zero (pow_ne_zero _ hleft) hright) H.symm
    have hmem (v : ZMod p) : depressed d v ∈ S :=
      Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hsub : ({depressed d u, depressed d (-u)} : Finset (ZMod p)) ⊆ S := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hmem u
      · exact hmem (-u)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := deficit) hsub
      (fun _ _ _ => Nat.zero_le _)
    simp [Finset.sum_insert, huv, hpair hu0 hu, hpair (neg_ne_zero.mpr hu0) hnu] at hle
    omega
  · have hreg (x : ZMod p) : 3 * x ^ 2 + d ≠ 0 := fun hx => hcrit ⟨x, hx⟩
    have hzero (y : ZMod p) (hy : y ∈ S) : deficit y = 0 := by
      have hle : deficit y ≤ ∑ v ∈ S, deficit v :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy
      have hh := hN y
      have hnot : N y ≠ 2 := depressed_no_two d hreg y
      have hle1 := hle.trans hdef
      change 3 - N y ≤ 1 at hle1
      change 3 - N y = 0
      omega
    have hz : (∑ y ∈ S, deficit y) = 0 := Finset.sum_eq_zero (fun y hy => hzero y hy)
    omega

private theorem depressed_regular_sum {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (h3 : (3 : ZMod p) ≠ 0)
    (d z : ZMod p) :
    ∃ a b c : ZMod p, depressed d a + depressed d b + depressed d c = z ∧
      3 * a ^ 2 + d ≠ 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let S : Finset (ZMod p) := Finset.univ.image (depressed d)
  have hS : S.Nonempty := ⟨depressed d 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  obtain ⟨u, hu, v, hv, w, hw, hsum⟩ :=
    threeSumOfCard hp S hS (depressed_card hp hp5 h2 h3 d) z
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hw
  have hregular (x : ZMod p) :
      (∃ y, depressed d y = depressed d x ∧ 3 * y ^ 2 + d ≠ 0) ∨
        (d = 0 ∧ depressed d x = 0) := by
    by_cases hx : 3 * x ^ 2 + d = 0
    · by_cases hx0 : x = 0
      · right
        exact ⟨by simpa [hx0] using hx, by simp [depressed, hx0]⟩
      · left
        refine ⟨-(2*x), ?_, ?_⟩
        · apply sub_eq_zero.mp
          rw [depressed_critical_factor hx]
          simp
        · have he : 3 * (-(2*x)) ^ 2 + d = 3 * 3 * x ^ 2 := by
            linear_combination hx
          rw [he]
          exact mul_ne_zero (mul_ne_zero h3 h3) (pow_ne_zero _ hx0)
    · exact Or.inl ⟨x, rfl, hx⟩
  rcases hregular a with ⟨a', ha', hreg⟩ | ha
  · exact ⟨a', b, c, by simpa [ha'] using hsum, hreg⟩
  rcases hregular b with ⟨b', hb', hreg⟩ | hb
  · exact ⟨b', a, c, by simpa [hb', add_comm, add_left_comm, add_assoc] using hsum, hreg⟩
  rcases hregular c with ⟨c', hc', hreg⟩ | hc
  · exact ⟨c', a, b, by simpa [hc', add_comm, add_left_comm, add_assoc] using hsum, hreg⟩
  -- The exceptional value is zero for the depressed cube.
  have hz : z = 0 := by simpa [ha.2, hb.2, hc.2] using hsum.symm
  refine ⟨1, -1, 0, ?_, ?_⟩
  · rw [hz, ha.1]
    unfold depressed
    ring
  · simpa [ha.1] using h3

private theorem fieldBase {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (h3 : (3 : ZMod p) ≠ 0) (A C z : ZMod p) :
    ∃ a b c : ZMod p, cubic A 3 C a + cubic A 3 C b + cubic A 3 C c = z ∧
      slope A 3 C a ≠ 0 := by
  by_cases hA : A = 0
  · subst A
    let h : ZMod p := C / (2 * 3)
    let E := cubic 0 3 C (-h)
    have hC : h * (2 * 3) = C := div_mul_cancel₀ _ (mul_ne_zero h2 h3)
    have hv (x : ZMod p) : cubic 0 3 C (x - h) = 3 * x ^ 2 + E := by
      dsimp [E]
      unfold cubic
      linear_combination -x * hC
    have hD : slope 0 3 C (1 - h) = 2 * 3 := by
      unfold slope
      linear_combination -hC
    let w := (z - 3 * E) / 3
    have hw : w * 3 = z - 3 * E := div_mul_cancel₀ _ h3
    obtain ⟨b, c, hbc⟩ := ZMod.sq_add_sq p (w - 1)
    refine ⟨1 - h, b - h, c - h, ?_, ?_⟩
    · rw [hv, hv, hv]
      linear_combination 3 * hbc + hw
    · rw [hD]
      exact mul_ne_zero h2 h3
  · let h : ZMod p := 3 / (3 * A)
    let d : ZMod p := (C - 3 * A * h ^ 2) / A
    let E := cubic A 3 C (-h)
    have hB : 3 * A * h = 3 := by
      dsimp [h]
      rw [mul_comm, div_mul_cancel₀ _ (mul_ne_zero h3 hA)]
    have hd : A * d = C - 3 * A * h ^ 2 := by
      dsimp only [d]
      rw [mul_comm, div_mul_cancel₀ _ hA]
    have hv (x : ZMod p) : cubic A 3 C (x - h) = A * depressed d x + E := by
      dsimp [E]
      unfold cubic depressed
      linear_combination -(x ^ 2 - 2*x*h) * hB - x * hd
    have hD (x : ZMod p) : slope A 3 C (x - h) = A * (3 * x ^ 2 + d) := by
      unfold slope
      linear_combination -(2*x - 2*h) * hB - hd
    let w := (z - 3 * E) / A
    have hw : w * A = z - 3 * E := div_mul_cancel₀ _ hA
    obtain ⟨a, b, c, habc, ha⟩ := depressed_regular_sum hp hp5 h2 h3 d w
    refine ⟨a - h, b - h, c - h, ?_, ?_⟩
    · rw [hv, hv, hv]
      linear_combination A * habc + hw
    · rw [hD]
      exact mul_ne_zero hA ha

private theorem residueDvd {p : ℕ} {F : ℤ → ℤ} {a b c z : ℤ}
    (h : (F a : ZMod p) + (F b : ZMod p) + (F c : ZMod p) = (z : ZMod p)) :
    (p : ℤ) ∣ F a + F b + F c - z := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Int.cast_sub, Int.cast_add, h, sub_self]

private theorem largePrime {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k)
    (F : ℤ → ℤ) (A z : ℤ) (hscale : ∀ x, 6 * F x = cubic A 3 (3 - A) x) :
    LocalAt F z (p ^ k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnd2 : ¬ p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  have hnd3 : ¬ p ∣ 3 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 3) h
    omega
  have hnd6 : ¬ p ∣ 6 := by
    intro h
    exact (hp.dvd_mul.mp (show p ∣ 2 * 3 from h)).elim hnd2 hnd3
  have hnz (n : ℕ) (h : ¬ p ∣ n) : (n : ZMod p) ≠ 0 :=
    fun he => h ((ZMod.natCast_eq_zero_iff n p).mp he)
  have h2 : (2 : ZMod p) ≠ 0 := by simpa using hnz 2 hnd2
  have h3 : (3 : ZMod p) ≠ 0 := by simpa using hnz 3 hnd3
  have h6 : (6 : ZMod p) ≠ 0 := by simpa using hnz 6 hnd6
  have hd : IsCoprime (p : ℤ) 6 := intCoprime_of_nat (hp.coprime_iff_not_dvd.mpr hnd6)
  obtain ⟨a, b, c, hsum, ha⟩ :=
    fieldBase hp hp5 h2 h3 (A : ZMod p) ((3 - A : ℤ) : ZMod p) (6 * (z : ZMod p))
  obtain ⟨a', ea⟩ := ZMod.intCast_surjective (n := p) a
  obtain ⟨b', eb⟩ := ZMod.intCast_surjective (n := p) b
  obtain ⟨c', ec⟩ := ZMod.intCast_surjective (n := p) c
  have hpoly (x : ℤ) :
      (6 : ZMod p) * (F x : ZMod p) = cubic (A : ZMod p) 3 ((3 - A : ℤ) : ZMod p) (x : ZMod p) := by
    simpa only [Int.cast_mul, Int.cast_ofNat, cast_cubic] using
      congrArg (fun t : ℤ => (t : ZMod p)) (hscale x)
  have hrep : (F a' : ZMod p) + (F b' : ZMod p) + (F c' : ZMod p) = (z : ZMod p) := by
    apply mul_left_cancel₀ h6
    rw [mul_add, mul_add, hpoly, hpoly, hpoly, ea, eb, ec]
    exact hsum
  have hreg : (↑(slope A 3 (3-A) a') : ZMod p) ≠ 0 := by
    simpa only [cast_slope, Int.cast_ofNat, ea] using ha
  exact primeLocal hp F 1 6 A 3 (3-A) z one_ne_zero (one_dvd _) hd
    (fun x => by simpa only [one_mul] using hscale x)
    ⟨a', b', c', residueDvd (p := p) (F := F) hrep, hreg⟩ hk

private theorem smallValues (F : ℤ → ℤ) (A : ℤ)
    (hscale : ∀ x, 6 * F x = cubic A 3 (3 - A) x) :
    F 0 = 0 ∧ F 1 = 1 ∧ F 2 = A + 3 ∧ F 3 = 4 * A + 6 ∧ F 6 = 35 * A + 21 := by
  have atInput (x v : ℤ) (h : cubic A 3 (3-A) x = 6 * v) : F x = v := by
    exact mul_left_cancel₀ (by decide : (6 : ℤ) ≠ 0) ((hscale x).trans h)
  exact ⟨atInput 0 0 (by unfold cubic; ring),
    atInput 1 1 (by unfold cubic; ring),
    atInput 2 (A+3) (by unfold cubic; ring),
    atInput 3 (4*A+6) (by unfold cubic; ring),
    atInput 6 (35*A+21) (by unfold cubic; ring)⟩

private theorem twoBase (F : ℤ → ℤ) (A z : ℤ)
    (hscale : ∀ x, 6 * F x = cubic A 3 (3 - A) x) :
    ∃ a b c : ℤ, (2 : ℤ) ∣ F a + F b + F c - z ∧
      (↑(slope A 3 (3-A) a) : ZMod 2) ≠ 0 := by
  obtain ⟨h0, h1, _, h3, _⟩ := smallValues F A hscale
  have hF3 : (F 3 : ZMod 2) = 0 := by
    rw [h3, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_ofNat,
      show (4 : ZMod 2) = 0 by decide, show (6 : ZMod 2) = 0 by decide]
    simp
  have hmod (x : ℤ) (hx : (x : ZMod 2) = 1) :
      (↑(slope A 3 (3-A) x) : ZMod 2) = 1 := by
    rw [cast_slope, Int.cast_sub, Int.cast_ofNat, hx, slope,
      show (3 : ZMod 2) = 1 by decide, show (2 : ZMod 2) = 0 by decide]
    ring
  have hz : (z : ZMod 2) = 0 ∨ (z : ZMod 2) = 1 := by
    generalize (z : ZMod 2) = w
    fin_cases w
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hz with hz | hz
  · refine ⟨3, 0, 0, residueDvd (p := 2) (F := F) ?_, ?_⟩
    · simp [h0, hF3, hz]
    · rw [hmod 3 (by decide)]
      exact one_ne_zero
  · refine ⟨1, 0, 0, residueDvd (p := 2) (F := F) ?_, ?_⟩
    · simp [h0, h1, hz]
    · rw [hmod 1 (by decide)]
      exact one_ne_zero

private theorem threeResidues (w : ZMod 3) : w = 0 ∨ w = 1 ∨ w = 2 := by
  fin_cases w
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem threeBaseUnit (F : ℤ → ℤ) (A z : ℤ)
    (hA : (A : ZMod 3) ≠ 0) (hscale : ∀ x, 6 * F x = cubic A 3 (3 - A) x) :
    ∃ a b c : ℤ, (3 : ℤ) ∣ F a + F b + F c - z ∧
      (↑(slope A 3 (3-A) a) : ZMod 3) ≠ 0 := by
  obtain ⟨h0, _, _, h3, h6⟩ := smallValues F A hscale
  have hF3 : (F 3 : ZMod 3) = (A : ZMod 3) := by
    rw [h3, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_ofNat,
      show (4 : ZMod 3) = 1 by decide, show (6 : ZMod 3) = 0 by decide]
    simp
  have hF6 : (F 6 : ZMod 3) = 2 * (A : ZMod 3) := by
    rw [h6, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_ofNat,
      show (35 : ZMod 3) = 2 by decide, show (21 : ZMod 3) = 0 by decide]
    simp
  have hreg (x : ℤ) : (↑(slope A 3 (3-A) x) : ZMod 3) ≠ 0 := by
    rw [cast_slope, Int.cast_sub, Int.cast_ofNat, slope, show (3 : ZMod 3) = 0 by decide]
    simpa using neg_ne_zero.mpr hA
  let w := (z : ZMod 3) / (A : ZMod 3)
  have hw : w * (A : ZMod 3) = (z : ZMod 3) := div_mul_cancel₀ _ hA
  rcases threeResidues w with h | h | h
  · refine ⟨0, 0, 0, residueDvd (p := 3) (F := F) ?_, hreg 0⟩
    simpa [h, h0] using hw
  · refine ⟨3, 0, 0, residueDvd (p := 3) (F := F) ?_, hreg 3⟩
    simpa [h, h0, hF3] using hw
  · refine ⟨6, 0, 0, residueDvd (p := 3) (F := F) ?_, hreg 6⟩
    simpa [h, h0, hF6] using hw

private theorem threeBaseDivisible (F : ℤ → ℤ) (K z : ℤ)
    (hscale : ∀ x, 6 * F x = cubic (3*K) 3 (3 - 3*K) x) :
    ∃ a b c : ℤ, (3 : ℤ) ∣ F a + F b + F c - z ∧
      (↑(slope K 1 (1-K) a) : ZMod 3) ≠ 0 := by
  obtain ⟨h0, h1, h2, _, _⟩ := smallValues F (3*K) hscale
  have hF2 : (F 2 : ZMod 3) = 0 := by
    simp only [h2, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      show (3 : ZMod 3) = 0 by decide, zero_mul, add_zero]
  have e0 : (↑(slope K 1 (1-K) 0) : ZMod 3) = 1 - (K : ZMod 3) := by
    rw [cast_slope, Int.cast_sub]
    simp [slope]
  have e2 : (↑(slope K 1 (1-K) 2) : ZMod 3) = 2 - (K : ZMod 3) := by
    rw [cast_slope]
    simp only [Int.cast_sub, Int.cast_one, Int.cast_ofNat]
    rw [slope, show (3 : ZMod 3) = 0 by decide]
    calc
      _ = (2 : ZMod 3) * 1 * 2 + (1 - (K : ZMod 3)) := by ring
      _ = (1 : ZMod 3) + (1 - (K : ZMod 3)) := by
        rw [show (2 : ZMod 3) * 1 * 2 = 1 by decide]
      _ = _ := by ring
  obtain ⟨a, ha, ha'⟩ : ∃ a : ℤ, (F a : ZMod 3) = 0 ∧
      (↑(slope K 1 (1-K) a) : ZMod 3) ≠ 0 := by
    by_cases h : (1 : ZMod 3) - (K : ZMod 3) = 0
    · refine ⟨2, hF2, ?_⟩
      rw [e2]
      intro ht
      have hz : (1 : ZMod 3) = 0 := by linear_combination ht - h
      exact one_ne_zero hz
    · refine ⟨0, by simp [h0], ?_⟩
      rwa [e0]
  rcases threeResidues (z : ZMod 3) with hz | hz | hz
  · exact ⟨a, 0, 0, residueDvd (p := 3) (F := F) (by simp [ha, h0, hz]), ha'⟩
  · exact ⟨a, 1, 0, residueDvd (p := 3) (F := F) (by simp [ha, h1, h0, hz]), ha'⟩
  · exact ⟨a, 1, 1, residueDvd (p := 3) (F := F) (by simp [ha, h1, hz]; decide), ha'⟩

private theorem localPrimePower (F : ℤ → ℤ) (A z : ℤ)
    (hscale : ∀ x, 6 * F x = cubic A 3 (3 - A) x)
    (p k : ℕ) (hp : p.Prime) (hk : 0 < k) : LocalAt F z (p ^ k) := by
  by_cases hp2 : p = 2
  · subst p
    exact primeLocal hp F 2 3 A 3 (3-A) z (by decide) (dvd_refl _)
      (intCoprime_of_nat (p := 2) (d := 3) (by decide)) hscale (twoBase F A z hscale) hk
  by_cases hp3 : p = 3
  · subst p
    by_cases hA : (A : ZMod 3) = 0
    · obtain ⟨K, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd A 3).mp hA
      have hQ (x : ℤ) : 1 * 2 * F x = cubic K 1 (1-K) x := by
        apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
        calc
          _ = 6 * F x := by ring
          _ = cubic (3*K) 3 (3-3*K) x := hscale x
          _ = _ := by unfold cubic; ring
      exact primeLocal hp F 1 2 K 1 (1-K) z one_ne_zero (one_dvd _)
        (intCoprime_of_nat (p := 3) (d := 2) (by decide)) hQ
        (threeBaseDivisible F K z hscale) hk
    · exact primeLocal hp F 3 2 A 3 (3-A) z (by decide) (dvd_refl _)
        (intCoprime_of_nat (p := 3) (d := 2) (by decide))
        hscale (threeBaseUnit F A z hA hscale) hk
  have hp5 : 5 ≤ p := by
    have hp₂ := hp.two_le
    by_contra! h
    have h4 : p = 4 := by omega
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  exact largePrime hp hp5 hk F A z hscale

private theorem combineInputs {m n : ℕ} (h : m.Coprime n) (a b : ℤ) :
    ∃ x : ℤ, x ≡ a [ZMOD ((m : ℤ) ^ 2)] ∧ x ≡ b [ZMOD ((n : ℤ) ^ 2)] := by
  let M := (m : ℤ) ^ 2
  let N := (n : ℤ) ^ 2
  have hMN : IsCoprime M N := (intCoprime_of_nat h).pow_left.pow_right
  obtain ⟨u, v, huv⟩ := hMN
  refine ⟨b * (u * M) + a * (v * N), Int.modEq_of_dvd ⟨u * (a-b), ?_⟩,
    Int.modEq_of_dvd ⟨v * (b-a), ?_⟩⟩
  · change a - (b * (u * M) + a * (v * N)) = M * (u * (a-b))
    linear_combination -a * huv
  · change b - (b * (u * M) + a * (v * N)) = N * (v * (b-a))
    linear_combination -b * huv

private theorem combineLocal {F : ℤ → ℤ} {z : ℤ} {m n : ℕ} (h : m.Coprime n)
    (hm : LocalAt F z m) (hn : LocalAt F z n) : LocalAt F z (m*n) := by
  have hcrt {x y : ℤ} (hx : x ≡ y [ZMOD (m : ℤ)]) (hy : x ≡ y [ZMOD (n : ℤ)]) :
      x ≡ y [ZMOD ((m*n : ℕ) : ℤ)] := by
    rw [Nat.cast_mul]
    exact (Int.modEq_and_modEq_iff_modEq_mul (by simpa using h)).mp ⟨hx, hy⟩
  constructor
  · intro x y hxy
    have hh : x ≡ y [ZMOD (m : ℤ)^2 * (n : ℤ)^2] := by
      simpa only [Nat.cast_mul, mul_pow] using hxy
    exact hcrt (hm.1 x y (hh.of_mul_right _)) (hn.1 x y (hh.of_mul_left _))
  · obtain ⟨a₁, b₁, c₁, h₁⟩ := hm.2
    obtain ⟨a₂, b₂, c₂, h₂⟩ := hn.2
    obtain ⟨a, ha₁, ha₂⟩ := combineInputs h a₁ a₂
    obtain ⟨b, hb₁, hb₂⟩ := combineInputs h b₁ b₂
    obtain ⟨c, hc₁, hc₂⟩ := combineInputs h c₁ c₂
    refine ⟨a, b, c, hcrt ?_ ?_⟩
    · exact h₁.trans (((hm.1 _ _ ha₁).add (hm.1 _ _ hb₁)).add (hm.1 _ _ hc₁)).symm
    · exact h₂.trans (((hn.1 _ _ ha₂).add (hn.1 _ _ hb₂)).add (hn.1 _ _ hc₂)).symm

private theorem allModuli (F : ℤ → ℤ) (A z : ℤ)
    (hscale : ∀ x, 6 * F x = cubic A 3 (3-A) x) :
    ∀ m : ℕ, 0 < m → LocalAt F z m := by
  apply Nat.recOnPosPrimePosCoprime
  · intro p k hp hk _
    exact localPrimePower F A z hscale p k hp hk
  · intro hz
    omega
  · intro _
    exact ⟨fun _ _ _ => by simp [Int.ModEq], 0, 0, 0, by simp [Int.ModEq]⟩
  · intro m n hm hn h hm' hn' _
    exact combineLocal h (hm' (by omega)) (hn' (by omega))

end A000330Local
end OMA

theorem OMA.solution : OMA.R_oeis_a000330_R1.H1 := by
  intro r _ z m hm
  let F := OMA.S_oeis_a000330.generalizedPolygonalPyramidal r
  let A : ℤ := (r : ℤ) - 2
  have hscale (x : ℤ) : 6 * F x = OMA.A000330Local.cubic A 3 (3 - A) x := by
    have he : 3 - A = 5 - (r : ℤ) := by dsimp [A]; ring
    rw [he]
    exact OMA.A000330Local.sixValue r x
  exact (OMA.A000330Local.allModuli F A z hscale m hm).2
