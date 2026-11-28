import OMAReductions.R_mse_2615963_R3
import Mathlib

-- Every residue x is a + a⁻¹ with a a root of unity of order p - 1 or p + 1 in an algebraic
-- closure of F_p, and C_m(a + a⁻¹) = a^m + a^(-m). Summing over both groups counts every x
-- exactly twice, and the power sums over a group of roots of unity are elementary.

namespace ChebyshevSumModP

open Polynomial

variable {K : Type*} [Field K]

lemma cheb_eval (a : K) (ha : a ≠ 0) :
    ∀ m : ℕ, (Chebyshev.C K (m : ℤ)).eval (a + a⁻¹) = a ^ m + a⁻¹ ^ m := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [Nat.cast_zero, Chebyshev.C_zero, pow_zero, pow_zero, eval_ofNat]
    norm_num
  | one => rw [Nat.cast_one, Chebyshev.C_one, eval_X, pow_one, pow_one]
  | more m h0 h1 =>
    have e : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
    have e1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    have hmul : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
    rw [e1] at h1
    rw [e, Chebyshev.C_add_two, eval_sub, eval_mul, eval_X, h0, h1]
    linear_combination (a ^ m + a⁻¹ ^ m) * hmul

lemma power_sum [DecidableEq K] (n m : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    ∑ x ∈ nthRootsFinset n (1 : K), x ^ m = if n ∣ m then (n : K) else 0 := by
  have hmem : ∀ x : K, x ∈ nthRootsFinset n (1 : K) ↔ x ^ n = 1 :=
    fun x => mem_nthRootsFinset hn 1
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [Finset.sum_congr rfl (g := fun _ => (1 : K))
      (fun x hx => by rw [pow_mul, (hmem x).mp hx, one_pow])]
    rw [Finset.sum_const, hζ.card_nthRootsFinset, nsmul_eq_mul, mul_one]
  · have hz : ζ ≠ 0 := hζ.ne_zero hn.ne'
    have key : ∑ x ∈ nthRootsFinset n (1 : K), x ^ m
        = ∑ x ∈ nthRootsFinset n (1 : K), (ζ * x) ^ m := by
      symm
      refine Finset.sum_nbij' (fun x => ζ * x) (fun x => ζ⁻¹ * x) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        rw [hmem] at hx ⊢
        rw [mul_pow, hζ.pow_eq_one, hx, one_mul]
      · intro x hx
        rw [hmem] at hx ⊢
        rw [mul_pow, inv_pow, hζ.pow_eq_one, hx, inv_one, one_mul]
      · intro x _
        exact inv_mul_cancel_left₀ hz x
      · intro x _
        exact mul_inv_cancel_left₀ hz x
      · intro x _
        rfl
    simp only [mul_pow, ← Finset.mul_sum] at key
    have hne : ζ ^ m ≠ 1 := fun e => h ((hζ.pow_eq_one_iff_dvd m).mp e)
    have : (ζ ^ m - 1) * ∑ x ∈ nthRootsFinset n (1 : K), x ^ m = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

lemma inv_sum [DecidableEq K] (n m : ℕ) (hn : 0 < n) :
    ∑ x ∈ nthRootsFinset n (1 : K), x⁻¹ ^ m = ∑ x ∈ nthRootsFinset n (1 : K), x ^ m := by
  have hmem : ∀ x : K, x ∈ nthRootsFinset n (1 : K) → x⁻¹ ∈ nthRootsFinset n (1 : K) := by
    intro x hx
    rw [mem_nthRootsFinset hn] at hx ⊢
    rw [inv_pow, hx, inv_one]
  exact Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹) hmem hmem
    (fun x _ => inv_inv x) (fun x _ => inv_inv x) (fun x _ => rfl)

lemma main (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) :
    ∑ x : ZMod p, (Chebyshev.C (ZMod p) (m : ℤ)).eval x
      = (if (p - 1) ∣ m then (-1 : ZMod p) else 0) + (if (p + 1) ∣ m then 1 else 0) := by
  classical
  have hp : p.Prime := Fact.out
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  let K := AlgebraicClosure (ZMod p)
  let ι : ZMod p →+* K := algebraMap (ZMod p) K
  have ιinj : Function.Injective ι := ι.injective
  haveI : CharP K p := charP_of_injective_algebraMap ιinj p
  have two0 : (2 : K) ≠ 0 := by
    have : ((2 : ℕ) : K) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff K p]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    exact_mod_cast this
  have cast1 : ((p - 1 : ℕ) : K) = -1 := by
    rw [Nat.cast_sub (by omega), CharP.cast_eq_zero K p, Nat.cast_one, zero_sub]
  have cast2 : ((p + 1 : ℕ) : K) = 1 := by
    rw [Nat.cast_add, CharP.cast_eq_zero K p, Nat.cast_one, zero_add]
  haveI : NeZero ((p - 1 : ℕ) : K) := ⟨by rw [cast1]; exact neg_ne_zero.mpr one_ne_zero⟩
  haveI : NeZero ((p + 1 : ℕ) : K) := ⟨by rw [cast2]; exact one_ne_zero⟩
  obtain ⟨z1, hz1⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (p - 1)
  obtain ⟨z2, hz2⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (p + 1)
  let A := nthRootsFinset (p - 1) (1 : K)
  let B := nthRootsFinset (p + 1) (1 : K)
  have memA : ∀ a : K, a ∈ A ↔ a ^ (p - 1) = 1 := fun a => mem_nthRootsFinset (by omega) 1
  have memB : ∀ a : K, a ∈ B ↔ a ^ (p + 1) = 1 := fun a => mem_nthRootsFinset (by omega) 1
  -- the elements of F_p inside K are the fixed points of Frobenius
  have fixed : ∀ y : K, y ^ p = y → y ∈ Finset.univ.image ι := by
    intro y hy
    let P : K[X] := X ^ p - X
    have P0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hp.one_lt
    have sub : Finset.univ.image ι ⊆ P.roots.toFinset := by
      intro z hz
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
      rw [Multiset.mem_toFinset, mem_roots P0]
      change eval (ι x) P = 0
      simp only [P, eval_sub, eval_pow, eval_X, ← map_pow, ZMod.pow_card, sub_self]
    have card : P.roots.toFinset.card ≤ (Finset.univ.image ι).card := by
      rw [Finset.card_image_of_injective _ ιinj, Finset.card_univ, ZMod.card]
      refine (Multiset.toFinset_card_le _).trans ((card_roots' P).trans ?_)
      exact (FiniteField.X_pow_card_sub_X_natDegree_eq K hp.one_lt).le
    rw [Finset.eq_of_subset_of_card_le sub card, Multiset.mem_toFinset, mem_roots P0]
    change eval y P = 0
    simp only [P, eval_sub, eval_pow, eval_X, hy, sub_self]
  have nz : ∀ a : K, a ∈ A ∨ a ∈ B → a ≠ 0 := by
    rintro a h rfl
    rcases h with h | h
    · rw [memA, zero_pow (by omega)] at h; exact zero_ne_one h
    · rw [memB, zero_pow (by omega)] at h; exact zero_ne_one h
  have powA : ∀ a : K, a ∈ A → a ^ p = a := by
    intro a h
    rw [memA] at h
    rw [← pow_sub_one_mul hp.ne_zero a, h, one_mul]
  have powB : ∀ a : K, a ∈ B → a ^ p = a⁻¹ := by
    intro a h
    rw [memB, pow_succ] at h
    exact eq_inv_of_mul_eq_one_left h
  let g : K → K := fun a => a + a⁻¹
  have maps : ∀ a ∈ A ∪ B, g a ∈ Finset.univ.image ι := by
    intro a ha
    apply fixed
    change (a + a⁻¹) ^ p = a + a⁻¹
    rw [add_pow_char, inv_pow]
    rcases Finset.mem_union.mp ha with h | h
    · rw [powA a h]
    · rw [powB a h, inv_inv, add_comm]
  have mapsI : ∀ a ∈ A ∩ B, g a ∈ Finset.univ.image ι :=
    fun a ha => maps a (Finset.mem_union_left _ (Finset.mem_inter.mp ha).1)
  let f : K → K := fun a => a ^ m + a⁻¹ ^ m
  let c : K → K := fun y => (Chebyshev.C K (m : ℤ)).eval y
  have fc : ∀ a : K, a ≠ 0 → f a = c (g a) := fun a ha => (cheb_eval a ha m).symm
  have fib : ∀ y ∈ Finset.univ.image ι,
      ((A ∪ B).filter (fun a => g a = y)).card + ((A ∩ B).filter (fun a => g a = y)).card
        = 2 := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    -- a root of a² - y a + 1
    obtain ⟨a, ha⟩ : ∃ a : K, a ^ 2 - ι x * a + 1 = 0 := by
      have deg : (X ^ 2 - Polynomial.C (ι x) * X + 1 : K[X]).degree = 2 := by
        compute_degree!
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_root
        (X ^ 2 - Polynomial.C (ι x) * X + 1 : K[X]) (by rw [deg]; decide)
      refine ⟨a, ?_⟩
      simpa [IsRoot] using ha
    have a0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have mul1 : a * a⁻¹ = 1 := mul_inv_cancel₀ a0
    have ga : g a = ι x := by
      change a + a⁻¹ = ι x
      apply mul_left_cancel₀ a0
      linear_combination ha + mul1
    have yp : (ι x) ^ p = ι x := by rw [← map_pow, ZMod.pow_card]
    have aU : a ∈ A ∨ a ∈ B := by
      have e : a ^ p + (a ^ p)⁻¹ = a + a⁻¹ := by
        have : (a + a⁻¹) ^ p = a + a⁻¹ := by
          change (g a) ^ p = g a
          rw [ga, yp]
        rwa [add_pow_char, inv_pow] at this
      have ap0 : a ^ p ≠ 0 := pow_ne_zero _ a0
      have fac : (a ^ p - a) * (a ^ p * a - 1) = 0 := by
        have h1 : a ^ p * (a ^ p)⁻¹ = 1 := mul_inv_cancel₀ ap0
        linear_combination (a ^ p * a) * e - a * h1 + a ^ p * mul1
      rcases mul_eq_zero.mp fac with h | h
      · left
        rw [memA]
        apply mul_right_cancel₀ a0
        rw [one_mul, ← pow_succ, show p - 1 + 1 = p by omega]
        exact sub_eq_zero.mp h
      · right
        rw [memB, pow_succ]
        exact sub_eq_zero.mp h
    have invmem : ∀ b : K, b ∈ A ∨ b ∈ B → b⁻¹ ∈ A ∨ b⁻¹ ∈ B := by
      rintro b (h | h)
      · left; rw [memA] at h ⊢; rw [inv_pow, h, inv_one]
      · right; rw [memB] at h ⊢; rw [inv_pow, h, inv_one]
    have roots : ∀ b : K, b ∈ A ∨ b ∈ B → (g b = ι x ↔ b = a ∨ b = a⁻¹) := by
      intro b hb
      have b0 := nz b hb
      have mulb : b * b⁻¹ = 1 := mul_inv_cancel₀ b0
      constructor
      · intro h
        change b + b⁻¹ = ι x at h
        rw [← ga] at h
        change b + b⁻¹ = a + a⁻¹ at h
        have : (b - a) * (b - a⁻¹) = 0 := by
          linear_combination b * h - mulb + mul1
        rcases mul_eq_zero.mp this with h' | h'
        · exact Or.inl (sub_eq_zero.mp h')
        · exact Or.inr (sub_eq_zero.mp h')
      · rintro (rfl | rfl)
        · exact ga
        · change a⁻¹ + a⁻¹⁻¹ = ι x
          rw [inv_inv, add_comm]
          exact ga
    have fU : (A ∪ B).filter (fun b => g b = ι x) = {a, a⁻¹} := by
      ext b
      rw [Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hb, h⟩
        exact (roots b hb).mp h
      · intro h
        have hb : b ∈ A ∨ b ∈ B := by
          rcases h with rfl | rfl
          · exact aU
          · exact invmem a aU
        exact ⟨hb, (roots b hb).mpr h⟩
    have both : ∀ b : K, b ∈ A ∩ B ↔ b = b⁻¹ ∧ b ≠ 0 := by
      intro b
      rw [Finset.mem_inter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, nz b (Or.inl h1)⟩
        rw [← powB b h2, powA b h1]
      · rintro ⟨h, b0⟩
        have sq : b ^ 2 = 1 := by
          rw [sq]
          nth_rewrite 2 [h]
          exact mul_inv_cancel₀ b0
        obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
        constructor
        · rw [memA, show p - 1 = 2 * k by omega, pow_mul, sq, one_pow]
        · rw [memB, show p + 1 = 2 * (k + 1) by omega, pow_mul, sq, one_pow]
    by_cases h : a = a⁻¹
    · have fI : (A ∩ B).filter (fun b => g b = ι x) = {a} := by
        ext b
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hb, e⟩
          rcases (roots b (Or.inl (Finset.mem_inter.mp hb).1)).mp e with h' | h'
          · exact h'
          · rw [h', ← h]
        · intro hb
          rw [hb]
          exact ⟨(both a).mpr ⟨h, a0⟩, ga⟩
      rw [fU, fI, ← h]
      simp
    · have fI : (A ∩ B).filter (fun b => g b = ι x) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro b hb e
        have hb' := (both b).mp hb
        rcases (roots b (Or.inl (Finset.mem_inter.mp hb).1)).mp e with h' | h'
        · rw [h'] at hb'
          exact h hb'.1
        · rw [h', inv_inv] at hb'
          exact h hb'.1.symm
      rw [fU, fI, Finset.card_pair h, Finset.card_empty]
  have total : ∑ a ∈ A, f a + ∑ a ∈ B, f a = 2 * ∑ y ∈ Finset.univ.image ι, c y := by
    rw [← Finset.sum_union_inter, ← Finset.sum_fiberwise_of_maps_to maps,
      ← Finset.sum_fiberwise_of_maps_to mapsI, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have h1 : ∑ a ∈ (A ∪ B).filter (fun a => g a = y), f a
        = ∑ _a ∈ (A ∪ B).filter (fun a => g a = y), c y := by
      refine Finset.sum_congr rfl (fun a ha => ?_)
      obtain ⟨ha, e⟩ := Finset.mem_filter.mp ha
      rw [fc a (nz a (Finset.mem_union.mp ha)), e]
    have h2 : ∑ a ∈ (A ∩ B).filter (fun a => g a = y), f a
        = ∑ _a ∈ (A ∩ B).filter (fun a => g a = y), c y := by
      refine Finset.sum_congr rfl (fun a ha => ?_)
      obtain ⟨ha, e⟩ := Finset.mem_filter.mp ha
      rw [fc a (nz a (Or.inl (Finset.mem_inter.mp ha).1)), e]
    rw [h1, h2, Finset.sum_const, Finset.sum_const, ← add_nsmul, fib y hy, nsmul_eq_mul,
      Nat.cast_ofNat]
  have sumA : ∑ a ∈ A, f a = 2 * (if (p - 1) ∣ m then (-1 : K) else 0) := by
    simp only [f, Finset.sum_add_distrib]
    rw [inv_sum (p - 1) m (by omega), power_sum (p - 1) m (by omega) z1 hz1, cast1, two_mul]
  have sumB : ∑ a ∈ B, f a = 2 * (if (p + 1) ∣ m then (1 : K) else 0) := by
    simp only [f, Finset.sum_add_distrib]
    rw [inv_sum (p + 1) m (by omega), power_sum (p + 1) m (by omega) z2 hz2, cast2, two_mul]
  rw [sumA, sumB, ← mul_add] at total
  have fin := mul_left_cancel₀ two0 total
  apply ιinj
  rw [map_sum, map_add, apply_ite ι, apply_ite ι, map_neg, map_one, map_zero, fin,
    Finset.sum_image (fun x _ y _ h => ιinj h)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  change ι (eval x (Chebyshev.C (ZMod p) (m : ℤ))) = eval (ι x) (Chebyshev.C K (m : ℤ))
  rw [← Chebyshev.map_C ι, eval_map_apply]

end ChebyshevSumModP

theorem OMA.solution : OMA.R_mse_2615963_R3.H1 := by
  intro p hp hp2 m
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  have key := ChebyshevSumModP.main p hp2 m
  have conv : ((∑ k ∈ Finset.range p,
      (Polynomial.Chebyshev.C ℤ (m : ℤ)).eval (k : ℤ) : ℤ) : ZMod p)
      = ∑ x : ZMod p, (Polynomial.Chebyshev.C (ZMod p) (m : ℤ)).eval x := by
    rw [Int.cast_sum]
    refine Finset.sum_nbij (fun k => (k : ZMod p)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb h
      rw [Finset.coe_range, Set.mem_Iio] at ha hb
      have := congrArg ZMod.val h
      rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this
    · intro x _
      exact ⟨x.val, Finset.mem_coe.mpr (Finset.mem_range.mpr x.val_lt),
        ZMod.natCast_zmod_val x⟩
    · intro k _
      rw [← Polynomial.Chebyshev.map_C (Int.castRingHom (ZMod p))]
      have : ((k : ℕ) : ZMod p) = Int.castRingHom (ZMod p) (k : ℤ) := by simp
      rw [this, Polynomial.eval_map_apply]
      rfl
  rw [conv, key, Int.cast_add]
  congr 1 <;> split_ifs <;> simp
