import FormalConjectures.ErdosProblems.«770»

/-! Jacobi reciprocity makes every small positive integer a square modulo the chosen prime. -/

open Erdos770
theorem OMA.solution : type_of% @Erdos770.erdos_770.variants.odd_h_unbounded := by
  intro a
  let K := a + 2
  have : NeZero (8 * K.factorial) := ⟨by positivity⟩
  obtain ⟨p, hpK, hp, hpa⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 8 * K.factorial) isUnit_one.neg K
  have := Fact.mk hp
  have hdvd : 8 * K.factorial ∣ p + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hpa]; ring
  have h8 : 8 ∣ p + 1 := dvd_trans ⟨_, rfl⟩ hdvd
  let n := p / 2
  have hp4 : p % 4 = 3 := by omega
  have hpOdd : Odd p := Nat.odd_iff.mpr (by omega)
  have hjtwo : jacobiSym 2 p = 1 := by
    rw [jacobiSym.at_two hpOdd, ZMod.χ₈_nat_mod_eight, show p % 8 = 7 by omega]
    decide +kernel
  have hfactor : K.factorial ∣ p + 1 := dvd_trans (dvd_mul_left _ _) hdvd
  have hj (i : ℕ) : 0 < i → i ≤ K → jacobiSym (i : ℤ) p = 1 := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi0 hiK
      rcases Nat.even_or_odd i with ⟨j, he⟩ | ho
      · have eq : (i : ℤ) = 2 * (j : ℤ) := by exact_mod_cast (show i = 2 * j by omega)
        rw [eq, jacobiSym.mul_left, hjtwo, ih j (by omega) (by omega) (by omega), one_mul]
      · have hm : (-1 : ℤ) ≡ (p : ℤ) [ZMOD (i : ℤ)] := Int.modEq_iff_dvd.mpr (by
          simpa [sub_neg_eq_add] using Int.natCast_dvd_natCast.mpr
            ((Nat.dvd_factorial hi0 hiK).trans hfactor))
        have hsign : qrSign p i = jacobiSym (-1) i := by
          rw [qrSign, ZMod.χ₄_nat_three_mod_four hp4]
        rw [jacobiSym.quadratic_reciprocity' ho hpOdd, jacobiSym.mod_left' hm.symm, ← hsign,
          ← pow_two]
        exact qrSign.sq_eq_one hpOdd ho
  have hres (i : ℕ) (hi0 : 0 < i) (hiK : i ≤ K) : (i : ZMod p) ^ n = 1 := by
    have eq := legendreSym.eq_pow p (i : ℤ)
    rw [jacobiSym.legendreSym.to_jacobiSym, hj i hi0 hiK] at eq
    simpa [n] using eq.symm
  have hn3 : 3 ≤ n := by have := hpK; omega
  let M := 2 ^ n - 1
  have hM : 7 ≤ M := by have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn3; omega
  let g (m : ℕ) := ((Finset.Icc 2 m).image fun i => i ^ n - 1).gcd id
  let S : Set ℕ∞ := {m | 2 < m ∧ g m.toNat = 1}
  have hmem : (M : ℕ∞) ∈ S := by
    refine ⟨by exact_mod_cast (by omega : 2 < M), ?_⟩
    change g M = 1
    have hd (i : ℕ) (h1 : 2 ≤ i) (h2 : i ≤ M) : g M ∣ i ^ n - 1 :=
      Finset.gcd_dvd (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨h1, h2⟩))
    have hd2 := hd 2 le_rfl (by omega)
    have hdM := hd M (by omega) le_rfl
    have h1 : 1 ≤ M ^ n := Nat.one_le_pow n M (by omega)
    exact Nat.dvd_one.mp ((show M ^ n - (M ^ n - 1) = 1 by omega) ▸
      Nat.dvd_sub (dvd_pow hd2 (by omega)) hdM)
  have hge : ((K + 1 : ℕ) : ℕ∞) ≤ h n := le_sInf (s := S) fun x ⟨_, hgcd⟩ => by
    induction x using ENat.recTopCoe with
    | top => exact le_top
    | coe k =>
      change g k = 1 at hgcd
      by_contra hk
      rw [Nat.cast_le] at hk
      have hpG : p ∣ g k :=
        Finset.dvd_gcd fun b hb => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
          rw [Finset.mem_Icc] at hi
          rw [id, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
          push_cast; rw [hres i (by omega) (by omega), sub_self]
      exact hp.one_lt.ne' (Nat.dvd_one.mp (hgcd ▸ hpG))
  have hne : h n ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top M) (sInf_le hmem)
  refine ⟨(h n).toNat, ⟨h n, ⟨n, Nat.odd_iff.mpr (by omega), rfl⟩, rfl⟩, ?_⟩
  rw [← ENat.natCast_toNat hne, Nat.cast_le] at hge
  omega
