import OMAStatements.S_oeis_a106521
import Mathlib

namespace OMA.Helpers_a106521
open OMA.S_oeis_a106521

def XZ : ℕ → ℤ × ℤ
  | 0 => (23, 7)
  | 1 => (43, 13)
  | n + 2 => (10 * (XZ n).1 + 33 * (XZ n).2, 3 * (XZ n).1 + 10 * (XZ n).2)

lemma XZ_succ2 (n : ℕ) : XZ (n + 2) = (10 * (XZ n).1 + 33 * (XZ n).2, 3 * (XZ n).1 + 10 * (XZ n).2) := rfl

lemma pell (n : ℕ) : (XZ n).1 ^ 2 - 11 * (XZ n).2 ^ 2 = -10 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => norm_num [XZ]
    | 1 => norm_num [XZ]
    | n + 2 =>
      rw [XZ_succ2]; simp only
      linear_combination ih n (by omega)

lemma mono (n : ℕ) : 0 < (XZ n).1 ∧ 0 < (XZ n).2 ∧ (XZ n).1 < (XZ (n + 1)).1 ∧
    (XZ n).2 < (XZ (n + 1)).2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => norm_num [XZ]
    | 1 => norm_num [XZ]
    | n + 2 =>
      have := ih n (by omega)
      have h1 := ih (n + 1) (by omega)
      rw [XZ_succ2, show n + 2 + 1 = (n + 1) + 2 by ring, XZ_succ2]; simp only
      refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- descent classification -/
lemma classify (z : ℕ) : ∀ x : ℤ, 0 < x → x ^ 2 - 11 * (z : ℤ) ^ 2 = -10 →
    (x = 1 ∧ z = 1) ∨ ∃ n, x = (XZ n).1 ∧ (z : ℤ) = (XZ n).2 := by
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro x hx hp
    rcases (show z = 0 ∨ z = 1 ∨ z = 2 ∨ 3 ≤ z by omega) with rfl | rfl | rfl | hz
    · simp at hp; nlinarith
    · left; refine ⟨?_, rfl⟩
      have h : (x - 1) * (x + 1) = 0 := by push_cast at hp; linear_combination hp
      rcases mul_eq_zero.mp h with h | h <;> linarith
    · exfalso
      have : x ^ 2 = 34 := by push_cast at hp; linarith
      have h5 : x < 6 := by nlinarith
      have h6 : 5 < x := by nlinarith
      omega
    · obtain ⟨x', hx'⟩ : ∃ x', x' = 10 * x - 33 * (z : ℤ) := ⟨_, rfl⟩
      obtain ⟨z', hz'⟩ : ∃ z', z' = 10 * (z : ℤ) - 3 * x := ⟨_, rfl⟩
      have hzz : 3 ≤ (z : ℤ) := by exact_mod_cast hz
      have hz'pos : 0 < z' := by nlinarith
      have hz'lt : z' < z := by nlinarith
      have hp' : x' ^ 2 - 11 * z' ^ 2 = -10 := by rw [hx', hz']; linear_combination hp
      have hxe : x = 10 * x' + 33 * z' := by rw [hx', hz']; ring
      have hze : (z : ℤ) = 3 * x' + 10 * z' := by rw [hx', hz']; ring
      obtain ⟨w, hw⟩ : ∃ w : ℕ, (w : ℤ) = z' := ⟨z'.toNat, by omega⟩
      rcases lt_trichotomy x' 0 with hneg | hzero | hpos
      · -- x' < 0 forces (x', z') = (-1, 1)
        have hzs : (z : ℤ) ≤ 9 := by nlinarith
        have hw8 : w ≤ 8 := by omega
        have hw8' : (w : ℤ) ≤ 8 := by exact_mod_cast hw8
        have hxb : -30 ≤ x' := by nlinarith
        right; refine ⟨0, ?_⟩
        rw [← hw] at hp' hxe hze
        have hxn : x' ≤ -1 := by omega
        have hw1 : 1 ≤ w := by omega
        clear ih hx' hz' hp hw hz'pos hz'lt
        interval_cases w <;> interval_cases x' <;>
          first | (norm_num at hp'; done) | omega | (constructor <;> norm_num [XZ, hxe, hze]; done)
      · exfalso; rw [hzero] at hp'; nlinarith
      · rcases ih w (by omega) x' hpos (by rw [hw]; exact hp') with ⟨h1, h2⟩ | ⟨n, h1, h2⟩
        · right; refine ⟨1, ?_⟩
          rw [h1] at hxe hze; rw [← hw, h2] at hxe hze; push_cast at hxe hze
          simp only [XZ]; constructor <;> linarith
        · right; refine ⟨n + 2, ?_⟩
          rw [XZ_succ2]; simp only
          rw [h1, ← hw, h2] at hxe hze
          exact ⟨hxe, hze⟩

lemma X_rec (j : ℕ) : (XZ (j + 4)).1 = 20 * (XZ (j + 2)).1 - (XZ j).1 := by
  rw [show j + 4 = (j + 2) + 2 by ring, XZ_succ2, XZ_succ2]; simp only; ring

lemma X_ge (n : ℕ) : 23 ≤ (XZ n).1 := by
  induction n with
  | zero => norm_num [XZ]
  | succ n ih => have := (mono n).2.2.1; linarith

lemma sum_eq (m : ℕ) : ∑ k ∈ Finset.range 11, (m + k) ^ 2 = 11 * ((m + 5) ^ 2 + 10) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; ring

lemma mem_iff (m : ℕ) : IsSquare (∑ k ∈ Finset.range 11, (m + k) ^ 2) ↔
    ∃ n, (m : ℤ) + 5 = (XZ n).1 := by
  rw [sum_eq]
  constructor
  · rintro ⟨r, hr⟩
    have h11 : 11 ∣ r * r := ⟨_, hr.symm⟩
    obtain ⟨q, rfl⟩ := (Nat.Prime.dvd_mul (by norm_num)).mp h11 |>.elim id id
    have hq : (m + 5) ^ 2 + 10 = 11 * (q * q) := by nlinarith
    have hz : ((m : ℤ) + 5) ^ 2 - 11 * (q : ℤ) ^ 2 = -10 := by
      have := congrArg (fun t : ℕ => (t : ℤ)) hq; push_cast at this; linear_combination this
    rcases classify q _ (by positivity) hz with ⟨h1, _⟩ | ⟨n, h1, _⟩
    · omega
    · exact ⟨n, h1⟩
  · rintro ⟨n, hn⟩
    refine ⟨11 * (XZ n).2.toNat, ?_⟩
    have hz := (mono n).2.1
    have hp := pell n
    zify
    rw [Int.toNat_of_nonneg hz.le]
    push_cast
    rw [hn]; linear_combination 11 * hp

def Y (n : ℕ) : ℕ := ((XZ n).1 - 5).toNat

lemma Y_cast (n : ℕ) : (Y n : ℤ) = (XZ n).1 - 5 := by
  have := X_ge n; unfold Y; omega

lemma Y_mono : StrictMono Y := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h1 := Y_cast n; have h2 := Y_cast (n + 1); have := (mono n).2.2.1
  omega

lemma nth_eq (n : ℕ) :
    Nat.nth (fun m => IsSquare (∑ k ∈ Finset.range 11, (m + k) ^ 2)) n = Y n := by
  set p := fun m => IsSquare (∑ k ∈ Finset.range 11, (m + k) ^ 2) with hp
  have hmaps : ∀ j, p (Y j) := fun j => by
    rw [hp]; simp only; rw [mem_iff]; exact ⟨j, by rw [Y_cast]; ring⟩
  have hinf : (Set.ofPred p).Infinite :=
    Set.infinite_of_injective_forall_mem Y_mono.injective (fun j => hmaps j)
  have hmem : ∀ j, j ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred p), n < hf.toFinset.card } :=
    fun j hf => absurd hf hinf
  symm
  refine Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn Y ?_ ?_ ?_ (hmem n)
  · intro m hm
    have hm' : IsSquare (∑ k ∈ Finset.range 11, (m + k) ^ 2) := hm
    obtain ⟨j, hj⟩ := (mem_iff m).1 hm'
    refine ⟨j, hmem j, ?_⟩
    have := Y_cast j; omega
  · intro j _; exact hmaps j
  · intro i _ j _ hij; exact Y_mono hij

end OMA.Helpers_a106521

open OMA.S_oeis_a106521 OMA.Helpers_a106521 in
theorem OMA.solution : type_of% @OMA.S_oeis_a106521.main := by
  have hA : ∀ n, (a (n + 1) : ℤ) = (XZ n).1 - 5 := fun n => by
    unfold a; rw [if_neg (by omega), show n + 1 - 1 = n by omega, nth_eq, Y_cast]
  have hA0 : a 0 = 0 := by simp [a]
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ)) with hF
  have hL : (1 - PowerSeries.X) * (1 - 20 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4) * F =
      F - F * PowerSeries.X ^ 1 - 20 * (F * PowerSeries.X ^ 2) + 20 * (F * PowerSeries.X ^ 3) +
        F * PowerSeries.X ^ 4 - F * PowerSeries.X ^ 5 := by ring
  have hR : (2 * PowerSeries.X * (9 + 10 * PowerSeries.X + 29 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 -
      2 * PowerSeries.X ^ 4) : PowerSeries ℤ) =
      18 * PowerSeries.X ^ 1 + 20 * PowerSeries.X ^ 2 + 58 * PowerSeries.X ^ 3 -
        2 * PowerSeries.X ^ 4 - 4 * PowerSeries.X ^ 5 := by ring
  rw [hL, hR]
  ext d
  simp only [map_add, map_sub, ← map_ofNat PowerSeries.C, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul_X_pow, hF, PowerSeries.coeff_mk]
  rcases (show d ≤ 5 ∨ 6 ≤ d by omega) with hd | hd
  · have a1 := hA 0
    have a2 := hA 1
    have a3 := hA 2
    have a4 := hA 3
    have a5 := hA 4
    simp only [XZ] at a1 a2 a3 a4 a5
    norm_num at a1 a2 a3 a4 a5
    interval_cases d <;> simp only [PowerSeries.coeff_C, hA0, a1, a2, a3, a4, a5, Nat.cast_zero] <;>
      norm_num [hA0, a1, a2, a3, a4, a5]
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 6 := ⟨d - 6, by omega⟩
    have c1 : 1 ≤ k + 6 := by omega
    have c2 : 2 ≤ k + 6 := by omega
    have c3 : 3 ≤ k + 6 := by omega
    have c4 : 4 ≤ k + 6 := by omega
    have c5 : 5 ≤ k + 6 := by omega
    have n1 : k + 6 ≠ 1 := by omega
    have n2 : k + 6 ≠ 2 := by omega
    have n3 : k + 6 ≠ 3 := by omega
    have n4 : k + 6 ≠ 4 := by omega
    have n5 : k + 6 ≠ 5 := by omega
    simp only [c1, c2, c3, c4, c5, n1, n2, n3, n4, n5, if_true, if_false, ↓reduceIte]
    rw [show k + 6 - 1 = (k + 4) + 1 by omega, show k + 6 - 2 = (k + 3) + 1 by omega,
      show k + 6 - 3 = (k + 2) + 1 by omega, show k + 6 - 4 = (k + 1) + 1 by omega,
      show k + 6 - 5 = k + 1 by omega, show k + 6 = (k + 5) + 1 by omega]
    rw [hA, hA, hA, hA, hA, hA]
    have r1 := X_rec (k + 1)
    have r2 := X_rec k
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 2 = k + 3 by ring] at r1
    simp only [PowerSeries.coeff_C, Nat.add_one_ne_zero, if_false, ↓reduceIte]
    linear_combination r1 - r2
