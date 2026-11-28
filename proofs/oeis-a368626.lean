import OMAStatements.S_oeis_a368626
import Mathlib

open OMA.S_oeis_a368626
open PowerSeries

namespace P368626

open Finset

theorem sym (f : ℕ → ZMod 2) (m : ℕ) :
    ∑ p ∈ antidiagonal m, f p.1 * f p.2 = if Even m then f (m / 2) * f (m / 2) else 0 := by
  have key : ∀ s : Finset (ℕ × ℕ), (∀ p ∈ s, p.1 ≠ p.2) → (∀ p ∈ s, p.swap ∈ s) →
      ∑ p ∈ s, f p.1 * f p.2 = 0 := by
    intro s hne hsw
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun p hp => hsw p hp) ?_
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm (f p.2)]
      exact CharTwo.add_self_eq_zero _
    · intro p hp _ h
      apply hne p hp
      have := congrArg Prod.fst h
      simpa using this.symm
    · intro p _; simp
  split_ifs with he
  · obtain ⟨k, rfl⟩ := he
    have hk : (k + k) / 2 = k := by omega
    rw [hk]
    have hmem : (k, k) ∈ antidiagonal (k + k) := by simp
    rw [← Finset.add_sum_erase _ _ hmem]
    rw [key, add_zero]
    · intro p hp
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
      intro h
      apply hp.1
      ext <;> simp <;> omega
    · intro p hp
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      refine ⟨?_, by simp; omega⟩
      intro h
      apply hp.1
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp at h1 h2
      ext <;> simp <;> omega
  · apply key
    · intro p hp h
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      apply he
      exact ⟨p.1, by omega⟩
    · intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      simp; omega

theorem c3_eq (A : PowerSeries ℤ) (n : ℕ) :
    coeff n (A ^ 3) = ∑ p ∈ antidiagonal n, coeff p.1 (A ^ 2) * coeff p.2 A := by
  rw [show A ^ 3 = A ^ 2 * A by ring, coeff_mul]

theorem c2_eq (A : PowerSeries ℤ) (n : ℕ) :
    coeff n (A ^ 2) = ∑ p ∈ antidiagonal n, coeff p.1 A * coeff p.2 A := by
  rw [pow_two, coeff_mul]

theorem coeff_two_mul (A : PowerSeries ℤ) (n : ℕ) : coeff n (2 * A) = 2 * coeff n A := by
  rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp, coeff_C_mul]

theorem coeff_rhs (A : PowerSeries ℤ) (n : ℕ) :
    coeff (n + 1) (2 + X * (A ^ 2 - (rescale (-1 : ℤ) A) ^ 2) + X * (A ^ 3 + (rescale (-1 : ℤ) A) ^ 3))
      = coeff n (A ^ 2) - (-1) ^ n * coeff n (A ^ 2) + (coeff n (A ^ 3) + (-1) ^ n * coeff n (A ^ 3)) := by
  rw [← map_pow, ← map_pow, map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul, map_add, map_sub,
    coeff_rescale, coeff_rescale, show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp, coeff_C]
  simp

theorem coeff_rel (A : PowerSeries ℤ) (h : IsGF A) (n : ℕ) :
    coeff (n + 1) A = if Even n then coeff n (A ^ 3) else coeff n (A ^ 2) := by
  have e := congrArg (coeff (n + 1)) h
  rw [coeff_two_mul, coeff_rhs] at e
  split_ifs with he
  · rw [he.neg_one_pow] at e; linarith
  · rw [(Nat.not_even_iff_odd.mp he).neg_one_pow] at e; linarith

theorem coeff_zero_eq (A : PowerSeries ℤ) (h : IsGF A) : coeff 0 A = 1 := by
  have e := congrArg (coeff 0) h
  rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp] at e
  rw [coeff_C_mul, map_add, map_add, coeff_C, coeff_zero_X_mul, coeff_zero_X_mul, if_pos rfl] at e
  linarith

theorem idem : ∀ x : ZMod 2, x * x = x := by decide

theorem not_pow2 (m : ℕ) (hm : 0 < m) (he : Even m) : ¬ ∃ k, m + 1 = 2 ^ k := by
  rintro ⟨k, hk⟩
  obtain ⟨r, rfl⟩ := he
  cases k with
  | zero => simp at hk; omega
  | succ k => rw [pow_succ] at hk; omega

theorem parity (A : PowerSeries ℤ) (h : IsGF A) :
    ∀ n, Odd (coeff n A) ↔ ∃ k, n + 1 = 2 ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => exact ⟨fun _ => ⟨0, rfl⟩, fun _ => by rw [coeff_zero_eq A h]; decide⟩
    | succ n =>
      rw [coeff_rel A h n, ← ZMod.intCast_eq_one_iff_odd]
      split_ifs with he
      · rw [c3_eq]
        push_cast
        have hsum : ∑ p ∈ antidiagonal n, ((coeff p.1 (A ^ 2) : ℤ) : ZMod 2) *
            ((coeff p.2 A : ℤ) : ZMod 2) = ((coeff (n / 2) A : ℤ) : ZMod 2) := by
          rw [Finset.sum_eq_single (n, 0)]
          · simp only
            rw [c2_eq]
            push_cast
            rw [sym (fun i => ((coeff i A : ℤ) : ZMod 2)) n, if_pos he, coeff_zero_eq A h, idem]
            simp
          · intro p hp hne
            rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
            rw [c2_eq]
            push_cast
            rw [sym (fun i => ((coeff i A : ℤ) : ZMod 2)) p.1]
            split_ifs with hp1
            · have h2 : 0 < p.2 := by
                rcases Nat.eq_zero_or_pos p.2 with h0 | h0
                · exact absurd (Prod.ext (by simp; omega) (by simpa using h0)) hne
                · exact h0
              have h3 : Even p.2 := by
                obtain ⟨u, hu⟩ := he; obtain ⟨v, hv⟩ := hp1; exact ⟨u - v, by omega⟩
              have h4 : ¬ Odd (coeff p.2 A) := by
                rw [ih p.2 (by omega)]; exact not_pow2 p.2 h2 h3
              rw [Int.not_odd_iff_even, ← ZMod.intCast_eq_zero_iff_even] at h4
              rw [h4, mul_zero]
            · rw [zero_mul]
          · intro hn; exfalso; apply hn; simp
        rw [hsum, ZMod.intCast_eq_one_iff_odd, ih (n / 2) (by omega)]
        obtain ⟨m, rfl⟩ := he
        have hm : (m + m) / 2 = m := by omega
        rw [hm]
        constructor
        · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [pow_succ]; omega⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
      · rw [c2_eq]
        push_cast
        rw [sym (fun i => ((coeff i A : ℤ) : ZMod 2)) n, if_neg he]
        simp only [zero_ne_one, false_iff]
        rintro ⟨k, hk⟩
        apply he
        cases k with
        | zero => simp at hk
        | succ k =>
          exact ⟨2 ^ k - 1, by rw [pow_succ] at hk; have := Nat.one_le_two_pow (n := k); omega⟩

def b : ℕ → ℤ
  | 0 => 1
  | n + 1 => if n % 2 = 0 then
        ∑ i : Fin (n + 1), (∑ j : Fin (i + 1), b j * b (i - j)) * b (n - i)
      else ∑ i : Fin (n + 1), b i * b (n - i)
decreasing_by
  all_goals first
    | (have := i.isLt; have := j.isLt; omega)
    | (have := i.isLt; omega)

theorem fin_sum (f : ℕ → ℤ) (m : ℕ) :
    ∑ p ∈ antidiagonal m, f p.1 * f p.2 = ∑ i : Fin (m + 1), f i * f (m - i) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Fin.sum_univ_eq_sum_range (fun i => f i * f (m - i))]

theorem exists_gf : ∃ A, IsGF A := by
  refine ⟨mk b, ?_⟩
  unfold IsGF
  ext n
  cases n with
  | zero =>
    rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp]
    rw [coeff_C_mul, map_add, map_add, coeff_C, coeff_zero_X_mul, coeff_zero_X_mul, if_pos rfl,
      coeff_mk, b]
    ring
  | succ n =>
    rw [coeff_two_mul]
    rw [coeff_rhs, c3_eq, c2_eq, coeff_mk]
    have hc2 : ∀ m, coeff m (mk b ^ 2) = ∑ i : Fin (m + 1), b i * b (m - i) := by
      intro m; rw [c2_eq]; simp only [coeff_mk]; exact fin_sum b m
    simp only [coeff_mk, hc2]
    rw [fin_sum b n, b, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Fin.sum_univ_eq_sum_range (fun i => (∑ j : Fin (i + 1), b j * b (i - j)) * b (n - i))]
    split_ifs with hn
    · rw [(Nat.even_iff.mpr hn).neg_one_pow]; ring
    · rw [(Nat.odd_iff.mpr (by omega)).neg_one_pow]; ring

end P368626

theorem OMA.solution : type_of% @OMA.S_oeis_a368626.main := by
  refine ⟨P368626.exists_gf, fun A h n => ?_⟩
  rw [P368626.parity A h n]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by have := Nat.one_le_two_pow (n := k); omega⟩
