import OMAStatements.S_oeis_a306562
import Mathlib

open OMA.S_oeis_a306562


def tt (j : ℕ) : ℕ := j * (j + 1) / 2

theorem two_tt (j : ℕ) : 2 * tt j = j * (j + 1) := by
  unfold tt
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self j).two_dvd

theorem tt_succ (j : ℕ) : tt (j + 1) = tt j + (j + 1) := by
  have h1 := two_tt j
  have h2 := two_tt (j + 1)
  nlinarith

theorem tt_mono {i j : ℕ} (h : i ≤ j) : tt i ≤ tt j := by
  have h1 := two_tt i
  have h2 := two_tt j
  have : i * (i + 1) ≤ j * (j + 1) := Nat.mul_le_mul h (by omega)
  omega

theorem blk_eq (j k : ℕ) (hj : 1 ≤ j) (h1 : tt (j - 1) < k) (h2 : k ≤ tt j) : blk k = j := by
  apply le_antisymm
  · exact Nat.sInf_le (show k ≤ j * (j + 1) / 2 from h2)
  · apply le_csInf ⟨j, show k ≤ j * (j + 1) / 2 from h2⟩
    intro i hi
    by_contra hlt
    have : tt i ≤ tt (j - 1) := tt_mono (by omega)
    have hi' : k ≤ tt i := hi
    omega

theorem blk_spec (k : ℕ) (hk : 1 ≤ k) : 1 ≤ blk k ∧ tt (blk k - 1) < k ∧ k ≤ tt (blk k) := by
  have hne : ({j : ℕ | k ≤ j * (j + 1) / 2} : Set ℕ).Nonempty := by
    refine ⟨k, ?_⟩
    show k ≤ tt k
    have := two_tt k
    nlinarith
  have hmem : k ≤ tt (blk k) := Nat.sInf_mem hne
  have h1 : 1 ≤ blk k := by
    by_contra h0
    have : blk k = 0 := by omega
    rw [this] at hmem
    simp [tt] at hmem
    omega
  refine ⟨h1, ?_, hmem⟩
  by_contra hc
  have : blk k ≤ blk k - 1 := Nat.sInf_le (show k ≤ (blk k - 1) * (blk k - 1 + 1) / 2 by
    show k ≤ tt (blk k - 1); omega)
  omega

noncomputable def sg (k : ℕ) : ℤ := if blk k % 2 = 1 then 1 else -1

theorem a_zero : a 0 = 1 := by simp [a]

theorem a_succ (m : ℕ) : a (m + 1) = a m + sg (m + 1) * ((m + 1 : ℕ) + 1) := by
  unfold a sg
  rw [Finset.sum_Icc_succ_top (by omega)]
  split_ifs <;> ring

theorem sign_blk (n : ℕ) : (if (n + 1) % 2 = 1 then (1 : ℤ) else -1) = (-1) ^ n := by
  rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [if_pos (by omega), show r + r = 2 * r by ring, pow_mul]; norm_num
  · rw [if_neg (by omega), pow_succ, pow_mul]; norm_num

theorem block (n : ℕ) : ∀ i, i ≤ n + 1 →
    2 * a (tt n + i) = 2 * a (tt n) + (-1) ^ n * (2 * i * ((tt n : ℤ) + 1) + i * (i + 1)) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hb : blk (tt n + i + 1) = n + 1 := by
      apply blk_eq (n + 1) _ (by omega)
      · simp only [Nat.add_sub_cancel]; omega
      · rw [tt_succ]; omega
    rw [← Nat.add_assoc, a_succ, sg, hb, sign_blk, mul_add, ih (by omega)]
    push_cast
    ring

theorem value (n : ℕ) : 16 * a (tt n) = (-1) ^ (n + 1) * (2 * n + 1) * (2 * n ^ 2 + 2 * n + 5) + 21 := by
  induction n with
  | zero => simp [tt, a_zero]
  | succ n ih =>
    have hb := block n (n + 1) le_rfl
    rw [← tt_succ] at hb
    have ht : (2 : ℤ) * (tt n : ℤ) = n * (n + 1) := by exact_mod_cast two_tt n
    have e : 16 * a (tt (n + 1)) = 8 * (2 * a (tt (n + 1))) := by ring
    rw [e, hb]
    have e2 : 8 * (2 * a (tt n) + (-1) ^ n * (2 * ((n + 1 : ℕ) : ℤ) * ((tt n : ℤ) + 1) +
        ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) + 1))) =
        16 * a (tt n) + 8 * (-1) ^ n * ((n + 1 : ℤ) * (2 * (tt n : ℤ)) + 2 * (n + 1) + (n + 1) * (n + 2)) := by
      push_cast; ring
    rw [e2, ih, ht]
    push_cast
    ring

theorem sg_ne (m : ℕ) (hm : 1 ≤ m) : (sg m ≠ sg (m + 1)) ↔ ∃ n : ℕ, 1 ≤ n ∧ m = tt n := by
  obtain ⟨h1, h2, h3⟩ := blk_spec m hm
  set j := blk m with hj
  constructor
  · intro hne
    refine ⟨j, h1, ?_⟩
    by_contra hc
    have : blk (m + 1) = j := blk_eq j (m + 1) h1 (by omega) (by omega)
    apply hne
    unfold sg; rw [this]
  · rintro ⟨n, hn, rfl⟩
    have e1 : blk (tt n) = n := blk_eq n (tt n) hn (by
      obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
      rw [tt_succ]; simp) le_rfl
    have e2 : blk (tt n + 1) = n + 1 := blk_eq (n + 1) (tt n + 1) (by omega) (by simp) (by rw [tt_succ]; omega)
    unfold sg; rw [e1, e2]
    rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · rw [if_neg (by omega), if_pos (by omega)]; norm_num
    · rw [if_pos (by omega), if_neg (by omega)]; norm_num

theorem sg_cases (k : ℕ) : sg k = 1 ∨ sg k = -1 := by
  unfold sg; split_ifs <;> simp

theorem OMA.solution : type_of% @OMA.S_oeis_a306562.main := by
  refine ⟨fun n _ => value n, ?_⟩
  intro m hm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have key := sg_ne (m' + 1) hm
  have e : (a (m' + 1 - 1) - a (m' + 1)) * (a (m' + 1 + 1) - a (m' + 1)) =
      -(sg (m' + 1) * sg (m' + 1 + 1)) * (((m' : ℤ) + 2) * ((m' : ℤ) + 3)) := by
    rw [Nat.add_sub_cancel, a_succ (m' + 1), a_succ m']
    push_cast
    ring
  rw [e]
  show _ ↔ ∃ n, 1 ≤ n ∧ m' + 1 = tt n
  rw [← key]
  have hpos : (0 : ℤ) < ((m' : ℤ) + 2) * ((m' : ℤ) + 3) := by positivity
  rcases sg_cases (m' + 1) with h1 | h1 <;> rcases sg_cases (m' + 1 + 1) with h2 | h2 <;>
    rw [h1, h2] <;> constructor <;> intro h <;>
    first | exact absurd rfl h | nlinarith | norm_num
