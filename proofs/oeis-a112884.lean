import OMAStatements.S_oeis_a112884
import Mathlib

-- Problem: A112884: Number of bits required to represent binomial(2^n, 2^(n-1)).
-- Upstream: formal-conjectures statements/oeis-a112884.lean:0 (declaration OMA.S_oeis_a112884.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Let c(m) = binomial(2m, m). By induction from (m+1) c(m+1) = 2 (2m+1) c(m),
16^m <= 4 m c(m)^2 for m >= 1 and (3m+1) c(m)^2 <= 16^m for all m. With m = 2^(n-1) these give
2^E <= c(m) < 2^(E+1) for E = 2^n - floor(n/2) - 1: for odd n = 2j+1 one has 4 m (2^E)^2 = 16^m,
and for even n = 2j+2 one has 8 m (2^E)^2 = 16^m. So c(m) has exactly E + 1 binary digits. -/

namespace A112884Aux

open OMA.S_oeis_a112884

theorem lower : ∀ m : ℕ, 1 ≤ m → 16 ^ m ≤ 4 * m * Nat.centralBinom m ^ 2 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => norm_num [Nat.centralBinom]
  | succ m hm ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    refine le_of_mul_le_mul_left ?_ (show 0 < m + 1 by omega)
    have e : (m + 1) * (4 * (m + 1) * Nat.centralBinom (m + 1) ^ 2) =
        4 * ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 := by ring
    rw [e, h]
    calc (m + 1) * 16 ^ (m + 1) = 16 * (m + 1) * 16 ^ m := by ring
      _ ≤ 16 * (m + 1) * (4 * m * Nat.centralBinom m ^ 2) := Nat.mul_le_mul_left _ ih
      _ = (16 * (4 * m * (m + 1))) * Nat.centralBinom m ^ 2 := by ring
      _ ≤ (16 * ((2 * m + 1) ^ 2)) * Nat.centralBinom m ^ 2 := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_left
          nlinarith
      _ = 4 * (2 * (2 * m + 1) * Nat.centralBinom m) ^ 2 := by ring

theorem upper : ∀ m : ℕ, (3 * m + 1) * Nat.centralBinom m ^ 2 ≤ 16 ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    have hpos : 0 < (m + 1) ^ 2 := by positivity
    refine le_of_mul_le_mul_left ?_ hpos
    have e : (m + 1) ^ 2 * ((3 * (m + 1) + 1) * Nat.centralBinom (m + 1) ^ 2) =
        (3 * m + 4) * ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 := by ring
    rw [e, h]
    calc (3 * m + 4) * (2 * (2 * m + 1) * Nat.centralBinom m) ^ 2
        = (4 * (3 * m + 4) * (2 * m + 1) ^ 2) * Nat.centralBinom m ^ 2 := by ring
      _ ≤ (16 * (m + 1) ^ 2 * (3 * m + 1)) * Nat.centralBinom m ^ 2 := by
          apply Nat.mul_le_mul_right
          nlinarith [sq_nonneg m]
      _ = 16 * (m + 1) ^ 2 * ((3 * m + 1) * Nat.centralBinom m ^ 2) := by ring
      _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
      _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring

theorem log_eq (m E : ℕ) (hm : 1 ≤ m) (K : 4 * m * (2 ^ E) ^ 2 ≤ 16 ^ m)
    (K' : 16 ^ m < (3 * m + 1) * (2 ^ (E + 1)) ^ 2) : Nat.log 2 (Nat.centralBinom m) = E := by
  have hl := lower m hm
  have hu := upper m
  have h1 : (2 ^ E) ^ 2 ≤ Nat.centralBinom m ^ 2 :=
    le_of_mul_le_mul_left (K.trans hl) (by omega : 0 < 4 * m)
  have h2 : Nat.centralBinom m ^ 2 < (2 ^ (E + 1)) ^ 2 :=
    lt_of_mul_lt_mul_left (lt_of_le_of_lt hu K') (Nat.zero_le _)
  have h3 : 2 ^ E ≤ Nat.centralBinom m := (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  have h4 : Nat.centralBinom m < 2 ^ (E + 1) := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h2
  exact Nat.log_eq_of_pow_le_of_lt_pow h3 h4

theorem odd_case (j E t : ℕ) (ht : t = 2 ^ (2 * j)) (hW : 2 * t = E + j + 1) :
    4 * t * (2 ^ E) ^ 2 = 16 ^ t := by
  have e2 : (16 : ℕ) ^ t = 2 ^ (4 * t) := by
    rw [show (16 : ℕ) = 2 ^ 4 from by norm_num, ← pow_mul]
  have e3 : (2 : ℕ) ^ (4 * t) = 2 ^ (2 + 2 * j + 2 * E) := by
    congr 1
    omega
  rw [e2, e3, ht]
  ring

theorem even_case (j E t : ℕ) (ht : t = 2 ^ (2 * j + 1)) (hW : 2 * t = E + j + 2) :
    8 * t * (2 ^ E) ^ 2 = 16 ^ t := by
  have e2 : (16 : ℕ) ^ t = 2 ^ (4 * t) := by
    rw [show (16 : ℕ) = 2 ^ 4 from by norm_num, ← pow_mul]
  have e3 : (2 : ℕ) ^ (4 * t) = 2 ^ (3 + (2 * j + 1) + 2 * E) := by
    congr 1
    omega
  rw [e2, e3, ht]
  ring

theorem a_succ (k : ℕ) : a (k + 1) = Nat.log 2 (Nat.centralBinom (2 ^ k)) + 1 := by
  unfold a
  have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [Nat.add_sub_cancel, h1, ← Nat.centralBinom_eq_two_mul_choose,
    Nat.length_digits 2 _ (by norm_num) (Nat.centralBinom_pos _).ne']

theorem main_odd (j : ℕ) : a (2 * j + 1) = 2 ^ (2 * j + 1) - (2 * j + 1) / 2 := by
  have hlt : 2 * j + 1 < 2 ^ (2 * j + 1) := Nat.lt_two_pow_self
  have hp : 2 ^ (2 * j + 1) = 2 * 2 ^ (2 * j) := by ring
  obtain ⟨E, hE⟩ : ∃ E, 2 * 2 ^ (2 * j) = E + j + 1 := ⟨2 * 2 ^ (2 * j) - j - 1, by omega⟩
  have hK := odd_case j E (2 ^ (2 * j)) rfl hE
  have hpos : 1 ≤ 2 ^ (2 * j) := Nat.one_le_two_pow
  have hlog : Nat.log 2 (Nat.centralBinom (2 ^ (2 * j))) = E := by
    apply log_eq _ _ hpos (le_of_eq hK)
    have e : (3 * 2 ^ (2 * j) + 1) * (2 ^ (E + 1)) ^ 2 =
        3 * (4 * 2 ^ (2 * j) * (2 ^ E) ^ 2) + 4 * (2 ^ E) ^ 2 := by ring
    rw [e, hK]
    have h16 : 0 < 16 ^ 2 ^ (2 * j) := by positivity
    omega
  rw [a_succ, hlog, hp]
  omega

theorem main_even (j : ℕ) : a (2 * j + 2) = 2 ^ (2 * j + 2) - (2 * j + 2) / 2 := by
  have hlt : 2 * j + 2 < 2 ^ (2 * j + 2) := Nat.lt_two_pow_self
  have hp : 2 ^ (2 * j + 2) = 2 * 2 ^ (2 * j + 1) := by ring
  obtain ⟨E, hE⟩ : ∃ E, 2 * 2 ^ (2 * j + 1) = E + j + 2 := ⟨2 * 2 ^ (2 * j + 1) - j - 2, by omega⟩
  have hK := even_case j E (2 ^ (2 * j + 1)) rfl hE
  have hpos : 1 ≤ 2 ^ (2 * j + 1) := Nat.one_le_two_pow
  have hlog : Nat.log 2 (Nat.centralBinom (2 ^ (2 * j + 1))) = E := by
    apply log_eq _ _ hpos
    · have e0 : 8 * 2 ^ (2 * j + 1) * (2 ^ E) ^ 2 = 2 * (4 * 2 ^ (2 * j + 1) * (2 ^ E) ^ 2) := by
        ring
      have hK2 := hK
      rw [e0] at hK2
      omega
    · have e : 2 * ((3 * 2 ^ (2 * j + 1) + 1) * (2 ^ (E + 1)) ^ 2) =
          3 * (8 * 2 ^ (2 * j + 1) * (2 ^ E) ^ 2) + 8 * (2 ^ E) ^ 2 := by ring
      have h16 : 0 < 16 ^ 2 ^ (2 * j + 1) := by positivity
      rw [hK] at e
      omega
  have e1 : 2 * j + 2 = (2 * j + 1) + 1 := by omega
  rw [e1, a_succ, hlog, ← e1, hp]
  omega

end A112884Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a112884.main := by
  intro n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp [OMA.S_oeis_a112884.a]
  · rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have e : n = 2 * i + 2 := by omega
      rw [e]
      exact A112884Aux.main_even i
    · rw [hj]
      exact A112884Aux.main_odd j
