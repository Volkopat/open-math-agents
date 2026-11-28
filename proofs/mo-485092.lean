import OMAStatements.S_mo_485092
import Mathlib

-- Problem: mo-485092, for every 2-colouring of the natural numbers, is there a difference d
-- such that one colour contains arbitrarily long arithmetic progressions with difference d?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No: colour n by the parity of its binary digit sum s(n) (Thue-Morse). We show that for every
-- d >= 1 there is a bound L such that every progression a, a + d, ..., of length L contains
-- two consecutive terms of different colours.
-- * If d = 2e is even, then s(a + k d) = s(a/2 + k e) + (a mod 2), so a bound for e works.
-- * If d is odd, take K with d < 2^K and M = 2^(K+2). Among the first M terms there are
--   N = 2^K - d and N' = 2^(K+1) - d modulo M. Then s(N + d) - s(N) = 1 - s(2^K - d) and
--   s(N' + d) - s(N') = 1 - s(2^(K+1) - d) = - s(2^K - d) up to the same high part, so one
--   of the two steps changes the parity.

namespace MO485092

def s : ℕ → ℕ
  | 0 => 0
  | n + 1 => s ((n + 1) / 2) + (n + 1) % 2
decreasing_by all_goals omega

theorem s_zero : s 0 = 0 := by
  rw [s]

theorem s_eq (n : ℕ) : s n = s (n / 2) + n % 2 := by
  cases n with
  | zero => simp [s_zero]
  | succ m => rw [s]

theorem s_one : s 1 = 1 := by
  have h := s_eq 1
  rw [h]
  show s 0 + 1 = 1
  rw [s_zero]

theorem split (M : ℕ) : ∀ lo H : ℕ, lo < 2 ^ M → s (lo + 2 ^ M * H) = s lo + s H := by
  induction M with
  | zero =>
    intro lo H h
    have h0 : lo = 0 := by simpa using h
    subst h0
    simp [s_zero]
  | succ M ih =>
    intro lo H h
    have e0 : 2 ^ (M + 1) * H = 2 * (2 ^ M * H) := by ring
    have hlo : lo / 2 < 2 ^ M := by
      have hp : 2 ^ (M + 1) = 2 * 2 ^ M := by ring
      omega
    have e1 : (lo + 2 * (2 ^ M * H)) / 2 = lo / 2 + 2 ^ M * H := by omega
    have e2 : (lo + 2 * (2 ^ M * H)) % 2 = lo % 2 := by omega
    rw [e0, s_eq (lo + 2 * (2 ^ M * H)), s_eq lo, e1, e2, ih (lo / 2) H hlo]
    omega

theorem s_pow (K : ℕ) : s (2 ^ K) = 1 := by
  have h := split K 0 1 (by positivity)
  simpa [s_zero, s_one] using h

theorem lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ]
    omega

theorem res (M d : ℕ) (hM : 0 < M) (hc : Nat.Coprime d M) (a r : ℕ) (hr : r < M) :
    ∃ j, j < M ∧ (a + j * d) % M = r := by
  have hne : NeZero M := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : ZMod M, u = ((r : ZMod M) - (a : ZMod M)) * (d : ZMod M)⁻¹ :=
    ⟨_, rfl⟩
  have hinv : (d : ZMod M)⁻¹ * (d : ZMod M) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one d hc
  have h1 : ((a + u.val * d : ℕ) : ZMod M) = (r : ZMod M) := by
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, hu, mul_assoc, hinv, mul_one]
    ring
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
  refine ⟨u.val, ZMod.val_lt u, ?_⟩
  rw [h2, Nat.mod_eq_of_lt hr]

theorem bound : ∀ d : ℕ, 0 < d → ∃ L₀ : ℕ, ∀ a : ℕ, ∃ k : ℕ, k + 1 < L₀ ∧
    s (a + k * d) % 2 ≠ s (a + (k + 1) * d) % 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases Nat.even_or_odd d with he | ho
    · obtain ⟨e, he⟩ := he
      have he0 : 0 < e := by omega
      obtain ⟨L₀, hL⟩ := ih e (by omega) he0
      refine ⟨L₀, fun a => ?_⟩
      obtain ⟨k, hk, hne⟩ := hL (a / 2)
      refine ⟨k, hk, ?_⟩
      have e1 := s_eq (a + k * d)
      have e2 := s_eq (a + (k + 1) * d)
      have x1 : k * d = 2 * (k * e) := by
        rw [he]
        ring
      have x2 : (k + 1) * d = 2 * ((k + 1) * e) := by
        rw [he]
        ring
      have d1 : (a + k * d) / 2 = a / 2 + k * e := by omega
      have d2 : (a + (k + 1) * d) / 2 = a / 2 + (k + 1) * e := by omega
      have m1 : (a + k * d) % 2 = a % 2 := by omega
      have m2 : (a + (k + 1) * d) % 2 = a % 2 := by omega
      rw [d1, m1] at e1
      rw [d2, m2] at e2
      omega
    · obtain ⟨K, hK⟩ : ∃ K, d < 2 ^ K := ⟨d, lt_two_pow d⟩
      have hM : 0 < 2 ^ (K + 2) := by positivity
      have hc : Nat.Coprime d (2 ^ (K + 2)) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr ho)
      have p1 : (2 : ℕ) ^ (K + 2) = 4 * 2 ^ K := by ring
      have p2 : (2 : ℕ) ^ (K + 1) = 2 * 2 ^ K := by ring
      refine ⟨2 ^ (K + 2) + 2, fun a => ?_⟩
      obtain ⟨j₁, hj₁, r₁⟩ := res (2 ^ (K + 2)) d hM hc a (2 ^ K - d) (by omega)
      obtain ⟨j₂, hj₂, r₂⟩ := res (2 ^ (K + 2)) d hM hc a (2 ^ (K + 1) - d) (by omega)
      by_contra hcon
      have q1 : s (a + j₁ * d) % 2 = s (a + (j₁ + 1) * d) % 2 := by
        by_contra hne
        exact hcon ⟨j₁, by omega, hne⟩
      have q2 : s (a + j₂ * d) % 2 = s (a + (j₂ + 1) * d) % 2 := by
        by_contra hne
        exact hcon ⟨j₂, by omega, hne⟩
      obtain ⟨H₁, hH₁⟩ : ∃ H, a + j₁ * d = (2 ^ K - d) + 2 ^ (K + 2) * H := by
        refine ⟨(a + j₁ * d) / 2 ^ (K + 2), ?_⟩
        have hdm := Nat.div_add_mod (a + j₁ * d) (2 ^ (K + 2))
        rw [r₁] at hdm
        omega
      obtain ⟨H₂, hH₂⟩ : ∃ H, a + j₂ * d = (2 ^ (K + 1) - d) + 2 ^ (K + 2) * H := by
        refine ⟨(a + j₂ * d) / 2 ^ (K + 2), ?_⟩
        have hdm := Nat.div_add_mod (a + j₂ * d) (2 ^ (K + 2))
        rw [r₂] at hdm
        omega
      have y1 : (j₁ + 1) * d = j₁ * d + d := by ring
      have y2 : (j₂ + 1) * d = j₂ * d + d := by ring
      have a1 : s (a + j₁ * d) = s (2 ^ K - d) + s H₁ := by
        rw [hH₁]
        exact split (K + 2) (2 ^ K - d) H₁ (by omega)
      have b1 : s (a + (j₁ + 1) * d) = 1 + s H₁ := by
        have e : a + (j₁ + 1) * d = 2 ^ K + 2 ^ (K + 2) * H₁ := by omega
        rw [e, split (K + 2) (2 ^ K) H₁ (by omega), s_pow]
      have a2 : s (a + j₂ * d) = s (2 ^ K - d) + 1 + s H₂ := by
        have e : 2 ^ (K + 1) - d = (2 ^ K - d) + 2 ^ K * 1 := by omega
        rw [hH₂, split (K + 2) (2 ^ (K + 1) - d) H₂ (by omega), e,
          split K (2 ^ K - d) 1 (by omega), s_one]
      have b2 : s (a + (j₂ + 1) * d) = 1 + s H₂ := by
        have e : a + (j₂ + 1) * d = 2 ^ (K + 1) + 2 ^ (K + 2) * H₂ := by omega
        rw [e, split (K + 2) (2 ^ (K + 1)) H₂ (by omega), s_pow]
      omega

end MO485092

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_485092.main) := by
  intro h
  obtain ⟨d, hd, hcases⟩ := h {n | MO485092.s n % 2 = 1}
  obtain ⟨L₀, hL⟩ := MO485092.bound d hd
  rcases hcases with h1 | h0
  · obtain ⟨a, ha⟩ := h1 L₀
    obtain ⟨k, hk, hne⟩ := hL a
    have m1 : MO485092.s (a + k * d) % 2 = 1 := ha k (by omega)
    have m2 : MO485092.s (a + (k + 1) * d) % 2 = 1 := ha (k + 1) hk
    omega
  · obtain ⟨a, ha⟩ := h0 L₀
    obtain ⟨k, hk, hne⟩ := hL a
    have m1 : ¬ (MO485092.s (a + k * d) % 2 = 1) := ha k (by omega)
    have m2 : ¬ (MO485092.s (a + (k + 1) * d) % 2 = 1) := ha (k + 1) hk
    omega
