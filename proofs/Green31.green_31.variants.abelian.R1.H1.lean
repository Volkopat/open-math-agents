import OMAReductions.R_Green31_green_31_variants_abelian_R1
import Mathlib

-- Step Green31.green_31.variants.abelian.R1.H1: hypothesis H1 of reduction Green31.green_31.variants.abelian.R1
-- Credit: @ivillar

/-!
The Erdős–Turán construction. For an odd prime `p` the numbers `2 * p * k + (k ^ 2 % p)`,
`k < p`, form a Sidon set: a coincidence of sums forces `a + b = c + d` and
`a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2` in `ZMod p`, hence `(a - c) * (a - d) = 0`. Given `L ≥ 17`, put
`m = √(L - 1) / 2` and take a prime `m < p ≤ 2 * m - 1` (Bertrand); the first `m + 1` of these
numbers lie below `4 * m ^ 2 ≤ L - 1`, and `L ≤ 4 * (m + 1) ^ 2`. For `L ≤ 16` the sets `{0}` and
`{0, 1}` suffice.
-/

namespace F2G31

/-- The Erdős–Turán map. -/
def et (p k : ℕ) : ℕ := 2 * p * k + k ^ 2 % p

theorem et_sidon (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (a b c d : ℕ) (ha : a < p)
    (hc : c < p) (hd : d < p) (h : et p a + et p b = et p c + et p d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold et at h
  have hra : a ^ 2 % p < p := Nat.mod_lt _ hp.pos
  have hrb : b ^ 2 % p < p := Nat.mod_lt _ hp.pos
  have hrc : c ^ 2 % p < p := Nat.mod_lt _ hp.pos
  have hrd : d ^ 2 % p < p := Nat.mod_lt _ hp.pos
  have hsum : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with hlt | heq | hgt
    · have h1 : 2 * p * (a + b + 1) ≤ 2 * p * (c + d) := Nat.mul_le_mul_left _ hlt
      linarith [Nat.zero_le (c ^ 2 % p), Nat.zero_le (d ^ 2 % p)]
    · exact heq
    · have h1 : 2 * p * (c + d + 1) ≤ 2 * p * (a + b) := Nat.mul_le_mul_left _ hgt
      linarith [Nat.zero_le (a ^ 2 % p), Nat.zero_le (b ^ 2 % p)]
  have hrem : a ^ 2 % p + b ^ 2 % p = c ^ 2 % p + d ^ 2 % p := by
    have h1 : 2 * p * (a + b) = 2 * p * (c + d) := by rw [hsum]
    linarith
  have hs : (a : ZMod p) + b = c + d := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hsum
  have hq : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ZMod p) hrem
    simp only [Nat.cast_add, ZMod.natCast_mod, Nat.cast_pow] at h1
    exact h1
  have hfact : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    have h3 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h1
    have h4 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h3
    have h5 : 2 ≤ p := hp.two_le
    omega
  have hz : ((a : ZMod p) - c) * ((a : ZMod p) - d) = 0 := by
    have h1 : (2 : ZMod p) * (((a : ZMod p) - c) * ((a : ZMod p) - d)) = 0 := by
      linear_combination ((a : ZMod p) - b - c - d) * hs + hq
    exact (mul_eq_zero.mp h1).resolve_left h2
  rcases mul_eq_zero.mp hz with h0 | h0
  · have h1 : a = c :=
      ((ZMod.natCast_eq_natCast_iff a c p).mp (sub_eq_zero.mp h0)).eq_of_lt_of_lt ha hc
    left
    exact ⟨h1, by omega⟩
  · have h1 : a = d :=
      ((ZMod.natCast_eq_natCast_iff a d p).mp (sub_eq_zero.mp h0)).eq_of_lt_of_lt ha hd
    right
    exact ⟨h1, by omega⟩

theorem small_one : IsSidon ((({0} : Finset ℕ)) : Set ℕ) := by
  intro i₁ h1 j₁ h2 i₂ h3 j₂ h4 _
  rw [Finset.mem_coe, Finset.mem_singleton] at h1 h2 h3 h4
  omega

theorem small_two : IsSidon ((({0, 1} : Finset ℕ)) : Set ℕ) := by
  intro i₁ h1 j₁ h2 i₂ h3 j₂ h4 h
  rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3 h4
  omega

theorem sidon_exists : ∀ L : ℕ, 0 < L → ∃ A : Finset ℕ,
    A ⊆ Finset.range L ∧ IsSidon (A : Set ℕ) ∧ L ≤ 4 * A.card ^ 2 := by
  intro L hL
  by_cases hsmall : L ≤ 16
  · by_cases hone : L = 1
    · refine ⟨{0}, ?_, small_one, ?_⟩
      · intro x hx
        rw [Finset.mem_singleton] at hx
        rw [Finset.mem_range]
        omega
      · rw [Finset.card_singleton]
        omega
    · refine ⟨{0, 1}, ?_, small_two, ?_⟩
      · intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_range]
        omega
      · rw [Finset.card_pair (by norm_num)]
        omega
  · obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
    have hs1 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have hs2 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
    have hs4 : 4 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
    obtain ⟨m, hm⟩ : ∃ m, m = Nat.sqrt n / 2 := ⟨_, rfl⟩
    have hm1 : 2 * m ≤ Nat.sqrt n := by omega
    have hm2 : Nat.sqrt n + 1 ≤ 2 * m + 2 := by omega
    have hm3 : 2 ≤ m := by omega
    have h4m : 4 * m * m ≤ n := by
      have h1 : 2 * m * (2 * m) ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul hm1 hm1
      nlinarith
    have hbig : n + 1 ≤ (2 * m + 2) * (2 * m + 2) := by
      have h1 : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ (2 * m + 2) * (2 * m + 2) :=
        Nat.mul_le_mul hm2 hm2
      omega
    obtain ⟨p, hp, hmp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
    have hodd : p ≠ 2 := by omega
    have hne : p ≠ 2 * m := by
      intro h0
      have h1 : 2 ∣ p := by
        rw [h0]
        exact dvd_mul_right 2 m
      exact hodd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h1).symm
    have hp3 : p ≤ 2 * m - 1 := by omega
    have hcard : ((Finset.range (m + 1)).image (et p)).card = m + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro a ha b hb hab
      have ha' : a < p := by
        have := Finset.mem_range.mp (Finset.mem_coe.mp ha)
        omega
      have hb' : b < p := by
        have := Finset.mem_range.mp (Finset.mem_coe.mp hb)
        omega
      rcases et_sidon p hp hodd a a b b ha' hb' hb' (by rw [hab]) with ⟨h0, _⟩ | ⟨h0, _⟩
      · exact h0
      · exact h0
    refine ⟨(Finset.range (m + 1)).image (et p), ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [Finset.mem_range] at hk ⊢
      have hr : k ^ 2 % p < p := Nat.mod_lt _ hp.pos
      have h1 : 2 * p * k ≤ 2 * p * m := Nat.mul_le_mul_left _ (by omega)
      have h2 : p * (2 * m + 1) ≤ (2 * m - 1) * (2 * m + 1) := Nat.mul_le_mul_right _ hp3
      have h3 : (2 * m - 1) * (2 * m + 1) + 1 = 4 * m * m := by
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have h4 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
        rw [h4]
        ring
      unfold et
      nlinarith
    · intro i₁ h1 j₁ h2 i₂ h3 j₂ h4 h
      rw [Finset.mem_coe, Finset.mem_image] at h1 h2 h3 h4
      obtain ⟨a, ha, rfl⟩ := h1
      obtain ⟨c, hc, rfl⟩ := h2
      obtain ⟨b, hb, rfl⟩ := h3
      obtain ⟨d, hd, rfl⟩ := h4
      rw [Finset.mem_range] at ha hb hc hd
      rcases et_sidon p hp hodd a b c d (by omega) (by omega) (by omega) h with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rw [hcard]
      nlinarith

end F2G31

theorem OMA.solution : OMA.R_Green31_green_31_variants_abelian_R1.H1 :=
  F2G31.sidon_exists
