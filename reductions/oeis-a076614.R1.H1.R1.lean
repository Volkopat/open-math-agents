import OMAReductions.R_oeis_a076614_R1

namespace OMA.R_oeis_a076614_R1_H1_R1

open OMA.S_oeis_a076614 OMA.R_oeis_a076614_R1

/-- A square sum colliding with a higher even power sum has offset four. -/
def H1 : Prop :=
  ∀ n l m : ℕ, 1 ≤ m → 2 < l → m < n → Even l →
    n + 4 ≡ m [MOD 8] → S 2 n = S l m → S 2 n = 160

/-- For higher even exponents the lengths agree modulo eight. -/
def H2 : Prop :=
  ∀ k n l m : ℕ, 4 ≤ k → 1 ≤ m → k < l → m < n → Even k → Even l →
    n ≡ m [MOD 8] → S k n = S l m → S k n = 160

lemma mod_eight {k : ℕ} (he : Even k) (n : ℕ) :
    S k (n+1) ≡ 2^k + n [MOD 8] := by
  induction n with
  | zero => simp [S, Nat.nth_prime_zero_eq_two, Nat.ModEq]
  | succ n ih =>
    rw [S, Finset.sum_range_succ]
    obtain ⟨j,hj⟩ := he
    have ho := odd_nth_prime (i := n+1) (by omega)
    let p := Nat.nth Nat.Prime (n+1)
    change p % 2 = 1 at ho
    have hr : p%8 = 1 ∨ p%8 = 3 ∨ p%8 = 5 ∨ p%8 = 7 := by omega
    have hs : p^2 ≡ 1 [MOD 8] := by
      rcases hr with h | h | h | h <;> norm_num [Nat.ModEq, Nat.pow_mod, h]
    have hk : k = 2*j := by omega
    have ht : p^k ≡ 1 [MOD 8] := by
      rw [hk, pow_mul]
      simpa using hs.pow j
    exact ih.add ht

lemma zero_mod {k : ℕ} (hk : 3 ≤ k) : 2^k % 8 = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hk : 2^3 ∣ 2^k)

theorem main : H1 → H2 → OMA.R_oeis_a076614_R1.H1 := by
  intro hSquare hHigher k n l m hk hm hkl hmn hek hel _ eq
  obtain ⟨a,rfl⟩ : ∃ a, n = a+1 := ⟨n-1, by omega⟩
  obtain ⟨b,rfl⟩ : ∃ b, m = b+1 := ⟨m-1, by omega⟩
  have heq := (mod_eight hek a).symm
  rw [eq] at heq
  have h := heq.trans (mod_eight hel b)
  obtain ⟨j,hj⟩ := hek
  have hl : 3 ≤ l := by omega
  change (2^k+a)%8 = (2^l+b)%8 at h
  rw [Nat.add_mod (2^l), zero_mod hl] at h
  by_cases h2 : k = 2
  · rw [h2] at hkl eq h ⊢
    apply hSquare _ _ _ hm hkl hmn hel _ eq
    change (_ : ℕ)%8 = _%8
    norm_num at h
    omega
  · have hk4 : 4 ≤ k := by omega
    apply hHigher _ _ _ _ hk4 hm hkl hmn ⟨j,hj⟩ hel _ eq
    rw [Nat.add_mod (2^k), zero_mod (by omega : 3 ≤ k)] at h
    change (_ : ℕ)%8 = _%8
    omega

end OMA.R_oeis_a076614_R1_H1_R1
