import OMAStatements.S_oeis_a063043

open OMA.S_oeis_a063043

namespace P

def mf (n d : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if n < d * d then n else if n % d = 0 then d else mf n (d + 1) k

def st (n : ℕ) : ℕ :=
  if n < 2 then 0 else
  let p := mf n 2 30
  if p = 0 then 0 else if p = n then n * primeAtMost (n - 1) + 1 else n / p

def orb (a : ℕ) : ℕ → ℕ
  | 0 => a
  | k + 1 => st (orb a k)

theorem mf_eq {n : ℕ} (hn : 2 ≤ n) :
    ∀ {d k}, 2 ≤ d → d ≤ n.minFac → mf n d k ≠ 0 → mf n d k = n.minFac
  | _, 0, _, _, h0 => absurd rfl h0
  | d, k + 1, hd2, hd, h0 => by
    rw [mf] at h0 ⊢
    split_ifs at h0 ⊢ with h1 h2
    · by_contra hne
      have hsq := Nat.minFac_sq_le_self (by omega) fun hp => hne hp.minFac_eq.symm
      have := Nat.mul_le_mul hd hd; rw [Nat.pow_two] at hsq; omega
    · have := Nat.minFac_le_of_dvd hd2 (Nat.dvd_of_mod_eq_zero h2); omega
    · refine mf_eq hn (by omega) ?_ h0
      have : n.minFac ≠ d := fun he => h2 (Nat.mod_eq_zero_of_dvd (he ▸ Nat.minFac_dvd n))
      omega

theorem st_eq {n : ℕ} (h : st n ≠ 0) : st n = step n := by
  simp only [st] at h ⊢
  split_ifs at h ⊢ with h2 h0 hp <;> try contradiction
  all_goals
    have hm := mf_eq (by omega) (by omega) (Nat.minFac_prime (by omega)).two_le h0
    simp [step, Nat.prime_def_minFac, ← hm, hp, show 2 ≤ n by omega]

theorem orb_eq {a : ℕ} : ∀ {k}, orb a k ≠ 0 → orbit a k = orb a k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [orb, orbit] at h ⊢
    rw [orb_eq fun h0 => h (by simp [h0, st]), st_eq h]

theorem orb_val {a k b : ℕ} (h : orb a k = b ∧ 0 < b) : orbit a k = b :=
  (orb_eq (by omega)).trans h.1

end P

theorem OMA.solution : type_of% @OMA.S_oeis_a063043.main := by
  have h17 (i : Fin 28) : orbit 17 i = P.orb 17 i := P.orb_eq (by revert i; decide +kernel)
  exact ⟨⟨P.orb_val (by decide +kernel), P.orb_val (by decide +kernel)⟩,
    fun i j => by rw [h17, h17]; revert i j; decide +kernel,
    by decide +kernel,
    fun h => absurd (h 29 (by decide) ⟨15, by decide, P.orb_val (by decide +kernel)⟩) (by decide)⟩
