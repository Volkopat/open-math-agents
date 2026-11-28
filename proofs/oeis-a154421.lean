import OMAStatements.S_oeis_a154421

lemma h11_fib_succ_le_lucas (n : ℕ) :
    Nat.fib (n + 1) ≤ OMA.S_oeis_a154421.lucas n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [OMA.S_oeis_a154421.lucas]
  | one => norm_num [OMA.S_oeis_a154421.lucas]
  | more n ih0 ih1 =>
    have hf : Nat.fib (n + 2 + 1) = Nat.fib (n + 1) + Nat.fib (n + 1 + 1) := by
      simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n + 1))
    rw [hf, OMA.S_oeis_a154421.lucas]
    omega

lemma h11_lucas_index_bound (t : ℕ)
    (h : OMA.S_oeis_a154421.lucas (3 * t) ≤ 36930553345551) : t < 22 := by
  by_contra ht
  have hidx : 67 ≤ 3 * t + 1 := by omega
  have hmono := Nat.fib_mono hidx
  have hl := h11_fib_succ_le_lucas (3 * t)
  have heval : Nat.fib 67 = 44945570212853 := by norm_num
  omega

lemma h11_lucas_succ_eq_fib (n : ℕ) :
    OMA.S_oeis_a154421.lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [OMA.S_oeis_a154421.lucas]
  | one => norm_num [OMA.S_oeis_a154421.lucas]
  | more n ih0 ih1 =>
    rw [show n + 2 + 1 = (n + 1) + 2 by omega, OMA.S_oeis_a154421.lucas, ih1, ih0]
    simp only [Nat.fib_add_two]
    omega

lemma h11_lucas_eq_fib (n : ℕ) :
    OMA.S_oeis_a154421.lucas n =
      if n = 0 then 2 else Nat.fib (n - 1) + Nat.fib (n + 1) := by
  cases n with
  | zero => rfl
  | succ n => simpa using h11_lucas_succ_eq_fib n



theorem OMA.fib_index_bound_154421 (s : ℕ)
    (h : Nat.fib s ≤ 36930553345551) : s < 67 := by
  by_contra hs
  have hs : 67 ≤ s := by omega
  have hf := Nat.fib_mono hs
  norm_num at hf
  omega


def h11_divisors : List (List ℕ) := [
  [29, 3, 4649, 3, 3, 5, 7, 23, 37, 3, 7, 3, 3, 5, 29, 7, 131, 3, 47, 3, 3, 5],
  [37, 3, 5, 3, 3, 11, 5, 7, 19, 3, 5, 3, 3, 29, 5, 11, 19, 3, 5, 3, 3, 1713223],
  [3, 67, 11, 7, 5, 3, 47, 3, 3, 11, 337, 17, 5, 3, 23, 3, 3, 7817, 11, 7, 5, 3],
  [5, 769, 3, 269, 5, 19, 3, 24697, 5, 11, 3, 7, 5, 7, 3, 107, 5, 19, 3, 11, 5, 53],
  [3, 7, 7, 5, 11, 3, 11, 3, 3, 6163, 29, 5, 54709, 3, 7, 3, 3, 7, 7, 5, 101, 3],
  [3, 7, 7, 13, 5, 3, 157, 3, 3, 227, 41, 13, 5, 3, 7, 3, 3, 7, 7, 17, 5, 3],
  [41, 3, 11, 3, 3, 181, 17, 47, 11, 3, 89, 3, 3, 502597, 887, 173, 13, 3, 11, 3, 3, 197],
  [521, 17, 3, 13, 19, 17, 3, 36781, 7, 103, 3, 13, 79, 17, 3, 107, 19, 17, 3, 41, 19, 107],
  [31, 3, 5, 3, 3, 746981, 5, 17, 13, 3, 5, 3, 3, 67, 5, 2963, 37, 3, 5, 3, 3, 2553829],
  [4092637, 3, 26959, 3, 3, 7, 113, 5, 13, 3, 29, 3, 3, 17, 157, 5, 109, 3, 29, 3, 3, 7],
  [3, 7, 5, 190997, 5002859, 3, 5, 3, 3, 29, 5, 53, 5573, 3, 5, 3, 3, 7, 5, 103, 31, 3],
  [7, 5, 3, 61, 1721, 5, 3, 17, 67, 5, 3, 17, 227, 5, 3, 11, 7, 5, 3, 17, 888661, 5],
  [3, 263, 11, 7, 13, 3, 127, 3, 3, 11, 41, 37, 11, 3, 23, 3, 3, 3631, 11, 7, 209257, 3],
  [3, 29, 11, 7, 19, 3, 131, 3, 3, 11, 19, 179, 11, 3, 19, 3, 3, 571, 11, 7, 19, 3],
  [29, 3, 1231, 3, 3, 1675873, 7, 5, 821, 3, 7, 3, 3, 31, 11, 5, 11, 3, 1429, 3, 3, 41],
  [73, 521, 3, 691, 271, 19, 3, 572183, 7, 359, 3, 19, 107, 29, 3, 173, 2003, 19, 3, 48121, 839, 13],
  [5, 3, 11, 3, 3, 7013, 7, 23, 5, 3, 7, 3, 3, 521, 179, 7, 5, 3, 11, 3, 3, 13],
  [59, 3, 7, 3, 3, 5, 31, 7, 23, 3, 73, 3, 3, 5, 7, 13, 31, 3, 7, 3, 3, 5],
  [3, 5, 23, 7, 29, 3, 17, 3, 3, 5, 29, 8461, 293, 3, 23, 3, 3, 5, 17, 7, 13, 3],
  [373, 17, 3, 5, 19, 17, 3, 5, 19, 15497, 3, 5, 23, 7, 3, 5, 19, 17, 3, 5, 19, 31],
  [3, 5, 7, 1061, 359, 3, 321007, 3, 3, 5, 31, 17, 13, 3, 7, 3, 3, 5, 7, 17, 31, 3],
  [3, 7, 5, 107, 83, 3, 5, 3, 3, 31, 5, 19, 2749, 3, 5, 3, 3, 7, 5, 31, 29, 0]
]

def h11_divisor (s t : ℕ) : ℕ :=
  if s % 3 = 0 then ((h11_divisors.getD (s / 3 - 1) []).getD t 0) else 2

def h11_residual (s t : ℕ) : ℕ :=
  36930553345551 - Nat.fib s -
    (if 3 * t = 0 then 2 else Nat.fib (3 * t - 1) + Nat.fib (3 * t + 1))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem h11_certificate : ∀ (s : Fin 66) (t : Fin 22),
    h11_residual (s.val + 1) t.val < 2 ∨
      (2 ≤ h11_divisor (s.val + 1) t.val ∧
       h11_divisor (s.val + 1) t.val < h11_residual (s.val + 1) t.val ∧
       h11_divisor (s.val + 1) t.val ∣ h11_residual (s.val + 1) t.val) := by
  decide +kernel

theorem h11_residual_not_prime (s t : ℕ) (hs : 0 < s) (hsb : s < 67) (ht : t < 22) :
    ¬ Nat.Prime (36930553345551 - Nat.fib s - OMA.S_oeis_a154421.lucas (3 * t)) := by
  have h := h11_certificate ⟨s - 1, by omega⟩ ⟨t, ht⟩
  have hidx : s - 1 + 1 = s := by omega
  simp only [hidx] at h
  rw [h11_lucas_eq_fib]
  change ¬ Nat.Prime (h11_residual s t)
  rcases h with hsmall | ⟨hd, hlt, hdiv⟩
  · intro hp
    have := hp.two_le
    omega
  · exact Nat.not_prime_of_dvd_of_lt hdiv hd hlt

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a154421.main) := by
  intro h
  obtain ⟨p, s, t, hp, _, hs, heq⟩ := h 36930553345551 (by norm_num)
  have hsle : Nat.fib s ≤ 36930553345551 := by omega
  have htle : OMA.S_oeis_a154421.lucas (3 * t) ≤ 36930553345551 := by omega
  have hsb := OMA.fib_index_bound_154421 s hsle
  have htb := h11_lucas_index_bound t htle
  have hpval : p = 36930553345551 - Nat.fib s - OMA.S_oeis_a154421.lucas (3 * t) := by omega
  exact h11_residual_not_prime s t hs hsb htb (hpval ▸ hp)
