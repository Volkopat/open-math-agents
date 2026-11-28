import OMAStatements.S_oeis_a367191
import Mathlib

-- Problem: A367191: a(n) is the largest positive number k such that k^2 + k*n + n^2 is a perfect
-- square, or 0 if no such k exists.
-- Upstream: formal-conjectures statements/oeis-a367191.lean:0 (declaration OMA.S_oeis_a367191.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof.  Let n >= 1, k >= 1 and k^2 + k n + n^2 = m^2.  Then (2m)^2 - (2k + n)^2 = 3 n^2, that is
--   d * e = 3 n^2   with   d = 2m - 2k - n > 0,   e = 2m + 2k + n,   e - d = 4k + 2n.
-- So k is largest when d is smallest.
-- * n odd, n = 2t + 1.  From d >= 1:  (2m)^2 >= (2k + n + 1)^2, which gives k <= t (3t + 2), and
--   k = t (3t + 2) works with m = 3t^2 + 3t + 1.
-- * n = 4t + 2.  Then d is even, so m >= k + 2t + 2, which gives k <= 2t (3t + 2), and
--   k = 2t (3t + 2) works with m = 6t^2 + 6t + 2.
-- * n = 4s + 4.  Then m and k have the same parity (m^2 = k^2 mod 2), so d/2 = m - k - 2s - 2 is
--   even and positive, hence m >= k + 2s + 4, which gives k <= s (3s + 4), and k = s (3s + 4)
--   works with m = 3s^2 + 6s + 4.
-- In each case the bound is the conjectured formula; when the bound is 0 there is no admissible k.

namespace OMA.A367191

theorem d_pos (K N M : ℤ) (hN : 0 < N) (hK : 0 < K) (hM : 0 ≤ M)
    (h : K ^ 2 + K * N + N ^ 2 = M ^ 2) : 0 < 2 * M - 2 * K - N := by
  by_contra hcon
  have h1 : 0 ≤ 2 * K + N - 2 * M := by linarith
  have h2 : 0 ≤ 2 * K + N + 2 * M := by linarith
  nlinarith [mul_nonneg h1 h2, mul_pos hN hN]

theorem bound_odd (K M t : ℤ) (hK : 0 < K) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (h : K ^ 2 + K * (2 * t + 1) + (2 * t + 1) ^ 2 = M ^ 2) : K ≤ t * (3 * t + 2) := by
  have hd := d_pos K (2 * t + 1) M (by linarith) hK hM h
  have h1 : 0 ≤ (2 * M - 2 * K - (2 * t + 1)) - 1 := by linarith
  have h2 : 0 ≤ (2 * M + 2 * K + (2 * t + 1)) + 1 := by linarith
  nlinarith [mul_nonneg h1 h2]

theorem bound_two (K M t : ℤ) (hK : 0 < K) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (h : K ^ 2 + K * (4 * t + 2) + (4 * t + 2) ^ 2 = M ^ 2) : K ≤ 2 * t * (3 * t + 2) := by
  have hd := d_pos K (4 * t + 2) M (by linarith) hK hM h
  have h1 : 0 ≤ (M - K - (2 * t + 1)) - 1 := by omega
  have h2 : 0 ≤ (M + K + (2 * t + 1)) + 1 := by linarith
  nlinarith [mul_nonneg h1 h2]

theorem bound_four (K M s : ℤ) (hK : 0 < K) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (h : K ^ 2 + K * (4 * s + 4) + (4 * s + 4) ^ 2 = M ^ 2) : K ≤ s * (3 * s + 4) := by
  have hd := d_pos K (4 * s + 4) M (by linarith) hK hM h
  have hpar : (M - K) % 2 = 0 := by
    by_contra hne
    obtain ⟨u, hu⟩ : ∃ u : ℤ, M = K + 2 * u + 1 := ⟨(M - K) / 2, by omega⟩
    rw [hu] at h
    have h3 : 2 * (2 * u ^ 2 + 2 * u * K + K + 2 * u) + 1
        = 2 * (2 * s * K + 2 * K + 8 * s ^ 2 + 16 * s + 8) := by
      linear_combination (-1 : ℤ) * h
    omega
  have h1 : 0 ≤ (M - K - (2 * s + 2)) - 2 := by omega
  have h2 : 0 ≤ (M + K + (2 * s + 2)) + 2 := by linarith
  nlinarith [mul_nonneg h1 h2]

/-- Transfer of a natural-number solution to the integers. -/
theorem cast_eq (k n m : ℕ) (h : k ^ 2 + k * n + n ^ 2 = m * m) :
    (k : ℤ) ^ 2 + (k : ℤ) * (n : ℤ) + (n : ℤ) ^ 2 = (m : ℤ) ^ 2 := by
  rw [sq (m : ℤ)]
  exact_mod_cast h

theorem ub_odd (t k m : ℕ) (hk : 0 < k)
    (h : k ^ 2 + k * (2 * t + 1) + (2 * t + 1) ^ 2 = m * m) : k ≤ t * (3 * t + 2) := by
  have hz := cast_eq k (2 * t + 1) m h
  push_cast at hz
  have := bound_odd (k : ℤ) (m : ℤ) (t : ℤ) (by exact_mod_cast hk) (by positivity) (by positivity) hz
  exact_mod_cast this

theorem ub_two (t k m : ℕ) (hk : 0 < k)
    (h : k ^ 2 + k * (4 * t + 2) + (4 * t + 2) ^ 2 = m * m) : k ≤ 2 * t * (3 * t + 2) := by
  have hz := cast_eq k (4 * t + 2) m h
  push_cast at hz
  have := bound_two (k : ℤ) (m : ℤ) (t : ℤ) (by exact_mod_cast hk) (by positivity) (by positivity) hz
  exact_mod_cast this

theorem ub_four (s k m : ℕ) (hk : 0 < k)
    (h : k ^ 2 + k * (4 * s + 4) + (4 * s + 4) ^ 2 = m * m) : k ≤ s * (3 * s + 4) := by
  have hz := cast_eq k (4 * s + 4) m h
  push_cast at hz
  have := bound_four (k : ℤ) (m : ℤ) (s : ℤ) (by exact_mod_cast hk) (by positivity) (by positivity) hz
  exact_mod_cast this

/-- If every admissible `k` is at most `a`, and `a` is admissible whenever it is positive, then `a`
is the term of the sequence. -/
theorem isValue_of (n a : ℕ)
    (hub : ∀ k m : ℕ, 0 < k → k ^ 2 + k * n + n ^ 2 = m * m → k ≤ a)
    (hex : ∃ m : ℕ, a ^ 2 + a * n + n ^ 2 = m * m) :
    OMA.S_oeis_a367191.IsValue n a := by
  unfold OMA.S_oeis_a367191.IsValue OMA.S_oeis_a367191.Admissible
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · right
    refine ⟨h0, ?_⟩
    rintro k ⟨hk, m, hm⟩
    have := hub k m hk hm
    omega
  · left
    refine ⟨⟨hpos, hex⟩, ?_⟩
    rintro k ⟨hk, m, hm⟩
    exact hub k m hk hm

end OMA.A367191

theorem OMA.solution : type_of% @OMA.S_oeis_a367191.main := by
  intro n hn
  have hcases : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 2 = 1 := by omega
  rcases hcases with h0 | h2 | h1
  · -- n = 4 s + 4
    obtain ⟨s, rfl⟩ : ∃ s, n = 4 * s + 4 := ⟨n / 4 - 1, by omega⟩
    refine ⟨s * (3 * s + 4), ?_, ?_, ?_, ?_⟩
    · exact OMA.A367191.isValue_of _ _ (fun k m hk h => OMA.A367191.ub_four s k m hk h)
        ⟨3 * s ^ 2 + 6 * s + 4, by ring⟩
    · intro _
      push_cast
      ring
    · intro h
      omega
    · intro h
      omega
  · -- n = 4 t + 2
    obtain ⟨t, rfl⟩ : ∃ t, n = 4 * t + 2 := ⟨n / 4, by omega⟩
    refine ⟨2 * t * (3 * t + 2), ?_, ?_, ?_, ?_⟩
    · exact OMA.A367191.isValue_of _ _ (fun k m hk h => OMA.A367191.ub_two t k m hk h)
        ⟨6 * t ^ 2 + 6 * t + 2, by ring⟩
    · intro h
      omega
    · intro h
      omega
    · intro _
      push_cast
      ring
  · -- n = 2 t + 1
    obtain ⟨t, rfl⟩ : ∃ t, n = 2 * t + 1 := ⟨n / 2, by omega⟩
    refine ⟨t * (3 * t + 2), ?_, ?_, ?_, ?_⟩
    · exact OMA.A367191.isValue_of _ _ (fun k m hk h => OMA.A367191.ub_odd t k m hk h)
        ⟨3 * t ^ 2 + 3 * t + 1, by ring⟩
    · intro h
      omega
    · intro _
      push_cast
      ring
    · intro h
      omega
