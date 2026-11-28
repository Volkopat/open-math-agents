import OMAStatements.S_oeis_a057032
import Mathlib

namespace Kurkov

open OMA.S_oeis_a057032

/-- The accumulator form of the PARI program recorded in A057032. -/
def run : ℕ → ℕ → ℕ
  | 0, p => p
  | d + 1, p => run d (if p % (d + 1) = 0 then p + (d + 1) else p)

private lemma run_le (d p : ℕ) : p ≤ run d p := by
  induction d generalizing p with
  | zero => simp [run]
  | succ d ih =>
    rw [run]
    exact le_trans (by split <;> omega) (ih _)

private lemma run_add_one_le (d p : ℕ) (hd : 0 < d) : p + 1 ≤ run d p := by
  cases d with
  | zero => omega
  | succ d =>
    rw [run]
    cases d with
    | zero =>
      have hm : p % (0 + 1) = 0 := by simpa using Nat.mod_one p
      simp [run, hm]
    | succ d =>
      exact le_trans (by split <;> omega) (run_add_one_le (d + 1) _ (by omega))

private lemma PS_eq_run : ∀ d p : ℕ, PS d (p + d) = run d p
  | 0, p => by simp [PS, run]
  | 1, p => by
      have hm : p % (0 + 1) = 0 := by simpa using Nat.mod_one p
      simp [PS, run, hm]
  | d + 2, p => by
      rw [PS, run]
      simp only [rot]
      have hnot : ¬p + (d + 2) ≤ d + 1 := by omega
      simp only [hnot, ↓reduceIte]
      have hsub : p + (d + 2) - (d + 1 + 1) = p := by omega
      rw [hsub]
      by_cases h : p % (d + 2) = 0
      · simp only [h, ↓reduceIte]
        convert PS_eq_run (d + 1) (p + (d + 2)) using 2 <;> omega
      · simp only [h, ↓reduceIte]
        convert PS_eq_run (d + 1) p using 2 <;> omega

private lemma a_eq_run (n : ℕ) : a n = run n 0 := by
  rw [a]
  have hdiag : PS (n + 1) n = PS n n := by
    cases n with
    | zero => simp [PS]
    | succ n => simp [PS, rot]
  rw [hdiag]
  simpa using PS_eq_run n 0

private lemma no_dvd_of_tight :
    ∀ d p k : ℕ, 2 ≤ k → k ≤ d → run d p = p + 1 → ¬k ∣ p
  | 0, p, k, _, hk, _ => by omega
  | 1, p, k, _, hk, _ => by omega
  | d + 2, p, k, hk2, hkd, htight => by
      rw [run] at htight
      by_cases htop : p % (d + 2) = 0
      · simp only [htop, ↓reduceIte] at htight
        have hbad : p + (d + 2) + 1 ≤ p + 1 := by
          calc
            p + (d + 2) + 1 ≤ run (d + 1) (p + (d + 2)) :=
              run_add_one_le (d + 1) (p + (d + 2)) (by omega)
            _ = p + 1 := htight
        omega
      · simp only [htop, ↓reduceIte] at htight
        intro hkp
        rcases Nat.eq_or_lt_of_le hkd with rfl | hlt
        · exact htop (Nat.dvd_iff_mod_eq_zero.mp hkp)
        · exact no_dvd_of_tight (d + 1) p k hk2 (by omega) htight hkp

private lemma tight_prime (n : ℕ) (hn : 1 ≤ n) (htight : run n 0 = n + 1) :
    n.Prime := by
  have hn2 : 2 ≤ n := by
    by_contra h
    interval_cases n <;> simp [run] at htight
  rw [Nat.prime_def_lt']
  refine ⟨hn2, ?_⟩
  intro k hk2 hklt
  have hfirst : run n 0 = run (n - 1) n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [run]
  have htail : run (n - 1) n = n + 1 := hfirst ▸ htight
  exact no_dvd_of_tight (n - 1) n k hk2 (by omega) htail

private lemma recover_prime :
    ∀ d p q : ℕ, 1 ≤ d → d < q → q.Prime → run d p = q + 1 → p = q
  | 0, p, q, hd, _, _, _ => by omega
  | 1, p, q, _, _, _, h => by simpa [run, Nat.mod_one] using h
  | d + 2, p, q, _, hdq, hq, hrun => by
      rw [run] at hrun
      by_cases htop : p % (d + 2) = 0
      · simp only [htop, ↓reduceIte] at hrun
        have hpq := recover_prime (d + 1) (p + (d + 2)) q (by omega) (by omega) hq hrun
        have hdvd : d + 2 ∣ q := by
          rw [← hpq]
          exact Nat.dvd_add_self_right.mpr (Nat.dvd_iff_mod_eq_zero.mpr htop)
        rcases hq.eq_one_or_self_of_dvd (d + 2) hdvd with h | h
        · omega
        · omega
      · simp only [htop, ↓reduceIte] at hrun
        exact recover_prime (d + 1) p q (by omega) (by omega) hq hrun

private lemma prime_iff_tight (n : ℕ) (hn : 1 ≤ n) :
    (run n 0 - 1).Prime ↔ run n 0 = n + 1 := by
  constructor
  · intro hq
    let q := run n 0 - 1
    have hrun : run n 0 = q + 1 := by
      dsimp [q]
      have := hq.two_le
      omega
    have hn2 : 2 ≤ n := by
      by_contra h
      interval_cases n <;> norm_num [run] at hq
    have hfirst : run n 0 = run (n - 1) n := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      simp [run]
    have hbound : n + 1 ≤ run n 0 := by
      rw [hfirst]
      exact run_add_one_le (n - 1) n (by omega)
    have hnq : n ≤ q := by omega
    rcases hnq.eq_or_lt with h | h
    · omega
    · have hz := recover_prime n 0 q hn h hq hrun
      omega
  · intro h
    rw [h]
    simpa using tight_prime n hn h

/-- The two cyclic constructions are conjugate by shifting positions and values by one. -/
private lemma shift_PS : ∀ m i : ℕ, PS' m (i + 1) = PS m i + 1
  | 0, i => by simp [PS, PS']
  | 1, i => by simp [PS, PS']
  | m + 2, i => by
      rw [PS', PS]
      simp only [rot]
      by_cases hfix : i ≤ m + 1
      · have hfix' : i + 1 ≤ m + 2 := by omega
        simp only [hfix, hfix', ↓reduceIte]
        exact shift_PS (m + 1) i
      · have hfix' : ¬i + 1 ≤ m + 2 := by omega
        simp only [hfix, hfix', ↓reduceIte]
        have hsub : i + 1 - (m + 2 + 1) = i - (m + 1 + 1) := by omega
        rw [hsub]
        by_cases hmod : (i - (m + 1 + 1)) % (m + 2) = 0
        · simp only [hmod, ↓reduceIte]
          convert shift_PS (m + 1) (i + (m + 2) - 1) using 2 <;> omega
        · simp only [hmod, ↓reduceIte]
          have hi : 0 < i := by omega
          convert shift_PS (m + 1) (i - 1) using 2 <;> omega

end Kurkov

theorem OMA.solution : type_of% @OMA.S_oeis_a057032.main := by
  intro n hn
  constructor
  · simpa [Kurkov.a_eq_run] using Kurkov.prime_iff_tight n hn
  · rw [OMA.S_oeis_a057032.a, OMA.S_oeis_a057032.b]
    have h := Kurkov.shift_PS (n + 1) n
    omega
