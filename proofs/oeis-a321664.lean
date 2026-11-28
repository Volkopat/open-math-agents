import OMAStatements.S_oeis_a321664
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a321664

open OMA.S_oeis_a321664

/-- Counterexample sequence A321664: three interleaved copies of Fibonacci,
`a(3k) = F(k + 2)`, `a(3k + 1) = F(k + 2)`, `a(3k + 2) = F(k + 1)`. -/
private def seq (n : ℕ) : ℕ :=
  if n % 3 = 2 then Nat.fib (n / 3 + 1) else Nat.fib (n / 3 + 2)

private lemma seq_pos (n : ℕ) : 0 < seq n := by
  unfold seq
  split_ifs
  · exact Nat.fib_pos.mpr (by omega)
  · exact Nat.fib_pos.mpr (by omega)

private lemma seq_unbounded (M : ℕ) : ∃ n, M < seq n := by
  refine ⟨3 * (M + 1), ?_⟩
  have hmod : (3 * (M + 1)) % 3 ≠ 2 := by omega
  have hdiv : (3 * (M + 1)) / 3 = M + 1 := by omega
  simp only [seq, hmod, ↓reduceIte, hdiv]
  have hle : M + 2 ≤ Nat.fib (M + 3) := by
    induction M with
    | zero => decide
    | succ r ih =>
      rw [show r + 1 + 3 = (r + 2) + 2 by omega, Nat.fib_add_two, show r + 2 + 1 = r + 3 by omega]
      have hpos : 1 ≤ Nat.fib (r + 2) := Nat.fib_pos.mpr (by omega)
      omega
  rw [show M + 1 + 2 = M + 3 by omega]
  omega

private lemma seq_four_window (n : ℕ) :
    FourWindowMaxEqSumTwoMin (seq n) (seq (n + 1)) (seq (n + 2)) (seq (n + 3)) := by
  set k := n / 3
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hfib_rec : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
    rw [show k + 3 = (k + 1) + 2 by omega, Nat.fib_add_two]
  have hle1 : Nat.fib (k + 1) ≤ Nat.fib (k + 2) := Nat.fib_mono (by omega)
  have hle2 : Nat.fib (k + 2) ≤ Nat.fib (k + 3) := Nat.fib_mono (by omega)
  rcases hr with h0 | h1 | h2
  · have ha0 : seq n = Nat.fib (k + 2) := by simp [seq, h0, k]
    have ha1 : seq (n + 1) = Nat.fib (k + 2) := by
      simp [seq, show (n + 1) % 3 = 1 by omega, show (n + 1) / 3 = k by omega]
    have ha2 : seq (n + 2) = Nat.fib (k + 1) := by
      simp [seq, show (n + 2) % 3 = 2 by omega, show (n + 2) / 3 = k by omega]
    have ha3 : seq (n + 3) = Nat.fib (k + 3) := by
      simp [seq, show (n + 3) % 3 = 0 by omega, show (n + 3) / 3 = k + 1 by omega]
    rw [ha0, ha1, ha2, ha3]
    refine ⟨Nat.fib (k + 1), Nat.fib (k + 2), Nat.fib (k + 2), Nat.fib (k + 3),
      hle1, le_refl _, hle2, hfib_rec, ?_⟩
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    abel
  · have ha0 : seq n = Nat.fib (k + 2) := by simp [seq, h1, k]
    have ha1 : seq (n + 1) = Nat.fib (k + 1) := by
      simp [seq, show (n + 1) % 3 = 2 by omega, show (n + 1) / 3 = k by omega]
    have ha2 : seq (n + 2) = Nat.fib (k + 3) := by
      simp [seq, show (n + 2) % 3 = 0 by omega, show (n + 2) / 3 = k + 1 by omega]
    have ha3 : seq (n + 3) = Nat.fib (k + 3) := by
      simp [seq, show (n + 3) % 3 = 1 by omega, show (n + 3) / 3 = k + 1 by omega]
    rw [ha0, ha1, ha2, ha3]
    refine ⟨Nat.fib (k + 1), Nat.fib (k + 2), Nat.fib (k + 3), Nat.fib (k + 3),
      hle1, hle2, le_refl _, hfib_rec, ?_⟩
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    abel
  · have ha0 : seq n = Nat.fib (k + 1) := by simp [seq, h2, k]
    have ha1 : seq (n + 1) = Nat.fib (k + 3) := by
      simp [seq, show (n + 1) % 3 = 0 by omega, show (n + 1) / 3 = k + 1 by omega]
    have ha2 : seq (n + 2) = Nat.fib (k + 3) := by
      simp [seq, show (n + 2) % 3 = 1 by omega, show (n + 2) / 3 = k + 1 by omega]
    have ha3 : seq (n + 3) = Nat.fib (k + 2) := by
      simp [seq, show (n + 3) % 3 = 2 by omega, show (n + 3) / 3 = k + 1 by omega]
    rw [ha0, ha1, ha2, ha3]
    refine ⟨Nat.fib (k + 1), Nat.fib (k + 2), Nat.fib (k + 3), Nat.fib (k + 3),
      hle1, hle2, le_refl _, hfib_rec, ?_⟩
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    abel

private lemma seq_not_eventually_padovan :
    ¬ ∃ N, ∀ n ≥ N, seq (n + 3) = seq (n + 1) + seq n := by
  rintro ⟨N, hN⟩
  set k := N + 1
  have h := hN (3 * k) (by omega)
  have h0 : seq (3 * k) = Nat.fib (k + 2) := by
    simp [seq, show (3 * k) % 3 = 0 by omega, show (3 * k) / 3 = k by omega]
  have h1 : seq (3 * k + 1) = Nat.fib (k + 2) := by
    simp [seq, show (3 * k + 1) % 3 = 1 by omega, show (3 * k + 1) / 3 = k by omega]
  have h3 : seq (3 * k + 3) = Nat.fib (k + 3) := by
    simp [seq, show (3 * k + 3) % 3 = 0 by omega, show (3 * k + 3) / 3 = k + 1 by omega]
  rw [h0, h1, h3] at h
  have hfib_rec : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
    rw [show k + 3 = (k + 1) + 2 by omega, Nat.fib_add_two]
  have hlt : Nat.fib (k + 1) < Nat.fib (k + 2) := by
    have hk2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    have hpos : 0 < Nat.fib k := Nat.fib_pos.mpr (by omega)
    omega
  omega

end OMA.P_oeis_a321664

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a321664.main) := by
  intro h
  exact OMA.P_oeis_a321664.seq_not_eventually_padovan
    (h OMA.P_oeis_a321664.seq OMA.P_oeis_a321664.seq_pos
       OMA.P_oeis_a321664.seq_unbounded OMA.P_oeis_a321664.seq_four_window)
