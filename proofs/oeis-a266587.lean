import OMAStatements.S_oeis_a266587
import Mathlib

-- Problem: OEIS A266587, conjecture of Forberg: if a is the least index with p | L(a) for an
-- odd prime p (L = Lucas numbers), then p^m divides
-- L(a + a (p-1) Sum_{j=1..m-1} p^(j-1) + 2 i a p^(m-1)) for all m > 1 and i >= 0.
-- Statement: statements/oeis-a266587.lean (declaration OMA.S_oeis_a266587.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. The index is a p^(m-1) (2i+1), because (p-1) Sum_{j=1..m-1} p^(j-1) = p^(m-1) - 1.
-- Let Q = [[1,1],[1,0]], so the trace of Q^k is L(k). For X = Q^N let s = L(N) be the trace and
-- d = (-1)^N the determinant. The traces W(j) = L(N j) of X^j satisfy
-- W(j+2) = s W(j+1) - d W(j), W(0) = 2, W(1) = s. By induction, modulo s^2:
-- W(2t) == 2 (-d)^t and W(2t+1) == (2t+1) (-d)^t s.
-- So L(N) divides L(N j) for odd j, and if p^m | L(N) with m >= 1 and p odd, then
-- L(N p) == +-p L(N) (mod L(N)^2) is divisible by p^(m+1). Induction on m gives
-- p^m | L(a p^(m-1) (2t+1)). The minimality of a is not necessary.

namespace OMA.A266587

open Finset Matrix OMA.S_oeis_a266587

lemma lucas_succ_succ (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := by
  rw [lucas]

lemma lucas_eq_aux : ∀ n : ℕ, lucas (n + 1) = Nat.fib (n + 2) + Nat.fib n ∧
    lucas (n + 2) = Nat.fib (n + 3) + Nat.fib (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h0 : lucas (n + 1 + 2) = lucas (n + 2) + lucas (n + 1) := lucas_succ_succ (n + 1)
    have h1 : Nat.fib (n + 2 + 2) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have h3 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have e1 : n + 1 + 3 = n + 2 + 2 := by ring
    have e2 : n + 1 + 1 = n + 2 := by ring
    rw [h0, ih.1, ih.2, e1, e2, h1]
    omega

/-- The Fibonacci matrix. -/
def Q (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![1, 1; 1, 0]

lemma Q_pow (R : Type*) [CommRing R] (k : ℕ) :
    Q R ^ (k + 1) = !![(Nat.fib (k + 2) : R), (Nat.fib (k + 1) : R);
      (Nat.fib (k + 1) : R), (Nat.fib k : R)] := by
  induction k with
  | zero => simp [Q]
  | succ k ih =>
    rw [pow_succ, ih, Q]
    have h3 : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h3] <;> rw [h2] <;> push_cast <;> ring

/-- The trace of Q^k is the Lucas number L(k). -/
lemma trQ (k : ℕ) : (Q ℤ ^ k) 0 0 + (Q ℤ ^ k) 1 1 = (lucas k : ℤ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [lucas]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Q_pow, (lucas_eq_aux j).1]
    simp

/-- The traces W(j) of the powers X^j satisfy W(j+2) = s W(j+1) - d W(j). -/
lemma trace_rec (X : Matrix (Fin 2) (Fin 2) ℤ) (s d : ℤ) (hs : X 0 0 + X 1 1 = s)
    (hd : X 0 0 * X 1 1 - X 0 1 * X 1 0 = d) (j : ℕ) :
    (X ^ (j + 2)) 0 0 + (X ^ (j + 2)) 1 1
      = s * ((X ^ (j + 1)) 0 0 + (X ^ (j + 1)) 1 1) - d * ((X ^ j) 0 0 + (X ^ j) 1 1) := by
  have e2 : X ^ (j + 2) = X ^ j * X * X := by rw [pow_succ, pow_succ]
  have e1 : X ^ (j + 1) = X ^ j * X := pow_succ _ _
  rw [e2, e1]
  generalize X ^ j = Y
  subst hs hd
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Modulo s^2: W(2t) = 2 (-d)^t and W(2t+1) = (2t+1) (-d)^t s. -/
lemma modsq (X : Matrix (Fin 2) (Fin 2) ℤ) (s d : ℤ) (hs : X 0 0 + X 1 1 = s)
    (hd : X 0 0 * X 1 1 - X 0 1 * X 1 0 = d) : ∀ t : ℕ,
    (∃ u : ℤ, (X ^ (2 * t)) 0 0 + (X ^ (2 * t)) 1 1 = 2 * (-d) ^ t + s ^ 2 * u) ∧
    (∃ v : ℤ, (X ^ (2 * t + 1)) 0 0 + (X ^ (2 * t + 1)) 1 1
      = (2 * t + 1) * (-d) ^ t * s + s ^ 2 * v) := by
  intro t
  induction t with
  | zero =>
    refine ⟨⟨0, by simp⟩, ⟨0, ?_⟩⟩
    simp [hs]
  | succ t ih =>
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := ih
    have r1 := trace_rec X s d hs hd (2 * t)
    have r2 := trace_rec X s d hs hd (2 * t + 1)
    have e1 : 2 * (t + 1) = 2 * t + 2 := by ring
    have e2 : 2 * (t + 1) + 1 = 2 * t + 1 + 2 := by ring
    have e3 : 2 * t + 1 + 1 = 2 * t + 2 := by ring
    rw [e3] at r2
    have hA : (X ^ (2 * t + 2)) 0 0 + (X ^ (2 * t + 2)) 1 1
        = 2 * (-d) ^ (t + 1) + s ^ 2 * ((2 * t + 1) * (-d) ^ t + s * v - d * u) := by
      rw [r1, hu, hv, pow_succ]; ring
    refine ⟨⟨(2 * t + 1) * (-d) ^ t + s * v - d * u, by rw [e1]; exact hA⟩,
      ⟨s * ((2 * t + 1) * (-d) ^ t + s * v - d * u) - d * v, ?_⟩⟩
    rw [e2, r2, hA, hv, pow_succ]
    push_cast
    ring

/-- The matrix X = Q^N has trace L(N), determinant ±1 and X^j = Q^(N j). -/
lemma lucas_modsq (N t : ℕ) :
    ∃ v e : ℤ, (e = 1 ∨ e = -1) ∧
      (lucas (N * (2 * t + 1)) : ℤ) = (2 * t + 1) * e * lucas N + (lucas N : ℤ) ^ 2 * v := by
  have hdet : (Q ℤ ^ N) 0 0 * (Q ℤ ^ N) 1 1 - (Q ℤ ^ N) 0 1 * (Q ℤ ^ N) 1 0 = (-1) ^ N := by
    rw [← Matrix.det_fin_two, Matrix.det_pow]
    have : (Q ℤ).det = -1 := by simp [Q, Matrix.det_fin_two_of]
    rw [this]
  obtain ⟨v, hv⟩ := (modsq (Q ℤ ^ N) (lucas N) ((-1) ^ N) (trQ N) hdet t).2
  rw [← pow_mul, trQ] at hv
  refine ⟨v, (-(-1) ^ N) ^ t, ?_, hv⟩
  rcases neg_one_pow_eq_or ℤ N with h | h <;> rw [h]
  · rcases neg_one_pow_eq_or ℤ t with h' | h' <;> simp [h']
  · simp

lemma dvd_odd (N t : ℕ) : lucas N ∣ lucas (N * (2 * t + 1)) := by
  obtain ⟨v, e, _, h⟩ := lucas_modsq N t
  have hz : (lucas N : ℤ) ∣ (lucas (N * (2 * t + 1)) : ℤ) := by
    rw [h]; exact ⟨(2 * t + 1) * e + lucas N * v, by ring⟩
  exact Int.natCast_dvd_natCast.1 hz

lemma lift (p N m : ℕ) (hodd : Odd p) (hm : 1 ≤ m) (h : p ^ m ∣ lucas N) :
    p ^ (m + 1) ∣ lucas (N * p) := by
  obtain ⟨t, rfl⟩ := hodd
  obtain ⟨v, e, _, hv⟩ := lucas_modsq N t
  obtain ⟨c, hc⟩ := h
  have hz : (((2 * t + 1) ^ (m + 1) : ℕ) : ℤ) ∣ (lucas (N * (2 * t + 1)) : ℤ) := by
    rw [hv, hc]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine ⟨e * c + (2 * t + 1) ^ m' * c ^ 2 * v, ?_⟩
    push_cast
    ring
  exact Int.natCast_dvd_natCast.1 hz

lemma power (p a : ℕ) (hodd : Odd p) (hpa : p ∣ lucas a) :
    ∀ m : ℕ, 1 ≤ m → ∀ t : ℕ, p ^ m ∣ lucas (a * p ^ (m - 1) * (2 * t + 1)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro t
    simp only [Nat.sub_self, pow_zero, mul_one, pow_one]
    exact Dvd.dvd.trans hpa (dvd_odd a t)
  | succ m hm ih =>
    intro t
    have h := lift p (a * p ^ (m - 1) * (2 * t + 1)) m hodd hm (ih t)
    have e : a * p ^ (m - 1) * (2 * t + 1) * p = a * p ^ (m + 1 - 1) * (2 * t + 1) := by
      have : p ^ (m + 1 - 1) = p ^ (m - 1) * p := by
        rw [← pow_succ]; congr 1; omega
      rw [this]; ring
    rw [e] at h
    exact h

lemma geo (p k : ℕ) (hp : 1 ≤ p) : (p - 1) * (∑ j ∈ Icc 1 k, p ^ (j - 1)) + 1 = p ^ k := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_Icc_succ_top (by omega), Nat.add_sub_cancel, pow_succ, ← ih]
    ring

theorem main' (p a : ℕ) (hp : p.Prime) (hp2 : 2 < p) (ha : IsLeast {k : ℕ | p ∣ lucas k} a)
    (m i : ℕ) (hm : 1 < m) :
    p ^ m ∣ lucas (a + a * (p - 1) * (∑ j ∈ Icc 1 (m - 1), p ^ (j - 1))
      + 2 * i * a * p ^ (m - 1)) := by
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
  have hpa : p ∣ lucas a := ha.1
  have h := power p a hodd hpa m (by omega) i
  have hg := geo p (m - 1) hp.pos
  have e : a + a * (p - 1) * (∑ j ∈ Icc 1 (m - 1), p ^ (j - 1)) + 2 * i * a * p ^ (m - 1)
      = a * p ^ (m - 1) * (2 * i + 1) := by
    rw [← hg]; ring
  rw [e]
  exact h

end OMA.A266587

theorem OMA.solution : type_of% @OMA.S_oeis_a266587.main :=
  fun p a hp hp2 ha m i hm => OMA.A266587.main' p a hp hp2 ha m i hm
