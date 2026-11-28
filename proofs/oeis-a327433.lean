import OMAStatements.S_oeis_a327433
import Mathlib

-- Problem: A327433: a(n) is the smallest k > 2 such that n divides A000587(k).
-- Upstream: formal-conjectures statements/oeis-a327433.lean:0 (declaration OMA.S_oeis_a327433.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. Fix n >= 1 and, for f : ZMod n -> ZMod n, put (Phi f)(x) = x f(x) - f(x + 1). From
-- S(k+1, i+1) = (i+1) S(k, i+1) + S(k, i) one gets, for every f,
--   sum_i (-1)^i S(k, i) f(i) = (Phi^k f)(0)   in ZMod n,
-- so B(k) = (Phi^k 1)(0) mod n for the complementary Bell numbers B(k). Phi is injective: if
-- h(x + 1) = x h(x) for all x then h(1) = 0, hence h(2) = 0, ..., hence h = 0. An injective map of
-- a finite set to itself is a permutation, so Phi^P = id for some P >= 1, and then
-- B(2 + P) = B(2) = 0 mod n.

namespace CompBell327433Proof
open OMA.S_oeis_a327433

lemma stirling2_eq_zero : ∀ k j : ℕ, k < j → stirling2 k j = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, j + 1, _ => by simp [stirling2]
  | k + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, j + 1, h => by
      have h1 := stirling2_eq_zero k (j + 1) (by omega)
      have h2 := stirling2_eq_zero k j (by omega)
      simp [stirling2, h1, h2]

def Phi (n : ℕ) (f : ZMod n → ZMod n) : ZMod n → ZMod n := fun x => x * f x - f (x + 1)

lemma key (n : ℕ) : ∀ (k : ℕ) (f : ZMod n → ZMod n),
    ∑ i ∈ Finset.range (k + 1),
        (-1 : ZMod n) ^ i * (stirling2 k i : ZMod n) * f (i : ZMod n)
      = ((Phi n)^[k] f) 0 := by
  intro k
  induction k with
  | zero =>
    intro f
    simp [stirling2]
  | succ k ih =>
    intro f
    rw [Function.iterate_succ_apply, ← ih (Phi n f), Finset.sum_range_succ']
    have hS0 : stirling2 (k + 1) 0 = 0 := by simp [stirling2]
    rw [hS0]
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have hG : ∑ i ∈ Finset.range (k + 1),
          (-1 : ZMod n) ^ (i + 1) * ((i + 1 : ℕ) : ZMod n) * (stirling2 k (i + 1) : ZMod n)
            * f ((i + 1 : ℕ) : ZMod n)
        = ∑ i ∈ Finset.range (k + 1),
          (-1 : ZMod n) ^ i * (i : ZMod n) * (stirling2 k i : ZMod n) * f (i : ZMod n) := by
      have h1 := Finset.sum_range_succ' (fun i : ℕ =>
        (-1 : ZMod n) ^ i * (i : ZMod n) * (stirling2 k i : ZMod n) * f (i : ZMod n)) (k + 1)
      have h2 := Finset.sum_range_succ (fun i : ℕ =>
        (-1 : ZMod n) ^ i * (i : ZMod n) * (stirling2 k i : ZMod n) * f (i : ZMod n)) (k + 1)
      have hk : stirling2 k (k + 1) = 0 := stirling2_eq_zero k (k + 1) (by omega)
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero] at h1
      rw [hk] at h2
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero] at h2
      rw [← h1, h2]
    have hL : ∀ i ∈ Finset.range (k + 1),
        (-1 : ZMod n) ^ (i + 1) * (stirling2 (k + 1) (i + 1) : ZMod n) * f ((i + 1 : ℕ) : ZMod n)
        = (-1 : ZMod n) ^ (i + 1) * ((i + 1 : ℕ) : ZMod n) * (stirling2 k (i + 1) : ZMod n)
            * f ((i + 1 : ℕ) : ZMod n)
          - (-1 : ZMod n) ^ i * (stirling2 k i : ZMod n) * f ((i : ZMod n) + 1) := by
      intro i _
      have hS : stirling2 (k + 1) (i + 1) = (i + 1) * stirling2 k (i + 1) + stirling2 k i := by
        simp [stirling2]
      rw [hS]
      push_cast
      ring
    have hR : ∀ i ∈ Finset.range (k + 1),
        (-1 : ZMod n) ^ i * (stirling2 k i : ZMod n) * Phi n f (i : ZMod n)
        = (-1 : ZMod n) ^ i * (i : ZMod n) * (stirling2 k i : ZMod n) * f (i : ZMod n)
          - (-1 : ZMod n) ^ i * (stirling2 k i : ZMod n) * f ((i : ZMod n) + 1) := by
      intro i _
      simp only [Phi]
      ring
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, hG]

lemma cast_compBell (n k : ℕ) : ((compBell k : ℤ) : ZMod n)
    = ∑ i ∈ Finset.range (k + 1),
        (-1 : ZMod n) ^ i * (stirling2 k i : ZMod n) * (fun _ : ZMod n => (1 : ZMod n)) (i : ZMod n) := by
  unfold compBell
  push_cast
  simp

lemma Phi_injective (n : ℕ) [NeZero n] : Function.Injective (Phi n) := by
  intro f g hfg
  have hrec : ∀ x : ZMod n, f (x + 1) - g (x + 1) = x * (f x - g x) := by
    intro x
    have h := congrFun hfg x
    simp only [Phi] at h
    linear_combination -h
  have hz : ∀ j : ℕ, f ((j + 1 : ℕ) : ZMod n) = g ((j + 1 : ℕ) : ZMod n) := by
    intro j
    induction j with
    | zero =>
      have h := hrec 0
      rw [zero_mul, sub_eq_zero] at h
      simpa using h
    | succ j ih =>
      have h := hrec ((j + 1 : ℕ) : ZMod n)
      rw [ih, sub_self, mul_zero, sub_eq_zero] at h
      have hc : ((j + 1 + 1 : ℕ) : ZMod n) = ((j + 1 : ℕ) : ZMod n) + 1 := by push_cast; ring
      rw [hc]
      exact h
  funext x
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hx : x = ((x.val + n - 1 + 1 : ℕ) : ZMod n) := by
    have h1 : x.val + n - 1 + 1 = x.val + n := by omega
    rw [h1]
    simp
  rw [hx]
  exact hz _

lemma exists_period (n : ℕ) [NeZero n] :
    ∃ P : ℕ, 0 < P ∧ ∀ f : ZMod n → ZMod n, (Phi n)^[P] f = f := by
  have hbij : Function.Bijective (Phi n) :=
    Finite.injective_iff_bijective.mp (Phi_injective n)
  refine ⟨orderOf (Equiv.ofBijective (Phi n) hbij), orderOf_pos _, fun f => ?_⟩
  have h := pow_orderOf_eq_one (Equiv.ofBijective (Phi n) hbij)
  have h2 := congrArg (fun σ : Equiv.Perm (ZMod n → ZMod n) => σ f) h
  simp only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq] at h2
  exact h2

end CompBell327433Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a327433.main := by
  intro n hn
  have : NeZero n := ⟨by omega⟩
  obtain ⟨P, hP, hper⟩ := CompBell327433Proof.exists_period n
  refine ⟨2 + P, by omega, ?_⟩
  have h2 : OMA.S_oeis_a327433.compBell 2 = 0 := by decide
  have hz : ((OMA.S_oeis_a327433.compBell (2 + P) : ℤ) : ZMod n) = 0 := by
    have e1 := CompBell327433Proof.cast_compBell n (2 + P)
    have e2 := CompBell327433Proof.key n (2 + P) (fun _ => (1 : ZMod n))
    have e3 := CompBell327433Proof.cast_compBell n 2
    have e4 := CompBell327433Proof.key n 2 (fun _ => (1 : ZMod n))
    rw [e1, e2, Function.iterate_add_apply, hper, ← e4, ← e3, h2]
    simp
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
