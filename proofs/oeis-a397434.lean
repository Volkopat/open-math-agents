import OMAStatements.S_oeis_a397434
import Mathlib

namespace A397434W
open Finset

def S (k t : ℕ) : ℕ := ∑ m ∈ range (k+1), if t ≤ m then k.choose m else 0

lemma coef_eq {α : Type*} (t : ℕ) (s : Finset α) :
    OMA.S_oeis_a397434.coefficient t s = S s.card t % 2 := by
  unfold OMA.S_oeis_a397434.coefficient S
  rw [Finset.sum_powerset_apply_card (fun m => if t ≤ m then 1 else 0)]
  simp [mul_ite]

lemma mono_eq (n : ℕ) : OMA.S_oeis_a397434.monomials n =
    ∑ k ∈ range (n+1), n.choose k * (S k ((n+1)/2) % 2) := by
  unfold OMA.S_oeis_a397434.monomials
  simp_rw [coef_eq]
  rw [Finset.sum_powerset_apply_card (fun m => S m ((n+1)/2) % 2)]
  simp

lemma S_split (k t : ℕ) : S k t = k.choose t + S k (t+1) := by
  unfold S
  have : ∀ m ∈ range (k+1), (if t ≤ m then k.choose m else 0) =
      (if t = m then k.choose m else 0) + (if t + 1 ≤ m then k.choose m else 0) := by
    intro m _
    by_cases h1 : t = m
    · subst h1; simp
    · by_cases h2 : t + 1 ≤ m
      · simp [h1, h2, show t ≤ m by omega]
      · simp [h1, h2, show ¬ t ≤ m by omega]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simp at h; omega)]

lemma S_shift (k t : ℕ) :
    (∑ m ∈ range (k+1), if t ≤ m then k.choose (m+1) else 0) = S k (t+1) := by
  unfold S
  rw [Finset.sum_range_succ' (fun m => if t + 1 ≤ m then k.choose m else 0)]
  rw [Finset.sum_range_succ]
  simp only [show ¬ (t + 1 ≤ 0) by omega, if_false, add_zero]
  rw [Nat.choose_eq_zero_of_lt (by omega : k < k + 1)]
  simp

lemma S_succ (k t : ℕ) : S (k+1) (t+1) = k.choose t + 2 * S k (t+1) := by
  have h1 : S (k+1) (t+1) = S k t +
      ∑ m ∈ range (k+1), (if t ≤ m then k.choose (m+1) else 0) := by
    unfold S
    rw [Finset.sum_range_succ' (fun m => if t + 1 ≤ m then (k+1).choose m else 0)]
    simp only [show ¬ (t + 1 ≤ 0) by omega, if_false, add_zero]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : t ≤ m
    · simp [h, Nat.choose_succ_succ']
    · simp [h]
  rw [h1, S_shift, S_split k t]; ring

lemma S_par (k t : ℕ) : S (k+1) (t+1) % 2 = k.choose t % 2 := by
  rw [S_succ]; omega

lemma S_zero (t : ℕ) : S 0 (t+1) = 0 := by
  simp [S]

lemma mono_eq2 (n : ℕ) (hn : 1 ≤ n) : OMA.S_oeis_a397434.monomials n =
    ∑ i ∈ range n, n.choose (i+1) * (i.choose ((n+1)/2 - 1) % 2) := by
  rw [mono_eq, Finset.sum_range_succ']
  obtain ⟨t, ht⟩ : ∃ t, (n+1)/2 = t + 1 := ⟨(n+1)/2 - 1, by omega⟩
  rw [ht, S_zero]
  simp only [Nat.zero_mod, mul_zero, add_zero, S_par, show t + 1 - 1 = t by omega]

/-- Extend the range. -/
lemma ext_range (n β d : ℕ) :
    (∑ i ∈ range (n + d), n.choose (i+1) * (i.choose β % 2)) =
      ∑ i ∈ range n, n.choose (i+1) * (i.choose β % 2) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← add_assoc, Finset.sum_range_succ, ih,
      Nat.choose_eq_zero_of_lt (by omega : n < n + d + 1)]
    simp

lemma pair_sum (f : ℕ → ℕ) (K : ℕ) :
    (∑ i ∈ range (2*K), f i) = ∑ c ∈ range K, (f (2*c) + f (2*c+1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K+1) = 2*K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

lemma luc (x y : ℕ) : x.choose y % 2 = ((x%2).choose (y%2) * (x/2).choose (y/2)) % 2 := by
  have := Fact.mk Nat.prime_two
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

lemma l00 (c b : ℕ) : (2*c).choose (2*b) % 2 = c.choose b % 2 := by
  rw [luc]; simp [show (2*c)%2 = 0 by omega, show (2*b)%2 = 0 by omega,
    show 2*c/2 = c by omega, show 2*b/2 = b by omega]
lemma l10 (c b : ℕ) : (2*c+1).choose (2*b) % 2 = c.choose b % 2 := by
  rw [luc]; simp [show (2*c+1)%2 = 1 by omega, show (2*b)%2 = 0 by omega,
    show (2*c+1)/2 = c by omega, show 2*b/2 = b by omega]
lemma l01 (c b : ℕ) : (2*c).choose (2*b+1) % 2 = 0 := by
  rw [luc]; simp [show (2*c)%2 = 0 by omega, show (2*b+1)%2 = 1 by omega]
lemma l11 (c b : ℕ) : (2*c+1).choose (2*b+1) % 2 = c.choose b % 2 := by
  rw [luc]; simp [show (2*c+1)%2 = 1 by omega, show (2*b+1)%2 = 1 by omega,
    show (2*c+1)/2 = c by omega, show (2*b+1)/2 = b by omega]

/-- Generic form with range 2K. -/
lemma mono_K (n K : ℕ) (hn : 1 ≤ n) (hK : n ≤ 2 * K) : OMA.S_oeis_a397434.monomials n =
    ∑ c ∈ range K, (n.choose (2*c+1) * ((2*c).choose ((n+1)/2 - 1) % 2) +
      n.choose (2*c+2) * ((2*c+1).choose ((n+1)/2 - 1) % 2)) := by
  rw [mono_eq2 n hn, ← ext_range n _ (2*K - n), show n + (2*K - n) = 2*K by omega, pair_sum]

/-- Case n = 4b+2: equality. -/
lemma caseB (b : ℕ) : OMA.S_oeis_a397434.monomials (4*b+2) =
    OMA.S_oeis_a397434.monomials (4*b+3) := by
  rw [mono_K (4*b+2) (2*b+2) (by omega) (by omega), mono_K (4*b+3) (2*b+2) (by omega) (by omega)]
  simp only [show (4*b+2+1)/2 - 1 = 2*b by omega, show (4*b+3+1)/2 - 1 = 2*b+1 by omega,
    l00, l10, l01, l11]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : (4*b+3).choose (2*c+2) = (4*b+2).choose (2*c+1) + (4*b+2).choose (2*c+2) :=
    Nat.choose_succ_succ' _ _
  rw [h1]; ring

/-- Case n odd. -/
lemma caseA (r : ℕ) : OMA.S_oeis_a397434.monomials (2*r+1) <
    OMA.S_oeis_a397434.monomials (2*r+2) := by
  rw [mono_eq2 _ (by omega), mono_eq2 _ (by omega), Finset.sum_range_succ _ (2*r+1)]
  simp only [show (2*r+1+1)/2 - 1 = r by omega, show (2*r+2+1)/2 - 1 = r by omega]
  refine lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
  apply Finset.sum_lt_sum
  · intro i _
    exact Nat.mul_le_mul_right _ (Nat.choose_le_choose _ (by omega))
  · refine ⟨r, by simp; omega, ?_⟩
    simp only [Nat.choose_self, Nat.one_mod, mul_one]
    rw [Nat.choose_succ_succ' (2*r+1) r]
    have : 0 < (2*r+1).choose r := Nat.choose_pos (by omega)
    omega

/-- Case n = 4b+4: strict. -/
lemma caseC (b : ℕ) : OMA.S_oeis_a397434.monomials (4*b+4) <
    OMA.S_oeis_a397434.monomials (4*b+5) := by
  set K := 2*b+3 with hKdef
  rw [mono_K (4*b+4) K (by omega) (by omega), mono_K (4*b+5) K (by omega) (by omega)]
  simp only [show (4*b+4+1)/2 - 1 = 2*b+1 by omega, show (4*b+5+1)/2 - 1 = 2*b+2 by omega,
    show 2*b+2 = 2*(b+1) by ring, l00, l10, l01, l11]
  set N := 4*b+4 with hN
  set w : ℕ → ℕ := fun c => c.choose (b+1) % 2 with hw
  -- rewrite RHS terms
  have hR : ∀ c, (4*b+5).choose (2*c+1) * (c.choose (b+1) % 2) +
      (4*b+5).choose (2*c+2) * (c.choose (b+1) % 2) =
      (N.choose (2*c) + N.choose (2*c+2)) * w c + 2 * (N.choose (2*c+1) * w c) := by
    intro c
    rw [show 4*b+5 = N+1 by omega, Nat.choose_succ_succ' N (2*c), Nat.choose_succ_succ' N (2*c+1)]
    simp only [hw]; ring
  have hL : ∀ c, N.choose (2*c+1) * 0 + N.choose (2*c+2) * (c.choose b % 2) ≤
      N.choose (2*c+2) * w c + N.choose (2*(c+1)) * w (c+1) := by
    intro c
    have hp : (c+1).choose (b+1) = c.choose b + c.choose (b+1) := Nat.choose_succ_succ' c b
    have : c.choose b % 2 ≤ w c + w (c+1) := by simp only [hw, hp]; omega
    rw [show 2*(c+1) = 2*c+2 by ring]
    nlinarith [Nat.zero_le (N.choose (2*c+2))]
  have hshift : (∑ c ∈ range K, N.choose (2*(c+1)) * w (c+1)) ≤
      ∑ c ∈ range K, N.choose (2*c) * w c := by
    have := Finset.sum_range_succ' (fun c => N.choose (2*c) * w c) K
    rw [Finset.sum_range_succ] at this
    rw [Nat.choose_eq_zero_of_lt (by omega : N < 2*K)] at this
    simp only [zero_mul, add_zero] at this
    rw [this]; exact Nat.le_add_right _ _
  have hS : (∑ c ∈ range K, (N.choose (2*c+1) * 0 + N.choose (2*c+2) * (c.choose b % 2))) ≤
      ∑ c ∈ range K, (N.choose (2*c) + N.choose (2*c+2)) * w c := by
    calc _ ≤ ∑ c ∈ range K, (N.choose (2*c+2) * w c + N.choose (2*(c+1)) * w (c+1)) :=
          Finset.sum_le_sum fun c _ => hL c
      _ = (∑ c ∈ range K, N.choose (2*c+2) * w c) + ∑ c ∈ range K, N.choose (2*(c+1)) * w (c+1) :=
          Finset.sum_add_distrib
      _ ≤ (∑ c ∈ range K, N.choose (2*c+2) * w c) + ∑ c ∈ range K, N.choose (2*c) * w c :=
          Nat.add_le_add_left hshift _
      _ = _ := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun c _ => by ring
  have hpos : 0 < ∑ c ∈ range K, 2 * (N.choose (2*c+1) * w c) := by
    apply Finset.sum_pos' (fun c _ => Nat.zero_le _)
    refine ⟨b+1, by simp [hKdef]; omega, ?_⟩
    have : w (b+1) = 1 := by simp [hw]
    rw [this]
    have : 0 < N.choose (2*(b+1)+1) := Nat.choose_pos (by omega)
    omega
  calc _ ≤ ∑ c ∈ range K, (N.choose (2*c) + N.choose (2*c+2)) * w c := hS
    _ < (∑ c ∈ range K, (N.choose (2*c) + N.choose (2*c+2)) * w c) +
          ∑ c ∈ range K, 2 * (N.choose (2*c+1) * w c) := by omega
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => (hR c).symm

theorem solution_main : ∀ n : ℕ, 1 ≤ n →
    (OMA.S_oeis_a397434.monomials n = OMA.S_oeis_a397434.monomials (n+1) ↔ n % 4 = 2) := by
  intro n hn
  obtain ⟨q, hq⟩ : ∃ q, n = 4*q + n % 4 := ⟨n/4, by omega⟩
  have h4 : n % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : n % 4
  · -- n = 4q, q ≥ 1
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    have := caseC b
    rw [hq, show 4*(b+1)+0 = 4*b+4 by ring, show 4*b+4+1 = 4*b+5 by ring]
    simp; omega
  · have := caseA (2*q)
    rw [hq, show 4*q+1 = 2*(2*q)+1 by ring, show 2*(2*q)+1+1 = 2*(2*q)+2 by ring]
    simp; omega
  · rw [hq, show 4*q+2+1 = 4*q+3 by ring]
    simpa using caseB q
  · have := caseA (2*q+1)
    rw [hq, show 4*q+3 = 2*(2*q+1)+1 by ring, show 2*(2*q+1)+1+1 = 2*(2*q+1)+2 by ring]
    simp; omega

end A397434W

theorem OMA.solution : type_of% @OMA.S_oeis_a397434.main := A397434W.solution_main
