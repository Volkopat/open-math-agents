import OMAStatements.S_oeis_a325696
import Mathlib

-- Problem: A325696, length-3 strict compositions of n with no part the sum of the other two.
-- Proof: sorting the three parts maps each such composition to a strict partition a < b < c
-- with c /= a + b, and every fibre of the sorting map has exactly 6 elements, so the count
-- is 6 times the count of A325695. For that count the inner sum has a closed form with a
-- period-12 step identity, which gives the order-9 recurrence by induction and the
-- generating function coefficientwise.

namespace OMA.P_a325696
open PowerSeries

def allowedP (n u v : ℕ) : Bool :=
  let a := u+1
  let b := a+v+1
  let c := n-(a+b)
  decide (b<c ∧ a+b+c=n ∧ c≠a+b)

def termP (n : ℕ) : ℕ := ∑ u ∈ Finset.range (n+1),
  ((Finset.range (n+1)).filter (fun v => allowedP n u v)).card

noncomputable def seriesP : PowerSeries ℚ := PowerSeries.mk (fun n => termP n)

def A' (n u : ℕ) : ℕ := (n - (3*u+5) + 1)/2
def B' (n u : ℕ) : ℕ := if n % 2 = 0 ∧ 4*u+6 ≤ n then 1 else 0

lemma allowedP_iff (n u v : ℕ) :
    allowedP n u v = true ↔ 3*u+2*v+5 < n ∧ n ≠ 4*u+2*v+6 := by
  simp only [allowedP, decide_eq_true_eq]
  omega

lemma card_eq (n u : ℕ) :
    ((Finset.range (n+1)).filter (fun v => allowedP n u v)).card + B' n u = A' n u := by
  unfold A' B'
  split_ifs with h
  · have hs : (Finset.range (n+1)).filter (fun v => allowedP n u v) =
        (Finset.range ((n - (3*u+5) + 1)/2)).erase ((n - (4*u+6))/2) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, allowedP_iff]
      omega
    have hm : (n - (4*u+6))/2 ∈ Finset.range ((n - (3*u+5) + 1)/2) := by
      simp only [Finset.mem_range]; omega
    rw [hs, Finset.card_erase_of_mem hm, Finset.card_range]
    omega
  · have hs : (Finset.range (n+1)).filter (fun v => allowedP n u v) =
        Finset.range ((n - (3*u+5) + 1)/2) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, allowedP_iff]
      omega
    rw [hs, Finset.card_range, add_zero]

lemma term_eq (n : ℕ) :
    termP n + ∑ u ∈ Finset.range (n+1), B' n u = ∑ u ∈ Finset.range (n+1), A' n u := by
  simp only [termP, ← Finset.sum_add_distrib, card_eq]

lemma sumA_ext (n j : ℕ) :
    ∑ u ∈ Finset.range (n+1+j), A' n u = ∑ u ∈ Finset.range (n+1), A' n u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show n+1+(j+1) = (n+1+j)+1 by omega, Finset.sum_range_succ, ih]
    have : A' n (n+1+j) = 0 := by unfold A'; omega
    rw [this, add_zero]

lemma sumB_ext (n j : ℕ) :
    ∑ u ∈ Finset.range (n+1+j), B' n u = ∑ u ∈ Finset.range (n+1), B' n u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show n+1+(j+1) = (n+1+j)+1 by omega, Finset.sum_range_succ, ih]
    have : B' n (n+1+j) = 0 := by unfold B'; split_ifs <;> omega
    rw [this, add_zero]

lemma sumA_shift (n : ℕ) :
    ∑ u ∈ Finset.range (n+12+1), A' (n+12) u = ∑ u ∈ Finset.range (n+1), A' n u +
      (A' (n+12) 0 + A' (n+12) 1 + A' (n+12) 2 + A' (n+12) 3) := by
  rw [show n+12+1 = 4 + (n+1+8) by omega, Finset.sum_range_add]
  have : ∀ u, A' (n+12) (4+u) = A' n u := by intro u; unfold A'; omega
  simp only [this]
  rw [sumA_ext]
  have hs : ∑ u ∈ Finset.range 4, A' (n+12) u =
      A' (n+12) 0 + A' (n+12) 1 + A' (n+12) 2 + A' (n+12) 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hs]
  ring

lemma sumB_shift (n : ℕ) :
    ∑ u ∈ Finset.range (n+12+1), B' (n+12) u = ∑ u ∈ Finset.range (n+1), B' n u +
      (B' (n+12) 0 + B' (n+12) 1 + B' (n+12) 2) := by
  rw [show n+12+1 = 3 + (n+1+9) by omega, Finset.sum_range_add]
  have : ∀ u, B' (n+12) (3+u) = B' n u := by
    intro u; unfold B'
    have : (4*(3+u)+6 ≤ n+12) ↔ 4*u+6 ≤ n := by omega
    have h2 : (n+12) % 2 = n % 2 := by omega
    simp only [this, h2]
  simp only [this]
  rw [sumB_ext]
  have hs : ∑ u ∈ Finset.range 3, B' (n+12) u = B' (n+12) 0 + B' (n+12) 1 + B' (n+12) 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hs]
  ring

lemma key (n : ℕ) (hn : 1 ≤ n) :
    termP (n+12) + 3*((n+1)%2) = termP n + ((n+8)/2 + (n+5)/2 + (n+2)/2 + (n-2+1)/2) := by
  have h1 := term_eq (n+12)
  have h2 := term_eq n
  rw [sumA_shift, sumB_shift] at h1
  have hB : B' (n+12) 0 + B' (n+12) 1 + B' (n+12) 2 = 3*((n+1)%2) := by
    unfold B'; split_ifs <;> omega
  have hA : A' (n+12) 0 + A' (n+12) 1 + A' (n+12) 2 + A' (n+12) 3 =
      (n+8)/2 + (n+5)/2 + (n+2)/2 + (n-2+1)/2 := by
    unfold A'; omega
  omega

set_option maxRecDepth 100000 in
lemma base (k : ℕ) (hk : k < 12) :
    termP (k+10)+termP (k+5)+termP (k+4)+termP (k+3) =
      termP (k+8)+termP (k+7)+termP (k+6)+termP (k+1) := by
  interval_cases k <;> decide +kernel

lemma recur : ∀ k : ℕ, termP (k+10)+termP (k+5)+termP (k+4)+termP (k+3) =
      termP (k+8)+termP (k+7)+termP (k+6)+termP (k+1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 12
    · exact base k hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 12 := ⟨k - 12, by omega⟩
      have IH := ih j (by omega)
      have e1 := key (j+10) (by omega)
      have e2 := key (j+5) (by omega)
      have e3 := key (j+4) (by omega)
      have e4 := key (j+3) (by omega)
      have e5 := key (j+8) (by omega)
      have e6 := key (j+7) (by omega)
      have e7 := key (j+6) (by omega)
      have e8 := key (j+1) (by omega)
      rw [show j+12+10 = j+10+12 by omega, show j+12+5 = j+5+12 by omega,
        show j+12+4 = j+4+12 by omega, show j+12+3 = j+3+12 by omega,
        show j+12+8 = j+8+12 by omega, show j+12+7 = j+7+12 by omega,
        show j+12+6 = j+6+12 by omega, show j+12+1 = j+1+12 by omega]
      omega

set_option maxRecDepth 100000 in
lemma small : termP 0 = 0 ∧ termP 1 = 0 ∧ termP 2 = 0 ∧ termP 3 = 0 ∧ termP 4 = 0 ∧
    termP 5 = 0 ∧ termP 6 = 0 ∧ termP 7 = 1 ∧ termP 8 = 1 ∧ termP 9 = 3 := by
  decide +kernel

lemma poly_eq : ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2) : PowerSeries ℚ) =
    1 - X^2 - X^3 - X^4 + X^5 + X^6 + X^7 - X^9 := by ring

lemma gf : ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2))*seriesP =
    (X^7*(1+X+2*X^2) : PowerSeries ℚ) := by
  rw [poly_eq, show (X^7*(1+X+2*X^2) : PowerSeries ℚ) = X^7 + X^8 + X^9 + X^9 by ring]
  ext n
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add, coeff_X_pow_mul', seriesP, coeff_mk,
    coeff_X_pow]
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := small
  by_cases hn : 10 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have h := recur k
    have h' : ((termP (k+10) : ℚ) + termP (k+5) + termP (k+4) + termP (k+3)) =
        termP (k+8) + termP (k+7) + termP (k+6) + termP (k+1) := by exact_mod_cast h
    simp only [show 2 ≤ k+10 by omega, show 3 ≤ k+10 by omega, show 4 ≤ k+10 by omega,
      show 5 ≤ k+10 by omega, show 6 ≤ k+10 by omega, show 7 ≤ k+10 by omega,
      show 9 ≤ k+10 by omega, if_true, show k+10 ≠ 7 by omega, show k+10 ≠ 8 by omega,
      show k+10 ≠ 9 by omega, if_false,
      show k+10-2 = k+8 by omega, show k+10-3 = k+7 by omega, show k+10-4 = k+6 by omega,
      show k+10-5 = k+5 by omega, show k+10-6 = k+4 by omega, show k+10-7 = k+3 by omega,
      show k+10-9 = k+1 by omega]
    linarith
  · interval_cases n <;> simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] <;> norm_num


def S (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n+1) ×ˢ Finset.range (n+1)).filter
    (fun p => OMA.S_oeis_a325696.allowed n p.1 p.2)

def T (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n+1) ×ˢ Finset.range (n+1)).filter (fun p => allowedP n p.1 p.2)

def psi (n a b : ℕ) : ℕ × ℕ :=
  (min a (min b (n-(a+b))) - 1,
    (n - min a (min b (n-(a+b))) - max a (max b (n-(a+b)))) - min a (min b (n-(a+b))) - 1)

lemma allowed_iff (n a b : ℕ) :
    OMA.S_oeis_a325696.allowed n a b = true ↔
      0 < a ∧ 0 < b ∧ a + b < n ∧ a ≠ b ∧ 2*a + b ≠ n ∧ a + 2*b ≠ n ∧
        2*a ≠ n ∧ 2*b ≠ n ∧ 2*(a+b) ≠ n := by
  simp only [OMA.S_oeis_a325696.allowed, decide_eq_true_eq]
  omega

lemma term_card (n : ℕ) : OMA.S_oeis_a325696.term n = (S n).card := by
  simp only [OMA.S_oeis_a325696.term, S, Finset.card_filter, Finset.sum_product]

lemma termP_card (n : ℕ) : termP n = (T n).card := by
  simp only [termP, T, Finset.card_filter, Finset.sum_product]

lemma psi_mem (n : ℕ) : ∀ p ∈ S n, psi n p.1 p.2 ∈ T n := by
  rintro ⟨a, b⟩ hp
  simp only [S, T, Finset.mem_filter, Finset.mem_product, Finset.mem_range, allowed_iff,
    allowedP_iff, psi, min_def, max_def] at hp ⊢
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
lemma fiber (n : ℕ) : ∀ t ∈ T n, ((S n).filter (fun p => psi n p.1 p.2 = t)).card = 6 := by
  rintro ⟨u, v⟩ ht
  simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range, allowedP_iff] at ht
  have hs : (S n).filter (fun p => psi n p.1 p.2 = (u, v)) =
      {(u+1, u+v+2), (u+v+2, u+1), (u+1, n-(2*u+v+3)), (n-(2*u+v+3), u+1),
        (u+v+2, n-(2*u+v+3)), (n-(2*u+v+3), u+v+2)} := by
    ext ⟨a, b⟩
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range, allowed_iff, psi,
      Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton, min_def, max_def]
    constructor
    · rintro ⟨h1, h2⟩
      split_ifs at h2 <;>
        first
          | (left; omega) | (right; left; omega) | (right; right; left; omega)
          | (right; right; right; left; omega) | (right; right; right; right; left; omega)
          | (right; right; right; right; right; omega) | omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        split_ifs <;> omega
  rw [hs]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega

lemma term_eq_six (n : ℕ) : OMA.S_oeis_a325696.term n = 6 * termP n := by
  rw [term_card, termP_card, Finset.card_eq_sum_card_fiberwise (psi_mem n),
    Finset.sum_congr rfl (fiber n)]
  simp [mul_comm]

lemma series_eq : OMA.S_oeis_a325696.series = C (6 : ℚ) * seriesP := by
  ext n
  simp only [OMA.S_oeis_a325696.series, seriesP, coeff_mk, coeff_C_mul, term_eq_six]
  push_cast
  ring

end OMA.P_a325696

theorem OMA.solution : type_of% @OMA.S_oeis_a325696.main := by
  refine ⟨?_, ?_⟩
  · intro k
    have h := OMA.P_a325696.recur k
    simp only [OMA.P_a325696.term_eq_six]
    omega
  · rw [OMA.P_a325696.series_eq, mul_left_comm, OMA.P_a325696.gf,
      show (PowerSeries.C (6 : ℚ) : PowerSeries ℚ) = 6 from map_ofNat _ 6]
    ring
