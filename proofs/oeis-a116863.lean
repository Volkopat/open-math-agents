import OMAStatements.S_oeis_a116863
import Mathlib.Tactic

open OMA.S_oeis_a116863 Finset Matrix

namespace CartanRowSums

private def pad {n : ℕ} (v : Fin n → ℚ) : ℕ → ℚ
  | 0 => 0
  | k+1 => if h : k < n then v ⟨k,h⟩ else 0

private lemma selector_sum {n : ℕ} (k : ℕ) (v : Fin n → ℚ) :
    (∑ j : Fin n, selector k j * v j) = pad v k := by
  cases k with
  | zero => simp [selector, pad]
  | succ k =>
    by_cases hk : k < n
    · let index : Fin n := ⟨k,hk⟩
      rw [sum_eq_single index]
      · simp [index, selector, pad, hk]
      · intro j _ hj
        have h : j.val ≠ k := fun he => hj (Fin.ext he)
        simp [selector, h]
      · simp
    · have none (j : Fin n) : j.val ≠ k := by have := j.isLt; omega
      simp [selector, pad, hk, none]

private lemma action {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    ((cartan n) *ᵥ v) i = 2 * pad v (i.val+1) - pad v i.val - pad v (i.val+2) := by
  change (∑ j : Fin n,
    (2 * selector (i.val+1) j - selector i.val j - selector (i.val+2) j) * v j) = _
  simp only [sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum, selector_sum]

private def system (n : ℕ) (c : ℚ) (u : ℕ → ℚ) : Prop :=
  u 0 = 0 ∧ u (n+1) = 0 ∧ ∀ i, i < n → 2*u (i+1) - u i - u (i+2) = c

private lemma by_action {n : ℕ} {c : ℚ} {v : Fin n → ℚ}
    (h : (cartan n) *ᵥ v = fun _ => c) : system n c (pad v) := by
  refine ⟨rfl, by simp [pad], ?_⟩
  intro i hi
  simpa only [action] using congrFun h (⟨i,hi⟩ : Fin n)

private lemma unique_on {n : ℕ} {c : ℚ} {u v : ℕ → ℚ} (hu : system n c u)
    (hv : system n c v) (i : ℕ) (hi : i ≤ n+1) : u i = v i := by
  let d (k : ℕ) := u k - v k
  have recn (k : ℕ) (hk : k < n) : d (k+2) = 2*d (k+1) - d k := by
    dsimp [d]
    linear_combination hv.2.2 k hk - hu.2.2 k hk
  let rec linear : (k : ℕ) → k ≤ n+1 → d k = (k : ℚ) * d 1
    | 0, _ => by simp [d,hu.1,hv.1]
    | 1, _ => by simp
    | k+2, h => by
      rw [recn k (by omega), linear (k+1) (by omega), linear k (by omega)]
      push_cast
      ring
  have right : d (n+1) = 0 := by simp [d,hu.2.1,hv.2.1]
  have product : ((n+1 : ℕ) : ℚ) * d 1 = 0 := (linear _ le_rfl).symm.trans right
  have slope : d 1 = 0 := (mul_eq_zero.mp product).resolve_left (by positivity)
  have eqn := linear i hi
  rw [slope, mul_zero] at eqn
  exact sub_eq_zero.mp eqn

private lemma isUnit_det (n : ℕ) : IsUnit (cartan n).det := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  obtain ⟨v,hv,zero⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := cartan n)).2 h
  have zeroSystem : system n 0 (fun _ => 0) := by simp [system]
  apply hv
  funext i
  have agree := unique_on (by_action (c := 0) zero) zeroSystem (i.val+1) (by have := i.isLt; omega)
  simpa [pad, i.isLt] using agree

private def profile (n i : ℕ) : ℚ := (i : ℚ) * ((n : ℚ)+1-i) / 2

private lemma profile_system (n : ℕ) : system n 1 (profile n) := by
  refine ⟨by simp [profile], by simp [profile], ?_⟩
  intro i _
  unfold profile
  push_cast
  ring

private lemma moment (a : ℚ) (k : ℕ) :
    12 * (∑ i ∈ range (k+1), (i : ℚ)*(a-i)/2) =
      (k : ℚ)*(k+1)*(3*a-2*k-1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination ih

private lemma profile_total (n : ℕ) :
    12 * (∑ i : Fin n, profile n (i.val+1)) = (n : ℚ)*(n+1)*(n+2) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => profile n (i+1)) n]
  have extend : (∑ i ∈ range n, profile n (i+1)) = ∑ i ∈ range (n+1), profile n i := by
    rw [sum_range_succ']
    simp [profile]
  rw [extend]
  unfold profile
  linear_combination moment ((n : ℚ)+1) n

end CartanRowSums

open CartanRowSums

theorem OMA.solution : type_of% @OMA.S_oeis_a116863.main := by
  intro n _
  let v := (cartan n)⁻¹ *ᵥ (fun _ : Fin n => (1 : ℚ))
  have eqn : (cartan n) *ᵥ v = fun _ => 1 := by
    dsimp [v]
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_det n), one_mulVec]
  have row (i : Fin n) : (∑ j : Fin n, (cartan n)⁻¹ i j) = profile n (i.val+1) := by
    have agree := unique_on (by_action eqn) (profile_system n) (i.val+1) (by have := i.isLt; omega)
    simpa [pad, i.isLt, v, Matrix.mulVec, dotProduct] using agree
  unfold rowSum pyramidal
  simp_rw [row]
  push_cast
  linear_combination (((n : ℚ)+1)/4) * profile_total n
