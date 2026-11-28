import OMAStatements.S_mo_375001
import Mathlib

-- Credit: @Aryan-Poonacha
-- Antonio AN's question: https://mathoverflow.net/questions/375001
-- The delayed-agreement construction follows the ideas of Doriano Brogioli
-- and Jochen Glueck in comments 950539 and 950560. A uniform discount gives
-- both row and column bounds, even for the map that jumps immediately.
namespace DelayedAgreement

open Matrix Finset
open scoped Matrix

private def delta {r : ℕ} (i : Fin r) : Fin r → ℝ := Pi.single i 1

private def step {r : ℕ} (w : ℝ) (f : Fin r → Fin r) : Matrix (Fin r) (Fin r) ℝ :=
  fun i => w • delta (f i)

private lemma orbit {r : ℕ} (w : ℝ) (f : Fin r → Fin r) (s : Fin r) (k : ℕ) :
    delta s ᵥ* (step w f)^k = w^k • delta ((f^[k]) s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul, ih, Matrix.smul_vecMul,
      show delta ((f^[k]) s) ᵥ* step w f = w • delta (f ((f^[k]) s)) by
        exact Matrix.single_one_vecMul .., smul_smul, ← pow_succ, Function.iterate_succ_apply']

private lemma delta_ne {r : ℕ} (i : Fin r) (z : ℝ) (hz : z ≠ 0) : z • delta i ≠ 0 := by
  intro h
  have hi := congrFun h i
  exact hz (by simpa [delta] using hi)

private lemma bounds {n : ℕ} (f : Fin (n+1) → Fin (n+1)) (w : ℝ)
    (hw : 0 < w) (hs : ((n:ℝ)+1)*w = 1) :
    (∀ i j, 0 ≤ step w f i j) ∧ (∀ i, (∑ j, step w f i j) ≤ 1) ∧
      (∀ j, (∑ i, step w f i j) ≤ 1) := by
  have h (i j) : 0 ≤ step w f i j ∧ step w f i j ≤ w := by
    by_cases hij : f i = j <;> simp [step, delta, hij, hw.le]
  have hc : ∑ _i : Fin (n+1), w = 1 := by simpa using hs
  refine ⟨fun i j => (h i j).1, fun i => ?_, fun j => ?_⟩
  · exact (sum_le_sum fun j _ => (h i j).2).trans_eq hc
  · exact (sum_le_sum fun i _ => (h i j).2).trans_eq hc

private def tick (n : ℕ) (i : Fin (n+1)) : Fin (n+1) :=
  ⟨min (i.val+1) n, by omega⟩

private lemma ticks (n k : ℕ) : (tick n)^[k] 0 = ⟨min k n, by omega⟩ := by
  induction k with
  | zero => ext; simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    apply Fin.ext
    change min (min k n + 1) n = min (k+1) n
    omega

end DelayedAgreement

open DelayedAgreement OMA.S_mo_375001 Matrix Finset
open scoped Matrix

theorem OMA.solution : type_of% @OMA.S_mo_375001.main := by
  intro n hn
  let w : ℝ := 1 / ((n:ℝ)+1)
  have hw : 0 < w := by dsimp [w]; positivity
  have hs : ((n:ℝ)+1)*w = 1 := by dsimp [w]; field_simp
  let topState : Fin (n+1) := Fin.last n
  let jump : Fin (n+1) → Fin (n+1) := fun _ => topState
  have jump_iter (k : ℕ) (hk : 0 < k) : jump^[k] 0 = topState := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [Function.iterate_succ_apply']
  have meet (k : ℕ) (hk : n ≤ k) :
      delta 0 ᵥ* (step w jump)^k = delta 0 ᵥ* (step w (tick n))^k := by
    have ht : (tick n)^[k] 0 = topState := Fin.ext (by rw [ticks]; exact min_eq_right hk)
    rw [orbit, orbit, jump_iter k (by omega), ht]
  have survive (f : Fin (n+1) → Fin (n+1)) (k : ℕ) : (step w f)^k ≠ 0 := by
    intro h
    exact delta_ne _ _ (pow_ne_zero k hw.ne') (by rw [← orbit w f 0 k, h, Matrix.vecMul_zero])
  obtain ⟨an, ar, ac⟩ := bounds jump w hw hs
  obtain ⟨bn, br, bc⟩ := bounds (tick n) w hw hs
  refine ⟨n+1, delta 0, step w jump, step w (tick n), by omega, ?_, ?_, ?_,
    an, bn, ar, ac, br, bc, survive jump, survive (tick n), meet n le_rfl, ?_, ?_, meet⟩
  · intro i
    by_cases hi : i = 0 <;> simp [delta, hi]
  · simp [delta, Pi.single_apply]
  · intro i
    by_cases hi : i = 0 <;> simp [delta, hi]
  · rw [orbit]
    exact delta_ne _ _ (pow_ne_zero n hw.ne')
  · intro k hk hkn h
    have ht : (tick n)^[k] 0 = (⟨k, by omega⟩ : Fin (n+1)) :=
      Fin.ext (by rw [ticks]; exact min_eq_left hkn.le)
    rw [orbit, orbit, jump_iter k hk, ht] at h
    have hdiff : (⟨k, by omega⟩ : Fin (n+1)) ≠ topState := by
      intro he
      have := congrArg Fin.val he
      change k = n at this
      omega
    have H := congrFun h topState
    exact (pow_ne_zero k hw.ne') (by simpa [delta, Pi.single_apply, hdiff, Ne.symm hdiff] using H)
