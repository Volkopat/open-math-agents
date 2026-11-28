import FormalConjectures.ErdosProblems.«454»
import Mathlib.NumberTheory.Chebyshev

/-! The first minimum of a linearly tilted prime sequence gives a strict midpoint. -/

open Filter

namespace OMA

/-- Chebyshev’s prime-counting bound gives an affine lower bound on the nth prime. -/
lemma primeIndexLinearBound (c : ℕ) :
    ∃ K : ℕ, ∀ n : ℕ, c * n ≤ n.nth Nat.Prime + K := by
  have hlog := (tendsto_atTop.mp Real.tendsto_log_atTop)
    (max 1 ((c : ℝ) * (Real.log 4 + 1)))
  have hbound : ∀ᶠ x : ℝ in atTop, (c : ℝ) * (⌊x⌋₊.primeCounting : ℝ) ≤ x := by
    filter_upwards [Chebyshev.eventually_primeCounting_le (ε := 1) one_pos, hlog,
      eventually_ge_atTop (0 : ℝ)] with x hπ hxlog hx
    have hpos : 0 < Real.log x := zero_lt_one.trans_le ((le_max_left _ _).trans hxlog)
    calc
      _ ≤ (c : ℝ) * ((Real.log 4 + 1) * x / Real.log x) :=
        mul_le_mul_of_nonneg_left hπ (Nat.cast_nonneg c)
      _ = ((c : ℝ) * (Real.log 4 + 1)) * x / Real.log x := by ring
      _ ≤ x := (div_le_iff₀ hpos).2 <| by
        rw [mul_comm x]
        exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hxlog) hx
  obtain ⟨b, hb⟩ := eventually_atTop.mp hbound.natCast_atTop
  refine ⟨c * b.primeCounting', fun n ↦ ?_⟩
  let p := n.nth Nat.Prime
  have hp : p.primeCounting' = n := Nat.primeCounting'_nth_eq n
  by_cases hbp : b ≤ p
  · have hcp : c * p.primeCounting ≤ p := by
      have h := hb p hbp
      rw [Nat.floor_natCast] at h
      exact_mod_cast h
    have hn : n ≤ p.primeCounting := by
      rw [← hp]
      exact Nat.monotone_primeCounting' (Nat.le_succ p)
    exact (Nat.mul_le_mul_left c hn).trans (hcp.trans (Nat.le_add_right _ _))
  · have hn : n ≤ b.primeCounting' := by
      rw [← hp]
      exact Nat.monotone_primeCounting' (le_of_not_ge hbp)
    exact (Nat.mul_le_mul_left c hn).trans (Nat.le_add_left _ _)

lemma integerSequence_first_minimum (g : ℕ → ℤ) (K : ℤ) (hK : ∀ n, K ≤ g n) :
    ∃ n, (∀ m, g n ≤ g m) ∧ ∀ m < n, g n < g m := by
  classical
  obtain ⟨z, hz, hzmin⟩ := Int.exists_least_of_bdd (P := fun z => ∃ n, g n = z)
    ⟨K, by rintro _ ⟨n, rfl⟩; exact hK n⟩ ⟨g 0, 0, rfl⟩
  let n := Nat.find hz
  have hn : g n = z := Nat.find_spec hz
  refine ⟨n, ?_, ?_⟩
  · intro m
    rw [hn]
    exact hzmin _ ⟨m, rfl⟩
  · intro m hm
    rw [hn]
    exact lt_of_le_of_ne (hzmin _ ⟨m, rfl⟩) (Ne.symm (Nat.find_min hz hm))

lemma nth_prime_odd_of_pos {n : ℕ} (hn : 0 < n) : Odd (n.nth Nat.Prime) := by
  apply (Nat.prime_nth_prime n).odd_of_ne_two
  have := Nat.add_two_le_nth_prime n
  omega

end OMA

theorem OMA.solution : type_of% @Erdos454.erdos_454.variants.two_le_limsup := by
  classical
  have hpred : (Prime : ℕ → Prop) = Nat.Prime :=
    funext fun _ => propext Nat.prime_iff.symm
  simp only [hpred]
  apply le_limsup_of_frequently_le'
  refine frequently_atTop.mpr fun N => ?_
  let M := max N 1
  let k := M + 1
  let c := k.nth Nat.Prime + 1
  let g (n : ℕ) : ℤ := (n.nth Nat.Prime : ℤ) - (c : ℤ) * (n : ℤ)
  obtain ⟨K, hK⟩ := OMA.primeIndexLinearBound c
  have hbounded (j : ℕ) : -(K : ℤ) ≤ g j := by
    have hj : (c : ℤ) * (j : ℤ) ≤ (j.nth Nat.Prime : ℤ) + (K : ℤ) := by
      exact_mod_cast hK j
    dsimp only [g]
    linarith only [hj]
  obtain ⟨n, hmin, hfirst⟩ := OMA.integerSequence_first_minimum g (-(K : ℤ)) hbounded
  have hnM : M < n := by
    by_contra h
    have hn : n ≤ M := by omega
    have hnk : (n : ℤ) + 1 ≤ (k : ℤ) := by
      exact_mod_cast (show n + 1 ≤ k from Nat.add_le_add_right hn 1)
    have hmul := mul_le_mul_of_nonneg_left hnk (Int.natCast_nonneg c)
    have hpk : (k.nth Nat.Prime : ℤ) + 1 = (c : ℤ) := by simp [c]
    have hn0 := Int.natCast_nonneg (n.nth Nat.Prime)
    have hnk' := hmin k
    dsimp only [g] at hnk'
    linarith only [hmul, hpk, hn0, hnk']
  have hn1 : 1 < n := lt_of_le_of_lt (le_max_right _ _) hnM
  have hnN : N ≤ n := (le_max_left _ _).trans hnM.le
  refine ⟨n, hnN, ?_⟩
  have hFn : 2 * n.nth Nat.Prime + 2 ≤ Erdos454.f n := by
    unfold Erdos454.f
    simp only [hpred, if_neg (not_le_of_gt hn1)]
    have : Nonempty {i : Fin n // 0 < (i : ℕ)} := ⟨⟨⟨1, hn1⟩, Nat.zero_lt_succ _⟩⟩
    apply le_ciInf
    intro i
    let j : ℕ := i.1
    have hjpos : 0 < j := i.2
    have hjlt : j < n := i.1.isLt
    change 2 * n.nth Nat.Prime + 2 ≤ (n + j).nth Nat.Prime + (n - j).nth Nat.Prime
    have hminus := hfirst (n - j) (by omega)
    have hplus := hmin (n + j)
    dsimp only [g] at hminus hplus
    rw [Int.natCast_sub (by omega : j ≤ n)] at hminus
    push_cast at hplus
    have hstrictI : (2 : ℤ) * (n.nth Nat.Prime : ℤ) <
        ((n + j).nth Nat.Prime : ℤ) + ((n - j).nth Nat.Prime : ℤ) := by
      linarith only [hminus, hplus]
    have hstrict : 2 * n.nth Nat.Prime <
        (n + j).nth Nat.Prime + (n - j).nth Nat.Prime := by exact_mod_cast hstrictI
    have hoddl := OMA.nth_prime_odd_of_pos (show 0 < n + j by omega)
    have hoddr := OMA.nth_prime_odd_of_pos (show 0 < n - j by omega)
    obtain ⟨q, hq⟩ := hoddl.add_odd hoddr
    omega
  have hFn' : (2 : ℕ∞) * (n.nth Nat.Prime : ℕ∞) + 2 ≤ (Erdos454.f n : ℕ∞) := by
    exact_mod_cast hFn
  have hfinite : (2 : ℕ∞) * (n.nth Nat.Prime : ℕ∞) ≠ ⊤ := by
    change ((2 * n.nth Nat.Prime : ℕ) : ℕ∞) ≠ ⊤
    exact ENat.natCast_ne_top _
  exact ENat.le_sub_of_add_le_left hfinite hFn'
