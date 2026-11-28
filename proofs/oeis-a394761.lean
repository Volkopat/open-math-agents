import OMAStatements.S_oeis_a394761
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.NatDivisors

open OMA.S_oeis_a394761

namespace OMA.S_oeis_a394761.Proof

private theorem odd_of_gcd_one (s n : ℕ)
    (hg : Nat.gcd s n = 1) (hn : n % 2 = 0) : s % 2 = 1 := by
  by_contra hs
  have hs0 : s % 2 = 0 := by omega
  have hdiv : 2 ∣ Nat.gcd s n :=
    Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hs0) (Nat.dvd_of_mod_eq_zero hn)
  rw [hg] at hdiv
  norm_num at hdiv

private theorem no_four (s n : ℕ)
    (h0 : Nat.gcd s n = 1)
    (h1 : Nat.gcd (s + n) (n + 1) = 1)
    (h2 : Nat.gcd (s + n + (n + 1)) (n + 2) = 1)
    (h3 : Nat.gcd (s + n + (n + 1) + (n + 2)) (n + 3) = 1) : False := by
  by_cases hn : n % 2 = 0
  · have hs := odd_of_gcd_one s n h0 hn
    have hs2 := odd_of_gcd_one _ _ h2 (by omega)
    omega
  · have hs1 := odd_of_gcd_one _ _ h1 (by omega)
    have hs3 := odd_of_gcd_one _ _ h3 (by omega)
    omega

private theorem add_step (n : ℕ) (h : gcdAt n = 1) :
    state (n + 1) = state n + (n + 1) := by
  unfold gcdAt at h
  simp only [state, if_pos h]

private theorem reset_step (n : ℕ) (h : gcdAt n ≠ 1) :
    state (n + 1) = (n + 1) / gcdAt n := by
  unfold gcdAt at h ⊢
  simp only [state, if_neg h]

private def Good (n : ℕ) : Prop :=
  state n ∣ n ∧ 2 ≤ state n ∧ 2 * state n ≤ n ∧
    (n % 2 = 1 → state n ≠ 3)

private theorem division (d m : ℕ) (hd : d ∣ m) :
    m = (m / d) * d := by
  exact (Nat.div_mul_cancel hd).symm

private theorem step_congr (q n g pred c : ℕ) (hg0 : g ∣ pred) (hg1 : g ∣ n)
    (j : ℕ) (he : pred + c = q + j * n) : q % g = c % g := by
  have h := congrArg (· % g) he
  rw [Nat.add_mod pred c, Nat.mod_eq_zero_of_dvd hg0, Nat.zero_add, Nat.mod_mod] at h
  rw [Nat.add_mod q (j * n), Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hg1 j),
    Nat.add_zero, Nat.mod_mod] at h
  exact h.symm

private theorem require_two (n : ℕ) (h : Good n) :
    gcdAt n = 1 := by
  unfold gcdAt
  have hh : Nat.gcd (state n) (n + 1) ∣ 1 := by
    have hd := Nat.gcd_dvd_left (state n) (n + 1)
    have hn := dvd_trans hd h.1
    simpa only [Nat.add_sub_cancel_left] using
      Nat.dvd_sub (Nat.gcd_dvd_right (state n) (n + 1)) hn
  exact Nat.dvd_one.mp hh

private theorem bound_three (q n : ℕ) (hd : q ∣ n) (h : 2 * q ≤ n)
    (hq : 2 ≤ q) (hnOdd : n % 2 = 1) : 3 * q ≤ n := by
  obtain ⟨k, hk⟩ := hd
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hh : k ≤ 1 := by omega
    interval_cases k <;> simp_all <;> omega
  have hkOdd : k % 2 = 1 := by
    rw [hk, Nat.mul_mod] at hnOdd
    have h0 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h0 with he | he
    · simp [he] at hnOdd
    · exact he
  rw [hk]
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left q (show 3 ≤ k by omega)

private theorem three_excluded (q n j g c : ℕ) (hn : 27 ≤ n) (hq : 2 ≤ q)
    (hqle : 2 * q ≤ n) (hd : q ∣ n) (hod : n % 2 = 1 → q ≠ 3)
    (hj : (j = 2 ∧ c = 1) ∨ (j = 3 ∧ c = 3) ∨ (j = 4 ∧ c = 6))
    (hmod : q % g = c % g) (hnEq : n + j = 3 * g)
    (hOdd : (n + j) % 2 = 1) (hprior : j = 3 → q ≠ 3) : False := by
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hh := bound_three q n hd hqle hq (by omega)
    rw [Nat.mod_eq_of_lt (show q < g by omega), Nat.mod_eq_of_lt (show 1 < g by omega)] at hmod
    omega
  · rw [Nat.mod_eq_of_lt (show 3 < g by omega)] at hmod
    have hgPos : 0 < g := by omega
    have hqBound : q < 2 * g := by omega
    have hk : q / g < 2 := (Nat.div_lt_iff_lt_mul hgPos).2 (by simpa [Nat.mul_comm] using hqBound)
    have hq' := Nat.mod_add_div q g
    rw [hmod] at hq'
    have two_cases (x : ℕ) (hx : x < 2) : x = 0 ∨ x = 1 := by omega
    have hor := two_cases _ hk
    rcases hor with he | he
    · have : q = 3 := by simpa [he] using hq'.symm
      exact hprior rfl this
    · have heq : q = g + 3 := by simpa [he, Nat.add_comm] using hq'.symm
      obtain ⟨k, hkN⟩ := hd
      have hklt : k < 3 := by
        by_contra hh
        have hh' := Nat.mul_le_mul_left q (show 3 ≤ k by omega)
        omega
      interval_cases k <;> simp_all <;> omega
  · have hh := bound_three q n hd hqle hq (by omega)
    rw [Nat.mod_eq_of_lt (show q < g by omega), Nat.mod_eq_of_lt (show 6 < g by omega)] at hmod
    subst q
    obtain ⟨k, hk⟩ := hd
    omega

private theorem good_reset (n j : ℕ) (hn : 27 ≤ n) (h : Good n)
    (hjMin : 2 ≤ j) (hjMax : j ≤ 4) (hg : gcdAt (n + j - 1) ≠ 1)
    (hcopy : ∀ t < j - 1, gcdAt (n + t) = 1) :
    Good (n + j) := by
  let q := state n
  let m := n + j
  let g := gcdAt (m - 1)
  obtain ⟨hqD, hqMin, hqMax, hqOdd⟩ := h
  change q ∣ n at hqD
  change 2 ≤ q at hqMin
  change 2 * q ≤ n at hqMax
  change n % 2 = 1 → q ≠ 3 at hqOdd
  have hstep : state m = m / g := by
    simpa only [g, Nat.sub_add_cancel (show 1 ≤ m by dsimp [m]; omega)] using
      reset_step (m - 1) hg
  have hgcd : g = Nat.gcd (state (m - 1)) m := by
    unfold g gcdAt
    rw [Nat.sub_add_cancel (show 1 ≤ m by dsimp [m]; omega)]
  have hgD : g ∣ m := hgcd ▸ Nat.gcd_dvd_right _ _
  have hg0 : 0 < g := hgcd ▸ Nat.gcd_pos_of_pos_right _ (by dsimp [m]; omega)
  have hg2 : 2 ≤ g := by change g ≠ 1 at hg; omega
  have hmul : m = (m / g) * g := division g m hgD
  have hbound : 2 * (m / g) ≤ m := by
    have hh := Nat.mul_le_mul_left (m / g) hg2
    omega
  have hA : state (n + 1) = q + (n + 1) := add_step n (hcopy 0 (by omega))
  have hB (hJ : 3 ≤ j) : state (n + 2) = q + (n + 1) + (n + 2) := by
    rw [show n + 2 = (n + 1) + 1 from rfl, add_step _ (hcopy 1 (by omega)), hA]
  have hC (hJ : 4 ≤ j) : state (n + 3) = q + (n + 1) + (n + 2) + (n + 3) := by
    rw [show n + 3 = (n + 2) + 1 from rfl, add_step _ (hcopy 2 (by omega)), hB (by omega)]
  have hprior : j = 3 → q ≠ 3 := by
    intro hj hq
    by_cases hnOdd : n % 2 = 1
    · exact hqOdd hnOdd hq
    · have hcop := hcopy 1 (by omega)
      unfold gcdAt at hcop
      rw [hA, hq] at hcop
      have hf : 2 ∣ Nat.gcd (3 + (n + 1)) (n + 1 + 1) := Nat.dvd_gcd
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega))
      rw [hcop] at hf
      norm_num at hf
  have hprior6 : j = 4 → q ≠ 6 := by
    intro hj hq
    have hnd : 6 ∣ n := hq ▸ hqD
    have hnm := Nat.mod_eq_zero_of_dvd hnd
    have hcop := hcopy 2 (by omega)
    unfold gcdAt at hcop
    rw [hB (by omega), hq] at hcop
    have hf : 3 ∣ Nat.gcd (6 + (n + 1) + (n + 2)) (n + 2 + 1) := Nat.dvd_gcd
      (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hcop] at hf
    norm_num at hf
  have hgPred : g ∣ state (m - 1) := hgcd ▸ Nat.gcd_dvd_left _ _
  let c := j * (j - 1) / 2
  have hcases : (j = 2 ∧ c = 1) ∨ (j = 3 ∧ c = 3) ∨ (j = 4 ∧ c = 6) := by
    dsimp [c]
    interval_cases j <;> decide
  have hmod : q % g = c % g := by
    apply step_congr _ _ _ _ _ hgPred hgD (j - 1)
    rcases hcases with ⟨hj, hc⟩ | ⟨hj, hc⟩ | ⟨hj, hc⟩
    · rw [show m - 1 = n + 1 by dsimp [m]; omega, hA, hj, hc]
      dsimp [m]
      omega
    · rw [show m - 1 = n + 2 by dsimp [m]; omega, hB (by omega), hj, hc]
      dsimp [m]
      omega
    · rw [show m - 1 = n + 3 by dsimp [m]; omega, hC (by omega), hj, hc]
      dsimp [m]
      omega
  have hmin : 2 ≤ m / g := by
    by_contra hc
    have hOne : m / g = 1 := by
      have hn' : 0 < m := by dsimp [m]; omega
      by_contra hne
      have hz : m / g = 0 := by omega
      simp [hz] at hmul
      omega
    have hgm : g = m := by simpa [hOne] using hmul.symm
    have hcl : c < g := by dsimp [m] at hgm; rcases hcases with h' | h' | h' <;> omega
    have hql : q < g := by dsimp [m] at hgm; omega
    rw [Nat.mod_eq_of_lt hql, Nat.mod_eq_of_lt hcl] at hmod
    rcases hcases with ⟨_, hc⟩ | ⟨hj, hc⟩ | ⟨hj, hc⟩
    · omega
    · exact hprior hj (hmod.trans hc)
    · exact hprior6 hj (hmod.trans hc)
  change Good m
  unfold Good
  rw [hstep]
  refine ⟨⟨g, hmul⟩, hmin, hbound, ?_⟩
  intro hodd heq
  apply three_excluded q n j g c hn hqMin hqMax hqD hqOdd hcases hmod _ hodd hprior
  rw [heq] at hmul
  exact hmul

private theorem current (m : ℕ) (hm : 27 ≤ m) :
    ∃ k ≤ 3, k ≤ m - 27 ∧ Good (m - k) ∧ ∀ j < k, gcdAt (m - k + j) = 1 := by
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨0, by decide, by decide, ?_, by omega⟩
    unfold Good
    decide +kernel
  | succ m hm ih =>
    obtain ⟨k, hk, hk', hgood, hcopy⟩ := ih
    let t := m - k
    have ht : t + k = m := by dsimp [t]; omega
    by_cases hcop : gcdAt m = 1
    · have hlt : k < 3 := by
        by_contra hge
        have he : k = 3 := by omega
        have h0 : gcdAt t = 1 := by simpa [t] using hcopy 0 (by omega)
        have h1 := hcopy 1 (by omega)
        have h2 := hcopy 2 (by omega)
        have h3 : gcdAt (t + 3) = 1 := by simpa only [← he, ht] using hcop
        have ha := add_step t h0
        have hb := add_step (t + 1) h1
        have hc := add_step (t + 2) h2
        change gcdAt (t + 1) = 1 at h1
        change gcdAt (t + 2) = 1 at h2
        change state (t + 2) = _ at hb
        change state (t + 3) = _ at hc
        unfold gcdAt at h0 h1 h2 h3
        rw [ha] at h1
        rw [hb, ha] at h2
        rw [hc, hb, ha] at h3
        apply no_four _ _ h0
        · exact h1
        · exact h2
        · exact h3
      have he : m + 1 - (k + 1) = t := by dsimp [t]; omega
      refine ⟨k + 1, by omega, by omega, ?_, ?_⟩
      · rw [he]
        exact hgood
      · intro j hj
        rw [he]
        by_cases hjk : j < k
        · exact hcopy j hjk
        · have hEq : j = k := by omega
          rw [hEq, ht]
          exact hcop
    · have hk0 : 0 < k := by
        by_contra hh
        have he : k = 0 := by omega
        simp only [he, Nat.sub_zero] at hgood
        exact hcop (require_two _ hgood)
      have hnext := good_reset t (k + 1) (by dsimp [t]; omega) hgood
        (by omega) (by omega) (by simpa only [show t + (k + 1) - 1 = m by omega] using hcop) (by simpa using hcopy)
      have he' : t + (k + 1) = m + 1 := by omega
      rw [he'] at hnext
      exact ⟨0, by omega, by omega, by simpa only [Nat.sub_zero] using hnext, by omega⟩

private def advance (start initial : ℕ) : ℕ → ℕ
  | 0 => initial
  | n + 1 =>
    let s := advance start initial n
    let i := start + n + 1
    let g := Nat.gcd s i
    if g = 1 then s + i else i / g

private theorem state_advance (start steps : ℕ) :
    state (start + steps) = advance start (state start) steps := by
  induction steps with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ, state, advance, ih]

private def tinyDivisors : Fin 4 → Finset ℕ
  | 0 => {1, 43, 454303, 19535029}
  | 1 => {1, 2, 3, 4, 6, 12, 1627919, 3255838, 4883757, 6511676, 9767514, 19535028}
  | 2 => {1, 23, 849349, 19535027}
  | 3 => {1, 2, 7, 14, 49, 98, 199337, 398674, 1395359, 2790718, 9767513, 19535026}

private theorem divisor_lists (k : Fin 4) : Nat.divisors (19535029 - k.val) = tinyDivisors k := by
  fin_cases k
  · change Nat.divisors 19535029 = _
    rw [show 19535029 = 43 * 454303 by decide, Nat.divisors_mul, (show Nat.Prime 43 by norm_num).divisors,
      (show Nat.Prime 454303 by norm_num).divisors]
    decide +kernel
  · change Nat.divisors 19535028 = _
    rw [show 19535028 = 2 ^ 2 * 3 * 1627919 by decide, Nat.divisors_mul, Nat.divisors_mul,
      Nat.divisors_prime_pow Nat.prime_two, (show Nat.Prime 3 by norm_num).divisors,
      (show Nat.Prime 1627919 by norm_num).divisors]
    decide +kernel
  · change Nat.divisors 19535027 = _
    rw [show 19535027 = 23 * 849349 by decide, Nat.divisors_mul, (show Nat.Prime 23 by norm_num).divisors,
      (show Nat.Prime 849349 by norm_num).divisors]
    decide +kernel
  · change Nat.divisors 19535026 = _
    rw [show 19535026 = 2 * 7 ^ 2 * 199337 by decide, Nat.divisors_mul, Nat.divisors_mul,
      Nat.prime_two.divisors, Nat.divisors_prime_pow (show Nat.Prime 7 by norm_num),
      (show Nat.Prime 199337 by norm_num).divisors]
    decide +kernel

private theorem advanced_additions (n k : ℕ) (hk : k ≤ 3) (hn : k ≤ n)
    (h : ∀ j < k, gcdAt (n - k + j) = 1) :
    state n = state (n - k) + (k * n - k * (k - 1) / 2) := by
  interval_cases k
  · simp
  · have ha := add_step (n - 1) (by simpa using h 0 (by decide))
    rw [Nat.sub_add_cancel (by omega)] at ha
    simpa using ha
  · have ha := add_step (n - 2) (by simpa using h 0 (by decide))
    have hb := add_step (n - 2 + 1) (h 1 (by decide))
    have hEq : n - 2 + 1 + 1 = n := by omega
    rw [hEq, ha] at hb
    rw [hb]
    omega
  · have ha := add_step (n - 3) (by simpa using h 0 (by decide))
    have hb := add_step (n - 3 + 1) (h 1 (by decide))
    have hc := add_step (n - 3 + 2) (h 2 (by decide))
    have hEq : n - 3 + 2 + 1 = n := by omega
    rw [hEq] at hc
    change state (n - 3 + 2) = _ at hb
    rw [hb, ha] at hc
    rw [hc]
    omega

set_option maxRecDepth 6000 in
set_option maxHeartbeats 6000000 in
private theorem all_candidates :
    ∀ k : Fin 4, ∀ q ∈ tinyDivisors k, 2 ≤ q → 2 * q ≤ 19535029 - k.val →
      ((19535029 - k.val) % 2 = 1 → q ≠ 3) →
      advance 19535029 (q + (k.val * 19535029 - k.val * (k.val - 1) / 2)) 14 = 6511681 := by
  decide +kernel

private theorem anchor : state 19535043 = 6511681 := by
  obtain ⟨k, hk, hkBefore, hGood, hCopy⟩ := current 19535029 (by decide)
  obtain ⟨hDvd, hMin, hMax, hOdd⟩ := hGood
  have hMem : state (19535029 - k) ∈ tinyDivisors ⟨k, by omega⟩ := by
    rw [← divisor_lists]
    exact Nat.mem_divisors.mpr ⟨hDvd, by omega⟩
  have hAdvance := all_candidates ⟨k, by omega⟩ _ hMem hMin hMax hOdd
  change state (19535029 + 14) = _
  rw [state_advance, advanced_additions _ _ hk (by omega) hCopy]
  exact hAdvance

private theorem tailGcd (t : ℕ) :
    gcdAt (19535043 + t) = Nat.gcd (advance 19535043 6511681 t) (19535043 + t + 1) := by
  rw [gcdAt, state_advance, anchor]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 6000000 in
private theorem alternating :
    ∀ j : Fin 9,
      Nat.gcd (advance 19535043 6511681 (26 + 2 * j.val)) (19535043 + (26 + 2 * j.val) + 1) ≠ 1 ∧
      Nat.gcd (advance 19535043 6511681 (27 + 2 * j.val)) (19535043 + (27 + 2 * j.val) + 1) = 1 ∧
      Nat.gcd (advance 19535043 6511681 (28 + 2 * j.val)) (19535043 + (28 + 2 * j.val) + 1) ≠ 1 := by
  decide +kernel

end OMA.S_oeis_a394761.Proof

open OMA.S_oeis_a394761.Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a394761.main) := by
  intro h
  apply (h 19535070).1
  intro j hj
  have ha := alternating ⟨j, hj⟩
  refine ⟨by decide, Or.inr ?_, ?_, ?_⟩
  · rw [show 19535070 + j * (1 + 1) - 1 = 19535043 + (26 + 2 * j) by omega, tailGcd]
    exact ha.1
  · intro i hi
    have h0 : i = 0 := by omega
    rw [show 19535070 + j * (1 + 1) + i = 19535043 + (27 + 2 * j) by omega, tailGcd]
    exact ha.2.1
  · rw [show 19535070 + j * (1 + 1) + 1 = 19535043 + (28 + 2 * j) by omega, tailGcd]
    exact ha.2.2
