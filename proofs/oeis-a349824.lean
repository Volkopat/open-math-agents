import OMAStatements.S_oeis_a349824
import Mathlib

/-!
# OEIS A349824: every n reaches a prime, 0, 27, 30, 28 or 33 under n -> Omega(n)*sopfr(n), and those are fixed points or the loop (28, 33)

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Write F for the map and k = Omega(n). (1) For prime factors p_1..p_k of n: sum p_i <= n/2^(k-1) +
2(k-1) (induction on k using (p-2)(t-1) >= 0), and F(n)/n <= k^2/2^(k-1). (2) For composite n >=
256: if k >= 3 these give F(n) <= 4n/5; if k = 2 with both primes >= 3 then p + q <= n/3 + 3 and
F(n) <= 2n/3 + 6 <= 4n/5. (3) The remaining case n = 2p (p > 3 prime): F(n) = n + 4 = 2(p+2); if p+2
is composite, x = n+4 has at least three prime factors; otherwise p+4 is composite (one of p, p+2,
p+4 is divisible by 3), F(n+4) = n + 8 =: x; in both cases F(x) <= 4x/5 < n. So every composite n >=
256 reaches a smaller value within three steps, primes are fixed, and all n < 256 reach the target
set within 13 steps (finite check). Strong induction finishes.
-/

open OMA.S_oeis_a349824

namespace OMA.A349824Proof

lemma a_of_factorization (l : List ℕ) (hp : ∀ p ∈ l, p.Prime) :
    a l.prod = l.length * l.sum := by
  have h := Nat.primeFactorsList_unique rfl hp
  exact congrArg₂ (· * ·) h.length_eq.symm h.sum_eq.symm

lemma prime_fixed (p : ℕ) (hp : p.Prime) : a p = p := by
  simp [a, Nat.primeFactorsList_prime hp]

lemma prod_lower (l : List ℕ) (hp : ∀ p ∈ l, 2 ≤ p) :
    2 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have h₂ : 2 ≤ p := hp p (by simp)
    have ht : ∀ q ∈ l, 2 ≤ q := fun q hq => hp q (by simp [hq])
    simpa [pow_succ, mul_comm] using Nat.mul_le_mul h₂ (ih ht)

lemma sum_bound (l : List ℕ) (hp : ∀ p ∈ l, 2 ≤ p) :
    2 ^ l.length * l.sum + 2 * 2 ^ l.length ≤
      2 * l.prod + 2 * l.length * 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have h₂ : 2 ≤ p := hp p (by simp)
    have ht : ∀ q ∈ l, 2 ≤ q := fun q hq => hp q (by simp [hq])
    have hi := ih ht
    have hd := prod_lower l ht
    have hm : p * 2 ^ l.length + 2 * l.prod ≤
        p * l.prod + 2 * 2 ^ l.length := by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h₂
      nlinarith [Nat.mul_le_mul_left q hd]
    simp only [List.length_cons, List.sum_cons, List.prod_cons, pow_succ]
    nlinarith

lemma sum_bound_crude (l : List ℕ) (hp : ∀ p ∈ l, 2 ≤ p) :
    2 ^ l.length * l.sum ≤ 2 * l.length * l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have h₂ : 2 ≤ p := hp p (by simp)
    have ht : ∀ q ∈ l, 2 ≤ q := fun q hq => hp q (by simp [hq])
    have hi := ih ht
    have hd := Nat.mul_le_mul_left (2 * p) (prod_lower l ht)
    have hm := Nat.mul_le_mul_left (2 * l.length * l.prod) h₂
    simp only [List.length_cons, List.sum_cons, List.prod_cons, pow_succ]
    nlinarith

lemma exponential_bound (k : ℕ) (hk : 7 ≤ k) : 10 * k * k ≤ 4 * 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith

lemma contract_list (l : List ℕ) (hp : ∀ p ∈ l, 2 ≤ p)
    (hk : 3 ≤ l.length) (hn : 256 ≤ l.prod) :
    5 * (l.length * l.sum) ≤ 4 * l.prod := by
  have h₁ := sum_bound l hp
  have h₂ := sum_bound_crude l hp
  by_cases h : l.length < 7
  · interval_cases he : l.length <;> norm_num [he] at h₁ h₂ ⊢ <;> omega
  · have he := exponential_bound l.length (by omega)
    have hm := Nat.mul_le_mul_left (5 * l.length) h₂
    have ht := Nat.mul_le_mul_right l.prod he
    have hpos : 0 < 2 ^ l.length := by positivity
    nlinarith

lemma contract_or_twice_prime (n : ℕ) (hn : 256 ≤ n) (hnp : ¬ n.Prime) :
    5 * a n ≤ 4 * n ∨ ∃ p, p.Prime ∧ n = 2 * p := by
  have hprod := Nat.prod_primeFactorsList (show n ≠ 0 by omega)
  have hp : ∀ p ∈ n.primeFactorsList, p.Prime :=
    fun p h => Nat.prime_of_mem_primeFactorsList h
  have ha : a n = n.primeFactorsList.length * n.primeFactorsList.sum := rfl
  generalize he : n.primeFactorsList = l at hprod hp ha
  cases l with
  | nil => simp at hprod; omega
  | cons p l =>
    have hpp : p.Prime := hp p (by simp)
    cases l with
    | nil =>
      simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
      exact False.elim (hnp (hprod ▸ hpp))
    | cons q l =>
      have hqp : q.Prime := hp q (by simp)
      cases l with
      | nil =>
        simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
        by_cases hpe : p = 2
        · exact Or.inr ⟨q, hqp, by simpa [hpe] using hprod.symm⟩
        by_cases hqe : q = 2
        · exact Or.inr ⟨p, hpp, by simpa [hqe, mul_comm] using hprod.symm⟩
        have hp3 : 3 ≤ p := by have := hpp.two_le; omega
        have hq3 : 3 ≤ q := by have := hqp.two_le; omega
        have hs : 3 * (p + q) ≤ p * q + 9 := by
          obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hp3
          obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hq3
          nlinarith [Nat.zero_le (r * s)]
        left
        simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at ha
        nlinarith
      | cons r l =>
        left
        have hb := contract_list (p :: q :: r :: l)
          (fun x hx => (hp x hx).two_le) (by simp) (by omega)
        rw [ha, ← hprod]
        exact hb

lemma twice_prime (p : ℕ) (hp : p.Prime) : a (2 * p) = 2 * (p + 2) := by
  have h := a_of_factorization [2, p] (by simp [hp, Nat.prime_two])
  simpa [add_comm] using h

lemma twice_composite_contract (m : ℕ) (hm : 128 ≤ m) (hmp : ¬ m.Prime) :
    5 * a (2 * m) ≤ 4 * (2 * m) := by
  have hnp : ¬ (2 * m).Prime := by
    intro h
    have he := (h.dvd_iff_eq (by decide : 2 ≠ 1)).mp (dvd_mul_right 2 m)
    omega
  rcases contract_or_twice_prime (2 * m) (by omega) hnp with h | ⟨p, hp, he⟩
  · exact h
  · have : m = p := by omega
    exact False.elim (hmp (this ▸ hp))

lemma third_not_prime (p : ℕ) (hp3 : 3 < p) (hp : p.Prime)
    (hp2 : (p + 2).Prime) : ¬ (p + 4).Prime := by
  have h₀ : p % 3 ≠ 0 := by
    intro h
    have he := (hp.dvd_iff_eq (by decide : 3 ≠ 1)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have h₂ : (p + 2) % 3 ≠ 0 := by
    intro h
    have he := (hp2.dvd_iff_eq (by decide : 3 ≠ 1)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  intro hp4
  have hd : 3 ∣ p + 4 := Nat.dvd_of_mod_eq_zero (by omega)
  have he := (hp4.dvd_iff_eq (by decide : 3 ≠ 1)).mp hd
  omega

lemma large_descends (n : ℕ) (hn : 256 ≤ n) (hnp : ¬ n.Prime) :
    ∃ t, a^[t] n < n := by
  rcases contract_or_twice_prime n hn hnp with hc | ⟨p, hp, rfl⟩
  · refine ⟨1, ?_⟩
    simpa using (show a n < n by omega)
  · have hp128 : 128 ≤ p := by omega
    have h₁ := twice_prime p hp
    by_cases hp2 : (p + 2).Prime
    · have h₂ := twice_prime (p + 2) hp2
      have h₃ := twice_composite_contract (p + 4) (by omega)
        (third_not_prime p (by omega) hp hp2)
      refine ⟨3, ?_⟩
      change a (a (a (2 * p))) < 2 * p
      rw [h₁, h₂]
      have he : p + 2 + 2 = p + 4 := by omega
      rw [he]
      omega
    · have h₂ := twice_composite_contract (p + 2) (by omega) hp2
      refine ⟨2, ?_⟩
      change a (a (2 * p)) < 2 * p
      rw [h₁]
      omega


def target (n : ℕ) : Prop :=
  n.Prime ∨ n = 0 ∨ n = 27 ∨ n = 30 ∨ n = 28 ∨ n = 33

instance (n : ℕ) : Decidable (target n) := inferInstanceAs (Decidable
  (n.Prime ∨ n = 0 ∨ n = 27 ∨ n = 30 ∨ n = 28 ∨ n = 33))

def factorTable : List (List ℕ) := [
  [], [], [2], [3], [2, 2], [5], [2, 3], [7], [2, 2, 2], [3, 3],
  [2, 5], [11], [2, 2, 3], [13], [2, 7], [3, 5], [2, 2, 2, 2], [17], [2, 3, 3], [19],
  [2, 2, 5], [3, 7], [2, 11], [23], [2, 2, 2, 3], [5, 5], [2, 13], [3, 3, 3], [2, 2, 7], [29],
  [2, 3, 5], [31], [2, 2, 2, 2, 2], [3, 11], [2, 17], [5, 7], [2, 2, 3, 3], [37], [2, 19], [3, 13],
  [2, 2, 2, 5], [41], [2, 3, 7], [43], [2, 2, 11], [3, 3, 5], [2, 23], [47], [2, 2, 2, 2, 3], [7, 7],
  [2, 5, 5], [3, 17], [2, 2, 13], [53], [2, 3, 3, 3], [5, 11], [2, 2, 2, 7], [3, 19], [2, 29], [59],
  [2, 2, 3, 5], [61], [2, 31], [3, 3, 7], [2, 2, 2, 2, 2, 2], [5, 13], [2, 3, 11], [67], [2, 2, 17], [3, 23],
  [2, 5, 7], [71], [2, 2, 2, 3, 3], [73], [2, 37], [3, 5, 5], [2, 2, 19], [7, 11], [2, 3, 13], [79],
  [2, 2, 2, 2, 5], [3, 3, 3, 3], [2, 41], [83], [2, 2, 3, 7], [5, 17], [2, 43], [3, 29], [2, 2, 2, 11], [89],
  [2, 3, 3, 5], [7, 13], [2, 2, 23], [3, 31], [2, 47], [5, 19], [2, 2, 2, 2, 2, 3], [97], [2, 7, 7], [3, 3, 11],
  [2, 2, 5, 5], [101], [2, 3, 17], [103], [2, 2, 2, 13], [3, 5, 7], [2, 53], [107], [2, 2, 3, 3, 3], [109],
  [2, 5, 11], [3, 37], [2, 2, 2, 2, 7], [113], [2, 3, 19], [5, 23], [2, 2, 29], [3, 3, 13], [2, 59], [7, 17],
  [2, 2, 2, 3, 5], [11, 11], [2, 61], [3, 41], [2, 2, 31], [5, 5, 5], [2, 3, 3, 7], [127], [2, 2, 2, 2, 2, 2, 2], [3, 43],
  [2, 5, 13], [131], [2, 2, 3, 11], [7, 19], [2, 67], [3, 3, 3, 5], [2, 2, 2, 17], [137], [2, 3, 23], [139],
  [2, 2, 5, 7], [3, 47], [2, 71], [11, 13], [2, 2, 2, 2, 3, 3], [5, 29], [2, 73], [3, 7, 7], [2, 2, 37], [149],
  [2, 3, 5, 5], [151], [2, 2, 2, 19], [3, 3, 17], [2, 7, 11], [5, 31], [2, 2, 3, 13], [157], [2, 79], [3, 53],
  [2, 2, 2, 2, 2, 5], [7, 23], [2, 3, 3, 3, 3], [163], [2, 2, 41], [3, 5, 11], [2, 83], [167], [2, 2, 2, 3, 7], [13, 13],
  [2, 5, 17], [3, 3, 19], [2, 2, 43], [173], [2, 3, 29], [5, 5, 7], [2, 2, 2, 2, 11], [3, 59], [2, 89], [179],
  [2, 2, 3, 3, 5], [181], [2, 7, 13], [3, 61], [2, 2, 2, 23], [5, 37], [2, 3, 31], [11, 17], [2, 2, 47], [3, 3, 3, 7],
  [2, 5, 19], [191], [2, 2, 2, 2, 2, 2, 3], [193], [2, 97], [3, 5, 13], [2, 2, 7, 7], [197], [2, 3, 3, 11], [199],
  [2, 2, 2, 5, 5], [3, 67], [2, 101], [7, 29], [2, 2, 3, 17], [5, 41], [2, 103], [3, 3, 23], [2, 2, 2, 2, 13], [11, 19],
  [2, 3, 5, 7], [211], [2, 2, 53], [3, 71], [2, 107], [5, 43], [2, 2, 2, 3, 3, 3], [7, 31], [2, 109], [3, 73],
  [2, 2, 5, 11], [13, 17], [2, 3, 37], [223], [2, 2, 2, 2, 2, 7], [3, 3, 5, 5], [2, 113], [227], [2, 2, 3, 19], [229],
  [2, 5, 23], [3, 7, 11], [2, 2, 2, 29], [233], [2, 3, 3, 13], [5, 47], [2, 2, 59], [3, 79], [2, 7, 17], [239],
  [2, 2, 2, 2, 3, 5], [241], [2, 11, 11], [3, 3, 3, 3, 3], [2, 2, 61], [5, 7, 7], [2, 3, 41], [13, 19], [2, 2, 2, 31], [3, 83],
  [2, 5, 5, 5], [251], [2, 2, 3, 3, 7], [11, 23], [2, 127], [3, 5, 17], [2, 2, 2, 2, 2, 2, 2, 2], [257], [2, 3, 43], [7, 37]]

def factors (n : ℕ) : List ℕ := factorTable[n]?.getD []

def step (n : ℕ) : ℕ := (factors n).length * (factors n).sum

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma table_correct : ∀ n : Fin 260, n.val ≠ 0 →
    (factors n.val).prod = n.val ∧ ∀ p ∈ factors n.val, p.Prime := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma table_closed : ∀ n : Fin 260, step n.val < 260 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma table_reaches : ∀ n : Fin 260, target (step^[13] n.val) := by
  decide +kernel

lemma step_eq (n : ℕ) (hn : n < 260) : step n = a n := by
  by_cases hz : n = 0
  · subst n
    have hs : step 0 = 0 := by decide +kernel
    rw [hs]
    simp [a]
  · obtain ⟨hprod, hp⟩ := table_correct ⟨n, hn⟩ hz
    have h := a_of_factorization (factors n) hp
    rw [hprod] at h
    exact h.symm

lemma iterate_step_eq (t n : ℕ) (hn : n < 260) :
    step^[t] n = a^[t] n ∧ step^[t] n < 260 := by
  induction t with
  | zero => simpa using hn
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨(step_eq _ ih.2).trans (congrArg a ih.1), table_closed ⟨_, ih.2⟩⟩

lemma small_reaches (n : ℕ) (hn : n < 256) : ∃ t, target (a^[t] n) := by
  have hb : n < 260 := by omega
  refine ⟨13, ?_⟩
  rw [← (iterate_step_eq 13 n hb).1]
  exact table_reaches ⟨n, hb⟩


lemma reaches (n : ℕ) : ∃ t, target (a^[t] n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 256
    · exact small_reaches n hn
    by_cases hp : n.Prime
    · exact ⟨0, Or.inl hp⟩
    obtain ⟨s, hs⟩ := large_descends n (by omega) hp
    obtain ⟨t, ht⟩ := ih (a^[s] n) hs
    refine ⟨t + s, ?_⟩
    simpa only [Function.iterate_add_apply] using ht

end OMA.A349824Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a349824.main := by
  constructor
  · refine ⟨OMA.A349824Proof.prime_fixed, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      rw [← OMA.A349824Proof.step_eq _ (by decide)]
      decide +kernel
  · exact OMA.A349824Proof.reaches

