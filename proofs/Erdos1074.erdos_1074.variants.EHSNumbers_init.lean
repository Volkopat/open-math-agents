import FormalConjectures.ErdosProblems.«1074»

-- Problem: Erdős Problem 1074 — EHSNumbers init
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1074.lean:122 (declaration Erdos1074.erdos_1074.variants.EHSNumbers_init)
-- Credit: @Slayzkami (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA.E1074

open Nat Erdos1074

lemma two (m q r a b : ℕ) (hq : q.Prime := by norm_num) (hr : r.Prime := by norm_num)
    (h : m ! + 1 = q ^ a * r ^ b := by norm_num [Nat.factorial])
    (e : q % m = 1 % m := by norm_num) (f : r % m = 1 % m := by norm_num) : m ∉ EHSNumbers := by
  rintro ⟨-, p, hp, hne, hd⟩
  rw [h] at hd
  rcases hp.dvd_mul.1 hd with d | d
  · exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow d) ▸ e)
  · exact hne ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow d) ▸ f)

lemma mem_of (m p : ℕ) (hm : 1 ≤ m := by norm_num) (hp : p.Prime := by norm_num)
    (hne : p % m ≠ 1 % m := by norm_num) (hd : p ∣ m ! + 1 := by norm_num [Nat.factorial]) :
    m ∈ EHSNumbers := ⟨hm, p, hp, hne, hd⟩

lemma n0 : 0 ∉ EHSNumbers := fun h => absurd h.1 (by norm_num)
lemma n1 : 1 ∉ EHSNumbers := two 1 2 2 1 0
lemma n2 : 2 ∉ EHSNumbers := two 2 3 3 1 0
lemma n3 : 3 ∉ EHSNumbers := two 3 7 7 1 0
lemma n4 : 4 ∉ EHSNumbers := two 4 5 5 2 0
lemma n5 : 5 ∉ EHSNumbers := two 5 11 11 2 0
lemma n6 : 6 ∉ EHSNumbers := two 6 7 103 1 1
lemma n7 : 7 ∉ EHSNumbers := two 7 71 71 2 0
lemma n10 : 10 ∉ EHSNumbers := two 10 11 329891 1 1
lemma n11 : 11 ∉ EHSNumbers := two 11 39916801 39916801 1 0
lemma n12 : 12 ∉ EHSNumbers := two 12 13 2834329 2 1

lemma m8 : 8 ∈ EHSNumbers := mem_of 8 61
lemma m9 : 9 ∈ EHSNumbers := mem_of 9 71
lemma m13 : 13 ∈ EHSNumbers := mem_of 13 83
lemma m14 : 14 ∈ EHSNumbers := mem_of 14 23
lemma m15 : 15 ∈ EHSNumbers := mem_of 15 59
lemma m16 : 16 ∈ EHSNumbers := mem_of 16 61
lemma m17 : 17 ∈ EHSNumbers := mem_of 17 661

def P : ℕ → Prop := fun n => n ∈ EHSNumbers

lemma counts [DecidablePred P] : count P 8 = 0 ∧ count P 9 = 1 ∧ count P 13 = 2 ∧
    count P 14 = 3 ∧ count P 15 = 4 ∧ count P 16 = 5 ∧ count P 17 = 6 := by
  simp only [Nat.count_succ, P, n0, n1, n2, n3, n4, n5, n6, n7, m8, m9,
    n10, n11, n12, m13, m14, m15, m16]
  norm_num

end OMA.E1074

open OMA.E1074 in
theorem OMA.solution : type_of% @Erdos1074.erdos_1074.variants.EHSNumbers_init := by
  classical
  obtain ⟨c8, c9, c13, c14, c15, c16, c17⟩ := counts
  have h0 : Nat.nth P 0 = 8 := c8 ▸ Nat.nth_count (p := P) m8
  have h1 : Nat.nth P 1 = 9 := c9 ▸ Nat.nth_count (p := P) m9
  have h2 : Nat.nth P 2 = 13 := c13 ▸ Nat.nth_count (p := P) m13
  have h3 : Nat.nth P 3 = 14 := c14 ▸ Nat.nth_count (p := P) m14
  have h4 : Nat.nth P 4 = 15 := c15 ▸ Nat.nth_count (p := P) m15
  have h5 : Nat.nth P 5 = 16 := c16 ▸ Nat.nth_count (p := P) m16
  have h6 : Nat.nth P 6 = 17 := c17 ▸ Nat.nth_count (p := P) m17
  change Nat.nth P '' Set.Icc 0 6 = _
  have hI : Set.Icc 0 6 = ({0, 1, 2, 3, 4, 5, 6} : Set ℕ) := by
    ext i
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [hI]
  simp [Set.image_insert_eq, h0, h1, h2, h3, h4, h5, h6]
