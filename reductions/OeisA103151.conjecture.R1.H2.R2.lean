import OMAReductions.R_OeisA103151_conjecture_R1

-- Reduction of the 6k+5 case of the odd-prime Lemoine conjecture.
-- Credit: @Alewawa

namespace OMA.R_OeisA103151_conjecture_R1_H2_R2

open OeisA103151

/-- For 12k+5 the two remaining prime progressions are 6u+5 and 12v+7. -/
def H1 : Prop :=
  ∀ k : ℕ, 100000 < 6 * k + 2 →
    ¬ (12 * k - 1).Prime → ¬ (6 * k + 1).Prime →
    (∀ u v : ℕ, u + v + 1 = k → (u < 32 ∨ v < 32) →
      ¬ ((6 * u + 5).Prime ∧ (12 * v + 7).Prime)) →
    ∃ u v : ℕ, u + v + 1 = k ∧ 32 ≤ u ∧ 32 ≤ v ∧
      (6 * u + 5).Prime ∧ (12 * v + 7).Prime

/-- For 12k+11 the second prime progression is 12v+1. Here the undoubled
prime cannot equal three. -/
def H2 : Prop :=
  ∀ k : ℕ, 100000 < 6 * k + 5 →
    ¬ (12 * k + 5).Prime →
    (∀ u v : ℕ, u + v = k → (u < 32 ∨ v < 32) →
      ¬ ((6 * u + 5).Prime ∧ (12 * v + 1).Prime)) →
    ∃ u v : ℕ, u + v = k ∧ 32 ≤ u ∧ 32 ≤ v ∧
      (6 * u + 5).Prime ∧ (12 * v + 1).Prime

lemma count_pos_iff (n : ℕ) :
    1 ≤ a n ↔ ∃ p q : ℕ, p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ 2 * p + q = 2 * n + 1 := by
  unfold a
  rw [← Nat.lt_iff_add_one_le, Finset.card_pos]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨_, hpPrime, hpOdd, hpLe, hqPrime⟩ := Finset.mem_filter.mp hp
    exact ⟨p, 2 * n + 1 - 2 * p, hpPrime, hpOdd, hqPrime, by omega⟩
  · rintro ⟨p, q, hp, hpOdd, hq, hs⟩
    have hq2 := hq.two_le
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, hpOdd, by omega, ?_⟩⟩
    have hqeq : 2 * n + 1 - 2 * p = q := by omega
    simpa only [hqeq] using hq

private lemma prime_mod_six {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hodd := hp.eq_two_or_odd.resolve_left h2
  have hno : p % 3 ≠ 0 := by
    intro h
    have hd := (Nat.prime_def.mp hp).2 3 (Nat.dvd_of_mod_eq_zero h)
    exact h3 (hd.resolve_left (by decide)).symm
  omega

private lemma pair_mod_six {n p q : ℕ} (hn : n % 3 = 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hq : q.Prime) (hq3 : q ≠ 3)
    (hs : 2 * p + q = 2 * n + 1) : p % 6 = 5 ∧ q % 6 = 1 := by
  have hpmod := prime_mod_six hp hp2 hp3
  have hqmod := prime_mod_six hq (by omega) hq3
  omega

/-- Exact normalization of the even-index case, including both uses of three. -/
lemma even_index_iff (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ a (6 * k + 2) ↔ (12 * k - 1).Prime ∨ (6 * k + 1).Prime ∨
      ∃ u v : ℕ, u + v + 1 = k ∧ (6 * u + 5).Prime ∧ (12 * v + 7).Prime := by
  rw [count_pos_iff]
  constructor
  · rintro ⟨p, q, hp, hp2, hq, hs⟩
    by_cases hp3 : p = 3
    · exact Or.inl ((show q = 12 * k - 1 by omega) ▸ hq)
    by_cases hq3 : q = 3
    · exact Or.inr (Or.inl ((show p = 6 * k + 1 by omega) ▸ hp))
    obtain ⟨hpmod, _⟩ := pair_mod_six (by omega) hp hp2 hp3 hq hq3 hs
    have hqmod : q % 12 = 7 := by omega
    have hpEq : 6 * (p / 6) + 5 = p := by omega
    have hqEq : 12 * (q / 12) + 7 = q := by omega
    exact Or.inr (Or.inr ⟨p / 6, q / 12, by omega, hpEq.symm ▸ hp, hqEq.symm ▸ hq⟩)
  · rintro (hp | hq | ⟨u, v, huv, hp, hq⟩)
    · exact ⟨3, 12 * k - 1, Nat.prime_three, by decide, hp, by omega⟩
    · exact ⟨6 * k + 1, 3, hq, by omega, Nat.prime_three, by omega⟩
    · exact ⟨6 * u + 5, 12 * v + 7, hp, by omega, hq, by omega⟩

/-- In the odd-index case the use of three is possible only as the doubled prime. -/
lemma odd_index_iff (k : ℕ) :
    1 ≤ a (6 * k + 5) ↔ (12 * k + 5).Prime ∨
      ∃ u v : ℕ, u + v = k ∧ (6 * u + 5).Prime ∧ (12 * v + 1).Prime := by
  rw [count_pos_iff]
  constructor
  · rintro ⟨p, q, hp, hp2, hq, hs⟩
    by_cases hp3 : p = 3
    · exact Or.inl ((show q = 12 * k + 5 by omega) ▸ hq)
    have hq3 : q ≠ 3 := by
      have hpOdd := hp.eq_two_or_odd.resolve_left hp2
      omega
    obtain ⟨hpmod, _⟩ := pair_mod_six (by omega) hp hp2 hp3 hq hq3 hs
    have hqmod : q % 12 = 1 := by omega
    have hpEq : 6 * (p / 6) + 5 = p := by omega
    have hqEq : 12 * (q / 12) + 1 = q := by omega
    exact Or.inr ⟨p / 6, q / 12, by omega, hpEq.symm ▸ hp, hqEq.symm ▸ hq⟩
  · rintro (hq | ⟨u, v, huv, hp, hq⟩)
    · exact ⟨3, 12 * k + 5, Nat.prime_three, by decide, hq, by omega⟩
    · exact ⟨6 * u + 5, 12 * v + 1, hp, by omega, hq, by omega⟩

private lemma prime_of_factorial_gcd {q : ℕ} (hq : 2 ≤ q) (hupper : q < 450 * 450)
    (hcoprime : Nat.gcd q (Nat.factorial 450) = 1) : q.Prime := by
  refine Nat.prime_def_le_sqrt.mpr ⟨hq, ?_⟩
  intro d hd hs hdiv
  have hdmax := hs.trans (Nat.le_of_lt (Nat.sqrt_lt.mpr hupper))
  have hfac : d ∣ Nat.factorial 450 := Nat.dvd_factorial (by omega) hdmax
  have hone : d ∣ 1 := hcoprime ▸ Nat.dvd_gcd hdiv hfac
  have h := Nat.dvd_one.mp hone
  omega

set_option maxRecDepth 4096 in
private lemma factorial_value : Nat.factorial 450 = 17333687331126326593447131461045793996778112652090510155692075095553330016834367506046750882904387106145811284518424097858618583806301650208347296181351667570171918700422280962237272230663528084038062312369342674135036610101508838220494970929739011636793766165023730853896403901590836144149594432684204513784716402303182604094683993315061302563918385303341510606761462420205820006936352095967417183191538725617509521380556781309195429800229273803342553558164591996298912368598547771179158461351340068905647127658164836377126303774923360078072307462008554355068361448126606281145760960499187813428397924840592504537849487425060488481036571447957046788635742936714615176219148469743102979949740714485104716169664052397392602848408694007408998901127492905171514473431386633392492040661522692303043813960541966093224243809225137268851717904303214058238447936111678568236973036238404626507890688000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  rfl

private lemma candidates_prime :
    ([3, 5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89, 101, 107, 113, 131,
      137, 149, 167, 173, 179, 191, 197, 227, 233, 239, 251, 257, 263, 269, 281, 293] : List ℕ).all
      (fun p => decide (p.Prime ∧ p ≠ 2)) = true := by
  decide +kernel

private lemma checked_block {candidates : List ℕ}
    (valid : candidates.all (fun p => decide (p.Prime ∧ p ≠ 2)) = true)
    (start width : ℕ) (hbound : start + width ≤ 33332)
    (checked : (List.range width).all (fun i => candidates.any (fun p =>
      let m := 6 * (start + i) + 11
      let q := m - 2 * p
      decide (2 * p < m) &&
        (if q ≤ 450 then decide q.Prime else decide (Nat.gcd q (Nat.factorial 450) = 1)))) = true)
    (k : ℕ) (hlo : start ≤ k) (hhi : k < start + width) :
    1 ≤ a (3 * k + 5) := by
  have atK := List.all_eq_true.mp checked (k - start) (List.mem_range.mpr (by omega))
  rw [show start + (k - start) = k by omega] at atK
  obtain ⟨p, hp, hcheck⟩ := List.any_eq_true.mp atK
  have hpFacts : p.Prime ∧ p ≠ 2 := of_decide_eq_true (List.all_eq_true.mp valid p hp)
  obtain ⟨hlt, hq⟩ := Bool.and_eq_true_iff.mp hcheck
  have hpLt : 2 * p < 6 * k + 11 := of_decide_eq_true hlt
  let q := 6 * k + 11 - 2 * p
  have hqPrime : q.Prime := by
    change (if q ≤ 450 then decide q.Prime else decide (Nat.gcd q (Nat.factorial 450) = 1)) = true at hq
    split at hq
    · exact of_decide_eq_true hq
    · exact prime_of_factorial_gcd (by omega) (by dsimp [q]; omega) (of_decide_eq_true hq)
  exact (count_pos_iff _).2 ⟨p, q, hpFacts.1, hpFacts.2, hqPrime, by dsimp [q]; omega⟩

-- Checking separate blocks keeps the kernel's memory use bounded.
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private lemma verified_block_1 (k : ℕ) (hlo : 0 ≤ k) (hhi : k < 8333) :
    1 ≤ a (3 * k + 5) := by
  refine checked_block candidates_prime 0 8333 (by decide) ?_ k hlo hhi
  rw [factorial_value]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private lemma verified_block_2 (k : ℕ) (hlo : 8333 ≤ k) (hhi : k < 16666) :
    1 ≤ a (3 * k + 5) := by
  refine checked_block candidates_prime 8333 8333 (by decide) ?_ k hlo hhi
  rw [factorial_value]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private lemma verified_block_3 (k : ℕ) (hlo : 16666 ≤ k) (hhi : k < 24999) :
    1 ≤ a (3 * k + 5) := by
  refine checked_block candidates_prime 16666 8333 (by decide) ?_ k hlo hhi
  rw [factorial_value]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private lemma verified_block_4 (k : ℕ) (hlo : 24999 ≤ k) (hhi : k < 33332) :
    1 ≤ a (3 * k + 5) := by
  refine checked_block candidates_prime 24999 8333 (by decide) ?_ k hlo hhi
  rw [factorial_value]
  decide +kernel

lemma verified_range (k : ℕ) (hk : k < 33332) : 1 ≤ a (3 * k + 5) := by
  by_cases h1 : k < 8333
  · exact verified_block_1 k (Nat.zero_le _) h1
  by_cases h2 : k < 16666
  · exact verified_block_2 k (by omega) h2
  by_cases h3 : k < 24999
  · exact verified_block_3 k (by omega) h3
  exact verified_block_4 k (by omega) hk

theorem main : H1 → H2 → OMA.R_OeisA103151_conjecture_R1.H2 := by
  intro evenCase oddCase n hn hmod
  change 1 ≤ a n
  by_cases hsmall : n ≤ 100000
  · let k := (n - 5) / 3
    have hk : k < 33332 := by dsimp [k]; omega
    have he : 3 * k + 5 = n := by dsimp [k]; omega
    exact he ▸ verified_range k hk
  let k := n / 6
  have nr : n % 6 = 2 ∨ n % 6 = 5 := by omega
  rcases nr with hnEven | hnOdd
  · have he : n = 6 * k + 2 := by dsimp [k]; omega
    rw [he, even_index_iff k (by omega)]
    by_cases h3Left : (12 * k - 1).Prime
    · exact Or.inl h3Left
    by_cases h3Right : (6 * k + 1).Prime
    · exact Or.inr (Or.inl h3Right)
    right
    right
    by_cases smallPair : ∃ u v : ℕ, u + v + 1 = k ∧ (u < 32 ∨ v < 32) ∧
        (6 * u + 5).Prime ∧ (12 * v + 7).Prime
    · obtain ⟨u, v, heq, _, hp, hq⟩ := smallPair
      exact ⟨u, v, heq, hp, hq⟩
    obtain ⟨u, v, heq, _, _, hp, hq⟩ := evenCase k (by omega) h3Left h3Right
      (fun u v hsum hr ⟨hp, hq⟩ => smallPair ⟨u, v, hsum, hr, hp, hq⟩)
    exact ⟨u, v, heq, hp, hq⟩
  · have he : n = 6 * k + 5 := by dsimp [k]; omega
    rw [he, odd_index_iff]
    by_cases h3Left : (12 * k + 5).Prime
    · exact Or.inl h3Left
    right
    by_cases smallPair : ∃ u v : ℕ, u + v = k ∧ (u < 32 ∨ v < 32) ∧
        (6 * u + 5).Prime ∧ (12 * v + 1).Prime
    · obtain ⟨u, v, heq, _, hp, hq⟩ := smallPair
      exact ⟨u, v, heq, hp, hq⟩
    obtain ⟨u, v, heq, _, _, hp, hq⟩ := oddCase k (by omega) h3Left
      (fun u v hsum hr ⟨hp, hq⟩ => smallPair ⟨u, v, hsum, hr, hp, hq⟩)
    exact ⟨u, v, heq, hp, hq⟩

end OMA.R_OeisA103151_conjecture_R1_H2_R2
