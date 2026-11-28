import OMAStatements.S_oeis_a380876
import Mathlib

/-!
# OEIS A380876: a(2p+1) = p for primes p and a(p+1) = 2p for primes p > 3

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. (1) Terms exist (large multiples of n-1 are eligible), are positive and distinct. (2) Deadline
lemma: every y >= 1 appears by position 2y+1 (induction: at position 2y+1 all smaller values are
used, gcd(y, 2y) = y > 1 and |2y+1-y| > 1, so y is the least eligible value if still unused). (3) A
prime p can only be chosen at a position n with p | n-1; below 2p+1 that is n = p+1, where |p - n| =
1 forbids it. So a(2p+1) = p. (4) For p > 3, 2p is unused before position p+1: a position n <= p
choosing 2p needs gcd(2p, n-1) > 1 with n-1 < p, so n is odd; among the even numbers 2..2p-2 fewer
than p-1 are unavailable (used or within distance 1 of n), so a smaller even eligible value exists.
(5) At position p+1 the eligible values are multiples of p; p is at distance 1, and 2p is unused, so
a(p+1) = 2p.
-/

open OMA.S_oeis_a380876

namespace OMA.A380876Proof

lemma distance (y n : ℕ) :
    1 < |(y : ℤ) - (n : ℤ)| ↔ y + 1 < n ∨ n + 1 < y := by
  rw [lt_abs]
  omega

lemma chosen {a : ℕ → ℕ} (ha : IsSeq a) {n : ℕ} (hn : 2 < n) :
    Eligible a n (a n) := (ha.2.2 n hn).1

lemma least {a : ℕ → ℕ} (ha : IsSeq a) {n y : ℕ} (hn : 2 < n)
    (hy : Eligible a n y) : a n ≤ y := (ha.2.2 n hn).2 hy

lemma positive {a : ℕ → ℕ} (ha : IsSeq a) {n : ℕ} (hn : 1 ≤ n) : 0 < a n := by
  by_cases h1 : n = 1
  · simp [h1, ha.1]
  by_cases h2 : n = 2
  · simp [h2, ha.2.1]
  exact (chosen ha (by omega)).1

lemma deadline {a : ℕ → ℕ} (ha : IsSeq a) (y : ℕ) (hy : 1 ≤ y) :
    ∃ m, 1 ≤ m ∧ m ≤ 2 * y + 1 ∧ a m = y := by
  induction y using Nat.strong_induction_on with
  | h y ih =>
    by_cases h1 : y = 1
    · exact ⟨1, by omega, by omega, by simpa [h1] using ha.1⟩
    by_cases hu : ∃ m, 1 ≤ m ∧ m < 2 * y + 1 ∧ a m = y
    · obtain ⟨m, hm, hb, he⟩ := hu
      exact ⟨m, hm, by omega, he⟩
    have he : Eligible a (2 * y + 1) y := by
      refine ⟨by omega, ?_, ?_, (distance _ _).2 (Or.inl (by omega))⟩
      · intro m hm hb he
        exact hu ⟨m, hm, hb, he⟩
      · simpa using (show 1 < y by omega)
    have hn : 2 < 2 * y + 1 := by omega
    have hle := least ha hn he
    have hge : y ≤ a (2 * y + 1) := by
      by_contra h
      obtain ⟨m, hm, hb, heq⟩ := ih (a (2 * y + 1)) (by omega)
        (positive ha (by omega))
      exact (chosen ha hn).2.1 m hm (by omega) heq
    exact ⟨2 * y + 1, by omega, le_rfl, by omega⟩

lemma prime_dvd {p k : ℕ} (hp : p.Prime) (hg : 1 < Nat.gcd p k) : p ∣ k := by
  have h := hp.eq_one_or_self_of_dvd (Nat.gcd p k) (Nat.gcd_dvd_left p k)
  rcases h with h | h
  · omega
  · rw [← h]
    exact Nat.gcd_dvd_right p k

lemma prime_unused {a : ℕ → ℕ} (ha : IsSeq a) {p : ℕ} (hp : p.Prime)
    {n : ℕ} (hn : 1 ≤ n) (hb : n < 2 * p + 1) : a n ≠ p := by
  intro he
  have hp2 := hp.two_le
  by_cases h1 : n = 1
  · have := ha.1
    simp only [h1] at he
    omega
  by_cases h2 : n = 2
  · have hp4 : p = 4 := by simpa [h2, ha.2.1] using he.symm
    rw [hp4] at hp
    norm_num at hp
  have hc := chosen ha (show 2 < n by omega)
  rw [he] at hc
  have hd := prime_dvd hp hc.2.2.1
  obtain ⟨k, hk⟩ := hd
  have hn3 : 2 < n := by omega
  have hn0 : 0 < n - 1 := by omega
  have hb2 : n - 1 < 2 * p := by omega
  have hk1 : k = 1 := by
    have hpos : 0 < k := by nlinarith
    have hsmall : k < 2 := by nlinarith
    omega
  have hdist := (distance _ _).1 hc.2.2.2
  subst k
  simp only [mul_one] at hk
  omega

lemma prime_position {a : ℕ → ℕ} (ha : IsSeq a) {p : ℕ} (hp : p.Prime) :
    a (2 * p + 1) = p := by
  obtain ⟨m, hm, hb, he⟩ := deadline ha p (by have := hp.two_le; omega)
  have : m = 2 * p + 1 := by
    by_contra h
    exact prime_unused ha hp hm (by omega) he
  simpa [this] using he

lemma term_eq {a : ℕ → ℕ} (ha : IsSeq a) {n y : ℕ} (hn : 2 < n)
    (he : Eligible a n y) (hl : ∀ z, Eligible a n z → y ≤ z) : a n = y := by
  exact Nat.le_antisymm (least ha hn he) (hl _ (chosen ha hn))

lemma initial_terms {a : ℕ → ℕ} (ha : IsSeq a) :
    a 3 = 6 ∧ a 4 = 9 ∧ a 5 = 2 ∧ a 6 = 10 ∧ a 7 = 3 ∧ a 8 = 14 := by
  have h1 := ha.1
  have h2 := ha.2.1
  have h3 : a 3 = 6 := by
    apply term_eq ha (by omega)
    · refine ⟨by decide, ?_, by decide, by decide⟩
      intro m hm hb
      interval_cases m <;> simp_all
    · intro z hz
      by_contra h
      have hz5 : z ≤ 5 := by omega
      interval_cases z <;> norm_num [Eligible, h1, h2] at hz
  have h4 : a 4 = 9 := by
    apply term_eq ha (by omega)
    · refine ⟨by decide, ?_, by decide, by decide⟩
      intro m hm hb
      interval_cases m <;> simp_all
    · intro z hz
      by_contra h
      have hz8 : z ≤ 8 := by omega
      interval_cases z <;> norm_num [Eligible, h1, h2, h3] at hz
      exact hz 3 (by omega) (by omega) h3
  have h5 : a 5 = 2 := prime_position ha (by decide : Nat.Prime 2)
  have h6 : a 6 = 10 := by
    apply term_eq ha (by omega)
    · refine ⟨by decide, ?_, by decide, by decide⟩
      intro m hm hb
      interval_cases m <;> simp_all
    · intro z hz
      by_contra h
      have hz9 : z ≤ 9 := by omega
      interval_cases z <;> norm_num [Eligible, h1, h2, h3, h4, h5] at hz
  have h7 : a 7 = 3 := prime_position ha (by decide : Nat.Prime 3)
  have h8 : a 8 = 14 := by
    apply term_eq ha (by omega)
    · refine ⟨by decide, ?_, by decide, by decide⟩
      intro m hm hb
      interval_cases m <;> simp_all
    · intro z hz
      by_contra h
      have hz13 : z ≤ 13 := by omega
      interval_cases z <;> norm_num [Eligible, h1, h2, h3, h4, h5, h6, h7] at hz
  exact ⟨h3, h4, h5, h6, h7, h8⟩

lemma eligible_exists (a : ℕ → ℕ) (n : ℕ) (hn : 2 < n) : ∃ y, Eligible a n y := by
  let b := (Finset.range n).sup a
  let y := (n - 1) * (b + n + 2)
  have hb : ∀ m, m < n → a m ≤ b := by
    intro m hm
    exact Finset.le_sup (Finset.mem_range.mpr hm)
  have hy : b + n + 1 < y := by
    dsimp [y]
    have : 2 ≤ n - 1 := by omega
    nlinarith
  refine ⟨y, by omega, ?_, ?_, (distance _ _).2 (Or.inr (by omega))⟩
  · intro m hm hmn he
    have := hb m hmn
    omega
  · have hd : n - 1 ∣ y := ⟨b + n + 2, rfl⟩
    rw [Nat.gcd_eq_right hd]
    omega

lemma least_exists (a : ℕ → ℕ) (n : ℕ) (hn : 2 < n) :
    ∃ y, IsLeast {y : ℕ | Eligible a n y} y := by
  classical
  have h := eligible_exists a n hn
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hy => Nat.find_min' h hy⟩

lemma exists_sequence : ∃ a : ℕ → ℕ, IsSeq a := by
  classical
  let F : (n : ℕ) → ((m : ℕ) → m < n → ℕ) → ℕ := fun n f =>
    if n = 1 then 1 else if n = 2 then 4 else
      if h : 2 < n then
        (least_exists (fun m => if hm : m < n then f m hm else 0) n h).choose
      else 0
  let a : ℕ → ℕ := Nat.lt_wfRel.wf.fix F
  have heq (n : ℕ) : a n = F n (fun m _ => a m) :=
    WellFounded.fix_eq _ _ _
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [heq]
    simp [F]
  · rw [heq]
    simp [F]
  · intro n hn
    have h1 : n ≠ 1 := by omega
    have h2 : n ≠ 2 := by omega
    rw [heq]
    dsimp only [F]
    simp only [if_neg h1, if_neg h2, dif_pos hn]
    have hc := (least_exists (fun m => if hm : m < n then a m else 0) n hn).choose_spec
    have he (y : ℕ) :
        Eligible (fun m => if hm : m < n then a m else 0) n y ↔ Eligible a n y := by
      simp only [Eligible]
      constructor
      · rintro ⟨hp, hu, hg, hd⟩
        exact ⟨hp, fun m hm hmn => by simpa [hmn] using hu m hm hmn, hg, hd⟩
      · rintro ⟨hp, hu, hg, hd⟩
        exact ⟨hp, fun m hm hmn => by simpa [hmn] using hu m hm hmn, hg, hd⟩
    exact ⟨(he _).1 hc.1, fun y hy => hc.2 ((he y).2 hy)⟩

lemma two_dvd_pred {a : ℕ → ℕ} (ha : IsSeq a) {p n : ℕ} (hp : p.Prime)
    (hn : 2 < n) (hnp : n ≤ p) (he : a n = 2 * p) : 2 ∣ n - 1 := by
  have hc := chosen ha hn
  rw [he] at hc
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show Nat.gcd (2 * p) (n - 1) ≠ 1 by have := hc.2.2.1; omega)
  have hqmul : q ∣ 2 * p := dvd_trans hqd (Nat.gcd_dvd_left _ _)
  have hqn : q ∣ n - 1 := dvd_trans hqd (Nat.gcd_dvd_right _ _)
  rcases hq.dvd_mul.mp hqmul with hq2 | hqp
  · rcases Nat.prime_two.eq_one_or_self_of_dvd q hq2 with heq | heq
    · have := hq.two_le
      omega
    · simpa [heq] using hqn
  · rcases hp.eq_one_or_self_of_dvd q hqp with heq | heq
    · have := hq.two_le
      omega
    · have hle := Nat.le_of_dvd (show 0 < n - 1 by omega) hqn
      omega

lemma even_count_bound {a : ℕ → ℕ} (ha : IsSeq a) {p n : ℕ}
    (hn : 2 < n) (hnodd : 2 ∣ n - 1) (he : a n = 2 * p)
    (T : Finset ℕ) (hTsub : T ⊆ Finset.Icc 1 (n - 1))
    (hTodd : ∀ m ∈ T, ¬2 ∣ a m) : p - 1 ≤ n - 1 - T.card + 2 := by
  classical
  let S := (Finset.Icc 1 (p - 1)).image (fun k => 2 * k)
  let B := Finset.Icc 1 (n - 1) \ T
  have hsub : S ⊆ B.image a ∪ {n - 1, n + 1} := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hk1, hkp⟩ := Finset.mem_Icc.mp hk
    by_cases hu : ∃ m ∈ B, a m = 2 * k
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr hu)
    by_cases hd : 1 < |((2 * k : ℕ) : ℤ) - (n : ℤ)|
    · have hc : Eligible a n (2 * k) := by
        refine ⟨by omega, ?_, ?_, hd⟩
        · intro m hm hmn hem
          have hmT : m ∉ T := by
            intro hmT
            exact hTodd m hmT ⟨k, hem⟩
          exact hu ⟨m, Finset.mem_sdiff.mpr
            ⟨Finset.mem_Icc.mpr ⟨hm, by omega⟩, hmT⟩, hem⟩
        · have hdiv : 2 ∣ Nat.gcd (2 * k) (n - 1) := Nat.dvd_gcd ⟨k, rfl⟩ hnodd
          have hpos : 0 < Nat.gcd (2 * k) (n - 1) :=
            Nat.gcd_pos_of_pos_left _ (by omega)
          have := Nat.le_of_dvd hpos hdiv
          omega
      have hle := least ha hn hc
      rw [he] at hle
      omega
    · have hne : 2 * k ≠ n := by
        obtain ⟨j, hj⟩ := hnodd
        omega
      have hx : 2 * k = n - 1 ∨ 2 * k = n + 1 := by
        rw [distance] at hd
        omega
      exact Finset.mem_union_right _ (by simpa using hx)
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro x y h
    change 2 * x = 2 * y at h
    omega
  have hcard : S.card = p - 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    omega
  have hpair : ({n - 1, n + 1} : Finset ℕ).card = 2 := by
    simp [show n - 1 ≠ n + 1 by omega]
  have hbcard : B.card = n - 1 - T.card := by
    dsimp [B]
    rw [Finset.card_sdiff_of_subset hTsub, Nat.card_Icc]
    omega
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (B.image a) {n - 1, n + 1}
  have hi := Finset.card_image_le (s := B) (f := a)
  omega

lemma double_prime_unused {a : ℕ → ℕ} (ha : IsSeq a) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {n : ℕ} (hn : 1 ≤ n) (hnp : n < p + 1) : a n ≠ 2 * p := by
  intro he
  have h1 := ha.1
  have h2 := ha.2.1
  have hn3 : 2 < n := by
    by_contra h
    interval_cases n <;> omega
  have hnodd := two_dvd_pred ha hp hn3 (by omega) he
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  by_cases hnp2 : n ≤ p - 2
  · have hb := even_count_bound ha hn3 hnodd he {1} (by
        intro m hm
        simp only [Finset.mem_singleton] at hm
        subst m
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (by
        intro m hm
        simp only [Finset.mem_singleton] at hm
        subst m
        simp [h1])
    norm_num at hb
    omega
  have hnp : n = p := by
    obtain ⟨j, hj⟩ := hnodd
    omega
  subst n
  obtain ⟨h3, h4, h5, h6, h7, h8⟩ := initial_terms ha
  by_cases hp7 : p ≤ 7
  · interval_cases p <;> norm_num at hp <;> omega
  have hb := even_count_bound ha hn3 hnodd he {1, 4, 7} (by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl <;> exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl <;> norm_num [h1, h4, h7])
  norm_num at hb
  omega

lemma double_prime_position {a : ℕ → ℕ} (ha : IsSeq a) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) : a (p + 1) = 2 * p := by
  apply term_eq ha (by omega)
  · refine ⟨by omega, ?_, ?_, (distance _ _).2 (Or.inr (by omega))⟩
    · intro m hm hmp
      exact double_prime_unused ha hp hp3 hm hmp
    · simpa using (show 1 < p by omega)
  · intro y hy
    have hd : p ∣ y := by
      have hg : 1 < Nat.gcd p y := by
        simpa [Nat.gcd_comm] using hy.2.2.1
      exact prime_dvd hp hg
    obtain ⟨k, hk⟩ := hd
    have hypos := hy.1
    have hdist := (distance _ _).1 hy.2.2.2
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k = 0 ∨ k = 1 := by omega
      rcases hk1 with hk0 | hk1
      · rw [hk0, mul_zero] at hk
        omega
      · rw [hk1, mul_one] at hk
        omega
    nlinarith

end OMA.A380876Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a380876.main := by
  refine ⟨OMA.A380876Proof.exists_sequence, ?_⟩
  intro a ha p hp
  exact ⟨OMA.A380876Proof.prime_position ha hp,
    OMA.A380876Proof.double_prime_position ha hp⟩
