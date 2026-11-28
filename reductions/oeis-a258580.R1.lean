import OMAStatements.S_oeis_a258580

-- Reduction oeis-a258580.R1
-- Credit: @Pixelstorm44

namespace OMA.R_oeis_a258580_R1

open OMA.S_oeis_a258580 (prime)

/-- The two residue classes of Shiu's strings theorem needed for the sum.
See D. K. L. Shiu, Strings of congruent primes, JLMS 61 (2000), 359–373. -/
def H1 : Prop :=
  ∀ n D : ℕ, 2 ≤ n → 3 ≤ D → ∀ c : ℕ, c = 1 ∨ c = D - 1 →
    ∃ s : ℕ, ∀ t < n, prime (s + t + 1) % D = c

/-- The coefficients realized by sums are closed under removal of one prime factor.
The three primes witnessing the smaller coefficient may all change. -/
def H2 : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    let S := {p : ℕ | p.Prime ∧ n ∣ p.primeCounting}
    let C := {b : ℕ | ∃ x ∈ S, ∃ y ∈ S, ∃ r ∈ S, x < y ∧ x + y = 2 * (b * r ^ m)}
    ∀ a p : ℕ, 0 < a → p.Prime → a * p ∈ C → a ∈ C

/-- The corresponding one-prime descent for coefficients of positive differences. -/
def H3 : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    let S := {p : ℕ | p.Prime ∧ n ∣ p.primeCounting}
    let C := {b : ℕ | ∃ x ∈ S, ∃ r ∈ S, x + 2 * (b * r ^ m) ∈ S}
    ∀ a p : ℕ, 0 < a → p.Prime → a * p ∈ C → a ∈ C

lemma rank_sample {i : ℕ} (hi : 0 < i) : (prime i).primeCounting = i := by
  unfold prime Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime]
  omega

lemma sampled_mem {n i : ℕ} (hn : 0 < n) (hi : 0 < i) :
    (prime (i*n)).Prime ∧ n ∣ (prime (i*n)).primeCounting := by
  exact ⟨Nat.prime_nth_prime _, by rw [rank_sample (Nat.mul_pos hi hn)]; exact dvd_mul_left _ _⟩

lemma extract_sample {n p : ℕ} (hp : p.Prime ∧ n ∣ p.primeCounting) :
    ∃ i > 0, prime (i*n) = p := by
  have hc : p.primeCounting = Nat.count Nat.Prime p + 1 := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, hp.1]
  obtain ⟨i, hi⟩ := hp.2
  refine ⟨i, ?_, ?_⟩
  · by_contra! hz
    rw [show i = 0 by omega, Nat.mul_zero] at hi
    omega
  · rw [Nat.mul_comm, ← hi, prime, hc, Nat.add_sub_cancel, Nat.nth_count hp.1]

lemma order_indices {n i j : ℕ}
    (h : prime (i*n) < prime (j*n)) : i < j := by
  by_contra! hji
  have hle := (Nat.nth_monotone Nat.infinite_setOfPred_prime)
    (Nat.sub_le_sub_right (Nat.mul_le_mul_right n hji) 1)
  exact (not_lt_of_ge hle) h

/-- Every block of n consecutive positive ranks meets the sampled ranks. -/
lemma hit_residue (h : H1) {n D : ℕ} (hn : 0 < n) (hD : 3 ≤ D)
    (c : ℕ) (hc : c = 1 ∨ c = D-1) :
    ∃ p : ℕ, (p.Prime ∧ n ∣ p.primeCounting) ∧ p % D = c := by
  by_cases hsmall : n = 1
  · subst n
    have hcop : c.Coprime D := by
      rcases hc with rfl | rfl
      · simp
      · exact (Nat.coprime_self_sub_left (by omega : 1 ≤ D)).2 (by simp)
    obtain ⟨p, _, hp, he⟩ := Nat.forall_exists_prime_gt_and_modEq 0 (by omega : D ≠ 0) hcop
    have hlt : c < D := by rcases hc with rfl | rfl <;> omega
    exact ⟨p, ⟨hp, one_dvd _⟩, Eq.trans (he : p % D = c % D) (Nat.mod_eq_of_lt hlt)⟩
  obtain ⟨s, hs⟩ := h n D (by omega) hD c hc
  have hdiv := Nat.mod_add_div s n
  have hmod := Nat.mod_lt s hn
  let t := n - 1 - s % n
  have ht : t < n := by dsimp [t]; omega
  have hr : s + t + 1 = (s / n + 1) * n := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (s/n)]
    dsimp [t]
    omega
  refine ⟨_, sampled_mem hn (Nat.succ_pos (s/n)), ?_⟩
  simpa only [hr] using hs t ht

/-- Descend from any represented positive multiple by removing its prime factors. -/
lemma peel {C : Set ℕ}
    (step : ∀ a p : ℕ, 0 < a → p.Prime → a*p ∈ C → a ∈ C)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a*b ∈ C) : a ∈ C := by
  induction b using induction_on_primes with
  | zero => omega
  | one => simpa using hab
  | prime_mul p b hp ih =>
    have hb' : 0 < b := by by_contra! hz; simp [show b = 0 by omega] at hb
    apply ih hb'
    apply step (a*b) p (Nat.mul_pos ha hb') hp
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hab

/-- Opposite reduced classes give a positive multiple of the desired sum. -/
lemma sum_seed (h : H1) {a m n : ℕ} (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    let S := {p : ℕ | p.Prime ∧ n ∣ p.primeCounting}
    ∃ b > 0, ∃ x ∈ S, ∃ y ∈ S, ∃ r ∈ S, x < y ∧ x + y = 2 * ((a*b) * r ^ m) := by
  dsimp only
  let r := prime (1*n)
  have hr := sampled_mem hn (by decide : 0 < 1)
  have hpow : 2 ≤ r ^ m := le_trans hr.1.two_le (Nat.le_self_pow hm.ne' r)
  let D := 2 * (a * r ^ m)
  have hD : 3 ≤ D := by dsimp [D]; nlinarith [Nat.mul_le_mul_right (r^m) ha]
  obtain ⟨p, hp, hpr⟩ := hit_residue h hn hD 1 (Or.inl rfl)
  obtain ⟨q, hq, hqr⟩ := hit_residue h hn hD (D-1) (Or.inr rfl)
  have hdvd : D ∣ p + q := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, hpr, hqr, show 1 + (D-1) = D by omega, Nat.mod_self]
  obtain ⟨b, heq⟩ := hdvd
  have hb : 0 < b := by
    have := hp.1.pos
    by_contra! hz
    simp [show b = 0 by omega] at heq
    omega
  have he : p+q = 2*((a*b)*r^m) := by rw [heq]; dsimp [D]; ring
  rcases lt_trichotomy p q with hlt | he' | hgt
  · exact ⟨b, hb, p, hp, q, hq, r, hr, hlt, he⟩
  · subst q; omega
  · exact ⟨b, hb, q, hq, p, hp, r, hr, hgt, (Nat.add_comm q p).trans he⟩

/-- Equal residues of two sampled primes produce a positive multiple of any
prescribed gap. This side needs no theorem on strings of primes. -/
lemma diff_seed {a m n : ℕ} (ha : 0 < a) (hn : 0 < n) :
    let S := {p : ℕ | p.Prime ∧ n ∣ p.primeCounting}
    ∃ b > 0, ∃ x ∈ S, ∃ r ∈ S, x + 2 * ((a*b) * r ^ m) ∈ S := by
  dsimp only
  let r := prime (1*n)
  have hr := sampled_mem hn (by decide : 0 < 1)
  let D := 2 * (a * r^m)
  have hrpos : 0 < r := hr.1.pos
  have hD : 0 < D := by dsimp [D]; positivity
  let f (i : ℕ) := prime ((i+1)*n)
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => (⟨f i % D, Nat.mod_lt _ hD⟩ : Fin D))
  have hmod : f i % D = f j % D := congrArg Fin.val he
  have hne : f i ≠ f j := by
    intro heq
    have hh := congrArg Nat.primeCounting heq
    change (prime ((i+1)*n)).primeCounting = (prime ((j+1)*n)).primeCounting at hh
    rw [rank_sample (Nat.mul_pos (Nat.succ_pos _) hn),
        rank_sample (Nat.mul_pos (Nat.succ_pos _) hn)] at hh
    have := Nat.eq_of_mul_eq_mul_right hn hh
    omega
  have build (u v : ℕ) (hlt : f u < f v) (heq : f u % D = f v % D) :
      ∃ b > 0, ∃ x : ℕ, (x.Prime ∧ n ∣ x.primeCounting) ∧
        ∃ r' : ℕ, (r'.Prime ∧ n ∣ r'.primeCounting) ∧
        ((x + 2*((a*b)*r'^m)).Prime ∧ n ∣ (x + 2*((a*b)*r'^m)).primeCounting) := by
    obtain ⟨b, hb⟩ := (Nat.modEq_iff_dvd' hlt.le).mp heq
    have hbpos : 0 < b := by
      by_contra! hz
      simp [show b = 0 by omega] at hb
      omega
    refine ⟨b, hbpos, f u, sampled_mem hn (Nat.succ_pos u), r, hr, ?_⟩
    have hv : f u + 2*((a*b)*r^m) = f v := by
      have hprod : 2*((a*b)*r^m) = D*b := by dsimp [D]; ring
      omega
    rw [hv]
    exact sampled_mem hn (Nat.succ_pos v)
  rcases lt_or_gt_of_ne hne with h | h
  · exact build i j h hmod
  · exact build j i h hmod.symm

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a258580.main := by
  intro strings sumStep diffStep
  have sums (a m n : ℕ) (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
      ∃ i j k : ℕ, 0 < j ∧ j < i ∧ 0 < k ∧
        prime (i*n) + prime (j*n) = 2*(a*prime (k*n)^m) := by
    obtain ⟨b, hb, h⟩ := sum_seed strings ha hm hn
    obtain ⟨x, hx, y, hy, r, hr, hlt, he⟩ := peel (sumStep m n hm hn) ha hb h
    obtain ⟨j, hj, rfl⟩ := extract_sample hx
    obtain ⟨i, hi, rfl⟩ := extract_sample hy
    obtain ⟨k, hk, rfl⟩ := extract_sample hr
    exact ⟨i,j,k,hj,order_indices hlt,hk,(Nat.add_comm ..).trans he⟩
  constructor
  · intro n hn
    obtain ⟨k,j,i,hj,hjk,hi,h⟩ := sums 1 2 n (by decide) (by decide) hn
    exact ⟨i,j,k,hi,hj,hjk,by simpa [Nat.add_comm] using h⟩
  · intro a m n ha hm hn
    refine ⟨sums a m n ha hm hn, ?_⟩
    obtain ⟨b, hb, h⟩ := diff_seed (m := m) ha hn
    obtain ⟨x, hx, r, hr, hy⟩ := peel (diffStep m n hm hn) ha hb h
    obtain ⟨j, hj, rfl⟩ := extract_sample hx
    obtain ⟨k, hk, hr'⟩ := extract_sample hr
    obtain ⟨i, hi, he⟩ := extract_sample hy
    have hpos : 0 < 2*(a*r^m) := by have := hr.1.pos; positivity
    refine ⟨i,j,k,hj,order_indices (n := n) (by omega),hk,?_⟩
    rw [he, hr']
    push_cast
    ring

end OMA.R_oeis_a258580_R1
