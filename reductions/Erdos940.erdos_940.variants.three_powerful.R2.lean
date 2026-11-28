import FormalConjectures.ErdosProblems.«940»

/-! # Three powerful summands in a square class

Multiplication by a square preserves every representation. Consequently the bad
multipliers of a fixed squarefree kernel form a divisor-closed set. Such a set
is finite if it contains only finitely many primes and omits some power of each
of those primes. This separates the large squarefree kernels, prime multipliers,
and individual prime-power towers. All three conditions follow from the original
eventual assertion as well.
-/

-- Credit: @AlfredMelson
namespace OMA.R_Erdos940_erdos_940_variants_three_powerful_R2
open Filter Finset

/-- The squarefree instances of the original assertion. -/
def H1 : Prop := ∀ᶠ s : ℕ in atTop, Squarefree s →
  ∃ S : Multiset ℕ, S.card ≤ 3 ∧ (∀ t ∈ S, Nat.Full 2 t) ∧ s = S.sum

/-- For each exceptional squarefree kernel, all sufficiently large prime multipliers repair it. -/
def H2 : Prop :=
  let R (x : ℕ) := ∃ S : Multiset ℕ, S.card ≤ 3 ∧ (∀ t ∈ S, Nat.Full 2 t) ∧ x = S.sum
  ∀ s : ℕ, Squarefree s → ¬ R s → ∀ᶠ p : ℕ in atTop, p.Prime → R (s*p^2)

/-- Each exceptional prime multiplier is repaired somewhere along its own tower. -/
def H3 : Prop :=
  let R (x : ℕ) := ∃ S : Multiset ℕ, S.card ≤ 3 ∧ (∀ t ∈ S, Nat.Full 2 t) ∧ x = S.sum
  ∀ s p : ℕ, Squarefree s → p.Prime → ¬ R (s*p^2) → ∃ e : ℕ, R (s*(p^e)^2)

lemma kernel_decomposition (n : ℕ) (hn : 0 < n) : ∃ s m : ℕ, Squarefree s ∧ n = s*m^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : Squarefree n
    · exact ⟨n,1,hs,by simp⟩
    · rw [Nat.squarefree_iff_prime_squarefree] at hs
      push Not at hs
      obtain ⟨p,hp,a,ha⟩ := hs
      have ha0 : 0 < a := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at ha; omega
      have hlt : a < n := by
        rw [ha]
        exact lt_mul_of_one_lt_left ha0 (one_lt_mul_of_lt_of_le hp.one_lt hp.one_lt.le)
      obtain ⟨s,m,hs,hm⟩ := ih a hlt ha0
      exact ⟨s,p*m,hs,by rw [ha,hm]; ring⟩

lemma full_mul_square {n : ℕ} (h : Nat.Full 2 n) (m : ℕ) : Nat.Full 2 (n*m^2) := by
  intro p hp
  obtain ⟨pp,hd,hn⟩ := Nat.mem_primeFactors.mp hp
  rcases pp.dvd_mul.mp hd with hd|hd
  · exact dvd_mul_of_dvd_left (h p (Nat.mem_primeFactors.mpr ⟨pp,hd,left_ne_zero_of_mul hn⟩)) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (pp.dvd_of_dvd_pow hd) 2) _

lemma scale_rep (x m : ℕ) (h : ∃ S : Multiset ℕ, S.card ≤ 3 ∧
    (∀ t ∈ S, Nat.Full 2 t) ∧ x = S.sum) :
    ∃ S : Multiset ℕ, S.card ≤ 3 ∧ (∀ t ∈ S, Nat.Full 2 t) ∧ x*m^2 = S.sum := by
  obtain ⟨S,hS,hf,rfl⟩ := h
  refine ⟨S.map (· * m^2),by simpa using hS,?_,?_⟩
  · intro t ht
    obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp ht
    exact full_mul_square (hf a ha) m
  · simpa using (Multiset.sum_map_mul_right (s := S) (f := id) (a := m^2)).symm

/-- A divisor-closed exceptional set with bounded primes and bounded exponents is bounded. -/
lemma eventual_of_prime_tests (P : ℕ → Prop) (up : ∀ a b, a ∣ b → P a → P b)
    (primes : ∀ᶠ p : ℕ in atTop, p.Prime → P p)
    (towers : ∀ p : ℕ, p.Prime → ∃ e : ℕ, P (p^e)) : ∀ᶠ m : ℕ in atTop, P m := by
  classical
  obtain ⟨B,hB⟩ := eventually_atTop.mp primes
  let S := (range B).filter Nat.Prime
  have exp : ∀ p ∈ S, ∃ e : ℕ, P (p^e) := fun p hp => towers p (mem_filter.mp hp).2
  choose e he using exp
  let f (p : ℕ) := if hp : p ∈ S then e p hp else 0
  let limit := ∏ p ∈ S, p^(f p)
  filter_upwards [eventually_gt_atTop limit] with m hm
  by_contra hbad
  have hm0 : m ≠ 0 := by omega
  have sub : m.primeFactors ⊆ S := by
    intro p hp
    obtain ⟨pp,hd,_⟩ := Nat.mem_primeFactors.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (by
      by_contra! h
      exact hbad (up _ _ hd (hB p h pp))),pp⟩
  have powbound (p) (hp : p ∈ m.primeFactors) : m.factorization p ≤ f p := by
    by_contra! h
    have hit : P (p^(f p)) := by simpa [f,sub hp] using he p (sub hp)
    exact hbad (up _ _ ((pow_dvd_pow p h.le).trans (Nat.ordProj_dvd m p)) hit)
  have hd : m ∣ limit := by
    calc
      m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := Nat.prod_primeFactors_pow_factorization hm0
      _ ∣ ∏ p ∈ m.primeFactors, p ^ f p := Finset.prod_dvd_prod_of_dvd _ _ (fun p hp => pow_dvd_pow p (powbound p hp))
      _ ∣ limit := Finset.prod_dvd_prod_of_subset _ _ _ sub
  have hpos : 0 < limit := Finset.prod_pos fun p hp => pow_pos (mem_filter.mp hp).2.pos _
  exact (not_le_of_gt hm) (Nat.le_of_dvd hpos hd)

theorem main : H1 → H2 → H3 → type_of% @Erdos940.erdos_940.variants.three_powerful := by
  classical
  intro h1 h2 h3
  let R (x : ℕ) := ∃ S : Multiset ℕ, S.card ≤ 3 ∧ (∀ t ∈ S, Nat.Full 2 t) ∧ x = S.sum
  have fixed (s : ℕ) (hs : Squarefree s) : ∀ᶠ m : ℕ in atTop, R (s*m^2) := by
    by_cases hr : R s
    · exact Eventually.of_forall (fun m => scale_rep s m hr)
    apply eventual_of_prime_tests (fun m => R (s*m^2)) _ (h2 s hs hr)
    · intro p hp
      by_cases hrp : R (s*p^2)
      · exact ⟨1,by simpa using hrp⟩
      · exact h3 s p hs hp hrp
    · rintro a b ⟨u,rfl⟩ ha
      simpa [mul_pow,mul_assoc] using scale_rep _ u ha
  obtain ⟨T,hT⟩ := eventually_atTop.mp h1
  have small (s) (_ : s ∈ range T) : ∀ᶠ n : ℕ in atTop, Squarefree s →
      ∀ m : ℕ, n=s*m^2 → R n := by
    by_cases hs : Squarefree s
    · obtain ⟨k,hk⟩ := eventually_atTop.mp (fixed s hs)
      filter_upwards [eventually_gt_atTop (s*k^2)] with n hn _ m he
      subst n
      apply hk
      by_contra! h
      exact (not_le_of_gt hn) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h.le 2))
    · exact Eventually.of_forall fun _ h => (hs h).elim
  filter_upwards [(eventually_all_finset (range T)).mpr small,eventually_gt_atTop 0] with n hsmall hn
  obtain ⟨s,m,hs,he⟩ := kernel_decomposition n hn
  by_cases st : s < T
  · exact hsmall s (mem_range.mpr st) hs m he
  · rw [he]
    exact scale_rep _ _ (hT s (by omega) hs)
end OMA.R_Erdos940_erdos_940_variants_three_powerful_R2
