import OMAStatements.S_oeis_a129912

-- Credit: @Pixelstorm44
namespace OMA.R_oeis_a129912_R1

open OMA.S_oeis_a129912

/-- A prime below the next prime in the enumeration divides the entire primorial. -/
lemma prefix_dvd {k r : ℕ} (hr : r.Prime) (h : r < Nat.nth Nat.Prime k) :
    r ∣ S_oeis_a129912.primorial k := by
  have hi : Nat.count Nat.Prime r < k := by
    apply (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).1
    rwa [Nat.nth_count hr]
  unfold S_oeis_a129912.primorial
  have hdiv := Finset.dvd_prod_of_mem (Nat.nth Nat.Prime) (Finset.mem_range.mpr hi)
  rwa [Nat.nth_count hr] at hdiv

/-- Exact local sieve. Primes in the prefix are automatically excluded.
The other primes matter only up to the square root of the actual distance. -/
lemma sift_iff {p t k : ℕ} (hp : p.Prime) (ht : S_oeis_a129912.primorial k ∣ t)
    (hd : 0 < ((p : ℤ) - t).natAbs) (hsmall : ((p : ℤ) - t).natAbs < p) :
    (((p : ℤ) - t).natAbs = 1 ∨ ((p : ℤ) - t).natAbs.Prime) ↔
    ∀ r : ℕ, r.Prime → Nat.nth Nat.Prime k ≤ r →
      r ^ 2 ≤ ((p : ℤ) - t).natAbs → t % r ≠ p % r := by
  let d := ((p : ℤ) - t).natAbs
  have residue (r : ℕ) : t % r = p % r ↔ r ∣ d := by
    change t ≡ p [MOD r] ↔ r ∣ ((p : ℤ) - t).natAbs
    rw [Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]
  constructor
  · intro good r hr _ hs eq
    have rd := (residue r).mp eq
    have two := hr.two_le
    change d = 1 ∨ d.Prime at good
    change r ^ 2 ≤ d at hs
    rcases good with one | prime
    · nlinarith
    · rcases prime.eq_one_or_self_of_dvd r rd with h | h <;> nlinarith
  · intro avoid
    change d = 1 ∨ d.Prime
    by_contra! bad
    let r := d.minFac
    have hr : r.Prime := Nat.minFac_prime bad.1
    have hs : r ^ 2 ≤ d := Nat.minFac_sq_le_self hd bad.2
    have rd : r ∣ d := Nat.minFac_dvd _
    have eq := (residue r).mpr rd
    by_cases early : r < Nat.nth Nat.Prime k
    · have rt := (prefix_dvd hr early).trans ht
      have rp : r ∣ p := Nat.dvd_of_mod_eq_zero (eq ▸ Nat.mod_eq_zero_of_dvd rt)
      have h := hp.eq_one_or_self_of_dvd r rp
      have two := hr.two_le
      change d < p at hsmall
      rcases h with h | h <;> nlinarith
    · exact avoid r hr (by omega) hs eq

/-- In a short window even the residual sieve is empty. -/
lemma window {p t k : ℕ} (hp : p.Prime) (ht : S_oeis_a129912.primorial k ∣ t)
    (hd : 0 < ((p : ℤ) - t).natAbs) (hsmall : ((p : ℤ) - t).natAbs < p)
    (hw : ((p : ℤ) - t).natAbs < (Nat.nth Nat.Prime k)^2) :
    ((p : ℤ) - t).natAbs = 1 ∨ ((p : ℤ) - t).natAbs.Prime := by
  apply (sift_iff hp ht hd hsmall).2
  intro r _ h hs
  nlinarith [Nat.pow_le_pow_left h 2]

/-- Each index of a possible witness is bounded logarithmically. -/
lemma index_bound {p i : ℕ} {s : Finset ℕ} (hi : i ∈ s)
    (h : (∏ j ∈ s, S_oeis_a129912.primorial j) < 2*p) : i ≤ (2*p).log2 := by
  have lower : 2^i ≤ S_oeis_a129912.primorial i := by
    simpa [S_oeis_a129912.primorial] using
      (Finset.prod_le_prod' (s := Finset.range i) (f := fun _ => (2 : ℕ))
        (g := Nat.nth Nat.Prime) (fun j _ => (Nat.prime_nth_prime j).two_le))
  have pos : 0 < ∏ j ∈ s, S_oeis_a129912.primorial j := by
    apply Finset.prod_pos
    intro j _
    exact Finset.prod_pos (fun a _ => (Nat.prime_nth_prime a).pos)
  have le := Nat.le_of_dvd pos (Finset.dvd_prod_of_mem S_oeis_a129912.primorial hi)
  apply (Nat.le_log2 (by omega)).mpr
  omega

private lemma short_list_mem {t : ℕ} (ht : t ∈ [2,6,12,30]) : InA129912 t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨{1}, by simp [S_oeis_a129912.primorial]⟩
  · exact ⟨{2}, by norm_num [S_oeis_a129912.primorial, Finset.prod_range_succ]⟩
  · exact ⟨{1,2}, by norm_num [S_oeis_a129912.primorial, Finset.prod_range_succ]⟩
  · exact ⟨{3}, by norm_num [S_oeis_a129912.primorial, Finset.prod_range_succ]⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private lemma small_table : ∀ n : Fin 257, n.val.Prime → n.val ≠ 2 →
    [2,6,12,30].any (fun t : ℕ =>
      let d := ((n.val : ℤ) - t).natAbs
      decide (d < n.val ∧ (d = 1 ∨ d.Prime))) = true := by decide

/-- The largest selected index gives the strongest automatic exclusions.
The empty set contributes the empty primorial, which is one. -/
private lemma top_dvd (s : Finset ℕ) :
    S_oeis_a129912.primorial (s.sup id) ∣ ∏ i ∈ s, S_oeis_a129912.primorial i := by
  rcases s.eq_empty_or_nonempty with rfl | h
  · simp [S_oeis_a129912.primorial]
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup s h id
    rw [he]
    exact Finset.dvd_prod_of_mem _ hi

/-- The finite residue test loses no witnesses in either direction. -/
lemma finite_sieve_iff (p : ℕ) (hp : p.Prime) :
    (∃ t, InA129912 t ∧ (((p : ℤ) - t).natAbs = 1 ∨
      ∃ q : ℕ, q.Prime ∧ q < p ∧ ((p : ℤ) - t).natAbs = q)) ↔
    ∃ s ∈ (Finset.range ((2*p).log2 + 1)).powerset,
      let t := ∏ i ∈ s, S_oeis_a129912.primorial i
      let d := ((p : ℤ) - t).natAbs
      0 < d ∧ d < p ∧ ∀ r : ℕ, r.Prime → Nat.nth Nat.Prime (s.sup id) ≤ r →
        r^2 ≤ d → t % r ≠ p % r := by
  constructor
  · rintro ⟨t, ⟨s, rfl⟩, good⟩
    let t := ∏ i ∈ s, S_oeis_a129912.primorial i
    let d := ((p : ℤ) - t).natAbs
    have facts : 0 < d ∧ d < p ∧ (d = 1 ∨ d.Prime) := by
      rcases good with one | ⟨q, hq, hqp, eq⟩
      · change d = 1 at one
        rw [one]
        exact ⟨Nat.zero_lt_one, hp.one_lt, Or.inl rfl⟩
      · change d = q at eq
        rw [eq]
        exact ⟨hq.pos, hqp, Or.inr hq⟩
    have range : t < 2*p := by
      have h : ((p : ℤ) - t).natAbs < p := facts.2.1
      omega
    refine ⟨s, Finset.mem_powerset.mpr (fun i hi => Finset.mem_range.mpr ?_),
      facts.1, facts.2.1, (sift_iff hp (top_dvd s) facts.1 facts.2.1).mp facts.2.2⟩
    exact Nat.lt_succ_of_le (index_bound hi range)
  · rintro ⟨s, _, hd, hlt, avoid⟩
    refine ⟨_, ⟨s,rfl⟩, ?_⟩
    rcases (sift_iff hp (top_dvd s) hd hlt).mpr avoid with one | prime
    · exact Or.inl one
    · exact Or.inr ⟨_, prime, hlt, rfl⟩

/-- Residual sieve for primes congruent to 1 modulo six after the four fixed shifts fail. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 256 < p → p % 6 = 1 →
  (∀ t ∈ [2,6,12,30], ¬ (p-t).Prime) →
  ∃ s ∈ (Finset.range ((2*p).log2 + 1)).powerset,
    let t := ∏ i ∈ s, S_oeis_a129912.primorial i
    let d := ((p : ℤ) - t).natAbs
    0 < d ∧ d < p ∧ ∀ r : ℕ, r.Prime → Nat.nth Nat.Prime (s.sup id) ≤ r →
      r^2 ≤ d → t % r ≠ p % r

/-- Residual sieve for primes congruent to 5 modulo six after the four fixed shifts fail. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → 256 < p → p % 6 = 5 →
  (∀ t ∈ [2,6,12,30], ¬ (p-t).Prime) →
  ∃ s ∈ (Finset.range ((2*p).log2 + 1)).powerset,
    let t := ∏ i ∈ s, S_oeis_a129912.primorial i
    let d := ((p : ℤ) - t).natAbs
    0 < d ∧ d < p ∧ ∀ r : ℕ, r.Prime → Nat.nth Nat.Prime (s.sup id) ≤ r →
      r^2 ≤ d → t % r ≠ p % r

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a129912.main := by
  intro h₁ h₂ p hp odd
  by_cases small : p ≤ 256
  · obtain ⟨t, ht, good⟩ := List.any_eq_true.mp (small_table ⟨p, by omega⟩ hp odd)
    simp only [decide_eq_true_eq] at good
    refine ⟨t, short_list_mem ht, ?_⟩
    rcases good.2 with one | prime
    · exact Or.inl one
    · exact Or.inr ⟨_, prime, good.1, rfl⟩
  by_cases fixed : ∃ t ∈ [2,6,12,30], (p-t).Prime
  · obtain ⟨t, ht, hprime⟩ := fixed
    have bounds : 0 < t ∧ t ≤ p := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      omega
    refine ⟨t, short_list_mem ht, Or.inr ⟨p-t, hprime, by omega, ?_⟩⟩
    omega
  push_neg at fixed
  have hodd := (hp.eq_two_or_odd.resolve_left odd)
  have hthree : p % 3 ≠ 0 := by
    intro hz
    have h := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero hz)
    omega
  apply (finite_sieve_iff p hp).mpr
  rcases (show p % 6 = 1 ∨ p % 6 = 5 by omega) with a | b
  · exact h₁ p hp (by omega) a fixed
  · exact h₂ p hp (by omega) b fixed

end OMA.R_oeis_a129912_R1
