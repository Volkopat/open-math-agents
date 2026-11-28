import OMAStatements.S_oeis_a394382

/-! A counterexample to each of Chai Wah Wu's two decimal-digit conjectures.
The primality certificates and both digit lists are checked in Lean. -/

namespace DecimalSquarePair

open OMA.S_oeis_a394382

theorem binary_pow_eq {G : Type*} [Monoid G] (x : G) (k : ℕ) :
    npowBinRec k x = x^k := by
  induction k with
  | zero => simp [npowBinRec_zero]
  | succ k ih => rw [npowBinRec_succ, ih, pow_succ]

private theorem prime_mem_factors {q : ℕ} (hq : q.Prime) (xs : List ℕ)
    (known : ∀ x ∈ xs, Nat.Prime x) (dvd : q ∣ xs.prod) : q ∈ xs := by
  induction xs with
  | nil => exact (hq.not_dvd_one dvd).elim
  | cons x xs ih =>
    rcases hq.dvd_mul.mp dvd with hx | rest
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq
        (known x List.mem_cons_self)).mp hx))
    · exact List.mem_cons_of_mem _ (ih (fun v hv => known v (List.mem_cons_of_mem _ hv)) rest)

/-- Lucas certificate with one previously certified prime and small remaining factors. -/
theorem lucas_step {n child : ℕ} (childPrime : child.Prime) (small : List ℕ) (g : ℕ)
    (cert : child * small.prod = n-1 ∧ (∀ q ∈ small, Nat.Prime q) ∧
      npowBinRec (n-1) (g : ZMod n) = 1 ∧
      ∀ q ∈ child :: small, npowBinRec ((n-1)/q) (g : ZMod n) ≠ 1) : n.Prime := by
  obtain ⟨factor, prime, one, proper⟩ := cert
  simp only [binary_pow_eq] at one proper
  apply lucas_primality n (g : ZMod n) one
  intro q hq hd
  apply proper q
  exact prime_mem_factors hq (child :: small) (List.forall_mem_cons.mpr ⟨childPrime, prime⟩)
    (by simpa only [List.prod_cons, factor] using hd)

structure PrimeNode where
  n : ℕ
  witness : ℕ
  child : ℕ
  rest : List ℕ

def knownFactors (known factors : List ℕ) : Prop :=
  ∀ r ∈ factors, if r ≤ 4096 then r.Prime else r ∈ known

instance (known factors : List ℕ) : Decidable (knownFactors known factors) := by
  unfold knownFactors
  infer_instance

private theorem prime_factors {known factors : List ℕ} (hp : ∀ r ∈ known, Nat.Prime r)
    (ok : knownFactors known factors) : ∀ r ∈ factors, Nat.Prime r := by
  intro r hr
  have certified := ok r hr
  split at certified
  · exact certified
  · exact hp r certified

def nodeValid (known : List ℕ) (c : PrimeNode) : Prop :=
  c.child * c.rest.prod = c.n - 1 ∧ knownFactors known (c.child :: c.rest) ∧
  npowBinRec (c.n - 1) (c.witness : ZMod c.n) = 1 ∧
  ∀ r ∈ c.child :: c.rest, npowBinRec ((c.n - 1) / r) (c.witness : ZMod c.n) ≠ 1

instance (known : List ℕ) (c : PrimeNode) : Decidable (nodeValid known c) := by
  unfold nodeValid
  infer_instance

def checkNodes (known : List ℕ) : List PrimeNode → Bool
  | [] => true
  | c :: cs => decide (nodeValid (cs.map PrimeNode.n ++ known) c) && checkNodes known cs

theorem certified_primes (cs : List PrimeNode) (known : List ℕ) (ps : ∀ r ∈ known, Nat.Prime r)
    (ok : checkNodes known cs = true) : ∀ r ∈ cs.map PrimeNode.n ++ known, Nat.Prime r := by
  induction cs with
  | nil => exact ps
  | cons c cs ih =>
    simp only [checkNodes, Bool.and_eq_true, decide_eq_true_eq] at ok
    have earlier := ih ok.2
    obtain ⟨eq, valid, pow, checks⟩ := ok.1
    have ps := prime_factors earlier valid
    simp only [List.map_cons, List.cons_append, List.forall_mem_cons]
    exact ⟨lucas_step (ps _ List.mem_cons_self) c.rest c.witness
      ⟨eq, fun r hr => ps _ (List.mem_cons_of_mem _ hr), pow, checks⟩, earlier⟩

private abbrev p : ℕ := 301101000010109901101
private abbrev q : ℕ := 101099011010000101103

private def nodes : List PrimeNode := [
  ⟨301101000010109901101, 2, 39013332643609, [2, 2, 5, 5, 113, 683]⟩,
  ⟨101099011010000101103, 5, 8820248497, [2, 5731074983]⟩,
  ⟨39013332643609, 17, 61683889, [2, 2, 2, 3, 19, 19, 73]⟩,
  ⟨8820248497, 10, 183755177, [2, 2, 2, 2, 3]⟩,
  ⟨5731074983, 5, 114773, [2, 24967]⟩,
  ⟨183755177, 3, 1087, [2, 2, 2, 11, 17, 113]⟩,
  ⟨61683889, 23, 10799, [2, 2, 2, 2, 3, 7, 17]⟩,
  ⟨114773, 2, 4099, [2, 2, 7]⟩,
  ⟨24967, 3, 73, [2, 3, 3, 19]⟩,
  ⟨10799, 19, 5399, [2]⟩,
  ⟨5399, 7, 2699, [2]⟩,
  ⟨4099, 2, 683, [2, 3]⟩]

set_option maxRecDepth 30000 in
private theorem primes : ∀ r ∈ nodes.map PrimeNode.n ++ [], Nat.Prime r :=
  certified_primes nodes [] (by simp) (by decide +kernel)

private def rootDigits : List ℕ := [1, 0, 1, 1, 0, 9, 9, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 3]
private def squareDigits : List ℕ := [1, 0, 2, 2, 1, 0, 1, 0, 0, 2, 7, 2, 0, 0, 1, 2, 1, 6, 6, 2, 9, 2, 6, 6, 2, 0, 2, 8, 8, 0, 7, 0, 2, 2, 1, 8, 1, 6, 6, 0, 9]

private theorem root_digits : Nat.digits 10 p = rootDigits := by
  have repr : Nat.ofDigits 10 rootDigits = p := by decide
  rw [← repr]
  exact Nat.digits_ofDigits 10 (by decide) rootDigits (by decide)
    (by intro h; exact (by decide : (3 : ℕ) ≠ 0))

private theorem square_digits : Nat.digits 10 (p^2) = squareDigits := by
  have repr : Nat.ofDigits 10 squareDigits = p^2 := by decide
  rw [← repr]
  exact Nat.digits_ofDigits 10 (by decide) squareDigits (by decide)
    (by intro h; exact (by decide : (9 : ℕ) ≠ 0))

private theorem qualifies : IsTerm p := by
  refine ⟨primes _ (by decide), q, primes _ (by decide), ?_, by decide, ?_⟩
  · unfold reverseDecimal
    rw [square_digits]
    decide
  · unfold reverseDecimal
    rw [root_digits]
    decide

/-- The same qualifying prime has a leading three and contains the prohibited digit three. -/
theorem both_fail :
    (¬ ∀ n : ℕ, IsTerm n → outerDigitsOne n) ∧
    (¬ ∀ n : ℕ, IsTerm n → allowedDigits n) := by
  constructor
  · intro claim
    have lead := (claim p qualifies).1
    rw [root_digits] at lead
    exact (by decide : rootDigits.getLast? ≠ some 1) lead
  · intro claim
    have digits := claim p qualifies
    unfold allowedDigits at digits
    rw [root_digits] at digits
    exact (by decide : ¬ (3=0 ∨ 3=1 ∨ 3=2 ∨ 3=9)) (digits 3 (by decide))

end DecimalSquarePair

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a394382.main) :=
  fun h => DecimalSquarePair.both_fail.1 h.1
