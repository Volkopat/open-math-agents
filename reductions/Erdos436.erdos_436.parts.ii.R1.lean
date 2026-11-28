import FormalConjectures.ErdosProblems.«436»

-- Reduction Erdos436.erdos_436.parts.ii.R1 of Erdős Problem 436, part ii
-- Credit: @LordMike
-- Credit: @NickLeko (PR #3655): H1 is H1 of the merged Erdos436.erdos_436.variants.three_three.R1,
-- and lift_sum and upper below generalise its lemmas lift_sum and upper from 3 to k.
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Three consecutive `k`th power residues, from a statement about additive labelings

`Λ(k, 3) < ∞` for every odd `k ≥ 3` is reduced to a statement with no primes `p`, no residues
and no limsup: every completely additive map from the positive integers to `ZMod k` vanishes at
three successive integers below a bound that depends only on `k`.

* `H1` (known, finite): the case `k = 3` with the sharp bound `23532` of Lehmer, Lehmer, Mills
  and Selfridge. It is the same statement, character for character, as `H1` of the merged
  reduction `Erdos436.erdos_436.variants.three_three.R1`, which is proved upstream.
* `H2` (open): for every odd `k ≥ 5` there is `N` such that every labeling `w` of the primes by
  `ZMod k`, extended additively over prime factors with multiplicity, has `n ≤ N` with zero sums
  at `n`, `n + 1` and `n + 2`.

`main`: for a prime `p > N + 2` take a generator `g` of the units of `ZMod p` and label each
prime `q < p` by its discrete logarithm modulo `k`. If the label sum of `n` is zero then the
discrete logarithm of `n` is a multiple of `k`, so `n` is a `k`th power modulo `p`. Hence
`r(k, 3, p) ≤ N` for all large primes `p`, whatever `gcd(k, p - 1)` is.

`H2` is not weaker than the target in strength: by Kummer theory and Chebotarev every labeling of
the primes up to `N + 2` is realised by the `k`th power residue character of infinitely many
primes `p ≡ 1 (mod k)` (this is `H2` of the `three_three` reduction for `k = 3`), so `H2` is
equivalent to the target for odd `k ≥ 5`. The gain is that the open part is now purely
combinatorial.
-/

namespace OMA.R_Erdos436_erdos_436_parts_ii_R1
open Filter Erdos436

/-- Every labeling of the small primes modulo three has three successive zero sums. -/
def H1 : Prop :=
  ∀ w : ℕ → ZMod 3, ∃ n ∈ Finset.Icc 1 23532,
    (n.primeFactorsList.map w).sum = 0 ∧ ((n+1).primeFactorsList.map w).sum = 0 ∧
      ((n+2).primeFactorsList.map w).sum = 0

/-- For odd `k ≥ 5`, every labeling of the primes modulo `k` has three successive zero sums
below a bound depending only on `k`. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → Odd k → ∃ N : ℕ, ∀ w : ℕ → ZMod k, ∃ n ∈ Finset.Icc 1 N,
    (n.primeFactorsList.map w).sum = 0 ∧ ((n+1).primeFactorsList.map w).sum = 0 ∧
      ((n+2).primeFactorsList.map w).sum = 0

lemma lift_sum {p : ℕ} [Fact p.Prime] (g : (ZMod p)ˣ) (e : ℕ → ℤ)
    (l : List ℕ) (h : ∀ q ∈ l, ((g ^ e q : (ZMod p)ˣ) : ZMod p) = q) :
    ((g ^ (l.map e).sum : (ZMod p)ˣ) : ZMod p) = l.prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons,List.sum_cons,List.prod_cons,zpow_add,Units.val_mul,Nat.cast_mul]
    rw [h q (by simp),ih (fun a ha => h a (by simp [ha]))]

lemma upper {k N : ℕ}
    (search : ∀ w : ℕ → ZMod k, ∃ n ∈ Finset.Icc 1 N,
      (n.primeFactorsList.map w).sum = 0 ∧ ((n+1).primeFactorsList.map w).sum = 0 ∧
        ((n+2).primeFactorsList.map w).sum = 0)
    {p : ℕ} (hp : p.Prime) (hbig : N + 2 < p) :
    r k 3 p ≤ N := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  let unit (q : ℕ) : (ZMod p)ˣ := if h : (q : ZMod p) ≠ 0 then Units.mk0 _ h else 1
  have hexp (q : ℕ) : ∃ t : ℤ, g ^ t = unit q := hg (unit q)
  choose e he using hexp
  have nz {n : ℕ} (hn : 0 < n) (hs : n ≤ N + 2) : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun d => (Nat.not_le.mpr (hs.trans_lt hbig)) (Nat.le_of_dvd hn d)
  have power {n : ℕ} (hn : 0 < n) (hs : n ≤ N + 2)
      (hc : (n.primeFactorsList.map (fun q => (e q : ZMod k))).sum = 0) :
      IsPowerResidue k p n := by
    have hc' : (((n.primeFactorsList.map e).sum : ℤ) : ZMod k) = 0 := by
      simpa [List.map_map, Function.comp_def] using hc
    obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).mp hc'
    have h := lift_sum g e n.primeFactorsList (fun q hq => by
      rw [he]
      simp [unit,nz (Nat.pos_of_mem_primeFactorsList hq)
        ((Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hq)).trans hs)])
    rw [Nat.prod_primeFactorsList hn.ne', ha, mul_comm, zpow_mul] at h
    exact ⟨nz hn hs, ((g ^ a : (ZMod p)ˣ) : ZMod p), by simpa using h⟩
  obtain ⟨n,hi,hn,hn',hn''⟩ := search (fun q => (e q : ZMod k))
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hi
  have hr : 1 ≤ n ∧ ∀ i < 3, IsPowerResidue k p (n+i) := by
    refine ⟨hl,?_⟩
    intro i hi
    interval_cases i
    · simpa using power (by omega) (by omega) hn
    · exact power (by omega) (by omega) hn'
    · exact power (by omega) (by omega) hn''
  exact (iInf₂_le n hr).trans (by exact_mod_cast hu)

lemma finite_of_search {k N : ℕ}
    (search : ∀ w : ℕ → ZMod k, ∃ n ∈ Finset.Icc 1 N,
      (n.primeFactorsList.map w).sum = 0 ∧ ((n+1).primeFactorsList.map w).sum = 0 ∧
        ((n+2).primeFactorsList.map w).sum = 0) :
    runLimsup k 3 < ⊤ := by
  rw [runLimsup, Filter.limsup_eq]
  refine lt_of_le_of_lt (sInf_le (a := (N : ℕ∞)) ?_) (ENat.natCast_lt_top N)
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_gt_atTop (N + 2)] with p hp hprime
  exact upper search hprime hp

theorem main : H1 → H2 → type_of% @Erdos436.erdos_436.parts.ii := by
  intro h3 h5 k hk hodd
  by_cases h : k = 3
  · subst h
    exact finite_of_search h3
  · have hk5 : 5 ≤ k := by
      obtain ⟨m, rfl⟩ := hodd
      omega
    obtain ⟨N, hN⟩ := h5 k hk5 hodd
    exact finite_of_search hN

end OMA.R_Erdos436_erdos_436_parts_ii_R1
