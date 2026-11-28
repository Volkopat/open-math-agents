import OMAStatements.S_mo_267651
import Mathlib

-- Problem mo-267651: only finitely many ordered pairs (p, q) of distinct primes have the property that the
-- progression p, p + q, p + 2q, ... contains only finitely many primes.
-- Upstream: statements/mo-267651.lean (declaration OMA.S_mo_267651.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: there are no such pairs at all. If p and q are distinct primes, then p is a unit modulo q, so by
-- Dirichlet's theorem on primes in arithmetic progressions there are primes r congruent to p modulo q that
-- are larger than any given bound. Each such r >= p has the form p + k q, so the progression contains
-- infinitely many primes. Hence the set in the statement is empty, and in particular finite.

theorem OMA.solution : type_of% @OMA.S_mo_267651.main := by
  apply Set.Finite.subset Set.finite_empty
  rintro ⟨p, q⟩ ⟨hp, hq, hne, hfin⟩
  exfalso
  have hp' : Nat.Prime p := hp
  have hq' : Nat.Prime q := hq
  have hne' : p ≠ q := hne
  have hq0 : NeZero q := ⟨hq'.ne_zero⟩
  have hunit : IsUnit ((p : ℕ) : ZMod q) :=
    (ZMod.isUnit_iff_coprime p q).mpr ((Nat.coprime_primes hp' hq').mpr hne')
  refine Set.infinite_of_forall_exists_gt (fun n => ?_) hfin
  obtain ⟨r, hr, hrp, hrmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (max n p)
  have hle : p ≤ r := le_of_lt (lt_of_le_of_lt (le_max_right n p) hr)
  have hmod : p ≡ r [MOD q] := ((ZMod.natCast_eq_natCast_iff r p q).mp hrmod).symm
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
  refine ⟨r, ⟨hrp, k, ?_⟩, lt_of_le_of_lt (le_max_left n p) hr⟩
  show r = p + k * q
  rw [mul_comm]
  omega
