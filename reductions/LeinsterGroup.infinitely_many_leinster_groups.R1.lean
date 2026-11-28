import FormalConjectures.Wikipedia.LeinsterGroup
import Mathlib

/-!
# Infinitely many Mersenne primes implies infinitely many Leinster groups

`H1` (known, Euclid): `2^p - 1` prime implies `2^(p-1) (2^p - 1)` perfect.
`H2` (open core): the Mersenne prime conjecture, `{p | 2 ^ p - 1 prime}` is infinite.
Sketch: Euclid gives the perfect number `2 ^ (p - 1) * (2 ^ p - 1)`; the cyclic group of
perfect order is Leinster (Leinster 2001), and these orders are unbounded.
-/

namespace OMA.R_LeinsterGroup_infinitely_many_leinster_groups_R1

open ArithmeticFunction

/-- Euclid: a Mersenne prime `2^p - 1` gives the even perfect number `2^(p-1) (2^p - 1)`. -/
def H1 : Prop :=
  ∀ p : ℕ, (2 ^ p - 1).Prime → Nat.Perfect (2 ^ (p - 1) * (2 ^ p - 1))

/-- The Mersenne prime conjecture: infinitely many exponents `p` make `2^p - 1` prime. -/
def H2 : Prop :=
  {p : ℕ | (2 ^ p - 1).Prime}.Infinite

theorem subset_pow_eq_one {G : Type*} [Group G] (H : Subgroup G) [Finite H] :
    ((H : Set G)) ⊆ {a : G | a ^ Nat.card H = 1} := by
  intro x hx
  show x ^ Nat.card H = 1
  have h1 : (⟨x, hx⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
  exact congrArg Subtype.val h1

theorem card_pow_set_le {G : Type*} [Group G] [Fintype G] [IsCyclic G] {n : ℕ} (hn : 0 < n) :
    Set.ncard {a : G | a ^ n = 1} ≤ n := by
  classical
  have e : {a : G | a ^ n = 1} = ↑(Finset.univ.filter (fun a : G => a ^ n = 1)) := by
    ext a
    simp
  rw [e, Set.ncard_coe_finset]
  exact IsCyclic.card_pow_eq_one_le hn

theorem eq_of_card_eq {G : Type*} [Group G] [Fintype G] [IsCyclic G] (H K : Subgroup G)
    (h : Nat.card H = Nat.card K) : H = K := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hS : ∀ L : Subgroup G, Nat.card L = Nat.card H →
      (L : Set G) = {a : G | a ^ Nat.card H = 1} := by
    intro L hL
    have hsub : (L : Set G) ⊆ {a : G | a ^ Nat.card H = 1} := by
      rw [← hL]
      exact subset_pow_eq_one L
    apply Set.eq_of_subset_of_ncard_le hsub
    have e : (L : Set G).ncard = Nat.card L := (Nat.card_coe_set_eq (L : Set G)).symm
    rw [e, hL]
    exact card_pow_set_le hpos
  apply SetLike.coe_injective
  rw [hS H rfl, hS K h.symm]

/-- Cyclic groups of perfect order are Leinster. -/
theorem cyclic_leinster (G : Type*) [Group G] [Fintype G] [IsCyclic G]
    (hp : Nat.Perfect (Fintype.card G)) : LeinsterGroup.IsLeinster G := by
  classical
  obtain ⟨hsum, hpos⟩ : (∑ i ∈ Nat.properDivisors (Fintype.card G), i = Fintype.card G) ∧
      0 < Fintype.card G := hp
  have hdiv : ∑ i ∈ Nat.divisors (Fintype.card G), i = 2 * Fintype.card G := by
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, hsum]
    omega
  unfold LeinsterGroup.IsLeinster
  rw [← hdiv]
  refine Finset.sum_bij (fun H _ => Nat.card H.1) ?_ ?_ ?_ ?_
  · intro H _
    refine Nat.mem_divisors.2 ⟨?_, hpos.ne'⟩
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card H.1
  · intro H₁ _ H₂ _ h
    exact Subtype.ext (eq_of_card_eq H₁.1 H₂.1 h)
  · intro d hd
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.1 hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hpos
    have htot : 0 < Nat.totient d := Nat.totient_pos.2 hdpos
    have hcard := IsCyclic.card_orderOf_eq_totient hdvd
    have hne : 0 < (Finset.univ.filter (fun a : G => orderOf a = d)).card := by
      rw [hcard]
      exact htot
    obtain ⟨a, ha⟩ := Finset.card_pos.1 hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hnorm : (Subgroup.zpowers a).Normal := inferInstance
    refine ⟨⟨Subgroup.zpowers a, hnorm⟩, Finset.mem_univ _, ?_⟩
    show Nat.card (Subgroup.zpowers a) = d
    rw [Nat.card_zpowers, ha]
  · intro H _
    rfl

/-- Euclid: `2 ^ k * (2 ^ (k + 1) - 1)` is perfect when `2 ^ (k + 1) - 1` is prime. -/
theorem euclid_perfect (k : ℕ) (hq : (2 ^ (k + 1) - 1).Prime) :
    Nat.Perfect (2 ^ k * (2 ^ (k + 1) - 1)) := by
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hodd : Odd (2 ^ (k + 1) - 1) := by
    rw [Nat.odd_iff]
    have : 2 ^ (k + 1) % 2 = 0 := by simp [Nat.pow_mod]
    omega
  have hcop : Nat.Coprime (2 ^ k) (2 ^ (k + 1) - 1) :=
    (Nat.Coprime.pow_left k ((Nat.coprime_two_left).2 hodd))
  have hpos : 0 < 2 ^ k * (2 ^ (k + 1) - 1) := Nat.mul_pos (by positivity) hq.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow Nat.prime_two,
    sigma_one_apply, hq.sum_divisors, Nat.geomSum_eq (le_refl 2)]
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [Nat.sub_add_cancel h1]
  simp only [Nat.add_one_sub_one, Nat.div_one]
  rw [h2]
  ring

/-- `H1` holds (so its step closes at once). -/
theorem H1_holds : H1 := by
  intro p hp
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; exact absurd hp (by norm_num)
    · omega⟩
  simpa using euclid_perfect k hp

theorem main : H1 → H2 → type_of% @LeinsterGroup.infinitely_many_leinster_groups := by
  intro hE hH ⟨N, hN⟩
  obtain ⟨p, hp, hpN⟩ := Set.Infinite.exists_gt hH (N + 1)
  have hpr : (2 ^ p - 1).Prime := hp
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  set m := 2 ^ k * (2 ^ (k + 1) - 1) with hm
  have hperf : Nat.Perfect m := by simpa using hE (k + 1) hpr
  have hm0 : 0 < m := hperf.2
  have : NeZero m := ⟨hm0.ne'⟩
  have hcard : Fintype.card (Multiplicative (ZMod m)) = m := by
    simp [ZMod.card]
  have hL : LeinsterGroup.IsLeinster (Multiplicative (ZMod m)) :=
    cyclic_leinster _ (by rw [hcard]; exact hperf)
  have hlt := hN (Multiplicative (ZMod m)) inferInstance inferInstance hL
  rw [hcard] at hlt
  have hk : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
  have hge : 2 ^ (k + 1) - 1 ≤ m := Nat.le_mul_of_pos_left _ (by positivity)
  omega

end OMA.R_LeinsterGroup_infinitely_many_leinster_groups_R1
