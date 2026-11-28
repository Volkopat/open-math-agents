import OMAReductions.R_OeisA245211_conjecture_R2
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! A squarefree fixed point of A245211 cannot have an odd prime-power
number of distinct prime factors. -/

namespace A245211

open Finset Function
open OMA.R_OeisA245211_conjecture_R2 (baseProduct_lt large_prime squarefree_fixed_point_product)

section PrimeProducts

variable {ι : Type*}
variable (p : ι → ℕ)

private theorem baseProduct (s : Finset ι) :
    2 ^ s.card * (∏ i ∈ s, p i) ≤ ∏ i ∈ s, (2 * p i + 1) := by
  rw [← prod_const, ← prod_mul_distrib]
  exact prod_le_prod' fun _ _ => Nat.le_succ _

variable [Fintype ι] [DecidableEq ι]

private theorem closed_eq_univ (hp : ∀ i, (p i).Prime) (hinj : Injective p)
    (hf : ι → ι) (hdvd : ∀ i, p i ∣ 2 * p (hf i) + 1)
    (hprod : (∏ i, (2 * p i + 1)) = (2 ^ Fintype.card ι + 1) * ∏ i, p i)
    (s : Finset ι) (hs : s.Nonempty) (hclosed : ∀ i ∈ s, hf i ∈ s) : s = univ := by
  have hd : (∏ i ∈ s, p i) ∣ ∏ i ∈ s, (2 * p i + 1) := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro i _ j _ hne
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hne (hinj h)))
    · intro i hi
      exact (hdvd i).trans (dvd_prod_of_mem _ (hclosed i hi))
  obtain ⟨d, hd⟩ := hd
  have hpos : 0 < ∏ i ∈ s, p i := prod_pos fun i _ => (hp i).pos
  have hds : 2 ^ s.card + 1 ≤ d := by
    have hh := baseProduct_lt p s hs hp
    rw [hd, mul_comm (∏ i ∈ s, p i)] at hh
    exact Nat.succ_le_of_lt ((Nat.mul_lt_mul_right hpos).mp hh)
  let t := univ \ s
  have hdis : Disjoint t s := disjoint_sdiff_self_left
  have hunion : t ∪ s = univ := sdiff_union_of_subset (subset_univ s)
  have hcard : Fintype.card ι = t.card + s.card := by
    rw [← card_union_of_disjoint hdis, hunion, card_univ]
  have hbalance : d * (∏ i ∈ t, (2 * p i + 1)) =
      (2 ^ (t.card + s.card) + 1) * ∏ i ∈ t, p i := by
    rw [← hunion, prod_union hdis, prod_union hdis, hd, hcard] at hprod
    apply Nat.eq_of_mul_eq_mul_right hpos
    linarith only [hprod]
  by_contra hne
  have ht : t.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    apply hne
    simpa [he] using hunion
  have ht2 : 2 ≤ 2 ^ t.card := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) (card_pos.mpr ht))
  have htp : 0 < ∏ i ∈ t, p i := prod_pos fun i _ => (hp i).pos
  have hle := Nat.mul_le_mul hds (baseProduct p t)
  rw [hbalance, pow_add, ← mul_assoc] at hle
  have : (2 ^ s.card + 1) * 2 ^ t.card ≤ 2 ^ t.card * 2 ^ s.card + 1 :=
    le_of_mul_le_mul_right hle htp
  rw [add_mul, one_mul, mul_comm (2 ^ s.card)] at this
  omega

private theorem orbit_length (hp : ∀ i, (p i).Prime) (hinj : Injective p)
    (f : ι → ι) (hdvd : ∀ i, p i ∣ 2 * p (f i) + 1)
    (hprod : (∏ i, (2 * p i + 1)) = (2 ^ Fintype.card ι + 1) * ∏ i, p i)
    [Nonempty ι] : Bijective f ∧ ∀ x, minimalPeriod f x = Fintype.card ι := by
  have hsurj : Surjective f := by
    intro x
    have hi : univ.image f = univ := closed_eq_univ p hp hinj f hdvd hprod _
      (univ_nonempty.image f) (fun i _ => mem_image.mpr ⟨i, mem_univ _, rfl⟩)
    obtain ⟨y, _, hy⟩ := mem_image.mp (hi ▸ mem_univ x)
    exact ⟨y, hy⟩
  have hfinj : Injective f := Finite.injective_iff_surjective.mpr hsurj
  refine ⟨⟨hfinj, hsurj⟩, fun x => ?_⟩
  let r := minimalPeriod f x
  have hr : 0 < r := minimalPeriod_pos_of_mem_periodicPts (hfinj.mem_periodicPts x)
  let s := (range r).image fun i => f^[i] x
  have hs : s.Nonempty := ⟨x, mem_image.mpr ⟨0, mem_range.mpr hr, rfl⟩⟩
  have hclosed (i : ι) (hi : i ∈ s) : f i ∈ s := by
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    apply mem_image.mpr
    refine ⟨(j + 1) % r, mem_range.mpr (Nat.mod_lt _ hr), ?_⟩
    rw [iterate_mod_minimalPeriod_eq, iterate_succ_apply']
  have hu := closed_eq_univ p hp hinj f hdvd hprod s hs hclosed
  have hcard : s.card = r := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj hij
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod (mem_range.mp hi)
      (mem_range.mp hj)).mp hij
  rw [hu, card_univ] at hcard
  exact hcard.symm

end PrimeProducts

private theorem factor_residue_of_prime_power_count {q k ℓ : ℕ} (hq : q.Prime)
    (hl : ℓ.Prime) (hl3 : ℓ ≠ 3) (hdvd : ℓ ∣ 2 ^ (q ^ k) + 1) : (ℓ : ZMod q) = 1 := by
  let : Fact ℓ.Prime := ⟨hl⟩
  have hsum : (2 : ZMod ℓ) ^ (q ^ k) + 1 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff (2 ^ (q ^ k) + 1) ℓ).mpr hdvd
  have hneg : (2 : ZMod ℓ) ^ (q ^ k) = -1 := by linear_combination hsum
  have htwo : (2 : ZMod ℓ) ≠ 0 := by
    intro hz
    simp [hz, zero_pow (pow_ne_zero _ hq.ne_zero)] at hsum
  have hoDvd : orderOf (2 : ZMod ℓ) ∣ 2 * q ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [mul_comm, pow_mul, hneg]
    ring
  have hqDvd : q ∣ orderOf (2 : ZMod ℓ) := by
    by_contra hn
    have hcop := (hq.coprime_iff_not_dvd.mpr hn).symm.pow_right k
    have hdiv := hcop.dvd_of_dvd_mul_right hoDvd
    have hsq := orderOf_dvd_iff_pow_eq_one.mp hdiv
    have h3 : (3 : ZMod ℓ) = 0 := by linear_combination hsq
    have hp3 : ℓ ∣ 3 := (ZMod.natCast_eq_zero_iff 3 ℓ).mp h3
    exact hl3 ((Nat.prime_dvd_prime_iff_eq hl (by decide)).mp hp3)
  obtain ⟨a, ha⟩ := hqDvd.trans (ZMod.orderOf_dvd_card_sub_one htwo)
  have he : ℓ = q * a + 1 := by have := hl.pos; omega
  simp [he]

private theorem factor_without_three {q k d : ℕ} (hq : q.Prime)
    (hdvd : d ∣ 2 ^ (q ^ k) + 1) (h3 : ¬ 3 ∣ d) : (d : ZMod q) = 1 := by
  revert hdvd h3
  induction d using induction_on_primes with
  | zero => simp
  | one => simp
  | prime_mul ℓ d hl ih =>
    intro hdvd h3
    have hne : ℓ ≠ 3 := by rintro rfl; exact h3 (dvd_mul_right ..)
    have hℓ := factor_residue_of_prime_power_count hq hl hne ((dvd_mul_right ℓ d).trans hdvd)
    have hd := ih ((dvd_mul_left d ℓ).trans hdvd) (fun h => h3 (h.trans (dvd_mul_left d ℓ)))
    simp [Nat.cast_mul, hℓ, hd]

private theorem three_divides_pow_add_one {r : ℕ} (ho : Odd r) : 3 ∣ 2 ^ r + 1 := by
  have h : (2 : ZMod 3) = -1 := by decide
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  rw [h, ho.neg_one_pow, neg_add_cancel]

private theorem nine_not_dvd_pow_add_one {r : ℕ} (ho : Odd r) (hr : ¬ 3 ∣ r) :
    ¬ 9 ∣ 2 ^ r + 1 := by
  have hr6 : r % 6 = 1 ∨ r % 6 = 5 := by
    rw [Nat.odd_iff] at ho
    rw [Nat.dvd_iff_mod_eq_zero] at hr
    omega
  have hsmall : (2 : ZMod 9) ^ r = (2 : ZMod 9) ^ (r % 6) := by
    nth_rw 1 [← Nat.mod_add_div r 6]
    rw [pow_add, pow_mul, show (2 : ZMod 9) ^ 6 = 1 by decide, one_pow, mul_one]
  intro h
  have hzero := (ZMod.natCast_eq_zero_iff (2 ^ r + 1) 9).mpr h
  push_cast at hzero
  rw [hsmall] at hzero
  rcases hr6 with h | h
  · rw [h] at hzero
    exact (by decide : (2 : ZMod 9) ^ 1 + 1 ≠ 0) hzero
  · rw [h] at hzero
    exact (by decide : (2 : ZMod 9) ^ 5 + 1 ≠ 0) hzero

private theorem pow_two_add_one_lt_pow_three {r : ℕ} (hr : 2 ≤ r) :
    2 ^ r + 1 < 3 ^ r := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hle : 2 ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by decide) t
  have hpos : 0 < (2 : ℕ) ^ t := by positivity
  norm_num [pow_add]
  omega

private theorem three_divides_coordinate {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (h : 3 ∣ ∏ i, d i) : ∃ i, 3 ∣ d i := by
  obtain ⟨i, _, hi⟩ := ((show Nat.Prime 3 by decide).prime.dvd_finsetProd_iff d).mp h
  exact ⟨i, hi⟩

private theorem other_coordinates_not_dvd_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → ℕ} {i j : ι} (hi : 3 ∣ d i) (hij : j ≠ i) (hprod : ¬ 9 ∣ ∏ k, d k) :
    ¬ 3 ∣ d j := by
  intro hj
  have hm : j ∈ (univ : Finset ι).erase i := mem_erase.mpr ⟨hij, mem_univ _⟩
  have hrest := hj.trans (dvd_prod_of_mem d hm)
  apply hprod
  rw [← mul_prod_erase univ d (mem_univ i)]
  exact mul_dvd_mul hi hrest

private theorem prime_power_cycle_impossible {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {p : ι → ℕ} (hp : ∀ i, (p i).Prime) (hinj : Injective p)
    (hprod : (∏ i, (2 * p i + 1)) = (2 ^ Fintype.card ι + 1) * ∏ i, p i)
    {q k : ℕ} (hq : q.Prime) (ho : Odd q) (hk : 0 < k)
    (hr : Fintype.card ι = q ^ k) : False := by
  let r := Fintype.card ι
  have hrq : q ≤ r := by simpa only [r, hr] using Nat.le_self_pow hk.ne' q
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rw [Nat.odd_iff] at ho
    omega
  have hr3 : 3 ≤ r := hq3.trans hrq
  have hlarge (i : ι) : r < p i := by
    have hb := large_prime p hp (by omega : 2 ≤ r) hprod i
    change 2 ^ (r - 1) < p i at hb
    have hl : r - 1 < 2 ^ (r - 1) := Nat.lt_two_pow_self
    omega
  have hord : Odd r := by simpa only [r, hr] using (show Odd (q ^ k) from ho.pow)
  have hdiv (i : ι) : ∃ j : ι, p i ∣ 2 * p j + 1 := by
    have hd : p i ∣ ∏ j, p j := dvd_prod_of_mem p (mem_univ i)
    have hL : p i ∣ ∏ j, (2 * p j + 1) := by
      rw [hprod]
      exact dvd_mul_of_dvd_right hd _
    obtain ⟨j, _, hj⟩ := ((hp i).prime.dvd_finsetProd_iff (fun j => 2 * p j + 1)).mp hL
    exact ⟨j, hj⟩
  choose f hf using hdiv
  obtain ⟨hbij, hperiod⟩ := orbit_length p hp hinj f hf hprod
  choose d he using hf
  have hprod_d : (∏ i, d i) = 2 ^ r + 1 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < ∏ i, p i from prod_pos fun i _ => (hp i).pos)
    calc
      (∏ i, p i) * (∏ i, d i) = ∏ i, (2 * p (f i) + 1) := by
        rw [← prod_mul_distrib]
        exact prod_congr rfl fun i _ => (he i).symm
      _ = ∏ i, (2 * p i + 1) :=
        Fintype.prod_equiv (Equiv.ofBijective f hbij) _ _ (fun _ => rfl)
      _ = (∏ i, p i) * (2 ^ r + 1) := hprod.trans (mul_comm _ _)
  have hd (i : ι) : d i ∣ 2 ^ (q ^ k) + 1 := by
    rw [← hr, ← hprod_d]
    exact dvd_prod_of_mem d (mem_univ i)
  let z (i : ι) : ZMod q := p i
  have hnz (i : ι) : z i ≠ 0 := by
    intro h
    have hz := (ZMod.natCast_eq_zero_iff (p i) q).mp h
    have heq := (Nat.prime_dvd_prime_iff_eq hq (hp i)).mp hz
    exact (hrq.trans_lt (hlarge i)).ne heq
  have hE (i : ι) : 2 * z (f i) + 1 = (d i : ZMod q) * z i := by
    have hc := congrArg (fun a : ℕ => (a : ZMod q)) (he i)
    change ((2 * p (f i) + 1 : ℕ) : ZMod q) = ((p i * d i : ℕ) : ZMod q) at hc
    push_cast at hc
    simpa [z, mul_comm] using hc
  obtain ⟨x, hx⟩ := three_divides_coordinate d (by rw [hprod_d]; exact three_divides_pow_add_one hord)
  by_cases hq_eq : q = 3
  · subst q
    have zero_step : ∀ b : ZMod 3, 2 * b + 1 = 0 → b = 1 := by decide
    have unit_step : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → 2 * b + 1 = a → a = 2 := by decide
    have d_zero_of_val_one (i : ι) (hi : z i = 1) : 3 ∣ d i := by
      by_contra nh
      have hh := hE i
      rw [factor_without_three hq (hd i) nh, one_mul] at hh
      have heq := unit_step (z i) (z (f i)) (hnz i) (hnz (f i)) hh
      exact (by decide : (1 : ZMod 3) ≠ 2) (hi.symm.trans heq)
    have val_one_of_d_zero (i : ι) (hi : 3 ∣ d i) : z (f i) = 1 := by
      have hh := hE i
      rw [(ZMod.natCast_eq_zero_iff (d i) 3).mpr hi, zero_mul] at hh
      exact zero_step _ hh
    let s := univ.filter fun i => z i = 1
    have hs : s.Nonempty := ⟨f x, mem_filter.mpr ⟨mem_univ _, val_one_of_d_zero x hx⟩⟩
    have hclosed (i : ι) (hi : i ∈ s) : f i ∈ s :=
      mem_filter.mpr ⟨mem_univ _, val_one_of_d_zero i (d_zero_of_val_one i (mem_filter.mp hi).2)⟩
    have hsu := closed_eq_univ p hp hinj f (fun i => ⟨d i, he i⟩) hprod s hs hclosed
    have hthree : 3 ^ r ∣ 2 ^ r + 1 := by
      change 3 ^ Fintype.card ι ∣ 2 ^ r + 1
      rw [← hprod_d, ← card_univ (α := ι), ← prod_const]
      apply prod_dvd_prod_of_dvd
      intro i _
      have hi : i ∈ s := by rw [hsu]; exact mem_univ i
      change i ∈ univ.filter (fun j => z j = 1) at hi
      exact d_zero_of_val_one i (mem_filter.mp hi).2
    exact (not_le_of_gt (pow_two_add_one_lt_pow_three (by omega)))
      (Nat.le_of_dvd (by positivity) hthree)
  · let : Fact q.Prime := ⟨hq⟩
    have hthree : Nat.Prime 3 := by decide
    have h3q : ¬ 3 ∣ q := fun h => hq_eq ((Nat.prime_dvd_prime_iff_eq hthree hq).mp h).symm
    have h3r : ¬ 3 ∣ r := by
      intro h
      change 3 ∣ Fintype.card ι at h
      rw [hr] at h
      exact h3q (hthree.dvd_of_dvd_pow h)
    have h9 : ¬ 9 ∣ ∏ i, d i := by rw [hprod_d]; exact nine_not_dvd_pow_add_one hord h3r
    have hothers (i : ι) (hi : i ≠ x) : (d i : ZMod q) = 1 :=
      factor_without_three hq (hd i) (other_coordinates_not_dvd_three hx hi h9)
    have hfirst : (d x : ZMod q) = 3 := by
      obtain ⟨u, hu⟩ := hx
      have hud : u ∣ d x := hu ▸ dvd_mul_left u 3
      have hu3 : ¬ 3 ∣ u := by
        intro h
        apply h9
        apply dvd_trans _ (dvd_prod_of_mem d (mem_univ x))
        rw [hu]
        exact mul_dvd_mul dvd_rfl h
      rw [hu, Nat.cast_mul, factor_without_three hq (hud.trans (hd x)) hu3, mul_one]
      norm_num
    have htwo : (2 : ZMod q) ≠ 0 := by
      intro hz
      have hdvd := (ZMod.natCast_eq_zero_iff 2 q).mp hz
      have := Nat.le_of_dvd (by decide : 0 < 2) hdvd
      omega
    have hDiv : q - 1 ∣ r - 1 := by
      simpa only [r, hr] using Nat.sub_one_dvd_pow_sub_one q k
    have hpow : (2 : ZMod q) ^ (r - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((ZMod.orderOf_dvd_card_sub_one htwo).trans hDiv)
    let y (i : ℕ) := z (f^[i] x) + 1
    have hyr : y r = y 0 := by
      have hloop : f^[r] x = x := by
        change f^[Fintype.card ι] x = x
        rw [← hperiod x, iterate_minimalPeriod]
      simp [y, hloop]
    have hstep (i : ℕ) (hi : 0 < i) (hir : i < r) : 2 * y (i + 1) = y i := by
      have hne : f^[i] x ≠ x := by
        intro heq
        have hl : i < minimalPeriod f x := (hperiod x).symm ▸ hir
        have h0 : 0 < minimalPeriod f x := by rw [hperiod]; omega
        have := (iterate_eq_iterate_iff_of_lt_minimalPeriod hl h0).mp heq
        omega
      have hh := hE (f^[i] x)
      rw [hothers _ hne, one_mul] at hh
      change 2 * (z (f^[i + 1] x) + 1) = z (f^[i] x) + 1
      rw [iterate_succ_apply']
      linear_combination hh
    have chain (j : ℕ) (hj : j < r) : (2 : ZMod q) ^ j * y r = y (r - j) := by
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', mul_assoc, ih (by omega), show r - j = r - (j + 1) + 1 by omega]
        exact hstep _ (by omega) (by omega)
    have hy1 : y 1 = y 0 := by
      have hh := chain (r - 1) (by omega)
      rw [hpow, one_mul, show r - (r - 1) = 1 by omega, hyr] at hh
      exact hh.symm
    have hz1 : z (f x) = z x := by
      dsimp [y] at hy1
      exact add_right_cancel hy1
    have hzx : z x = 1 := by
      have hh := hE x
      rw [hfirst, hz1] at hh
      linear_combination -hh
    have hy2 := chain (r - 2) (by omega)
    rw [show r - (r - 2) = 2 by omega, hyr] at hy2
    have hy0 : y 0 = 2 := by norm_num [y, hzx]
    rw [hy0, ← pow_succ, show r - 2 + 1 = r - 1 by omega, hpow] at hy2
    dsimp [y] at hy2
    exact hnz _ (by linear_combination -hy2)

/-- No squarefree fixed point has an odd prime-power number of prime factors. -/
theorem no_squarefree_fixed_point_odd_prime_power_count {n q k : ℕ}
    (hs : Squarefree n) (hq : q.Prime) (ho : Odd q) (hk : 0 < k)
    (hr : n.primeFactors.card = q ^ k) : OeisA245211.a n ≠ n := by
  classical
  intro ha
  let P := n.primeFactors
  have hp (p : ℕ) (hm : p ∈ P) : p.Prime := Nat.prime_of_mem_primeFactors hm
  have he : (∏ p ∈ P, (2 * p + 1)) = (2 ^ P.card + 1) * ∏ p ∈ P, p :=
    squarefree_fixed_point_product hs ha
  have hPos : 0 < P.card := hr ▸ pow_pos hq.pos _
  let : Nonempty P := (card_pos.mp hPos).to_subtype
  refine prime_power_cycle_impossible
    (p := fun i : P => (i : ℕ)) (fun i => hp i i.property) Subtype.val_injective ?_ hq ho hk ?_
  · have hc : Fintype.card P = P.card := by simp
    rw [hc]
    calc
      (∏ i : P, (2 * (i : ℕ) + 1)) = ∏ p ∈ P, (2 * p + 1) :=
        Finset.prod_coe_sort P (fun p => 2 * p + 1)
      _ = (2 ^ P.card + 1) * ∏ p ∈ P, p := he
      _ = (2 ^ P.card + 1) * ∏ i : P, (i : ℕ) :=
        congrArg (fun x : ℕ => (2 ^ P.card + 1) * x)
          (Finset.prod_coe_sort P (fun p => p)).symm
  · simpa using hr

end A245211

theorem OMA.solution : OMA.R_OeisA245211_conjecture_R2.H1 := by
  intro n q k hs hq ho hk hr
  exact A245211.no_squarefree_fixed_point_odd_prime_power_count hs hq ho hk hr
