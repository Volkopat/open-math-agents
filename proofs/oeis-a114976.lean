import OMAStatements.S_oeis_a114976
import Mathlib

open Finset OMA.S_oeis_a114976

/- At the two endpoint means, the singleton is the only possible nonempty subset. -/
private abbrev meanPrimeFamily (n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter fun S => S.Nonempty ∧ S.card ∣ ∑ x ∈ S, x ∧
    (∑ x ∈ S, x) / S.card ∣ n

private lemma mean_singleton_mem {d n : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) (hdiv : d ∣ n) :
    {d} ∈ meanPrimeFamily n := by
  simp [meanPrimeFamily, hd, hdn, hdiv]

private lemma mean_prime_endpoints {n : ℕ} (hp : n.Prime) {S : Finset ℕ}
    (hS : S ∈ meanPrimeFamily n) : S = {1} ∨ S = {n} := by
  obtain ⟨hsub, hnonempty, hcard_dvd, hdiv⟩ := mem_filter.mp hS
  have hb := mem_powerset.mp hsub
  have hprod := Nat.div_mul_cancel hcard_dvd
  rcases (Nat.dvd_prime hp).mp hdiv with h | h
  · rw [h, one_mul] at hprod
    have hlow : ∀ i ∈ S, 1 ≤ i := fun i hi => (mem_Icc.mp (hb hi)).1
    have hsum : (∑ _i ∈ S, 1) = ∑ i ∈ S, i := by simpa using hprod
    exact Or.inl <| eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨hnonempty, fun i hi => ((sum_eq_sum_iff_of_le hlow).mp hsum i hi).symm⟩
  · rw [h] at hprod
    have hle : ∀ i ∈ S, i ≤ n := fun i hi => (mem_Icc.mp (hb hi)).2
    have hsum : (∑ i ∈ S, i) = ∑ _i ∈ S, n := by simpa [Nat.mul_comm] using hprod.symm
    exact Or.inr <| eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨hnonempty, (sum_eq_sum_iff_of_le hle).mp hsum⟩

private theorem subset_mean_prime_iff (n : ℕ) (hn : 1 ≤ n) : a n = 2 ↔ n.Prime := by
  change (meanPrimeFamily n).card = 2 ↔ n.Prime
  constructor
  · intro hc
    by_contra hnp
    by_cases h1 : n = 1
    · subst n
      exact (by decide : (meanPrimeFamily 1).card ≠ 2) hc
    obtain ⟨d, hdvd, hd, hdn⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
    have hsub : ({{1}, {d}, {n}} : Finset (Finset ℕ)) ⊆ meanPrimeFamily n := by
      intro S hS
      simp only [mem_insert, mem_singleton] at hS
      rcases hS with rfl | rfl | rfl
      · exact mean_singleton_mem (by omega) hn (one_dvd _)
      · exact mean_singleton_mem (by omega) hdn.le hdvd
      · exact mean_singleton_mem hn le_rfl (dvd_refl _)
    have hcnt := card_le_card hsub
    have hd1 : d ≠ 1 := by omega
    have hdn' : d ≠ n := by omega
    simp [Ne.symm hd1, hdn', Ne.symm h1] at hcnt
    omega
  · intro hp
    have hfamily : meanPrimeFamily n = {{1}, {n}} := by
      ext S
      simp only [mem_insert, mem_singleton]
      refine ⟨mean_prime_endpoints hp, ?_⟩
      rintro (rfl | rfl)
      · exact mean_singleton_mem le_rfl hn (one_dvd _)
      · exact mean_singleton_mem hn le_rfl (dvd_refl _)
    simp [hfamily, Ne.symm hp.ne_one]

/- Partition the subsets by their mean. -/
private lemma subset_mean_partition {n : ℕ} (hn : 1 ≤ n) :
    a n = ∑ d ∈ n.divisors, ((Icc 1 n).powerset.filter
      (fun S => S.Nonempty ∧ (∑ x ∈ S, x) = S.card*d)).card := by
  let mean (S : Finset ℕ) := (∑ x ∈ S, x) / S.card
  let good := (Icc 1 n).powerset.filter
    (fun S => S.Nonempty ∧ S.card ∣ ∑ x ∈ S, x ∧ mean S ∣ n)
  have maps : (good : Set (Finset ℕ)).MapsTo mean n.divisors := by
    intro S hS
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hS).2.2.2, by omega⟩
  change good.card = _
  rw [card_eq_sum_card_fiberwise maps]
  apply sum_congr rfl
  intro d hd
  congr 1
  ext S
  simp only [good, mem_filter]
  constructor
  · rintro ⟨⟨hsub, hne, hdvd, _⟩, hm⟩
    refine ⟨hsub, hne, ?_⟩
    rw [← hm]
    exact (Nat.mul_div_cancel' hdvd).symm
  · rintro ⟨hsub, hne, hs⟩
    have hm : mean S = d := by
      simp [mean, hs, hne.card_pos]
    exact ⟨⟨hsub, hne, ⟨d, hs⟩, hm ▸ (Nat.mem_divisors.mp hd).1⟩, hm⟩

/- Insertion and removal of d preserve mean d. The unpaired nonempty subset is the singleton {d}. -/
private lemma oma_subset_mean_odd {n d : ℕ} (hd₁ : 1 ≤ d) (hdn : d ≤ n) :
    Odd (((Icc 1 n).powerset.filter (fun S => S.Nonempty ∧ (∑ x ∈ S, x) = S.card * d)).card) := by
  let A := (Icc 1 n).powerset.filter (fun S => d ∉ S ∧ (∑ x ∈ S, x) = S.card*d)
  have memA {S : Finset ℕ} : S ∈ A ↔ S ⊆ Icc 1 n ∧ d ∉ S ∧ (∑ x ∈ S, x) = S.card*d := by
    simp [A]
  have empty : ∅ ∈ A := memA.mpr (by simp)
  have part : (Icc 1 n).powerset.filter (fun S => S.Nonempty ∧ (∑ x ∈ S, x) = S.card*d) =
      (A.erase ∅) ∪ A.image (insert d) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_union, mem_erase, mem_image]
    constructor
    · rintro ⟨hsub,hne,hmean⟩
      by_cases h : d ∈ S
      · right
        refine ⟨S.erase d, memA.mpr ⟨(erase_subset ..).trans hsub, by simp, ?_⟩,
          insert_erase h⟩
        have hsum := sum_erase_add S (fun x => x) h
        have hcard := card_erase_add_one h
        rw [← hcard, Nat.add_mul] at hmean
        omega
      · exact Or.inl ⟨hne.ne_empty, memA.mpr ⟨hsub,h,hmean⟩⟩
    · rintro (⟨hne, h⟩ | ⟨U, hU,rfl⟩)
      · have hU := memA.mp h
        exact ⟨hU.1, nonempty_iff_ne_empty.mpr hne, hU.2.2⟩
      · obtain ⟨hsub,hd,hmean⟩ := memA.mp hU
        refine ⟨insert_subset (mem_Icc.mpr ⟨hd₁,hdn⟩) hsub, insert_nonempty .., ?_⟩
        rw [sum_insert hd, card_insert_of_notMem hd, hmean, Nat.add_mul]
        omega
  have disj : Disjoint (A.erase ∅) (A.image (insert d)) := by
    apply disjoint_left.mpr
    intro S hS him
    obtain ⟨U,_,rfl⟩ := mem_image.mp him
    exact (memA.mp (mem_of_mem_erase hS)).2.1 (mem_insert_self ..)
  have injective : Set.InjOn (insert d) (A : Set (Finset ℕ)) := by
    intro S hS U hU heq
    have hs := (memA.mp hS).2.1
    have hu := (memA.mp hU).2.1
    simpa [hs, hu] using congrArg (fun V : Finset ℕ => V.erase d) heq
  rw [part, card_union_of_disjoint disj, card_image_of_injOn injective]
  have hsize := card_erase_add_one empty
  exact ⟨(A.erase ∅).card, by omega⟩

/- The divisor count is odd exactly when every prime exponent is even. -/
private lemma oma_divisors_odd_iff_square {n : ℕ} (hn : n ≠ 0) :
    Odd n.divisors.card ↔ IsSquare n := by
  have allOdd (s : Finset ℕ) (f : ℕ → ℕ) :
      Odd (∏ p ∈ s, f p) ↔ ∀ p ∈ s, Odd (f p) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert p s hp ih => simp [hp, Nat.odd_mul, ih]
  rw [Nat.card_divisors hn, allOdd]
  constructor
  · intro h
    rw [isSquare_iff_exists_sq]
    refine ⟨∏ p ∈ n.primeFactors, p^(n.factorization p / 2), ?_⟩
    rw [← Finset.prod_pow]
    calc
      n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
        simpa only [Finsupp.prod, Nat.support_factorization] using (Nat.prod_factorization_pow_eq_self hn).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        rcases h p hp with ⟨k,hk⟩
        rw [←pow_mul,show n.factorization p / 2 * 2 = n.factorization p by omega]
  · rintro ⟨m, rfl⟩ p _
    rw [←sq, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    exact ⟨m.factorization p, rfl⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a114976.main := by
  refine ⟨subset_mean_prime_iff, ?_⟩
  intro n hn
  let f (d : ℕ) := ((Icc 1 n).powerset.filter (fun S => S.Nonempty ∧ (∑ x ∈ S, x) = S.card*d)).card
  have hodd (d : ℕ) (hd : d ∈ n.divisors) : Odd (f d) := by
    exact oma_subset_mean_odd (Nat.pos_of_mem_divisors hd) (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd))
  have full : n.divisors.filter (fun d => Odd (f d)) = n.divisors := filter_true_of_mem hodd
  rw [subset_mean_partition hn]
  change Odd (∑ d ∈ n.divisors, f d) ↔ IsSquare n
  rw [Finset.odd_sum_iff_odd_card_odd, full]
  exact oma_divisors_odd_iff_square (by omega)
