import OMAReductions.R_opg_subgroup_formed_by_elements_of_order_dividing_n_R1

theorem OMA.solution :
    OMA.R_opg_subgroup_formed_by_elements_of_order_dividing_n_R1.H1 := by
  classical
  intro G _ _ n L K normal p a hp hn hd roots
  letI : K.Normal := normal
  letI : Fact p.Prime := ⟨hp⟩
  have hdiv : p ^ a ∣ Nat.card (L ⧸ K) := by
    apply Nat.dvd_of_mul_dvd_mul_right (Nat.card_pos : 0 < Nat.card K)
    calc
      p ^ a * Nat.card K = n := hn.symm
      _ ∣ Nat.card L := hd
      _ = Nat.card (L ⧸ K) * Nat.card K := K.card_eq_card_quotient_mul_card_subgroup
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime p hdiv
  let P := Q.comap (QuotientGroup.mk' K)
  have hP : Nat.card P = n := by
    calc
      Nat.card P = Nat.card (K × Q) :=
        Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet K (Q : Set (L ⧸ K)))
      _ = Nat.card K * Nat.card Q := Nat.card_prod K Q
      _ = n := by rw [hQ, mul_comm, ← hn]
  let H := P.map L.subtype
  have hH : Nat.card H = n := (L.card_subtype P).trans hP
  have hsub : (H : Set G) ⊆ {x : G | x ^ n = 1} := by
    intro x hx
    change x ^ n = 1
    rw [← hH]
    exact orderOf_dvd_iff_pow_eq_one.mp (H.orderOf_dvd_natCard hx)
  have heq : (H : Set G) = {x : G | x ^ n = 1} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [roots]; exact hH.ge)
  refine ⟨H, fun x => ?_⟩
  change x ∈ (H : Set G) ↔ x ∈ {y : G | y ^ n = 1}
  rw [heq]
