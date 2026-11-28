import OMAReductions.R_Fermat_fermat_number_are_composite_R1
-- Credit: @kofls (shorter proof)
theorem OMA.solution : OMA.R_Fermat_fermat_number_are_composite_R1.H1 := by
  intro n _ _
  have k (q : ℕ) (h : 2 ≤ q ∧ q < 2 ^ 2 ^ n + 1 ∧ (2 ^ 2 ^ n + 1) % q = 0 := by decide +kernel) :
      ¬ Prime n.fermatNumber :=
    Nat.prime_iff.not.1 (Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h.2.2) h.1 h.2.1)
  interval_cases n
  exacts [k 641, k 274177, k 59649589127497217, k 1238926361552897, k 2424833, k 45592577, k 319489,
    k 114689, k 2710954639361, k 116928085873074369829035993834596371340386703423373313,
    k 1214251009, k 825753601, k 31065037602817, k 13631489, k 70525124609]
