import OMAReductions.R_Erdos542_erdos_542_variants_only_two_R1

/-!
A set containing four has reciprocal sum at most one for every n ≥ 12. After
removing four, a member has the form u or 2u for an odd u > n/4, with each u
used at most once. For n ≥ 72 we bound the odd reciprocal sum by a decreasing
sequence of interval sums. For 12 ≤ n ≤ 71 at least one of x and 3x is absent,
where x = 2⌊n/8⌋+1. Its contribution can come only from its double.

The remaining problems choose just the lower half of the set. Every upper-half
member is an integer divisible by none of the chosen lower-half members.
-/

-- Credit: @Dolcruz

namespace OMA.R_Erdos542_erdos_542_variants_only_two_R1_H2_R1

open Finset

private theorem envelope_step (k : ℕ) :
    ∑ j ∈ Ico (k + 1) (4 * (k + 1) + 4), ((1 : ℚ) / (2*j+1 : ℕ)) ≤
      ∑ j ∈ Ico k (4 * k + 4), ((1 : ℚ) / (2*j+1 : ℕ)) := by
  let z := 4 * k + 4
  have hz : k + 1 ≤ z := by dsimp [z]; omega
  have hsingle (j : ℕ) (hj : z ≤ j) :
      ((1 : ℚ) / (2*j+1 : ℕ)) ≤ ((1 : ℚ) / (2 * k + 1 : ℕ)) / 4 := by
    push_cast
    rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
    dsimp [z] at hj
    exact_mod_cast (by omega : (2*k+1)*4 ≤ 2*j+1)
  have htail : ∑ j ∈ Ico z (z+4), ((1 : ℚ) / (2*j+1 : ℕ)) ≤ ((1 : ℚ) / (2*k+1 : ℕ)) := by
    calc
      _ ≤ ∑ _j ∈ Ico z (z+4), ((1 : ℚ) / (2*k+1 : ℕ)) / 4 :=
        sum_le_sum fun j hj => hsingle j (mem_Ico.mp hj).1
      _ = _ := by simp; ring
  change ∑ j ∈ Ico (k+1) (z+4), ((1 : ℚ) / (2*j+1 : ℕ)) ≤ ∑ j ∈ Ico k z, ((1 : ℚ) / (2*j+1 : ℕ))
  rw [← sum_Ico_consecutive _ hz (by omega : z ≤ z+4),
    ← sum_Ico_consecutive _ (by omega : k ≤ k+1) hz]
  simpa [add_comm] using add_le_add_left htail (∑ j ∈ Ico (k+1) z, ((1 : ℚ) / (2*j+1 : ℕ)))

private theorem envelope_bound (k : ℕ) (hk : 9 ≤ k) :
    ∑ j ∈ Ico k (4*k+4), ((1 : ℚ) / (2*j+1 : ℕ)) ≤ 3/4 := by
  induction k, hk using Nat.le_induction with
  | base => decide +kernel
  | succ k _ ih => exact (envelope_step k).trans ih

private theorem pool_small :
    ∀ n ∈ Icc 12 71, ∀ e ∈ ({2*(n/8)+1, 3*(2*(n/8)+1)} : Finset ℕ),
      ∑ j ∈ ((range (n+1)).filter fun j => 2*j+1 ≤ n ∧ n < 4*(2*j+1)), (fun j : ℕ => if 2*j+1 = e then
      if 2*(2*j+1) ≤ n then (1 : ℚ) / (2*(2*j+1) : ℕ) else 0
    else (1 : ℚ) / (2*j+1 : ℕ)) j ≤ 3/4 := by
  decide +kernel

private theorem pool_bound {n : ℕ} (hn : 12 ≤ n) {e : ℕ}
    (he : e ∈ ({2*(n/8)+1, 3*(2*(n/8)+1)} : Finset ℕ)) :
    ∑ j ∈ ((range (n+1)).filter fun j => 2*j+1 ≤ n ∧ n < 4*(2*j+1)), (fun j : ℕ => if 2*j+1 = e then
      if 2*(2*j+1) ≤ n then (1 : ℚ) / (2*(2*j+1) : ℕ) else 0
    else (1 : ℚ) / (2*j+1 : ℕ)) j ≤ 3/4 := by
  let pool := ((range (n+1)).filter fun j => 2*j+1 ≤ n ∧ n < 4*(2*j+1))
  let weight := (fun j : ℕ => if 2*j+1 = e then
      if 2*(2*j+1) ≤ n then (1 : ℚ) / (2*(2*j+1) : ℕ) else 0
    else (1 : ℚ) / (2*j+1 : ℕ))
  change ∑ j ∈ pool, weight j ≤ 3/4
  by_cases hs : n ≤ 71
  · exact pool_small n (mem_Icc.mpr ⟨hn,hs⟩) e he
  have hsub : pool ⊆ Ico (n/8) (4*(n/8)+4) := by
    intro j hj
    obtain ⟨_,h1,h2⟩ := mem_filter.mp hj
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  calc
    _ ≤ ∑ j ∈ pool, ((1 : ℚ) / (2*j+1 : ℕ)) := by
      apply sum_le_sum
      intro j _
      dsimp only [weight]
      split_ifs <;> first | rfl | positivity | (apply one_div_le_one_div_of_le (by positivity); exact_mod_cast (by omega : 2*j+1 ≤ 2*(2*j+1)))
    _ ≤ ∑ j ∈ Ico (n/8) (4*(n/8)+4), ((1 : ℚ) / (2*j+1 : ℕ)) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := envelope_bound _ (by omega)

private theorem divides_eq {n : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A)
    {b c : ℕ} (hb : b ∈ A) (hc : c ∈ A) (hd : b ∣ c) : b = c := by
  by_contra hne
  have h := hA.2 hb hc hne
  have hI := mem_Icc.mp (hA.1 hc)
  have hle := Nat.le_of_dvd (by omega : 0 < c) (Nat.lcm_dvd hd (dvd_refl c))
  omega

/-- Every member other than four has a distinct odd part in (n/4,n]. -/
theorem four_mem {n : ℕ} {A : Finset ℕ} (hn : 12 ≤ n) (hA : Erdos542.IsLcmFree n A)
    (h4 : 4 ∈ A) : ∑ b ∈ A, (1 : ℚ) / b ≤ 1 := by
  let idx (b : ℕ) := if b % 2 = 0 then b/4 else b/2
  have classify (b : ℕ) (hb : b ∈ A.erase 4) :
      b = 2*(idx b)+1 ∨ b = 2*(2*(idx b)+1) := by
    obtain ⟨hne,hm⟩ := mem_erase.mp hb
    have hnd : ¬ 4 ∣ b := fun h => hne (divides_eq hA h4 hm h).symm
    dsimp [idx]
    split <;> omega
  let pool := ((range (n+1)).filter fun j => 2*j+1 ≤ n ∧ n < 4*(2*j+1))
  have hpool (b : ℕ) (hb : b ∈ A.erase 4) : idx b ∈ pool := by
    obtain ⟨hne,hm⟩ := mem_erase.mp hb
    have hI := mem_Icc.mp (hA.1 hm)
    have hl := hA.2 h4 hm hne.symm
    have hdiv : b ∣ 4*(2*idx b+1) := by
      rcases classify b hb with h | h
      · exact ⟨4, by omega⟩
      · exact ⟨2, by omega⟩
    have hle := Nat.le_of_dvd (by positivity : 0 < 4*(2*idx b+1))
      (Nat.lcm_dvd (dvd_mul_right 4 _) hdiv)
    have hc := classify b hb
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,by omega⟩
  have hinj : Set.InjOn idx (↑(A.erase 4) : Set ℕ) := by
    intro b hb c hc hij
    have hm := (mem_erase.mp hb).2
    have hn' := (mem_erase.mp hc).2
    rcases classify b hb with h | h <;> rcases classify c hc with g | g
    · omega
    · exact divides_eq hA hm hn' ⟨2, by omega⟩
    · exact (divides_eq hA hn' hm ⟨2, by omega⟩).symm
    · omega
  let x := 2*(n/8)+1
  obtain ⟨e, he, hmiss⟩ : ∃ e ∈ ({x,3*x} : Finset ℕ), e ∉ A := by
    by_cases hx : x ∈ A
    · refine ⟨3*x, by simp, fun h3 => ?_⟩
      have h := divides_eq hA hx h3 (dvd_mul_left x 3)
      dsimp [x] at h
      omega
    · exact ⟨x,by simp,hx⟩
  let weight := (fun j : ℕ => if 2*j+1 = e then
      if 2*(2*j+1) ≤ n then (1 : ℚ) / (2*(2*j+1) : ℕ) else 0
    else (1 : ℚ) / (2*j+1 : ℕ))
  have hterm (b : ℕ) (hb : b ∈ A.erase 4) : (1 : ℚ) / b ≤ weight (idx b) := by
    obtain ⟨_,hm⟩ := mem_erase.mp hb
    have hI := mem_Icc.mp (hA.1 hm)
    have hc := classify b hb
    dsimp only [weight]
    split_ifs with heq hle
    · have hb2 : b = 2*(2*idx b+1) := hc.resolve_left (by
        intro h; exact hmiss ((h.trans heq) ▸ hm))
      rw [← hb2]
    · rcases hc with h | h
      · exact (hmiss ((h.trans heq) ▸ hm)).elim
      · omega
    · apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (by omega : 2*idx b+1 ≤ b)
  have hsum : ∑ b ∈ A.erase 4, (1 : ℚ) / b ≤ 3/4 := by
    calc
      _ ≤ ∑ b ∈ A.erase 4, weight (idx b) := sum_le_sum hterm
      _ = ∑ j ∈ (A.erase 4).image idx, weight j := by rw [sum_image hinj]
      _ ≤ ∑ j ∈ pool, weight j := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact image_subset_iff.mpr hpool
        · intro j _ _; dsimp only [weight]; split_ifs <;> positivity
      _ ≤ _ := pool_bound hn he
  rw [← Finset.add_sum_erase A _ h4]
  norm_num at *
  linarith

private theorem split_upper (n : ℕ) (T U : Finset ℕ)
    (h : ∀ m ∈ T, ¬ m ≤ n/2 → m ∈ U) :
    ∑ b ∈ T, (1 : ℚ)/b ≤ ∑ b ∈ T.filter (fun b => b ≤ n/2), (1 : ℚ)/b
      + ∑ m ∈ U, (1 : ℚ)/m := by
  calc
    _ = _ := (sum_filter_add_sum_filter_not T (fun b => b ≤ n/2) (fun b => (1 : ℚ)/b)).symm
    _ ≤ _ := by
      apply add_le_add_right
      apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
      intro m hm
      obtain ⟨hmem, hlarge⟩ := mem_filter.mp hm
      exact h m hmem hlarge

private theorem loss_of_sum {n : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A)
    (hs : ∑ b ∈ A, (1 : ℚ)/b ≤ 1) :
    ∑ a ∈ A, ((n % a : ℕ) : ℚ) / a ≤ ((Erdos542.uncovered n A).card : ℚ) := by
  have hterm (a : ℕ) (ha : a ∈ A) :
      (n : ℚ) * ((1 : ℚ)/a) = ((n/a : ℕ) : ℚ) + ((n%a : ℕ) : ℚ)/a := by
    have hI := mem_Icc.mp (hA.1 ha)
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
    have hdm : (n : ℚ) = (a : ℚ) * ((n / a : ℕ) : ℚ) + ((n % a : ℕ) : ℚ) := by
      exact_mod_cast (Nat.div_add_mod n a).symm
    field_simp
    linarith
  have hc : (∑ a ∈ A, ((n/a : ℕ) : ℚ)) + ((Erdos542.uncovered n A).card : ℚ) = n := by
    exact_mod_cast OMA.R_Erdos542_erdos_542_variants_only_two_R1.count_identity hA
  have h := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℚ) n)
  rw [mul_one, Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib] at h
  linarith

/-- With distinguished member five, only the middle interval contains choices.
The admissible upper-half elements have been filled in. -/
def H1 : Prop := ∀ (n : ℕ) (B : Finset ℕ), 25 ≤ n → Erdos542.IsLcmFree n B →
    (∀ b ∈ B, n < 5*b ∧ b ≤ n/2 ∧ ¬ 5 ∣ b) →
    ∑ b ∈ B, (1 : ℚ) / b +
      ∑ m ∈ (Icc (n/2+1) n).filter (fun m => ¬ 5 ∣ m ∧ ∀ b ∈ B, ¬ b ∣ m),
        (1 : ℚ) / m ≤ 4/5

/-- When all members are at least six, one only needs the choices in the lower half. -/
def H2 : Prop := ∀ (n : ℕ) (B : Finset ℕ), Erdos542.IsLcmFree n B →
    (∀ b ∈ B, 6 ≤ b ∧ b ≤ n/2) → (∃ a ∈ B, a*a ≤ n) →
    ∑ b ∈ B, (1 : ℚ) / b +
      ∑ m ∈ (Icc (n/2+1) n).filter (fun m => ∀ b ∈ B, ¬ b ∣ m),
        (1 : ℚ) / m ≤ 1

theorem main : H1 → H2 → OMA.R_Erdos542_erdos_542_variants_only_two_R1.H2 := by
  intro hfive hlarge n A hn hA h2 h3 hsmall
  apply loss_of_sum hA
  by_cases h1 : 1 ∈ A
  · have hsingleton : A = {1} := by
      ext b
      exact ⟨fun hb => mem_singleton.mpr (divides_eq hA h1 hb (one_dvd b)).symm,
        fun hb => (mem_singleton.mp hb) ▸ h1⟩
    simp [hsingleton]
  by_cases h4 : 4 ∈ A
  · exact four_mem hn hA h4
  have hmin (b : ℕ) (hb : b ∈ A) : 5 ≤ b := by
    have hi := mem_Icc.mp (hA.1 hb)
    by_contra! hl
    interval_cases b <;> simp_all
  have hsub {B : Finset ℕ} (hBA : B ⊆ A) : Erdos542.IsLcmFree n B :=
    ⟨Subset.trans hBA hA.1, fun _ hx _ hy hne => hA.2 (hBA hx) (hBA hy) hne⟩
  obtain ⟨a,ha,hsq⟩ := hsmall
  have ha5 := hmin a ha
  by_cases h5 : 5 ∈ A
  · let T := A.erase 5
    let B := T.filter (fun b => b ≤ n/2)
    have hBA (b : ℕ) (hb : b ∈ B) : b ∈ A := (mem_erase.mp (mem_filter.mp hb).1).2
    have hcore (b : ℕ) (hb : b ∈ B) : n < 5*b ∧ b ≤ n/2 ∧ ¬ 5 ∣ b := by
      obtain ⟨hbT,hlo⟩ := mem_filter.mp hb
      obtain ⟨hne,hm⟩ := mem_erase.mp hbT
      have hI := mem_Icc.mp (hA.1 hm)
      have hl := hA.2 h5 hm hne.symm
      have hbound := Nat.le_of_dvd (by omega : 0 < 5*b) (Nat.lcm_dvd_mul 5 b)
      exact ⟨by omega,hlo,fun hd => hne (divides_eq hA h5 hm hd).symm⟩
    let U := (Icc (n/2+1) n).filter (fun m => ¬ 5 ∣ m ∧ ∀ b ∈ B, ¬ b ∣ m)
    have htail : ∀ m ∈ T, ¬ m ≤ n/2 → m ∈ U := by
      intro m hm hhi
      obtain ⟨hne,hmA⟩ := mem_erase.mp hm
      have hI := mem_Icc.mp (hA.1 hmA)
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hI.2⟩,
        fun hd => hne (divides_eq hA h5 hmA hd).symm, ?_⟩
      intro b hb hd
      have hEq := divides_eq hA (hBA b hb) hmA hd
      have hlo := (hcore b hb).2.1
      omega
    have h := (split_upper n T U htail).trans (hfive n B (by nlinarith) (hsub (fun _ => hBA _)) hcore)
    rw [← add_sum_erase A _ h5]
    change (1 : ℚ)/(5 : ℕ) + (∑ b ∈ T, (1 : ℚ)/b) ≤ 1
    linarith
  · let B := A.filter (fun b => b ≤ n/2)
    have hBA : B ⊆ A := filter_subset _ _
    have hcore (b : ℕ) (hb : b ∈ B) : 6 ≤ b ∧ b ≤ n/2 := by
      have hm := hmin b (hBA hb)
      have hne : b ≠ 5 := fun h => h5 (h ▸ hBA hb)
      exact ⟨by omega,(mem_filter.mp hb).2⟩
    let U := (Icc (n/2+1) n).filter (fun m => ∀ b ∈ B, ¬ b ∣ m)
    have htail : ∀ m ∈ A, ¬ m ≤ n/2 → m ∈ U := by
      intro m hm hhi
      have hI := mem_Icc.mp (hA.1 hm)
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hI.2⟩,?_⟩
      intro b hb hd
      have hEq := divides_eq hA (hBA hb) hm hd
      have hlo := (hcore b hb).2
      omega
    have hdouble : 2*a ≤ n := by nlinarith
    exact (split_upper n A U htail).trans
      (hlarge n B (hsub hBA) hcore ⟨a,mem_filter.mpr ⟨ha,by omega⟩,hsq⟩)

end OMA.R_Erdos542_erdos_542_variants_only_two_R1_H2_R1
