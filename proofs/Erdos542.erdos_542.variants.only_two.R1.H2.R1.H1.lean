import OMAReductions.R_Erdos542_erdos_542_variants_only_two_R1_H2_R1

-- Credit: @Dolcruz
-- uses note #51956

/-! A divisor cover for the distinguished-five case of Erdős problem 542.
For fixed n, charge a nonmultiple m of five weight 1/m if 2m > n,
1/(2m) if 2m ≤ n < 3m, and 1/(6m) if 3m ≤ n < 5m. The multiples
of each admissible member other than five pay its full reciprocal.

Writing the charge as three nested interval sums gives a decreasing
block estimate for n ≥ 900. For smaller n, rounded-up reciprocals
give a direct integer check except at eleven values. There, a few
low denominators determine which other choices still need to be bounded.
The double-counting argument follows mrnato255's divisor-cover lemma. -/

namespace Erdos542Five
open Finset

def band (n d : ℕ) : Finset ℕ :=
  (Icc 1 n).filter fun m => n < d*m ∧ ¬ 5 ∣ m

def mass (n d : ℕ) : ℚ := ∑ m ∈ band n d, (1 : ℚ)/m

def total (n : ℕ) : ℚ := mass n 2 / 2 + mass n 3 / 3 + mass n 5 / 6

/-- At most four nonmultiples of five lie in each block from 5j to 5j+4. -/
def blockSum (d k : ℕ) : ℚ :=
  ∑ j ∈ Ico k (d*(k+1)), (4 : ℚ)/(5*j+1 : ℕ)

theorem blockSum_step (d k : ℕ) (hd : 1 ≤ d) : blockSum d (k+1) ≤ blockSum d k := by
  let z := d*(k+1)
  have hz : k+1 ≤ z := by dsimp [z]; nlinarith
  have htop : d*(k+1+1) = z+d := by dsimp [z]; ring
  have htail : ∑ j ∈ Ico z (z+d), (4 : ℚ)/(5*j+1 : ℕ) ≤ 4/(5*k+1 : ℕ) := by
    have hdq : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    calc
      _ ≤ ∑ _j ∈ Ico z (z+d), (4 : ℚ)/(5*k+1 : ℕ)/d := by
        apply sum_le_sum
        intro j hj
        have hzj := (mem_Ico.mp hj).1
        have hden : (5*k+1)*d ≤ 5*j+1 := by dsimp [z] at hzj; nlinarith
        rw [div_div]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact_mod_cast hden
      _ = _ := by simp; field_simp
  unfold blockSum
  rw [htop]
  change ∑ j ∈ Ico (k+1) (z+d), (4 : ℚ)/(5*j+1 : ℕ) ≤ ∑ j ∈ Ico k z, (4 : ℚ)/(5*j+1 : ℕ)
  rw [← sum_Ico_consecutive _ hz (by omega : z ≤ z+d),
    ← sum_Ico_consecutive _ (by omega : k ≤ k+1) hz]
  simpa [add_comm] using add_le_add_left htail (∑ j ∈ Ico (k+1) z, (4 : ℚ)/(5*j+1 : ℕ))

theorem blockSum_anti {d k l : ℕ} (hd : 1 ≤ d) (h : k ≤ l) : blockSum d l ≤ blockSum d k := by
  induction l, h using Nat.le_induction with
  | base => rfl
  | succ l _ ih => exact (blockSum_step d l hd).trans ih

theorem mass_le_blocks (n d : ℕ) (hd : 1 ≤ d) : mass n d ≤ blockSum d (n/(5*d)) := by
  let k := n/(5*d)
  have hden := Nat.div_mul_le_self n (5*d)
  have hnext := Nat.lt_mul_div_succ n (by positivity : 0 < 5*d)
  change k*(5*d) ≤ n at hden
  change n < (5*d)*(k+1) at hnext
  have hloc (m : ℕ) (hm : m ∈ band n d) : m/5 ∈ Ico k (d*(k+1)) := by
    obtain ⟨hi,hgt,hnd⟩ := mem_filter.mp hm
    have hmle := (mem_Icc.mp hi).2
    have hk : 5*k ≤ m := by nlinarith
    have hhi : m < 5*(d*(k+1)) := by nlinarith
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  have hpart : ∑ j ∈ Ico k (d*(k+1)), ∑ m ∈ (band n d).filter (fun m => m/5=j), (1:ℚ)/m =
      mass n d := by
    simp only [sum_filter, mass]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    simp [hloc m hm]
  rw [← hpart]
  apply sum_le_sum
  intro j _
  let F := (band n d).filter (fun m => m/5=j)
  have hbounds (m : ℕ) (hm : m ∈ F) : 5*j+1 ≤ m ∧ m ≤ 5*j+4 := by
    obtain ⟨hb,hq⟩ := mem_filter.mp hm
    have hnd := (mem_filter.mp hb).2.2
    omega
  have hc : F.card ≤ 4 := by
    have hs : F ⊆ Icc (5*j+1) (5*j+4) := fun m hm => mem_Icc.mpr (hbounds m hm)
    simpa using card_le_card hs
  calc
    _ ≤ ∑ _m ∈ F, (1:ℚ)/(5*j+1 : ℕ) := by
      apply sum_le_sum
      intro m hm
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (hbounds m hm).1
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul, mul_one_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

theorem total_large {n : ℕ} (hn : 900 ≤ n) : total n ≤ 4/5 := by
  have h2 := (mass_le_blocks n 2 (by decide)).trans (blockSum_anti (by decide) (by omega : 90 ≤ n/(5*2)))
  have h3 := (mass_le_blocks n 3 (by decide)).trans (blockSum_anti (by decide) (by omega : 60 ≤ n/(5*3)))
  have h5 := (mass_le_blocks n 5 (by decide)).trans (blockSum_anti (by decide) (by omega : 36 ≤ n/(5*5)))
  have hnum : blockSum 2 90 / 2 + blockSum 3 60 / 3 + blockSum 5 36 / 6 ≤ 4/5 := by decide +kernel
  unfold total
  linarith

/-- The numerator of each eligible reciprocal rounded upwards in units of one millionth. -/
def rounded (m : ℕ) : ℕ := if 5 ∣ m then 0 else (1000000 + m - 1)/m

def roundedSum : ℕ → ℕ
  | 0 => 0
  | k+1 => roundedSum k + rounded (k+1)

def exceptional : Finset ℕ := {13,14,17,19,23,29,31,32,33,34,53}

theorem rounded_check : ∀ n ∈ Icc 12 899, n ∉ exceptional →
    5 * (3*(roundedSum n - roundedSum (n/2)) + 2*(roundedSum n - roundedSum (n/3)) +
      (roundedSum n - roundedSum (n/5))) ≤ 24*1000000 := by
  decide +kernel

theorem roundedSum_eq (n : ℕ) : roundedSum n = ∑ m ∈ Ioc 0 n, rounded m := by
  induction n with
  | zero => simp [roundedSum]
  | succ n ih => rw [roundedSum, ih, sum_Ioc_succ_top (by omega : 0 ≤ n)]

theorem mass_le_rounded (n d : ℕ) (hd : 0 < d) :
    mass n d ≤ ((roundedSum n - roundedSum (n/d) : ℕ) : ℚ)/1000000 := by
  have hk := Nat.div_le_self n d
  have htotal : ∑ m ∈ Ioc (n/d) n, rounded m = roundedSum n - roundedSum (n/d) := by
    rw [roundedSum_eq,roundedSum_eq]
    have h := sum_Ioc_consecutive (f := rounded) (Nat.zero_le (n/d)) hk
    omega
  have hs : band n d ⊆ Ioc (n/d) n := by
    intro m hm
    obtain ⟨hi,hmul,_⟩ := mem_filter.mp hm
    exact mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hd).mpr (by simpa [mul_comm] using hmul),(mem_Icc.mp hi).2⟩
  calc
    mass n d ≤ ∑ m ∈ band n d, (rounded m : ℚ)/1000000 := by
      apply sum_le_sum
      intro m hm
      obtain ⟨hi,_,hnd⟩ := mem_filter.mp hm
      have hmp := (mem_Icc.mp hi).1
      have hq := Nat.lt_mul_div_succ (1000000+m-1) (by omega : 0 < m)
      rw [Nat.mul_add, Nat.mul_one] at hq
      rw [rounded, if_neg hnd, div_le_div_iff₀ (by exact_mod_cast hmp : (0 : ℚ) < m) (by norm_num)]
      rw [one_mul, mul_comm]
      exact_mod_cast (by omega : 1000000 ≤ m * ((1000000+m-1)/m))
    _ ≤ ∑ m ∈ Ioc (n/d) n, (rounded m : ℚ)/1000000 :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
    _ = _ := by rw [← sum_div, ← Nat.cast_sum,htotal]

theorem total_regular {n : ℕ} (hn : 12 ≤ n) (he : n ∉ exceptional) : total n ≤ 4/5 := by
  by_cases h : 900 ≤ n
  · exact total_large h
  have hc := rounded_check n (mem_Icc.mpr ⟨hn,by omega⟩) he
  have hc' : 5 * (3*((roundedSum n - roundedSum (n/2) : ℕ) : ℚ) +
      2*((roundedSum n - roundedSum (n/3) : ℕ) : ℚ) +
      ((roundedSum n - roundedSum (n/5) : ℕ) : ℚ)) ≤ 24*1000000 := by exact_mod_cast hc
  unfold total
  linarith [mass_le_rounded n 2 (by decide),mass_le_rounded n 3 (by decide),mass_le_rounded n 5 (by decide)]

def levy (n d m : ℕ) : ℚ := if n < d*m ∧ ¬ 5 ∣ m then 1/(m : ℚ) else 0

def weight (n m : ℕ) : ℚ := levy n 2 m / 2 + levy n 3 m / 3 + levy n 5 m / 6

theorem weight_nonneg (n m : ℕ) : 0 ≤ weight n m := by
  unfold weight levy
  split_ifs <;> positivity

theorem sum_weight (n : ℕ) : ∑ m ∈ Icc 1 n, weight n m = total n := by
  simp only [weight,total,mass,band,sum_filter,levy,sum_add_distrib,sum_div]

theorem point_cover {n b : ℕ} (hb : 0 < b) (hbn : b ≤ n) (h5 : n < 5*b) (hnd : ¬ 5 ∣ b) :
    (1 : ℚ)/b ≤ ∑ k ∈ Icc 1 4, if k*b ≤ n then weight n (k*b) else 0 := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hprime : Nat.Prime 5 := by decide
  have htwo : ¬ 5 ∣ 2*b := by simp [hprime.dvd_mul,hnd]
  have hthree : ¬ 5 ∣ 3*b := by simp [hprime.dvd_mul,hnd]
  have hfour : ¬ 5 ∣ 4*b := by simp [hprime.dvd_mul,hnd]
  rw [show Icc 1 4 = ({1,2,3,4} : Finset ℕ) by decide]
  simp only [sum_insert (by decide : (1:ℕ) ∉ {2,3,4}),
    sum_insert (by decide : (2:ℕ) ∉ {3,4}),sum_insert (by decide : (3:ℕ) ∉ {4}),
    sum_singleton,one_mul,if_pos hbn]
  rcases (show n < 2*b ∨ (2*b ≤ n ∧ n < 3*b) ∨
      (3*b ≤ n ∧ n < 4*b) ∨ 4*b ≤ n by omega) with h | ⟨h,g⟩ | ⟨h,g⟩ | h
  all_goals
    simp only [weight,levy,hnd,htwo,hthree,hfour,not_false_eq_true,and_true]
    simp (disch := omega) only [if_pos,if_neg]
    push_cast
    field_simp
    ring_nf
    norm_num

def choices (n : ℕ) : Finset ℕ := (Icc (n/5+1) (n/2)).filter (fun b => ¬ 5 ∣ b)

def upper (n : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (Icc (n/2+1) n).filter (fun m => ¬ 5 ∣ m ∧ ∀ b ∈ B, ¬ b ∣ m)

def topSet (n : ℕ) : Finset ℕ := (Icc (n/2+1) n).filter (fun m => ¬ 5 ∣ m)

def replaced (n b : ℕ) : ℚ := ∑ m ∈ topSet n, if b ∣ m then (1:ℚ)/m else 0

/-- Extra weight allowed for choosing b after its upper-half multiples are removed. -/
def gain (n b : ℕ) : ℚ := max ((1:ℚ)/b - replaced n b) 0

def pivots (n : ℕ) : Finset ℕ :=
  if n ≤ 14 then {3} else if n ≤ 19 then {4} else if n = 23 then {6}
  else if n = 29 then {6,7} else if n = 53 then {11,12,13} else {7,8}

def possible (n : ℕ) (C : Finset ℕ) : Finset ℕ :=
  (choices n).filter fun b => (b ∈ pivots n → b ∈ C) ∧ ∀ c ∈ C, b ≠ c → n < Nat.lcm b c

theorem pivot_check : ∀ n ∈ exceptional, ∀ C ∈ (pivots n).powerset,
    (∀ b ∈ C, ∀ c ∈ C, b ≠ c → n < Nat.lcm b c) →
    (∑ m ∈ topSet n, (1:ℚ)/m) + ∑ b ∈ possible n C, gain n b ≤ 4/5 := by
  decide +kernel

theorem top_partition {n : ℕ} {B : Finset ℕ}
    (sep : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → n < Nat.lcm a b) :
    (∑ b ∈ B, replaced n b) + ∑ m ∈ upper n B, (1:ℚ)/m = ∑ m ∈ topSet n, (1:ℚ)/m := by
  have heq : upper n B = (topSet n).filter (fun m => ∀ b ∈ B, ¬ b ∣ m) := by
    ext
    simp [upper,topSet,and_assoc]
  simp only [replaced, heq,sum_filter]
  rw [sum_comm, ← sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  have hI := mem_Icc.mp (mem_filter.mp hm).1
  by_cases h : ∀ b ∈ B, ¬ b ∣ m
  · rw [if_pos h, sum_eq_zero (fun b hb => if_neg (h b hb)), zero_add]
  · obtain ⟨c,hc,hcm⟩ : ∃ c ∈ B, c ∣ m := by simpa only [not_forall,exists_prop,not_not] using h
    rw [if_neg h, add_zero, sum_eq_single_of_mem c hc]
    · simp [hcm]
    · intro b hb hne
      apply if_neg
      intro hbm
      have hle := Nat.le_of_dvd (by omega : 0 < m) (Nat.lcm_dvd hbm hcm)
      have hgt := sep b hb c hc hne
      omega

theorem exceptional_check : ∀ n ∈ exceptional, ∀ B ∈ (choices n).powerset,
    (∀ b ∈ B, ∀ c ∈ B, b ≠ c → n < Nat.lcm b c) →
    ∑ b ∈ B, (1:ℚ)/b + ∑ m ∈ upper n B, (1:ℚ)/m ≤ 4/5 := by
  intro n hn B hB sep
  let C := B ∩ pivots n
  have hCP : C ⊆ pivots n := inter_subset_right
  have hCB : C ⊆ B := inter_subset_left
  have hpos : B ⊆ possible n C := by
    intro b hb
    exact mem_filter.mpr ⟨mem_powerset.mp hB hb,(fun hp => mem_inter.mpr ⟨hb,hp⟩),
      fun c hc hne => sep b hb c (hCB hc) hne⟩
  have hc := pivot_check n hn C (mem_powerset.mpr hCP) (fun b hb c hc => sep b (hCB hb) c (hCB hc))
  have hpaid := top_partition sep
  have hg : ∑ b ∈ B, ((1:ℚ)/b - replaced n b) ≤ ∑ b ∈ possible n C, gain n b := by
    calc
      _ ≤ ∑ b ∈ B, gain n b := sum_le_sum fun b _ => le_max_left _ _
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hpos (fun b _ _ => le_max_right _ _)
  rw [sum_sub_distrib] at hg
  linarith

theorem paid {n b : ℕ} (hb : 0 < b) (hbn : b ≤ n) (h5 : n < 5*b) (hnd : ¬ 5 ∣ b) :
    (1:ℚ)/b ≤ ∑ m ∈ (Icc 1 n).filter (b ∣ ·), weight n m := by
  let K := (Icc 1 4).filter fun k => k*b ≤ n
  have hinj : Set.InjOn (fun k => k*b) (↑K : Set ℕ) :=
    fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_right hb h
  have hsub : K.image (fun k => k*b) ⊆ (Icc 1 n).filter (b ∣ ·) := by
    intro m hm
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hm
    obtain ⟨hI,hle⟩ := mem_filter.mp hk
    have hkpos := (mem_Icc.mp hI).1
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith,hle⟩,dvd_mul_left b k⟩
  calc
    _ ≤ ∑ k ∈ K, weight n (k*b) := by simpa only [K,sum_filter] using point_cover hb hbn h5 hnd
    _ = ∑ m ∈ K.image (fun k => k*b), weight n m := by rw [sum_image hinj]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => weight_nonneg n m)

/-- Double-counting the divisor cover, as in mrnato255's DivisorCover.lean. -/
theorem charge_family {n : ℕ} {T : Finset ℕ}
    (sep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → n < Nat.lcm a b)
    (hs : ∀ a ∈ T, 0 < a ∧ a ≤ n ∧ n < 5*a ∧ ¬ 5 ∣ a) :
    ∑ b ∈ T, (1:ℚ)/b ≤ total n := by
  calc
    _ ≤ ∑ b ∈ T, ∑ m ∈ Icc 1 n, if b ∣ m then weight n m else 0 := by
      apply sum_le_sum
      intro b hb
      obtain ⟨h1,h2,h3,h4⟩ := hs b hb
      simpa only [sum_filter] using paid h1 h2 h3 h4
    _ = ∑ m ∈ Icc 1 n, ∑ b ∈ T, if b ∣ m then weight n m else 0 := sum_comm
    _ ≤ ∑ m ∈ Icc 1 n, weight n m := by
      apply sum_le_sum
      intro m hm
      obtain ⟨hmpos,hmle⟩ := mem_Icc.mp hm
      have hc : (T.filter (· ∣ m)).card ≤ 1 := by
        apply card_le_one.mpr
        intro a ha b hb
        obtain ⟨ha,had⟩ := mem_filter.mp ha
        obtain ⟨hb,hbd⟩ := mem_filter.mp hb
        by_contra hne
        have hgt := sep a ha b hb hne
        have hle := Nat.le_of_dvd hmpos (Nat.lcm_dvd had hbd)
        omega
      rw [← sum_filter, sum_const,nsmul_eq_mul]
      exact mul_le_of_le_one_left (weight_nonneg n m) (by exact_mod_cast hc)
    _ = _ := sum_weight n

private theorem high_multiple {n u m : ℕ} (hu : n/2 < u) (hm : 0 < m) (hmn : m ≤ n)
    (hdiv : u ∣ m) : m = u := by
  obtain ⟨j,rfl⟩ := hdiv
  have hj : j = 1 := by
    by_contra! hne
    have h2 : 2 ≤ j := by
      by_cases hz : j = 0
      · simp [hz] at hm
      · omega
    have h := Nat.mul_le_mul_left u h2
    omega
  simp [hj]

theorem lower_half {n : ℕ} {B : Finset ℕ} (hn : 12 ≤ n) (hB : Erdos542.IsLcmFree n B)
    (hb : ∀ b ∈ B, n < 5*b ∧ b ≤ n/2 ∧ ¬ 5 ∣ b) :
    ∑ b ∈ B, (1:ℚ)/b + ∑ m ∈ upper n B, (1:ℚ)/m ≤ 4/5 := by
  by_cases he : n ∈ exceptional
  · apply exceptional_check n he B
    · apply mem_powerset.mpr
      intro b hm
      obtain ⟨hlt,hle,hnd⟩ := hb b hm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hle⟩,hnd⟩
    · exact fun _ ha _ hc hne => hB.2 ha hc hne
  let U := upper n B
  have huinfo (u : ℕ) (hu : u ∈ U) : n/2 < u ∧ u ≤ n ∧ ¬ 5 ∣ u ∧ ∀ b ∈ B, ¬ b ∣ u := by
    obtain ⟨hI,hnd,hdiv⟩ := mem_filter.mp hu
    obtain ⟨hl,hr⟩ := mem_Icc.mp hI
    exact ⟨by omega,hr,hnd,hdiv⟩
  have hdis : Disjoint B U := by
    apply disjoint_left.mpr
    intro b hm hu
    exact (huinfo b hu).2.2.2 b hm (dvd_refl b)
  have hsingle (u : ℕ) (hu : u ∈ U) (v : ℕ) (hv : v ∈ B ∪ U) (hne : u ≠ v) :
      n < Nat.lcm u v := by
    by_contra! hle
    obtain ⟨hlo,_,_,havoid⟩ := huinfo u hu
    obtain hBv | hUv := mem_union.mp hv
    · have hpos := (mem_Icc.mp (hB.1 hBv)).1
      have heq := high_multiple hlo (Nat.lcm_pos (by omega) hpos) hle (Nat.dvd_lcm_left u v)
      exact havoid v hBv (heq ▸ Nat.dvd_lcm_right u v)
    · have hvlo := (huinfo v hUv).1
      have hp : 0 < Nat.lcm u v := Nat.lcm_pos (by omega) (by omega)
      exact hne ((high_multiple hlo hp hle (Nat.dvd_lcm_left u v)).symm.trans
        (high_multiple hvlo hp hle (Nat.dvd_lcm_right u v)))
  have hsep : ∀ a ∈ B ∪ U, ∀ b ∈ B ∪ U, a ≠ b → n < Nat.lcm a b := by
    intro a ha b hc hne
    rcases mem_union.mp ha with hBa | hUa
    · rcases mem_union.mp hc with hBc | hUc
      · exact hB.2 hBa hBc hne
      · simpa [Nat.lcm_comm] using hsingle b hUc a ha hne.symm
    · exact hsingle a hUa b hc hne
  have hs (a : ℕ) (ha : a ∈ B ∪ U) : 0 < a ∧ a ≤ n ∧ n < 5*a ∧ ¬ 5 ∣ a := by
    rcases mem_union.mp ha with h | h
    · obtain ⟨hpos,hle⟩ := mem_Icc.mp (hB.1 h)
      obtain ⟨hlt,_,hnd⟩ := hb a h
      exact ⟨hpos,hle,hlt,hnd⟩
    · obtain ⟨hl,hr,hnd,_⟩ := huinfo a h
      exact ⟨by omega,hr,by omega,hnd⟩
  have h := (charge_family hsep hs).trans (total_regular hn he)
  rwa [sum_union hdis] at h

/-- For all n ≥ 12 an LCM-free family containing five has reciprocal sum at most one. -/
theorem five_mem {n : ℕ} {A : Finset ℕ} (hn : 12 ≤ n) (hA : Erdos542.IsLcmFree n A)
    (h5 : 5 ∈ A) : ∑ a ∈ A, (1:ℚ)/a ≤ 1 := by
  let T := A.erase 5
  let B := T.filter (fun b => b ≤ n/2)
  have hBA {b : ℕ} (hb : b ∈ B) : b ∈ A := (mem_erase.mp (mem_filter.mp hb).1).2
  have hfree : Erdos542.IsLcmFree n B :=
    ⟨fun _ h => hA.1 (hBA h), fun _ ha _ hb hab => hA.2 (hBA ha) (hBA hb) hab⟩
  have hmem (b : ℕ) (hb : b ∈ T) : n < 5*b ∧ ¬ 5 ∣ b := by
    obtain ⟨hne,ha⟩ := mem_erase.mp hb
    obtain ⟨hbpos,hbn⟩ := mem_Icc.mp (hA.1 ha)
    have hlt := hA.2 h5 ha hne.symm
    refine ⟨hlt.trans_le (Nat.le_of_dvd (by omega : 0 < 5*b) (Nat.lcm_dvd_mul 5 b)),fun hd => ?_⟩
    have hle := Nat.le_of_dvd hbpos (Nat.lcm_dvd hd (dvd_refl b))
    omega
  have hcore (b : ℕ) (hb : b ∈ B) : n < 5*b ∧ b ≤ n/2 ∧ ¬ 5 ∣ b := by
    obtain ⟨hT,hlo⟩ := mem_filter.mp hb
    exact ⟨(hmem b hT).1,hlo,(hmem b hT).2⟩
  have hsu : T.filter (fun m => ¬ m ≤ n/2) ⊆ upper n B := by
    intro m hm
    obtain ⟨hT,hhi⟩ := mem_filter.mp hm
    obtain ⟨_,hmA⟩ := mem_erase.mp hT
    have hI := mem_Icc.mp (hA.1 hmA)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hI.2⟩,(hmem m hT).2,?_⟩
    intro b hb hd
    have hlo := (hcore b hb).2.1
    have hlt := hA.2 (hBA hb) hmA (by omega : b ≠ m)
    have hle := Nat.le_of_dvd hI.1 (Nat.lcm_dvd hd (dvd_refl m))
    omega
  have htail : ∑ m ∈ T.filter (fun m => ¬ m ≤ n/2), (1:ℚ)/m ≤ ∑ m ∈ upper n B, (1:ℚ)/m :=
    sum_le_sum_of_subset_of_nonneg hsu (fun _ _ _ => by positivity)
  have hbound := lower_half hn hfree hcore
  have hsplit := sum_filter_add_sum_filter_not T (fun b => b ≤ n/2) (fun b => (1:ℚ)/b)
  change (∑ b ∈ B, (1:ℚ)/b) + _ = _ at hsplit
  rw [← add_sum_erase A _ h5]
  change (1:ℚ)/(5:ℕ) + (∑ b ∈ T, (1:ℚ)/b) ≤ 1
  linarith

theorem five : OMA.R_Erdos542_erdos_542_variants_only_two_R1_H2_R1.H1 :=
  fun _ _ hn hB hb => lower_half (by omega) hB hb

end Erdos542Five

theorem OMA.solution : OMA.R_Erdos542_erdos_542_variants_only_two_R1_H2_R1.H1 :=
  Erdos542Five.five
