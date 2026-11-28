import OMAReductions.R_Erdos945_erdos_945_R1

-- Reduction Erdos945.erdos_945.R1.H1.R1 of step Erdos945.erdos_945.R1.H1
-- Credit: @hiattco

namespace OMA.R_Erdos945_erdos_945_R1_H1_R1

open Finset
open scoped Classical

/-- Multiples of small prime squares occupy at most seven eighths of the interval. -/
def H1 : Prop := ∀ n H : ℕ, 64 ≤ H →
    ((Ioc n (n + H)).filter fun q =>
      ∃ p : ℕ, p.Prime ∧ p ≤ H / 8 ∧ p * p ∣ q).card ≤ 7 * H / 8

/-- Bound the number of positions hit by a large prime square at a polynomial
length in the binary size parameter. -/
def H2 : Prop := ∃ A D : ℕ, ∀ m n : ℕ, n ≤ 2^m →
    let H := D * (m + 1)^A
    64 ≤ H ∧ ((Ioc n (n + H)).filter fun q =>
      ∃ p : ℕ, p.Prime ∧ H / 8 < p ∧ p * p ∣ q).card < H - 7 * H / 8

theorem squarefree_of_count_bounds {n H : ℕ}
    (hs : ((Ioc n (n+H)).filter fun q => ∃ p : ℕ, p.Prime ∧ p ≤ H/8 ∧ p*p ∣ q).card ≤ 7*H/8)
    (hl : ((Ioc n (n+H)).filter fun q => ∃ p : ℕ, p.Prime ∧ H/8 < p ∧ p*p ∣ q).card < H - 7*H/8) :
    ∃ q : ℕ, n < q ∧ q ≤ n+H ∧ Squarefree q := by
  let I := Ioc n (n+H)
  let small := I.filter fun q => ∃ p : ℕ, p.Prime ∧ p ≤ H/8 ∧ p*p ∣ q
  let large := I.filter fun q => ∃ p : ℕ, p.Prime ∧ H/8 < p ∧ p*p ∣ q
  change small.card ≤ 7*H/8 at hs
  change large.card < H - 7*H/8 at hl
  by_contra hnone
  have cover : I ⊆ small ∪ large := by
    intro q hq
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hq
    have hbad : ¬ Squarefree q := fun hqfree => hnone ⟨q, hlo, hhi, hqfree⟩
    rw [Nat.squarefree_iff_prime_squarefree] at hbad
    push Not at hbad
    obtain ⟨p, hp, hd⟩ := hbad
    by_cases h : p ≤ H / 8
    · exact mem_union_left _ (mem_filter.mpr ⟨hq, p, hp, h, hd⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hq, p, hp, Nat.lt_of_not_ge h, hd⟩)
  have hcard : I.card = H := by simp [I]
  have hcount := (card_le_card cover).trans (card_union_le small large)
  omega

theorem main : H1 → H2 → OMA.R_Erdos945_erdos_945_R1.H1 := by
  intro smallBound largeBound
  obtain ⟨A, D, hAD⟩ := largeBound
  refine ⟨A, D, ?_⟩
  intro m n hn
  obtain ⟨hH, hLarge⟩ := hAD m n hn
  exact squarefree_of_count_bounds (smallBound n _ hH) hLarge

private theorem square_div_le_difference (H d : Nat) (hd : 2 ≤ d) :
    H / d ^ 2 ≤ H / (d - 1) - H / d := by
  rw [Nat.pow_two, ← Nat.div_div_eq_div_mul]
  let q := H / d
  change q / d ≤ H / (d - 1) - q
  apply Nat.le_sub_of_add_le
  apply (Nat.le_div_iff_mul_le (by omega : 0 < d - 1)).2
  have hsmall : q / d * (d - 1) ≤ q := by
    exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.sub_le d 1)) (Nat.div_mul_le_self q d)
  have hsplit : q * (d - 1) + q = q * d := by
    rw [← Nat.mul_succ]
    have : (d - 1).succ = d := by omega
    rw [this]
  rw [Nat.add_mul]
  exact Nat.le_trans (Nat.add_le_add_right hsmall _) (by
    rw [Nat.add_comm q, hsplit]
    exact Nat.div_mul_le_self H d)

/-- An interval of length H contains at most H / b + 1 multiples of b. -/
private theorem interval_multiple_bound (n H b : Nat) (hb : 0 < b) :
    (n + H) / b - n / b ≤ H / b + 1 := by
  rw [Nat.add_div hb]
  generalize n / b = q, H / b = r
  split <;> omega

private theorem interval_multiple_card (n H b : ℕ) (hb : 0 < b) :
    ((Finset.Ioc n (n + H)).filter fun x => b ∣ x).card =
      (n + H) / b - n / b := by
  rw [← Nat.card_Ioc]
  apply Finset.card_bij' (fun x _ => x / b) (fun k _ => k * b)
  · intro x hx
    obtain ⟨hx, hdvd⟩ := Finset.mem_filter.mp hx
    obtain ⟨hl, hr⟩ := Finset.mem_Ioc.mp hx
    exact Finset.mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hb).2 (by
      rwa [Nat.div_mul_cancel hdvd]), Nat.div_le_div_right hr⟩
  · intro k hk
    obtain ⟨hl, hr⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hb).1 hl, (Nat.le_div_iff_mul_le hb).1 hr⟩,
       dvd_mul_left b k⟩
  · intro x hx
    exact Nat.div_mul_cancel (Finset.mem_filter.mp hx).2
  · intro k _
    exact Nat.mul_div_cancel k hb

/-- The small-square hypothesis holds uniformly in the interval start. -/
theorem small_prime_bound : H1 := by
  intro n H hH
  let tailCount (n H : ℕ) : ℕ → ℕ :=
    Nat.rec 0 (fun k total => total + ((n+H) / ((k+3)^2) - n / ((k+3)^2)))
  have tail_bound (n H k : Nat)
      (step : ∀ a : Nat, H / ((a+3)^2) + H / (a+3) ≤ H / (a+2)) :
      tailCount n H k + H/(k+2) ≤ H/2 + k := by
    induction k with
    | zero => simp [tailCount]
    | succ k ih =>
      have hm := interval_multiple_bound n H ((k+3)^2)
        (Nat.pow_pos (by omega))
      have hs := step k
      change tailCount n H k + ((n+H)/((k+3)^2) - n/((k+3)^2)) + H/(k+3) ≤ H/2+(k+1)
      omega

  -- Count all square divisors with multiplicity.
  have small_square_budget (n H : Nat) (hH : 64 ≤ H) :
      ((n+H)/4 - n/4) + tailCount n H (H/8-2) ≤ 7*H/8 := by
    have step (a : Nat) : H / ((a+3)^2) + H / (a+3) ≤ H / (a+2) := by
      have h := square_div_le_difference H (a+3) (by omega)
      have m : H / (a+3) ≤ H / (a+2) := Nat.div_le_div_left (by omega) (by omega)
      change H / ((a+3)^2) ≤ H / (a+2) - H / (a+3) at h
      omega
    have h₂ := interval_multiple_bound n H 4 (by decide)
    have ht := tail_bound n H (H/8-2) step
    have bound := Nat.le_trans (Nat.le_add_right ..) ht
    omega

  let hits (n H t : ℕ) : Finset ℕ :=
    (Ioc n (n + H)).filter fun q => ∃ d : ℕ, 2 ≤ d ∧ d ≤ t ∧ d ^ 2 ∣ q

  have hits_card (n H k : ℕ) :
      (hits n H (k+2)).card ≤ (n+H)/4 - n/4 + tailCount n H k := by
    induction k with
    | zero =>
      have hs : hits n H 2 ⊆ (Ioc n (n+H)).filter fun q => 4 ∣ q := by
        intro q hq
        obtain ⟨hi,d,hd,hle,hdvd⟩ := mem_filter.mp hq
        have : d = 2 := by omega
        subst d
        exact mem_filter.mpr ⟨hi,hdvd⟩
      change (hits n H 2).card ≤ (n+H)/4 - n/4 + 0
      simpa only [Nat.add_zero, interval_multiple_card n H 4 (by decide)] using card_le_card hs
    | succ k ih =>
      let last := (Ioc n (n+H)).filter fun q => (k+3)^2 ∣ q
      have cover : hits n H (k+3) ⊆ hits n H (k+2) ∪ last := by
        intro q hq
        obtain ⟨hi,d,hd,hle,hdiv⟩ := mem_filter.mp hq
        by_cases h : d ≤ k+2
        · exact mem_union_left _ (mem_filter.mpr ⟨hi,d,hd,h,hdiv⟩)
        · have eq : d = k+3 := by omega
          subst d
          exact mem_union_right _ (mem_filter.mpr ⟨hi,hdiv⟩)
      have hpos : 0 < (k+3)^2 := Nat.pow_pos (by omega)
      have hlast : last.card = (n+H)/((k+3)^2) - n/((k+3)^2) := interval_multiple_card n H _ hpos
      have hcount := (card_le_card cover).trans (card_union_le _ _)
      apply hcount.trans
      simpa only [hlast, tailCount, Nat.add_assoc] using
        (Nat.add_le_add_right ih ((n+H)/((k+3)^2) - n/((k+3)^2)))
  have cover : ((Ioc n (n + H)).filter fun q =>
      ∃ p : ℕ, p.Prime ∧ p ≤ H / 8 ∧ p * p ∣ q) ⊆ hits n H (H/8 - 2 + 2) := by
    intro q hq
    obtain ⟨hi, p, hp, hle, hdiv⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hi, p, hp.two_le, by omega, by simpa only [pow_two] using hdiv⟩
  exact (card_le_card cover).trans ((hits_card n H (H/8-2)).trans
    (small_square_budget n H hH))

/-- Cofactors give a uniform upper bound on positions hit by large prime squares. -/
theorem uniform_large_count (n H : ℕ) (hH : 64 ≤ H) :
    ((Ioc n (n+H)).filter (fun v => ∃ p : ℕ, p.Prime ∧ H/8 < p ∧ p^2 ∣ v)).card ≤
      (n+H)/(H/8+1)^2 + 1 := by
  classical
  -- Separate the two possible odd-root residues when the cofactor is one.
  let label (k p : ℕ) := if k=1 ∧ p%4=1 then 0 else k

  have large_separation {n H k p q : ℕ} (hp : n < k*p^2) (hpq : p < q)
      (hlarge : H/8 < p) (ho : p%2=1) (ho' : q%2=1)
      (hk : 0 < k) (he : label k p = label k q) : n+H < k*q^2 := by
    by_cases h1 : k = 1
    · subst k
      have h4 : p+4 ≤ q := by
        unfold label at he
        split at he <;> split at he <;> omega
      have scale := Nat.pow_le_pow_left h4 2
      simp only [Nat.one_mul] at hp ⊢
      have h8 : H < 8*p := by omega
      nlinarith only [hp,scale,h8]
    · have h2 : p+2 ≤ q := by omega
      have scale := Nat.mul_le_mul_left k (Nat.pow_le_pow_left h2 2)
      have hk2 : 2 ≤ k := by omega
      have cross := Nat.mul_le_mul_right p hk2
      have h8 : H < 8*p := by omega
      nlinarith only [hp,scale,cross,h8,Nat.zero_le k]
  let t := H/8
  let L := (Ioc n (n+H)).filter (fun v => ∃ p : ℕ, p.Prime ∧ t < p ∧ p^2 ∣ v)
  have witness (q : L) : ∃ p : ℕ, p.Prime ∧ t < p ∧ p^2 ∣ q.val :=
    (mem_filter.mp q.property).2
  let p (q : L) := Classical.choose (witness q)
  let k (q : L) := q.val / (p q)^2
  have factor (q : L) : k q * (p q)^2 = q.val :=
    Nat.div_mul_cancel (Classical.choose_spec (witness q)).2.2
  have in_I (q : L) : n < q.val ∧ q.val ≤ n+H :=
    mem_Ioc.mp (mem_filter.mp q.property).1
  have high (q : L) : H/8 < p q := (Classical.choose_spec (witness q)).2.1
  have oddw (q : L) : (p q)%2=1 := by
    have hpq : (p q).Prime := (Classical.choose_spec (witness q)).1
    have hi := high q
    exact hpq.eq_two_or_odd.elim (fun h => by omega) id
  have nonzero (q : L) : 0 < k q := by
    have pos := (in_I q).1
    by_contra! hk
    have hzero : k q = 0 := by omega
    have := factor q
    rw [hzero, Nat.zero_mul] at this
    omega
  let B := (n+H)/(t+1)^2
  have hbound (q : L) : k q ≤ B := by
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega : 0 < t+1))).mpr
    apply LE.le.trans (Nat.mul_le_mul_left (k q) (Nat.pow_le_pow_left
      (show t+1 ≤ p q from (Classical.choose_spec (witness q)).2.1) 2))
    rw [factor]
    exact (in_I q).2
  let F (q : L) : Icc 0 B := ⟨label (k q) (p q), by
    apply mem_Icc.mpr
    exact ⟨Nat.zero_le _,by unfold label; split <;> first | exact Nat.zero_le _ | exact hbound q⟩⟩
  have hinj : Function.Injective F := by
    intro a b h
    have hl : label (k a) (p a) = label (k b) (p b) := congrArg Subtype.val h
    have hk : k a = k b := by
      have := nonzero a
      have := nonzero b
      unfold label at hl
      split at hl <;> split at hl <;> omega
    rw [← hk] at hl
    have af := factor a
    have bf := factor b
    have ai := in_I a
    have bi := in_I b
    rcases lt_trichotomy (p a) (p b) with hlt|heq|hgt
    · have bound := large_separation (af.symm ▸ ai.1) hlt (high a) (oddw a) (oddw b) (nonzero a) hl
      rw [hk,bf] at bound
      omega
    · apply Subtype.ext
      rw [← af, ← bf, hk, heq]
    · rw [hk] at hl
      have bound := large_separation (bf.symm ▸ bi.1) hgt (high b) (oddw b) (oddw a) (nonzero b) hl.symm
      rw [← hk,af] at bound
      omega
  have final := Finset.card_le_card_of_injective hinj
  simpa [F, B, t, Nat.card_Icc] using final


/-- The large-square hypothesis at all starts up to the cube of floor(H/8). -/
theorem cube_window (n H : ℕ) (hH : 80 ≤ H) (hn : n ≤ (H/8)^3) :
    ((Ioc n (n+H)).filter (fun v => ∃ p : ℕ, p.Prime ∧ H/8 < p ∧ p*p ∣ v)).card <
      H - 7*H/8 := by
  let K := H/8
  have hK : 10 ≤ K := by dsimp [K]; omega
  have hH' : H ≤ 8*K+7 := by dsimp [K]; omega
  have poly : K^3+8*K+7 < (K-1)*(K+1)^2 := by
    have hten (k : ℕ) : (k+10)^3+8*(k+10)+7 < ((k+10)-1)*((k+10)+1)^2 := by
      rw [show k+10-1 = k+9 by omega]
      nlinarith only [Nat.zero_le (k^2), Nat.zero_le k]
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hK
    simpa only [hj, Nat.add_comm 10 j] using hten j
  have hd : (n+H)/(K+1)^2 < K-1 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega : 0 < K+1))).mpr
    exact lt_of_le_of_lt (Nat.add_le_add hn hH') (by simpa only [Nat.add_assoc] using poly)
  have hcard := uniform_large_count n H (by omega)
  simp only [← Nat.pow_two] at ⊢
  change _ ≤ (n+H)/(K+1)^2+1 at hcard
  have hrest : K ≤ H - 7*H/8 := by dsimp [K]; omega
  omega

theorem squarefree_in_cube_window (n H : ℕ) (hH : 80 ≤ H) (hn : n ≤ (H/8)^3) :
    ∃ q : ℕ, n < q ∧ q ≤ n + H ∧ Squarefree q :=
  squarefree_of_count_bounds (small_prime_bound n H (by omega))
    (cube_window n H hH hn)

/-- A bound on the large prime squares alone yields the squarefree gap criterion. -/
theorem of_large_squares (h : H2) : OMA.R_Erdos945_erdos_945_R1.H1 :=
  main small_prime_bound h

end OMA.R_Erdos945_erdos_945_R1_H1_R1
