import OMAStatements.S_oeis_a033496

/-!
Every fan size above ten occurs at a power of four. Choose a shape with
two or three multiples of each odd stem, realize the chosen predecessor
path by lifting a congruence, and count all bounded predecessors.

Sources: https://oeis.org/A033496 and https://oeis.org/A087256
-/

namespace A033496Fan

open Function
open OMA.S_oeis_a033496 (collatz fan)

private theorem collatz_double (m : ℕ) : collatz (2 * m) = m := by
  simp [collatz]

private theorem collatz_positive {m : ℕ} (hm : 1 ≤ m) : 1 ≤ collatz m := by
  unfold collatz
  split <;> omega

private theorem collatz_odd {m : ℕ} (hm : m % 2 = 1) : collatz m = 3 * m + 1 := by
  simp [collatz, hm]

private theorem collatz_pow_two_mul (a j : ℕ) :
    collatz (2^(j+1) * a) = 2^j * a := by
  rw [pow_succ', mul_assoc, collatz_double]

private theorem iterate_pow_two_mul (a j : ℕ) : (collatz^[j]) (2^j * a) = a := by
  induction j with
  | zero => simp
  | succ j hj => rw [iterate_succ_apply, collatz_pow_two_mul, hj]

private theorem pow_two_iterates_bounded {k : ℕ} (hk : 2 ≤ k) :
    ∀ i, (collatz^[i]) (2^k) ≤ 2^k := by
  let powers : Set ℕ := {m | ∃ j ≤ k, m = 2^j}
  have hp : (2^k : ℕ) ∈ powers := ⟨k, le_rfl, rfl⟩
  have hclosed : Set.MapsTo collatz powers powers := by
    rintro _ ⟨j, hj, rfl⟩
    cases j with
    | zero => exact ⟨2, hk, by decide⟩
    | succ j =>
      refine ⟨j, by omega, ?_⟩
      simpa only [mul_one] using collatz_pow_two_mul 1 j
  intro i
  obtain ⟨j, hj, he⟩ := hclosed.iterate i hp
  rw [he]
  exact Nat.pow_le_pow_right (by decide) hj

/-- A set of bounded backward paths gives the fan when it contains all bounded predecessors. -/
private theorem fan_eq_of_predecessors {n : ℕ} {S : Finset ℕ}
    (hroot : n ∈ S) (hpos : ∀ m ∈ S, 1 ≤ m) (hbound : ∀ m ∈ S, m ≤ n)
    (hfuture : ∀ i, (collatz^[i]) n ≤ n)
    (hprev : ∀ m, 1 ≤ m → m ≤ n → collatz m ∈ S → m ∈ S)
    (hnext : ∀ m ∈ S, m ≠ n → collatz m ∈ S)
    (hreach : ∀ m ∈ S, ∃ i, (collatz^[i]) m = n) : fan n = (S : Set ℕ) := by
  ext m
  change (1 ≤ m ∧ m ≤ n ∧ (∀ i, (collatz^[i]) m ≤ n) ∧
    (∃ i, (collatz^[i]) m = n)) ↔ m ∈ S
  constructor
  · rintro ⟨hm, _, hb, i, hi⟩
    induction i generalizing m with
    | zero =>
      change m = n at hi
      simpa only [hi] using hroot
    | succ i ih =>
      apply hprev m hm (hb 0)
      refine ih (collatz m) (collatz_positive hm) (by simpa using hb 1) ?_ ?_
      · intro j
        simpa only [iterate_succ_apply] using hb (j+1)
      · simpa only [iterate_succ_apply] using hi
  · intro hm
    refine ⟨hpos m hm, hbound m hm, ?_, hreach m hm⟩
    have hstep (i : ℕ) : (collatz^[i]) m ∈ S ∨
        ∃ j, (collatz^[i]) m = (collatz^[j]) n := by
      induction i with
      | zero => exact Or.inl hm
      | succ i ih =>
        rw [iterate_succ_apply']
        rcases ih with h | ⟨j, hj⟩
        · by_cases hroot' : (collatz^[i]) m = n
          · rw [hroot']
            exact Or.inr ⟨1, rfl⟩
          · exact Or.inl (hnext _ h hroot')
        · exact Or.inr ⟨j+1, by rw [iterate_succ_apply', hj]⟩
    intro i
    rcases hstep i with hi | ⟨j, hj⟩
    · exact hbound _ hi
    · rw [hj]
      exact hfuture j

private def oddPart (a : ℕ) : ℕ := a / 2^(a.factorization 2)

private theorem oddPart_pow_two_mul {a : ℕ} (ha : a % 2 = 1) (i : ℕ) :
    oddPart (2^i*a) = a := by
  have hna : a ≠ 0 := by omega
  have hndvd : ¬ 2 ∣ a := by omega
  rw [oddPart, Nat.factorization_mul (by positivity) hna, Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]
  exact Nat.mul_div_cancel_left a (by positivity)

private theorem iterate_inverse_chain (f u : ℕ → ℕ) {t : ℕ}
    (hu : ∀ i < t, f (u (i+1)) = u i) (i j : ℕ) (h : i+j ≤ t) :
    (f^[j]) (u (i+j)) = u i := by
  induction j with
  | zero => simp
  | succ j hj =>
    rw [iterate_succ_apply, show i+j.succ = (i+j)+1 by omega, hu _ (by omega)]
    exact hj (by omega)

private theorem chain_injective (f u : ℕ → ℕ) {t : ℕ}
    (hu : ∀ i < t, f (u (i+1)) = u i)
    (hn : ∀ i, 0 < i → i ≤ t → u i ≠ u 0) : Set.InjOn u (Set.Iic t) := by
  intro i hi j hj heq
  have hlt (i j : ℕ) (hi : i ≤ t) (hj : j ≤ t) (hl : i < j) (he : u i = u j) : False := by
    have h₀ := iterate_inverse_chain f u hu 0 i (by simpa using hi)
    have h₁ := iterate_inverse_chain f u hu (j-i) i (by omega)
    rw [zero_add] at h₀
    rw [Nat.sub_add_cancel (by omega : i ≤ j)] at h₁
    rw [he, h₁] at h₀
    exact hn (j-i) (by omega) (by omega) h₀
  rcases lt_trichotomy i j with h | h | h
  · exact (hlt i j hi hj h heq).elim
  · exact h
  · exact (hlt j i hj hi h heq.symm).elim

private theorem collatz_preimage {m v : ℕ} (h : collatz m = v) :
    m = 2*v ∨ (m % 2 = 1 ∧ 3*m+1 = v) := by
  unfold collatz at h
  split at h <;> omega

private theorem unique_odd_predecessor {m m' v a b : ℕ}
    (ha : 1 ≤ a) (ha' : a ≤ 2) (hb : 1 ≤ b) (hb' : b ≤ 2)
    (h : 3*m+1 = 2^a*v) (h' : 3*m'+1 = 2^b*v) : m = m' := by
  interval_cases a <;> interval_cases b <;> norm_num at h h' <;> omega

private def leg (a J : ℕ) : Finset ℕ :=
  (Finset.range (J+1)).image (fun j => 2^j*a)

private theorem mem_leg {a J m : ℕ} :
    m ∈ leg a J ↔ ∃ j ≤ J, 2^j*a = m := by
  simp [leg]

private theorem card_leg {a J : ℕ} (ha : 0 < a) : (leg a J).card = J+1 := by
  unfold leg
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro i j h
  exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) (Nat.eq_of_mul_eq_mul_right ha h)

/-- A path of odd predecessors with legs of length two or three has no other bounded branches. -/
theorem cardinality {k T : ℕ} (y J jump : ℕ → ℕ) (hk : 2 ≤ k) (hT : 0 < T)
    (hodd : ∀ r, 1 ≤ r → r ≤ T → y r % 2 = 1)
    (hlarge : ∀ r, 1 ≤ r → r ≤ T → 1 < y r)
    (hJ : ∀ r, 1 ≤ r → r ≤ T → 1 ≤ J r ∧ J r ≤ 2)
    (hsize : ∀ r, 1 ≤ r → r ≤ T → 2^(J r)*y r ≤ 2^k ∧ 2^k < 2^(J r+1)*y r)
    (hfirst : 3*y 1+1 = 2^k)
    (hjump : ∀ r, 1 ≤ r → r < T → 1 ≤ jump r ∧ jump r ≤ J r)
    (hstep : ∀ r, 1 ≤ r → r < T → 3*y (r+1)+1 = 2^(jump r)*y r)
    (hlast : 3 ∣ y T) : (fan (2^k)).ncard = 1 + ∑ r ∈ Finset.Icc 1 T, (J r+1) := by
  let n : ℕ := 2^k
  let I := Finset.Icc 1 T
  let B := I.biUnion (fun r => leg (y r) (J r))
  let S := insert n B
  have hn : 0 < n := by dsimp [n]; positivity
  have ht1 : 1 ≤ T := by omega
  have hS {m : ℕ} : m ∈ S ↔ m = n ∨ ∃ r, 1 ≤ r ∧ r ≤ T ∧ ∃ j ≤ J r, 2^j*y r = m := by
    simp [S, B, I, mem_leg, and_assoc]
  have hin {r : ℕ} (hr : 1 ≤ r) (hrT : r ≤ T) (j : ℕ) :
      2^j*y r ≤ n ↔ j ≤ J r := by
    constructor
    · intro hh
      by_contra! hj
      have hl : 2^(J r+1) ≤ (2 : ℕ)^j := Nat.pow_le_pow_right (by decide) (by omega)
      exact ((hsize r hr hrT).2.trans_le ((Nat.mul_le_mul_right _ hl).trans hh)).false
    · intro hj
      have hl : 2^j ≤ (2 : ℕ)^(J r) := Nat.pow_le_pow_right (by decide) hj
      exact (Nat.mul_le_mul_right _ hl).trans (hsize r hr hrT).1
  have hprev (m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n) (hm : collatz m ∈ S) : m ∈ S := by
    rcases hS.mp hm with he | ⟨r, hr, hrT, j, hj, he⟩
    · rcases collatz_preimage he with hh | ⟨_, hh⟩
      · omega
      · have hmy : m = y 1 := by omega
        exact hS.mpr (Or.inr ⟨1, le_rfl, ht1, 0, Nat.zero_le _, by simpa using hmy.symm⟩)
    · rcases collatz_preimage he.symm with hh | ⟨_, hh⟩
      · have hmul : m = 2^(j+1)*y r := by rw [hh, pow_succ', mul_assoc]
        rw [hmul] at hmn
        exact hS.mpr (Or.inr ⟨r, hr, hrT, j+1, (hin hr hrT _).mp hmn, hmul.symm⟩)
      · have hj1 : 1 ≤ j := by
          by_contra! h
          have hj0 : j = 0 := by omega
          subst j
          simp at hh
          have hoy := hodd r hr hrT
          omega
        have hrlt : r < T := by
          by_contra! hlo
          have hrEq : r = T := by omega
          subst r
          have hdiv : 3 ∣ 2^j*y T := dvd_mul_of_dvd_right hlast _
          omega
        have hh' := hjump r hr hrlt
        have heq := unique_odd_predecessor hj1 (hj.trans (hJ r hr hrT).2)
          hh'.1 (hh'.2.trans (hJ r hr hrT).2) hh (hstep r hr hrlt)
        exact hS.mpr (Or.inr ⟨r+1, by omega, by omega, 0, Nat.zero_le _, by simpa using heq.symm⟩)
  have hnext (m : ℕ) (hm : m ∈ S) (hmn : m ≠ n) : collatz m ∈ S := by
    obtain ⟨r, hr, hrT, j, hj, rfl⟩ := (hS.mp hm).resolve_left hmn
    cases j with
    | zero =>
      rw [pow_zero, one_mul, collatz_odd (hodd r hr hrT)]
      by_cases h : r = 1
      · subst r
        exact hS.mpr (Or.inl hfirst)
      · have h₁ : 1 ≤ r-1 := by omega
        have h₂ : r-1 < T := by omega
        have heq : r-1+1 = r := by omega
        have hs := hstep (r-1) h₁ h₂
        rw [heq] at hs
        exact hS.mpr (Or.inr ⟨r-1, h₁, by omega, jump (r-1), (hjump (r-1) h₁ h₂).2, hs.symm⟩)
    | succ j =>
      rw [collatz_pow_two_mul]
      exact hS.mpr (Or.inr ⟨r, hr, hrT, j, by omega, rfl⟩)
  have hyreach (r : ℕ) (hr : 1 ≤ r) (hrT : r ≤ T) : ∃ i, (collatz^[i]) (y r) = n := by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      by_cases h : r = 1
      · subst r
        exact ⟨1, by simpa [collatz_odd (hodd 1 le_rfl ht1)] using hfirst⟩
      · have h₁ : 1 ≤ r-1 := by omega
        have h₂ : r-1 < T := by omega
        have heq : r-1+1 = r := by omega
        have hs := hstep (r-1) h₁ h₂
        rw [heq] at hs
        obtain ⟨i, hi⟩ := ih (r-1) (by omega) h₁ (by omega)
        refine ⟨i+jump (r-1)+1, ?_⟩
        rw [iterate_succ_apply, collatz_odd (hodd r hr hrT), hs, iterate_add_apply,
          iterate_pow_two_mul, hi]
  have hFan : fan n = (S : Set ℕ) := by
    refine fan_eq_of_predecessors (hS.mpr (Or.inl rfl)) ?_ ?_ (pow_two_iterates_bounded hk) hprev hnext ?_
    · intro m hm
      rcases hS.mp hm with rfl | ⟨r, hr, hrT, j, _, rfl⟩
      · exact hn
      · have h := hlarge r hr hrT
        exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.two_pow_pos _) (by omega))
    · intro m hm
      rcases hS.mp hm with rfl | ⟨r, hr, hrT, j, hj, rfl⟩
      · exact le_rfl
      · exact (hin hr hrT _).mpr hj
    · intro m hm
      rcases hS.mp hm with rfl | ⟨r, hr, hrT, j, _, rfl⟩
      · exact ⟨0, rfl⟩
      · obtain ⟨i, hi⟩ := hyreach r hr hrT
        exact ⟨i+j, by rw [iterate_add_apply, iterate_pow_two_mul, hi]⟩
  have hnOdd : oddPart n = 1 := by
    simpa [n] using oddPart_pow_two_mul (by decide : (1 : ℕ) % 2 = 1) k
  have hinj : Set.InjOn y (I : Set ℕ) := by
    let u : ℕ → ℕ := fun j => if j = 0 then 1 else y j
    have hu (i : ℕ) (hi : i < T) : oddPart (collatz (u (i+1))) = u i := by
      by_cases hi0 : i = 0
      · subst i
        simpa [u, collatz_odd (hodd 1 le_rfl ht1), hfirst, ← show n = 2^k by rfl] using hnOdd
      · have h₁ : 1 ≤ i := by omega
        have h₂ : i+1 ≤ T := by omega
        simpa [u, hi0, collatz_odd (hodd (i+1) (by omega) h₂), hstep i h₁ hi] using
          oddPart_pow_two_mul (hodd i h₁ (by omega)) (jump i)
    have hiu := chain_injective (fun z => oddPart (collatz z)) u hu (by
      intro i hi hiT
      simpa [u, show i ≠ 0 by omega] using (hlarge i (by omega) hiT).ne')
    intro r hri s hsi h
    have hr := Finset.mem_Icc.mp (show r ∈ I from hri)
    have hs := Finset.mem_Icc.mp (show s ∈ I from hsi)
    apply hiu hr.2 hs.2
    simpa [u, show r ≠ 0 by omega, show s ≠ 0 by omega] using h
  have hdis : (I : Set ℕ).PairwiseDisjoint (fun r => leg (y r) (J r)) := by
    intro r hr s hs hrs
    change Disjoint (leg (y r) (J r)) (leg (y s) (J s))
    rw [Finset.disjoint_left]
    intro m hm hm'
    obtain ⟨i, _, hi⟩ := mem_leg.mp hm
    obtain ⟨j, _, hj⟩ := mem_leg.mp hm'
    have hr' := Finset.mem_Icc.mp (show r ∈ I from hr)
    have hs' := Finset.mem_Icc.mp (show s ∈ I from hs)
    have h := congrArg oddPart (hi.trans hj.symm)
    rw [oddPart_pow_two_mul (hodd r hr'.1 hr'.2), oddPart_pow_two_mul (hodd s hs'.1 hs'.2)] at h
    exact hrs (hinj hr hs h)
  have hnB : n ∉ B := by
    intro h
    obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.mp h
    obtain ⟨i, _, he⟩ := mem_leg.mp hm
    have hr' := Finset.mem_Icc.mp (show r ∈ I from hr)
    have hh := congrArg oddPart he
    rw [oddPart_pow_two_mul (hodd r hr'.1 hr'.2), hnOdd] at hh
    exact (hlarge r hr'.1 hr'.2).ne' hh
  change (fan n).ncard = 1 + ∑ r ∈ I, (J r+1)
  rw [hFan, Set.ncard_coe_finset, show S = insert n B from rfl, Finset.card_insert_of_notMem hnB,
    show B = I.biUnion (fun r => leg (y r) (J r)) from rfl, Finset.card_biUnion hdis, Nat.add_comm]
  apply congrArg (fun m : ℕ => 1+m)
  apply Finset.sum_congr rfl
  intro r hr
  obtain ⟨hr₁, hr₂⟩ := Finset.mem_Icc.mp (show r ∈ I from hr)
  exact card_leg (by have := hlarge r hr₁ hr₂; omega)

end A033496Fan

namespace OMA.A033496

def height (r : ℕ) : ℕ := Nat.log 2 (3 ^ r)

def levels (δ r : ℕ) : ℕ :=
  if r = 1 ∨ (r = 3 ∧ 1 ≤ δ) ∨ (r = 5 ∧ 2 ≤ δ) then 1 else 2

def scaleExponent (δ r : ℕ) : ℕ := height r - levels δ r

def jump (δ r : ℕ) : ℕ := scaleExponent δ (r + 1) - scaleExponent δ r

theorem height_bounds (r : ℕ) : 2 ^ height r ≤ 3 ^ r ∧ 3 ^ r < 2 ^ (height r + 1) :=
  ⟨Nat.pow_log_le_self 2 (by positivity), Nat.lt_pow_succ_log_self (by decide) _⟩

theorem height_pos (r : ℕ) (hr : 1 ≤ r) : 1 ≤ height r := by
  apply (Nat.le_log_iff_pow_le (by decide) (by positivity)).2
  have : 3 ^ 1 ≤ 3 ^ r := Nat.pow_le_pow_right (by decide) hr
  omega

theorem strict_height_bounds (r : ℕ) (hr : 1 ≤ r) :
    2 ^ height r < 3 ^ r ∧ 3 ^ r < 2 ^ (height r + 1) := by
  obtain ⟨hlo, hhi⟩ := height_bounds r
  refine ⟨lt_of_le_of_ne hlo ?_, hhi⟩
  intro heq
  have h := congrArg (fun x : ℕ => x % 2) heq
  norm_num [Nat.pow_mod, Nat.zero_pow (height_pos r hr)] at h

theorem height_step (r : ℕ) :
    height r + 1 ≤ height (r + 1) ∧ height (r + 1) ≤ height r + 2 := by
  obtain ⟨hlo, hhi⟩ := height_bounds r
  constructor
  · apply (Nat.le_log_iff_pow_le (by decide) (by positivity)).2
    rw [pow_succ, pow_succ]
    omega
  · change Nat.log 2 (3 ^ (r + 1)) ≤ height r + 2
    apply Nat.lt_succ_iff.mp
    apply (Nat.log_lt_iff_lt_pow (by decide) (by positivity)).2
    have hpow : 2 ^ (height r + 2).succ = 2 ^ (height r + 1) * 4 := by
      change 2 ^ ((height r + 1) + 2) = _
      rw [pow_add]
      norm_num
    rw [hpow, pow_succ]
    omega

theorem levels_bounds (δ r : ℕ) : 1 ≤ levels δ r ∧ levels δ r ≤ 2 := by
  unfold levels
  split <;> omega

theorem levels_le_height (δ r : ℕ) (hr : 1 ≤ r) : levels δ r ≤ height r := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp [levels, height, show Nat.log 2 3 = 1 by decide]
  · have h₁ : height 2 = 3 := by decide
    have h₂ : height 2 ≤ height r := Nat.log_mono_right (Nat.pow_le_pow_right (by decide) hr)
    have h₃ := (levels_bounds δ r).2
    omega

theorem scaleExponent_one (δ : ℕ) : scaleExponent δ 1 = 0 := by
  simp [scaleExponent, levels, height, show Nat.log 2 3 = 1 by decide]

theorem scaleExponent_add_levels (δ r : ℕ) (hr : 1 ≤ r) :
    scaleExponent δ r + levels δ r = height r :=
  Nat.sub_add_cancel (levels_le_height δ r hr)

theorem jump_bounds (δ r : ℕ) (hδ : δ ≤ 2) (hr : 1 ≤ r) :
    1 ≤ jump δ r ∧ jump δ r ≤ levels δ r := by
  by_cases hu : r ≤ 5
  · interval_cases r <;> interval_cases δ <;> decide
  · have hl : levels δ r = 2 := by
      simp [levels, show r ≠ 1 by omega, show r ≠ 3 by omega, show r ≠ 5 by omega]
    have hl' : levels δ (r + 1) = 2 := by
      simp [levels, show r ≠ 0 by omega, show r + 1 ≠ 3 by omega,
        show r + 1 ≠ 5 by omega]
    obtain ⟨ha, hb⟩ := height_step r
    have he := scaleExponent_add_levels δ r hr
    have he' := scaleExponent_add_levels δ (r + 1) (by omega)
    rw [hl] at he ⊢
    rw [hl'] at he'
    unfold jump
    omega

theorem scaleExponent_step (δ r : ℕ) (hδ : δ ≤ 2) (hr : 1 ≤ r) :
    scaleExponent δ (r + 1) = jump δ r + scaleExponent δ r := by
  have h := (jump_bounds δ r hδ hr).1
  unfold jump at h ⊢
  omega

theorem levels_sum (T δ : ℕ) (ht : 4 ≤ T) (hδ : δ ≤ 2)
    (hfive : 2 ≤ δ → 5 ≤ T) :
    1 + ∑ r ∈ Finset.Icc 1 T, (levels δ r + 1) = 3 * T - δ := by
  classical
  have point (r : ℕ) :
      levels δ r + 1 + (if r = 1 then 1 else 0) +
        (if r = 3 ∧ 1 ≤ δ then 1 else 0) + (if r = 5 ∧ 2 ≤ δ then 1 else 0) = 3 := by
    by_cases h1 : r = 1
    · subst r
      simp [levels]
    by_cases h3 : r = 3
    · subst r
      by_cases hd : 1 ≤ δ <;> simp [levels, hd, h1]
    by_cases h5 : r = 5
    · subst r
      by_cases hd : 2 ≤ δ <;> simp [levels, hd, h1, h3]
    · simp [levels, h1, h3, h5]
  have summed := Finset.sum_congr (s₁ := Finset.Icc 1 T) rfl fun r _ => point r
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc] at summed
  have h1 : 1 ∈ Finset.Icc (1 : ℕ) T := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have h3 : 3 ∈ Finset.Icc (1 : ℕ) T := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h5 : 2 ≤ δ → 5 ∈ Finset.Icc (1 : ℕ) T :=
    fun h => Finset.mem_Icc.mpr ⟨by omega, hfive h⟩
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  interval_cases δ <;> simp_all [Finset.sum_ite_eq'] <;> omega

theorem choose_levels (k : ℕ) (hk : 10 < k) :
    ∃ T δ : ℕ, 1 ≤ T ∧ δ ≤ 2 ∧ 1 + ∑ r ∈ Finset.Icc 1 T, (levels δ r + 1) = k := by
  let T := (k + 2) / 3
  let δ := 3 * T - k
  have ht : 4 ≤ T := by dsimp [T]; omega
  have hd : δ ≤ 2 := by dsimp [δ, T]; omega
  have hfive : 2 ≤ δ → 5 ≤ T := by dsimp [δ, T]; omega
  refine ⟨T, δ, by omega, hd, (levels_sum T δ ht hd hfive).trans ?_⟩
  dsimp [δ, T]
  omega

end OMA.A033496

namespace OMA.A033496

private theorem pow_four_precision (u : ℕ) :
    ∃ v : ℤ, v % 3 = 1 ∧ (4 : ℤ) ^ ((3 : ℕ) ^ u) = 1 + 3 ^ (u + 1) * v := by
  induction u with
  | zero => exact ⟨1, by decide, by norm_num⟩
  | succ u ih =>
    obtain ⟨v, hv, hpow⟩ := ih
    refine ⟨v + 3 ^ (u + 1) * v ^ 2 + 3 * (3 ^ u : ℤ) ^ 2 * v ^ 3, ?_, ?_⟩
    · simp [Int.add_emod, Int.mul_emod, pow_succ (3 : ℤ), hv]
    · rw [pow_succ (3 : ℕ), pow_mul, hpow]
      simp only [pow_succ (3 : ℤ)]
      ring

private theorem choose_digit (a q : ℤ) (ha : ¬(3 : ℤ) ∣ a) :
    ∃ d : ℕ, d ≤ 2 ∧ (3 : ℤ) ∣ q + (d : ℤ) * a := by
  have ha' : a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hq : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases ha' with ha' | ha' <;> rcases hq with hq | hq | hq
  all_goals first
    | exact ⟨0, by decide, by push_cast; omega⟩
    | exact ⟨1, by decide, by push_cast; omega⟩
    | exact ⟨2, by decide, by push_cast; omega⟩

private theorem pow_digit_modEq (p v : ℤ) (hp : (3 : ℤ) ∣ p) (d : ℕ) (hd : d ≤ 2) :
    (1 + p * v) ^ d ≡ 1 + (d : ℤ) * p * v [ZMOD 3 * p] := by
  interval_cases d
  · simp
  · simp
  · obtain ⟨q, rfl⟩ := hp
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(q * v ^ 2), ?_⟩
    push_cast
    ring

private theorem pow_four_lift (t : ℕ) (M A : ℤ)
    (hM : ¬(3 : ℤ) ∣ M) (hA : (3 : ℤ) ∣ M - A) :
    ∃ e : ℕ, (3 : ℤ) ^ (t + 1) ∣ M * (4 : ℤ) ^ e - A := by
  induction t with
  | zero => exact ⟨0, by simpa using hA⟩
  | succ u ih =>
    obtain ⟨e, q, hq⟩ := ih
    obtain ⟨v, hv, hpow⟩ := pow_four_precision u
    let p : ℤ := 3 ^ (u + 1)
    have hp3 : (3 : ℤ) ∣ p := dvd_pow_self 3 (by omega)
    have ha : ¬(3 : ℤ) ∣ M * (4 : ℤ) ^ e * v := by
      rw [Int.prime_three.dvd_mul, Int.prime_three.dvd_mul]
      have hf : ¬(3 : ℤ) ∣ (4 : ℤ) ^ e :=
        fun h => (by decide : ¬(3 : ℤ) ∣ 4) (Int.prime_three.dvd_of_dvd_pow h)
      have hv' : ¬(3 : ℤ) ∣ v := by omega
      simp [hM, hf, hv']
    obtain ⟨d, hd, w, hw⟩ := choose_digit (M * (4 : ℤ) ^ e * v) q ha
    refine ⟨e + (3 : ℕ) ^ u * d, ?_⟩
    have hmod :
        (4 : ℤ) ^ (e + (3 : ℕ) ^ u * d) ≡
          (4 : ℤ) ^ e * (1 + (d : ℤ) * p * v) [ZMOD 3 * p] := by
      rw [pow_add, pow_mul, hpow]
      exact (pow_digit_modEq p v hp3 d hd).mul_left _
    have hab :
        A ≡ M * ((4 : ℤ) ^ e * (1 + (d : ℤ) * p * v)) [ZMOD 3 * p] := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨w, ?_⟩
      calc
        _ = (M * (4 : ℤ) ^ e - A) + p * ((d : ℤ) * (M * (4 : ℤ) ^ e * v)) := by ring
        _ = (3 * p) * w := by
          change M * (4 : ℤ) ^ e - A = p * q at hq
          rw [hq]
          linear_combination p * hw
    have hh := Int.modEq_iff_dvd.mp (hab.trans (hmod.symm.mul_left M))
    simpa only [p, pow_succ', Nat.succ_eq_add_one] using hh

theorem large_pow_four (t : ℕ) (M A : ℤ)
    (hM : ¬(3 : ℤ) ∣ M) (hA : (3 : ℤ) ∣ M - A) (B : ℕ) :
    ∃ e : ℕ, B < 4 ^ e ∧ (3 : ℤ) ^ (t + 1) ∣ M * (4 : ℤ) ^ e - A := by
  obtain ⟨e, he⟩ := pow_four_lift t M A hM hA
  obtain ⟨v, _, hv⟩ := pow_four_precision t
  have hper : 1 ≡ (4 : ℤ) ^ ((3 : ℕ) ^ t) [ZMOD (3 : ℤ) ^ (t + 1)] := by
    apply Int.modEq_iff_dvd.mpr
    rw [hv]
    exact ⟨v, by ring⟩
  let e' := e + (3 : ℕ) ^ t * (B + 1)
  refine ⟨e', ?_, ?_⟩
  · apply lt_trans ?_ (Nat.lt_pow_self (n := e') (by decide))
    have h : B + 1 ≤ (3 : ℕ) ^ t * (B + 1) := by
      calc
        B + 1 = 1 * (B + 1) := by simp
        _ ≤ (3 : ℕ) ^ t * (B + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (by positivity))
    dsimp [e']
    omega
  · have hm := (hper.pow (B + 1)).mul_left (M * (4 : ℤ) ^ e)
    simp only [one_pow, mul_one, ← pow_mul] at hm
    rw [mul_assoc, ← pow_add] at hm
    exact Int.modEq_iff_dvd.mp ((Int.modEq_iff_dvd.mpr he).trans hm)

end OMA.A033496

namespace OMA.A033496

private def offset (δ : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | r + 2 => 2 ^ jump δ (r + 1) * offset δ (r + 1) + 3 ^ (r + 1)

private theorem offset_step (δ r : ℕ) (hr : 1 ≤ r) :
    offset δ (r + 1) = 2 ^ jump δ r * offset δ r + 3 ^ r := by
  cases r with
  | zero => omega
  | succ r => rfl

private theorem offset_mod_three (δ r : ℕ) (hδ : δ ≤ 2) (hr : 1 ≤ r) :
    (2 : ℤ) ^ scaleExponent δ r ≡ (offset δ r : ℤ) [ZMOD 3] := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hx : r = 0
    · subst r
      simp [scaleExponent_one, offset]
    · have hr' : 1 ≤ r := by omega
      rw [scaleExponent_step δ r hδ hr', offset_step δ r hr']
      push_cast
      have hp : (0 : ℤ) ≡ 3 ^ r [ZMOD 3] :=
        Int.modEq_zero_iff_dvd.mpr (dvd_pow_self 3 hx) |>.symm
      simpa [pow_add] using ((ih hr').mul_left ((2 : ℤ) ^ jump δ r)).add hp

private theorem offset_mod_two (δ r : ℕ) (hδ : δ ≤ 2) (hr : 1 ≤ r) :
    (offset δ r : ℤ) ≡ 1 [ZMOD 2] := by
  cases r with
  | zero => omega
  | succ r =>
    by_cases hx : r = 0
    · subst r
      exact Int.ModEq.refl 1
    · have hr' : 1 ≤ r := by omega
      have hj := (jump_bounds δ r hδ hr').1
      have he : (2 : ℤ) ^ jump δ r ≡ 0 [ZMOD 2] :=
        Int.modEq_zero_iff_dvd.mpr (dvd_pow_self 2 (by omega))
      have ho : (3 : ℤ) ^ r ≡ 1 [ZMOD 2] := by
        simpa using (show (3 : ℤ) ≡ 1 [ZMOD 2] by decide).pow r
      rw [offset_step δ r hr']
      push_cast
      simpa using (he.mul_right (offset δ r : ℤ)).add ho

private theorem not_three_dvd_two_pow (r : ℕ) : ¬(3 : ℤ) ∣ (2 : ℤ) ^ r :=
  fun h => (by decide : ¬(3 : ℤ) ∣ 2) (Int.prime_three.dvd_of_dvd_pow h)

theorem construct (T δ : ℕ) (hT : 1 ≤ T) (hδ : δ ≤ 2) :
    ∃ e : ℕ, ∃ y : ℕ → ℕ, 2 ≤ e ∧
      (∀ r, 1 ≤ r → r ≤ T → 1 < y r ∧ y r % 2 = 1 ∧
        2 ^ levels δ r * y r ≤ 2 ^ e ∧ 2 ^ e < 2 ^ (levels δ r + 1) * y r) ∧
      3 * y 1 + 1 = 2 ^ e ∧
      (∀ r, 1 ≤ r → r < T → 3 * y (r + 1) + 1 = 2 ^ jump δ r * y r) ∧
      3 ∣ y T := by
  let bound (r : ℕ) := 3 ^ r + offset δ r + 2 ^ (levels δ r + 1) * offset δ r
  let B := 4 + (Finset.Icc 1 T).sup bound
  obtain ⟨f, hBn, hterm⟩ := large_pow_four T (2 ^ scaleExponent δ T) (offset δ T)
    (not_three_dvd_two_pow _) (Int.modEq_iff_dvd.mp (offset_mod_three δ T hδ hT).symm) B
  let n : ℕ := 4 ^ f
  have hnlarge : 4 < n := by dsimp [B, n] at hBn ⊢; omega
  have hf : 1 ≤ f := by
    by_contra! hf
    have hzero : f = 0 := by omega
    have hsmall : n = 1 := by simp [n, hzero]
    omega
  have hnsize : n = 2 ^ (2 * f) := by simp [n, pow_mul]
  have hnmod : (n : ℤ) ≡ 0 [ZMOD 2] := by
    push_cast [n]
    apply Int.modEq_zero_iff_dvd.mpr
    exact (by decide : (2 : ℤ) ∣ 4).trans (dvd_pow_self 4 (by omega))
  have hbig (r : ℕ) (hr : 1 ≤ r) (hrt : r ≤ T) :
      (3 : ℤ) ^ r + (offset δ r : ℤ) + (2 : ℤ) ^ (levels δ r + 1) * (offset δ r : ℤ) < n := by
    have hb : bound r ≤ B := calc
      bound r ≤ (Finset.Icc 1 T).sup bound := Finset.le_sup (Finset.mem_Icc.mpr ⟨hr, hrt⟩)
      _ ≤ B := by dsimp [B]; omega
    exact_mod_cast (show bound r < n from hb.trans_lt hBn)
  let z (r : ℕ) : ℤ := (2 : ℤ) ^ scaleExponent δ r * (n : ℤ) - (offset δ r : ℤ)
  have z_step (r : ℕ) (hr : 1 ≤ r) :
      z (r + 1) = (2 : ℤ) ^ jump δ r * z r - 3 ^ r := by
    dsimp [z]
    rw [scaleExponent_step δ r hδ hr, offset_step δ r hr, pow_add]
    push_cast
    ring
  have z_terminal : (3 : ℤ) ^ (T + 1) ∣ z T := by
    simpa only [z, n, Nat.cast_pow, Nat.cast_ofNat] using hterm
  have z_dvd (r : ℕ) (hr : 1 ≤ r) (hrt : r ≤ T) : (3 : ℤ) ^ r ∣ z r := by
    refine Nat.decreasingInduction' (P := fun i => (3 : ℤ) ^ i ∣ z i) ?_ hrt
      ((pow_dvd_pow (3 : ℤ) (Nat.le_succ T)).trans z_terminal)
    intro i hiT hri ih
    have hi := hr.trans hri
    replace ih := (pow_dvd_pow (3 : ℤ) (Nat.le_succ i)).trans ih
    rw [z_step i hi] at ih
    have hm := dvd_add ih (dvd_refl ((3 : ℤ) ^ i))
    rw [sub_add_cancel] at hm
    have hc : IsCoprime (3 : ℤ) 2 := ⟨1, -1, by decide⟩
    exact hc.pow.dvd_of_dvd_mul_left hm
  have z_pos (r : ℕ) (hr : 1 ≤ r) (hrt : r ≤ T) : (3 : ℤ) ^ r < z r := by
    have hb := hbig r hr hrt
    have hp : 0 < (2 : ℤ) ^ scaleExponent δ r := by positivity
    have hle : 1 ≤ (2 : ℤ) ^ scaleExponent δ r := by omega
    have hn := mul_le_mul_of_nonneg_right hle (Int.natCast_nonneg n)
    have hc : 0 ≤ (2 : ℤ) ^ (levels δ r + 1) * (offset δ r : ℤ) := by positivity
    dsimp [z]
    linarith
  let y (r : ℕ) : ℕ := (z r / (3 : ℤ) ^ r).toNat
  have y_eq (r : ℕ) (hr : 1 ≤ r) (hrt : r ≤ T) : z r = (3 : ℤ) ^ r * (y r : ℤ) := by
    have hp : 0 < (3 : ℤ) ^ r := by positivity
    have hz := z_pos r hr hrt
    have hn : 0 ≤ z r := by omega
    dsimp [y]
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn hp.le), mul_comm,
      Int.ediv_mul_cancel (z_dvd r hr hrt)]
  have y_pos (r : ℕ) (hr : 1 ≤ r) (hrt : r ≤ T) : 1 < y r := by
    by_contra! hy
    have hy' : (y r : ℤ) ≤ 1 := by exact_mod_cast hy
    have hh := mul_le_mul_of_nonneg_left hy' (show 0 ≤ (3 : ℤ) ^ r by positivity)
    rw [← y_eq r hr hrt, mul_one] at hh
    exact (not_lt_of_ge hh) (z_pos r hr hrt)
  have y_odd (r : ℕ) (hr : 1 ≤ r) (hrt : r ≤ T) : y r % 2 = 1 := by
    have hp : (3 : ℤ) ^ r ≡ 1 [ZMOD 2] := by
      simpa using (show (3 : ℤ) ≡ 1 [ZMOD 2] by decide).pow r
    have ha : z r ≡ 1 [ZMOD 2] := by
      have hn := (hnmod.mul_left ((2 : ℤ) ^ scaleExponent δ r)).sub (offset_mod_two δ r hδ hr)
      exact (show z r ≡ -1 [ZMOD 2] from by simpa [z] using hn).trans (by decide)
    have hb := hp.mul_right (y r : ℤ)
    rw [← y_eq r hr hrt, one_mul] at hb
    exact Int.natCast_modEq_iff.mp (hb.symm.trans ha)
  have y_bounds (r : ℕ) (hr : 1 ≤ r) (hrt : r ≤ T) :
      2 ^ levels δ r * y r ≤ n ∧ n < 2 ^ (levels δ r + 1) * y r := by
    let J := levels δ r
    let b := height r
    have hb := height_bounds r
    have he := scaleExponent_add_levels δ r hr
    have scale (i : ℕ) :
        (2 : ℤ) ^ (J + i) * (2 : ℤ) ^ scaleExponent δ r = (2 : ℤ) ^ (b + i) := by
      rw [← pow_add]
      congr 1
      dsimp [J, b]
      omega
    have expand (i : ℕ) :
        (3 : ℤ) ^ r * ((2 : ℤ) ^ (J + i) * (y r : ℤ)) =
          (2 : ℤ) ^ (b + i) * n - (2 : ℤ) ^ (J + i) * (offset δ r : ℤ) := by
      calc
        _ = (2 : ℤ) ^ (J + i) * ((3 : ℤ) ^ r * (y r : ℤ)) := by ring
        _ = (2 : ℤ) ^ (J + i) * z r := by rw [y_eq r hr hrt]
        _ = _ := by dsimp [z]; rw [mul_sub, ← mul_assoc, scale]
    have hp : 0 < (3 : ℤ) ^ r := by positivity
    have hn : 0 ≤ (n : ℤ) := by positivity
    constructor
    · have hlo : (2 : ℤ) ^ b ≤ 3 ^ r := by exact_mod_cast hb.1
      have hm := mul_le_mul_of_nonneg_right hlo hn
      have hx : 0 ≤ (2 : ℤ) ^ J * (offset δ r : ℤ) := by positivity
      have hh := expand 0
      simp only [Nat.add_zero] at hh
      have h : (3 : ℤ) ^ r * ((2 : ℤ) ^ J * (y r : ℤ)) ≤ (3 : ℤ) ^ r * n := by
        linarith
      exact_mod_cast (mul_le_mul_iff_of_pos_left hp).mp h
    · have hhi : (3 : ℤ) ^ r + 1 ≤ 2 ^ (b + 1) := by exact_mod_cast hb.2
      have hm := mul_le_mul_of_nonneg_right hhi hn
      rw [add_mul, one_mul] at hm
      have hb' := hbig r hr hrt
      have hsmall : (2 : ℤ) ^ (J + 1) * (offset δ r : ℤ) < n := by
        have : 0 ≤ (offset δ r : ℤ) := by positivity
        dsimp [J]
        linarith
      have hh := expand 1
      have h : (3 : ℤ) ^ r * n < (3 : ℤ) ^ r * ((2 : ℤ) ^ (J + 1) * (y r : ℤ)) := by
        linarith
      exact_mod_cast (mul_lt_mul_iff_of_pos_left hp).mp h
  have y_first : 3 * y 1 + 1 = n := by
    have he := y_eq 1 le_rfl hT
    simp [z, scaleExponent_one, offset] at he
    omega
  have y_step (r : ℕ) (hr : 1 ≤ r) (hrt : r < T) :
      3 * y (r + 1) + 1 = 2 ^ jump δ r * y r := by
    have hz := z_step r hr
    rw [y_eq (r + 1) (by omega) (by omega), y_eq r hr hrt.le, pow_succ (3 : ℤ)] at hz
    have he : (3 : ℤ) ^ r * (3 * (y (r + 1) : ℤ) + 1) =
        (3 : ℤ) ^ r * ((2 : ℤ) ^ jump δ r * (y r : ℤ)) := by
      linear_combination hz
    exact_mod_cast mul_left_cancel₀ (by positivity : (3 : ℤ) ^ r ≠ 0) he
  have y_terminal : 3 ∣ y T := by
    rw [y_eq T hT le_rfl, pow_succ (3 : ℤ)] at z_terminal
    obtain ⟨w, hw⟩ := z_terminal
    have he : (3 : ℤ) ^ T * (y T : ℤ) = (3 : ℤ) ^ T * (3 * w) := by rw [hw]; ring
    exact_mod_cast (show (3 : ℤ) ∣ (y T : ℤ) from
      ⟨w, mul_left_cancel₀ (by positivity : (3 : ℤ) ^ T ≠ 0) he⟩)
  refine ⟨2 * f, y, by omega, ?_, ?_, y_step, y_terminal⟩
  · intro r hr hrt
    simpa only [← hnsize] using
      ⟨y_pos r hr hrt, y_odd r hr hrt, y_bounds r hr hrt⟩
  · simpa only [← hnsize] using y_first

end OMA.A033496

theorem OMA.solution : type_of% @OMA.S_oeis_a033496.main := by
  intro k hk
  obtain ⟨T, δ, hT, hδ, hcount⟩ := OMA.A033496.choose_levels k hk
  obtain ⟨e, y, he, hy, hfirst, hstep, hlast⟩ := OMA.A033496.construct T δ hT hδ
  refine ⟨2 ^ e, ?_⟩
  exact (A033496Fan.cardinality y (OMA.A033496.levels δ) (OMA.A033496.jump δ) he hT
    (fun r hr hrt => (hy r hr hrt).2.1) (fun r hr hrt => (hy r hr hrt).1)
    (fun r _ _ => OMA.A033496.levels_bounds δ r) (fun r hr hrt => (hy r hr hrt).2.2)
    hfirst (fun r hr _ => OMA.A033496.jump_bounds δ r hδ hr) hstep hlast).trans hcount
