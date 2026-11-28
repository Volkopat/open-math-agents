import OMAReductions.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_variants_set_R1

-- Antihydra reduction by the even run preceding the first negative balance.
-- Credit: @Alewawa

namespace OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_variants_set_R1_H2_R1

open Finset

/-- The final odd run follows one even term. Its initial value is six modulo nine. -/
def H1 : Prop :=
  ∀ (a : ℕ → ℕ), a 0 = 8 → (∀ n, a (n + 1) = 3 * a n / 2) →
    ∀ t r : ℕ, 300000 < t + r → 3 ≤ r → 5 * r ≤ 3 * t + 18 →
      a t % 9 = 6 →
      t + r = 3 * ((Ico 0 t).filter fun i ↦ Even (a i)).card + 1 →
      ¬ 2 ^ r ∣ (a t - 1)

/-- The final odd run follows at least two even terms. Its initial value is divisible by nine. -/
def H2 : Prop :=
  ∀ (a : ℕ → ℕ), a 0 = 8 → (∀ n, a (n + 1) = 3 * a n / 2) →
    ∀ t r : ℕ, 300000 < t + r → 5 ≤ r → 5 * r ≤ 3 * t + 18 →
      a t % 9 = 0 →
      t + r = 3 * ((Ico 0 t).filter fun i ↦ Even (a i)).card + 1 →
      ¬ 2 ^ r ∣ (a t - 1)

lemma even_count_succ (a : ℕ → ℕ) (n : ℕ) :
    ((Ico 0 (n + 1)).filter fun i ↦ Even (a i)).card =
      ((Ico 0 n).filter fun i ↦ Even (a i)).card + if a n % 2 = 0 then 1 else 0 := by
  simp only [← range_eq_Ico, card_filter, sum_range_succ, Nat.even_iff]

lemma parity_card (a : ℕ → ℕ) (n : ℕ) :
    ((Ico 0 n).filter fun i ↦ Even (a i)).card +
      ((Ico 0 n).filter fun i ↦ Odd (a i)).card = n := by
  simpa only [Nat.not_even_iff_odd, Nat.card_Ico, Nat.sub_zero] using
    card_filter_add_card_filter_not (s := Ico 0 n) (fun i ↦ Even (a i))

private lemma odd_suffix (a : ℕ → ℕ) (n : ℕ) :
    ∃ t ≤ n, (0 < t → a (t - 1) % 2 = 0) ∧
      (∀ i, t ≤ i → i < n → a i % 2 = 1) := by
  induction n with
  | zero => exact ⟨0, by omega, by omega, by omega⟩
  | succ n ih =>
    by_cases he : a n % 2 = 0
    · refine ⟨n + 1, by omega, ?_, by omega⟩
      intro _
      simpa using he
    · obtain ⟨t, ht, hprev, hrun⟩ := ih
      refine ⟨t, by omega, hprev, ?_⟩
      intro i hi hin
      by_cases h : i = n
      · subst i
        omega
      · exact hrun i hi (by omega)

private lemma odd_block_count (a : ℕ → ℕ) (t r : ℕ)
    (ho : ∀ i < r, a (t + i) % 2 = 1) :
    ((Ico 0 (t + r)).filter fun i ↦ Even (a i)).card =
      ((Ico 0 t).filter fun i ↦ Even (a i)).card := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.add_succ, even_count_succ, ih (fun i hi => ho i (by omega)),
      if_neg (by have h := ho r (by omega); omega), Nat.add_zero]

private lemma odd_block_dvd (a : ℕ → ℕ)
    (step : ∀ n, a (n + 1) = 3 * a n / 2) (r : ℕ) :
    ∀ t, (∀ i < r, a (t + i) % 2 = 1) → 2^r ∣ a t - 1 := by
  induction r with
  | zero =>
    intro t ht
    simp
  | succ r ih =>
    intro t ht
    have hodd : a t % 2 = 1 := by simpa using ht 0 (by omega)
    have htail : 2^r ∣ a (t + 1) - 1 := ih (t + 1) (by
      intro i hi
      rw [show t + 1 + i = t + (i + 1) by omega]
      exact ht (i + 1) (by omega))
    obtain ⟨q, hq⟩ := htail
    have hstep := step t
    have hf : 2 * (a (t + 1) - 1) = 3 * (a t - 1) := by omega
    have hdiv : 2^(r + 1) ∣ 3 * (a t - 1) := by
      refine ⟨q, ?_⟩
      rw [← hf, hq, pow_succ]
      ac_rfl
    exact ((show Nat.Coprime 2 3 by decide).pow_left _).dvd_of_dvd_mul_left hdiv

private lemma growth_five (a : ℕ → ℕ) (step : ∀ n, a (n + 1) = 3 * a n / 2) (k : ℕ) :
    a (k + 5) ≤ 8 * a k := by
  have h1 := step k
  have h2 := step (k + 1)
  have h3 := step (k + 2)
  have h4 := step (k + 3)
  have h5 := step (k + 4)
  rw [show k+1+1 = k+2 by omega] at h2
  rw [show k+2+1 = k+3 by omega] at h3
  rw [show k+3+1 = k+4 by omega] at h4
  rw [show k+4+1 = k+5 by omega] at h5
  omega

private lemma growth_bound (a : ℕ → ℕ) (a0 : a 0 = 8)
    (step : ∀ n, a (n + 1) = 3 * a n / 2) (t : ℕ) :
    a t ≤ 2^(3 * (t / 5) + 3 + t % 5) := by
  have base (j : ℕ) : a (5*j) ≤ 2^(3*j+3) := by
    induction j with
    | zero => simp [a0]
    | succ j ih =>
      rw [show 5*(j+1) = 5*j+5 by omega, show 3*(j+1)+3 = (3*j+3)+3 by omega, pow_add]
      exact (growth_five a step (5*j)).trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left 8 ih)
  have tail (k j : ℕ) : a (k+j) ≤ a k * 2^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        a (k+(j+1)) ≤ 2 * a (k+j) := by
          rw [← Nat.add_assoc, step]
          omega
        _ ≤ 2 * (a k * 2^j) := Nat.mul_le_mul_left 2 ih
        _ = a k * 2^(j+1) := by rw [pow_succ]; ac_rfl
  have ht : t = 5 * (t / 5) + t % 5 := by omega
  calc
    a t = a (5*(t/5) + t%5) := congrArg a ht
    _ ≤ a (5*(t/5)) * 2^(t%5) := tail _ _
    _ ≤ 2^(3*(t/5)+3) * 2^(t%5) := Nat.mul_le_mul_right _ (base _)
    _ = _ := (pow_add _ _ _).symm

private lemma odd_run_bound (a : ℕ → ℕ) (a0 : a 0 = 8)
    (step : ∀ n, a (n + 1) = 3 * a n / 2) (t r : ℕ) (hd : 2^r ∣ a t - 1) :
    5*r ≤ 3*t + 18 := by
  have hpos (j : ℕ) : 8 ≤ a j := by
    induction j with
    | zero => omega
    | succ j ih => have := step j; omega
  have hle := Nat.le_of_dvd (show 0 < a t - 1 by have := hpos t; omega) hd
  have hg := growth_bound a a0 step t
  have hp : 2^r < 2^(3*(t/5)+3+t%5) := by omega
  have hr := (Nat.pow_lt_pow_iff_right (show 1 < (2 : ℕ) by decide)).mp hp
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Counts for all prefixes through 300000. For each 128-step block only
the low 128 bits are needed to count its even terms. A large enough
balance at a checked block boundary covers every prefix up to the next
boundary, since the balance can decrease by at most one at each step. -/
lemma finite_range (a : ℕ → ℕ) (a0 : a 0 = 8)
    (step : ∀ i, a (i+1) = 3*a i/2) (n : ℕ) (hn : n ≤ 300000) :
    n ≤ 3*((Ico 0 n).filter fun i ↦ Even (a i)).card := by
  let E (i : ℕ) := ((Ico 0 i).filter fun j ↦ Even (a j)).card
  let pairStep (p : ℕ × ℕ) : ℕ × ℕ :=
    (3*p.1/2, p.2 + if p.1%2 = 0 then 1 else 0)
  let small (k x e : ℕ) : ℕ × ℕ :=
    Nat.rec (x,e) (fun _ p => pairStep p) k
  let fast (x e : ℕ) : ℕ × ℕ :=
    let low := small 128 (x % 2^128) e
    (low.1 + 3^128*(x / 2^128), low.2)
  let early (i : ℕ) : ℕ × ℕ × Bool :=
    Nat.rec (8,0,true) (fun j s =>
      let next := pairStep (s.1,s.2.1)
      (next.1, next.2, s.2.2 && decide (j+1 ≤ 3*next.2))) i
  let blocks (i : ℕ) : ℕ × ℕ × Bool :=
    Nat.rec (8,0,true) (fun j s =>
      let next := fast s.1 s.2.1
      (next.1, next.2, s.2.2 && (if 4 ≤ j then decide (128*j+128 ≤ 3*s.2.1) else true))) i
  have checkEarly : (early 512).2.2 = true := by decide +revert +kernel
  have checkBlocks : (blocks 1600).2.2 = true ∧ 300000 ≤ 3*(blocks 1600).2.1 := by
    decide +revert +kernel
  have e0 : E 0 = 0 := by simp [E]
  have sameStep (i : ℕ) : pairStep (a i,E i) = (a (i+1),E (i+1)) :=
    Prod.ext (step i).symm (even_count_succ a i).symm
  have earlier (x y : ℕ) (h : x ≤ y) : E x ≤ E y := by
    apply card_le_card
    intro i hi
    obtain ⟨hr, he⟩ := mem_filter.mp hi
    obtain ⟨hz, hx⟩ := mem_Ico.mp hr
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hz, hx.trans_le h⟩, he⟩
  have earlyState (j : ℕ) : ((early j).1,(early j).2.1) = (a j,E j) := by
    induction j with
    | zero => simp [early, a0, e0]
    | succ j ih =>
      change pairStep ((early j).1,(early j).2.1) = (a (j+1),E (j+1))
      rw [ih, sameStep]
  have earlySafe (j : ℕ) (h : (early j).2.2 = true) : ∀ i ≤ j, i ≤ 3*E i := by
    induction j with
    | zero => intro i hi; omega
    | succ j ih =>
      have h' : ((early j).2.2 &&
          decide (j+1 ≤ 3*(pairStep ((early j).1,(early j).2.1)).2)) = true := h
      obtain ⟨hok, hnew⟩ := Bool.and_eq_true_iff.mp h'
      rw [earlyState, sameStep] at hnew
      intro i hi
      rcases eq_or_lt_of_le hi with rfl | hlt
      · exact of_decide_eq_true hnew
      · exact ih hok i (by omega)
  have smallState (s k : ℕ) :
      small k (a s) (E s) = (a (s+k),E (s+k)) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change pairStep (small k (a s) (E s)) = (a (s+(k+1)), E (s+(k+1)))
      rw [ih, sameStep, Nat.add_assoc]
  have smallCons (k : ℕ) (x e : ℕ) :
      small (k+1) x e = small k (pairStep (x,e)).1 (pairStep (x,e)).2 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change pairStep (small (k+1) x e) =
        pairStep (small k (pairStep (x,e)).1 (pairStep (x,e)).2)
      rw [ih]
  have pairShift (x e j : ℕ) :
      pairStep (x + 2*j,e) = ((pairStep (x,e)).1 + 3*j,(pairStep (x,e)).2) := by
    have hdiv : 3*(x+2*j)/2 = 3*x/2 + 3*j := by omega
    have hmod : (x+2*j)%2 = x%2 := by omega
    simp only [pairStep, hdiv, hmod]
  have smallShift (k : ℕ) :
      ∀ x e j : ℕ, small k (x+2^k*j) e = ((small k x e).1+3^k*j,(small k x e).2) := by
    induction k with
    | zero => intro x e j; simp [small]
    | succ k ih =>
      intro x e j
      rw [smallCons k (x+2^(k+1)*j), smallCons k x]
      rw [show 2^(k+1)*j = 2*(2^k*j) by rw [pow_succ]; ac_rfl, pairShift]
      change small k ((pairStep (x,e)).1 + 3*(2^k*j)) (pairStep (x,e)).2 = _
      rw [show 3*(2^k*j) = 2^k*(3*j) by ac_rfl, ih]
      rw [show 3^k*(3*j) = 3^(k+1)*j by rw [pow_succ]; ac_rfl]
  have fastState (s : ℕ) : fast (a s) (E s) = (a (s+128),E (s+128)) := by
    change ((small 128 (a s % 2^128) (E s)).1 + 3^128*(a s / 2^128),
      (small 128 (a s % 2^128) (E s)).2) = _
    rw [← smallShift, Nat.mod_add_div, smallState]
  have blockState (j : ℕ) : ((blocks j).1,(blocks j).2.1) = (a (128*j),E (128*j)) := by
    induction j with
    | zero => simp [blocks, a0, e0]
    | succ j ih =>
      change fast (blocks j).1 (blocks j).2.1 = _
      have h := congrArg Prod.fst ih
      have he := congrArg Prod.snd ih
      change (blocks j).1 = a (128*j) at h
      change (blocks j).2.1 = E (128*j) at he
      rw [h, he, fastState, Nat.mul_succ]
  have blockSafe (j : ℕ) (h : (blocks j).2.2 = true) :
      ∀ b < j, 4 ≤ b → 128*b+128 ≤ 3*E (128*b) := by
    induction j with
    | zero => omega
    | succ j ih =>
      have h' : ((blocks j).2.2 &&
          (if 4 ≤ j then decide (128*j+128 ≤ 3*(blocks j).2.1) else true)) = true := h
      obtain ⟨hok, hcurr⟩ := Bool.and_eq_true_iff.mp h'
      intro b hb hb4
      by_cases he : b = j
      · subst b
        rw [if_pos hb4] at hcurr
        have h := congrArg Prod.snd (blockState j)
        change (blocks j).2.1 = E (128*j) at h
        rw [h] at hcurr
        exact of_decide_eq_true hcurr
      · exact ih hok b (by omega) hb4
  change n ≤ 3*E n
  by_cases hnEarly : n ≤ 512
  · exact earlySafe 512 checkEarly n hnEarly
  by_cases hnBlock : n ≤ 204800
  · let j := (n-1)/128
    have hstart : 128*j ≤ n := by dsimp [j]; omega
    have hnext : n ≤ 128*j+128 := by dsimp [j]; omega
    have hj : j < 1600 := by dsimp [j]; omega
    have hj4 : 4 ≤ j := by dsimp [j]; omega
    exact hnext.trans ((blockSafe 1600 checkBlocks.1 j hj hj4).trans
      (Nat.mul_le_mul_left 3 (earlier _ _ hstart)))
  have h := congrArg Prod.snd (blockState 1600)
  change (blocks 1600).2.1 = E 204800 at h
  have hb := checkBlocks.2
  rw [h] at hb
  exact hn.trans (hb.trans (Nat.mul_le_mul_left 3 (earlier _ _ (by omega))))

theorem main : H1 → H2 →
    OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_variants_set_R1.H2 := by
  intro hsingle hmultiple a a0 step n _
  let E (i : ℕ) := ((Ico 0 i).filter fun j ↦ Even (a j)).card
  have esucc (i : ℕ) : E (i+1) = E i + (if a i % 2 = 0 then 1 else 0) :=
    even_count_succ a i
  have all : ∀ i, i ≤ 3 * E i := by
    by_contra! hex
    let m := Nat.find hex
    have hm : 3 * E m < m := Nat.find_spec hex
    have hprior (i : ℕ) (hi : i < m) : i ≤ 3 * E i :=
      Nat.le_of_not_gt (Nat.find_min hex hi)
    have hlarge : 300000 < m := by
      by_contra! h
      have := finite_range a a0 step m h
      change m ≤ 3 * E m at this
      omega
    have hlast : a (m-1) % 2 = 1 := by
      have hs := esucc (m-1)
      have hp := hprior (m-1) (by omega)
      rw [show m-1+1 = m by omega] at hs
      by_contra! he
      rw [if_pos (by omega : a (m-1)%2=0)] at hs
      omega
    obtain ⟨t, ht, hprev, hrun⟩ := odd_suffix a m
    have htm : t < m := by
      by_contra! hn
      have heq : t = m := by omega
      subst t
      have := hprev (by omega)
      omega
    have ha1 := step 0
    have ht2 : 2 ≤ t := by
      by_contra! h
      have he : a t % 2 = 1 := hrun t (by omega) htm
      have ht01 : t = 0 ∨ t = 1 := by omega
      rcases ht01 with rfl | rfl
      · simp [a0] at he
      · have haOne : a 1 = 12 := by simpa [a0] using ha1
        simp [haOne] at he
    let r := m-t
    have hsum : t+r = m := by dsimp [r]; omega
    have hor : ∀ i < r, a (t+i)%2=1 := fun i hi => hrun (t+i) (by omega) (by omega)
    have hsEq : E m = E t := by
      have h := odd_block_count a t r hor
      rw [hsum] at h
      exact h
    have hprevCount := hprior (m-1) (by omega)
    have hsame := esucc (m-1)
    rw [show m-1+1=m by omega, if_neg (by omega : a (m-1)%2 ≠ 0), Nat.add_zero] at hsame
    have hfailure : t+r = 3 * E t + 1 := by omega
    have hprevEven := hprev (by omega : 0 < t)
    have hprevGood := hprior (t-1) (by omega)
    have hcount := esucc (t-1)
    rw [show t-1+1=t by omega, if_pos hprevEven] at hcount
    have hr3 : 3 ≤ r := by omega
    have hd := odd_block_dvd a step r t hor
    have hg := odd_run_bound a a0 step t r hd
    have ha := step (t-1)
    have hb := step (t-2)
    rw [show t-1+1=t by omega] at ha
    rw [show t-2+1=t-1 by omega] at hb
    by_cases he : a (t-2)%2=0
    · have mod9 : a t % 9 = 0 := by omega
      have hold := hprior (t-2) (by omega)
      have hcount2 := esucc (t-2)
      rw [show t-2+1=t-1 by omega, if_pos he] at hcount2
      exact hmultiple a a0 step t r (by omega) (by omega) hg mod9 hfailure hd
    · have mod9 : a t % 9 = 6 := by omega
      exact hsingle a a0 step t r (by omega) hr3 hg mod9 hfailure hd
  have hn := all n
  have hp := parity_card a n
  change n ≤ 3 * ((Ico 0 n).filter fun j ↦ Even (a j)).card at hn
  omega

end OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_variants_set_R1_H2_R1
