import OMAStatements.S_oeis_a006165

/-!
The dyadic block formula follows from the defining recurrence. Iterating gives the formula
published by Byungwoong Yoo, and the first five identities follow by evaluating the resulting
affine expressions on each of four subintervals of a dyadic block. The sixth identity follows
from the clipped iterate formula. For (vii), the repeated values occupy the initial plateau of
each iterate block, whose two neighbours give the exact fibre.

Conjectures: Peter Bala, OEIS A006165, https://oeis.org/A006165.
Prior work on the iterate and repeated-value formulas: Byungwoong Yoo,
https://woongworks.com/en-a006165-bala-conjecture-iterates/.
-/

namespace A006165

open OMA.S_oeis_a006165

private theorem even_eq (n : ℕ) (hn : 2 ≤ n) : a (2*n) = 2 * a n := by
  obtain ⟨m, hm⟩ : ∃ m, 2*n = m+3 := ⟨2*n-3, by omega⟩
  rw [hm, a, if_pos (by omega)]
  congr 2
  omega

private theorem odd_eq (n : ℕ) (hn : 1 ≤ n) : a (2*n+1) = a (n+1) + a n := by
  obtain ⟨m, hm⟩ : ∃ m, 2*n+1 = m+3 := ⟨2*n-2, by omega⟩
  rw [hm, a, if_neg (by omega)]
  rw [show (m+3)/2 = n by omega]

/-- The classical dyadic piecewise-linear formula recorded in the OEIS. -/
theorem a_block (j d : ℕ) (hd : d ≤ 2^(j+1)) :
    a (2^(j+1)+d) = 2^j + min d (2^j) := by
  induction j generalizing d with
  | zero =>
    norm_num at hd
    interval_cases d <;> norm_num [a]
  | succ j ih =>
    let p := 2^j
    have hp : 0 < p := by positivity
    change a (2^(j+1+1)+d) = 2^(j+1) + min d (2^(j+1))
    have pow₁ : 2^(j+1) = 2*p := by simp [p, pow_succ, Nat.mul_comm]
    have pow₂ : 2^(j+1+1) = 2*(2*p) := by rw [pow_succ, pow₁, Nat.mul_comm]
    rw [pow₂] at hd ⊢
    rw [pow₁]
    by_cases he : d % 2 = 0
    · rw [show 2*(2*p)+d=2*(2*p+d/2) by omega, even_eq _ (by omega)]
      have hi := ih (d/2) (by rw [pow₁]; omega)
      rw [pow₁] at hi
      change a (2*p+d/2) = p + min (d/2) p at hi
      rw [hi]
      omega
    · rw [show 2*(2*p)+d=2*(2*p+d/2)+1 by omega, odd_eq _ (by omega)]
      have hi := ih (d/2) (by rw [pow₁]; omega)
      have hj := ih (d/2+1) (by rw [pow₁]; omega)
      rw [pow₁] at hi hj
      change a (2*p+d/2) = p + min (d/2) p at hi
      change a (2*p+(d/2+1)) = p + min (d/2+1) p at hj
      rw [Nat.add_assoc, hj, hi]
      omega

/-- The iterate formula of Byungwoong Yoo, obtained by composing the dyadic pieces. -/
theorem iter_block (k j d : ℕ) (hk : 1≤k) (hd : d ≤ 2^(k+j)) :
    a^[k] (2^(k+j)+d) = 2^j + min d (2^j) := by
  induction k generalizing j d with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      simpa [Nat.add_comm 1 j] using a_block j d (by simpa [Nat.add_comm 1 j] using hd)
    | succ k =>
      rw [Function.iterate_succ_apply']
      have ge : k+1+1+j = k+1+(j+1) := by omega
      rw [ge] at hd ⊢
      rw [ih (j+1) d (by omega) hd, a_block j _ (min_le_right ..)]
      have hle : 2^j ≤ 2^(j+1) := by rw [pow_succ]; omega
      omega

theorem iter_small (k n : ℕ) (hn : 1≤n) (hl : n≤2^k) : a^[k] n=1 := by
  induction k generalizing n with
  | zero =>
    simp at hl
    simpa using (show n=1 by omega)
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : n≤2^k
    · rw [ih n hn h]
      norm_num [a]
    · have hn' : n=2^k+(n-2^k) := by omega
      cases k with
      | zero =>
        norm_num at h hl
        rw [show n=2 by omega]
        norm_num [a]
      | succ k =>
        have bound : n-2^(k+1) ≤ 2^(k+1+0) := by
          simp only [Nat.add_zero]
          change n ≤ 2^((k+1)+1) at hl
          rw [pow_succ] at hl
          omega
        have hi := iter_block (k+1) 0 (n-2^(k+1)) (by omega) bound
        simp only [Nat.add_zero, pow_zero] at hi
        rw [← hn'] at hi
        rw [hi, show min (n-2^(k+1)) 1 = 1 by omega]
        norm_num [a]

end A006165

namespace A006165

open OMA.S_oeis_a006165

/-- The first five identities, grouped at their common input. -/
private def FixedAt (n : ℕ) : Prop :=
  a n + a (n - a (n - a (n - a (n - a n)))) = n ∧
  a (n - a (n - a (n - a n))) = a (n - a (n - a (n - a (n - a (n - a n))))) ∧
  a^[2] n = a (n - a (n - a (n - a n))) ∧
  n - a n = a (n - a^[2] n) ∧
  a (n - a n) = a^[2] (n - a^[2] (n - a^[2] (n - a^[2] n)))

private theorem fixed_on_block {n p : ℕ} (hn : 16*p ≤ n) (hn' : n ≤ 32*p)
    (low : ∀ x, 8*p ≤ x → x ≤ 16*p → a x = 4*p + min (x-8*p) (4*p))
    (high : ∀ x, 16*p ≤ x → x ≤ 32*p → a x = 8*p + min (x-16*p) (8*p)) :
    FixedAt n := by
  have r₁ (x : ℕ) (h : 8*p ≤ x) (h' : x ≤ 12*p) : a x = x-4*p := by
    rw [low x h (by omega), min_eq_left (by omega)]
    omega
  have r₂ (x : ℕ) (h : 12*p ≤ x) (h' : x ≤ 16*p) : a x = 8*p := by
    rw [low x (by omega) h', min_eq_right (by omega)]
    omega
  have r₃ (x : ℕ) (h : 16*p ≤ x) (h' : x ≤ 24*p) : a x = x-8*p := by
    rw [high x h (by omega), min_eq_left (by omega)]
    omega
  have r₄ (x : ℕ) (h : 24*p ≤ x) (h' : x ≤ 32*p) : a x = 16*p := by
    rw [high x (by omega) h', min_eq_right (by omega)]
    omega
  have cases : n ≤ 20*p ∨ (20*p ≤ n ∧ n ≤ 24*p) ∨
      (24*p ≤ n ∧ n ≤ 28*p) ∨ 28*p ≤ n := by omega
  rcases cases with c | ⟨c, d⟩ | ⟨c, d⟩ | c <;>
    simp (disch := omega) only [FixedAt, Function.iterate_succ_apply, Function.iterate_zero_apply,
      r₁, r₂, r₃, r₄] <;>
    (repeat' apply And.intro) <;> first | trivial | omega

private theorem fixed_at
    (block : ∀ j d : ℕ, d ≤ 2^(j+1) →
      a (2^(j+1)+d) = 2^j + min d (2^j)) (n : ℕ) (hn : 2 ≤ n) : FixedAt n := by
  by_cases small : n < 16
  · unfold FixedAt
    interval_cases n <;> decide +kernel
  let j := Nat.log 2 (n/16)
  let p := 2^j
  have h1 : p ≤ n/16 := Nat.pow_log_le_self 2 (by omega)
  have h2 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n/16)
  rw [pow_succ] at h2
  change n/16 < p * 2 at h2
  have clip (i s x : ℕ) (hs : (2 : ℕ)^i = s) (hx : 2*s ≤ x) (hx' : x ≤ 4*s) :
      a x = s + min (x-2*s) s := by
    have hi : (2 : ℕ)^(i+1) = 2*s := by rw [pow_succ, hs, mul_comm]
    have hh := block i (x-2*s)
    rw [hi, hs, show 2*s+(x-2*s) = x by omega] at hh
    exact hh (by omega)
  apply fixed_on_block (p := p) (by omega) (by omega)
  · intro x hx hx'
    have hh := clip (j+2) (4*p) x (by dsimp [p]; rw [pow_add]; ring) (by omega) (by omega)
    convert hh using 1
    omega
  · intro x hx hx'
    have hh := clip (j+3) (8*p) x (by dsimp [p]; rw [pow_add]; ring) (by omega) (by omega)
    convert hh using 1
    omega

theorem fixed_identities
    (block : ∀ j d : ℕ, d ≤ 2^(j+1) →
      a (2^(j+1)+d) = 2^j + min d (2^j)) :
    (∀ n ≥ 2, a n + a (n - a (n - a (n - a (n - a n)))) = n) ∧
    (∀ n ≥ 2, a (n - a (n - a (n - a n))) = a (n - a (n - a (n - a (n - a (n - a n)))))) ∧
    (∀ n ≥ 2, a^[2] n = a (n - a (n - a (n - a n)))) ∧
    (∀ n ≥ 2, n - a n = a (n - a^[2] n)) ∧
    (∀ n ≥ 2, a (n - a n) = a^[2] (n - a^[2] (n - a^[2] (n - a^[2] n)))) :=
  ⟨fun n hn => (fixed_at block n hn).1, fun n hn => (fixed_at block n hn).2.1,
   fun n hn => (fixed_at block n hn).2.2.1, fun n hn => (fixed_at block n hn).2.2.2.1,
   fun n hn => (fixed_at block n hn).2.2.2.2⟩

end A006165

namespace A006165

open OMA.S_oeis_a006165

private theorem reflection_block (k j d y : ℕ) (hk : 2≤k)
    (hd : d≤2^(k+j)) (hy : y ≤ min d (2^j)) :
    a^[k] (2^(k+j)+d-(2^j+y)) = 2^j + min (d-(2^j+y)) (2^j) := by
  by_cases h : 2^j+y≤d
  · rw [show 2^(k+j)+d-(2^j+y)=2^(k+j)+(d-(2^j+y)) by omega]
    exact iter_block k j _ (by omega) (by omega)
  · rw [show d-(2^j+y) = 0 by omega, Nat.zero_min, Nat.add_zero]
    have hfour : 4 ≤ 2^k := calc
      4 = 2^2 := by decide
      _ ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
    cases j with
    | zero =>
      simp only [pow_zero, Nat.add_zero] at *
      exact iter_small k _ (by omega) (by omega)
    | succ j =>
      let q := 2^j
      let b := 2^(k+j)
      have hj : 2^(j+1) = 2*q := by simp [q, pow_succ, Nat.mul_comm]
      have hb : 2^(k+(j+1)) = 2*b := by
        rw [show k+(j+1)=k+j+1 by omega, pow_succ, Nat.mul_comm]
      have hbq : 4*q ≤ b := by
        change 4*q ≤ 2^(k+j)
        rw [pow_add]
        exact Nat.mul_le_mul_right _ hfour
      rw [hj] at h hy ⊢
      rw [hb] at hd ⊢
      let t := 2*b+d-(2*q+y)-b
      have ht : t≤2^(k+j) := by change t≤b; dsimp [t]; omega
      have hqt : q≤t := by dsimp [t]; omega
      rw [show 2*b+d-(2*q+y)=2^(k+j)+t by change _=b+t; dsimp [t]; omega]
      rw [iter_block k j t (by omega) ht]
      change q+min t q = 2*q
      omega

/-- On the relevant interval the map z ↦ Aₖ(n−z) is a clipped reflection, whose
third iterate agrees with its first. This proves Bala's sixth identity. -/
theorem sixth (k : ℕ) (hk : 2≤k) (n : ℕ) (hn : 2≤n) :
    a^[k] (n - a^[k] n) = a^[k] (n - a^[k] (n - a^[k] (n - a^[k] n))) := by
  by_cases hs : n≤2^k
  · have h₀ := iter_small k n (by omega) hs
    have h₁ := iter_small k (n-1) (by omega) (by omega)
    simp only [h₀, h₁]
  · let j := n.log2-k
    have hklog := (Nat.le_log2 (show n≠0 by omega)).2 (show 2^k≤n by omega)
    have hj : k+j = n.log2 := by dsimp [j]; omega
    let b := 2^(k+j)
    let p := 2^j
    let d := n-b
    have hn₁ : b≤n := by dsimp [b]; rw [hj]; exact Nat.log2_self_le (by omega)
    have hn₂ : n<2*b := by
      have ht := Nat.lt_log2_self (n:=n)
      rw [pow_succ] at ht
      dsimp [b]
      rw [hj]
      omega
    have hd : d≤2^(k+j) := by change d≤b; dsimp [d]; omega
    have hdecomp : b+d=n := by dsimp [d]; omega
    let x := min d p
    let T := fun y : ℕ => min (d-(p+y)) p
    have ha : a^[k] n=p+x := by
      have hi := iter_block k j d (by omega) hd
      change a^[k] (b+d) = p+x at hi
      rwa [hdecomp] at hi
    have hm (y : ℕ) (hy : y≤x) : a^[k] (n-(p+y)) = p+T y := by
      have hi := reflection_block k j d y hk hd hy
      change a^[k] (b+d-(p+y)) = p+T y at hi
      rwa [hdecomp] at hi
    have hy (y : ℕ) : T y≤x := by dsimp [T,x]; omega
    simp only [ha, hm x le_rfl, hm (T x) (hy x), hm (T (T x)) (hy (T x))]
    dsimp [T]
    omega

end A006165

namespace A006165

open OMA.S_oeis_a006165

theorem first_difference (k : ℕ) (hk : 1≤k) (n : ℕ) (hn : 1≤n) :
    n+1-a^[k] (n+1) = n-a^[k] n ∨ n+1-a^[k] (n+1) = n-a^[k] n+1 := by
  by_cases hs : n<2^k
  · rw [iter_small k n hn (by omega), iter_small k (n+1) (by omega) (by omega)]
    omega
  · let j := n.log2-k
    have hklog := (Nat.le_log2 (show n≠0 by omega)).2 (show 2^k≤n by omega)
    have hj : k+j=n.log2 := by dsimp [j]; omega
    let b := 2^(k+j)
    let d := n-b
    have h₁ : b≤n := by dsimp [b]; rw [hj]; exact Nat.log2_self_le (by omega)
    have h₂ : n<2*b := by
      have hh := Nat.lt_log2_self (n:=n)
      rw [pow_succ] at hh
      dsimp [b]
      rw [hj]
      omega
    have hd : d+1≤b := by dsimp [d]; omega
    have old := iter_block k j d hk (show d≤b by omega)
    have new := iter_block k j (d+1) hk hd
    change a^[k] (b+d) = _ at old
    change a^[k] (b+(d+1)) = _ at new
    rw [show b+d=n by dsimp [d]; omega] at old
    rw [show b+(d+1)=n+1 by dsimp [d]; omega] at new
    rw [old,new]
    omega

end A006165

namespace A006165

open OMA.S_oeis_a006165

/-- On each dyadic block, the repeated value occupies the initial plateau. -/
theorem repeated_fibres (k : ℕ) (hk : 1 ≤ k)
    (small : ∀ n, 1 ≤ n → n ≤ 2^k → a^[k] n = 1)
    (block : ∀ j d, d ≤ 2^(k+j) → a^[k] (2^(k+j)+d) = 2^j + min d (2^j))
    (difference : ∀ n ≥ 1, n+1-a^[k] (n+1) = n-a^[k] n ∨
      n+1-a^[k] (n+1) = n-a^[k] n+1) :
    (∀ n₁ n₂ : ℕ, 1 ≤ n₁ → 1 ≤ n₂ → n₁ ≠ n₂ → n₁ - a^[k] n₁ = n₂ - a^[k] n₂ →
      ∃ m : ℕ, n₁ - a^[k] n₁ = (2 ^ k - 1) * 2 ^ m) ∧
    (∀ m : ℕ, {n : ℕ | 1 ≤ n ∧ n - a^[k] n = (2 ^ k - 1) * 2 ^ m}.ncard = 2 ^ m + 1) := by
  let B (n : ℕ) := n - a^[k] n
  let p (j : ℕ) : ℕ := 2^j
  let q (j : ℕ) : ℕ := 2^(k+j)
  let v (j : ℕ) : ℕ := (2^k - 1) * p j
  have ppos (j : ℕ) : 0 < p j := by dsimp [p]; positivity
  have size (j : ℕ) : 2*p j ≤ q j := by
    have h : 2 ≤ (2:ℕ)^k := by
      simpa using (pow_le_pow_right₀ (show (1:ℕ) ≤ 2 by decide) hk)
    simpa [p, q, pow_add] using Nat.mul_le_mul_right (p j) h
  have pstep (j : ℕ) : p (j+1) = 2*p j := by simp [p, pow_succ, Nat.mul_comm]
  have qstep (j : ℕ) : q (j+1) = 2*q j := by simp [q, ← Nat.add_assoc, pow_succ, Nat.mul_comm]
  have qzero : q 0 = 2^k := by simp [q]
  have vrel (j : ℕ) : v j + p j = q j := by
    rw [show v j = q j - p j by simp [v, q, p, pow_add, Nat.sub_mul]]
    have hz := size j
    omega
  have plateau (j d : ℕ) (hd : d ≤ q j) : B (q j + d) = v j + (d - p j) := by
    have hv := vrel j
    have hb := block j d hd
    change a^[k] (q j+d) = p j + min d (p j) at hb
    change q j+d-a^[k] (q j+d) = v j + (d-p j)
    rw [hb]
    omega
  have low (n : ℕ) (hn : 1 ≤ n) (hlt : n ≤ q 0) : B n = n-1 := by
    change n - a^[k] n = n - 1
    rw [small n hn (qzero ▸ hlt)]
  have mono : Monotone B := by
    apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero => simp [B]
    | succ n =>
      rcases difference (n+1) (by omega) with h | h
      · exact Nat.le_of_eq h.symm
      · change B (n+1+1) = B (n+1)+1 at h
        omega
  have covers (n : ℕ) (hn : q 0 ≤ n) : ∃ j d, n = q j+d ∧ d < q j := by
    have exists_upper : ∃ t, n < q t := by
      refine ⟨n, ?_⟩
      have below_pow (t : ℕ) : t < (2:ℕ)^t := by
        induction t with
        | zero => decide
        | succ t ih =>
          rw [pow_succ]
          have hp : 0 < (2:ℕ)^t := by positivity
          omega
      have h := below_pow n
      have hh : (2:ℕ)^n ≤ q n := by
        exact pow_le_pow_right₀ (by decide) (by change n ≤ k+n; omega)
      omega
    have first_pos : Nat.find exists_upper ≠ 0 := by
      intro he
      have hh := Nat.find_spec exists_upper
      rw [he] at hh
      omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero first_pos
    have up := Nat.find_spec exists_upper
    rw [hj, Nat.succ_eq_add_one, qstep] at up
    have lower : q j ≤ n := by
      have hjl : j < Nat.find exists_upper := by omega
      exact Nat.le_of_not_gt (Nat.find_min exists_upper hjl)
    exact ⟨j, n-q j, by omega, by omega⟩
  have repetition (l r : ℕ) (hl : 1 ≤ l) (hlr : l < r) (he : B l = B r) :
      ∃ j, B l = v j := by
    have hmono₁ := mono (show l ≤ l+1 by omega)
    have hmono₂ := mono (show l+1 ≤ r by omega)
    have hstep : B l = B (l+1) := by omega
    have large : q 0 ≤ l := by
      by_contra! hs
      rw [low l hl (by omega), low (l+1) (by omega) (by omega)] at hstep
      omega
    obtain ⟨j,d,hex,hd⟩ := covers l large
    rw [hex, Nat.add_assoc, plateau j d (by omega), plateau j (d+1) (by omega)] at hstep
    refine ⟨j, ?_⟩
    rw [hex, plateau j d (by omega)]
    omega
  constructor
  · intro n₁ n₂ h₁ h₂ hne he
    change B n₁ = B n₂ at he
    rcases lt_or_gt_of_ne hne with h | h
    · exact repetition n₁ n₂ h₁ h he
    · obtain ⟨j,hj⟩ := repetition n₂ n₁ h₂ h he.symm
      exact ⟨j, he.trans hj⟩
  · intro j
    change {n : ℕ | 1 ≤ n ∧ B n = v j}.ncard = p j + 1
    have lower : B (q j-1) < v j := by
      cases j with
      | zero =>
        have hh := size 0
        have hp := ppos 0
        rw [low (q 0-1) (by omega) (by omega)]
        have hv := vrel 0
        have he : p 0 = 1 := by simp [p]
        omega
      | succ j =>
        rw [qstep, show 2*q j-1 = q j+(q j-1) by
          have hp := ppos j
          have hq := size j
          omega, plateau j (q j-1) (by omega)]
        have hv := vrel j
        have hv' := vrel (j+1)
        rw [qstep, pstep] at hv'
        have hp := ppos j
        have hq := size j
        omega
    have upper : v j < B (q j+p j+1) := by
      have hp := ppos j
      have hq := size j
      rw [Nat.add_assoc, plateau j (p j+1) (by omega)]
      omega
    have exact_fibre : {n : ℕ | 1 ≤ n ∧ B n = v j} = Set.Icc (q j) (q j+p j) := by
      ext n
      change (1 ≤ n ∧ B n = v j) ↔ q j ≤ n ∧ n ≤ q j+p j
      constructor
      · rintro ⟨_, he⟩
        constructor
        · by_contra! hl
          have hm := mono (show n ≤ q j-1 by omega)
          omega
        · by_contra! hu
          have hm := mono (show q j+p j+1 ≤ n by omega)
          omega
      · rintro ⟨hl,hu⟩
        have hq := size j
        have hp := ppos j
        have hn : n = q j+(n-q j) := by omega
        refine ⟨by omega, ?_⟩
        rw [hn, plateau j (n-q j) (by omega)]
        omega
    rw [exact_fibre, Set.ncard_Icc_nat]
    omega

end A006165

theorem OMA.solution : type_of% @OMA.S_oeis_a006165.main := by
  obtain ⟨first, second, third, fourth, fifth⟩ := A006165.fixed_identities A006165.a_block
  refine ⟨first, second, third, fourth, fifth, A006165.sixth, fun k hk =>
    ⟨A006165.first_difference k hk, ?_⟩⟩
  exact A006165.repeated_fibres k hk (A006165.iter_small k) (fun j d hd =>
    A006165.iter_block k j d hk hd) (A006165.first_difference k hk)
