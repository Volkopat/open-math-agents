import OMAReductions.R_Green14_W_3_14_R1_H3_R1_H3_R1

/-!
# Certificate for `Green14.W_3_14.R1.H3.R1.H3.R1.H1`

We prove that every 2-coloring `c : Nat → Bool` with `c 86 = true`, `c 96 = true`, and
`c q = false` for `86 < q < 96` contains either a red 3-term arithmetic progression or a
blue 14-term arithmetic progression inside `{0, ..., 181}`.

Shifting `[1, 181]` to `[0, 180]` (`N = 181`) places the fixed red positions at `85` and `95`
with blue positions `86..94`, giving exact reflection symmetry `x ↦ 180 - x`. The refutation
combines 3-way symmetric branching at symmetric nodes with 384-bit-lane bit-parallel unit
propagation over compact prefix-coded decision subtrees verified by `decide +kernel`.
-/

namespace OMA.W314H3R1H1

private def N : Nat := 181
private def W : Nat := 384

private def Goal (c : Nat → Bool) : Prop :=
  ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13) * d < N ∧
    ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a + t.val * d) = b

private def Bit (m i : Nat) : Prop := m.testBit i = true
private def At (j m x : Nat) : Prop := Bit m (W * j + x)

@[simp] private lemma bit_or {a b i} : Bit (a ||| b) i ↔ Bit a i ∨ Bit b i := by
  simp [Bit]

@[simp] private lemma bit_and {a b i} : Bit (a &&& b) i ↔ Bit a i ∧ Bit b i := by
  simp [Bit]

@[simp] private lemma bit_shr {a k i} : Bit (a >>> k) i ↔ Bit a (i + k) := by
  simp [Bit, Nat.add_comm]

private lemma bit_shl {a k i} : Bit (a <<< k) i ↔ k ≤ i ∧ Bit a (i - k) := by
  simp [Bit]

private def low (n : Nat) : Nat := (1 <<< n) - 1

@[simp] private lemma bit_low {n i} : Bit (low n) i ↔ i < n := by
  simp [Bit, low, Nat.shiftLeft_eq]

private lemma low_lt {n : Nat} : low n < 2 ^ n := by
  simp [low, Nat.shiftLeft_eq]

private def repMask (pat : Nat) (k : Nat) : Nat :=
  if k = 0 then 0
  else
    let half := k / 2
    let sub := repMask pat half
    let dbl := sub ||| (sub <<< (W * half))
    if k % 2 = 0 then dbl else dbl ||| (pat <<< (W * (k - 1)))
termination_by k
decreasing_by omega

private lemma repMask_bound {pat : Nat} (hpat : pat < 2 ^ W) :
    ∀ k, repMask pat k < 2 ^ (W * k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    unfold repMask
    split
    · rename_i hk; subst hk; simp
    · rename_i hk
      have hhalf : k / 2 < k := Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
      have hsub : repMask pat (k / 2) < 2 ^ (W * (k / 2)) := ih (k / 2) hhalf
      have hdbl : (repMask pat (k / 2) ||| (repMask pat (k / 2) <<< (W * (k / 2)))) <
          2 ^ (W * (2 * (k / 2))) := by
        apply Nat.or_lt_two_pow
        · exact lt_of_lt_of_le hsub (Nat.pow_le_pow_right (by decide) (by simp only [W]; omega))
        · rw [Nat.shiftLeft_eq, show W * (2 * (k / 2)) = W * (k / 2) + W * (k / 2) by simp only [W]; omega, Nat.pow_add]
          exact Nat.mul_lt_mul_of_pos_right hsub (Nat.two_pow_pos _)
      split
      · rename_i hev
        have hkeq : 2 * (k / 2) = k := by omega
        simpa [hkeq] using hdbl
      · rename_i hodd
        apply Nat.or_lt_two_pow
        · exact lt_of_lt_of_le hdbl (Nat.pow_le_pow_right (by decide) (by simp only [W]; omega))
        · rw [Nat.shiftLeft_eq, show W * k = W + W * (k - 1) by simp only [W]; omega, Nat.pow_add]
          exact Nat.mul_lt_mul_of_pos_right hpat (Nat.two_pow_pos _)

private lemma repMask_at {pat : Nat} (hpat : pat < 2 ^ W) :
    ∀ k j x, j < k → x < W → (At j (repMask pat k) x ↔ Bit pat x) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro j x hj hx
    unfold repMask
    split
    · rename_i hk; omega
    · rename_i hk
      have hhalf : k / 2 < k := Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
      have hsubB : repMask pat (k / 2) < 2 ^ (W * (k / 2)) := repMask_bound hpat (k / 2)
      have hdbl_at : ∀ j', j' < 2 * (k / 2) →
          (At j' (repMask pat (k / 2) ||| (repMask pat (k / 2) <<< (W * (k / 2)))) x ↔ Bit pat x) := by
        intro j' hj'
        dsimp only [At]
        rw [bit_or, bit_shl]
        by_cases hlt : j' < k / 2
        · have h1 : ¬ (W * (k / 2) ≤ W * j' + x) := by simp only [W] at *; omega
          simp only [h1, false_and, or_false]
          exact ih (k / 2) hhalf j' x hlt hx
        · have hge : W * (k / 2) ≤ W * j' + x := by simp only [W] at *; omega
          have hzero : ¬ Bit (repMask pat (k / 2)) (W * j' + x) := by
            have hb := lt_of_lt_of_le hsubB (Nat.pow_le_pow_right (by decide : 0 < 2) hge)
            simp [Bit, Nat.testBit_lt_two_pow hb]
          have heq : W * j' + x - W * (k / 2) = W * (j' - k / 2) + x := by simp only [W] at *; omega
          simp only [hzero, false_or, hge, true_and, heq]
          exact ih (k / 2) hhalf (j' - k / 2) x (by omega) hx
      split
      · rename_i hev
        exact hdbl_at j (by omega)
      · rename_i hodd
        by_cases hlast : j < k - 1
        · dsimp only [At]
          rw [bit_or, bit_shl]
          have h1 : ¬ (W * (k - 1) ≤ W * j + x) := by simp only [W] at *; omega
          simp only [h1, false_and, or_false]
          exact hdbl_at j (by omega)
        · have hjEq : j = k - 1 := by omega
          subst hjEq
          dsimp only [At]
          rw [bit_or, bit_shl]
          have hge : W * (k - 1) ≤ W * (k - 1) + x := Nat.le_add_right _ _
          have hdblB : (repMask pat (k / 2) ||| (repMask pat (k / 2) <<< (W * (k / 2)))) <
              2 ^ (W * (2 * (k / 2))) := by
            apply Nat.or_lt_two_pow
            · exact lt_of_lt_of_le hsubB (Nat.pow_le_pow_right (by decide) (by simp only [W]; omega))
            · rw [Nat.shiftLeft_eq, show W * (2 * (k / 2)) = W * (k / 2) + W * (k / 2) by simp only [W]; omega, Nat.pow_add]
              exact Nat.mul_lt_mul_of_pos_right hsubB (Nat.two_pow_pos _)
          have hzero : ¬ Bit (repMask pat (k / 2) ||| (repMask pat (k / 2) <<< (W * (k / 2))))
              (W * (k - 1) + x) := by
            have hle : W * (2 * (k / 2)) ≤ W * (k - 1) + x := by simp only [W] at *; omega
            have hb := lt_of_lt_of_le hdblB (Nat.pow_le_pow_right (by decide : 0 < 2) hle)
            simp [Bit, Nat.testBit_lt_two_pow hb]
          simp [hzero, hge]

private def Clean (k m : Nat) : Prop :=
  ∀ j x, j < k → N ≤ x → x < W → ¬ At j m x

private def Fact (c : Nat → Bool) (b : Bool) (j m : Nat) : Prop :=
  ∀ x, x < N → At j m x → c x = b

private lemma clean_and_left {k a b} (ha : Clean k a) : Clean k (a &&& b) :=
  fun j x hj h1 h2 h => ha j x hj h1 h2 (bit_and.mp h).1

private lemma clean_and_right {k a b} (hb : Clean k b) : Clean k (a &&& b) :=
  fun j x hj h1 h2 h => hb j x hj h1 h2 (bit_and.mp h).2

private lemma clean_or {k a b} (ha : Clean k a) (hb : Clean k b) : Clean k (a ||| b) :=
  fun j x hj h1 h2 h => (bit_or.mp h).elim (ha j x hj h1 h2) (hb j x hj h1 h2)

private lemma clean_repMask_low {n k : Nat} (hn : n ≤ N) : Clean k (repMask (low n) k) := by
  intro j x hj hx1 hx2 h
  have hpat : low n < 2 ^ W := lt_of_lt_of_le low_lt (Nat.pow_le_pow_right (by decide) (by simp only [N, W] at *; omega))
  have hbit := (repMask_at hpat k j x hj hx2).mp h
  rw [bit_low] at hbit
  omega

private lemma fact_or {c b j a d} (fa : Fact c b j a) (fd : Fact c b j d) : Fact c b j (a ||| d) :=
  fun x hx h => (bit_or.mp h).elim (fa x hx) (fd x hx)

private lemma fact_and_left {c b j a d} (fa : Fact c b j a) : Fact c b j (a &&& d) :=
  fun x hx h => fa x hx (bit_and.mp h).1

private lemma shR_at {k m j x s : Nat} (hj : j < k) (hx : x < N) (hs : s ≤ 180) (hm : Clean k m) :
    At j (m >>> s) x → x + s < N ∧ At j m (x + s) := by
  intro h
  have h1 : Bit m (W * j + (x + s)) := by
    have : W * j + x + s = W * j + (x + s) := by omega
    simpa [At, bit_shr, this] using h
  by_cases hlt : x + s < N
  · exact ⟨hlt, h1⟩
  · exfalso
    exact hm j (x + s) hj (by omega) (by simp only [N, W] at *; omega) h1

private lemma shL_at {k m j x s : Nat} (hj : j < k) (hx : x < N) (hs : s ≤ 180) (hm : Clean k m) :
    At j (m <<< s) x → s ≤ x ∧ At j m (x - s) := by
  intro h
  obtain ⟨hle, h1⟩ := bit_shl.mp h
  by_cases hle' : s ≤ x
  · refine ⟨hle', ?_⟩
    have : W * j + x - s = W * j + (x - s) := by omega
    simpa [At, this] using h1
  · exfalso
    cases j with
    | zero => simp at hle; omega
    | succ j' =>
      have heq : W * (j' + 1) + x - s = W * j' + (W + x - s) := by simp only [W]; omega
      rw [heq] at h1
      exact hm j' (W + x - s) (by omega) (by simp only [N, W] at *; omega) (by simp only [W] at *; omega) h1

-- Red 3-AP propagation: R -> B
private def redStepD (r d : Nat) : Nat :=
  let rHi := r >>> d
  let rLo := r <<< d
  let pair := r &&& rHi
  (pair <<< (2 * d)) ||| (pair >>> d) ||| (rLo &&& rHi)

private lemma redStepD_sound {c : Nat → Bool} (hno : ¬ Goal c) {k j r d : Nat}
    (hj : j < k) (hd1 : 0 < d) (hd2 : d ≤ 90) (hm : Clean k r) (fr : Fact c true j r) :
    Fact c false j (redStepD r d) := by
  intro x hx h
  have hpair_clean : Clean k (r &&& (r >>> d)) := clean_and_left hm
  have hnot3 : ∀ a, a + 2 * d < N → c a = true → c (a + d) = true → c (a + 2 * d) = true → False := by
    intro a ha h0 h1 h2
    apply hno
    refine ⟨true, a, d, hd1, ha, ?_⟩
    intro t ht
    have ht' : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 := by simp at ht; omega
    rcases ht' with h0' | h1' | h2'
    · simpa [h0'] using h0
    · simpa [h1'] using h1
    · simpa [h2'] using h2
  apply Bool.eq_false_iff.mpr
  intro hcx
  dsimp only [redStepD, At] at h
  rcases bit_or.mp h with h12 | h3
  · rcases bit_or.mp h12 with h1 | h2
    · obtain ⟨hge, hp⟩ := shL_at hj hx (by omega) hpair_clean h1
      obtain ⟨ha0, hhi⟩ := bit_and.mp hp
      obtain ⟨hbd, ha1⟩ := shR_at hj (by omega) (by omega) hm hhi
      have c0 := fr (x - 2 * d) (by omega) ha0
      have c1 := fr (x - 2 * d + d) hbd ha1
      exact hnot3 (x - 2 * d) (by omega) c0 c1 (by simpa [show x - 2 * d + 2 * d = x by omega] using hcx)
    · obtain ⟨hbd1, hp⟩ := shR_at hj hx (by omega) hpair_clean h2
      obtain ⟨ha1, hhi⟩ := bit_and.mp hp
      obtain ⟨hbd2, ha2⟩ := shR_at hj hbd1 (by omega) hm hhi
      have c1 := fr (x + d) hbd1 ha1
      have c2 := fr (x + d + d) hbd2 ha2
      exact hnot3 x (by omega) hcx c1 (by simpa [show x + 2 * d = x + d + d by omega] using c2)
  · obtain ⟨hlo, hhi⟩ := bit_and.mp h3
    obtain ⟨hge, ha0⟩ := shL_at hj hx (by omega) hm hlo
    obtain ⟨hbd, ha2⟩ := shR_at hj hx (by omega) hm hhi
    have c0 := fr (x - d) (by omega) ha0
    have c2 := fr (x + d) hbd ha2
    exact hnot3 (x - d) (by omega) c0 (by simpa [show x - d + d = x by omega] using hcx)
      (by simpa [show x - d + 2 * d = x + d by omega] using c2)

private def redLoop (r : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | d + 1, acc => redLoop r d (acc ||| redStepD r (d + 1))

private lemma redLoop_sound {c : Nat → Bool} (hno : ¬ Goal c) {k j r : Nat}
    (hj : j < k) (hm : Clean k r) (fr : Fact c true j r) :
    ∀ n acc, n ≤ 90 → Fact c false j acc → Fact c false j (redLoop r n acc) := by
  intro n
  induction n with
  | zero => intro acc _ hacc; exact hacc
  | succ n ih =>
    intro acc hn hacc
    exact ih _ (by omega) (fact_or hacc (redStepD_sound hno hj (by omega) hn hm fr))

private def redPropagate (M r b : Nat) : Nat :=
  b ||| (redLoop r 90 0 &&& M)

-- Blue 14-AP propagation: B -> R
private def Run (c : Nat → Bool) (j d len m : Nat) : Prop :=
  ∀ a, a < N → At j m a →
    a + (len - 1) * d < N ∧ ∀ t, t < len → c (a + t * d) = false

private def Need (c : Nat → Bool) (j d len m : Nat) : Prop :=
  ∀ a, a < N → At j m a →
    a + (len - 1) * d < N ∧ ∃ t, t < len ∧ c (a + t * d) = true

private lemma run_one {c : Nat → Bool} {j d b : Nat} (fb : Fact c false j b) : Run c j d 1 b := by
  intro a ha h
  refine ⟨by simpa using ha, ?_⟩
  intro t ht
  have : t = 0 := by omega
  simpa [this] using fb a ha h

private lemma run_join {c : Nat → Bool} {k j d p q mp mq : Nat}
    (hj : j < k) (hp : 0 < p) (hq : 0 < q) (hpd : p * d ≤ 180) (hmq : Clean k mq)
    (rp : Run c j d p mp) (rq : Run c j d q mq) :
    Run c j d (p + q) (mp &&& (mq >>> (p * d))) := by
  intro a ha h
  obtain ⟨h1, h2⟩ := bit_and.mp h
  obtain ⟨hbd, h3⟩ := shR_at hj ha hpd hmq h2
  obtain ⟨_, fp⟩ := rp a ha h1
  obtain ⟨hbd2, fq⟩ := rq (a + p * d) hbd h3
  have hsum : (p + q - 1) * d = p * d + (q - 1) * d := by
    rw [← Nat.add_mul]; congr 1; omega
  refine ⟨by rw [hsum]; omega, ?_⟩
  intro t ht
  by_cases htp : t < p
  · exact fp t htp
  · have hq' := fq (t - p) (by omega)
    have heq : a + p * d + (t - p) * d = a + t * d := by
      have : p * d + (t - p) * d = t * d := by rw [← Nat.add_mul]; congr 1; omega
      omega
    rwa [heq] at hq'

private lemma need_init {c : Nat → Bool} (hno : ¬ Goal c) {k j d : Nat}
    (hj : j < k) (hd1 : 0 < d) (hd2 : d ≤ 13) :
    Need c j d 14 (repMask (low (N - 13 * d)) k) := by
  intro a ha h
  have hpat : low (N - 13 * d) < 2 ^ W :=
    lt_of_lt_of_le low_lt (Nat.pow_le_pow_right (by decide) (by simp only [N, W]; omega))
  have hbit := (repMask_at hpat k j a hj (by simp only [N, W] at *; omega)).mp h
  rw [bit_low] at hbit
  have hbd : a + 13 * d < N := by simp only [N] at *; omega
  refine ⟨hbd, ?_⟩
  by_contra hnone
  apply hno
  refine ⟨false, a, d, hd1, hbd, ?_⟩
  intro t _
  apply Bool.eq_false_iff.mpr
  intro hct
  exact hnone ⟨t.val, t.isLt, hct⟩

private lemma need_or {c : Nat → Bool} {j d len m1 m2 : Nat}
    (h1 : Need c j d len m1) (h2 : Need c j d len m2) : Need c j d len (m1 ||| m2) :=
  fun a ha h => (bit_or.mp h).elim (h1 a ha) (h2 a ha)

private lemma need_and_left {c : Nat → Bool} {j d len m1 m2 : Nat}
    (h1 : Need c j d len m1) : Need c j d len (m1 &&& m2) :=
  fun a ha h => h1 a ha (bit_and.mp h).1

private lemma need_left {c : Nat → Bool} {k j d p q st rq : Nat}
    (hj : j < k) (hpd : p * d ≤ 180) (hmr : Clean k rq)
    (hs : Need c j d (p + q) st) (hr : Run c j d q rq) :
    Need c j d p (st &&& (rq >>> (p * d))) := by
  intro a ha h
  obtain ⟨hst, hsh⟩ := bit_and.mp h
  obtain ⟨hbd, hrq⟩ := shR_at hj ha hpd hmr hsh
  obtain ⟨_, t, ht, hct⟩ := hs a ha hst
  obtain ⟨_, hfr⟩ := hr (a + p * d) hbd hrq
  have hbdp : a + (p - 1) * d < N := by
    have : (p - 1) * d ≤ p * d := Nat.mul_le_mul_right d (Nat.sub_le p 1)
    omega
  refine ⟨hbdp, ?_⟩
  by_cases htp : t < p
  · exact ⟨t, htp, hct⟩
  · exfalso
    have hf := hfr (t - p) (by omega)
    have heq : a + p * d + (t - p) * d = a + t * d := by
      have : p * d + (t - p) * d = t * d := by rw [← Nat.add_mul]; congr 1; omega
      omega
    rw [heq, hct] at hf
    exact Bool.noConfusion hf

private lemma need_right {c : Nat → Bool} {k j d p q st rp : Nat}
    (hj : j < k) (hq : 0 < q) (hpd : p * d ≤ 180) (hmst : Clean k st)
    (hs : Need c j d (p + q) st) (hr : Run c j d p rp) :
    Need c j d q ((st &&& rp) <<< (p * d)) := by
  intro a ha h
  obtain ⟨hge, hsb⟩ := shL_at hj ha hpd (clean_and_left hmst) h
  obtain ⟨hst, hrp⟩ := bit_and.mp hsb
  obtain ⟨hbd, t, ht, hct⟩ := hs (a - p * d) (by omega) hst
  obtain ⟨_, hfr⟩ := hr (a - p * d) (by omega) hrp
  have hsum : (p + q - 1) * d = p * d + (q - 1) * d := by
    rw [← Nat.add_mul]; congr 1; omega
  refine ⟨by rw [hsum] at hbd; omega, ?_⟩
  by_cases htp : t < p
  · exfalso
    have hf := hfr t htp
    rw [hct] at hf
    exact Bool.noConfusion hf
  · refine ⟨t - p, by omega, ?_⟩
    have heq : a + (t - p) * d = a - p * d + t * d := by
      rw [Nat.sub_mul]
      have : p * d ≤ t * d := Nat.mul_le_mul_right d (by omega)
      omega
    rwa [heq]

private lemma need_one_fact {c : Nat → Bool} {j d m : Nat} (h : Need c j d 1 m) : Fact c true j m := by
  intro x hx hm
  obtain ⟨_, t, ht, hct⟩ := h x hx hm
  have : t = 0 := by omega
  simpa [this] using hct

private def blueStepD (M k b d : Nat) : Nat :=
  let r1 := b
  let r2 := r1 &&& (r1 >>> d)
  let r3 := r2 &&& (r1 >>> (2 * d))
  let r4 := r2 &&& (r2 >>> (2 * d))
  let r7 := r4 &&& (r3 >>> (4 * d))
  let st14 := repMask (low (N - 13 * d)) k
  let s7 := ((st14 &&& (r7 >>> (7 * d))) ||| ((st14 &&& r7) <<< (7 * d))) &&& M
  if s7 == 0 then 0
  else
    let s4 := s7 &&& (r3 >>> (4 * d))
    let s3 := ((s7 &&& r4) <<< (4 * d)) &&& M
    let s2 := ((s4 &&& (r2 >>> (2 * d))) ||| ((s4 &&& r2) <<< (2 * d)) ||| (s3 &&& (r1 >>> (2 * d)))) &&& M
    let s1 := (((s3 &&& r2) <<< (2 * d)) ||| (s2 &&& (r1 >>> d)) ||| ((s2 &&& r1) <<< d)) &&& M
    s1

private lemma blueStepD_clean {k b d : Nat} :
    Clean k (blueStepD (repMask (low N) k) k b d) := by
  unfold blueStepD
  dsimp only
  split
  · intro j x _ _ _ h; simp [At, Bit] at h
  · exact clean_and_right (clean_repMask_low (Nat.le_refl N))

private lemma blueStepD_sound {c : Nat → Bool} (hno : ¬ Goal c) {k j b d : Nat}
    (hj : j < k) (hd1 : 0 < d) (hd2 : d ≤ 13) (hmb : Clean k b) (fb : Fact c false j b) :
    Fact c true j (blueStepD (repMask (low N) k) k b d) := by
  unfold blueStepD
  dsimp only
  set M := repMask (low N) k
  set r2 := b &&& (b >>> d)
  set r3 := r2 &&& (b >>> (2 * d))
  set r4 := r2 &&& (r2 >>> (2 * d))
  set r7 := r4 &&& (r3 >>> (4 * d))
  set st14 := repMask (low (N - 13 * d)) k
  set s7 := ((st14 &&& (r7 >>> (7 * d))) ||| ((st14 &&& r7) <<< (7 * d))) &&& M
  have hM : Clean k M := clean_repMask_low (Nat.le_refl N)
  have hr1 : Run c j d 1 b := run_one fb
  have hcr2 : Clean k r2 := clean_and_left hmb
  have hr2 : Run c j d 2 r2 := by
    simpa [Nat.one_mul] using run_join (p := 1) (q := 1) hj (by decide) (by decide) (by omega) hmb hr1 hr1
  have hcr3 : Clean k r3 := clean_and_left hcr2
  have hr3 : Run c j d 3 r3 :=
    run_join (p := 2) (q := 1) hj (by decide) (by decide) (by omega) hmb hr2 hr1
  have hcr4 : Clean k r4 := clean_and_left hcr2
  have hr4 : Run c j d 4 r4 :=
    run_join (p := 2) (q := 2) hj (by decide) (by decide) (by omega) hcr2 hr2 hr2
  have hcr7 : Clean k r7 := clean_and_left hcr4
  have hr7 : Run c j d 7 r7 :=
    run_join (p := 4) (q := 3) hj (by decide) (by decide) (by omega) hcr3 hr4 hr3
  have hst14c : Clean k st14 := clean_repMask_low (Nat.sub_le N _)
  have hst14 : Need c j d 14 st14 := need_init hno hj hd1 hd2
  have hs7c : Clean k s7 := clean_and_right hM
  have hs7 : Need c j d 7 s7 :=
    need_and_left (need_or
      (need_left (p := 7) (q := 7) hj (by omega) hcr7 hst14 hr7)
      (need_right (p := 7) (q := 7) hj (by decide) (by omega) hst14c hst14 hr7))
  split
  · intro x _ h; simp [At, Bit] at h
  · set s4 := s7 &&& (r3 >>> (4 * d))
    set s3 := ((s7 &&& r4) <<< (4 * d)) &&& M
    set s2 := ((s4 &&& (r2 >>> (2 * d))) ||| ((s4 &&& r2) <<< (2 * d)) ||| (s3 &&& (b >>> (2 * d)))) &&& M
    have hs4c : Clean k s4 := clean_and_left hs7c
    have hs4 : Need c j d 4 s4 := need_left (p := 4) (q := 3) hj (by omega) hcr3 hs7 hr3
    have hs3c : Clean k s3 := clean_and_right hM
    have hs3 : Need c j d 3 s3 := need_and_left (need_right (p := 4) (q := 3) hj (by decide) (by omega) hs7c hs7 hr4)
    have hs2c : Clean k s2 := clean_and_right hM
    have hs2 : Need c j d 2 s2 := need_and_left (need_or
      (need_or
        (need_left (p := 2) (q := 2) hj (by omega) hcr2 hs4 hr2)
        (need_right (p := 2) (q := 2) hj (by decide) (by omega) hs4c hs4 hr2))
      (need_left (p := 2) (q := 1) hj (by omega) hmb hs3 hr1))
    have hs1 := need_and_left (m2 := M) (need_or
      (need_or
        (need_right (p := 2) (q := 1) hj (by decide) (by omega) hs3c hs3 hr2)
        (by simpa [Nat.one_mul] using need_left (p := 1) (q := 1) hj (by omega) hmb hs2 hr1))
      (by simpa [Nat.one_mul] using need_right (p := 1) (q := 1) hj (by decide) (by omega) hs2c hs2 hr1))
    exact need_one_fact hs1

private def blueLoop (M k b : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | d + 1, acc => blueLoop M k b d (acc ||| blueStepD M k b (d + 1))

private lemma blueLoop_clean {k b : Nat} :
    ∀ n acc, Clean k acc → Clean k (blueLoop (repMask (low N) k) k b n acc) := by
  intro n
  induction n with
  | zero => intro acc hacc; exact hacc
  | succ n ih =>
    intro acc hacc
    exact ih _ (clean_or hacc blueStepD_clean)

private lemma blueLoop_sound {c : Nat → Bool} (hno : ¬ Goal c) {k j b : Nat}
    (hj : j < k) (hmb : Clean k b) (fb : Fact c false j b) :
    ∀ n acc, n ≤ 13 → Fact c true j acc → Fact c true j (blueLoop (repMask (low N) k) k b n acc) := by
  intro n
  induction n with
  | zero => intro acc _ hacc; exact hacc
  | succ n ih =>
    intro acc hn hacc
    exact ih _ (by omega) (fact_or hacc (blueStepD_sound hno hj (by omega) hn hmb fb))

private def propRounds (M k : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, r, b => (r, b)
  | n + 1, r, b =>
    let b' := redPropagate M r b
    let r' := r ||| blueLoop M k b' 13 0
    propRounds M k n r' b'

private lemma propRounds_sound {c : Nat → Bool} (hno : ¬ Goal c) {k j : Nat} (hj : j < k) :
    ∀ n r b, Clean k r → Clean k b → Fact c true j r → Fact c false j b →
      let res := propRounds (repMask (low N) k) k n r b
      Clean k res.1 ∧ Clean k res.2 ∧ Fact c true j res.1 ∧ Fact c false j res.2 := by
  intro n
  induction n with
  | zero => intro r b hcr hcb fr fb; exact ⟨hcr, hcb, fr, fb⟩
  | succ n ih =>
    intro r b hcr hcb fr fb
    have hM : Clean k (repMask (low N) k) := clean_repMask_low (Nat.le_refl N)
    have hcb' : Clean k (redPropagate (repMask (low N) k) r b) :=
      clean_or hcb (clean_and_right hM)
    have fb' : Fact c false j (redPropagate (repMask (low N) k) r b) :=
      fact_or fb (fact_and_left (redLoop_sound hno hj hcr fr 90 0 (Nat.le_refl 90)
        (fun x _ h => by simp [At, Bit] at h)))
    have hcr' : Clean k (r ||| blueLoop (repMask (low N) k) k (redPropagate (repMask (low N) k) r b) 13 0) :=
      clean_or hcr (blueLoop_clean 13 0 (fun j' x' _ _ _ h => by simp [At, Bit] at h))
    have fr' : Fact c true j (r ||| blueLoop (repMask (low N) k) k (redPropagate (repMask (low N) k) r b) 13 0) :=
      fact_or fr (blueLoop_sound hno hj hcb' fb' 13 0 (Nat.le_refl 13)
        (fun x _ h => by simp [At, Bit] at h))
    exact ih _ _ hcr' hcb' fr' fb'

private lemma mod_mul_decomp (x a b : Nat) :
    x % (a * b) = x % a + a * ((x / a) % b) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp only [Nat.mul_zero, Nat.mod_zero]
    rw [Nat.add_comm]
    exact (Nat.div_add_mod x a).symm
  have h1 : x = a * b * (x / (a * b)) + x % (a * b) := (Nat.div_add_mod x (a * b)).symm
  have h2 : x / a = b * (x / (a * b)) + (x / a) % b := by
    rw [← Nat.div_div_eq_div_mul]; exact (Nat.div_add_mod (x / a) b).symm
  have h3 : x = a * (x / a) + x % a := (Nat.div_add_mod x a).symm
  rw [h2, Nat.mul_add, ← Nat.mul_assoc] at h3
  omega

private lemma div_mod_and (a b s m : Nat) :
    ((a &&& b) / 2 ^ s) % 2 ^ m = (a / 2 ^ s % 2 ^ m) &&& (b / 2 ^ s % 2 ^ m) := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases ht : t < m <;> simp [ht]

private def allConflict (k r b : Nat) : Bool :=
  let M := repMask (low N) k
  let C := (r &&& b) &&& M
  let H := repMask (1 <<< 383) k
  ((H - C) &&& H) == 0

private lemma allConflict_sound {c : Nat → Bool} {k j r b : Nat}
    (hj : j < k) (fr : Fact c true j r) (fb : Fact c false j b)
    (hok : allConflict k r b = true) : False := by
  unfold allConflict at hok
  simp only [beq_iff_eq] at hok
  set M := repMask (low N) k
  set C := (r &&& b) &&& M
  set H := repMask (1 <<< 383) k
  have hlowW : low N < 2 ^ W :=
    lt_of_lt_of_le low_lt (Nat.pow_le_pow_right (by decide) (by simp only [N, W]; decide))
  have h1bit : (1 <<< 383) < 2 ^ W := by
    rw [Nat.shiftLeft_eq, one_mul]
    exact Nat.pow_lt_pow_right (by decide) (by simp only [W]; decide)
  have hH_lane : ∀ i, i < k → (H / 2 ^ (W * i)) % 2 ^ W = 2 ^ 383 := by
    intro i hi
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    by_cases ht : t < W
    · have hAt : Bit H (W * i + t) ↔ Bit (1 <<< 383) t := repMask_at h1bit k i t hi ht
      simp only [ht, decide_true, Bool.true_and]
      rw [Nat.add_comm, Bool.eq_iff_iff]
      simpa [Bit, Nat.shiftLeft_eq, Nat.testBit_two_pow] using hAt
    · simp [ht, show 383 ≠ t by simp only [W] at ht; omega]
  have hM_lane : ∀ i, i < k → (M / 2 ^ (W * i)) % 2 ^ W = low N := by
    intro i hi
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    by_cases ht : t < W
    · have hAt : Bit M (W * i + t) ↔ Bit (low N) t := repMask_at hlowW k i t hi ht
      simp only [ht, decide_true, Bool.true_and]
      rw [Nat.add_comm, Bool.eq_iff_iff]
      simpa [Bit] using hAt
    · have hge : ¬ t < N := by simp only [N, W] at *; omega
      simp [ht, show (low N).testBit t = false by rw [Bool.eq_false_iff]; intro hb; exact hge (bit_low.mp hb)]
  have hC_lane_lt : ∀ i, i < k → (C / 2 ^ (W * i)) % 2 ^ W < 2 ^ 383 := by
    intro i hi
    have hle : (C / 2 ^ (W * i)) % 2 ^ W ≤ low N := by
      dsimp only [C]
      rw [div_mod_and, hM_lane i hi]
      exact Nat.and_le_right
    exact lt_of_le_of_lt hle (lt_trans low_lt (Nat.pow_lt_pow_right (by decide) (by simp only [N]; decide)))
  have hCj_zero : (C / 2 ^ (W * j)) % 2 ^ W = 0 := by
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit]
    by_cases htw : t < W
    · simp only [htw, decide_true, Bool.true_and]
      apply Bool.eq_false_iff.mpr
      intro hC
      rw [Nat.add_comm] at hC
      have ⟨hrb, hM⟩ := bit_and.mp hC
      have hlt := (repMask_at hlowW k j t hj htw).mp hM
      rw [bit_low] at hlt
      have ⟨hr, hb⟩ := bit_and.mp hrb
      have h1 := fr t hlt hr
      have h2 := fb t hlt hb
      rw [h1] at h2
      exact Bool.noConfusion h2
    · simp [htw]
  have hC_le_H_prefix : ∀ m, m ≤ k → C % 2 ^ (W * m) ≤ H % 2 ^ (W * m) := by
    intro m hm
    induction m with
    | zero => simp [Nat.mod_one]
    | succ m ih =>
      have h1 := ih (by omega)
      have hlt := hC_lane_lt m (by omega)
      have hHl := hH_lane m (by omega)
      rw [show W * (m + 1) = W * m + W by simp only [W]; omega, Nat.pow_add,
          mod_mul_decomp C, mod_mul_decomp H, hHl]
      have h2 : 2 ^ (W * m) * ((C / 2 ^ (W * m)) % 2 ^ W) ≤ 2 ^ (W * m) * 2 ^ 383 :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)
      omega
  have hC_bound : C < 2 ^ (W * k) := by
    have hMb : M < 2 ^ (W * k) := repMask_bound hlowW k
    exact lt_of_le_of_lt Nat.and_le_right hMb
  have hH_bound : H < 2 ^ (W * k) := repMask_bound h1bit k
  have hCleH : C ≤ H := by
    have := hC_le_H_prefix k (Nat.le_refl k)
    rwa [Nat.mod_eq_of_lt hC_bound, Nat.mod_eq_of_lt hH_bound] at this
  set P := 2 ^ (W * (j + 1))
  set Q := 2 ^ (W * j)
  have hPeq : P = Q * 2 ^ W := by
    simp only [P, Q, show W * (j + 1) = W * j + W by simp only [W]; omega, Nat.pow_add]
  have hCm : C % P = C % Q := by
    rw [hPeq, mod_mul_decomp, hCj_zero, Nat.mul_zero, Nat.add_zero]
  have hHm : H % P = H % Q + Q * 2 ^ 383 := by
    rw [hPeq, mod_mul_decomp, hH_lane j hj]
  have hCQ_le_HQ : C % Q ≤ H % Q := hC_le_H_prefix j (by omega)
  have hq_le : C / P ≤ H / P := Nat.div_le_div_right hCleH
  have hsub : H - C = (H / P - C / P) * P + (H % Q - C % Q) + Q * 2 ^ 383 := by
    have hHdec := (Nat.div_add_mod H P).symm
    have hCdec := (Nat.div_add_mod C P).symm
    have hmul : (H / P - C / P) * P = (H / P) * P - (C / P) * P := Nat.sub_mul _ _ _
    have h1 : (C / P) * P ≤ (H / P) * P := Nat.mul_le_mul_right P hq_le
    rw [Nat.mul_comm P (H / P)] at hHdec
    rw [Nat.mul_comm P (C / P)] at hCdec
    omega
  have hdiv : (H - C) / (Q * 2 ^ 383) = 2 * (H / P - C / P) + 1 := by
    have hPe : P = (Q * 2 ^ 383) * 2 := by
      rw [hPeq, show W = 383 + 1 by decide, Nat.pow_add, Nat.pow_one, Nat.mul_assoc]
    have hrem_lt : H % Q - C % Q < Q * 2 ^ 383 := by
      have hHQ : H % Q < Q := Nat.mod_lt H (Nat.two_pow_pos _)
      have hQle : Q ≤ Q * 2 ^ 383 := Nat.le_mul_of_pos_right Q (Nat.two_pow_pos _)
      omega
    have hrewrite : H - C = (H % Q - C % Q) + (Q * 2 ^ 383) * (2 * (H / P - C / P) + 1) := by
      rw [hsub, hPe]
      ring_nf
    rw [hrewrite, Nat.add_mul_div_left _ _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)),
        Nat.div_eq_of_lt hrem_lt, Nat.zero_add]
  have hbitHC : Bit (H - C) (W * j + 383) := by
    simp only [Bit, Nat.testBit, Nat.shiftRight_eq_div_pow]
    rw [Nat.pow_add]
    change (1 &&& (H - C) / (Q * 2 ^ 383) != 0) = true
    rw [hdiv, Nat.and_comm]
    simp [Nat.and_one_is_mod]
  have hbitH : Bit H (W * j + 383) :=
    (repMask_at h1bit k j 383 hj (by decide)).mpr (by simp [Bit, Nat.shiftLeft_eq])
  have hboth : Bit ((H - C) &&& H) (W * j + 383) := bit_and.mpr ⟨hbitHC, hbitH⟩
  rw [hok] at hboth
  simp [Bit] at hboth

-- Prefix-coded binary decision tree expansion directly into packed lanes
private def expand (fuel r b code : Nat) : Option (Nat × Nat × Nat × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if code &&& 1 == 0 then
      some (1, r, b, code >>> 1)
    else
      let v := (code >>> 1) &&& 255
      if v < N then
        let bit := 1 <<< v
        match expand fuel (r ||| bit) b (code >>> 9) with
        | none => none
        | some (k1, r1, b1, code1) =>
          match expand fuel r (b ||| bit) code1 with
          | none => none
          | some (k2, r2, b2, code2) =>
            some (k1 + k2, r1 ||| (r2 <<< (W * k1)), b1 ||| (b2 <<< (W * k1)), code2)
      else none

private lemma bit_single {v x : Nat} : Bit (1 <<< v) x ↔ v = x := by
  simp [Bit, Nat.shiftLeft_eq, Nat.testBit_two_pow]

private lemma fact_add_bit {c : Nat → Bool} {b : Bool} {m v : Nat}
    (hm : Fact c b 0 m) (hv : c v = b) : Fact c b 0 (m ||| (1 <<< v)) := by
  intro x hx h
  rcases bit_or.mp h with h1 | h2
  · exact hm x hx h1
  · have hveq : v = x := by simpa [At, bit_single] using h2
    exact hveq ▸ hv

private lemma lt_two_pow_or_bit {m v : Nat} (hm : m < 2 ^ N) (hv : v < N) :
    (m ||| (1 <<< v)) < 2 ^ N := by
  apply Nat.or_lt_two_pow hm
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by decide) hv

private def BlockOk (k r b : Nat) : Prop :=
  r < 2 ^ (W * k) ∧ b < 2 ^ (W * k) ∧ Clean k r ∧ Clean k b

private lemma blockOk_one {r b : Nat} (hr : r < 2 ^ N) (hb : b < 2 ^ N) : BlockOk 1 r b := by
  have hNW : N ≤ W := by decide
  refine ⟨lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by simp only [Nat.mul_one]; exact hNW)),
          lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by simp only [Nat.mul_one]; exact hNW)),
          ?_, ?_⟩
  · intro j x' hj hx1 _ hbit
    have hj0 : j = 0 := by omega
    subst hj0
    have hlt := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide : 0 < 2) hx1)
    simp [At, Bit, Nat.testBit_lt_two_pow hlt] at hbit
  · intro j x' hj hx1 _ hbit
    have hj0 : j = 0 := by omega
    subst hj0
    have hlt := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hx1)
    simp [At, Bit, Nat.testBit_lt_two_pow hlt] at hbit

private lemma merge_block_ok {k1 r1 b1 k2 r2 b2 : Nat}
    (h1 : BlockOk k1 r1 b1) (h2 : BlockOk k2 r2 b2) :
    BlockOk (k1 + k2) (r1 ||| (r2 <<< (W * k1))) (b1 ||| (b2 <<< (W * k1))) := by
  obtain ⟨hr1, hb1, hcr1, hcb1⟩ := h1
  obtain ⟨hr2, hb2, hcr2, hcb2⟩ := h2
  have hpow : ∀ m1 m2, m1 < 2 ^ (W * k1) → m2 < 2 ^ (W * k2) →
      (m1 ||| (m2 <<< (W * k1))) < 2 ^ (W * (k1 + k2)) := by
    intro m1 m2 hm1 hm2
    apply Nat.or_lt_two_pow
    · exact lt_of_lt_of_le hm1 (Nat.pow_le_pow_right (by decide) (by simp only [W]; omega))
    · rw [Nat.shiftLeft_eq, show W * (k1 + k2) = W * k2 + W * k1 by simp [Nat.mul_add, Nat.add_comm], Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hm2 (Nat.two_pow_pos _)
  have hcl : ∀ m1 m2, m1 < 2 ^ (W * k1) → Clean k1 m1 → Clean k2 m2 →
      Clean (k1 + k2) (m1 ||| (m2 <<< (W * k1))) := by
    intro m1 m2 hm1 hc1 hc2 j x hj hx1 hx2 h
    rcases bit_or.mp h with ha | hb
    · by_cases hjk : j < k1
      · exact hc1 j x hjk hx1 hx2 ha
      · have hle : W * k1 ≤ W * j + x := by simp only [W] at *; omega
        have hlt := lt_of_lt_of_le hm1 (Nat.pow_le_pow_right (by decide : 0 < 2) hle)
        simp [Bit, Nat.testBit_lt_two_pow hlt] at ha
    · obtain ⟨hle, hb'⟩ := bit_shl.mp hb
      have hjk : k1 ≤ j := by simp only [W] at *; omega
      have heq : W * j + x - W * k1 = W * (j - k1) + x := by simp only [W] at *; omega
      rw [heq] at hb'
      exact hc2 (j - k1) x (by omega) hx1 hx2 hb'
  exact ⟨hpow r1 r2 hr1 hr2, hpow b1 b2 hb1 hb2, hcl r1 r2 hr1 hcr1 hcr2, hcl b1 b2 hb1 hcb1 hcb2⟩

private lemma merge_fact_left {c : Nat → Bool} {k1 r1 b1 r2 b2 j : Nat}
    (hj : j < k1) (fr : Fact c true j r1) (fb : Fact c false j b1) :
    Fact c true j (r1 ||| (r2 <<< (W * k1))) ∧ Fact c false j (b1 ||| (b2 <<< (W * k1))) := by
  have hstep : ∀ (b : Bool) m1 m2, Fact c b j m1 → Fact c b j (m1 ||| (m2 <<< (W * k1))) := by
    intro b m1 m2 fm x hx h
    rcases bit_or.mp h with h1 | h2
    · exact fm x hx h1
    · obtain ⟨hle, _⟩ := bit_shl.mp h2
      simp only [N, W] at *; omega
  exact ⟨hstep true r1 r2 fr, hstep false b1 b2 fb⟩

private lemma merge_fact_right {c : Nat → Bool} {k1 r1 b1 r2 b2 j : Nat}
    (hr1 : r1 < 2 ^ (W * k1)) (hb1 : b1 < 2 ^ (W * k1))
    (fr : Fact c true j r2) (fb : Fact c false j b2) :
    Fact c true (k1 + j) (r1 ||| (r2 <<< (W * k1))) ∧
    Fact c false (k1 + j) (b1 ||| (b2 <<< (W * k1))) := by
  have hstep : ∀ (b : Bool) m1 m2, m1 < 2 ^ (W * k1) → Fact c b j m2 →
      Fact c b (k1 + j) (m1 ||| (m2 <<< (W * k1))) := by
    intro b m1 m2 hm1 fm x hx h
    rcases bit_or.mp h with h1 | h2
    · have hle : W * k1 ≤ W * (k1 + j) + x := by simp only [W]; omega
      have hlt := lt_of_lt_of_le hm1 (Nat.pow_le_pow_right (by decide : 0 < 2) hle)
      simp [Bit, Nat.testBit_lt_two_pow hlt] at h1
    · obtain ⟨_, h2'⟩ := bit_shl.mp h2
      have heq : W * (k1 + j) + x - W * k1 = W * j + x := by simp only [W]; omega
      rw [heq] at h2'
      exact fm x hx h2'
  exact ⟨hstep true r1 r2 hr1 fr, hstep false b1 b2 hb1 fb⟩

private lemma expand_ok :
    ∀ fuel r b code k R B code',
      r < 2 ^ N → b < 2 ^ N →
      expand fuel r b code = some (k, R, B, code') →
      BlockOk k R B := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ h; simp [expand] at h
  | succ fuel ih =>
    intro r b code k R B code' hr hb hrun
    unfold expand at hrun
    dsimp only at hrun
    split at hrun
    · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl, rfl, _⟩ := hrun
      exact blockOk_one hr hb
    · split at hrun
      · rename_i hv
        cases h1 : expand fuel (r ||| (1 <<< ((code >>> 1) &&& 255))) b (code >>> 9) with
        | none => rw [h1] at hrun; simp at hrun
        | some res1 =>
          rcases res1 with ⟨k1, r1, b1, code1⟩
          rw [h1] at hrun
          dsimp only at hrun
          cases h2 : expand fuel r (b ||| (1 <<< ((code >>> 1) &&& 255))) code1 with
          | none => rw [h2] at hrun; simp at hrun
          | some res2 =>
            rcases res2 with ⟨k2, r2, b2, code2⟩
            rw [h2] at hrun
            simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl, rfl, _⟩ := hrun
            exact merge_block_ok
              (ih _ _ _ _ _ _ _ (lt_two_pow_or_bit hr hv) hb h1)
              (ih _ _ _ _ _ _ _ hr (lt_two_pow_or_bit hb hv) h2)
      · simp at hrun

private lemma expand_sound {c : Nat → Bool} :
    ∀ fuel r b code k R B code',
      r < 2 ^ N → b < 2 ^ N →
      Fact c true 0 r → Fact c false 0 b →
      expand fuel r b code = some (k, R, B, code') →
      BlockOk k R B ∧ ∃ j < k, Fact c true j R ∧ Fact c false j B := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ h; simp [expand] at h
  | succ fuel ih =>
    intro r b code k R B code' hr hb fr fb hrun
    unfold expand at hrun
    dsimp only at hrun
    split at hrun
    · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl, rfl, _⟩ := hrun
      exact ⟨blockOk_one hr hb, 0, Nat.zero_lt_one, fr, fb⟩
    · split at hrun
      · rename_i hv
        cases h1 : expand fuel (r ||| (1 <<< ((code >>> 1) &&& 255))) b (code >>> 9) with
        | none => rw [h1] at hrun; simp at hrun
        | some res1 =>
          rcases res1 with ⟨k1, r1, b1, code1⟩
          rw [h1] at hrun
          dsimp only at hrun
          cases h2 : expand fuel r (b ||| (1 <<< ((code >>> 1) &&& 255))) code1 with
          | none => rw [h2] at hrun; simp at hrun
          | some res2 =>
            rcases res2 with ⟨k2, r2, b2, code2⟩
            rw [h2] at hrun
            simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl, rfl, _⟩ := hrun
            have hbk1 := expand_ok fuel _ _ _ _ _ _ _ (lt_two_pow_or_bit hr hv) hb h1
            have hbk2 := expand_ok fuel _ _ _ _ _ _ _ hr (lt_two_pow_or_bit hb hv) h2
            refine ⟨merge_block_ok hbk1 hbk2, ?_⟩
            cases hcv : c ((code >>> 1) &&& 255) with
            | true =>
              obtain ⟨_, j, hj, fr1, fb1⟩ := ih _ _ _ _ _ _ _ (lt_two_pow_or_bit hr hv) hb (fact_add_bit fr hcv) fb h1
              exact ⟨j, by omega, merge_fact_left hj fr1 fb1⟩
            | false =>
              obtain ⟨_, j, hj, fr2, fb2⟩ := ih _ _ _ _ _ _ _ hr (lt_two_pow_or_bit hb hv) fr (fact_add_bit fb hcv) h2
              exact ⟨k1 + j, by omega, merge_fact_right hbk1.1 hbk1.2.1 fr2 fb2⟩
      · simp at hrun

private def checkChunk (initRounds rounds fuel r b code : Nat) : Bool :=
  if r < 2 ^ N && b < 2 ^ N then
    let r0 := propRounds (repMask (low N) 1) 1 initRounds r b
    let r0' := r0.1 &&& low N
    let b0' := r0.2 &&& low N
    match expand fuel r0' b0' code with
    | none => false
    | some (k, R, B, _) =>
      let M := repMask (low N) k
      let res := propRounds M k rounds R B
      allConflict k res.1 res.2
  else false

private def Impossible (r b : Nat) : Prop :=
  ∀ c, ¬ Goal c → Fact c true 0 r → Fact c false 0 b → False

private lemma checkChunk_sound {initRounds rounds fuel r b code : Nat}
    (hok : checkChunk initRounds rounds fuel r b code = true) : Impossible r b := by
  intro c hno fr fb
  unfold checkChunk at hok
  dsimp only at hok
  split at hok
  · rename_i hrb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrb
    have hbk0 := blockOk_one hrb.1 hrb.2
    have hprop0 := propRounds_sound hno Nat.zero_lt_one initRounds r b hbk0.2.2.1 hbk0.2.2.2 fr fb
    set r0 := propRounds (repMask (low N) 1) 1 initRounds r b
    have hr0' : (r0.1 &&& low N) < 2 ^ N := lt_of_le_of_lt Nat.and_le_right low_lt
    have hb0' : (r0.2 &&& low N) < 2 ^ N := lt_of_le_of_lt Nat.and_le_right low_lt
    have fr0' : Fact c true 0 (r0.1 &&& low N) := fact_and_left hprop0.2.2.1
    have fb0' : Fact c false 0 (r0.2 &&& low N) := fact_and_left hprop0.2.2.2
    cases he : expand fuel (r0.1 &&& low N) (r0.2 &&& low N) code with
    | none => rw [he] at hok; simp at hok
    | some res =>
      rcases res with ⟨k, R, B, rest⟩
      rw [he] at hok
      dsimp only at hok
      obtain ⟨hBk, j, hj, frR, fbB⟩ := expand_sound fuel _ _ _ k R B rest hr0' hb0' fr0' fb0' he
      have hprop := propRounds_sound hno hj rounds R B hBk.2.2.1 hBk.2.2.2 frR fbB
      exact allConflict_sound hj hprop.2.2.1 hprop.2.2.2 hok
  · simp at hok

-- Branching and exact reflection symmetry
private def SymMask (m : Nat) : Prop :=
  ∀ x, x < N → Bit m x → Bit m (N - 1 - x)

private lemma sym_of_decide {m : Nat} (h : ∀ x : Fin N, m.testBit x.val = true → m.testBit (N - 1 - x.val) = true) :
    SymMask m :=
  fun x hx hb => h ⟨x, hx⟩ hb

private lemma sym_add_pair {m u : Nat} (hu : u < N) (hs : SymMask m) :
    SymMask (m ||| (1 <<< u) ||| (1 <<< (N - 1 - u))) := by
  intro x hx hb
  rcases bit_or.mp hb with hb1 | hb2
  · rcases bit_or.mp hb1 with hm | h1
    · exact bit_or.mpr (Or.inl (bit_or.mpr (Or.inl (hs x hx hm))))
    · have ex : u = x := bit_single.mp h1
      exact bit_or.mpr (Or.inr (bit_single.mpr (by omega)))
  · have ex : N - 1 - u = x := bit_single.mp hb2
    exact bit_or.mpr (Or.inl (bit_or.mpr (Or.inr (bit_single.mpr (by omega)))))

private lemma goal_rev {c : Nat → Bool} (h : Goal (fun x => c (N - 1 - x))) : Goal c := by
  obtain ⟨b, a, d, hd, hb, hm⟩ := h
  set L := if b then 2 else 13
  have hL : a + L * d < N := hb
  refine ⟨b, N - 1 - (a + L * d), d, hd, ?_, ?_⟩
  · change N - 1 - (a + L * d) + L * d < N
    omega
  · intro t ht
    have htL : t.val ≤ L := ht
    have hL14 : L < 14 := by dsimp only [L]; cases b <;> decide
    have hlt : L - t.val < 14 := by omega
    have hstep : c (N - 1 - (a + (L - t.val) * d)) = b := hm ⟨L - t.val, hlt⟩ (by dsimp only; omega)
    have hidx : N - 1 - (a + (L - t.val) * d) = N - 1 - (a + L * d) + t.val * d := by
      have : (L - t.val) * d + t.val * d = L * d := by rw [← Nat.add_mul]; congr 1; omega
      omega
    rwa [hidx] at hstep

private lemma fact_rev {c : Nat → Bool} {b : Bool} {m : Nat}
    (hs : SymMask m) (hf : Fact c b 0 m) : Fact (fun x => c (N - 1 - x)) b 0 m := by
  intro x hx hm
  have h1 : Bit m (N - 1 - x) := hs x hx (by simpa [At] using hm)
  exact hf (N - 1 - x) (by omega) (by simpa [At] using h1)

private lemma branch2 {r b : Nat} (u : Nat)
    (hR : Impossible (r ||| (1 <<< u)) b)
    (hB : Impossible r (b ||| (1 <<< u))) : Impossible r b := by
  intro c hno fr fb
  cases hcu : c u with
  | true => exact hR c hno (fact_add_bit fr hcu) fb
  | false => exact hB c hno fr (fact_add_bit fb hcu)

private lemma sym_branch3 {r b : Nat} (u : Nat) (hu : u < N)
    (sr : SymMask r) (sb : SymMask b)
    (hRR : Impossible (r ||| (1 <<< u) ||| (1 <<< (N - 1 - u))) b)
    (hBB : Impossible r (b ||| (1 <<< u) ||| (1 <<< (N - 1 - u))))
    (hRB : Impossible (r ||| (1 <<< u)) (b ||| (1 <<< (N - 1 - u)))) : Impossible r b := by
  intro c hno fr fb
  cases hcu : c u with
  | true =>
    cases hcv : c (N - 1 - u) with
    | true => exact hRR c hno (fact_add_bit (fact_add_bit fr hcu) hcv) fb
    | false => exact hRB c hno (fact_add_bit fr hcu) (fact_add_bit fb hcv)
  | false =>
    cases hcv : c (N - 1 - u) with
    | true =>
      let cr := fun x => c (N - 1 - x)
      have hnor : ¬ Goal cr := fun hg => hno (goal_rev hg)
      have hcru : cr u = true := hcv
      have hcrv : cr (N - 1 - u) = false := by
        simpa [cr, show N - 1 - (N - 1 - u) = u by omega] using hcu
      exact hRB cr hnor (fact_add_bit (fact_rev sr fr) hcru) (fact_add_bit (fact_rev sb fb) hcrv)
    | false => exact hBB c hno fr (fact_add_bit (fact_add_bit fb hcu) hcv)

private lemma goal_of_shift {c : Nat → Bool}
    (h : Goal (fun x => c (x + 1))) :
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13) * d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a + t.val * d) = b := by
  obtain ⟨b, a, d, hd, hb, hm⟩ := h
  refine ⟨b, a + 1, d, hd, ?_, ?_⟩
  · cases b <;> dsimp only [N] at hb <;> omega
  · intro t ht
    simpa [Nat.add_right_comm] using hm t ht

private lemma prove_H1_of_root
    (hroot : Impossible 0x802000000000000000000000 0x7fc000000000000000000000) :
    OMA.R_Green14_W_3_14_R1_H3_R1_H3_R1.H1 := by
  intro c h86 h96 hgap
  by_contra hno
  let c1 := fun x => c (x + 1)
  have hno1 : ¬ Goal c1 := fun hg => hno (goal_of_shift hg)
  have hr : Fact c1 true 0 0x802000000000000000000000 := by
    intro x hx h
    have hdec : ∀ i : Fin N, (0x802000000000000000000000 : Nat).testBit i.val = true →
        i.val = 85 ∨ i.val = 95 := by decide +kernel
    rcases hdec ⟨x, hx⟩ (by simpa [At, Bit] using h) with h1 | h2
    · rw [show x = 85 from h1]; exact h86
    · rw [show x = 95 from h2]; exact h96
  have hb : Fact c1 false 0 0x7fc000000000000000000000 := by
    intro x hx h
    have hdec : ∀ i : Fin N, (0x7fc000000000000000000000 : Nat).testBit i.val = true →
        85 < i.val ∧ i.val < 95 := by decide +kernel
    obtain ⟨hlo, hhi⟩ := hdec ⟨x, hx⟩ (by simpa [At, Bit] using h)
    dsimp only at hlo hhi
    exact hgap (x + 1) (by omega) (by omega)
  exact hroot c1 hno1 hr hb


set_option maxHeartbeats 8000000 in
private lemma chk_9 : Impossible 0x41480802025040000000000000000 0x7fc000000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=0) (fuel:=1) (code:=0x0) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_12 : Impossible 0x1482802825000000000000000000 0x400007fc000040000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=0) (fuel:=1) (code:=0x0) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_13 : Impossible 0x1480802025000000000000000000 0x400027fc800040000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=5) (fuel:=5) (code:=0x1f6669cc43) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_14 : Impossible 0x1480802825000000000000000000 0x400027fc000040000000000000000 :=
  checkChunk_sound (initRounds:=4) (rounds:=0) (fuel:=1) (code:=0x0) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_16 : Impossible 0x1480802025040000000000000000 0x400007fc000000000000000000000 :=
  checkChunk_sound (initRounds:=4) (rounds:=0) (fuel:=1) (code:=0x0) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_20 : Impossible 0x11400802005100000000000000000 0x807fc020000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=0) (fuel:=1) (code:=0x0) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_23 : Impossible 0x801400802005002000000000000000 0x100807fc020100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=5) (fuel:=9) (code:=0x325131ee4354251e1e7c8da7e9ea57) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_24 : Impossible 0x1400802005000000000000000000 0x8100807fc020102000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=16) (code:=0x4123c8b04f335ee751a41f28f1cd9a6d1742825d275ea66a12989c64594e5f06d8fa0c8686f9d48b19c6908b7a9be81a029d9190e3dc91b7c697c8fb3e53149d092f88999c44dee28dbe6182d8a6309b4ea8b1a457214458ba2f886878591c5082ea2c6f6fa26808df50dc61167515ca7086874b43cb0c899cc4f91685a26619277187a3c54e15dee9d14e619168499a6fbf5f20727330c670d46112c5d047054f14ea2c1eb3115d9287369c43f496e7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_25 : Impossible 0x1400802005002000000000000000 0x8100807fc020100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=16) (code:=0x39c5c4522d1330cdf089a164f10dee42dbe33923399864731c5f061975117b91610d92404f5639c40f45f518860df36829bd4e339c6d428e475115fa2027ca467aa22619c6cd174fd3895ce5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_27 : Impossible 0x1400802005100000000000000000 0x100807fc020000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=16) (code:=0x37bdcf14b4e538c20cba369f222cf6ef1ce7b9be618fb04f719bcf94c52715c433c430c5a73389461cc39a8c8715dde1bd069d) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_29 : Impossible 0x1400802025000000000000000000 0x807fc000000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=17) (code:=0x24e673abec6f09194cea0db789d41bd031cdee2398e2bc8d090e53a6d1be24edf1036f9f675338ae37c0e4ea4188a9d10d0d7bbe4a70398d2714ea242b86f97c7ca1a7395d9a349127b) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_37 : Impossible 0x800010608020c1000020000000000000 0x4007fc004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=4) (fuel:=6) (code:=0x31c175a22ca3479) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_38 : Impossible 0x10608020c1000000000000000000 0x800004007fc004000020000000000000 :=
  checkChunk_sound (initRounds:=3) (rounds:=0) (fuel:=1) (code:=0x0) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_39 : Impossible 0x10608020c1000020000000000000 0x800004007fc004000000000000000000 :=
  checkChunk_sound (initRounds:=4) (rounds:=0) (fuel:=1) (code:=0x0) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_43 : Impossible 0x101040802041010000000000000000 0x4207fc084000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=6) (fuel:=4) (code:=0x7520c9b) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_44 : Impossible 0x1040802041000000000000000000 0x1004207fc084010000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=18) (code:=0xba86bac1651add1ba7311af71a4222dd81b1c88c04f50446068d3246945a8c37d1d80a1a23685a268d7aa6a8288af91ba239d41947529a6c3d523374eb23a8bb7e0a3286f9bcea234e737d236387dbd4dd11a4586a9ea22988ea8eb7df2929c403d89be407a26be51112c14f138835df267a62819c5ea92a1a538d622a6412d2b9c425a8e9c459a2994797c824ce24d87233be4ea228ba619fe1c4ff1f2359d4454c90330e4ad1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_45 : Impossible 0x1040802041010000000000000000 0x1004207fc084000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=6) (fuel:=9) (code:=0xdd37ca33e47f0ea9b20c8d) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_47 : Impossible 0x10408020c1000000000000000000 0x4207fc004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=8) (code:=0x939467c98e0bad1468b26b) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_53 : Impossible 0x5001803001400000000000000000 0x4407fc044000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=0) (fuel:=1) (code:=0x0) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_54 : Impossible 0x5000802001400000000000000000 0x4417fd044000000000000000000 :=
  checkChunk_sound (initRounds:=2) (rounds:=6) (fuel:=14) (code:=0x67818ca2990635bfc8191665bd50520a2e946e707131c8b20c7f8dbbc1ea6d8dbac22cf5919ce368eadf) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_55 : Impossible 0x5000803001400000000000000000 0x4417fc044000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=19) (code:=0x2728b6f8d41548b42e3ae9214993f408b35cca510848538c3933833c04d2658e6265a243833a8c7b2650530bfc45d966f9021c8da3084cc2cf5989ca2abe4298f63fc414f97b90b6b9ea8ba0c7b1ea7f4c81cdea77c7535414c728da240cf7205be6b) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_59 : Impossible 0x41000802001040000000000000000 0x44407fc044400000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=18) (code:=0x4526ba4194c7164552e8da4084d434ff74c143fe2e9294e40c447522e679ce819fe4dc747fbd47f9f636a3a3783de3b1944949494cae1092c750220a51a228ac34fd3a48e8ba35a04ca0d653114c33a4b27a85326c8319c6b33c9a1acea1ac6f3f44d3ec0e64d28b841088b0544aa43f457084da1fcba23c369827584f15c374bd1945cd6fb26c4520c9a127465fa9f45cc7455110ba47c7437b0c77cc44748ebbcc73ace18c9b512c906d44d497e8eb868db1fa548fe46d134cc3b144537f9bccf494e78e8510fb3d9b654bf5091141237b9de84bf445239f66d6494e0431ec5136b2c5328c551648da1a929347d8e47da9c3685a08e6d288aa1cc891ec9a1347253bf5c2a1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_60 : Impossible 0x1000802001000000000000000000 0x444407fc044440000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=0) (fuel:=1) (code:=0x0) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_61 : Impossible 0x1000802001040000000000000000 0x444407fc044400000000000000000 :=
  checkChunk_sound (initRounds:=2) (rounds:=9) (fuel:=18) (code:=0xe632a6d171bd0b23a71266fb0f74da64ef0399c49b4f90377b3c29ea613df6399fe1361689a361027f9346542d1363853b1d3e7b8e249cdf46c9977b841562e86a06388eb6d99e77946928530425d0e4571eccf42c7f1c60a2c8779bf1b48cdb33dc2a108da62538b84d4ca4e438de759426080a6713695c229364c9345d0e251a3d3e28449d3333a361ad328493650c0c679fc14d1eeb6d8285173ec713689b22a4ac16383fb6c77a3a1fc530dc9a6b1145526d02c9041a64ce2d91e32902708ea1c46b20c8f36c389963250b8aa62fb4947b8ae6f10f41a62df107050653fcdb4da64da2846f3fc7520477b2499142df3d836d3292a16779466f9f686c6dd6a9) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_63 : Impossible 0x1000802001400000000000000000 0x44407fc044000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=25) (code:=0x164eb80c4461b2c611ec0ceff2f9d6438ae3fdee3dba47fb44f90e907bbfdd2cf4458635df630c5f438e9298f7429f23a4f6202749fe51b3c871fe7b689ac688df3fd310677fba4ca828671fc5f22c4515c0ce45c74a2e98a8da1eec34d46137c850c333a36298e63a4fb36d0345ca367885369be6507319d23659ae438da519bed13583fc862b90e6b3d9f2fd19636821e3998eff358fecb1b6e9415a28a90a19ca6519493f5397083fbbc41636db45ca33dc7b6f80e92c99cd72697d1615c857588f9ae1bb7d174c5f2f505f7d98e228b23d8d71cda21cdde3889345846e1b23246123aa9c4518487229d162aa36f90d6398a621dd6808a77ca2e38b6dbe2068b9d65f29c853fc674a4338fe42b3c7f9ec4599e71455d213c6710ca30ce730ba33a2c7f093b0cfb39cce04d3ab0c5717461194618ca6b0e67d97d520ea9f188673f9be474c337c550c4a345c547110a0a66d9d4571867117c6122ecb398f724d156f814d368537c713380ac73218a6309c5166d09e7082e90e7337ca6829ea7f86f99cbe185163889a1b48b3d4df77846d233991630bfda27b11538822c3113c35aaa2e71328a339cea2a99605a1aa2c9317c871fd4e1eca368923093c34be38c2d173bc36b2d036f88986a6f9c4751fc736dbe5fa1ac7b1b667b2c611961cc149f630a145f29c933690e3f916061298d613cbe26bfc26b84f644ca314ccb0daa7135f2fd06775926458f614c7324c338e6eb2146b0ce35b3c1cda24291b414c27b7f8eb32db6e972a847f8be8a9ce6b9ee45819cd6086672f9ae6f9ee7ca0c753284f3e4650be37c5f349b6288f93fcdb33a0cf70f933a2c3e4d67f0ce8505732badea368f611b7f9f735414db40c1ad4645bbc919b6df07eb6cf91d69f37cce1033e4d6758867151827b3c430e9679ae7c99c3399e7cbac339f2df4190f48cff2a4df3d8f933ceb37d0320c4345808adf2a8ba832368ba3f033fbd5a2991172988a388713ecce142731c2fb0e3094f815c6b8499414dee89c147d9d4da44e06101229f2711cee90db385f689c14748398ce73a84e920c9a39d153f9c26521c3fc9e7545819d16834c88dbfd4b40c938e66d906358ae43a06ef68815d42329cc4528c359d20e6db15cc75046d202651b6e982808a67939ce89a852f45d297c92770bec871c27499e1c9ce0a24d1ec7f5090e8b1d250a0a35a0220a81a846b738673a40e64d8e9fa33a4e81a84fb20a8e9ad017f839b1e1ad1729bec1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_65 : Impossible 0x1000802041000000000000000000 0x4407fc004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=29) (code:=0x7ca645d3ecff32c6fb040bedf46bf413cd62c8da2ea85110c120c7e2e9468903bc3728d129ab7ccb64885c9c31cdb7fa4e18e8321c730de858d28b1fd9221c4f15cff46bbc3fcdf45b8cf76088b235d673846a1e71b04df047512df64869234db21c34c0c80b9ce360a2ccf7e8088cd4a651b1c8b6fb243f9fe898e64d86f9ac731fcf748d094681464e91b7c7342cff44c89a9cf73ac6f9fe538d28b9ab0437e1a71a2653a621ee97b2438cef434532892910a3aa147c89b5c35dbf31458d244bf5f21ae84a72c92341cf0146839bfceb44c36d060a517398228d86913285923f512c1474778df2851a61b2cda0737c9062f9b63ad82818427f99608af90a4399b6df19c217e8da8d6881f289c35823f4f9688677586fcd48a831067911d3265132e906fa2649906518619bc8345c34439b4609cd1d329123488b0f941841a165d3f8da33c8b1fc7930cd742dfad14ca22029bbc6f1fc5d264a332c34d738c830ba719f67ca2451bc444d1d26d0b1e47d9fcca1bc21448ef224ba20d3251b1c378aa9f3ad923e50b2169b28c6b32cc13a50325040d355659ef14c81b65229cd17c9b6aaa3415df6749be36a647c9a4ca889c40daa0a1aff30d35494df39c1ebe446b05a203577b44c13a4ca0be239b4df3ac8d1d646ba408eb44be29b045d399ee48dbe494d10e6df3bc6b7c85f3e4ce438db3fbf4495f2a3508db17ccb1e20770d31cd16f8eb748e66744536474f908e91c9f22d9e6084fa2ef1195f2226f96b88b6fa32d11f2a1389d42054e2273538c379166b9be8cbdc22e22eb6482ca046b7f8df468c13f5a2749e206a40b248d106a31a511164897c8e20de2987e9fe8b469be4ccd5250fd3bc69264f91f251932d726c7f30ceb9aa12c916408ef93ae6a3e4991c4c14349ab9c9ac04cb202eb37c38c251ad13284fa642a9fac92344c9f26fb444c946ef0c7344f9298da9b1167e83fde275a644e4c39292740dfa6fbe5a26b9d296a628ca22713ab7411aa16088710936348722c82b994e2449321a48317423a3e8908d2f90e1865d3786f448eb3fa8437d0d3f80c4ba36a851a3edfa11a32a84597cb041fa2a994de2c912468d2a30ba174e612852189122a84733cde434d2418b2e90ca60a640c4ba0ba6d33ce90866f108b20bf33234720e4657c8469f70337ceb202f91bc348ba6507247374e960932711f27545819d1a4da123fa4eeb07184893be42353760bacfb39e1a2671d80b7c458e299226919826fbf4398a63883289e3488a8d1647111a9b1d5827eba5b60a686a84591c449d463698299a06fb11b609b70121a830db191be4688b474831c5092272560932e7035c0dcedd035c647160bfc809f211ac1424d7495baf711a2071926c7560906389ba2cba58e154890ba116358de898586e9b5fa14cea2691a39829a7301464dd3a47338b053e0ce551ce2c9fe4d8d2378ea1063795453a6c6b1cc399fc37d0b358e64d74b050140c1422cda02866781a349965c752922c04341a52408eb03658e93993246d17236898e518a1344cb22c39a66165a251a2e45a04710c70fd36438ea38917051a24094e99146ef6090329c409363893245c141cc712666ad16e8a10d7419268790332cfe474da32c670738190674a1e4f0ba7f4686726c713ab441aed1198339f681b446d468e9398de0ce993aa2c69040c672fb2c8b15c7f3a44f68964398338e687b44e22ca7c19c9b0ce749468d1cc9f68a044588322e063a90350c159e09b108a0b7d311cc574685d408e31d11a990fd3394e4191d458ae74b3c29906234e226d1d7488d93891a9c834ca26eb0399d68d6f9d267a85b623473135231f687a465315319ce649a4632c9483246498ae4190f3adae2c90324cea7111b80a06289261fc4214c7f929166d9de1d4931fc8b1cc7938a841421a8b2ef1070b9aa3a3f9f61647f8e675cd50349e261fc9a0d4591ac5319c6f90705504514085926c7f22ca73491322ce219444d8e11cdaa147447516378a61e93e6f9c4eac1010c3b2f93e278393384f39b4419cca8b14ce23ec388a66f40cdf27c8b3a87122cd20f465418591ac4740a8c4589a3f9021a8469944d15428d3e458a36b88b6f88b499c440cdea7206468f22b8de3a9267f04d194d642dae134f246cae40a0da2997cbd41368948c7f37592469170836891303284f7678435fac9235b61129f888e71ac3294233da2fd2243591a2f9423a9feef1121cc4546212ef4a404375c0c73468673a8eb4dbfc890689d5fea11a4db445d2e5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_67 : Impossible 0x1000802005000000000000000000 0x4007fc000000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=27) (code:=0x22ea330c33a7e618df0d2142e9867582ec35be919b428d9e1c8be6f8ae298da55045b0c4309e61a7a458c2a321c730aedf2e9c43edce1be8f22cda0eac39190a39cc33dc8b9c42b1bcf61ecdf47c6f214f739455184711c88627db6fd0ba6d9fe6785321c832b8f63ac8608f759fe33868986e712561bad0317ce32b8e73ac7330975460e65718439037b9626619ce7b9c67d8733097422dce899ee71b75fa30c711b48313f3d87b23cdb1bdd64195c673d5be44c850f673845885d61a8b27db7ca311671449133ece339d1f0571a8a61ea5e338de928bf0d1f667913789b62b9ce7b8fb93a3e44cd11e833c4cff36bf40f8f6459fa7b8ce7ab7ceaa91be678432f9ce338da086cf3acea19c5f438e61d45f7ea74738be6781cd0b1c4ba26b3dfa3f4f637c7ba021eccf0e73db0c713dcdf21a6f91e37bacae11e43bacc20f471184759ca459ee6f449760a09e67a2c673dc459127d8be2b8cf37a8c338decb1465309e7e8a67b0aeeb1fa6db7cea0434350a3c8a6519064591e0866fa0c871c48f54bac6f886057338874d429034790645b747e9ec42de275a027b9f68c91e1f6e754881b75facf12b45ce323d0d40dba23dd614c37738219fa89a3c459d678a8c8b9cc399ed9e1cdbe7566c441c9060e85a519163949a218e6658f638905434a303d8f46528cf122dfa72cc44d07a51a241a8378f64a7b986459c4ea1ee8f3f40d51e8b1ec7e8e21ab7dba21cf70dd4590edf28c6e9be0b43d4b6220d46d9899622882a9072658de3390e479162222b9d47329c345e2431bacb348f2710ae7888a216f146d13688ca268f27ba1a4ad0319c8b35d271136ebdc47c7b0aa86df116438c31a45f10d13344f60be415185f1bca6391be32aa4104f19aa22918de713abf4659860e6531c47b17dbe1cdf69b66814c7222bf4f50f4374f11d4474593e228f2438e64db34834e8c337c7a8daa9394cb2744c5ee8f872738a36b91f3d8860f70d619b616dc640da20f737b0ce319cdb6fbf47e8f6238e62b90e7b93a65bbc35d466f9ee2b8ce8285a7a9c542f90691c4e3086eb66840caeeb3bd0938cd76e872bfcf7444f10f78da2278a1692a128c8a111dea758c326cb4d73ec2e8ea399ae7b85d1546f3da1244586175163c8ff42d130d0419d66f2a9e272a743e5ae2ba161348322c757aa1a4444d15dc67886f42b348582b975061c88e3d8ff3dd0942857619126b8e63ab74719ae1eccf7aa06759f62b8819c678c447d8b6f90ce2bbd59a1f2c31f3094ccc738cf522645bddba715187b3dcc31b5113e49b3bc36c242149a3a9361f6cf3e50d378715387338d0e4184d3dd091bcf6f50e67ba46729367899e9d22e729ea29a167194633a1221d4e0ba398a717424a77bb75962326d03dc65271ccda54bec2bc7cd71350b26c1ee7e46c8915d3743d1f135177c9276b8ce81a46789f60f641be4fb1cc2aa25034dc3422c831be0a8b84c4de2ea0c23a2c6bbac791d6163987920c69225369d0673dc8b20c699c83390b15cbe4383388e4d15cf6fb152f788a2e0ea9cc34868ca3aaa41ccea9b08690622791a47d9c5f2cd1ae4c50d8590d8b8ea414f6398890aa3486a830e4871cc6d088b5d127110b7b9ec4d9d5f221ca975b743990b445032147148c38be4759888ba4b09868f6ef6f8889be53116c328c7ba14eb033a1c5d268ae1252e8d23695cde0ae831bc85175056f86f95cf645aa45199a1745719ceb218763d8e328cb60ce219ba754583e4dd6b95c8719c471b47b6f84f45c6f8cd7595d867147b247b8f62b912438fb6f9c63988923ceb6d87b638ff3ecf7113548f68f35dca7787d9868a916c9086a91847d9423dcd73ecf9186a92b8c94483730b7cda0e62f9123d81ed0a6f95d338d87b1cd1b28e4efb146ff43c889bef10f14ccf63694e1bc8920c731ec4fcdf1da1c6fa4ee71ce8b54bac6f86d0396faa47328c3d92be4478eb4460a77a4a7d8fb23d9228d42324da53b961a073368f6fb3e5961ee63942a3236cb192678ae459b432cf97d9170d29c1b4a91b94e268d20e50d7ca2adf7a8d737c7b89a6591e6f8ce349b420b35404654288f45b3c428ba4594689146f91ee0f723974ae7d916448be188f7348527b04d06f97c57269ecdb12cf239c734591e438f7428aa37819e4e7d9ec14d0d1b50a4395c43b6ca71c4baa17e87333c7b06d4188aaaa591a4f61cc871ec451a5154466aa9045ccd277d8a3739c6378794d49e9336fa22659461ecdf93bec7ebfca79183c88a328dafd8a82bc055528461194f111434a8c28cdf37872852665190a3c66a4793e438f711266ff75c34789eec7023deefd32e260f222c56027d91b86be59ae105d519be729ba0ba72b3c1bdee7a9f239b745b0ce819f2679ba3aa8c5f0733bc4ebe4be1742775a2a3dcef42cf96eb7c1ccc3239ae638556f9272f9ec27a1a858ea339ba8f64873428c28885190e2733c5f2147b3dc639ee73933164f68187b6587b4299e9b23c1ec798698e308ce09afb2f99e7cb859a81) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_77 : Impossible 0x4000050001803000140000400000000000 0x10007fc001000000000000000000 :=
  checkChunk_sound (initRounds:=2) (rounds:=4) (fuel:=2) (code:=0x7f) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_78 : Impossible 0x50001803000140000000000000000 0x40000010007fc001000000400000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=6) (fuel:=11) (code:=0x37d36ed0ae1e3073ecf74c4c6378793991505) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_79 : Impossible 0x50001803000140000400000000000 0x40000010007fc001000000000000000000 :=
  checkChunk_sound (initRounds:=2) (rounds:=4) (fuel:=3) (code:=0xb6cf) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_83 : Impossible 0x410001803000104000000000000000 0x410007fc001040000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=8) (code:=0x43c9b28c3d235110ae2d8ef25) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_84 : Impossible 0x10001803000100000000000000000 0x4410007fc001044000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=14) (code:=0xc73a4733ed1139d091dc28c813dcda42ce7308b22e8ee32cf7379e6dd37c8b) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_85 : Impossible 0x10001803000104000000000000000 0x4410007fc001040000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=10) (code:=0x4b022bde2a1ce8d28c519dceb79b7465c9511) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_87 : Impossible 0x10001803000140000000000000000 0x410007fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=6) (fuel:=16) (code:=0x4f8c6419e63722c6f1cc43dde4f89698c5592914199e65d1ee358da3f9d6848fa3ad163b8de399e62eb74e3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_93 : Impossible 0x404001803000404000000000000000 0x110007fc001100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=14) (code:=0x85a7295c551d0c24388a87e310d4491151d22a4d339d7030aa77115819d6f3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_94 : Impossible 0x4001803000400000000000000000 0x4110007fc001104000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=15) (code:=0x8b15c5f0692163e7f38c37c0d5313f9c6e74049640b344d4e3738d28709922c673a4759a245867718aaff066b44e63393234bcd3a454e722cd145ce940480a3eeb214e53f9dc09671bdd9a395fe6d8db43a3c82819cc242c24e5345fe40c7f79819c7b7f8ff054553240dbe6b) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_95 : Impossible 0x4001803000404000000000000000 0x4110007fc001100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=14) (code:=0x11508ec544d184ceff03b9adfa9087fcd606848849fe61394f3519be75916e322a7ea3a419ca758658eecd3ade67f0ff9aa06db) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_99 : Impossible 0x40001803000040000000000000000 0x150007fc001500000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=18) (code:=0x409ea64bdca504d32dea529361fccb808c97198afb0eb325427aa1a3ac9f348a1438ba529bc1a59e4389a3aa2c4053671a3a7ab7c648136065b19c7343c7f114c9678819927a95c8736cff71916629491648b349427d14211d33c3d033dc5b3ad25285360ce508eb1338c8f1ad0e6f9924743c85325164c9285110f30d3e84d1654a0851137e02ed) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_100 : Impossible 0x8001803000000000000000000000 0x550007fc001540000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=21) (code:=0x24a1a49b3accd3290241a761af90d23e902849d6f10f91fd02e914279865418c6069335428b20c990a6799928720443a16e94ec148687ca070d414cb4187d439ce434f10c942c653361a20c9b689a4435365b20ae73f80967119d064d8ba318de438fa9d7483e4fac947a9444469414ca369960da6db44651e47106d334d283106e7529420a133a6c0db0332ce93e471528a536e0a1649973a0c1bc8375a2c34a1d3b0119a1920b3010598eba4d17398e834e88086a834389a0711a53acd21d16274e93e90b40542750ea083739fdd24ca226487f1d60226de6036a753580b24cb26c26d4a1a53a47be61a1333e596819ce8ca0c8114a8c9c41fccb39d0366a3c4ec2466a6e0a0fe8f50a4af707d1940dd331fd0607d349fc61478b616d0ea56490b21c8b23d1710ef31d6a1669d2e313220d02348ca3794a438418966745c877991626a52a0c81154670da871a47d11dce136f320c75073a0d4a20d323e606349964590e9d1f2279424d91647b360212c41be45f49c872848b23dc6445174cc5318cfb7bbd48281b4b68738c7f528ba0fea574a1a21252c0d111034d94a3346b1fc45959d63d917252068ea5ae93e8a53a83250e418ce969f4a0a5a84ba43690f0108a8b4e841c24cd42c8b14b050eb14d4a84a1620e07017390310e4183ebe51d818fe2031d79a74e71ec47ce9418229f51e44501087918ea4ec0df21f4e33cc791047121c8b2028f3d90773b35ea3346d23c87081a746d1fc83bac33c9c8b250da798e2818a24ea02f52066d9d542ed) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_101 : Impossible 0x2001803000000000000000000000 0x5d0007fc001540000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=23) (code:=0x6281a4d6c5195f2388ba20e798ce6982a2a41596065848df01648f34ca6c3253a4c90513a4c9fa3f5ce68b14e975a0c398eb26c3893679a1e419d6f919d8a4ca045086e405073a52511d1f1427c902418fd4cb14cf75a2a8b0fd474d14249b75a3c849d239c879133bc8b39dfa80a849b0d2eb38ce91ce811e4ba9686b0fe1faf338cf13bd0129880bccfd1113e5e61eb14d61ff01314b269344834e81045b7c9cec5344da8709d1bc44c3b298d6688758be35886fd3e58a274fe71a8414cce3f8867143868a74c71bd17418713151617d32750ca14261114651248332cea0cb3f914839d4ff21d136492520c654c820dc67dbf4ef10904d20cd2818b6f33bceb106e77ea648121e8e90f1c4d21d70f4c9034d90f45511475092130379be443e3a8aa5a738bae90fe75629f41e69b39c5f2647d19d02689fa8083e9c6990c57ea020fa9926de6202d11f5e2405f20e232bacf18f8fd719a4e90674cb9cfe07d40cae9d1fa299a2628d24c9e2939ce6701f606731d4654e89eeb0fa4c8ce9384e53268b14e942501739fc73b8d060c719cfa809a23a4d1314495f2789fa749f4b60fb0331c7f16ce31847373a750e07d39d1d33a030311f4190e3ebac75b3c8b8b280b8c0d26895c6d1ac65418ce2d8c6719fd1ea521e0fd011d4748da20e80bace931d2773a0c81a053a26817dd681b9cc727c6b4c881079628e2358da4e91d1550247dd3031fd36404c521d161b4eb26d03040a125b48e063f847d06e740dd6a54781fd8b271544391e8896c730672e83a96c3f23c83a268fc563a93c0c99a2c26df6938b6c71e6e921e8ea8281903749de41c24418fe638e6479167493351e12e705787824a94c5418577988b3abacfa15c398f20e30f3acea8727d0311d278f24ea2c3bceb3a9f44fa3d42ed) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_102 : Impossible 0x1803000000000000000000000 0x5f0007fc001540000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=29) (code:=0x40d06216a0c0dda43cfef33dc3b9d64380ea7796c75e67a8fa3ecf34b515102f74046520df225b035047f0ee998fef776a740f30143875419361dcfd7b8ca75a7c3aa8c7aa06314ff405d68f1f24d4ff144ee2ea0e8b11e3d49b79a024f87228a846289d20c62843c7cf54ea94a10ea52c14a379a2a1fc1170b27dea5094a4dc3c20d132b936859170310b3e9164fa8c898fa268e23d479264909b4750ef44c467d0f5438f666a8443c748e9dcfe3d44b1ec571dc75274874186b1e4714f8671dc5725aa09fe7a8598e86b38a1c7a8728389d294e63aa0e062166f1e46d1746b12c5727d46f37687707543877459431d0ee9f11d43b148f0ea4790e23e7791c041ea4191320d018e8e294a742eb14ea0ee0fd3f1dd069d0da3fa6d4a0ca831f4474fe26232bd5414658a9488d9fe02770837aa0262c1d32f311d1e58a14a771e4a1206899f50e388870ae3d8963cc04529642d9f51e474712849d1f51614aa09c46d21638a74991847d1ed060e29d4f88322c9f13c87053459dc124591c53a268f620e834c954a13a8909b44521c77134991e43b8e29d0e25d3fbb5d6d103d46d1f5a29d758454ea368e6d13e4a13f5058183eb34ce0d14f88199aa51d4e68a9d22786d339fa82a750607319cfa3b8e29d4088995c628c5668ca7ea0cff27c81111334fa4f90223e21a0c7d3f45d106d162bad321a24f23a2599a6727d1e3d4d12740fd4f8c269669ea758721a4771c5193d53b0513ef918a47a6438a0409685a059a23e8118459194d14e9fa830f91a50674a127e8b2218ba689f421841872cd12cff3f4d21c50e1fac50dce62268719cfa7545852c744ec4488a0c7d4c452a16f1078a0d275286726446c7321a95eb15028a0d3b0908d9b51d62c1422c993a884a64c62189d3991e0fa75a64a53a428be4691cd063443b8fa2ea64a179b34fe44c831f468a746688e8f1eca121c731050752185f3fc549f3f6660ea388c6cd07d29bd41f47566a0e163d4810d13d59a3e8d183c551d20af1898593a4a11f6128b20a3e9161c4a10877a9fe7da0e398628fd16264fed18e91e08f27bd51d41c0f23ec45ea83a52d14184f2751f1c45d1b44d184773ec8f2853eeb10608ebc50e8a8e67d03f338868a8ea834e875458758283391619d06996284553acd74866c15423148342ccd15d1e41d0b2853f037682ba0c6704d3e94a508ba38b34fd0a5688711b47d0fa6140d13418ba2a8e94f9421f4994150327d133a87539bb546264eb0fe7cc4531454132eb42d0344d8a23ce239a131908f8ca26fb0f33f9067c88347a6a1d53e81ba44447f1d5064e9138fa328d88f8b9f64cbd41fcd2a17b9152745293226506388d2314eaeb1d6328ba438399d4994ea2c19c99528a5438eb03106a303f88e6d1c461528f2414ca45a3e02e70fa40cf505376a0a4f8f305375a84691dcef3a876bd5131a4e2368fac5019dea711b5daa50ee1642948cf33d4774b5da40dce464fa889420c442cf575a85013a47d3aa750e20a31b9c21aeb3b54af326c629e67382066743d8a3f3bc33bfc55454f1769f4654c81d69d7aa0a7e9d4a31f44e9ce9926c27c51799365047b27ce775bb506c70e91cceb6287594ce243dda0cee73ac733e88298a8080b2694ec14651cceeeb0711423899c791949f73a0274b342024fb34878b23993e7119cbaed1ce75a0440dce3b8eb1dcd2399d41f2eb18a814e8ba40d093ac77768e96683e546e734525314373c4eb1dcea3adde7d458cd40c1a49d164ed1d58a40c59669fe32a2c6744c7f00f465899dd0328dd6338f94ad030629da758ebad09738eb779f4819ad3222cf91b5050aa0ca7dc049f22cd24c9023b40aa4c99e26c5465ce195d2cd11684838a4a89bb473a0469339d67d478e71fc3ac81a362983339cce7b9dcfa226759da149f4fe3b5de8090335a642b8fa7d8a3103769a251a12673c4fd02dc0d1319c05ce1038096ca32047f7587399c7718d0174a3c73528628f23e8b640bac509d2899fc768d24f9cd36cf0f31ad0207b902a36790681a3d4a4f8ea0f3528e2811f4d133c409fc4dc14c74e8669fc294e22487e319f467184c74143ddeaa0a5278a228c8fe82a0420c7d7b8f7276026781d46966bd43c9a27d0fa5d205013fa6466a7ca109699a2628d4a7fa027aa3dcecb2067c8ea4d4295de9a81fa2e06fd22681bb4fa8284959a829da8f2648b80832a3c22cca77154f71d542c907d335ea16d4a769f219d92325d61eb111147abb4f93ac75324fe011616cd3e4ed3d4ce7d1f25198a338ca3d4cf3fced3e4e71f2848e740d0f0cc293b59a6499c1fec53d59a359f276a8cfa7718a03d2d8aa248b31147ce73d4573dc4e51f769eec91924332cfa7b1ee3247a8149edda5b18aff3f4f93bbac1ddda739f28692b339fa0fae70d63ebb4590ee3c9cef50faf743425f133b9ee4c50f3e8b234a8273bcd9a21aa50cc6b42c7b104769ea7d6484d5e664bd4f9659fc7a94b014c81659a3c8c21dd8a7e8faa305f3b8f215876218821c8c2188a2318d6349967f0269ce818627b90279b143e9ea40954693259a670e73e9da20673bb4e9404f332c818fac93386699c4f7b8339f5f21ddd69d418c9080c24533ed924c9d6679013fc34528a6a94714a4ee1ed968186988b3481154f107733ce766ba43f83fa167f9d693b2449cd6f920cda324e228dce43d020ae258d317132ff132e766bd44c873a4ecf43d4a265067cbf47a8d2528a57f902679f23dcf11ee3fbd467649f4116121fd4a759210eb2ba06408c23f9f443e82a507152c059a0eb1fdea7d64bb44acf54c9113a5023b8e23d94a0ee571ed1740dda1db033dc265ee81a0d3345dce1f3271dc693c421c2ce767b151e06b348e29489a30a2a9a98a7387b768aacd508ed18a115db091744d18a769253a5ff0f18aeb39d0100fd8a7d265da314e9409113487d7f8ca3141117ac853a329463f8d27eb9d060baed80b34071818ee508d3016682dbb4653e8408f634995eac90f51c5468188a1dacd1fc773bcf93c447324833e8c5324cd349d5161f41723c7540431622206509f4551b49d7687d185ce3a99cf30ed3cd3a7f0f68190342c7b76906eb0c5275423e9013aa2c1ea75334fa3e5151d43a942ed4e8eb478308b29d52b250ee3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_105 : Impossible 0x1803000040000000000000000 0x550007fc001500000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=23) (code:=0x2d8e2e321e41a3280a3a2e98ef10ea929964d9d66786b0b51d3c44ca94fb0329a471104454d8419643515d3b3ac391ec8f52b7c6d94ae71d638b3e03050eb284a5679bf0d0733bd033cce731cdf1b68719eeb19e9f404358ee7520c710e6818283f93443db6f11e4754d43aa1e75a063f8df051f491a2e1e4fa37c341fd016db7d4a1f5c6e9041e3a87cadb6719fe15cc741840d9eeb0cee321c570867b6483db7ccf13ef70d67f15c6711337e128e83ac4d0927d031acef38cf36da1c39ceb679be6d9f420675a83078ea567d91d4f9de73508a10e4cf05d8e93a358c68493e1645d1351d1c49918dbe0b250bad9e9b3fce3142168ea0baa13d88a389fe2093d1ca1c1dcea43d093acae3188a35a3a3c90f23d2b31ccf38a163da96021ad0f0f6929f443cf60f750a6ca523c22c7e3d9f45575b3c811461a0e287a949b3bd0122c87b8c9f052a0cfb3cc4d1d49f879163990e80820e1e81d04e722ca109b87b3c9f84b6c3ed016db1dd2ed07d769ce389061fd034d85350815cfa829329d0e67f4d43ea3c7b9323fb8c4e8e23e91edf13a9f26d960d67f3ad033ec714b4778993f8d623dee15cf633857818e27d0ae552841f47b2ba5e870a63e9a48b64bd408098dd63fa6c6739c759cdda408ed4f8ea43c671d42b9e61117999cc718cfb20d010862ba3b034d843a7d013bc832827d1c612738838eb1d15c8323c4399f013cdd6ed6d8eb348ed1f4693ac7526483719eac5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_107 : Impossible 0x1803000400000000000000000 0x150007fc001100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=24) (code:=0x3dd051b6689ee3a475679e6fd0a101ad8f1d339e70368bb479916249fa1dd9e1ddee51b941e65090673688d1678fe4286da850107550a063bba60a2840ac9f1d4ee8591e418be6db45053dc19473689d22fb3ce738dfa1fc8f20c7715c410fe7388b3b91e39b3c2fb8cfb3ddca4945f394750861e93e72885394d1398473aa843b8c272a0c8f76bac1cdca479063e53549461658833950122c7f274ee0c283738770fe929f6889fe458eee522e848ee889167db8c445eef328a819e682a8edf1ee819ce41916398ea3b92d7fba4ca20c739d29d3f4359d67fa4a82c04e50418fee7479e61a8e62f8799fceb3ece540cee17cea1dcd6ed68833984570c2413dce33cc1daa32f8df38c1ab9c96414617284b798f319cca7f27c1a5c6749da82867359d6728ae3cc35454e5194fe77024a7439339d6551ee274e9799d64fa02222799fdca274e5769cd42cd0cb3c8f6428fe738ba0cd769fceb3b8338dc733dc39a2ecb28c7691ee71ee768a63fa367706776bfd033ac20ccedf26812ce5348da769fc729da1b98e394c2368d23cce5444ed3f8f66b18e1e70f3ac734e82ea74ed3f99e1da9d1e628934739fd010fe691b4ce26acf3b5ca77082858673599672a2284a0a3cccb1dce73686b36ce734a0da21ace31fcdf3ac3f9c67fa2e39b34fd1fe63c3432cce35a068089a278cb274e624867408833fba43cdd27706f9d6638d70d799b6738df3ac79a0a80b9cdb3fb44808cb1ddd2309b6cf32a940ed130611a5ca4e8fe35a13010eb1ace63f8be14ceaed0fee30df3586117c202373ccc2399adda37c5f3f8819be3f9adc6cd508185c63d9b6a1478ed22ce33b836cff35ba5131dd8e3b45f868db4185f2741fa0c299da1a9d4791b501052904cd1141288a61175da6f9ca3b46737cf3395423a9ac508ce8f1e6159061e6369d255175013bcff1e6639ace6288f2729160d4ea770d669035285e62f9fda287020d4633b8c7f6588ab9c71bcc834d4eb3e4df0fe20441984419a9fee90ce74c959a474f94348a822c54fe7fa5292887cc4e94a51971b35ca142e5454339fa35bfc3f8c3091cea56d8a5688eb394db014984e30cf1f6689a43ceb6d80f315358c2cd135d220e1a1884d17c4104d21c57799d6e568c0c7594a3f8424c21fa0c4d3fdd2e70338c4491cc4d3f84d35873778ba1ccbe113799d7113e4c2a107f339ca79855395a243855639ddda024c744d52a1230ba4f936ce3057719f23e5cecd23a68929434d1818959d292915423bbb43991917c7fc942bbbceb44c8a1da3097c135fe671da57508818e6759463f9db1326276c1cfd3e4ef7381351617cdcd23f4d1435960f4eee567817dca871d6879130e63b8ceff3bdca73b3cc737c71b2c115d633996839f66d9ce77a16d11357e9d61dc72a3aff39c9210a2ae9062898ee20d35749a22f8d2cd068a84eb26906778aa0432699c9214cef44ca1308a12fbb4ea7d) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_109 : Impossible 0x1803000100000000000000000 0x110007fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=25) (code:=0x8793e9d36cdf0eedd1be1fd1737dd27ba062d86f33c5b3447f628f310c8537ccb6ea6c3798a74a02388d63f9a23ac9b6e880a75be871426ea8c3d9f6e501fc94e74053a0ef0f28d8a2a8f64a5ca41816e0e1e8ba3c8e2eb0ae2188527c3ad034fc1cc6c71036ebdc3acf73c8aee502ca146d42cc6df0dd2d9bef3037798862b8da509fc495be0b65927cf7318df7985b7289a3f9bc7b875914dd31cdf1fd0a7b20d3606b12c8a9f4045942477035229ce16c471753e2c8818b6719036e9a2285be2491481954d6206dd28525378f331cee9d1e6638ee738fe7186dbcce350b14830aa3fb950e10116536853143f1ecdd12ca30aef339815e270f28c5f1ec4d2843fa146322c770fe77964e70ef136061a24d17c851ce198dedd10aef314b2519421fca1344c5092dd3dcdf1fec71ec7328de6451be47947250f344cfe759be778f616d463b9ce2261dec53c8f61e8ff358bf2922942e53ebb41ac476d9be738f340ccb1cc8322c4db7c81badd20876dc142d84396c772a8e7257690f868610733adce24954631346b1c411e8f96c6b8194608e4d8e635915e6419b5ba0b7033ac8706126c6f2d8ee73bcc631d6e322c6e936730458922abad3a4da0d8a05b32d36dd3287698a6796c8b28c12cb612cee154e6114de3d8dd518caf33e84dbacf71da731fc8b2221e647c0cdf1542d9cc5f22e3a5199e3d840e3a3dbfccf3b8374332d91631a3dce3dd967d72a0439c965199e39cf66f9c66e98e8193e40ce9418729fce33ec9d31cee1ce3b8aa7b88a4b1da68b941b984c708e1a88a268ca2022ab45051850643445404dd3ddca67bace60da5f0c446c467f0c2a11ac3743f394db229063c8da1a8830c4db3946b0bca1454aa7301f955a27703cdda9290655689fa8a8e720dbac718e6d8dd3b436bae0a72b7d0e3b51537ca30cb38dba10edd36ccb8a87f32bcc40cd1374db444e3114be3b90715c17ce6e71ec7f0c6a144477758e73ace31dcff40d0e659bee53ea342845b1de266da061b8de638d131d1a718863b506518e7344ed1ec8f9a23d95c2297c414ed1551d68a848f9fea31bce61cceb0fd0b455508ed72a0a818431cc3546b44759bce3439163b4871da7b38cdb1cc4d174c7154114570d4493990e358ee8d111839c6a319ec522cfa404a16f91d428229f59675) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_117 : Impossible 0x200050802140008000000000000000 0x10017fd001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=13) (code:=0x22cfa3b8c617d028589a32ba4929d224ae542ced4150280a8c0d222902c722ccedf0e6318ce04d74a04631f5ca0aa6f19c633958e20449164ee85) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_118 : Impossible 0x50802140000000000000000000 0x2010017fd001008000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=14) (code:=0x3a45f454f738c1132f9bd16838749265f41d023a4ee3a50b0b39449ce941c856388b215ee7198c2147d639e61247331c513b45b35ce5215029b0e53b5463b9213dca34647d43c93214e574936cf) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_119 : Impossible 0x50802140008000000000000000 0x2010017fd001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=16) (code:=0x41ce518c810d23a5013ed07518349644522c8133b7c728358be8126c430ecce41daa3e8813bbcc6abdc395da6f886850ca339aae320e749ee7d892c0d0acf) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_123 : Impossible 0x140802050000000000000000000 0x10117fd101000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=23) (code:=0x2fa0e1f25393e49b15d2ff1fc040cae5f3ac54931078e9fe830bea32329f76b2c81946f130c31c85c0cff2f820e639989f51926496060ab1941c55da0fa7f41c751e49f28dea1fc8b28c8378824cb617d15314ff032269cb1c8f8ae538fa4085f498d71b10645a7c27d198aa8df2e70888e2408f23fb14be1d47111d62a221fe3e794b5f221a818fef93c4f528d0b73a6a03fc3e6a85c1ddaf320e629ce0bee7459267c8f920e1e63b5c474750dcc72f9ea938419c50f0715189afb106378eb0304b818463a9067f026a0435888de6b8eb0b1ea0a4631c4ea42dae937c85722e3aa3e7f1270b48de6df03d49a550c62f99d3e6280dc572fc2c4099c5d10c2230b15dce750e719e163b4ae63033c3cff31d1d818f9738c6c5418b620415c67819ea2e8628318c7517c3382699ce78e8ea1ce5d6ba2c259e45b38879c0cc73b4e718c18e223c8ba18cf1738de76a0c8104b164ba713f85930cf90eae70551c4c5819ce833d49f53bac4598e819fe49cf53fc8b28d030e30f27dda0b26bbd47531511102135789d443d1f98a42f54442fa04fe10f7acb494c343d4958af30e72ea6a8fa2a888a679a1aff23e7aa4a419ae8e8ea0be2b9fcff1f5e6ed06a9f7588d9f6388eae9062c0c9344cbe51b9cf142c17cfa26902106811f45962888c34fe38bac8fa1662b5c0d44750249a7287a6a8fb14f278a5a12ce2f37c9dc1d27396ce23187a6582cbb4eb1c439cb633bc492a5af33a4ee2a98a1d633954c509ae932c15c67758672044f0c4c53a5ce28dae174673b8e7659c47510b1c5f2df418711dd260c789986818bae73a41c507739d2750e28343c42de2216f13a5ce888a21d227c3d2140ddaf3079902773a877174e2eb0717c9f679902df3fa9420d4328d1388902618418e2e77fa5607f1d6230b456060e23f9cea51bf397c8ff78892a4eff1fcf13d47148dd60faff0f53c4faeb22cf94f88689a6b0967d0d459075cd4f186a268b85988a72750ce498ee3f81654b115047526aeb19cf1496167179b7439c2731c572c9d2538739f2833587e0eb3d4b25f154ce1f275906c5116313886b3c8228866b3ac791d4f911cfe1da6b0751e5da7f37c716582ea3aff23eed4d51103f8d4792e8ae299112c862f52066b9e67584458a590a4f506a7f40c79114bef93b8eb1fc0c72cc6d03279d61e7393f831218d67519c222eb3a9c43f94525115ba8d) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_124 : Impossible 0x40802040000000000000000000 0x11117fd111000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=26) (code:=0x174872347685921cb68691a114fea51e63491a98bac3887319c8594e29c531251a12d262f9c61e07329d1a71758b612cfef90eb33c5d355064991118c445013dcfb2c8fa67b5440c833d4b23ebe5363549b0a57999667bc5013e4fe1be3097ca51fc773accf29d013e51a165fe1f230a358ae506a965da7f9e63f88d38a023cd8a0ed46a6c6f1fc5b1a48583883031419263e9f69b1fcc518a8d0c5499366ba02419c5f214c693fcf331471136208e279a35d6c70fa1d6c74194e659f217c6b104731dd1a9f21a719ba1f4889c70f174dd24aeb62877404dd0e4fe3e47ba0617cc31868ba42dd23ed742df25b07b986dd7c9fd0f23eeb3883f9368692ae735c2ca0e0b2348e637c44ed26d2a0ce738eb113b4e2cf12a678629dc9f26cf2348e2eb08b42616629d6798fe4d986348e2dd2226b071425baa5428256227d1ac773ac6ebe4690eea503eb759e7d9d687a027298c7389cb9cd73b46f679d6528a56e852b5ccf24c6939df27122e808d63b94a7c8cf4a4f91ddba7f518ed07f51b9cc327c712167fa527b9e6dd65883395030f2496062cc2c9f0ee8d206710774748a1dcc51c6161bd361c4fe4fbcc1ca777da1281a1645872a345531c81a0ec5338c7658eb474e23d51127d0d46c418d63fb1ceb40c6282a98a638dc691e6223f88a94941444553e99c63936cb0de639c5e65f11a81881c2dd640d96099bde1b0b39419d8ec5948399fe96a3e4fbac398b633c0cf71fca379b74399be3f98a998968e2c548509818f34750922c40df6849166723a711f453e22df8aa8221af746d0717cff019cfb4f1246128c85819337f8c58dc45096eb9c858b2079d358a419f4593ec8d8b646840cf5a09f4fb206df8592f3f97cce2681251a63045a347d628ea5f1345507f0c52162b74e21ea7d155153ed1740546f918e818fa389ce0c73b90681bd5251fc929146389471468413cbb44947d3493e8ba0e7b9f61dc8318d170ce7aa8c850a399a1f11858fb3f84196485395361cc8b19c6126d1a3888d9ba7d45c6342d073dca08faa318a930c51c4522489a832363ea6c19d1b3ad1538bedf227cf926ddacf06e8825b43c5f32c291344f11c533b829bc4dd03bb74b26f0b229518a3759be19c3e5be3ba12dd3c4299962698d060d2a319676a128199ceb17cdf1251a3990b3950d1ce3790a4d2065f37cfe0cb43c0c8318c533ac429cc359fcf91bd362170124aed37c125da8d48485bc4a0b9c1dcfb39ceb3de7a485417687720e2a8ebe4e21f2f34748314c730484eb43d1d469ddf2379066762a95d281) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_125 : Impossible 0x40802050000000000000000000 0x11117fd101000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=25) (code:=0x294d581b8c63a0a90b9c40c596aa0a8ab7c639263bb5c76a4a73919414ed4f8ee7d18e810ee0aa338fa28c84f716c51a048b4f9be3f8cf38c51204f337e06f50a3718a27ba064599e63b14408b22e98a9086b0d03ba7d462da2e8690d10303295ce6f9ae3f92941c63a724fb9cc53fc597b89f40d41445eadd0f3868b23fc9e8fef31a5ba3162a3cdd643c338b6348de31a151b1ac7917c833dceb4f8772326ea145f1e4759d58e0fe91b14dd154831d4f54683d0c7468833f9268598a23428c85339069f1e67f8384693e831fdd61d4c5234f31fcee4120e339d6cf0cb39e3218a96423fc9f0c73ad064298c5f1aa3390a5509f908b213e9197ccf3ad06c509098e88a2a833a8d23c8a335a34c24444f10a670cee70dec740c3ddd663a42630de5f0ed4f8ce8d1cec50ea7f0ea86a2a3fdd6818ff6e9ae28cc5309dd161063fa6233c643d1e48d1463f94add24a79a42eb051a7649c759e2f9ce81855339063fdba4650b6b9d68b11a6b8799fc8d22d0f41d2318c792f846a42f375841bfdbac7388134be790f4590eeeb0e2cf37416c633c89a6b8de2ca420ea79374818c2594844d2f853678531645d0f44d4185f425213ac3d22ce23744533cfa0cea52a90333d3f0b038b3e4219c4d20679c44fb13ecf3de5a0f311dce8593f116e8f340dd63ae3a528831037397ccf294f2c540ba445842cc6dd3a94e268e709a319d62396cdf124433e8f20ea63b74629a4419547946837cc5319f46943479444dd06b1546f3d4633e8f2268b22d8ce6aa7c06cce8b288318d63b88e37c64791ae22ae935c4f8ee8291675b9d06c51d419ca33b8a320dae538d679b74418aa1f8d28d30851cacd70fadf0a56eba41f4df7a9d68594a3dca36e84d165d2631ee2d9263ba421f4fb6384189a2f9e52131dd21e70324e09af31642d3b9265b31dba3cdae17c671ae0b64d3c9dc637584d19d16c505b8592637d0b33dea7484199c6f628eb1f4a2550372c89609a79749033ddba1bac33387994ae704d3cba43cc5962a1684a4e1e89add28cee2a9fd02236529ee62b7412cdf24d1341c3ceb12f3a58a46a6a85bcc3a526d704724c828a283738eb6ba0e09e168b651415ea7487a09316c7a7531451134c76ea046f84b4e521268be1f9263a4df348e92d869464c53a49304b3aa266a98a8e96dee4548fbd4e9314499a4628fe3397dce47cc5638c53a53175890934e712c5f18a6ec4c89bdc7bbadae8b2368e9d67b896769aa18c4b5441ea2a8d9d6750946904b679eed51218c8f2a574831a824744d17cf252ba47da56e74158a102eb7a8933d4a39c86724cc73ed133ac529d2a3315ae1d4f74c4c507f3390689a3651cac51b5dba1260d9ce5f23e7bbac859eed711b51b75e67738be4529263fa620ce38a9475165d242812cfecf3b505354f33e8d53adea1fd0b3fca312538bcdba067389d3252150542ca50c33f946418ea3dd1179b751d18685bd47987a35a4e858258c6359d4852c84d4185919caa39c37503338aa7b9e6828f375c2cfb0d4083fb54d710f6a9d66b9467107f739af0d0773f8e24d50711f53e6a86a869ca52f3528776b8c6dd7c84f40c67a06e91fc43475679dc25659719aa355f6096757493940e0e17d076b9d6710d76a9d67bbe43dd9e61885b3e1a1c47f8b90728df2758f96bb75160aa67a0c77106eb029c6375a14de3a8d23b8d62f8f27b853c3463464ce7d0be2399e75ba4215464583a88a9a9f48322d173dcf931b753ef1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_127 : Impossible 0x40802140000000000000000000 0x10117fd001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=24) (code:=0x1da659ce828d64501fe32ed6f9f673a34f31cc439a41fc6b819ce631bca301654e871cd1a3eb442ca3a6f94638986748819fe0218a7328c716ba2c0fe8d22dbe749ae79b1c0dea71cd0b18c876a98621e948f2d576a544644f2045965824ca5e6103010f54688d4550222a164aa02f322c10288a03291e60619c714abb47ab45be081628e217487468714a8339468d42da2f304a9c54642dbeed1da79bc5ae4654d4940e4ed3f8e618cca3ba343f91a8886631a4a9c9fe6289a811e421a91bcd8a6972881b9444cd17691acb35c40a124a88d445ca95a0686a0af301fe06e56f8811fde6424e219d2a3951631c1dce3ec2ca2e90bb483bd432d0376b9432e0612b2b18f1542dbe9088a34863916839a44d8fe790e6617289531de7010fe0e47d1a5168788b1cca74a8baf16a8f307d94e7f11a7111a771bc7d908ba18b1d0b3b42350b6b8ce919237f869889da8b1e651a062e8279ae731fcf311477468f2d111691c347687f03731cba3888d76d0de61260231c7f154ce31dae40cf385a041c8c20e68d1e47f445aa409337f8ff34b95d25f212949460e6d1469ee4a4445ea4a509405e68122c954d50b1ead16fa3211d8a8ca4aa8cdf32c1c5094349541de6f57388d3d52143519718e717c59215273fc6fa62049329fc814cc79b8c8584911688e68d1231cde642b1446c043598a8ac65ca20ef5214428e22fa2a908728b1ce85883c053181a4294a5420e49519be65a0242a3a73b95251be6b996254df073468fa3f8852487d4ab960e90a2b19032cfe498a92a7aa4a12a739ca6ba8e32d176895464f531c40dce9cb944283fa32ed3d4e33dd160fe59215ca1bd2b016a83fb94c33fc849be72bcc63a0272a6a254e70a63187e45b962225701395ab073494482a0276818c8d88bb5ca4aa1a18c5d2224da05193ca42948951a4592148d435050fe8c9867fa0a34c3c458d3011da46a0ad7041e6251769fe40b95461daa4a3294a1b0141476a2ce735cc7345be37d0d26d2140c31dbf01314f1037a6c731dcc71fd02790ceed2022a8e276a543d4ba928920ce7f768f546b4426e22e579892a021e9a28124a8d08142c0c408bee50ee1fc4d28c7d17437a6c8e9c43fa165f408839462e8c240b451af374bac4092a868ba1dc95878958e8671fe0e424511ce817283fb951a22dae3c42c8789ce33c14951bcd22f9c4f539405cce3888e379f411972a727aa5692a0f05459fc8510543cce1cf35135ca6ba042051d35dce7f8be71a3418d2a1fc71408ba429ae175163942946bb54607f789c676883bc4ed459eb030f28c86722ca37886724dea950e24ab5c01f9e469a4bdc3fc0e268d9c646b95aa20485a3b0d3ad0f3543f91a7f90a6a9ee4d902e53b5d2cf) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_133 : Impossible 0x8100802010200000000000000000 0x10417fd041000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=6) (fuel:=11) (code:=0x1068d37439dba3f4954048370a242f91af52166e8f17aa4675027a0d013c5123c91ad708db9c691e5c278817e16fd12a793d4756b9ba93) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_134 : Impossible 0x8000802000200000000000000000 0x11417fd051000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=18) (code:=0x3c448c7383a22e5464fd43417cc783a1a39c550b1473999c092e53ed0b4994642c0442a2a2a9ee8583ebe4f74040d2537c9f6809151bcf30b49a2e768fb0fd859f68cbe47d4ad0f485177190f15636d7216428f291a1e42de286a067b9c62a8d210b195f2d740512c307e9947b3e48d216026b9c6f51de859263f9f208782a16c33850940ceb7e9233b4e3224f91fc5f7283eb0cfb48cdb395aa18671a1c5509e3e8aa89428790473dcc62ca14511b45d10b28cc62e9ee5517c08def03090a146f17dae639ca691ca2aa2a398be1da711cc69080c5ce2378d2154fb7897dae298fa0be6d1ba2a8b2853b43f16c4914d0e16d1527a4c3b467318f6349e22d85f3c8ba17cef4383ca2b0b3ec7b1a52370a9c0db053bc71374e534926439d52ac9) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_135 : Impossible 0x8000802010200000000000000000 0x11417fd041000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=14) (code:=0x2ab8df2d719d0130c2792a2f9e449bc444a143e5ae2cbd4709fc4a8779ee6d1e4f13f46e9fd863f5ae10b3c52a1b5ba5f49842dae638b627a4cc31e5c2284950c63aa250ac9) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_139 : Impossible 0x40000802000040000000000000000 0x90417fd041200000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=12) (fuel:=22) (code:=0x1f4c73dc3ce127da024347d3c8ef8ca5a0898e70d53a62f33dc53c04fd63863bec879ee778a7089d5cc67d1ac731744c54eed63a062f20d0178a24475127f98e8b9c6619b679b743ec4d1751211789c647f1dc6b1faa0a62dd226f53bc77bedee3dc1f4da8ab849b3bced125399de057109cdda2c9361cc517da252a1c25907f6187a90a22789c2893f444b7434a62889264748e9128dbed19455094941e44398a928c8ae1dc7344bb43dcfb3b6628cb0dc271a5546c90fa0c6f10ef2c9e27d424d71de7bb74fd405123747b9f6349fcf13f59240ba4409ae7691127d1d02e9dcc237a243d926738a2791079d9a40b693839f5c21bac30f71ec791bcfb134ed3cc2d1b469619441f6691ec771be3a7687d8573dd11619dc73186690ee6d4487ba0e4994483a3228bb50d1a4f2e10ba3848934bc42b8d3010378d2938e9f546c50d620e40b6c1e54e76a22398a234b84478e6a321cc3628e96aa347d8f2839d21f6f13dcef26c35cf146513319f4f33f43e9e683a1ae144879a9422a898e6e179a0a889fb190de4444f398ea3ccee385fa8936c398defb3a54e1fd133843d0b444c51529c2fd808398de0df0d28a3636b848d0922ac44889c289628a53fc1fc3744e3afb185173852523a9b87ebed13355113cd1714cff3d4953991b77913475c21e66aa3a7316c8e9d6779fd1b19c529de6b0ae6127c533ebdd923ecc50c53ac89318a64088a84a2a67875a662b9350d11467b54c73791ae103b4a657289d6799fe14c290e51a15cea3d87b3787f44c35225414bc758f73d4ff3ad8a3a9bc3d87b0dc293f8d64a89e3b83bbdd0f2ba2eed0ea2894d9265809a278bced448dc771ac7f324531ec6f6a9cc0eefb44a326b9f546a1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_140 : Impossible 0x200000802000000000000000000000 0x490417fd041240000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=24) (code:=0x47e028e91a73030c34fe448869fc9578bcd110953fce14763e7a91a20e3c8ec3b64a7144c08196bc5353b48c9e5a286a3a82a2a4351570a54389120d2389fe7c86929d033e4f2d114ee11a26184a35e623e799f2d70f61ed1908a338f67976b447f7eb140f939b5c75438539ea7e9fc790d17e9e2258e21846948c430a61e8c2258fd21a3a398fd384f9389e50e17479408711e4db344fe1bcda096d11cc7146b15e644a84154fd8a8a119d011c47742c389c30744442dce76bcc7d52a361d49b89ef34e4834685f09f2a8eaa718c711dc4f86a7994240420bb4ea9520c7d3c9152067c91f76a2ad1424e72467c9da79a0a469422370142523142f37e98444dfa3f447cf93b5fad14b4ea39ced3f41fdfa83a36db808fd09e8d9fa771edae434fd07f2f9dc689a50621689a473146c551f43fa84f939de60e7809ae8fbf41fb1f3b9ceed4d48d3085739d1d41dc225ae13ccdb1da85a3e1073b3b52d708f96d8fa772267996c4aa861223ef93443f4bc7f90b47d2f434ce3fc7e73bf44bdb707085cdd2f68a02f31f309819e58a990ee3c8790a136dfa06d8588a8e9a2a11fa7d4c90e7d9fc508faf71328e91f41d0128480b6cd73edfa89528ed485153cc7103ca06f376a222ea2481a65094ab24818db0fd81a3a79414f3384610d13cd030ce3ac84f241a2a8d0d273628f3509e264ba43d8fe3b8339fb11224771151b4aa7f13ef14c8571bc831e28a99c0aa4f7e8ce41b5c43cd77a89aa1019cee7d1e5da611112a8ed3b906894aa121da7f103225063d8da09e4d114fe1e50135cc33cdeafd0185da6735dfaa1468811c4592643891e40a3677a1e6b86741bc45508373c24308e641a3420e168a86920c405e241bd5151dcda4347d1b469308670770ecce258461dde66d154834c9011b483469fc1c50d05d0ecf31de1b09444c241a3a892060fa92a64833f9ae308633cc409323f91f4799c4378a7eed529032542026d1e4757c8495f277c9de2255daa13f4a51da19d0d4b5037ea64e9041bc4e21b47d20d2713cd2063388d2673ccee0a2790720aa52be433bb4c2454833b4673c9dc0ef2d8d8aa6199e8e8789b51d079474e693bf5f2694a82abb4691b45d0849747d40d21454ed30a95121dd230f291c750f4e47f0da17c794a8e63f87743d12ed5086923ef9504418df271f48ed1ca141c8ea0eed0ce3f4572550140d9e0ee2b8ca2ac750d0defd7c883a4e3ebf5da47c9540de6794c92340c8588f1ec7320c30a061a65239a8e8f99d1d9b8f91854240e0f093b51ad10f14a942e31de4c820c720af1508a41c246f3c85d19cd224a8378a552d0957b86e248da89106590ba76a1a37a5a3b45d8489e248b23ea6444bccee0258df1d175de404f38683bc75f31504b4489e3385d2347f23c771de890bad18a9b412b0f869f237bc542e11f21e28a9fa51174a54a88f9f2a53f4d2848424cf31a5447de6689097c8309f69520c553444f4654a77448697a88aa13230757e8791dc734a87c9d51eed0f278975422840c71f7ca3a9aa0a769eb09468f51a23d9ea50bf450c24610c27987694a9da5e617c9ea689dd32d76286d10cf73b436b8ccf3c41fcda45446c837a8c54ec533b9b54a76b440771687a2e8f6d17e89a3a81a45d7eb44c338521368d1475da891fa790aa4182ea0cee1e9424494a3ecda990c26887f1e4c32942e8fe529dc891843b8466d1d53207744bf5424de13032049f08981815caa71264f33b87b508a1708573b50b1f27b91f484808554062ac56882b97cf9405c63ecd1709dc2bc4426bd4693c8678da4d1dc344623a8d2710f52659f0b24a8a9eae308fbe4d221698a3683a06d196b1443ce342d273ba0e8fbb444a22e1788c5042c5a38cb5a2709c66d3b434a84f584a5592a302a87a891f47519dfa0ead119c83165110693f4e76288d9e27ec04c95298433a0e8d9fa1f592848d26d4c84cb14a54683eb24c50d13b4ea648fa408ce2c90e069449c2889faf11b4d13252a3451a739ece93987f3d41da772f8ed3e9c2739126d194950d142ce11991e869270ff031c4ef0ed19c9a19cee8e9ead121ad7789c67b8aa1dc7b35dfaa503f9dc0ee6d294fe44c0c7b20d32478aa47ce31d5094ab24192950f3528ef709fa3a8fd64a2444ba4789f4ee2688484199c4dd9309819ee76a827087fc25de9a9dc4d4c90946b1546dd) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_141 : Impossible 0x802000008000000000000000 0x2490417fd041240000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=28) (code:=0x186449fa0f2893b8b2368511ac8903a47a790d4891f44d528ea770fa6d16532d5095912849de6152b740c62b9dce73754a059134f2f51322c9067725a469a480a4dde225fae1084a3c808ae749ba1bb097c98677134e152b24678ee3e44d0f473234ed3f5c2154ef3e8c2a114a811ea3ea2a89a0e7c9e632d351dc24cda87906f56a9ce768448777c8c27d8ce79b84e91de748770fb7c8a231896269de7d185324191e2063bbbce73cd12d504cbdcf919c7138c753bceedd11d354e73e9da1a47a41dba268c63549925a769ce8998af30ed1ac714c9ce34a1e4b0d28336883134634481ea247723c3e8be258dd1f50d4498a7691ef32130f30873a6471374ed0d21acd53d41db9c694c9066d0993e98c0be330ed32349dc38984ced1528f540c8684c9b5251e51f3e48ba5a84a3e1b64e269ee1b4891c5f2e308ae93b8425f68f9b4893a5a267a94ed385920da118ee2691240419ceef3424f90eeef216f76e9c6a532ce1325020de77b843d4ef6a9f46a9d48150bc42c9ba081bcc9b769de78912d50e2dd3e9d21de799ba229f5c2206369643c5f276a3a3d849bc4793e82ac0c45636819ce9319cdad5021a03033bd1319cdadd08fc04f93b62a1f5fae16882f9aa38a72939e47c9d2889a2278db3a45b13c93344e71ecf21ce83309093dce76ea6c2248318cf32e81c47d84be45f1e72d404e71ecf2e162846c9e539368ac0430c247e83cbf6021883a710c51e60207181c25214551324c629dde607112c7718e12d53e5dadb2068c9266d2024d1e61447940d1d6a9f40fb4c65af347cfd10c8e188899e649cc4313bcfaf1073cc444caa494e7309f6f121a81c04115ce796a87a89132813d4425aa3ca5a7e9ce093629e47a409123148910d1cdaa1e8868b7133153225b9c3dc44308da388ca21237b54e74549946c5162a4c3f5aaf5799011f43ccf2c518c9b33b841c5f2909ce750fb24ce23e9121fa3ebed0342cf724c3ce5a7e8d58e9270113244c35e2174fd1946d2647d4850d11240cfb808fa49c9c499f7317786d9e4216f136cfa23a1a9319cfb1edea42c730714c9dc2661a4d0673b9f46d3d41ee7d4c9b6329e69370b24768ba1e88e8e23e8c236bc5924247707d3142f0ee12711d40aa7d8c23ebc50d6a9da6487a8979873992f126c6d3d86d338e7404738ea768ce38c0c6324c319ce7d32419d131dc231f49349dce648d54fdf640d07495013ed0d1dc9339c134e796a52809271379bc532d10e126c9340d924249b1ac5f39c264be3d484f91097c9de859031cdeec90f74c9d4738823199cc2206838923ea6440d014c9aadb2247b3bde2dd528309c2538f2d14540eca703b1b5ce4994e41b461218a61224d11d4f2d50219265d19cf2e90893143119c4d529ec38512fd1e606119c59849ce41b1492bf46d70a2a9932d1a3143c4ce44de662a6511234f542493915264da8284d789ea7eb840bef349d137e93670b6c1549321cf57e9c2369c4cb0e1338227157c8ec7d3451921cf5798e14489e44c7d17c388e612c490d2454692aa95320d638c550e1bc9944bcc899648e9d5e28080338ecbe3d4c91a44a8a9390efd1d4c21a49905f1553268a6c33a1c13225bcdfa0be1c89e31a64671ac7aa505b21c5f10de6318967d1c22ca24f2d50839e23ea6e3a799c2468c284ba407380c25e61c40bef33dcef4c9b5c268877955aa1b4ce74b2542c7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_142 : Impossible 0x8000000802000000000000000000000 0x2490417fd041248000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=26) (code:=0x1e54a4f8da30ca520c30986ef51a0279876a6c3b6123be02a520621e77c4d271123b8fa2c9063cc24206793f5df015288198b017a81e98b0127d86a34c844c049b3d4f907e8b29319d4a295123f5f2791f40f93b4f2754a9122c9e64687549d013f5eaa350b543cd8a185010f37c8d2c54c87cbf484912c54746750a220ee990c25291a1e83598e611091c4c2771353236b1435449cc552c4d394ad157cbb40fa93225fa22447dfa468daf96284a9dc670fd7c9f519234714ad1576a85461da6191aa30614a91a368de4f8c718663bf5aa3542546d16e26f946471235daa1398a17ab5c768f34346d6b8ba738819ae80b547b0f47539d4a224216a5498ea7c9ae628d74487324d361e4ced55083e50951cff898ee8d8ed7db5c6387c9a5114aa367d9864781e52acf04abb469629f6d70591d4eec36aa8467b9c899f6618fa1ae951dc1262683405aa779cea5518c76581e68f92e4aa51847535c1f4c67798612b0119c890ee339f67ac2c25bbc8352a8d32f10f94a9ea254892221dd13424ff1e515235f236b5c1fa2a8f2951b5f2a1222f562830a2299061114ee425314041b4fd80bbd3246b554a1f295285e2e3050bcde29093281089778789ae9b3d58e4683e9de6399e3088498f03134f546a8c639127309e46a6cf162824c8a8933bc8390a023bde215c7a77234f2d552902e908a778992348390691a2739089be5071ee730911af32844a8de3e88d08d4a85d1b542f384a42749cc31c4b468454e325354fb174ed4146903938912418ba80c242e8f2994b4ee12a3bbb47d12a8d888399de3b9e5ea0ba3d0ae2e9b4ed0399a4da268ba76a548a8ce8d0aa8f50a8d8a08989a0e349c4839e67924a9883b9da8988a8c3ebe44482e8e689255aa829ea1f24492a7d0ba4a8f696b15464951e76a841123cbcd2a8103e5467d3ca65e20fa1c9e50906d6b8898891a268b2c504c912d53e84c8fa79226f11bd09498e273a5af91ea4987ac4c44c049518a398da8318af13bbbc810f33ea7a339ce8fa32808771147d28c96a64f5204a13684cb153d2351939d2d444f307d3cc8989a021cc3ce16773546ac7c7b1e68d62c2424daa6bbd4f228c1b4f943d4d2252d19daa7a9031305d50837cb4d70f461448da4088cb9d2af3061448f24a94299789074443c62291a1646bcddac7528f9087a54f5406822254e84b1c4492a226f9224a32644047a359127963892a17eb8444ce69d8b26ba360a7369e6028ca1a21a5d1ece10e17ea3a3ea1a73448ce0e2498faf10e4591d40faf1389e4890769cce2d745424d11475053d60ee14a83b94e44b5495509d241cd7354fd1dce91ae709d27e94e7d40c3552a3e90d7887738a623a94e3d9c2a54c88f2641c4da8498a509150778ab0c691f279265217988fa6af349d393ed1146c31a65e2950f21f638a5489184c331489be5e2a507aa64c5789da4f830d031ccf2ed1da4c9f67aa160dac53d50152bc52a29436932528c2f14051250b5421278a55191c4a112af9205ae12a7c9e66d154c5355110389b4d5404ee3d98462862c252a44932436227aa3af152b8c1e51d5298e4f942409dae90478ee6d1e479bb52a12a773c461224793154a454a57a942e103ac4c6d6b94a74889284a5638e94f88970bf546c90fd2559262906324426070749512184a546861659023d9d20d7386128923499065255321dc931ec81386022248131c4198e23d023786b4cc0c4a932f53bc449e60ee894a88963a1285a06808ce3e47ca4a8da0279a06774346f18e7b42c6b19d321dcea236d747d0342cf34087777985e22a82ba4e890d747ce77ca1a4aa6684a023e4f34050d1ac671bc750ee7b4c9de65985faa510314ce2314d7386124c9fa3086a9fa7c91e612249552b2546dd) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_143 : Impossible 0x8802000000000000000000000 0x82490417fd041248000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=28) (code:=0x1a4d70936ba268f8e78a8962a9b50319c4c9fe05f689bb03254c23689ca22469f249a2af3374888268eef33751b308fa90926996b84ab750d3b4f31ec7d2343e8968aa761a51a309b5c20d2d17ab1449a04449e6469266a899345ce0774498b0d808f3338952347d225da4083ba548d24c896e807f093ba4c8d0772358a1a27735cf31f526711de690e1212773fced12cd71c526991d481368309aaf31d4818aa12680bcdae738d7405ba338fa99065185266d0613cd121e8d76e87d368ce76b85faa508a9c2a57987088696c359263b9854a8f9f67485576bf51235506818d27a9020d7225e69320c7b3ec754ab240aa44b14ee1120bb0f1fe6b9e7096289637902454fa6d70895738ce808ea3859274824cc5404e13bb5ce73bc6f3d5aaa10e2248ce01c5a2849dcda30a4c4ca12811ec85a02499d43b9ac2d8ea358d5848ee1ea254a2540da96a95e6931ae811ac6aa25921a50912422ea5968a50673e91f3d8c26940c5d6a81ecfa7176877185c29521234a0c75069384ee3d9260ea35cb47d1ec691dc3d52a258a1b41c26d4b512c526444b547519c8150bc40b2771f41f5a21a26a85c1a231259dc259f4848fcda1e6870fc471dc2f78853b54f32a8f37e9096e9c4628c2691d43bcfa344778d66d44453bf47d38a0e709ba38546c9498ff1e64fc2467454e73c46583ccfad5414dd848aa314cea50da188799f51f455013eda27e9ba3b4ce0aea5039368ba4fc25154440ae6d498f33b88a4fb846abf47b39d8a711d46e87524c2126d41d2382879a1e9da0619e0ed51e6ff78913779c28e8a51edcec5689a424dba15c5b1ec6939d8a5912d1747d1c5aa1edda519b67983b5262c8d2f32a8109a23e9c43b4e2a341c202779f6f16a9baa71d4dac94a8ed1eca326d0906128cce8e8eadd0d70e735c591a4ce44e5af33752ac524c3ccf6c93a5023f43d0aa3a90210928e82451edda0da933b4212d749bcd031bdaa226d573bc424c72228d20c236b5c3d388f673b84425ba0fd308e724c6f1a4fb1f5e2d51ce6589a4989ee1204184fa869dad1055184a33f58a3d798dd1140f4aa219ba7b124b20ae899a2739b6f13aa94155c2229f6819aa77a226e8f63cc930fd435e6519f2819a27d9de6d9ba5552b25120798cef9438fd1a4754486d40b14226c5425151f511224a368b9c8494a1a45d4250d1246d28c89628697eb84226f97e92640b6c1466d225c26db243cc5d494aa31475254691647e9250e07da9d1521cfc67324fa068955e2155e680b5cc91647544b5426d12439eae950879912e13441e67d384fb8a9a236a12a1374414d5688f335cef3a489349da6d89536d42384499aa25906308d21c4771a45d3ecef3fd03688f37a93e1c2a3508f70936b151a7308b9f6ed6b8109929fa8ea828ba168da7280bcdae4d9ded50f11dde67da4642c677f8674d8f6ed68878b55ce1ae7b409b61aad73bc8347453404673b51f1e27b3cc3ea42e770839a4c38536671ea919f224d2b70b548905f384737a926a31ea7b1267682f9cc3982585e57388da2c8d13594e27a4c87798f314469518c23b60651df625a51b85de1f2d57a82ca6cf328c9304f498967318491a6248da3030e66a9b67099dd2344f709468988ead71fa6b849b5de61b59683bb4ef1aefb40c3a8f6e71da909e26b83b8d2d726d0349b540c67519dda12afd709aa6ba343e616354ed799de8da0641d067d1e60be839ff036d83e5db0368887a4683a6e858fc8304f6da4c33a123fd073e4d21fa4f4985f6aa3ae916d361f4571f2849fa771842f9f2278c27ebcdae4748d11f3ea3a469d2769e6430ff519065f0ef2d7091d40cfd738d11a47f8b634b84f31fad73db1532126838d284b84e71847503f477518e2f96b9b61cc5d28c3cc6d3794e4a88a43bc5c21b5021fad7031be526e1185034c878b847544b14e91fa789ea708d70a6168ba3289514c691c4de1944f1bc753d5f243499361b649bf4f14050e47c6ba167990e433e8344aa8e9c25d1a2518ba42c3728cea378d1628f11c90b70bf444d0b6b93e7d44b554211a7118414c934c9120997ca844f185aefd146202930937eb5d32398f640bb41b5b6f507ca84a33edfa3d9ea869da9992d28d333ed25142f90be7d434ed1ede6f13bc0ce7ec052744d328da3a39b9c40d093ccef39d0d628d703d3286a2287231c046d1843bc4b3ccd718602951de9b1ae369c526212ed35ce73bd0d464fa24a4a86293788571cc390f37ea3a15ce68c8b28726d0d3e41e9ce7a9e61012ec75e2405fa4e5f22ca4c404de6b0f144d0b6ba06259ce779f5420ed788b47d17478a848c824de6ed0c62f9f4fb788fd508ba86b5c769651235cf346b544b5e22c9ae21ad71250e46f4b50d13de60c30d7e9ea165de78c2d2603d369fa87c24a18087d35cef1aa8dbd46ac347fbb43bca33fe1e809da6a886c8d1903d4990e3e8e2234e64ccb4452547b185e60f4f31cd430939c6aa1e8f9ea97942858f673849a1a6d1f47fa1686cb4ed1ec44cfae779bc58ae152878c352127ce9345030ea0e25526d261d3211c4f13eb547b0a735de241c6b9c2f31aefb1ecf51327893703768736d876bbcf10731bcef26e0e930e2896aa540e2612250113dfa05d7dc04f507e9f61c8e2898092a4db5de2538808c23e8311cc611f4e2931d4114a738a3a86a241fa328e24513d264a936996d8613c4494fb1ae06889eb017790b3bcf12250147c449ec3b8a74447735c7d28d1235c404616bc2d070e31f49bf442c7328d26f570a959279) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_144 : Impossible 0x802000000000000000000000 0x82490497fd041248000000000000000 :=
  checkChunk_sound (initRounds:=2) (rounds:=8) (fuel:=27) (code:=0x19c930714999ed70125ea7d2248346d9e7c9e6dd0ee168ce73892ed11385a028aa1a8e8da418ce216f30991e906938c41ce714c8f3254e73099dda11f68c64388ee8946c3ba4dba318812246ec2438c6c13231c0ce7688e61ba71184634087d868713499c81c3c448da8367823e0f270ed7c879862ed41449c4d15689c468847b4481308da3452b678d26708a89ee71a4f51dda31b6b895225fa44d0b46cdd77a941f439c471c5a231a249335d4ae903199ed71a4ef135154a9e41b4d1528474cb6891d9e1326d0c273a1e6b9f47303e94a634c9e43e96526418319b51e2268d9866d1ae858ee41a9512132470c634984591241ae9918d4a368d27720c6b9ec730631ec831dd4a36a241ae89529e52a33c494f87924d0130c890793b9ce878e7264cf4186d23a95ded50d77c99e779061ae772551210b67c34f9124ef6eb84e30673bd02498188e281264ef249d435c7740d123a81e46d719fa1fa791c5f2770da39903418f610738b5d12d1529c2408498520e6fb4bd0711c5f4ec8bbd52d4451f23b1b9399ed71120f221b5cc6d50a54b4da1e8ce348f2e322a3182b926269cc5f76a228e876b3c1e53238a4c4ca24da38c794451b7ab852ac908491e7735cda0f36b8fa6d1cce93b44f1251b4931ad0f47c3d798f335cf540ce91a4fa8f68877708d1778711bcef06d3cd926b9dced174f23d840c6d348862bb444f13506030cb44324d0f52bcc0f634a0b2d4d52552836a5a7d9fa849a5aa4b50f678933f5f2d725aef03da94e235df22e8a2ed039be4d533d151ec5746dae790da8983b9b44d445c6838ba3899e107969a4751dc6d10d45c9a369e424e0e71445ae0d2fb7f8498ee338620af314e5253547b3c8bad776b24dd07cbedc68d81f67ad73ccdd324ed4345d499de17622e14a8752126e895a5b09768ed7c88da127cb44da212318a22e9dcc23b5093e44b1d45f3c836886613251134b5c10cc215c933cb840d12d8eb2d769de254ba1ac733e92d1f4ed1e695105254dd3f50d3e5ae879aa64a12773bcc23541265b6b99e57434ef10d708571846316c5f6ba063cdaa35d86354ba3e9de773ca9512c50792e892659024c8ce3d43e62a67b5c10d13319e63cbb52a77899bcd0f226479261125d15c7b7689a3cc451847506930c4484bb4399e52a1120be89254ea1c84a9ccd2799e42567149495224db097cb5c1d51e1267ebe4d22e9eae33bc338b284a4a3c86bbfcc312a799bc93435f21dddee1628d71dc793bd151cc670be309ae7538435cc624c893b9de3a8cf339f4339263c8769e67dbe51b33dae18af970a55aaa1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_149 : Impossible 0x802000040000000000000000 0x490417fd041200000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=27) (code:=0x30c13586398f644bdce711c3bde2288f12c87a7e8f64550f264f370a023ddea7719e950f64a9f43c59ed71064a9ea0f33da7c631ddae1f59e619de30cd738d420c2838c89935e020c269096bbd866ba84e31f5e21233cd1d619ea20d9e7fa65d20c63d404830ed1f4f64184190cde0de7d3486fa0a7c83a2a1450952428c444ca2420cf2ed1b436a7e8dc6642145de950f2f10891547f1ccb278a8404d399c53e5091e8d0308f2694ac35c2264425072ba4e3ba161a5e21da3da0d1d2646341c6f90b840f63ea64a176b5c0eec301e9f455318f699404691b46f20c2ca55c22844f468993a4eaef2030375b1427c425061da89165ee77a54f34b5c21c2f318c750d54f9d21bc630b29f14c6b16dc26b9f53288a02225e2dd204165328887a3c8833a479788c2059a08dc7aa02e14443b9062cba44c90644bc4f3778891643de420c68db0c997887ba66020ba89848f7308f715c6b1d461404b21d275388f7709dc11ecf3a8990f4611d426602cf384ef7b87f798633b5d6816e831bdc75154596ba94384ed448de619d27a9ba789d6424d71c2734044346cd509a769ba1c2f7448b21ef152244d1650913b709e67b9267190267996ed4b4629da7ba12408dedd2a8da0f73b525374ae27b850120e7d9da3ca2280b147bb3c759bc374b3091d6a11c2811c29339c8461c5c67bd42b8da3d99e0893dddb21708cf7a8896a8319e4c575bc52a0a14abb4f518a97a3e8583b9fd327bb74fd3c4989d637b3ce381878b5cd540c78a2444bace113b23863384c5298e1619126b9b4d205771bdceb424791b459154484b280a6271a121a8d6dd3a4155bafd0aa6e9c54ac91da78a2a4689234a5a13b37c1c7b19c731a418d36388e63b8d68d3c879a4c8d3d5013f4d71da0a37bc651b6b8de3fa02dd059498de79528d71c4106d71ccf32abb52942c35dda308ded539c3683b8dc79768e61e4de3d8d2e1035e0e551acea80880c2dfe899b63ed1326a989da3ea3222b5cdd6a81ee6f6bccca70fa24a5a591217ba36809fa53b752570a9512444e1464ed234a319c6b8d24d8e63d89a3c9ce3b40cc55339ee309651b1bd25216909e4949a5c21ac631cc793cc671a51ac54083ce32449f52d134f714e3c91277bc47b86d3b48924cf72c8fe4d9e23cc047b87ebdc31a1a3b946449b6f114cea708788c41dceb42cc6f70f737a4dae24c633e81c31b80c343120453866fd40cf10fe7d3387b8ce31a163aa4f01124ef2cb7442c83339fe3dc819fa7bb9ced6e83cbb4f76a851104796d8e707b73837bcdae39cdb75bf4ff348419ee691f46519c771bced2044fe326e89b92a3e779068087fb743dd3711494ef404698d8ef3ce1a7b0f634883799022d8fe37a4a20cc63e8ce3cceeeb0aa3e90d544d23f859154c618cee37a24102f73d8fe254ce07b44906611343d23a3120444974aa07b799dc6f18c670c4fb150ee318ca379da2326b91935d46494c646bdc8cbb485bbc13c6715dee833d88d3fc7d1551d41dd72112d2d8c62e9da2783d3bc3dc2c54c8e11ac730f63993e33a04710f287102709a4809f66e87d485fe05b88a02408ef1b4949d8fa4dc544748d1847719e37211063b8c70f708690ce4192d80b847d3ecfd069809fe46a0edb0f30324a8abcdd69974931404673cd253a40613d955123f602e10fd13475448809d498a0289194934db546d061448fe7486a498ca3ab74771e21ee890c6eb27c6714c83708e13d878cc4e93ddaa1ee92892e16e9f46ba3203ad73547f184ef3ac731ac6bc64e13ddfa35c87369014b43cdf64c8c27ba3275bf41ae78bdc791860298b544c9f68c8aa8eb6c3ee4280a3b250de121308de80c95fae10fd70975121b6858e24d86d968c3013bc44b84b20e2790c50b1bcd53847f3ec26bddea4849909996a3633899808a63f4e2404b2eb093388b2f51128383b8c532388a6ef085a2642384fd18532388fd8bbddba0573ccfe3d8d70b03d48a713bd266a8b2790c6670f37e8496ea3a6a873788f145d417abdcfaa50de788379af073cdda3487d2628aa36e10492b8a6713682aa727114c7bbb45920eef2647b9f5ba1ccd7264878571cd153bcf7464d74049b708554edbaed0789df2d4d8d237b551295648e71cc44db71121c6d9d6539cef51b42abc41cc991bc670f46a438ba2651a14f191248d288771bd1236b847aa027e9c223b013847ba9c539562a1cca73e9321e63fa022e91a8699c339c28094e0a2771846f2d8fd1bca609b01319369906b438de39924808c21c25d096b849a2e9cc8d539ea590ce2c9e67935d4a07ba95de3189b18ca72e8aa309325907d3dd369f1e27d8d6399d4454fd1019a8b288bc4db31877798f70c4f3164e6d744b54809ea5381cccb53b84758a9156b84da7c4da6ed71d512e907340cf35287b9dc57236db114e91ead53bcea04d1bc45709b6a51e630a1c9b0d57b9cc7b9c2759b6399f44549a7a8de6da366d3f87e98c379fae11fc733bcdb05536c2abbc9b7e89b748fad544b2542c7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_151 : Impossible 0x802000200000000000000000 0x90417fd041000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=33) (code:=0x1f2db34a84499f6779ce0daf12767939dc2464484931fdea709e40d72a90d1329ce142d2b628fa3f926f10e22f9ee611ae8686bbf4f1499f66d8fe53a02f90e7230aa24cf90e47f3e8a235ccb1550b541e5aaed0f789a2a438d714c874992a1f4ef53b9436ca70789da7aa4c473bce536a54791fd156ab247881a62688bc478b843f3243989a1a2fd709de2298a7886ba4cfa2c8f10154be45789b68da16d7404c92ea85aa8903cb8602385ca3acce0ce696b8f173839bd489649ec538f135c89395156a9c27eba41aee72e98e7583e9fb152245d18685bc4f5385da2a90701c9f4791fc89779eb1513c1d721268fa69044944fa3cbb5ca19e1c48b8e27aa131b44e0a3ba841761a7a9aeeb3bc415ae75b8d1d1ae68a0678b9435c7ea46eb31c35c7b36bc41eee33ed0346e7275a46e550be478830c1c98a524909275c25110e4fd50849728aaed0eb344e335c2e99e689ee7e9caed509e43f6827c8394bed7495422a812ddaf11da0ed7897dae71a84c71e2e52e835ceb508ee27be436b44c70f41dcba0ee1cb5cc33689e4fbc43c4da2a9a2759862eb94d2891ca077136724ab940be3b8f6e531cd72485352d41656f10f43f8960acde49348f10fc431bc4b19cba6d508174ee0baef35d3924c7b3e5426d3882a82a8df153c4d722a847b942770ee9300ef2b78884453692a269a4758ee8ea021ddee6b85f0f58e5d3c8758e26d444ed1e50d3085d0557b8613c6227712c631e42e98e78a4c0ee6d788f1729d6155ee38a3a6924a2a87234a2217c6d35c5b1a47b12c17cda259aef113cbaa144b843f5da88a12728f27c8691e2499c4499e434b943cbadc27d628e57483c6623d99ed71e2ef164e33dc1e31124c776b9c6779ee8940c44b0c315fa919128a8c230cd73e47b0de2a9af151f46b8f21da33b147f24df23e51237bf5ee1eb034c4ed3f4e14542f8ee7a8f6268cf70a547f0932367d9da49a265f6b830b3cce3d4fe779f5e205f2ac543d33cf13dc17c7a3bcf13e53348c18e2a2d926f7096e73ecfae140dcaa16a8e3081cb42f88a7c8420c8ab15369da44d1f13c3d0772a8929f2613489397c6919c4335c7f3b4dad17ebac8a9eee13541543ae721eefd4447585b2544caa693b445124818ee719f68d9fa899137ba2e6d62b948886d70a061e5da05f1e4891a58a219b4f53b5d60da44b858e2266f112338a17b8f78887776bacff0d2f524c2250d88942679ea4452633cd2e1728c52249310b1ecee218d77aa060426a9b436b850b1146f4997c49836886d73ac4f19cf7628c535477448e26978a5592a3051c1d1b3ade2728d2216f11ec55454309da24ccf3bde2718897b9d6a3708930938aa06448c372a8c6964b7434a267594602db0cba770c6791f4931b46f0fa713c42e96472906298b2279a41ca399bc71184591b5151c8832e82d8aa6f348693383943b1dc21ee88b14315ee619126b8f73b8729c27b9dcba1c877394c335c7176954f10b26b8da479a4405156d9de35c653788e7687b1ba6a8e66f44b1c7d64822592209ae4789e5d18c6f0c5378ba0fd37b14cf1c48964954449ca7d063175125389a44ce53bc0fc77165237b85e77a028594e398268bcde893d5aa36a0a0fa631bcd540592c721d42850f18987976a22729ce1cd121ea471c5921e21e93c0da693ade27287c926f1394eb0d53ace5369a511628a238b24611f54675146428e11b58a47a046b8679f47f3dd13728c224c1942cd7638e290a067a90a3990e61812d263081fbe4f73c9ead5444e52842690e34a2285031c86679ae4997cc3508758ce2598e719aea1076bace35098483848a11a50a6a81c96448c2b708ce8b9f2889ee329da7f215ca3e8318be3d4546125471214f2a30259e5ee33a2e214385463d8e23b926428e6759e58e28dca81ba58a1ee51a15091dcf91a4936e8f51e41c4e631a14709ed021dafd0960ba509850341e1276b14e7206269da11120cd23d3b43b4ba7962b94309266aa165187ac3c75184308a33a5de49a466b90775c2441d46769d6739d2e562b1da28d03b9eaeb369da22e4abb4c33d503428ed071618309a43e4c21f89a749da7a942672028575b3c309121b8ce3b9866791d1ec85434771a4f50aa9abe5d6d705d3b80ba779dc55214b4f21dd0a1548d06f1edde7908327cde2c8d2468a6238ee8510a6797450be5eee1628708ea44a54e936c5f0f980880bf4c27691a838ea4050a2a883444691748695441a340bf011dced4750b3dc7a7585f1dd21418f67939c19cf6448d2778ee80a15c2284ed0f9234d2509da226db1f23bbb5fa610863e4e12f8f93b853768f6791077e8ee932363da0e50a0275a15aec56381dcc947d23619da709ee44485a76174951bc5f1dcfd3e4d22dc2488c558e73b147091b3a511202fd6390281a2a84992851fa3acbe42a067a9866d6e9012167c8f61352a3b9127e9bae1324225927a8ce508d23bb5c1dca11c8ce3488925992c31262a9866d0de3c844a1422626259a4937ba0242cbe7e8dd738da21250b847bba4dd216ed02a8c307225133dcde259ba930f73b9b4448f634a02856bb1daa33cc518b1f0ed3fc1c8919e3498a7a942d70be0d29543c3f4ba349dc551f23bb5d8a35c71469e417d1237886468fe6d22a3b91273b7442d23284e7628ea349262846910b6a9540eeed42dae750ea709fc3e46320dd68885674a2677b140dad734a4dfa2543f8e11fcd53b5ce7da3e509b44b24c753162ac7688679da07149bb434b3c2d4d45d6b8d77a849bd5ce2246939d0b24d8e2a8933848917c338f512479174eb3b4892fa8d9230a54c30da50844b24a161836b2493344613e4cf6b8857081b4bf3176844b5cea345013dc42b84e74258ed5077225864a8713b58e49b75e299) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_153 : Impossible 0x8100802040000000000000000000 0x10417fd001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=11) (fuel:=27) (code:=0x42d0d3f51f45424ce7474e54464e8c9de6d9e63e616810dd47d0b3292a475cac9216207191fd0b3eca33cd1f7385f47c2b8be630b27f1cc36906799c526d51263bd03444fd3ed231ca7ea468ac75923bd1d405e6073658ce799fdce8591f3bca11547e8fe73a0667455f23cd353ed1f4041031fca5cee53e433bf481b74798b25346836a3495c2c1b606249b67d8f2338e679b9cfd1fc936aa1c859e29485d7292a2c996509aa40d1d4443aa3a229d280a1608b1d285457eb243ec873c8fa07e339e47181a121e4c749859788c91e47d50b54859f68086aa4d110da6aa0ccb1c481c04678481fc797da3e41b563ae78a8791ca474e5229750928473124711f6399060bafb0c71f8da871bd1781a6278a1250b54729aa84942f311d0f4ba021974fe2f8c685c0c3fbccf123a8349c736a87f86b9d120c62283587ee728612278aa6a85f41974279c51a10b7e9e655254d518e255158ea6303204648ce819e6a122e751393c8fa1277e9e63736d1f3ed1b0c98590ec7298e2930da3f9063ab9df22031b1f30b4ccf13bc7c911205ce77a2e202e73e4c942d2632597093cdba9b0898087da4641c55f21c5aa2167f1f51547cef939ca3e4e57981f71b28cef3f8e6891f48119c80a6443a82491f67107f38932f9053a0ce20c2873e8c7408f3378e60a74193639a3ef323e6ebe4e9469014c50929cf3455de3f81838a24673e4858ba338ff0910e448fe7c87f0fe12f302cc5509388ce7307f7ca12809f72707e8ea6a1fe023a509858593a66609e7119c3f4244993a0c1e2819e67f2f8f942d0193a7699073798e28a9ca2ca4e8582cc0d1542c86c9d063ea8dce1846d1e2308f942d15264a31156390e31778614d8e67d13c3bcd52649236a0c31808a839898c869b486bcc869442fbbc7888add3ea022e9fc8d07f404590ae838a9e6405ba714988939464ba4570ae438e68787543d92ef13681212749c47d9de339130b1d28d0e27288320441c247523415d46419368924c41a660274b9d96a507d3cd231252717d1d94a02539094d84e5093fbcd0f404670ce31815c93294051142427c3c932c94e835289b20c8b1f410c7d444dd3f8ae2a9166a94a27964ea31c9339d0336cf33ec1b45717c9331ca3529651a295014245920c6720e8a8512c85278c7452a128d084c6dca809331d51f29c498381646e9320c7d1ac4f11c674ed338a8831654a41d461c4499371528ca52530919df6e703391a4d8e739529ba11d989bb2948c920be52a34e740612f3408778eb292726ac1cdb11a3a9b43ac55420fed539d232344250139c8d204db839cc4760e7d0ff3126c3f8409fd3328dce81a47153c91d1c44d8fe206409fc8d38a949994a5f43d233f5117489b23446c2a8394a711952707f40c8324c508e323839d47dc34247350e68d21c4926e9b3be1208184d0d3146d2d284ef8ba1af31260b307529363e8ea40ca73a49b0da38926268b28d40c74a1a0e0fe73a4e361fdf60ce83d2cc74dd411ce061c46796a460711ccff034d51145de608781c745754d3b26b238795740d2d49d463ee131f06715ca721e0639926299de0a281a869b3bd0610737918fb1021f459204fe528ea7119c2c8cec710f238e8a53ed4620c538a6339068128cef49d1148e1f150ef9da9697a4e1e5412728d1e7350e7278fc05f21e61f65f1445719ce223846498c67f0820aeef1c49399ce710cb274a0c4760e8ba1e0c69320c3711ca319c3748f030593fbbdf207f7da3633c9dce19db61fc670dc5f3bc3139de67d22c8d4cbd48e8fb1ccef20d254062a8f9070c68593641c5479649016d853a468fa170d7991f36d0113347c7d31b24f37e92a0ce64be43f8ce4390638a6d2344464c2cef23a23a4d91d4391d39a248323f0b1f5923cd1a26e8ec541c47d339e71f11aa77c897c55018892a3abf494a02253013f5e623f092663a494a5888fd858eb0d1328890e10f1f4549b1f43fc2d92dd818831647518c9522c7489a97a2280a0479101494f28d1070911a9923e4b426e7f3e9d349292fb47c40a5b512461fcf62a15ca726c871368118c9b9fc3fced2f05298cae438cf1f8789b4b602f908d40511948f907329e3f0348c94c347cc3e5a0e28123501849097e87f1643129c8123532f37a88698d0325f1522b3314a8908d818e67d90226f03868738fc044485915c8d399ea2a92a3e916a310952a529aa4e8da3a425ea3d6867ca32089468ea5297467464338ae591e442e07113e61a204a540d0b3e485c35193ea0c40a022054105d96c2cf94451b869ea1363b8fbcc86a062b8ce319113e87d19e2a45494a2a93c34868fea524ef54050623b0345a65ce3e4f500b28da8bd4451d65288a1678a320554a8fe3e91af9424897ebcc458ba47c7f43a464d8fa21cea39b2542eb136454f310f0b26df21aa7321c9522c2545379946f91f279a35fa409ca106918e70747d014242f8e6378d64d90620e468bbe4fd04f2363e2351f45e027d899919170fe123adfaf37a8d51ac05d6aa2c432f88b37a66399c4fd3249b0d53d61299892369368c90d7d88bbf49b8f8f58089b2354af321a4550d0de8aa9531247097c9f674864c5c6b26c5d4c4185f26aa1c8b97dfa3e4fd1f48745c2d26d7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_154 : Impossible 0x200100802040000000000000000000 0x90417fd001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=29) (code:=0x551e49520d19022e3e4a98a674de3a4d43f6bbe4788721dcf23fa0642d065d3d40727c8acfb49cee819124191136d1d49d037aa343e4c340d1622cfa469067a9d43b9020fc395162224a4a509113b52125ac90eef928441bc4f5426163249529c1148cc7541325291552d17542174b67a89230a04a5103395023959252a0c52878c2ca73fd028f8964a9dc7d62845184a11f262a544752317606869ea88a0dfa0f5438874c45b229ce79059445923092a2d9f47c9b44a9d44948aa14d862a0c12e3e7314c2a8438ee064d94e29a844d076539362989a41984425063693e268ee5900fc76591cd361ccee258867946876a1aa147cfd3e4c9144591345d16ce72940f32553d423b8794194a21a5f4094e6185d4dc0cfe077144a576a2419c57398868d1d40966739a043b9fc888a54a5da78a3a42dea849f2445290771d5e281bb4f9424f5408f22952331c4329c5718475468811d4553f96451c44c7d19768ea4251a409ce04fca6668d254817ab5c528819cea531c6715d064a880c0c47ce62d8fef1408d70e6670e70929cc717d1a424892520a62bc250139a34553bb140e61fa0c95288418fe3148cea0f93999cc717d0203f409cd3e7d38bcc204fa0597c91a831b46342cfd2b8731f43e4550e5066e91a80a3e679392514a4698a85a3e2bbcd1523acf112fd04951d3f9e691a5e949e23c8da5717ce54482aa3ac541d06454e540b242a94a3792a2b8ce3e8f27281cd0b4660edd395e6679277e81fe0e2f93e8925593112682c91a3c82ba942ba3462712547d023924fa22b0b1fd2726a05ea1fc4702fa2cce46503729e6ed1cc3f4f92f8fe0e647448311b52ac9030b2516449741cc290ecce12a6f64873799ca395de23a7791cfe8103d40d093ccfe08e7f39a35420e28d0ce38a047d2942048d45a85ae1c4c309527c71408cf469cd0b22408d1a0fc39318b2570471b4f3409ca3c8ca468ae338c60b238a04ed102633cc5d399fc2e99e2b8571648127cd70dc2f39a163fa0c47c714088a11e16205112229f4bce5318fe7d071338239c47d20c673f8c211a571fc468ff01394f339a95ce071419120ab1f7e95c398ba8fa4e318f27f05d1e64f0b22a789fa2a942458629e4fd31897c0d010d462965133ed11464fd2b897a24228665d49c44662633f824a7f44c3ce631495225ae8fb246b9fa319251fc5743d2f47d9238a22f902b418b2388ae3c9bc448de7d2220b2571bce277a4a6ba1a3f8c51fc155ae71164455ce72a12859e25d0610fc5516592633cd123ea94174e60a65919c3711c4d3c492985013cc124ce6e93e799f6167787c99c7104d0dcc6731245d3fa04eea31fe2e821f2136de2f5388923983f96ca13c89b16c7719c8b216551f47f03b43a843cbbc5920e679c62225af1454832166d99ef527c8ca2ae518485c341469f7290b285ea1747139a5b112323f9b67a8673ccf5789de62a16222f58ac75020e650c3c30843a84791fc738a912fd073508638f8a199bfc72a3f071ae2f8fb0b0778f9caf321696a0c081238bb2f62887134c536dfa19d2f8a88a9dc8b1fc7d85c0c978c2448fa67a2a83c4442d037e98a1d88ecdd1f42cee4f87740d0642cd745902a3648550c27526d2542d1d1ae8f84d11f8e994ce3e8284ce611cceafd11f3b91516cc91dcce438e2c50711562a3982f87a794b47326d02f57c887be5210cf11424fd1fe94b943b8ba26a220ce3ba532518c75395420cf729ea629de772844d4090611511448f34b43cd09628cf36dea409ff1d3e490c44e273129104cf72a12969f227dfa3f4ea3898a61468217031d507153949b3bc31a061f8324c52a95d0b3b9114248181fa0f51649de88c540fe5b92a1a8ebc4ba893d4155e67c87cc648d1cc469e277338b68102b8ce398fe773288ec24fb1070b35d0740cff3cde21066bbe5238c890c8c43c721a9e623a227328c431651a7152ba48da4a0ef1b4945d8081ce8ec04be3e9e4315452146e1a8390d21b014651f4c52120298a5a1fe3e41a42077468aa650e5af252164fc1dda23f0d07d649df2d21ae70caa2893011d5ba21676a464693e229b67c9ae0ca7d8f9dcc309f3e8774350147c6f328ff117e88ea8b11083516228da4ae729cfd33cdb3e42e9da7c9de31a3f0109a7388617cce2d94e9f10686a167e9b6d77a80f4fa619fc8b27c0c9319fcc317d125388b20cca20cce20c671fce23e4fd374fa3c8529fc814051f1123d20e7d2dc4408610c5f19433338467786e18a7cfa5382a8e29f3142b04d938ba2a98c31164ef418833bca736c20c6d85a226d9da7ca0253902193f8339c46545bd44c5fe3e489102518f98d9df1d106ff42d3162a1a4c5da1fedd3ee227e88322c7f164328e24f8c6778fe2cbe4750b287a4aed7a8649743196c3f0c45319c449060c84b3f9c47508a65057519b54a3145b1947519c7f1e433a463b5462da270f04b18cce249de9f0c651b74fa770558681f626f59387d3f98a2271b4450718a89a0e3ea0c750c5a49da8399e3a226869fc8b30c3fa3a8920e0217c630678385f8da270b46441c945b4fb9e2a07e7d17c55204591c42b023666f32fb1c6302f8b2168fac51f859134aa0fa9b8fce214a858fcc618a22aa20c8fd1a67020e598e9f23f33a9c799da3e94a3f4c5455923883f5927d1c48317c4368285a5e52bcd8e0c6891f4c51ba449068098a38bcc0573ed0e2a46bb43eb6e0e0411345f8688a64872419f4a530c811743b1c4ce21b013cd25154833b439202c5738750553a8662188a2e97cc320c67539fc1fe1a639f2858106ef154fe4d2b84b0a49194a1d8fcce08ebbcfa2b88c3b2d8ff3bd2747d0722283c044dc76f31025f539bc4487ecdcf9444e7474fe216ed082228cb0d164e93d4fd2528eb1481798c91f84d16411459468fe7a882388cc75204ce494c53f4e9085a533798bcd110f2448fef906593bb4ef51812ce23a9e67f1da81464c519c388fd210ba67bbc651de6d528673248ac45130c5648ea2dbf432513978ce199fc2ca2626a8c1fcf531662f30799fc634651511b74314fd6499e51bbcfa770c5338648b32f20c6528c5d07e3b906671db070629646720c5ae71068090cbe3aa2e06079c2ced83a26539fc8b27c3a8e23e47c9de89a1f253fce94bcfd3ccbe18c5d1d4f323e319e65b14c3899c12de63a9b54a1d46e8f22d8ae633cc51e266e94a269fc52a76ef3e9dc115fa319de949da1f4a54948fa827ca5e7e8753e8b277939295052f30e0e1023f9e7250ee408da338e2a5164c353c0c17e4a237154954319caa3e81ac55290836bc94a31ddda1f440a0c890ba389ae368fa3a9dd4ae70ce1a94e206fd49c3ba9535206ef1bd1f1f50d1417e88353a870b67819e8e809af2f6d9254350726696894a0e370b73bd5e299) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_155 : Impossible 0x40100802040000000000000000000 0x2090417fd001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=25) (code:=0x3d439ccf849f67a8ba8abbd331ea67a347db0d0124e779062951d1b4e6505da49c676185743a660493a864924fa21c5f3c8891d4da4096c8e9865399d360593c99d1945d1b030989f6736199e205ea30d063e8192528ba57619cdde03e95c6761a3b034d85d19ccf46c3c26cf23bd1d19e88a1a7a9ba8ea02e73ed0740867a2244b0d1a33d1d3c529398fa1871533c9b3c50f2047da243ec1c26d9f1164821c9220a3aa087d67c0d0107d4764efb20707769fc1363eb7502469f62ea3a4762a202935289390e809cea576a0ec7083c0d0f788677d98e3c512288791037d92664924fe18e7d3246340c490513998e37892891128319c1cd128d226819de26a023bd077d8e7248e63e9fd4a1f7132530343c790893bc7981903498e67f2261cd13425f616513426068d439232948910e679963583f91c21c493ebbd17449191e52a2466b46c0c1acfe21e4d46865a1d174a5091cd1214d2afb619150fe0899b95dde91a2e07f3cc44933b4a51cdce1e4e733c0cc7112779cf011ce39c8b9ce7f31e3611d739e4ce29bec8db3d36164ef22477c1c979db0323a3e9da0fb1581a6ccf5087db1c8b43c399f6a12242e94263a6daed51da7d850a56ef3edaa2250148d170f2358fa368c250a02ef43c8d98efb4d8cb1f59e35448d968eb3c8d284ef4461232d2322c0cecf6a893a26ed0ce67b54f221d930342432e46fb192dd6188b99e8d7a80c2a18ca030733c896bbf4ff052a9c891dd968d88e996871dc7345d070779925b2b8d6495196aca487a9e060ed3694b030ed3c8c22bc3cdd3d4a139cce354dd22448cff43d3689986ed7e843df7291ce339023bc24ed1360db037689a7910e368ee1b96476a8487a251a252769296a9928ca0f03039ccd9640c424ef43e06cb1dd124260e5d0daf5186dd25273a9440dba3b942739da21e0e1dd4a673f823596499dc6f19c449fc52992309da8c9f4ff2126a8a520ced2245d4251a873f58e30cf51e4a11427a873819fe63c1d8af30f11cd237998e4748d24ca140c45cfb8ab54ef8488ec1d297a8ef648819eb294749326663c1c236128ea25fe0d526e1211a33b14fd3bc9b7fc6d9e204cf20632c73448ea339027d9fe67a6c43c8940d9240bbc879128d0f3948921dd028a99e499ea7f5282359e52bfcfd355aee91ba4f8de369e68c8498c7033ccfb225aa7e98a234fd2520ae5908135912cb8bbed3705b40d12339baf33b43fb3c2224f17cd687bbc92a228e9ba234455e246c245111c653b457448fb4a87f3eb9d86186cf073678d6249113ea07291e43cc7445d863b8b2679fce91d2358733c8722c8ca50a35ea206198848c66b2521f9bce91ddde2363b89a749acfe812060d46b175ce2f90115cee79823a0e659cc6b40c1fcd6e71ce6e9ddde8924c20cce2699e3f9ce0ae8888e739cc405ce658ba6b3a4739651236a354a1da792242799e24a6b1e49c8e689738be17d26224cf50a3467b15aea3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_156 : Impossible 0x100802040000000000000000000 0x2490417fd001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=27) (code:=0xdf073c8ef39c8c9df070da7741838a1280c747549b546ebcc9984d97526388b6e91d2ff1ea659ba61871798da1b63a811aa36c4b23a81388de22a2407784a0c5b388e7425023a8418b6717487996d12a50ef65b2447c8327cff474e7388cef90f23cc79565313d519475aa4551d24d9247cc33fc937cbf43550e408e27f87333cdb18ce910b67a046bc1c9b0c5338d52047144d4a83936f38f840ba41f2399550ed55081ae5295ccf2dc7c3d4486dba506033a0dae74b3d1521684a9467a05077a8339f40fa779e70736c776aa0cc9136749ea8103895ca7619fa7f9028965c3c3ca1652a126ea3273a0e7c819ced40b0d09474e23e58a1cc1aa12258ba89136931d449893a243d3254a7708ea4ce67d0879dc4f2b91741ca52ea0c2594a838e677a1c1e5367a99e0e6a51f46d26d06618f9185411e50e676a8495f267174c923e7cbccef41ccf0419b66729c7738bfc1e63b310ed6a9ba7cb0c1752745d076abd5fa23afd26c890419d46326cf22c81150e619362bc951223a61913271dc8367bb4938e2399de1b4779f8868789e30d9ed511297a167f902dd02cca4fd61a12979e7072526aa0e6ebd59625e739aac54b50743452bd4fd74c0c528fa4f87720c7ebfd271ab0b44c637a9e63b4dd067679b6779baf5154204ee3194e118d62a816c830d8fa7110663339dea530e06990fb368d5196228c36aa1c22a0cf518cf212cea3b8753cc3cd0922a1c635086311459325d20bea116cf529c773a50201a8cc5b17de63188e7388a77528751ce354213156a992819646a93d314d9e6769e5071ac3d60e8a873b3c2399e73b2cf34da04354b66586a9b45973835513228aa2cc0d0f16c6ab250e02cb560677a1d1739d868919e7703bc55b66791d738228d631c0ce7206419ddaa23b0d04f17b551379986a52e8474ded5154cb0b2355ce7e97473a04fb1ce9308e99ecb3ccb27d9d40df1d6aba43ba028f9f6879ce838831c9267c8e7134c544c772271f24c3921efb798775351508d92cee73a16339031d1d5d2a514a2b8be238ce23a1e6398486223b54c53b4b27d093bbcdb3ed1340cb22071d404dd20e3919f0f6a873c051d4090f23a839f66da06e952bd413daa769e653887b3ca57a82c9d50f3d45d15ca7658f53cdcec338883a16ef3ed1d081c748e2b86e338da3b90387b3c17e4ee7226db0e27d87715cd51f485a2edd819271f5074181418fc9cee53c0c1f31f9ca57134041c41744c8393c3db643d1320c80a1687bd40ba771c4838da4c93a3a85c0dde07d89a06670ad074edce1070346c08bc2e6303a79f695a7e9a97c988dd4741c38a0683a4c87c4c89b9de6a521e659de529062d992538ce79927294671660606722ef34054b0322e77bd5ba46c49ccf8da4b0d44cf33d5cec34c9fc1f2d7288ea1c8fa35d26858f9619ea0e50327c933241b5de3247d43c73caca730a1c164939c47d49844e670904320c9399c1ccf73a1ed71094747d38b0c133425ae3e8e63fca60e85a0249dba81a3a87bd41f2498e4faa106d6b8de508fe3b8e63ea25aa408e71ce499f48740cef36c8906f6ab5c8ebfc1547d1fd9e30902750897fb25d2038b3e0ef5224550fe449eae7047462cf4a51f36ce20be71738de449134ccee1aa7e97d26d74ca2c7ca1a6287398c8ea4c799bdaa12776a247d1bc3fa0422a891fcd6398f2409de2b8cecb07d3ee2a0e693a25aaa110279a024c8b23eb9c716190b3cc20e2e93a3a354ed474ce64898c1de7033ec0dcfa9311719c6d175323090209e67389dc0ef0341bbc1330119c7740872498ba0772e8ae7f448c22267712d0346d433a4f338838bccfa0d68912744c73268ee7141809e71358ba8377b9d4a1dc2264b324e62e8d60ee8abb53531495145fa8ea243ba2c1f2798726d3b9169301c97cc5499f43b8fa990778a926455f28d99e61932710713b8799dcc5498cea50f3629fa36a2a7ca0c44cf38f9268112730ddae76b8d71ae930fb351dc834546f04b809066b841ccb42dce749c4631fcef40d9e8112767b7437833a2e858e71d27c5d30d0f35d9e42dbad5106174cf19c470e50743cfb0ee27b5c6309eef4c885b9cd7748832088090684b9ccf43c3b9d2d740a95eaa301264fc7cfa999c9928088aa1652a64a31157ea167c8a620c7922531284c942d1d23b014d84b4613b992f9089a2a3a1e992908e30152b55de1431b1f53141d2109ea53f48ec0c3fd0680a068f8ff85a2a3e5023f53edd7a9150a143e2691992f912381c0480a8c43b2df610193a4b23375154c43551d48e06988a632d0385a02ef3e46743cfb0997d9f2839266a83bcee994e51747c44b550724c9b8184f15d1d1273be067d8933fa65213a826c8712606cb3390751859224ef26c9c9c44b1d49321c7f06f41d123f9031d3e6023eca30d63f16c6741e1ea50ce8a9234340a546a6ccf2b2631d37452a6421e3e8923a830fb1763a05b24cea2f8967720d32338c238a322252321d3f1565a1e045989b48327d1d24641a2481a4af932427e3e9911f26e47197e841b2c934ec49a94fb4ce0eff1397d8a9a3a83ce4d54050f37438be45d81883ce50b27e2a1c427df6f91e546f576828bd51d374454ed30a0d090e28d1aa10715109338bad51d44930a1c426067d9ea32cfb40c61769fe8e9f449d06959da80a04791da206836a9031b4771ad0b3eced102419dacb43889b2cfa891960cb3890e7726c1c596898091a3f8710ccce425021267126ceaa53e418cf5849068e896869de44c9f374517ca06499da1152c8928115c511744b1b46524c3887a42d1544d034083d44c054aa308aa0c7724e367684988a408ba1f8be20689a164f16e0211b23a26cb3a9dc3a9fc2265196c3b3b8867f99d4a997392940c354f984b9cc93f49ca0e87bb4992027a92627281a02f935444a26808e286c241ac849f28117475144651f4939ca42f57388e89945cf5476160fc59468e21dcf58797c8792c93465daa508d355ce76884b54ed2161f8cf3111b2322e40bd4fd3e60687024b239c8ba389328d81822607312327d7ebfde63bce720c9332c3b68a9c93e8ea3629dfa40d8a0fd419362ea3b25314711f4994489ca8aed31447dfb1b2650d47462bedf21f2fd83bfc62a2210703314f31368198a798fa891e7076a9030913373a061067d87a62ce43fe528ba3e47e1f031f6508ea32c55f23ccff3b48183bd5d20e2a31dd23264fd038a0e3ea4d1f485aa1e4f91445d4c4997e9eb0b20c94a2a6aba513089629f23894a0bf23294892789bc9452a1a9a87b1b45d213f5ea438629c50b41d26234fd308f92343e50b7e91a49a668da526150bcdaec7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_160 : Impossible 0x400802050000000000000000000 0x11417fd001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=26) (code:=0x101314809fc40463314c2f91a479202ef1b4258628823d0db3dcf339cef809844b082791b480896713b82f896909dc40e3244d0312d1f24d3180862939c43b8e2dd324fe3ec6920223263314ef4c44f2c8d2770632ca5a6f09e71448dd0318dd033ccee378fe89c04ed42b1c819dee90ce83081ba54a01fa0c6f4f8fe196ed44cdd1bc2fa0cfb39d8f092890343c658ce418c64f9ce27c4f90649a564b8189f93c24e27d0e965a266e8389ef031dc9da8d1739d3e27cf314427ce23f9e72529a858fedd7c8f30ee93a064493e19e1f250fedd0b2e96d87ba026ecd5130c52124e7d9c4e90634845b95a1e089b7462108ce7d1e46b1c461135e6f90429fc77184a3448d2262f720cfa1ddba13ce2ef0d67386911c50c698d8d644e064990f31906771138fa9c80b9c31a1f273f84733b6c81893be4473ea32779b54af118e3ccf9498be8b90a73a066d8114f30c64b4484f4c4dd389fc931e40c9319fc93988e2339f40b26dc04dd1f4c638a0c499b54adf0a54048242c294ce2d8fecf0b237843cda838b6593ea266e851418351dd4aef135389ce678f73bcdd33d469f0fe44d038087f418fa4fb6de21b5393c445ca7528fa9190683a4edb6f90945d0f18d39504164a59cc05f2f50593fa021fcfb3a50737d23389f28b1063b87720c517c9ea1de027488b0617b9da7d9b6649e63ce4252838a0e023e9dc10b3f4693b906dd308719386180a4c80912418fa851e646a127bba58e36c36c69298f515471418ee3e4dd41d268b3cc3ba264f9ea49bdc3699e52a626e9f2a378893093418ce2fb1c7d4ac389461f2f5419268b6fb5c808b67a8269446e94af13f8e25384718c404593582145964a4a8c94e7a8ea6ebc432d93013e4c67f1c442c4f7b8f13d5be839f283778ef0430fcf71c4fa11c67224c9359def120d3e041cf744c96f1404ef48cf938bd48924685112c90f112ce30331516c3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_161 : Impossible 0x100400802040000000000000000000 0x11417fd011000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=20) (code:=0x16c7da0e3c46333ccb7bb94db22a838fa4286907d8fb154298c3ca0d12196637bb1c809e2638236462eb1d1522a718fae52f8e5679ee3740e622f117c6f114db07f2ea1d0126c196591f4c280b1c71a0636cfb3cca340c451a5e222e21808c24450346b947144c24f91164d890926509f2f30f943d1b424c245a342862a9b11242c058e43d0136c4058e9b28dca45c6722dc67ba16d7024bbcf246992208f741c1cca726dee83c443cc04fb0f3097283cb96063ec1fe364a443878398ff3b24d1b988634a53151bbcf30fe7da864db6c449cb037887d35d4938a943c53e6d8948de5f6389f445f209b9c9ae87a0e42b1ccf3dd42f5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_162 : Impossible 0x400802040000000000000000000 0x1011417fd011000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=11) (fuel:=32) (code:=0xe51da20eef3b50a4f91679945031c682c44889cb253dc3be0e1b469729c610ee5214df23e799ca691db0328863bbce34250b888ed39430dda729ae514f5ee950a531dee838d282905779c67988aa12856f88510a43936c71f622dd0857b9f6838da6d9de72bf4424859088288b141de3e1f64fa3e899b427d0a369263fc1c0da87295de0a6ef459e66b9a58a0e6ef252496063394e6fa6c3161e0c53dcb639cacd3090738ba4233b5c8b834b5cf362a068ea16779b4a34abc40beed8c8c68994a295de36909226319de444a738d4a3b60f1972872a326322dbe7b881b7c3e91340ca385a6a8a906f7089c7d8efd444f336c2148763bbdba294ef788d71164284f8ce8783a06f1374a5629841b5fa1e64fbb4fd8c8fd62a4a1466f8c418d4a348d63e89e0fe65a941fd96229f50ae59882c9fc3f1cc188b20fe6906e5d40c349962e98dca2145d165b6192169cd2a494de0dc6f36a6c8b0ba44d0b4aca711d2e9b5921967bb246d02d97457659fca721e1e07287a14734187b8da73031a36938e5153f974072f73985702765c3c4d44c4ed2765a6626a26633f94e37a14df0da1f8e60fecf8cc0dca18b034f87f09d2d13e851f44745b0c7b88e20640e2e7f7287b9f4cb2153e10327e6a391a50f17ddea305147483429460aa2ebbc2a8ba8316cee259e63ccdf40c83215b610f77a2e8aa0e41cec44cfb28e76770ee2071749ca71f6773f8e6308b6279e673c65caa518a98a3a82a2618a2e90a179a41a50a6f1dd162266d1bc15cee8f9cea34f8f37b8fb8786ea15b61a4e772b5de23ec7d4c45d24a1151fe1e7bb0d130b2834750a2ebc48ea8c19231165e27703bca76496cfd78a1e3dd4630a543fa4a1be4ab24594da1edb0ef7b82ca26f711cdd41c2ea0de28b011d467d1bc61175e243a7c144fa0fb297e94683877b3c81a270778839a6630d432e8f751bc4619282c8c5070b6458cb778c38785130c5d3fbdca326e62e50a549d3142dde44dee7db1e22214f71cca321e4187317c6f1ddae35dce8b1961747f22ca3418b618b0779c0c1dd965298651a2e3edbe53889c65ce1158ca63133ec4950e8ba6227916319ce528ee5d0229f62a20f3b1dd192094e2786328a14fe05d739fcf324b0337c3f8d2fb4d9aee508e629063790a7d8371ee2891340ce732c772566131a8c6f3e82f916c56b90e9f0b64d82c906659fcdf22cba1fd0a6bb6e1224a241cd36369de3b8d630c43a0f0343c2ca827f0fe798c6df0b6309a43793c7722cba0ef8abdd17518831647f3946929d0a1b68516c51184470743128c144d6ef10645d1320d0a2886313e0649dcee55288b39d1f0c39d9b69b6b85936c8b3f4c53bc890c531dee778a3788c74386b3f8a2539be3bca341893a62ef1dca306377b1c6b0731a463188c2658c751cd437d8e206c7778de6d96512a508937c4f779fa629463f85b1a4834594e0d28fa124190edf4ab0c45a3e6e8df859c66da767b88ba624a8d252926f162b5c1af334a9fa6d8fe22442917164fe33a0e81a127e892db3742244999a55be0d23a9be5921442c54a50d60c6df428b241a24dd63a6d93010d2484439bea2964a27e9363b9ee21d2118e3b9d43b9a4a53083fa2c6d14c43cce7e88fbecdb3cd3d23ef71ba45c2c43bbd8e0c645c65256f984fa1fced78830a0c27cce0c26d418348867d1dcd74591320e064bd153f887b5d260d2d722c8344d46f162820dbec308e349baa535c2d8fe3aa7a8a89a9b116c5808491b5210691f4491d5be6b8b63390e1a5ca1f536510860d2f74449328c519dcfb40d8a14616399de40d36f14a9092947d1345b09a878fe2d93e3e8459f48d72c444f9ca3ea3f3135c21cd7394c27720698c04899da6f9c6145ca145ba7986f8dc7d0c7649de798d2259843eb940eefb64896f110b2b91a348ff010ee83528348fa39a02465be4fc5c62bdc7893eef03591e0727113789f66f9ee77a027f6187d9ee849dc4b232690778f88fbcdfaf10e6510aa830c28d405aea344be40dc8332d0319c7f3183bd8e931fcee3bd3e13477a951549c7731c871da6f9e28aa6c9eb5e020f9405be7287337d0177b0cf105f40e368f8a2808676f87d97d8e9b0ce7cb5d2a242e32123dc6b87e777c936839033dc67084bdcce39be4a34a98614a7324c7f1dc8777bc4db6281dea528c85639ae6fc042fa264d9aefd394879f4c50da88a322f8a22c98a3f88542d271bc5f41c2d90a1585927ca33ebbc7d8b6659de3e9fc64b1586059144fe629750e0598e98a289747d254854d8a321422946419dc5b12c3190adb0357799e2d9e6738358089ee552827a6cc56bbc46183f9f5ca4d9063b98e52a0217c8d16c144be2c9cc8307d7b9de8083085aa5404ae7714a7f51be51279131405b64a8c336892a3a8dcd513226f949d0f0f75385b378353dd063f9dc0ab317cbbcc30ae1489592d862f8ee6d05b379f6957887bb14474587322c1a4e60ee79bdcdf7c91b6d9861a45f10c7336c510869990a6f13d16f16b845a0c773ec6f3cc3686d35d3129cb665b0d3e1e645b5d0326c4da0c6327d8e713d47986722cef2f8fe6d85d4480e693a9e32ed40428993150fe7908e6907317d1a3fbe4778fe1fa25ca324f914cdb39c79876378ba64a258e0fa929da46be40e7079a817462fd43ccf7d844a14de41e261f67303894d26909467ea2c673dcf31da89116877c81ce2e691e4cf28c8b85192e26879f6f94abc40e37e9f5f291a164384c61651be50743c73146f146d16df07d22c8749a665185f3f4890553b8f27e8ea349be3150e338931dd1a44d12f9405e6c71fa788e6093459c4c77c8a291a0edb069448e3131a4a32ed37c6945df2429191a4890ce3b8e60c2c79289af92151a78b95ae214428f23a9eefb1266f072769cc691da3c91a348de672261a8e65308dccc7f8391279a067cb7c3fa022247f0dde2298733e44f225bedb1f47b86e3e82b9144919c39892278a67c8cef77286f6d98c4284299c871ac1fcbe44856454ce31a0e3c9148abe47122a4294df618ce506372be4d736ce73e885a0e931448917d036fb1d3621e1036f92a538d28da43298084cdaf29255e3074e5191de858a345cfb4d49b19c7724d21045a8c9e338ea878393ec0de26bb3c4064e5184f40c7d49db66b84a51a1fd263787919d0e3eb1c38a546b9b68b6fbe5ea0862c90f28d122794e3ebc433887c1c43d1533cb2ef1de87bdc1a48783a2ad712b83a26378899bdae1c5de43be46b8ba37a25e264894964f910b7c912819bc7ca1e239cc7d07113e2e69069809e27e9927ca1c42d92808e6f720e87a067b99dbe232f92248719dc68b080bbc577c8f71f5231de0723e95c6f134597c859808ba34992730f73f4de248e6878fa8b0c9959f2876fa5586a1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_165 : Impossible 0x4802040000000000000000000 0x15417fd001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=30) (code:=0x1f27707f7ca53251037fa0f1107d75aae1a666a6a522eb5d0f06ba5af743e1a2bb1f3f4f9758f98888d9ba8aa0e5913c349ddca222ff30c4a4ff869f28ca04888ff0706f4a9063b8fa30892c55024963e61bac83bc606c903b439034094e308da71839a04876b91aa105f468ba7e8da3c9024ab1c818a74e4731093b9d6399ee3792a30b5cc35091573a22719ba0fe61a0ef9040b0ca52d8ee36a24eb0da7b94128477226eb424937ca668bb5d0f788a543cdd1a48b0d290b5c9f077799066b8279fc379d68b3493e106eb28be405f78b5c7313c77348da338f23f8a2a1405fa71057759067b93e1f45b1cc79a948d6e8a56383bc5c348da8b44c831cc4f9f445b0ca51067f87e9e23898669144838fbe48d6b8f71f4ff2062c8c3399c67f90645888bfcc36e98e3bbe4eb35dca034bc4f91bdd604589f393f9d669728f2cf04d679123ba42638458933b9873911cf719cff1844f1cc7ea25f2288733acc73948946b5d4218425f311272fa4af93bbc4285f2718449f67719c6b1254a8d62f8b29330c2f869084fb3ba2c185e68378b5c848b244916dd05d35cdd3b8308ae6b8ba774184246992bc501374a14a98622477174a130cd70f17e8921de06809a516eb1094191212548512fb1bc8ea2a92a467ba428b20dd61fc6d2541cd123fbdceb1e4fb19d8649b9592a30630e42f27d867f89e3892a4d89f3fd571fc30cc64f85945d35ba0cf26cd244898bbd1d38d1320c9f1bd862226927c3cd0644512c341c0ff3530c4d44c8316e2223b073fcc33192a4f9f44aa1ca2057339f48722cc32248382da24cf889a4c207d944e63fa1c2b8fe79a6cf722ccf50b947789794228c85b6859863487d4ec1a54623b073190f3110790a3261051084a341c9b14e3aa172bac44c7775b5c7b92a3bc1cdee77a1e518fe458519163fc5e4a69448731fe4a8b24f9f4929ac39a242ba6e0e41c7f1de7fc0c8b3dd0f28d9e1fc830f70f734a250f3bc6b1f46788b0c7728c87718348b239a7c1a5f62249330c6b1dd47173cdae3bce335dd6f1116909070791646a308674d887458d2db759ef010458fe7e9a6221cb3148422dca7b98434c047da6b75921cc5133c1273fa53193ae9a4d8d214ec31caf538c9b43c5507f7293e298a733916693ad9e3cbc4d71ca42cc3759016e8e534875a1c731a4c32322ab749b1367f1ae0ec94085126d116380fe39c1cd784b94a333cc3213114a4c746a1463a42809026499e7c9ee27c7d19e2869b94ecf14edd41cf93986944892b3cdd3e5ee0fa81498fb1f54621e811ee338dd224e6518dd3ec44fd81b94495f227a0634a6253a0e3e90a3886911199a064fa4649906813f5051c5bac7146266f33dd0f029a0485a0b3c1f663037291140cef27cfd3dca36ea0af17f87d8fa771a5190d285454f110b0b0f3030457f9fa8ca2a20c399168dc04f33f44bd31809fa8fc546ec1db61fe87a0e8577840c7ce315c338451bc5d18c693943f8ce8192cdc40c1cfb12f9ba2e060ef03404f13f51519e16c90ee378f21cc85408fa3483edee77729c6448428821de02839f62f9dec9908856392d3899f1d1020c84da0471428e61cd1630a068d030902db969e21c419dc699a168121ea73c6063758f05034984ee0693b98429c691f46797cee1f4b6813384851a771b66931c6f3cce3184e226e670ce64aaf2528cfb0e2c70d240a9e06f9758399461cce281a3419c8b758929982e93e72a4239bc4db3e454e1e43e0a7da16eb1caf76788abe50363a05ea18428c5d729b66e98e690ba759ba6dc14639cb1d4847108508642389e612069789f23ccc96e8e6299de770ee7119ce71e442d062c8c651926cf04951979a2277bc449485ba82a727aa2a8ea1e739f271a048f8b67aa42494e614e7781871449920e6670cea740b6d4ae909f14a189c519104f33a4591f30112cc9184856e885678d2459ea1c4f30f92b8d6299926ea0225a7c7c9ba8b3d5ae618711bc43ce26740c388c233a1e8190343c837c9dc1dce97ca04848fa4283f9fe7ca0a779dc41c351387a4e83b6c8694a42b74e70772045b1a46f19c6121a2c9eb0911f338b63fbe5b6f303b865e67e8d20a740bcce781a0a7f819c5918c2d408ba1e9dc2e8f2408c619e061e9fc339840fc613b8e22c9a5b642c04212dd3f4ee2b8fe01dccedd9ba3a93a05213f5078187f49ca520e020f32d8ce7741c6322c6f184856db241c461528de2583091a428d2388fa676d8710fd7ca12519dc338bae7324f50de34a151614c8322c8540b5dd603b389127f22c7711275a2a40d0f3adf204b79c0c9349c6320e123b9f41e471809262068dbac12e06f343df2a54441c513205273fc3b984654260213e268be348b2188c63fc0c5b24ce71dc854e4a53e842dfe3f8d24590a41c047d39dd6dd053459013fd0b0c2419b6f93ec2fbf4ee519e63cd2642b5d8e99) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_166 : Impossible 0x10802050000000000000000000 0x15457fd001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=23) (code:=0x3a424cca0ef033dc351d502748fe7e90add032dc692cc45941e1a24a82b6dfef11319aa0a4290778a22df21a809c60ba10c34311b46b18d270fd013a5e2679e67e844456e308ebc4dd424fe24dfa13501938f129cdadf485de08a238ce298da899de319f40452e8c64b3f8c2891262c87f3c4e9a0b7cdd6d8809fca71f40de891dcfd424658883ba24931fc7d7bb743fd0179b6d8ea50c61d21fc0c859c66d98cee2a8de41dde062339b6633ecef638da3bc3c5dee947c6eb1d210b631b6c6d3f883902831fc8b0e949cfe319dc20e0e3a59e2da1671bbc88a0a1fb1c4c5de318da3a83b98d02458114b277134fedd2f890bf43bbb43aa12dd0b2df0dd88a42215da2d9443bc89928ae339d208a7499d3e36a0ef102a99d0618cee224632da04faeb0415966320c8127ceb22de210a262f1404fe2798c456028119c42a2dbe40ce3117134813f916ef32c838ceeb6eb0c639261f431cca931e642a0a859d66dba4aa3b8294ee35904358ee8921a6523e09a49985d2288da3586121455448eb214fb2114a4990b017e87d27ca324c2aa2de2d7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_167 : Impossible 0x10802240000000000000000000 0x15457fd011000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=20) (code:=0x3e5098c9fadd1ba5090644b949299e125f2888a149e060d27f3b9252a8773fccf37d07748308fe7733c85284f324adf47d077681a516e91b5073ec45a85011ddfa112770ee448b23688e1148b3fa63030c2752544292a4060688a4e1da773f9fa309cdba15ccf3dc50a4a9dc1c45c44769162ea1288892b8cd23a47da2511424e618c891dc6942845ba5064bc4d215ba7f041e4aed1a542889ba41bf5caeb10a378fe458ce062571ac23a3293835c2c633b4dd3791281196790ae85a2e8510d45501375027f3f442dee759ba278fe2fa2dbe204511a4850348829886a5739a24eb1acdd092bec8ca6ecb0ba9a9a42e8d285448896e9fcfd72b0c328224f185be47888a819fc035318d661428ca7e9063f882449f2dd3b9be10411c5f28842bed0d3f8853588197de226af13b89e89186dd1b442882597283dd0a44b74793ccdf63a9446dee7c9e6215be215d647c851eedd37c733ac693e5121dced0818da2a34b1d17116df0eeeb74826a4ae95082a883211d4793a41128b7b9a408b34a2475294ee35857185071f1ba2e8ea328d63488928a143cdba74a4c1a4e94489a41bc4458ee52a92968349ac77428e7010d224a5517c8b23eeb175173b87ba24e6154ea22d0aa17e92ad7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_168 : Impossible 0x30802040000000000000000000 0x15457fd211000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=25) (code:=0x43cef1b4fb2721c9b137151fefd01cd0a4393e2189f253eca77f936890cf42cce43b8c7788da427793653b6dfe86a2ae930c1f59e27936424cf4dd0749cfd779860fa67031c9ca52d9dc8314a49c7e238ce509cc93a1d331318387d295331cc671d45f3751541c450611f512570574490ea11a4812da6c99a326e99e0696ec9e8276a3a21d42fd818679c6839867d057428ce528fafb284e914a61a2250912fd00fa42a568ba24aec3424e6ef0892ba2a0cfa09f4a7174451e4a1184e629495338893491d40a6e1ee50da0c2730ee28a141ccfb8e89e890ce830e6a70c63290f18d414550d13c83398d6239024c54e1b4ce7eb0dca1f6127fa16f704d8c68eba6226e8f71f4e94088150a028a9b64a8e941c490e685883bc517125369520281b6c26c9e81998ef404e548c254514d8aa498bf1508295ce6538d68904450139bbc4f318aa86a16394ef4d8e51f4ce53a961e23a5709245c6b434c6339028311c778be509ba158a117ce653906204ce7d057398d671a1c409df1908380a94da1f44f24c5f20d0b0db809ba3ec24419ca6eb0c186ef3c9ba3e9b442cdaa10e93ec7436ce6419ca404e58e8d636a242b9ba3ea3a449e2877eb7c0858a8bea1729fa768e56e9e2144a119c7717c490ef6f9b443c34591cadd3e834a9c1751267a0e3b50d444f117c7d0839ce3a8910f82ba43e9a4f37296434b74728597694e2e9e244889748e579a05360f1369f43967a8ca4a3b43bd19879bef738d0a8a8da8912b124db0107294f254650144a04819ca79b75867f) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_169 : Impossible 0x10802040000000000000000000 0x15657fd211000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=30) (code:=0x950ee47d0b81b74c72850d36cf1206368d7509e2279ba34a02398eefd0a115cdb3e46938d0e21d4a6e83c4fa83204a175840c0cdd619fc1f49520a4abadb62d9da7e9ba14a7d254f9374697286950a6c21c793283e5e2593e84da1a791752a186278b27f18e613f4eb254794490d08740477c44339452b0f202c706333a2c8122299902dd10111c919f4fb1ce226d87d7ca3e40bac3c52a6d08780902202954154542447c811f5f26708e630c68b6e9243c4fa6e8c61f516409fc43936758538ca1fdd70522e025d18ea502ab0d0206e874a9d6889016d94a6386f45a244d89e319163682f8ce8b1146d3e8f31b512fd04319c95439162248b7b9fa52936e53484da94114f2378d626d8630d1626d022aa2426c9e4490e651cc1127ec35258890214a311130d1b481809a43dcc35061a4088ec5602405fa112fd7593420469248e63689b42602759da95202638d60e52cc450610e3c994439b49a133728c63f9d7113e8611b51611121dba9b02fa2c59889f486a94d20e51f9062e8de3aa6c471548b0431a536871ba7d4a81f9f48321cc31fd02678183505f1f45545c2ce50531acaa1f2870be80b0c3e586d7067819b67cbad1672bf41cc8b1b4458568161836bf5d62abbc3acd27c9e66182f9f27321c6f0be491f2e5409fa9b07e88a8b21c6b8286d2a8ca8aa243e45f10c694385f11ce348cfd1f243758349d6434d9fd4218e50c3485896570318e46e5f12af722c6ea32919f222ca17e92a870833bd8e2183e435869646b25465086693f50e12a3721cbe42dba37a6c195b61018da1d8e728d23682f98c59494c7374faa52161f237b1c5f374aa3c93631d02216fd45b5d26df2624d8436198e6f89b18c5707f15cd26f06a6f9d68982b90cfe4f8dec31351231c18c69528e63a8926f26c448a5255157593635b7c3bcdf47c6b2b9fe8388fc1dd6c302cbacd261a2dba7d90b22a22c3930c44d077793685c242cc552588bac22a85c460622c731fd4577b7c4545975bcc424696f98e4593e9ca3679bdc22d86238694388388e6f088c64b2730e6df0d28b1eec71ee5b3e87d1ee2b9d65931c6f418838b6459bc30e1e23916730e683448ff3acc718e5340c4a99c5293e418d2254ce21e7b9f4fb374e70714a18657779ba639f6df3193118cdf37437494592227db0c83083c6551424dd2c9093ecf71df0749483bac6fb0cc67d3fb94a21d65293635c641c6ef21c9b3cd0941cff8884944d759ee458574186333c454137c31c1e327d05730d21779360efa3a4e289f4c308e8b1d46f12338cfa8ca1c3e9a442e4e9b47dd60ff729dea54546947d8e1f44d8fa2c8d2778deeb30d0921c7599ee5838638c722c8752622eb6f83bbacdf7987d394df424691dc8b3bdeedd308eb1866326ccf1a431d0e0c74394cde21cce3acf337ce61ccc6424e53ccff31cf735cd61e6df1cc5b11ceb1fd361bce53bb750220e8498c228c6772548b07f3de0e77a5e730fe5702cc262a77a1c18cfb7591226907679de309be3ea6d42232c70c3449d6e538c81b742628cc75410a13e9127f0c60e4372b8fe9b0ef3e9844d88a81077a84612ca1c40a7dca3747d39419c556b8fe31cc44da058f0706ec2cc340e2a3ae128e8c73f9097292537509308318d6848d4339264d8e640dd6954090315cc322c9542d42df7683f9ae891c63f84768aef484e66b86db7d3637d02284c224edf36cd734bac18dbe439e6418c2c70c74d895424195363992aeb1d6062634d8c2896f9c6ed1270ff318fe32a12909a5d66b90e09534a12eb0c2ed22536dd092a6c2ca0a6bbec933dc771acf36388e9e619cd7759ba35a6db60b2df4b46b1dc4d484c777a960222677b9423a829fc733ad0b77b7cf31ca771d68b09a1bd124f89f30d06528ee089484fa6194a1d41c38c8adf093bfd126f87d8390ee57783adb677a3a349863edca893f8df0cf728169a5122898d3640c94d713667877a0eff21c84a3a34a6dca41d093bdbe24ecf44cf337ced3ed07758759f4877186937ced475ae951be4da4e77a0e36dae1be9b42c7f7683f9de311147752c05e2242eb39494a428588b348eb2b94a779f5090e53ad128589a5147c1b64fbacf390b5c828769e649c858e1db4929541728ef190fe4f82a08aeb45ce5448ca1163ed24f740d0b35c85c7c52814ca523c947d48cef3dd1790b1c0faff41519a4a068998684b94c2dd08b8c9ca849f66db7c758613ad131247727d1d50c6b4cdca8f8379164da3e470d4df30c639ac1dd1222c4d295ca4f8d26f9f472c25bb110ef2b8aa34a4227c33d3e691dc8a1d6939f681b6c75b7d1344bc40c469758a2308fb0eb8188b3990635b7d130d287916d744834bacdf22d096ec0415c8779a2e07f19bac576d9861370b15cc34d5be3ae0e424838a3d25d6819371d0628c9fef772a85fa8505d215fa20e87b6ca13bdca10e8110c5f062839ca409a45d22444a2240a15be0856f9ca4394e8978883bbcdb679033f507414852061a536999ee7e90326c631f4fd42b7446cf988902349420cf16cc742c6cf3285de1a529285fa10e539fa4dca4dd3e60671839a85eee51b60694b5216db3dfa7da0e1fb43778e57991f216067ba16f17f92524b0b444103254db6d0727d191230fa37c9439bed0b3b90e83a06ef08aa04437199ef90fac7082a14fa37a0e7b8d21d9f6458854188b204be4a5150ee888de5d1f69290e348630a4fa41a14fe24b111f690a1e7b9dc88a0a7d1eea141c8326f0377877c44cf24b1520494c0c99c1c694db943be364cc8348e028184dcab2f8aa0e46c8aa363ea17492251f24af9678908d250a150372bf44f8611a4349dd160ee6142d061a4473f93f42c9f1cc631a47f4083e9a5360de891dc6121c85a0481a1634a6c829f50add22a40e160c734a6ca122c81464103153fa228cc0c1650e83a8641a5e31c7f818734b646ef2070b82842c751f42dfa2848b2048aa025099c91bf51d4450b47df2df758933e48b20a79926c720aeb1d68aa4aa10fa969062f9128f93e8381f4a1a4a0edb759ee075c7cc255638837c8c76f8c749bf43e9153f5f21268b20c856fc2c415d60dd0d6fa367e88510ceb059428d23c9da40c8c8900ddd6612ba0c9363a6dae1be758fa8321c21cef6f94e3ac673b89a3a8e51dcfa2d964691de8089e859fa93083104eb80a247d843dde596f826dcadf3ed031bc758fe7788a140ef499ca438b6791fc7717482269034540631d77936e523a8a8636fa06379fa758b65d44bc54ae9) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_173 : Impossible 0x802040000000000000000000 0x15557fd001000000000000000000 :=
  checkChunk_sound (initRounds:=2) (rounds:=8) (fuel:=22) (code:=0xc6e520471081394df51b5cdb07d518771f5d63f901818de39a226f99628e1237ce21da868523e99f2b404f335c7f1bcef3e41dc9b67996799b629cf781884c0cfe445dee506794a3e418ee808e66bbac439466b9cadf40ba440e4a30d0a20d033cce23cdda30c3e896729063ba8cdb848676f833a1af30fee540413d36d70e23fb3cdb3487f37c7119c7d0ceeb1cacf8890b40d1f35cf70cedf05b6ba8df206936ce641c6c809aeeb3cc53937030e71128c86c2dd20fec315c831acd71dc0573b88c3b1046b419e63485e37d8638c7736cf30aec3728db6ba14618ae279e67b8ee46c8e1dca336dae7144bc4404ee3e9ae28cdf38b1c31833c250181a729a9fa0ee717c8fe4c43f46c670f37ebe50b0b62288b9c6818ce7f619066ba0463788371c4389fc6119cd71bdbe21a7f35dd608120ca395bc410915e56df4190251b0ceb3cdde23689a2efd49c930e2832260d31b18cea418d607d1c473133390344de67f35c0299c4373347cef18cee2185b1c48118c97a3f01202e721b273fbadb60eeed0e21c4fe2c8faf90c651a066f9d60c2630f4185f2769d673a2281085bfcc6853b840d1b3dcc27749886b9dfa075978ae2f8ce349dc7c9ee759ce339be711f2893fc044e52d389fa10b3f526771f4817cb5d8e99) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_179 : Impossible 0x10000803000100000000000000000 0x10017fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=26) (code:=0x3ea3c871ac831cc7b28ce71a273c148a91463a0a689dc508775189234525478f61b4814f843de62ca3c2d9d235d46368fea14248a20e4599e689ae84a5a7ba3c40911494813ba12228ba2da8c18d1e63ba4aa11e22bccfd3dd076f8929e2550ee9f147093bc50bdce912d61b7e0a18ee90f320c8f9290e1e8b20c86a249543d9461bf2d9291e7e90e398738aa84242f33a4aa3fa2a04454592974aaf33f58e399dd1aed03fb1c868a8631a2639e673518f747831e02a323ce934423c4b318e67e98eeb1da9994674a5a789f2829fa8db7c80b8c2b8fa80b6c7682c9462ea1b0b638fa4b4db41cf13f63ef32d83b4af0f404798f443d01799ee778fa2ea3e89879cb4809ec5d1e47d234b2c72027e8aa7b91ecf3b9093ed2d23cf741c5198efd1fae918edf084c061a8aa6668bcdce3f4e903190c4f479463ccc728cb7110899a2573e5463ddd2771fae76b81dd4673c3451b7c493b43bb5cfd1e4db3dd06a510d3ecb2228de22a5937cfd1bc3d06f3f5e62c83e7ba2a26c058e1fc596d9060c68a9350118e6f1ac8321a18c6f809ee268fadf6b82d9465718c6f21a789ee749de1ee9b1ec551e48b1dd3ecf20c3f887ba4b2379169383c95d061bd3edb0f2748869cc5d1dc7b1f41fc7a2c8e6a5798839ac9b1ec631bd0608a791f46d1bd3ec707330d163f5ee6fa12061917497898e799361a0f327bdcc737dd23586f18c8aa2284a1e859be35116518e6368de63c3506d70d739a566d87933c7749d3f7585735dbe1ac6315d113cc85a8c7708a9f134889bc2b96c5d639170176a140f4e74385b22cc3414f737812cdae720a7e9f611a550878e4f2309ee4d0572696c2696622731748b1ae419da2d91120c2a94a611da799fa80b447bb0cae2942a916789eed73ecc3415092e83dc9b21084c67751839c04f30f4651e48b05f63bf51d1fa2a9740fd2f994511e8f22a90d2c96c639fa798aa28d06773d81dadf15d362a98c2e8c6618862d8827b1ae8b045318b21b61fa92914f2779e6789eeed20ac32b8ca73086bb5ae639dc37d167b8f2828fd3cc831b465414e61e9bd0a951d214a1e9ec8f8082aa3c7b799c64f9ae3dc146c7849066b87ea8c7f1cc831edee92a9451bcd15102769e6495a2146d72ea120a385a2a84bdceb749546b9e67ea5414695155253a4e32ea2cee09f6391e74c54a5414176367ebdc7ea3641a266bc2451b8c84bac51bcc8a89fc1d1b14af3154ba4193e4051b63a0ad10593d851b5cf73acfa399068b7387b96483146d727c7b3ac4f88e954164fe4f8f635bde0e3ba123ddd23dc4579bb41dd46228e6798773dcc71cc636b828caa2386e6315c4336c774f9f41cdae6d8ee2d8fe7588363a4a10d3e799bc35c4f9e27e98cdb194fa13c773d906758e637a2d0add0ba27c571dc5d155ba799ce87807335c1d0625a7e99a4edb0d6e33fc419a277202e707780bec838fe6f0e63b9f4258e6f30fa2b9ce3b90a9f7e86d8fa611e4d1254731746f4048542424aa3358f6898de4282fbf4e7425068e87d7c9d247c8580b74174dd214731e4fd496021f485a02fd234d179a958e1bc590a380906a51f42fa0e2b8430ae73a94db31e02fd6fb2c0fa8715c6f619a26b916358c630d257ba0e0d15291a799ee7320e679fc61b7c8b07fb5ce64593e239ee7d057254d7398d63e96d460d63795c8aa1e93a6e5190e6f9136b9a2409ee7d27c3e9b63fa351e404759e60f52a329133bcfad149c51b3cf623a808734cd9e869fa7dc1c2345d1fc8d91aa54cda21fd1b619160d1269fc7b16cfa7da8c809a233c4d3e8a37d94a8f0631f626f73cc7d9eedf7383eb3c1746b7791b2548b30c899f4ed6b8957b9d6a32343ada27687f3aca33dcfa1fd1a8f3ec1cca3879d6f33b87735c1dacf3f8ed344e6a321c24acf3f90e399ec3f9463db7c0aa63114492f9ce7b8b63b90219445146cf15cdf3dcf67d5087b0551e47f7681161e0dc9f508f3133e98c2d9941d6a53b4b63d9dc3e9ac44cfa22a368381f4af2577a624aa021eced849cc404c6398ee8b09a398ae8d94a6f20218c5d1dc7345847542733785515c5b23a52872378ae39c34fa28c557683f48b013b50d475077d88095d2f434ed6fb5c435d673a3678a4e878319fc8b1bc731adee43cf722c9f1bd093b5ae0fef735d2b46d096f90d798ed7db0c7ea4a2b8733fc1cd1d3ad2727d42ed1db158391d6f8477d88399e8b6b839a926f9fa4508a6f22c9f80b6d0a26250839cfb158dbbd2344c24be491c3d333f4db0fa9d816cc67d3fa4e4f936998f61fa26c4cdb23a6dc6c31c9c8d4cce627d0907f51a36ef8a839c54df070e63784d28c5d528c2618ca08a518e6d1146c31dd1b0103e88a7f20c2f26c4f27c4b92986f31cefb093a67112670546e0e73b7d96e5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_180 : Impossible 0x30000803000000000000000000000 0x10017fc001100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=27) (code:=0x5efd2045d16cfb264455114ca623b99632d25335093cd1a4951e7d06142d966b9fe4385520c8aa8e3ba3426a1d9a1860a47ba4186cb1a477468cd47a0a4cc0423c8d669251dc9916c8323cfa4460286bb42b88d3ecc33b457368fa21c6b3d99ea10cf264e91ecfa28a92809421351a348ca85014a1c7d14c9932cda418c2888ee1dcbe134fd42c8d414ed678633da54264851348f928cf508db35c7d33c691ed2a98bc430e1a4aa22247154d495265fa76bd43d48f7492b4a94a1ea6799693a566b1b4e7184a525420a3c6916cfa4546d0f96b8d2953b41f4d6a512b7fb750606ba94f25727c671748f12a6b9f4309a4ee2547d3d887b5c7d33c9f0fa690fa7b4283db242086d3e8f61a47b4a88d13469418951a44d4c99c254a51eca19b95c0aa811b5ba7486119c553e85750818612571a52a7707d899d27e9fe3a513418ff939f6e76684959e7a9f419d063d8d23e9de3b9f2950771ad2d6b9921f49aa507d658ee89b75e2a31e621e43d277da3e8a9072524af30eecb3e88ab9c8891e469968ac3dd244c776e8fb4dce932e020e922c24ed1da8aa1288a347d5081951a6714a4688f7386565c247708d939467abec4ae4e8792743c5709d1a6794a43db67d11a9ba4eed14a348ee82a2214b2773a0219ce7269ea990999b89922a7d1dc51194fb3b44d93a140823ea364ec30673e91e1b90aa17e92708f33ceea520cf332ce724e7d932f506793b7476a84c37890f374cd1e67d07b66a84ef3c50e7f0f649c1dc9530bfce70c2fb51861324831ed3228dba4560242d33455017483393ea3a266b9f5011fe8d07b4cd9a6da8e4c99e1ed3e0fa616b99413e518fe7d3a473b3c5d99c148a9f28f885b9d1f19c77678e74ac5f405ba47c86438f695202a17e8450ca888ee8d0d78891ea4a54870fa3b9eca1878dd7a81e49ad7404671dd0a2148793251a2234a16509ba4d39c929ba7f3d5e28b0ee5090a19cf3284854aa2226a8aa466d7a8772223b9eaa33e54a116529f52d132f36487b07f325378aa0aa108d39ca11348f959323eba434a7650c0440525799323f4673d91688a54184ee7390613532a56681fb311de8292c547ea2b051fb091e70122ac9484a36ebdc4263e3343092a32a0a2e90a8a89ac9116833b93e375ee25602494794050d4247d22a4a9da868fa6ea148b3dd460ae3b8774f90e2db34cf0cb017e87d33c61174870324fa6695c7f1848327cee3350e254f27bc94850ab310f2fd093bf66b011168d10f4a99eed24e4f880a1c7727d0566c36221fe4fa22879f619602cd26e66a1e41a9488bdd05080c354a85748329d287b349f324953f542eb) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_181 : Impossible 0x10080803000000000000000000000 0x210017fc001100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=24) (code:=0x3f8cf0f22c8f24af702aa664a7e88f829167bbac3dcaaa311e451ee41c4d454ef0951684a2675a843dce7748e7284fe268839ec2f93374a3675a85163b9253ec21a6a41cf78d90d75c8c3b8c6284ce1ee88a3a673fc4c7da6e958eb45627010eb809023eba51e0ed3fa3675a841a4e733a0e2d9d67d0a1839d2809ce8b5190f0f4791dc19d118aa6a3f88a349922d85b3b9f532cd212839fe7d93e2c877455d251915909f2186e923c6928c7dbe60245525226778b2f73ac19d37749ddda23d0519c1064a26a0a21e68974ed414ff0ce8b8f9dc8a916e7115fa8d142458eb03f91723758453ae2665479461ce839422220bea143636d7345233bc34903073ac2db9d463ba2c44dce7fa0e226eb3dca31ee6dcb44346c45929a28f3e844d017ba3ca3082a02a33f4f72eb9c68a0299c1c1a4fe0427f1133f9026715c7f9ad0116469518ee1fced1245910cff3da851ae50066672061e809dcf710c19d2b346267f4c82699c6339d1a3eceb3dc0cf013a5ee759dd1f0e5839277596c1dcca3eb9d1e04d87a34e6067958c6309de7d1e4810ce47b9d46a5039d2441268ff246fd4550f46d077287b8a6348821991e3d8b68699c0e57696d0d3acf7198c67f28c7b8991ee479464cbc4eb27c75a92729fe83b25da21f41528e58a841ceb76bc4fb3fc33a92a50bafd8693428ceb46dca15d4a1072d946378ee46cfee5264a592bbcfa1ff251470d1fc9b36ceb08a9927d7b9ff134241fe263791608a2d9f46b51bbc7b9461cb0526cfe06783b0c7f28c24e7f6db94ff26c41d867da22f721a7bbac9a44c6d394a377bb5422340e70f7da0e8abb42e9fe6d835d250747d214dd2376bf4869faeb0fe4fbbd057486d8e6651152c821a2639965d619dfaa51d69da26228dee509b44d11729d292bb439a2c234993f50b358de459daa30eb76a8602850339dc7b2151a779e239c46e0e73bf4773bc33bc4fe0e67d3b43592b4ecfa89a0e309da8d0d6998e6899fa3fa6c214431a4fd91829ccc692149b2367f41cfd8992b73a6418c77369fa3294a199131351b42880c4cfe738868f7b8673f46910b7ea7c5b1fc0d2851f47f91a3c9902aa3499299dd1614a7f1b433a1611b7e9df152685d3f8c2529f40aa8f319de1adfa4f916788e623cd727cfa8551b74474ed508c30432ea84729a4393e8c239c89a22309ba2c8da37a8c6490c44cfb4adee1daa139c693f546794789e4d80fd6b97cd31147c509ae63202445053b546669ba9983de0272a8e0e4c8fb7ea3e23dae6f0e56ba22858631a51e8f9f41a4c606972a167ea024d51932670fd42c7951932e7458f71a4a1113084571a5ee15c37839fee53f429c0415d463c81c8dea33e9f634a3c13dd69b1ef0f24e0f8f23287d94cd21a4f707ec1d0b61b5ceb14701324de8b031a2cfa348662199d0a0b24c9fa809424f0ed394c9405d624a85285014ac88a8dee8391c1f5466714628c597b8c3838c37e8c93ea021e45f13d421744f155ce284551f4ce573d8269e42e8f2338b23eb9c838ce09ea33f46773a1e649ec8b2363e9f661822bc4f7769ba11b179bd1620e3713c43421378c64d088b5e1e739ee8da0e77a029295dca072e5455013ec4d202ed20edd648eb134a310f3e90743ca31e61a43e026e95cb21e45d18c878f2278a6571a44333a14e60c929896791fa878c26ba2c6b8a664a022ba14348c28f18c11325bde2a44c8531866670ca31992324ae731ecee9502153f073fdba50992878939fe3f8d28f26c731e50f0ee3d818cfa7f1ec8f21ea51a45f1cc39883924fa479f6db1ce879dc135a292bfcce44d3e8d0e68a90b08a178c2259cc9b1ee1e61a55fa24e30c94f9404618fa202a346e26469fa99b9cd10433f851a84fd42a021f54a6887b1fc43202a324a359cd1d435154cd1a0a33ecf515266611ecd14ac1c4687d2343ea4f230d6c33fa121cd074ad235186f4abbdcacb) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_182 : Impossible 0x10000803000000000000000000000 0x210817fc001100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=26) (code:=0xce61174411e48f23e989d6478859ed1f749f60ce510f331e026d50b3420dce1a84c9dca123c831428b1011bd42889964ca1e8fbcc79a0e89a1a68906e766c55351422e875c546120c20eeb2354268c059b0504e478ba3d9150a24197ca13ccce19db614283b7d3f454c70f621bac50a0efb0df79906e71f6798d220259508ee41877050944562197cce8d10139cf6339be41a2c939be26de64589390c6320d0775a3d9a65021a0edf91a2a319f2899e641a222472b06391a1efb44ce73a4f9165153ac17515759f2454daf322c09265888de8306fa6c5f3ae4a50916c9669f468a0241cd122db636c5f28d3330cf36f87b1f58ef511b6399a329d21326f418fd338994091e106eb648fd205961cf1b1dcf11943ba7eeb236873d5e6424739963b946799fa0bedb39dea99194799d6739968d1d6cd0738ca8346a2e02dd0eb31d1a335024b4c93e8358f6c73c4fb025af318e3e4d6f9fa3cc05ea1d23298e195be309ba9b06740a168f34419de68990e639ea479f4b606519d363e913639de27bcc1b48d68a122f9323ca0c0cdbe4c8ce2fa2a44d8e3c9fb017391339ceb12c6e8ce0612089a332e8eb318a32b91b19cfd1e60299033c2d9a8d8fa63a344ca0ceea50eb348e626841229328a8ef0f337b1d0f10e4c88da62cb3ccdb6fc04fb7a92b3d431dea7eb249698f010827eba5095288fbaccb39cef3c419cc6c707eb9cf344c3509aeb1653284c05ba174f53bcdf3ad86851052848b839277d98630cf941dbe5191b494d130c7739c174fb2fa8c99a566da36df0ca2485af91f68f14673a22eb10710d96194cb205426891e7b46850c2450a126f9ec4d1bc2846f37e0edb42830b454ae5089a858e6b823a838d64d4550aa110a7cb5d137284d09a47bad151b47b1dc18c43478673da2a799863998e44c3722c41c69459ec6f0def31cc899f483b7cfea1668215aee51864f9360fea11a4f6285ca1a4fb3946f478a10fee51b447be5be1ec8f45b36020f6759af2530c3d91531d1a9a9323e89a10d1e265357c935419154441f5ce9926c8d0f330c8f2662a7748c07b40cacca3ea84fecd0d661a15d206f61a147f0ef26d864c8c33fa2a809ec61944618c3285928a9de4c9be809b426a0e6ba3487823cc6852428d1327f838f6fb20e94c2c0833da34fa398a64f936c70df137a8235e67d3d409a77a65eac937c3bb34135324d91ae9085638ce4189915c8d1147b0851bc451ee367991a3cd116698e59808831bcfd04cbcc733bb35d2135011ecef42cc70a363a3451bedea6b528850673d44110c5546936798d2429f48f10b1943314cce1f5460da3bcd5ea2187eb5cff4050741467454ef428d29913b28e4a7492b3250a3f4d30911e748d24287991ae71a479a3d053d4a521484b24fa20a52b34c920c4183e9359210cb2809e635936850ba52a127ca0282906e709a8090a69216f54c83ea14f526cde265467f1132268f1ed0766a2dba11a671dc369fc7b31c37dca7e94a295ce0f6a530c5d414ee34c044d8f6216c944d1b3cd25478799dc8f4c9058394604d85882991b47d11a4786a3e9a4d6dd0811fd1e1f536458ba2a8dd4c84d1948a30d1146ba4c2f7087799be618e663837cd1729d210e6db1e2a8d02aa64492690e1c833906a3234fb43cbe7d1d23e9a2668a36385198ef32da96223d81a273798a54793e408fa4c8f667085a95e6848aa72a8c51bbc09ed79287335d1a2c9de47bdc02a9ed151f64a9b9de86bcd1ac73b907484c91eca52340be33a8d1a43a4a4946741c8321c0f72d2961e99c55e641db6c7123779b60b3233cc4449edb4698edf7a8390a541e4a31bc4313247ba1a63bbc7902120d0d339be99124a30921414ae16f736d4a7798619c833d88763ba430d92909de20e1dccca3014b4f879644d46bcd8e41db636c23586839af236fbd431e0e52946399073ed0b7ea4643cfb72c050a1147b0838dc3da8c28c54f73385d399fa8d0c36f9ee778a6729e63f45f3d84d17d467d1e4338f67b8df0671048a3cc8d10c959a2488d7e8e63e9b421e673d886435e651887becdf20ee542418e0ef7454f51ee6fbbd9220e436da15422142794a8e94683a2a9da3e9aa4282bdcef3d42164e95a3e92b1d0908d42b6dba29415cd152936439166e98e265d67d0f366a047b30c798f342dd26191e19ccd6884da3cdf28c351de6d9e67ba262d8727591e7d72902124c3828729f479528f71105945467469322f94619289a1a688beeb3bcfa335023cc8d415ba0f36399ca323c3cd32d1529dc3ccd119c594c8dd3cceb479866d10e4d91a3d98e0337d9044349cc73dce53ad0d1d6c30ef21b24593e837d36438e62c98e79b6cc37490718f0b21c730faf344c79a0aeb28d096ea147788343c673ccf71eca541dbe68a2a6e88542c83bccf763bd413679bdc8a8a9a2759be8090224946025914db2524b0517c92b943cdca339461a9ea829f6749fad13bcdb4683ce6b073ad150a2144fb37cfd83a2a75c94f508a36907394e63785931b6d0a06a9b3c8df214ef36cf328c468ce5f0c9429b48290aeb3ea84fe1e5153aca514a75a1289a1e1d6453ca3c374ae3da649f0fa8b06a1b68f3bca322cfa6b8be808b21f4d15293e4c83c97418e83c94f723c92bac75b446746955011441b6433cceb4693e68b9451a4a439a27599a639027b932a526c447486489a4fa3c479167b1465f0f73a4a347b74fa1ec87368dd4c8e53cc7f3dd2528c670d76ea6479a1cfd529dcc2ed10b3cdbe7585d619416b98e3986ba563c8ce510252f8ce528e620f0f728fb7e84f758a57b8d731cf38aa3435c79458fa3990e41b0c30cd723c573c8c3438b2828394af053e8a53996e2247c0f2a588a2aa0a3ed7394066a5288ba671eec3374ee95) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_186 : Impossible 0x404000803000000000000000000000 0x110017fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=25) (code:=0xee894191a42bdcef22a8989cbddf211ecf2252b44de2ff206779eef538c289e26893eeb20642b243dd3b10af14b48d89b5c528c71ee9d90a3ddea8e9af1940a7281875a945d1b5a27c8339ee476062491d3fd132da949f1746d04d7f93e71a266b9d6459067b93a8578a6426c9f2946740483818476026bb6d0a51933506164ed417f8f53d8d135c9f404731ae28d519c8e63d91f20e2a35e661329fa0c7f6891f474a5808634fd3ee732421a32528fa408aa8a9928508ea25a28a9168f93e809023fc0c3ebd40fa6f4f9163fa021c54542a7462a7612adb7387f1c50a4a5ea80a2651839c7d3b81c25d613e9b23c4ee128c8fe54dd6859c43891e1f8670dcc728c7f20c9b8493b21593030409f5926ba4685a26f51061f992617b89a93eeb4acd70a37f828e768bb5e2608f9470da0b5d0175a14cf0a094acf93a26a9a6a419d61d71f80a2f0378c1c3e9ae51a023391e9990e035a6c7d31c74a31014246748536c909ec65ee8094a48612d7106218f14ea121f49d45bac3f8d6874284dd0c5328d2b20dce21280a75ea47491a3e8ea430910e409064d8d68bc041563a8490a26e02216425192ac98191747c8520642a1c40c872ba4e80a16eb71b7c26aff55d4715d15042b5e3f0742e5a052a3c9b258ee4c92a5190b1d3145741e064ea2626707046c950b4063e8187728c711470723e614d51342c1164a8e93e89bc4c91ae85c84aa82cfcf51060fa5735cf538912468571c48d4282ba64812249f1044b1c4a50ae469ccee42d071b82bd1c810de4c8e3073f8411bc7343a75d612181a168095c2550e21a3528c8d4050a45dead76f878cb41e2a33893a99a1686b5ceb294495e20e7194948d455410d63ba2aa32930d6b9364b551528fe75a72851e296ca424a5a42c84256268f9fe75890a747d42b244cde3037bbcc26cd79089b4248b0388ac8590b5d154ae76294855189b738fe46486a5a144814850ad71fc9b295e6102a9c55054cd234058e2669d8f790a2e8f92184a15be20a9ca8280b1cc506293a712248d2058e45a7c315ee92a168ba3eff3ce06e9) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_187 : Impossible 0x4100803000000000000000000000 0x4110017fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=21) (code:=0x295bf033ac41cd4f532c0778dbad4a92a0a7a8ce4fe263c65a1be9b99c6f9d6e711b94bd5174d881a7e8d43bcc7a87a925d69292d31ceb3f53237c6b3cceb3f4f51eacb4d8eb45b241e645474e7325321cef54a51742cf321d094751a668ba11eeb19a45c873893234bcc3ccd647b6c339d6848bee752829616e73cc9fb34db44e0b011d69a91d4160241887265931511ee50f31ace232cdf40c571dce7404eb07f338ae1f5ce3b9c50609273b7d0e32c7f9ca6fbccc73bceb64916124cd3ac3adea8a98e4f9ce3b8799dcdf31cce02bc7dd6f33bd173fce7454b67d1ea649b4759b67a822bcc831650b1bc6315cc93e8eb2f8258e4716690d404db739fc09f1abadfe6d9928b4c84a5fecd394819caf3424334d652a1a84b7c79a0230bf4eb079bacee328da9946a748092a20c09e7b1dd46418e21bf0332c7320639c1c7f011254a1d64691f07212cb7f8a56d9034a5212742751b75893014b5e641c23b0319892f30eea310edf1e7257882951744dcf01728cb7e88187b5049b405ce36a8a459de65c74e544cff424fd82822681946e73eb962a8919208ec0dfe77a26519f5ca6593278903474ff1dc9523c45d07818e70120651844a8c8f80a26779fee55287f3bd3628d0308e892891f4e608d1e2f8eea526c52b2dcecf) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_188 : Impossible 0x1004000803000000000000000000000 0x4111017fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=23) (code:=0x35cf719c7f2123146733dfe419ae7ac1c3f8de3e9061f58e424737293ecb09b7b8b66b98a2748575845394fef30f50e54793e339f5fe7990aa311e10a731245b14d078d9fa38a56718e925440e2f013f6166b8773dccf28c338d2a38a33ba2e831d66798e425470107751851cb6268bb5c1ad46419123da264e9d281b95fe45ccf14c20e2e679c680bf48fa2e6b8ce47e06e96d84eb5cc545c45d8a6b84eb5dd6838629247d7ba02719a43e85b3b90e8b8fe155d67b22f0b07fbdc37c1c5b42c988ff1762c0de6a50a38da06799964946f1ae6587bb2ca3799b67d44847b6cfe3cc639b679a24429463398ef742d4a0ae478e63b8a63fc6d0b19d1f0fa47c0c51a54406066967c741a59e8a9ea859c67490a6293a8b06952a3a448b62bb7c28dee1dc83275136b9d6638859dea340ce349420667518eeff1020d238c0cfe2790342892a168e87142e030314ccea50fa348eed710a9b6780a58099d17899c6294e9819fc9f3fc4ea2c3499ed70834fbac4294ac76d8518ee34b5c3dc6a7594a7f0eb12c7716cfa214d23f8349dd032145b52a74e379a643fe3e0f772a3b0344d1e4e94a6d9c6639ae206c51037fa7c89b5dfa016e07174a53562a951d11390b5de604496c8a810ee950ce839ee639ae3ba954623e7bb5dbe3dccf38d031fc3ddae639462da1671a9435d9e954c827d123987d33d372520e7bb94712647f9c644a5596f9) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_189 : Impossible 0xc000803000000000000000000000 0x14111017fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=24) (code:=0x3247b20d273cca32144c91e404c942a56d707cc0c8579a6cf526684841a947d235253952b39c8ea3c8e99b4f818838d826996e74d842a0a5d04d41a9481a0452936868ce348fa47946939fa4599a0e327424cd22ccb7bb24102a566838936819a4cd22d1f28ccb6487143be61646dea2951b14a47a0a42baccb132409ea7589b5290e45b9c8d0cb669ea4b51b529ce136349941259a8d324991364c91ea581be41c50a6699673a8e0210b294042064699e028b834c7d2d48d17235254ad3126dee11e6972895a6dcecd0cef53ade67f109858668ff0d4253b35c8b415ee106f77e8a5416020c30306580a14871f442a05d619d2347d2721c714051b081195459583298481649ca1a41865e4083fa94e2cd4ec6d80c0c8fa6272820d8e6580bd4d77c8529c411f4c8ae715287236a0c9506741a144194a871068b23426cc680a66067658d45f4346d41a0472a6a7c9f5ce04b4b4fecd0a53387cbdd368b8ae43c0c34a0a853f519067438c922f011bd0ad70e2a2b9c8f93980a6a26a8bc05aef52060ded721e0221e3273bade69d1021c42f902389461ba0d4a3f9213e80b671478464d86e2f8dea51b5091ad0b1f5f20b2a50a580be4851f58e4047f18c83759ae404a3215e6891092353b8b8ce7b9011ec5f2247122e8352905184308da814841fd1f40d0515c7b7bb34850fe77849cff1742c57479014a87f4e87f1c50142a9438a4e45c12a34c7e2e818e2f92147b8499a80a1c2150e3da16eb6491f45c871014861a12196a1e3e7eb35193d5e6e3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_190 : Impossible 0x4000803000200000000000000000 0x14191017fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=21) (code:=0x1ae6921475b6c82b9d033342059af91032d840cc2e53dcfa205aecf1026ba241ce75c24f5115213e9fc19c4d679ca134e53e59a75817592eb1f4ee428f7234c93acf96b8c97a820503669aecf1fdcea30db31485274266c5275cf0523428d332348120dce7f7584299a679ff0547509728cf20242832a3d1f215031d8183adb66bc05ea35d01425ee20684b3cd707d1fe063da3616d460fe8f28e02e542c4099a6bbdc9d7cc1c3fc9f67a82908ff0eb12cff4791a4293a832123db9462a7c89829ae9a83ebfc3e91edb2251f44cc51b6871ce6798acd06933cdb314e723662d77c88599acf36e0247cf75052d0d2a08e24f9f4628d23ea14348a29d22ef564bf440481040d8b078093adb12c9f3fc4e9fac93ddd61743f93a1a9ea4a91d629c44a8e21faff419d66112a3f5ee4f9cef91031c5c67b9fa7a92ac91ee3893a419d67aa059a40462be5333fccf0f93ad8a8d99e770db1dc8333dfa8da124e9fee719a810fd45cdb3e506f5106856ba64276368189d11a40a127e93e8eb3cfa6286705d4c9dc8d1fd230817cc0c195f21c532314fa3086146840c0cfe3e53a7fb9d9a1b69d3150e1dd1d19a9910c9290a9d1ee893e44091a44a8dae23e9aa0a1c50e999326bb6dd6e9) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_191 : Impossible 0x4000803010000000000000000000 0x14191017fc001200000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=25) (code:=0xf30e77ca2e92a669693e1f6322196c1bcb63b8a2308f6a349d091f2738a52042049562be60664b3cf504fa4aff39d4627d093d4282712049f7fa5f0339cce9f9e6e30358929f184631bc7cbcd333250239d23418d2468e29d11d205ce8282059f0342c8332df2718e77a9096484b0ce4d8611c481628e9505174ec0d2944de67f022a048d358de3d889a0461083338ee308f311933a0ce318d0237528a5184f33fc8520cd20f666984ff33d361fe649dd0933cfa38867a6c770c26923cc91410fcfa27d02428d24d99cda1b43e5963b9847c98a208474f9259ac9a7120a8198a8120ae706b339e60f9338ba4b18c8315cee3e51b49dcea52127c9067390d79882bcd25668b2690d68518a22e95b9c95b2c8ec0c8579862a95069b04b339e61743112cd2096f3658b2739f41c54a8aa12428fa65b24214cb20592f53f8710fc1c506308f67c8ae2c9dce7204cb0ee40a1413481819f2659063b90a7998a7d0fa64bd546f72828f8ff335c62347f1f462a95ce49d2d6d90a1ee738fea540c528ce7f89ea087cbfdce71214739843dce73090328c7f388571fcfa39c9acd11b738a5276062790adb4184299ef704d1a4e7339f49d3353e11f39d032147d98b143146152a06a0a5a73be5e619a77c0cf71f4856486dc24f7275eafd0fe24ee707f4c606db215133cc849b6e35281fe06e73ccf54d87f021418c6378ae3498a7191e309020e283204cb05735866218f631a154646c389e6648c28291373d446924e81a3a89be4e33f8f338dfaa51246d0857f81860696902c51b438b2c83206679e6853f9137e9ea9b7bc043e90a7c99e7391313c42de689a1267a3a6489229471404f913a80c7dfa12c95368611f54677109408475e636a1640ccc630ee3ea8cfd86a147e90280bd5eed70ce1943fcdb309a4329dc4d0d271418b640ca316cfa3dc9f20c738fa66a3a7c99c7cb5d02194671a47d428818de40996429ce219f473889b5cff39c63325023483e4a6493e9dc8d03bd05fe40df218a811c5ce19cfa808ca096f96b90a834e839c8534902308db010d2831c4c90817389d39d06858b264b347ea3a6d9f209b8d8b6268eef939e021c592319dea51ce339927b9f27d3fb1c326828089634871021bfcd273877328e26489a61418a516c308d22d8694d5e664c7c528b6e73d8808b6771ec3bbdd0320d021ce3d9c4fa20c9b15ca3324814247d1dd0a1651f10c4d46cf73d42f9b44da14348692950b3ba2a4290141e067abcc20e8fc04e247a3641883429ea20d1a79b6c819fa52a3a519ee8d85d40503799012947141b9c41de6425ce7a9ee649f4fe1c4428c2408fa15ce2832345b0e78091f3f5923e8fd6b9d220242992a517c4b15c859927d2d9dc798d23cc69388da288b2668c63cca5215062f879a048364874bcce73e9fd3a0c30927c40c3093a3f8fa7749e4ac9405c6eb) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_192 : Impossible 0x4000803000000000000000000000 0x14191017fc011200000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=27) (code:=0x42bdcc710a8b94a214fe7a9963583dc9285678cf3164a214a512d3a6f1e6fd1ea8d07d3fd1a3b93a4d90e6d9ce3dd392547b32c0cd6589b417f8cb6da6a75a35061fe8f9ce899f43ec943ea74819968d12b4a51740e66a579852996cf3dc9d21cdb1e623cf33ea2e658cb4e881b3ccb21d1b310cb504bacd1b65293a46bac75c95ca073a8cf73ed048d45d256b83dd962b9ae6690e3498e75a740771fe1a89a32f746c690fc4316c7ebacfa8f28d9261041b9d2938ccf35e821ce9d1c692a2e37912228ba8fbf4cf06f1f6821f5274c6723f53e9291230aa22e9e6f713a6d9e6eb14a4eb360a38cc54ecc70429f6a2f71ee81b3498b2d171463f99e45c9f44dee669d6fd64831cfa66d042068735c7326c55798314ab2575847b35eec98a881b144c62e3ea36839e692bdccd0737bc563a0fa47b244d8fa7f0cb64b8c23ce31fe2b171a4799fa9d7a9c428279c64ff4a5058d9ea718cf1bd4611d72924850cb215ca1ba6c79b5cf51fe349ce89a3a6b90a8b86b7a9b43e89e214d74e8674fb24495966b90a7a992a31ca495963b90a73a2e7a9927f7b89d32ca30fe4290e7a996719465299f1914a23a62c9533828fe42a5a8a93e72837b2d367a87327d92f78183ec6ccb324379969d39c2950a659fc7fa52893158e23c651fc72a0e79a363d5ef291253ea759a20c9b31c1cf151788db5e168f93e27a3c7138c1c4de7f1eea30ee4d9ea4f94671b242da747288c9dd3a399463fa15d68114120d4738dfa839464f91a1c5021ee9ace62e1d68ac148d32cef3d4e36d8954949f67875bf4f53ddae11744deea53d4eb1fa9ab5c7bb8de64947b28c8f1f51b03f893033ad3a71bcd1710a75bbc798f30ef0540c8128c8599a2ef713a868c2cb0d732c7f21d3a10b75c7cc749d0332c294c547882f73e8a542bf5932101446b22506cb315ee7798e758c2728fd1de819033f48f85bacd731ccb0711a551659fa4abdc2153e1468bbdd9643b8c1846a7e9ca3fd073f50a9d648a341c22ecb4847f42c9d3f592f71fee322683946ef1927293e47c0c896790302750ac93949f839faeb18a428c97593eef14acb10a38bd47eb8db60fedb14c7d08f30b95ce23e0e34a90a478ba52bfc4853a47a2e3fb2596f711764bd44ec6cef2427ebac38cae3090647a423f99e44a8c0fee34792a529124eb9c81863b2ca331432ca3419ac873ac6598a891fa9d38a7c40dc64d92a3f53a44b960a19ccf0e512d1ea31ccc70a547a0e65bdc7291e26c737b94a3383e94af739d46639d6611920d2f733d0b478a5519ce7f146658519966d4f832d0339cb65d728a36ba243fdee7a9ce649ca3fa741fd3a4d83f93a9b1dc6523dca26c8f758e5295c6518714f89d6ba15020f727e565290672a8c0c2a5679ee185c60c2e32964228ccd27d02e7073105fa771ee1fc9f679a4eb14a40bd48d9fa75b6c2c88233ca6419d6851467ab5d1a314658829198af70fe12ac912947a2a6492a44b2c678bb257b9b68d90346ca321452a24819ce7f759c465a2a39c8335c8f20edb06b7bb2c6db951223ca3234a53bce5224fe818ec242d93e63826d0af731ccb36cd6848759ee1cceb79a124f8f332dca7d4488536ce7314fe19ea3274224671f63a6ba46112cb2153128cc5275e6474894cd0d7f8ff43479c862e474fe26286c85ce28c39a3e9cb9c95bfc484ff41873a0c6751c2c7f48e12f71171dc6747ce213a62a2e44a0dce6d99e3ddaefd065b3cf340b94339ee51a724adce6d83dd3643c2ce7225e63fdcb031254758a09d2247d4ce431f3151d7990a15c90a131f474856dbad4a1fa4e9ee731062984a20d03448898a8674e883091d67ba3a5284d08ab5caa529fe72a2446e6acf0c70b23a67409f51a0f366bdd0b07d669fee73090b1ce2e91a6dcc4cf27c678c281b944d827e3f0940a3a4291ac708d22af3504e527e0642a16eb82ba46799a13adb3251f14a6db9dfa1dd0945c3fa5a8fa1264bf439d1779b94295ce8f32c08173a0e7f8eee509565b24e6cf1e70b8d8fd03f8fa74a9a9a98acd8f8484ce3fb361644bcd0911ee713644b2c1c4cd7e8cd1c51d1443e9851ecf117478fe468ce095308b646871529f438a1c9f7ea42e38180c2737f91a66b2c1c47d408a230a3c39a7c9c8e247bcc1c44f409969b1e6d707d6591e40d3e1f5e6106cb23c30b241c4e71d04fd132547596f35281f49529656cb314c9848103134b64a4a91247bcdaf210f392a3a6bba414a6b38d1e4f8e635d2a0d2389dd3a23cc94849a4488f414d7484418ee7fc2489c5e3e3fcc92946b1b4cd1cc2565299cc290a349b256909e689658465fe93a36528e68b9f50973bf414a8d308a24e90212c570d29b18479a244d94481324e21a474936528a5315251f5e633592419851d4789b39cf619d2d325071030339e120de4099a9b0c2479f4c9235967f7b84dbdcc522439dee629093dc7b4f8834e909274a54491afd07d468c51bccd4f9178e9aee907fa34891846f41a261f6167a94acb638e30e35281c46165a94d77b87d728811f59a28a3c19dfe2087ba0ca53ccc21f4618489f668fe38c35739ae38dea8d06767a1238992378a295018525529dd1e0ee30a945135d2a3f87723cf335c833eb148fa56628c23b836a053e7983ec25ca3f50939dae8951be43f48f294cd255ee3acfe1a5054e89b35c733ac4dc0c3f91e3da9495052a748927a06773d4850cd399eea379819a349dde642bdd2741d1b10a74b1c2946b7ba8dfe274d74a50528dca214730e68926c8f40c75c747f6d8838cb669ae7e9e61f2f31bdea1c4853fc6c4387a9adfa408448e2a50e66f27c833d49b658f338cf904b26ccd729fcf54751e09d52996cd748f53950b030c220c531ea30a347b09e1ba2464a141c5f2999bc36a66399069b266368d264a3d963344c4cd39937150733159b3321498c8423d9a90a95e6052c0d1e4493a3d9ce46a3a42bccfe11acd26ccb2249d2152113a3f90a40a95d211ef533cf3196a539c9b7ebdc324f739c7b7e8359069d1f2a28de89658f739c6f4287b9fe73a068174b1e2e112455345d196cd1ee4e9c68511e748fd32dee10a8f08f91bde068587f28dc628ccb3dcc718eeb146e37f88da747f2248f112fd38c47d1383bac65b1db613b47c0c485064090a47b2c4349519a8c41a06e9266fd14c8b9fae373a942c93b7b9d20b2856d8a37f8ee7aa16224611fcdb739237188523dd61cf0742ce346cf53ae528d11e65a2e7e851cec7740c85274fd7591740c853ddea295c6c920624ecf4ec42946eb3fc3fb9e0e13328e767f936f71fd033359615c778d88f996cd10aeb1126d90a810d63ba3440b9cc774c761301) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_199 : Impossible 0x8100803000000000000000000000 0x150017fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=24) (code:=0x51a068890610731445e684b3438843bcc6340c2dc960a1961a0694ca9f05425063cdde2690528d0374a941d6418d6f53490e434f1324290f5051841183cc468d1e66d184653ed3b828338d8522d8f381a3c475e6848ce819f6369c41946d7a81a4e736885112661a38a0d4a1a48d1c4eb66834bac8da0af520cd70873edd6418d66ba3475c341b5ea06779c6c269c4653f82ca4f053d503438e732c7f41a94888fe438f2828f6469117ab34ea3ec7f41d0372c04758eb4449b21c671b40592bca50623a6743a94418fa990ce8094a8d7a84d9f6cb2851148c75a028fa4a3a8754d9ae43bf440ccb1d54ae564821c7ef52849b09a8091a8587e6b93611f4694c6f3250e31d1140ca121cfeeb1ea20d1d3d43351d0b338ea45c7d6b98e1151f42d011fc5d1d50e06e6b99d1aa57986322c834241d606871062f8ba4d8e24388347d9aeb39421b03749e21b49b1d461194991c602051388fa329fc878fa95ce9d01be03034447520c7b03f8090651b9d4a098ba50681a944d8438f6e75289e2b8faf30fe9f81c54696862a546e3a45c060a10e8d04751aeb4250e3e93af37e8a53cc6b1bc751f5057283aa948d285ae89) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_200 : Impossible 0x120803000000000000000000000 0x1d0017fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=22) (code:=0xe743c833246728d033ccc34250b31cf522a0513f906359431d27dfa948cf7498e31c7d1cd074345d445ce175860e730cfef531d321d4831f59244a74474fe778474ce8f9cdfe3fdea8198e3d5ce19db648e028d0731445d1ec754492a46a9482a42849d287a0607f9651a6716d1715c7517c10628932f58aa0e84b9d3a80b34528ba9787728d1705b2b9f52710f2b9fc4d779e21cc2f7d88199315206a53ec39a2481a2e8d4ea0e28c11a7749c672ea462354637c0c51c250702367351c1d05425271dddea514a8f0fe9b679030ea528412947767a3451927164e6278ea378f684a242962e8311b0723e0214a892745d23433d1a0faef43536998cf8491b8899a445ea1ea8d276021760e7f0924a839beccf52a1a94a224682e91aa5809ea66a8dce09e338ea3ea95e6e5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_201 : Impossible 0x100803000100000000000000000 0x1d0217fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=23) (code:=0x3942764aa522b1122220628a1c30d251351b2d9dd4a2f93e5085f1dd1aeb0e5619e62d8e5088a06c37291d79a16a53f49a295ce7f0c343ceb4f93a8b13646b1c6b98e4d8aa79939818fe61bb43bc5b284f33e83ea861e4a91a222222a13e99e80a52e501e9d25b164613b8ae838c541dce72a941fecf72a168d03b98a4a96e3e16d423e8e62843ea7c952942a8ee0eed7583ad3e4a8a23ac1d0f1dd160679daeb30dca8d26c0f5d6788ca03b759846573a94fe1dd1108098ae779a948d1d696879a5aa52547d2d9ceed638459dc5b20c1fd1a6390616cea2292a8705f0b4ea469cc1d4e6458ee63875394b67d0a22ea6dfa7b07710c738ee2d9f5073cd01729411e435cb68588a82a8296a4263954a106b884ee418eb3d8e60833b88aeb3945d1ecaa952422e92a6d1ca6b8f64f830dca7f1ca771ae828f22aa0e5097c5b2e911779f5da40d013b4fd0e567a529aa2261822c1ca1395daeb31c3966e50b5c2763e8f65d1cd117285d4260a2ab9d1a0e6c720e819071de2c9ccfb3cdca0ae73788573cc654198e4d35c729da798fa5b18e7b101184ae2370540480909165ca7498e57212f33983d3cce53f9e2111869d2731ed06394fae707a6b8849e231155250f52d7984d4b4d73c426a0cf30f5ce0eb79906553c45176a0a12f81c34ef17cd743ceb3eced0a2f3729dd4aa310e4d877092bcdd6554b4311b44518e8e88a9f21c0968b4b4ba3f48a17c623683bbac30cd73b8e6f31ecaa950b6168571dce92a85b28a75da3a4475d23a5ae5d146848aaf122a78a746b98b2d31c8493578a9a639ce88a5af30eba09e281827bacf121c759ecaa3cc1fe0e798b62abc65a1fc6f4e9d2ed1033ccb63b9ce2a907055282ea94ed0773c63a888638862da95da1e89a550ee74c148d98afd0aa8b3a9c43f879bac7f768a21d6556b843438ca10c16c871dce77985d80c0c1c4ba76a8c630f33bb5c308761c47740c5b18d2521af323a2d8e73b8c63d954ba0ec7a0f328cee5576bac1ce51758739f68d9750f3ae028e9e6e55282ab5cda3943b87b0c62a9ddd635946a53f4738f687468fa8f) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_202 : Impossible 0x100803040000000000000000000 0x1d0217fc001100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=20) (code:=0x872849520cf504748d16ddacd0d6e5438e7031aec71fa3a8f516c7f26dda619ae418753b83b8e45114c59194a130d1a739b440c3b0cc7f358ea298b21ca26a1c390fcf13e8e6328729351a35ce53b489965013b8739941246f3eb94f10ee6d41a942f8792840a65b285d63f8e71d0e72f99d0e678cf45833c558e9e63f9dc6b31c21a3e6799c50b9475c0d1a0e4fa3bc3fcfb63a164cdae0431fcea8723463bfcd722cba5f0eecf7683bc95151246b164650799ca770e4fe39a343c4750ec594383b964e5468393299d4a01cc2ce72fa341651140e1e3f8921044932a9506e906b8be4106781944574a9d2798aa3f90613dea3e87abaccf3b47588b184fa28bf45f3cc3adea3e8eb7499a839ce799fc0f4657a849838aa27a0c458fe2a99e2f9dcea39cf319c4d3d4eb0627f87389a73789da6b87a9ff23758378a27f0a2671ce7313de68331d4a71041a3e7ac3c4f9e667bf4fa2959a46811b0d48ca6419ddae618831b5ce10b3ba2228a0eff3cc6d44c3cced91b5c106e966b9cef2958e09af5046d2791bd53e9f82bc1e0627dfe1947a9da5f404717385521a2ac44e73b58e830ea3cc533b4633ea02529067775881a6e76992eb192ef1d6f5236ff2362bb9c6308fcc62677bccb639cfd3cc40dda79a263b4db47c33bd441a3ee711d769cef378a943e91316d35198762ca0e388c92181496c7121a7d16531798310ea7697c4123445144a51c4e7418c931bac41dd620e818a5ce878713a50739c05d3d6625b164833b90d268f5389ceeb79b3479a023c483165031c4c5174cd738d67eb0cfe154651fc6f1ce139d40431445a5f1fc6f12dd620e2f96c7f30c17dceeb668673ac5f1bc4b33dae710259c4750cc5b195d60831f8a6eb669dd1699) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_203 : Impossible 0x180803000000000000000000000 0x1d0217fc041100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=26) (code:=0xed35cf140ce73ac7394688817dfb1140c2699ce916dda35d927d0ed3a5ae759d47709f3c88589193d3780a1e64a2cff15cd71fd030be3fbb4e76283c829bad16899ff1d1922bc0c7f36c672472d1163bb5d111ae0ee7f99d2d1e4fa3f8daed7e90740de2990349d6c5444ba2a8ca74a842d84c9fa88b14fe9b1e24d90107e8e2c934c7ca11b46bbb476954e775a0616d0339cd74442da0633946ed3ea3c35cc6818e65181dc4f1e5328dc7434bc47d284e71423b8e743d031d47b40622ed7581cceeed1a49923c7b26ca323a88a6e939da0348fb1f459dd2740c791cceaeb1163b8f247a5a4c9862226951b5c28dae39a0a1133fd32288ba22c74571edda677ea5475834b5ce73bd071ce7540cc93e8ee20a7d14469324518ee3394273873839ed2a3a5361da790519a5d69541d031fe75a067d47b9419ced4343b60625667405ce349fc218ee21ae746cfe768aaeb4c8e672839469789de759cea31dd2a1db0328c69146e705d818ee8dc04c90b6d71462d9ce3b87731901819da1c4aaeb0613eb951ea5081bb509518ee3d9d21de4a835a72731e47f819da92839ca52534876c9542a307d819fe3fce740dd68f1dc7f9d646ceb3bba5ca1dd32405050e4ff3bcdb1ae729de7682ea2c671a463067329ce3e771073a8c3338e6728eb47c0dfa8d) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_204 : Impossible 0x100803000008000000000000000 0x1d0a17fc041100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=27) (code:=0x8f1b68388eba4db759ce990fd75b25110a3264be75bb46490e186990992f9f5093262a2027e9b681a2a424458b6348fb1f26c8ec0c876483bb0dda474ed73b15d60eb389a45b3d97422a0e7a9d60ed3da6c36cd23ea3c479747103b34a8d8a6d1d62e834bad1e289940f3638ee73a658a36a2a10c6911b759f46320e0e26ce9508768f2a139d1b17511194c70d2713d8e741c7b459d417c7b41d3223a993cca323c7b08783a848b768d2206671ec45666446067aba513207070e28f0ba76a8c20eed4c9463298a3691e8320a446423c9eaf322634c25ce1ce889341dc1dc7d629ea888ea41bcc3ab9c1dcbaed4c82589ac33889b3da02439e4096754ca2c2189676a3c47a846505d445326975b34819ce18a818f638a02e73b5e21c5d621a7dc2c42dcecd3aced7498e05d8199c81c04f320693bb4c923e819ea28c0e61a8344d2b41c82936f31e633a1b01738e7535b641c12e3e81bcce776bc4798771c4ce418fb3cd0306b28a0a1ca061e88267768f30e29b9e70341d0f74b34739864d8fa819068087a93641b26363bbad321ce86c0d0f20d07424fb404690e206d95a0d1d17481c0480bcdce649f61e71d1b5b63cd2776bc442e121a4f339c2ba0cdb8d9daeb478ed03e99c718187119d9a3d9d6f343a94528a51d2529067ab9d0541d9a619fa808348b2f520c7aa8ccd0d28f1ec0b2f53f4571b4720d2831f45f5185f3d834c44fd47c2c329748086523d1b11c7d1dde66187730dd239cf6a57582648f83bd487414a56d8cd39c7a867669cf0730c1dd9aa51424c8f2618f647badda8d11d44e0e628739a434b245122e738739424576a35464d8ed1da6285d45ced79a6ca322c6b194a5059334eb1cd428d3d9117484948a25a028d0ba809a51526c76a94769f51ee5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_205 : Impossible 0x100803000000000000000000000 0x1d0a17fc041108000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=29) (code:=0xce2e906c506bcb47919c7f915da414d295111668be968ce9b0638f2c53389540d0e4f895418424513245b10e2ba0e674ab14a13683b8c23e90e9520c9f7588198e879da670ce39d0f26c71628ee870ee888e28352bcc1e6c716ce519cfa3c88a418eb3694a1ce3eb94cd2946d3f43fdfa73a3683936c70c9508aa368fa52816ca1438e6318be2bb2450992e531c46cee10721bb542639ce84bcc8f9cafd4a8e73f506eb629ec38936878c717c5b1cc4320c40cba31cfa2da6c878fa7ea85da529d6e90d73cd8a06d418f2398ba7ebcc0866f9587220ed73c836bcd060ce61bf4f13dbb41ede61e67d768f2819927db94086fd40ce576bbc8f886474f21a5ca78a1204f648aa729dcba424fa425427e8770554e4f23e8e44f1ec3ca843d90ddaeb0c3218ae2e8ab050eb144668ae832845d1d67d768ed528a5829852a222809069573a8c839da1a46d41ca10a56b9da25b351f42cfd3942d8da528c23b896349470f1ede602f79a16c57f8e5334a17d8696d91173829b243b8b63f51b29455799fe43c4f154c61090fca5649dc7d518c918c871f0431a4da249fa0861da026d528c93e8aaf511d4a8daa11b6830e2418aae70f30ed0e3ccfa3d93e3181a9e4951f62228c43d37315414753348d0d799f67f93e5512ae51f4ee1e48e9ca998da3cc1dce2429c9e5ea021a7e4a8e8da79254e550bb5d6294cd0cd12c9b33a02e74743eb6ca339442cee2b9ceeb1e415de639d062e87112cee1dca21f5ca154ce394678383ad9a3ea3a5d144f2038a02cd3c92aeb19c4a9441c486518ce79a947594a738ce829f4439b48330bb6068f1154d86d99a63a7cf339d032949b3e863bbcff1a4db13c0cd88b1dce6dc54518d2a5418a50625b1446198e6ba2a669e43b54a42cf5294ed0e59a7e99cee0ce41a950f3f4d736d1e1e41f5e664a8c4f16cc739c2d85b2b85b15cfa1e45773879348c68f0ae5188602acdde67695e0673a0c0e23e8c4b61a41fe0c9363a6684b768d29519420896639468f9f44744d2f8d22599a76a0cf2777582fb0cef1da2d8cd236ff4350b0aaed15d01295ce15dde20cd279b1c3251f3ccb627946638d209efb739063cc5b3bbacf69911e389463d8ce80a0a0fd1eca69f23c5b1dc4b19cfa0fa8f728ef1dd0342d1f648a23ad0143c6739455037b345d2a9fa2f90e514a9070432845b838a317ce23bbb421b6d150fae939c6ba3c24a8f9dd07284d751877479ceeb0d751805d97b5e3a8583b4fd2e8ca2a8349745530c2ceea30fa0ee3934a3c87759dec910716cbe7d8ed6b876b5cc37e9de039324ee83c2c34b6c2e8aa6b9eaed03976a028db9dd6990eb17602439ca3acd24f8eb648046a385b24993ec75bbccd4751b394ee33816e0f1109f23c493a6665d08699484174e5475daeb739ed8a8b09520d9a12b032188189a5506b894735098e81a8cbe40dca334674784a906398e44f03b1f8fa41a3dd628cda10ee5484c73a4758b233946799fa3ea84f604d31ccd49453338be731113ea3c7291e7b52a347689540c43438760a69b3684d5288e3290320a729037686a669ea953f4a13e93e3b869079c7ce70e779b958a18a2221ec376a165b20e349e413c7d1b515334ed73a2e8781e6e73d5ca491e4ae7301a94a39bacae4312a1ca7ecfc5747d0b154769311b52a4f8b23e9117790c6293e7375a1c3fced15dd6799ce9b01dd2a7d79a367399c444fd3ccf522a10f111ccb63bbb4475054458ae74a8c93d536c73d80ae21b16367b21c3cca53b4f54544d4399c0d58a4f1543b4ce9f388798fa5b134219e6c730c619e70321ea13943ccb6eb1cdd21ae629da670432d89e39c4f2f8d2314ee0fd0b602eb3b49b0b65f638e7339ec6f0eb3d815cf65b31c76b9c37c0cf52a87596e3609218baca50f4ee39d0f40ca518e10c3d2947112421c1e0a2a82fb1cf6ed339f53210e4d8e227b9c772544c8389e7113d49b21dda748ee0ee7b21aeb3c426511759ea74bb47ac1c83c558e550ee4d9b410b2993c9a087117382692b116387ab14d20eb7398a3490c4f254f6790e7629da3bb9419279b14ed0e77687688657639ea551dd32308db031cd061ae75906991cc398ee7b0f6e71fae510731cbe669ea3b8a10551f4ae438be1647d39542154eeeb0ee438fa238e6218f22fb1cf61430f40c550c7284fa4c97c3f49517e1e7b1b41aec73f503919867733bb51a3ac8898a76a0e10cd23e93e7119a21a3629a0e05376b3435d9a279c4472a846a1b01334fd41cd29910e2e9443899c1649f335da7e87687228bac9f2d82998a953489e0a23e8c22489e168d2749322abac89bbcee339073b411c4f99886cd4044cd0e89a16628a61a5328d8eeeb0ce2d886e5739ed16750ea2893e0ce6693703144730bec5748d240c511cc553cce20b62699d4a0513cc9a67369063cd07294ef17c528fa228ca834c90f10379848c833686d52a7ef32a6d749c7719a799428f8877fa4e6bbf44454ae57699d1a3b47721c2960e08d43d9b071dca51c5da8d8873b5b66710ee535c834781d49f4394a41bccf61aec51e22a8623c8d232841de67eba412cd766bb433c5476bbcf11aea53ea6414a6d79a0e3cc791c5da85a3c3987e4143f13479395861354a2a9ae1233699c557aa35461da3dbcc4f9fa3da16369e6871a4a12941e617c6747606f542e0e03996a22819342a8faa30aa7a9ed0752a358e6b) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_212 : Impossible 0x8010803000000000000000000000 0x151017fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=25) (code:=0x7c9f683a6c3ea64050984d28f2660af71543e8da4c8be7590e3ad420f73f3ac8738b8c1fca132a2e7b9f22286941c34bad170d288be51e142758863d9953623d072681a9a4da1b4eb1fd0f010e28688196d073e48319c7b809c63f5467b916349d4828671012e8fd335066b9350520e693291640817cd2269071110d1d4d2f1204fa13c6f0691c81d99c3330cf315cef174ea2a9c6202671544d17c3538df2870677c8438df05759ae66a2c6d05f8289b329c6368ea7f50820e02c310b15c6199c431fb0941903424ff0748d969d06375834bae028ca468498623b013ecf1144348fa21c7f50badfa852022088e2891116cce404f62480de029d1fc1b53a3fa424135c6924e3a8fe514186120c7f4788f07b3a90a19675a74a319c851b50622ef70da61135273351f012c9e21d42e8d281a5a3699a1889a7f05d1a4450c4fd1b44d3fa3c1fc8f7ea14214863da1ce211e61134f10269862234a748532c7112d8889d21c348eb0d788e2e3041a75e232cc281bdcfaa506d7887b1e46d45e021d701154f719d0982888bacf345d9a20c5d1ec670ce808b6148f298bc426be4cb1b47580c4ba7b1a602658677b869458db050798cf1b41d313ac3490e459c602cd0ba3ea84ea8e88f99a80a1c6313c34a2c3ea0c6d079125f236a0a508fa4399c43a1a5d04338c5326c8b3acd2f1136cb080bacc3124863e942854ea546191647a0e07e94a613e47f4c62215ca565911839029d14a16ca53c4f94644d335c683a628f13a853e8439df0d23c7d3e427612f103d946a53e5191f4cd3a93af74a861334950c2f93f49d41c4d2147517d4218536e50f946505154e247a4a1d7251c4929ecc322cfa21ceb35c1c4fa458f2754a8814ac8b07b18509394f9438fe338be0bf493947f459f441d0b2f9f23f8918ce5f3bc573ea74479b43d86743a1e909464e8de45a541b87c8be61394f7274fa278da518ce3f9d48ca4a1f5252547590a0eeb508eb4841c63e09671484fa0cd4090e7cc1d432510750841ce2cd3aa3a0eaa319c874752b01424254a14a6468ea0290c36061370748cd730c5528c0553d8e236b8cae9507b1ac711fceb1b612a107595d1d30e4a1fc671b47b1ad0950810cff07389f4719e6818275d7274dc050aed) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_213 : Impossible 0x10803000000000000000000000 0x1d1017fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=30) (code:=0x530ed48d133ba367ba64f904f388ca9098a288d21dc430435298a8527462a2c7d8fbf47ba264c90a7e8fd3e603110ae0c634a96124f9320851564e4c9ee6f4a8c54589576a8c7c8da7da12888ee40477668fa4e90a76a841ce260858288522e3a318d27cbecee2ba03030a5888e65193210695265ee8488310ca521c734e94242889a0f2d4642654b0d48d155058a071275093691e88a4266bdc4eb1ca17c887444852742148f5193a06541a64444d28f0e2857ba94a10c57b93a43be5fa47410a8b3dd091cc8107328d0a3ba0f218eb1511174928ea63b3410e398d2c542a743ea421324391701464ea18c6f1f50a10b0118529465494e837c2c75508a11167b9422fc2d8afd0849b48b3cc7d6289511667a8c571350b3dc7d3cd9a24a45a8452c45137e93af97581c52b2d0851a64a22e8511f7ccf4da7991319e888697d98689a2e36a14f93ac47dd67ba128bbccfa41cc30f34449f46ccf9990761bdd0945c47a1261a8c8b96b1489a36679f67b84a94647b15e61d4a322ccf06952a3cc31e6223dccf4c8f33ec3414695678fb1d0674051b4cd9e439068681b4fa4190e879cc8f08547906a31f2eb0fb678be219d68b62bf41a5ee21e39c1c22e14b3cfafd4043bbaca54750a1e62cc35329d7884aa8cfd30c6b274870673a98a6691618aeb3c47531d464787522c414b4339f51521c8f275fa42c2649d255d68ac7cc3799dc7e92533ceb525213f5e28e91d3c4eb485023dc5521c8b24aeb1ee2a8ea75c6428e3e45c24e219f253cd151e678a3a83bac30e0f0931d2a1251c61e7319c4322cc709f9abac92a1f21464fa22ec51350b0eb8ec1d3b48c38892f31e27ec96028507590cba3a90a44d1928c8f334611f49d1d4873ae0e256c51b4959d6853e492a742d9f43390a757e81b5233b8772554647bdcfd0de85bac8779a85da28cc308d8e29563946f348d0b10aeb1fa21a2e991fa8b21a4343ed3f17186ff789327c9160e3092644d3c50110a3ea2c459e6f93f5d6c514a4cca547471215151f6227f91d46c7320c8b022df71131e6639a46519d5d6f71d6639f20e22158e8bd447ba8491be5012470909a1c98eeb8388498f0b30d2379bb5ead72024ca6e939ee8d8939f4a51133e8fe45a6442a7c7b26dfa50bbc13a8bc0d27529ae459861f51f052c053a1f49d2147b22dda770ae3bb5dd623e81c2c9f1ec40c773ec159a4c485254651d44d455011d6f1295ea01ba4e878fe7d62c24950619447b1fc8f62c550d3d4869de8793a62a941ed17404f5255168788b4141ecfe339c461144cf4c94acd11e0562b8c627a3d4a298ce13c7f0ff3545434c34f690bdc1f51331467435e21f59a7f90f030629f5217bbe408fa0a4311e794bc552b8fe93bc475284613e4fa80a2a3dd250f62d9163f8fa1f51e27bd48727d21285034059a09952a6234c04a11f4cd4ebae221ec24a791d46b20c3492af91c4419f66d628cf42b5c3886d1747b4a8791b5324286b26a9422a96a1b013154a7c9161a47b7abdc3c9322ebac1ee2222c5516c6938902116cf3ac6d5083492afb45c3ad03494ca8a865408694a8833aa2c1c4957fc26021024cc55033ed254448b0998a9ec690979ae7545badeacd0953b9ae7a88fa06269c4f5669021c50a78bb5461f54947c9544d0d0f6142571fd1e9283d62a3d9dc36c5d3f4c87721c7b4a93a52b348a8954252d528f67687f2548f1a45110980a940eef54c9427b66a8cf910d4b485629320d29d0691c5f295284856186b89a899dc1329d369fcfa275fe444770e222a3c3fa649d25a38a14788e27d52850a3c3d9868b8da33c049966bdde6e304aa1c731a4a135d0980816cf33ea3a81916c5274184cf41c7f479097993a4589d414c54c89d22c994ce23017588b3cc057779d6c538a144c99f031f222c85265de6bc443e9e63489b428ef526229d0d752a0677889a0683b148f445d63ce13011d641c4cc8737bac2ba7d0a3a8d23ad1e0d72748721872178be308fe47bad1623df20e4573ea85fa23c99254219e69899e294f3809330503942a060e677852cf1a5034e9f24b50380a2289a2afd78899444eb04b23a1234a948b19442871214de14af13ac6d4c916750713e8de93a0e4253245a3a3ac4be126f3ec34a4642a2c84a2e81a3a96a67010853f916348ea3ec45fac57a9053d43e9eb1114af371b6c1d9c6768c336d130ec1dc0c1f45181a04650f940ccd26a0c3e9dd3a05784c3cf71ee7c9f46f142ed4a9154d888a754a14276bac339da0d2a14458a1f47367a54810ed75a0c254fa7583e9d684a85da1f4877181f61e75c443e8e6a17bbcc3cccf3b5367f3d80f788a747b289d621e0ec503f9eceb62a6c21c69339863986f0c5438ee513ec697591d3d83d9d7113c5073ecf57b83dc44eb71a54274e62b8ea3f828c549b3bc8601cd8b470de8a9fe3b071dd11758fb7a826bec9f3fcf57b8eb718f6a11173fd133dd033bce6495d641d42cf03fe4a957999e8e98633c9f409d60feeb063758e6818d63f9195044579c24f750bb4819e6769ee40c5b125849ff07474e36786b1ccf73d85321c5710c10e432d9ac9f1da731941fd9e0df0575a4a768e419ceb1c9ed427d0faa54282271d508d2eb1c698942cf1ec7b99ec53d4754588698a7b1ee798898a2851134d9ee7b22d8a0cf3e98a7b868c526ca51f5eb1107f3ecea458611d5da1cd1910c145daef02690c9b1bc878e93eeb0a27b272289d444c927d42889bb4f9338491f41460e3d8a61fcfa7f89f4f5ea1f4ae853e4757ba85fa222508c513c5b22cd22846f43c7f3ed254d9943ccd6329f67a8c63383533c8b349c604d7696c431bc691ad0e8507fbdc7ba2c7b9f27f0e322e4acf7887f9a4f907fa267749dc621a0e629ee18c210869f1fc9a348351ec4341c44c2135027d1113e9da8b87d3dc1a542eb628445d6436785d33516950fa44ceb678348827d3f8d60eb4ad0d88934c2a5478fb1cc378f61133da36758be34a1a799458a10d0847b215fe759bd9e669ea315c67da543dc1458a6f424eb8899a831ac628cf214691e4c588a3c889fc1b9060ee349d52a42a2c3d99e3c904ed06793421acf989c6849f6a54752a4452d088a554af7495077a9160ea957688b61bc41ee4345821a2cf61d61db14fe359da268e63a8134662b9447b42a84269420ca8f66906618a13a9091d5da8151b940678fb3e4e7a83bd9e7d4048090aa53e5151c49f23c47bd5fa082c24fa8aa7436a2af528c3292a3d90a404518f661254c327485528834c942274fa20b013f8a530c8ba1a991f43e9fdeaf77183e9fcfb0c34ac54a102da04a14e87230a1a15d11093c1e1a42902734d91e20ef14ab3c4e89f1ecef48d133ccfa4a927819f28bb8c13128c3d2af728c7b82ec347509a2e94441475093ec7d4a8d67e9364293aa511743e1a222673e87d9398614a518fb11474817b87d3f9fa4dbd5cacb) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_215 : Impossible 0x40000803000000000000000000000 0x151117fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=11) (fuel:=25) (code:=0x2550529420e757b9d6439be2d83ca26f34e830bdd2309396d1eeb41c37c5b3adc633a941860a3c92a83b3c0d28f1ec7522d9e799be359063fa8e1a0facb3fc510f34a9a47f434cf92c442226fb9c9d7b875c45c63de2a8388f3ac9d6785d50505034947036787b37d073adee41d3b113ec643dc7b28c4d37c9d88873144673ac308de28d078ca7acf16c28a74df4a9f6f911102da1e230f799111fc469863f9ed0341d23222eb134454a23aa95ee1d652c453a09d9293730d4a83c45fe1166f91e0834694461274ee184518184de1f111bc8f29596f77c822cea52c44511ee8d41d9ee90927481d5316f9ed1528ceb08d14c4319c731bcdf3dbdd070752f9d69d04d1d6468a8739d46b27c677b8b60ce35a349521c41a0edf4e933458830ee348ea670d44d1ecfe1d4e37594622445f2f50fa6f9962087b3ac3b93e4754a759361fd1e3d87f144411349d65ba432cf67d0eb0513f8fa7b41e22f57b8438caf3434f509233a2a7d9fe5f1462791e458b623cfe7b0a09d2ff3d46588bac3ccc326a943ec15c640ce70529a81f4528f41e1a4ec44f90c37ca1a84a4a23c771349f274f988a0ee967a0432e4623459254a311a7f52820606cb07bb2d1a7b37c234b2a514a950fe41bac45d1aa38890304096e06a311e84c1c7b1dce90f610383a051e6188141d160694591e37cdc79184c33ad2b116788d1254f94a46c45234b46794a3acf733c8b88a3c0d31116d2a3b8d619e65295021ad1aa3047bad374b623071466b91ef57f94d44420f116789b3f87f519068110637c5720cd740c67135367591622d467d9d41a5be40a74658ee1fc209ac831cd133ac8b1dc74becca8d0819e4fe4e8eaa5075106622068b479f6957c8df1466fa0ccf3acfb1bca521c9d16c7703fccc651dc83618decb03f8ca5965a6c33c4332a3c7599e2ea060b012067981f48f3cd1a3f1dc4d083149447ba0e3a8eb08296dd67b9ec7f19ca337cc322ee32272b48cf93ec66221ee29234f31ed020ee46a3c7b28c491347530c4789a2e9364e90e458e63a8fe618b63d8ee5920602ed00e9cc871dc81799fe44d153ac0cf071ece61fd361ee26445d6f31d24ebfc75c65ee32c8b9ee3e9464ddff1137d193adc601c9fc2d4087b4a8c2134fa4ec447f8e98e93a1c9028d6789d4c417c6b3293a10ee341c27626cf19eeb1465f0d455348e70ed133ac5f46c444693a8a9466f86a7188b198281ec6930b8c83a2e20e8b45c571dc7f07b3f89a51a0481a546188b3c9d80830c4c5f37cd70759e6899851a2742f8fa4e8a70735c4d408f32538c2c82ca268d2548f8389a07f24a35463c93a6fc6437c590f6230903d87475c94cf1dc811cd1a4e9470176a8440d46839e63d5d24291209edb1eca33cd423e916137033ccf728c43c7f6d99a519fe510fa0c8ef27c8b1e29540430cfe39a6c6b1450a1462d9f43e92a851ac458fa7f4788b3bb3c07d2db3d163b9fe4197c25473798737b90e809c63f9fe1fac31cc5b1f5130b6610b6a141c93b8c458b63ea8c509fd9e7b1461ae8521ca3379064a8db33c9b3e85b309ce335e60c2f71ce7f3cca128cf60f6610691f546d74748736d133d5167503b8c4fa37a262244c831ee439031033dd3716d9a1fd367f8df11679e617529405d622d12226cf36cff38cf53ac78934f320c673ea3c1f5b61ee798b683a067fb3487bd53e20624b349b618f717ceb0be7f93675b6c898eba47591e3dce73adae34936618458269dd8630d3a3f8de0fe3534c44eb678c335a141f4f71867f19ca138c8b889010ce2d916652227d0513fa859a7b4085b27c8b0fa0d47d3d53a32a045121e426063f8fd4d87aa0c9b424953ec889f4691068166bcca104d22c7f1e4d2145020b674a823cb3c353cc434259a4481a8f2697e86106122c6f269014646f669a52a1145b0b60ca3096c5218c9a418ce813d47f10cfa8f089b9d113e98639d07124fb3cd571ce619f689bac89a76f71024d9fd9a226f738c7d39dfa509ec88942187113fd231e5ae7d83ac4495a267fb5c89115fa0a2691dc830c4411ac7f23d9a1a48f22435c692dbc445104faa37c8a11163f9371321c50bad23127719d689bf444c8940c9b48cf719c3dd364aa2628875145125526e67a270919e7d21e2207e40b5c21d538788b47627111f44445189bc4ff40c1463a4fc260e0594d8fb113f4f6035ce6511bc758e8f6a1758eb40cfd80a1446451309423d9f28188a448fa0a296a141ed41405d6958cee70814059a3e9e275c0e0e0b61289a7d15427e6796cf740cc278974719ee5121e228f10f84a268c91921c57758288f7112859a78bcc44e0e30d07818ee798398ee55334424d73c53f4b62687828b3606112d7618517987d7796e2207745906750ee7910483a16021ae752154241ca122a8ddac5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_216 : Impossible 0x1000000803000000000000000000000 0x551117fc001000000000000000000 :=
  checkChunk_sound (initRounds:=2) (rounds:=8) (fuel:=28) (code:=0x6783b0ca52066191608f52bf5d70143c9f28c0da7d8fa339d71b799168ba1e638c302d9dc6ba0a26418c628d86378a3638897dbfc31cfb1f51b45c5513c5b14c6b26c9d348776185b0e5124387b8fa8b9a63ef31fae75290a0e663bcca30e2c31ac8714673a2c38a048f44c4597c16cfa2a902389ce2671345a1261a241a52a09ac346c691c47d2550a27c1fb0f8b90a4a9a50d1ac895187fa8d1ecf106429e626c544789290a1e7e8f36387716d133ccc315c4f20c533ed46a58880e33329bed4347d2b19c5745d1321e24b3526d861c46d16d134fc1c88b1c47d2d83a428b90763bf4678958f23e90a5d1d516368d611138c1cf744885444a393e45a2f0747e264ac9f115f6418eea30c31ac835198ea50b68391141d3e2294a8f089a7ce63394128d2a3593628d1e4384fc443ea8d35434794651347c8ca22898faf742451a851228d4af3092c1d131dc52a7e84c7caeeb11e619fa4650d3f5d6e77688b10f8fa2245c4ce70a544e3eeb1117b9d68f11f8998e8891e3392b4451f7bbcc38bec2b9ee20ceb2245b19c9abce3e4788f20c891d4f744e221f698a543aa25421dced2851145a8df2d708bc145f4d4ef889f27680e2671a47d1ac5788a14e71dc7b618848fea323d4a758949429691eed39c8508f869f6a2871908ea47dfa1c5432047544834d0df249cbe11650b3c898794b11034a3c8b27e2223e3ba2284a2e5727c857691f284694251345c3ac44950eea57ca8c116a343d338894a47bdc8f94a88913294fb4bd1f45d094c51507d7bbe54643bcdaee307730ce70a34f9fe87c4438e1e8dc240e27719c7326e1e4789a619ce43cea7e88f80a9487bad9ee9) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_217 : Impossible 0xc0803000000000000000000000 0x10551117fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=22) (code:=0x12145ccd0f3f4731fa889422d8e616ca12354713034bed191f4794a8fe8087d9a49b3d93e46891a371f09544d2548d196b8f980c441f51131a7d1e44445a1a21a6ba551988bf43b88b4ec1dc5b29c4cea255aef927d3211e571bcd71f28b10121919404f96b8aa2bc44ed4154621b1d0ea4fa3e4aa4a879dd0181821c14218aa3b9ee6bc448d08111c6f1ec7f90a06a350bac4593e2848b4ad073dc12a674c8ba398fa3f8ea4093e508a151c0e2207d236262fc6c8dc1ced20e47a264d816d1f1317d3e4ec460a0ce812268c92a30a1a3f81fccac540c44ed05b314ea4f8e21c481a328da829c9eec545422e4275a56226ba6419c73408339331317c8b464951ce066bc1c35c733888d9f61a468750ce75b5d071c52aa37c8713b43ed13479466ba84991330d848294534c8e67535c1c4ea8b045c66668f1d68da8c8d232238e628cce1f6733e5ae950a33e87d1cdae6191f0d0e28c94a4a8e65191a3ed1f032321463a94c5f1ce3628e16446062891a9f7eb9c4850f0512852d62c24eb08f73850b9d3e8bc0e2229eab99ceb1032f8e73883ea7d1e17d1a75942a343e0a4650f40c6b2229aa1a7d242868be0ea38b15324dd3e81a2c75a2622d15194e76b94a8f2328d0751e46930c571ed0f889ce81a55fa12a93c0c93bac8b103768d250a2e194412548d2847545a12a324e1da6781a4684bf602e313e146219ac811bc519d67b8ce7f4c8ca19c811743f8ce83a56154a36b875808e671458810dca3294f71ee7f1f290bad1e1d47d1028f1ec19d072371f222d7518d746d1f30e66222d719dc68b1ae4d9cc7f09f47d463f93639c3c22d336bbacb618af927c754ccf729430dd6879c60eb0f3388799cfa3acf73fa641c4ea0e2751e52b184e335d32378f628a2d011c64c902528fe33a028f3b8409f2768ce1cdee9d03aa426bccd2b458fa990e6a509f2fa6c30cf7999fc8f11e7e8ea7db8c529324251741dda0eb1d7ca16a37384097c528531cc618fa6722c289fe4a3f66e144b222c7f1cc67166023a9dca34682ea2c5b1e43919c1e9fd330b422dae879553506787916518fe19c371fd153ed1b4851d27e6a75a347ba1e1c70f20ea335e2a99bb542e9) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_218 : Impossible 0x20040803000000000000000000000 0x10551917fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=22) (code:=0x7f07f20c774e6224aa64754348bbcd0314139d321867a92d313162250bf46b84b35ca31fd1a4c84b265351c4837988d4f8f761ba439d323a90639cf34e87f468553cc3ba8c3b9c4754a88b12c7f50bb421e6b1dc3aa2c837490322c7f38a1c39cff27c3b9ce84a5688a5f030e788c9c7a8468fef5495313162282c3d321fc671167da666bc442362e0554c9066745e0612b859069ca7e9699c5b45e1eed30dd22345b30ce76583b8ea831c48b1968d05174a327a91a4abb5463b4f50ac3a8ba3384f41932df1c47e93e419be33a2c3d45719d3245c993ecfd34a4e7f21e8b9fecb9197c1f4754c90e159131dc888ea444713e9029902b8d6557a8fa2fa34308faa11da629fa809fe3aa55460fa4692b0f3a50121e50a7e338b6ed0ce98a22f30ce4783d62e3a92a339064391a1dbe19c3397c5b21c77105508ca46c043b9c43f5ce338b6c50318098a0ee3b1a49938911328fa39d2a6f9d516264f311a1428d308ea0eaf53a4aa4f2223e8ff4f88280a2c677b8a139c3091ef30593cc3b50a1c31b0c799ce990d2753f9ec233234aa2a45448e428ac24ff7a84fbfd3148cf34d491a62389fef54c8991ea8798a339c438a1c7fa0c8d061478f7234f62583092cfe3e8e2a1829053f4df264ea4ec0114e26751c5642fd424f337c38c8c798ce5187b479be268e22352aa140dda082bd4ce7d0e2a10e27f32c4c8e4551946140879c8c3cdea81174a33fc11e8ab2dee6f8df1a67e43c1443e46ed40e026d04c9d4ed3ba020e2e717c1eced278da2a8e29545c611da348308ba5b0c2711acee8f084c04e947a041da6b418613da3546434711dc39d01444617ea54e91d23b8ba8d1413f4da738453147b39c71308ee8f7b8808ea9500af1127bdd8676a0c15c812d99634a3c47c0dbe4045d11e40ce2254f60798096de6df39d0e28d0f1ee3b83f49d3de3274a64ea439c46b0e28f1944787b9ce958ef1162a2e268f7186772350907161b9c5b0b68774bcc1a53220888bdc4c9dcfd0ee6940ce28307ba3e22619062b91a3ccc328cee1c50e81c04fea5121828df13c8b12a2bd1c9d0877ac3e22508774f847dfa82a1610ea0a2cfb41622878774ec85da49606494fd40ca143c1e61aa0a32077929f51921e0a5091e87c45fe49cdf42d0524eff28c48ca14593a7fc844ed1e38947038093721c3dd3e80c44a11164f86143c9d1d48b27cee11a7710c8b7b91180942ff35dd2eb) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_219 : Impossible 0x80040803000000000000000000000 0x10751917fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=25) (code:=0xdf22c33a3e37c8b3ec670de221e7113ac6d30c37d061cc677988e458ee617ca546f8f6658eb27d13256227d1060962c9dc7d469114d8614c89952ba47487b20c8b1069926c9537c6744e2236bd4529d67ca1a368ce3ea0419d2a4184b458e94c9c40bf15509364c8e284810cea30c660a4093323aa33cc79c0dd222c511c47d2643e93274bcd0945dea3d4e94347aa646941830c341e65d8190951ba54a4451322a2e861944ea19d13529c419d4a444ba4091e459111d45d3e9330d0c3659e64c89a1024d9d46523c8ba35f21c44323c8119441a347326d4a1ccc33dba44d93244d113ad06f508d798b2388d23cdd68989a3e8da7aa85ee7f01550699308ba83a621d65d1f4750c320cf723e56999f68ba726ba944ca822594a208bb054a42e8f71d7e8997a81d8be695091b3ed2117d2746479cc5131023ed033cd1b3dc338fe834c90e1a4611c51747a9479c540c2f39fa2a528950d2438ee6b8ea418fa4fc6ce620e064781c54a671ecf326c4d21c7d284fe42d193ec714cdee3ecc3454d720d1f40d16fd0f361a668b8f32662af503a93f217ac1e22444a50fe3e9ec5145cfb0f2438ee7b8898e675bcd1941cf61d4ce7da543fa0409f39388c2638c77f91b15e22106a5818a51dc67408f30d230a0c5320463033cc506318f7131fb1914b2b1068c9dc13d8e3d8ce717b8710e27ea0e3b91331de6758f38184f41a94510e23c9ee3d8a231a047d3fa64106f73d883111308c63e902c717c7716d3281a7c1a4611c5323d87a1c8ca1fc5f409d625a6a8b1e6369023888fa2641a94793fc7d18dd63dd178183dd4a9945d033f8758fe692047b10d168f7c91121c7726e3a9f24445f3ea644099446d8e81a6c8d863c6d33484732368b4ae223de167e8a0a64c37fa06831032d8fe3a9fa3dd1d41dfe1fcbe1fcba8a9c4206ff4c841c6cf68f0fd40d062f8f62d8710e23bbdd2117cfe40c4c8fe834d87114d1e438e6a574b1483929758ba08120d322c8ca3090ea541d8a1f51141c8b174a51fcdf32c41841874419f45d4c9be759c63220c7d8487f41cf33acdf50807145ce6671135c9f1ccf31023ed2745c99b1e2315464252908a238a64c74d622eb7a88318521204408a488a543e8419d63fb0d173ed15628c23b9c40ae3b9ba26204154f740828c44813086131b147f418ea295153dc830511a43d3f9160ae2695506c523675bd475b5ce20c68116c671c47f3ea641c4f33adea8294a4a8657ba06839f694b7df20ae99c0d1b45d093ec90c7445656455e64f8df8ec1d4106fa0ce21fe8340cf73cd323f91a40d02f90ee0ce3f9ee811d532848831fce2434f921b03425bea574a748b895bedfa2c8713ac93a268ba7299a5663a9507888268a2958716bbee421d5116f94711f2b1ec338e290916518e630a2a4fdf2fb0758eaa323c6788a12d72128c8751cd09464eb88c1c2671195b7c9d4a9020c393a66478671cc994e49f23e43190a57d9f23ed173e5ee1d40cef77da16a51747d3e5fa25b2b3e6063dd0347c444448f9593e7e9d707629173e4a19f24794628cd747df6a39869b8f627e2685a0e7ba2e63c440f28341dd6df7a88ec1d110774694b333dc2f9069aa2e908889fa7548488a4229a95be4f83fa95153f51145dee0ea189fe52a0d470b22e99811a531ccea3f91f338a8717c84d8392b529860714591a399d546fb11e20c5b1d47f388fa46820d1b150c733d3c7f316227e8f90fb153148f9090b4fa2f0374830bac455f66b8d7758fe81bf4819fa8c8f675c1c0a295115aea30573dc7f28cd74ce2ae937d42ed) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_220 : Impossible 0x40803000000000000000000000 0x10f51917fc001000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=27) (code:=0x67419328ca1ef90f986bcc41a9486a840ba670a52e8b67116414b17799f2338218b27f0ce87414e21c506751ec4094a248e2cb03c8ca531fc3f99c711e67b3abd5360cef90317c896750b2eb2951a206671e42354a7c83ca6e2e75bcccb4788130c7523516474294b6348f621ceb88bcc3c8e215c834c622268def904730d317cbd52a19469235430103f9950326a0a348f3464388fe41841b1de643c05d665899a1e84c1c8719d0345c8bc0463a02f37a89b7d8328d30d3ed034c440a3e2b8338fb31205062fbd441a0a3a87f14469414651d48b7a8fa4094a7110e3a91619c3f418de1a4e29509e7a838bd44d2050d418d2458389a4fe4386f1d52b017ca7413d1a4e8fe2754a4163a4a87b3a88b8fecb27495103194fe19d063d91a1ed2aa522d078084d9ad420fe7e8f65092b11082a86621868303fc0e3a9b22e8f1ed4b0148de640d2b1fa9893a953cc4452d45c65cae1613fa9c7d2d223174c52b79a370d0e2136491171d67a7149cfe23e224ac05f2f70b68488d0b208f31e46799591a3da550503a94cf626c6622134674088380ff2b1e4ea829d71f2ca6c8b0a5414e23ca3c38a740ae29a0c6718c8b11c4ae32878f91e950874aa34529ee0209583917230574463263906a38a3c46464060e21d354861eeb246f745c0da3a91b011cc0c9b9111ee463398ef37a90906749657073dd1742c8b9460fe8d2046d1ec42e568b9750583c0420b013dbcc0f30780a42278f68c916eb50bb419d072d881bcceb17c358ae3393483206cb05d4246a770ee514c8df4e51d4585d43883c451d0ee3398e87936f942c8722c888ea0fe41a0e9921c751329b494a247851cfc8f1e4f618e77a081f66aa2c451d14f45e62a2a72a0c3c4393241c543f8fa4d91e41c0df2f31f20f9639e62d9f47ca0c791ea7b18e774c8673cc7b4387b47bfc7c81e5ea63bcd0f4741e5023f9067723b074c8f9439030610c4774cbe48f90eff23b074789921d071752340d16eb6287d3ac8307542d321ed971d03fc74eb4c93f11098b0c5541c7b26a0e275888aa62bad323ac7b478445553d9d4814dbcc04b419dc3ba7c8f75bfc418958339f4711e46b0ea7f888c2409343f8ce3c882309dc1d4c738a1e408c2cb1453220c731bc67222409fd36111628caf348d0347be5ee2067f26c22333619364384ca8c98c3c32a1e8ba364d90f11424338c33f946418834d8389951f0362bcc15e060e27920d0d484ee4d903438711951e1c44388bac40c713389a41b7c8c8ce20c4d1d4ee81840d868e9c4750f46186b799dcfe3d87740c4764681be4114caf3478e64dbdc4ca36339fa9986e6187926c673a8e6cb528144cf2520c799862f9be21b2c18e6713c551dca2186673f9113a8418ea372943f2c8fa24a7f20925111288f6618fecb48ceb3fd3530bdd1a20c077389d6224f83896c4f9dc3b97d3221c9f8183ba651aeb0bf233d4cb0773c8672563ba2281bdc4cbad062051a43a944690e6383ac351d0eaa0c443899440932f50ee8d7599609e9919c4542419d0332d111dcf2268e28120683911268373b9fc88a1c40a354af307d1d45b22d3219c09ac541a64c246883514c50837594a6f8ce790f48d4b50223a7929a628ab150f2f50ee458aa2f8867b8fa3f8b6750be81132134df41902a538be53a4b4eb0ea9d8753d8f27717c0ea63bccf67fa2a4eb2c1fc4d98ac33fc4b1acca4e8c70ca4d84d9ee2e969f6f328cdf22ceb110458a88f1ed1d17c339fca31acca6587a01fc86cb1c47b19cca9b274419dc6f8d4a304b3ba2c870eec511665934eaf9079174cb1ec7723c2d99c268e24d9fca337822c0e1228df640c7f3dc5307bc0ccb4190e47b7c1fe2efb0e2a37c8eb3dc21e831dcce2e90e758eb38a74a37f85b20c7f61a942c8d67b9861ec5f22a3d9643f8d48b904ff0c32747335a95961fc295864114c8b1e4591d4ee8d809154b51908726a060ea873dd3e27dea8593361c448781d60e8fcad1d43d11206f56f80e3034c91e4d7b88731d0f265f6f9242918750e29a91643a2e83a2292c0c22a7491a06f56f87e93a871fca322df65f1033c87131cf31348328c8b3a9039291f0113a18e992745d3c93e8124a3885d425021d5061c4753f8757b8611e47107f4d975322694618675459443e8f247890946f310e419023eb1c8b98ef7246df7a9ec3383e99d0728cd647841145061a8590be3cc6763886399466b7aa028d035469462a846c3cbe10f404a37db1c4ae0661bddf21fef728cc331c990ea8d18e7d3d9dc444a31c4a23c8338c6063d9862069b1343889a439d41c4929d23dbe071208b2771f21c5173e4ee44606991ec38a061e9e62ca3c9b7b901104df28c7f46a95da045808cea29ea9d03fa6cca3e8aa269d64753a22ac70dc32872338fa259fcf52743ebad1af31350dd1ac30676f8879be7ba34711f4f63c93a07d4d98639bdc19cf73d946288fe40d1af312c08a4d3091a9f2749597e2a48c234f6f33dc3ca7c517abb542e90968d30b6fa461ea38bacdf12a7586fbadea80c8d3a37d2d1dc3a5234c93aeb22dee398df405f611988a662647812d16eb3a54622cfb264fd62823ccac5455413ac639fa48c7d7b81dc7d4558aeb1b45b3f53145e3e263116fbe40515198e4cb15f309485254b441ceb2946b4c892c2d1a4d91ee90a53e51e11e7598e309f638a2e5186741a947dbe58a2945b2226f8e29527ca33a89f0e62d93e3598a63c446728d02222f93dd1b0123a282eb4860246a2e3e932264f77c83e4a5809d2c718f1b969016fa74468e23e4ce51888a8c712228f3ac75a658a144144832058e75be4639f275a34419be994ebd5e646cfd42421d1d44533638ba409464f92d47a8228d1a84c0426701528daf713a23679bdca35291a7aa461064e8fb0f7cba5fe1f2951f4fd4cd131cc92a8c9f21c45ba48b9d2f301454a4d4393e518e64c84d185021c5163e50610e7122c20e2a7b90f1361645ba475907193a87bc2c873cd0716c3890e8f11e38a2c1cca22d91681628991d4f914683b1439216358eb150eaeb18a813e8339323c8a22d94638984731f4518ce629d52b112343191642d333dd1906188be41e4e23ea264a93a90bac8b4c88995cf71acc5478e63ac8b4cc8fa26574b4fb1ad095190b1f4c51d68fa5b011b4f7425e610690a567b99c99a2c52bccc7749dc63902445f29091126c831c43c8ee419164f91a83a6422ceaa32231523dd674884a8cdf222eb1d6714852d79951048e22e9879d6f945cf3222c71d70185bd5da11142502469be519ee7e9d2218daf30e612b83b7c73439460a26f94707458f73ed1e3a4771847d468c517ce928d021e4952348136830a2c9d75bb542d7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_224 : Impossible 0x803000000000000000000000 0x10551517fc001000000000000000000 :=
  checkChunk_sound (initRounds:=2) (rounds:=9) (fuel:=26) (code:=0x1861f689a071d76c452b23c9f187010be4aa327c91622c990433fa94891cc853a87f1cd360fb4465e9fa4f0342e0246d3efd04d1c4f93b475204fa1d43b8fe19451428853c8f63ea5a3aa643aa25390fa429da3a91219cee2e9029f0459d45d8ec05861645d405ce0e247c74c31f41ccb23a838a64ce9583d8091e77071224738ea568091ee752875404e74d8ef07d22c85968ba8f81ddde8b768778290173b0c8f9ce2ea0a76a6c3f8a23391e80a3e51a9484c3c8dbe43aa5a879f285a3eff7eba41c5334251651a1e8184450f4c9fc6b2550923d4a0ce777fb8c3b4a37c83b8f6991f2a346cc242d1b44c7f40ca33885b1e4ed4086f5090a1dd3b23c0f4ff34a8c45bb4379da39845ca5213b63efd40c25e9522d0d61a0647b9e021f27728cf728485878b2224e3132408fa458187218ea64b208b8ea64ea22dfa3dc7f3f602479dc8e8ee2249b264ea3e90285415d2eb1fe13345a42388fa87b3d15888a0a22ff52a7e222751322144ccd27118c4b1d4732548d9f6228090183a2a1c5128b295ce08927e4284bfc28c1c50c5d014444f94a83bec215868ca22528b68bc3d0b03bcacba4c90e318de858a133d862fa2dda444690751f67e8da32988da20c3b9ea96c04890ea1d45b13cd2328c261c454a1dd1d30e2aa3798890a314586a10e3111dc4e48b84a4a90c2c3a9867682665250bfd2f5048b0eb1151b8c47e22f313261b9df223d11484990c3226224ca3a38942f333c30e428588942a0e30cf33f507508cf41cf3073448144e32b8391e225fa90a850b8494f5042966f5110aa33ec378ee398ea8993e4c8754591e40847cfb5191e899452d0e6a1448fa11e3b9864f23e26a8d4b2188bb4506429c9fa3e8445472323cfd3ba568381152a45a8c8f5080ef4151861bfdfa44c7c84a848b20422c77518ce47d537e8a386c452371861a468c93a3bcc5152247d097411323ea3a92a128a91d47dfb11204494791bc73348ea1cd1219d02a179be44b622369230ee3098691a8df242c0428d1588a3683bd5ee133074341029986a02f31f4fb4249494139c4a63ea580a12038a0c8f52b9c8590942fd2169ca768fa0ea89ce39dfa4e5ea2144101dd32415253b294e728e1a7e9e4f520e4091e51a2e021451f41cf33d6122170949542ed03d4750913a1f9dc7d8f86916c7322d2f08f318e6768eaa129476b9dfa4081bc5b5089e398ea5293a41903251f4f523ee70278d33f418de42d093dcee4e8fa997989513c1b64a3b5310fc52a64531f48b8f9dc1c49997a02479daf5125369da7e916a151be5d6d70ce9690a1327a8d2678487519e2219df223a85509ce22e77a95111118ba123cc6949d0720d32f514a873e452912e72843a9ce41a12349ea43a4a0ba95508a54487d429ce360e352a0f411b5192130133c3989ba6c6d808fa853e43ed0e93819e4ee33ee1219ee37f839912ed264693e5af110e64a8424d72b9cc87428d247a861e1f6e749ced3a5130fb80887cbc8eb9d079886593a26a51d2889f293a2e8e9ceff23a0ff178088550a6293bd6062223486ecf224f941c2266621f113e5c68392776b5c2ea2a7490a871320be9983a2a50bd51620cef35c2193a4a90f011f2809eb090574194a3f9da5092a10c553fc693d50ef31e60ed87bccfd2ba1214176bce0e4753f33c576b81f738769ea5718c8139c9e236d741d1641cfe11b7eb9c76b5c814248741a3c3f48b3a91d48c40a030740cf5155da79907474cf848fa8510645a3e2784f4291e252f583a0a7691b1fa9c9db194544cdfa4e9070173a644ccf38e88f7c8ea23ca541e06828573e51d7a88142881cbd32e975b6c23b151b50a529f2073889d4692640ff03808859dc69494996b8fa84a9489a6e0e241a8c425151c50e44a85ae1a471205321bc8121d4a1ce0641cfaf914a22a776b8fa8ca221f2a13ec4d1f4144f92862a7121aa5438d709d8ba04451cc7d1d469418f95186bc546d4047d42bd5e61dc732548336c48d1f3dcf921711424fd3b9362d8fe41a64444f93ba8c4040e32d449ee2aa471127d07425aef311d516220f3254711cc6f88b5d12438fa36a02851014d9467cbd420f093d53e7c8e28ec0dda212db3b4ff504a14143b90e849094a9da44bcc28a0c13a9cc7df27e827be4fd20c2b13a8cced1b1a4db3cdae990db4c8f37a8fa7d814536d710e1ac0455769fe85759de3d5091f47aa0c2ea740ea517aa4a30a029b13a4d8fa8ea244da2a448fa75a1447cfa428fe25e79c0c8575a65d23d88ba948aa151f414ff44ceb46c7d3e44f87d3acf9404a57e86747e22991fa7c9f68aa6676a064cba5cec7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_233 : Impossible 0x803001100000000000000000 0x10007fc000000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=22) (code:=0x73a8c8f3f4e93ccdf038a2dce819033790e08c8b3cc8ec05be9507b3ce16788518be75b9cff36cef31d033a411e712d9460b6556f8df052e8309ec6f0f3438fe3d83d97dce5d86880a3ce93ccdf28dca0ae7137ce93949a1ece565a94a11ee869f680880974516f84d2287b99e32e0223a1a6b974de1bcd137cd728c7336c1645f1244513c5b0f4fd3d87b3f4e6e70219bca32e8e68698e3d88331dbe8511e7b8573990e4190a6f9341ce513983dcb58e6f873174de47b2d4a0c36f9bc7305d3f4733db9c65134268f608e5d1947331cfd37a1437cde63b2d2a0f7379470517447e0a870decb3682b88a731946b0495de73678ba219ec89a4a67a3c86b0cf302e9ed9e6b9cea304539cfe398decb08a32a2228d421bdaef724adf3eb843585b23ce33cce242546164e63d86b212639ecf3395031cd96103438e63f32c739ec5b136020e2729d7031e23887313ce57398e77a8c8708db1ce5739ec78a02f30f6cb6890a40cd731c3dca230b2c4851d42d96689e280bcc570853991ecf3788fc7474a122063f0e60220deee738dbe0aecf0fa779e6719d242ce384a2608e9545974214ae1fa74c0c81b9c818bea32e9e61f50971885808cae50fa73a06849d252bac73a02459ca93a12df0de0d630a8cba83916f78285d1bc7b1fc7d1cc518fa202f327dd64545d3a58ee70a53c546174f11bce9638fecb0d633ce61f91e2d8f67598e5193e1ae4333cde850a33a4c2328da4191e0ae7328c4327c3308db3ce6418ba6f429e6f70a311cf13dcfd3e8a237a2dc218e739549502d90e613883f35896418f609e839859639823a491c4617ba0e63b2c5b37a9432cf6517cb741bce23d9d637dce3689a03b2a97416dd6639ec73528415ce6f975ca0de739ccdf31d9616d4275) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_234 : Impossible 0x803001000400000000000000 0x10007fc000100000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=21) (code:=0x9a7c9ee08b2eb8ccf3ee0a294f90df3689af740c5d868df65a5465081946cf38bf41ecdaa121415d464590d4b41ed327dbdc873ac8b718cb6dbd432dc6679be7d1f614adf4aa626590a329427c9d6214fe1751632cf60fb26bd4c302e9bc4f8688e248ce7d8c33d9be45a5485113839d67c8f66fa85ee22ca1678659167b9fa83be4eb17c0cef989b3c08f1114872249ea658be719ecfae507cb7e024c9117b99211564a227bb8d0137c88be4d60ba333e47c8a2438ce5333c19ca58194667b0c6199e518b6819c679a647cb7dd2458e73d50b404d707b8ff1d4cc67658cb39cbee93ac0cec31fe0e809d6df0b6cf0c73382389e138af172999e40409e7328d962d99e2bba433b8d860e551b2cde202f96f9ac8b3287f28c6706f264b62b9fa308bacf0458c9ea7b116530ce6f9d2394eb3e42e8cea4ba4df7b87f7191145c33b94730f788a92e907f74be4c96793474881bac21b9c399d673ba59e6f840d3f4f99c7f7197c3a4861f3070ba7b7b817e671171b2cfa4441ce8b338ae2f8de30c8b116299862f8aee51bc5b809e6a306751b8cf7111798f3809864d946379ee236f97a86773b7c6487b916e5202df348fa618ae4447d1117d9e689bdc5f42cf573879b7cb639dc67b14a339ea368520fb4cce54448e4f3d9363e4de1bcf56f9c6cb4a9050a57c9417983116e0b01324458fe88bdc889f2f51ee2690e7f8b62f87b89a2da16f9266aa3dcff30c10d1661934ca148c31bd4a16cff8cba43aca5798674b48b7c889a2cf37bb5c219e6459ea1f29a94ae91bf19445eee7051be6328088b8fa060a57e8f67ca231916dce1ac458ce3fb9c8b96dd2cf206358c33a4e796840586a53fce77b911438e71ed163385f0a4e94c8e73ddea116819cefd4e5110f6f73ac21bd4df3cc15d466fc060a0df16c6a7a9e70513592e338b34218828e243799166187d17d1a648f319c3b134f146cf552837c6f8ce6d10e3f050392e8339c63a39d157d9966b8f335cd6a523efd4341be65799fe6ba0a7a996cd11d6d9be3da34435ce7e9fee58083fd0f749d60cecb1ed2a6b8b6fd2063999682a940ba3e91a64a0a93a667348e0e41dd27591d3bd237e9fe1bcf1254a11aca53252381b959ed1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_235 : Impossible 0x80803001000000000000000000 0x10007fc000100400000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=26) (code:=0x23ce72227394245846c433da84fb2371127a8a9f43da2c1ec8521a3c3e985ee08b077882e89a2b9f420a28c966a6da143acf73ed07238fa2b9ec0871f0744d34a2c7db9dfae10eb8894668a0e45845542e17bb241a4c244461b9c67324cb23c3da068b184ba2691328d0323d370212e81092e915de4f8f70736d9682883946ef738838f62d9dea344c4d15d1150b8419c9f15c9a40c129229fe067186789884a0e33914e65d3e440c7f39a266f0e6898baf765833b2c5b3db24838e68ba1e7ba0688a32813e915026c1cae3f8392399620e4d44cff338aa206273582391455174de1485719cf6c919409ec1c4d2b9cc7b64840c86399c25d414de1f5867ea545903395c3d8af154f470934653ea841965b0142b94e911338ca3478f7748737e9963ddce7286923d928e88f3c505394e91cda24aa9410f184e671932650d4c328dfa0bac37280baef21b94e939cfa45833a8c7f1ec855087b206519163d8ae5d19c6b1969ac04ff14665ba4818c29a872828ae1dea30731fca332b2c72c0c5f3585f458f6fd05ea568a34175032188188b349ce7c9922b994fe528da10c6139d0505d7196c2dbe46f0b7033e834c04eb202e3384f939c6740839902e5116eb1c2218e6951d6a1116e3222899ae7e8ba26a0e20ee53acfd7085b7c9f4174953e942e75188f16c186e18994620b11718e77586172a842d83398457114be219c67d0f7618fb14459348fa41cc92b9c6385ce45a54f608b34be4a514a9292a30e031120aa140c349163388bc451f6494ae341c39813cf62b8b639911308ff052ea3a908ca4a89a349f2e73883eb8cf735ce1444e708aa5165321f232a8ceb0cee30fa730ce47a9432a1e8d9015288f99933758652641ee7d994fea505b1acca39a041fc732e8ce519449b11234455163f9ee4566a5182f974a31fd013fd1a38a841cd493e91e0e1204fa732f946174e20fe8f52b9dd2cd0de349968383ea15de9f9071a43bd3f3ea14ae49c692153f3381bd0ae14d4e56b83ea04d74fc6713cd1738859acd11846f1f40f18a9f4714f8de1bdfe478e6cb06f7f9c28e9071f5ca90a7e8508ec1cde89a16ef042dfa9f3e9a284915255ca12cd147b9d4622e3a4e196a0a84a168507d1cdb6cb236e70fa1f2cb21501345054cd170fb1d839d20fa8544dde237134cdcee51cecd03ea15def13f8254e67b23c778779bd46278ce47851936ef4ae369d90b3d87b19a2e1928b9f4e61cc990c9398c93d9467d23e26850858de6b23d463d8fe0614a9bc7d39b2c3d88bb2ce680936479320e71746e260cecb95b9dee32c3f4d677a02e1324e5132f92948f0e7485fa7f9f21030b789caa345dc606b5188f2d833a6a8ec5532789f242c04d8e99c5f41d464c8866b15d1a32c4d649f48e828e0a5d3c4c93e8a25291a34a143289a0b7073dc7b8b68f3fd173590a12c11a978dca51f9251f5968390a6b39cce19cbe810d60812662a649f2213e92a528ae1273c4c93fd466b10c8299d01428d26f20a1847b89a3388644d313885219cb668a3c11ef7268b67e8ce6b1bd4a7285b1c4d11bcca2c842d4a331a4471bc7123d0a0d64c9a59626484a151746809685c5532f73f4d1394f13e43e5964c9fac91f24ca34fa7f07e4087ca346d658d28b8729968d688ae3dc351945b1bc7c90246b2c573e8c94a815c4d649f50a0573eb24a521469389ce060ba409343b0fc5910c329bc7b11e648de39c3116c6947465135013a4ba7102316c4216dc22682d8be398966140903649f4339c6398ff17e063fa340868f819c6518fa175ce1a4e63da5516dd) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_236 : Impossible 0x803001000000000000000000 0x10807fc000100400000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=27) (code:=0x46dea8c9f2a50f615c7b1cc9f3e94ae50f642b7c0fa65c1de6478591f4351744f3d88bd35f2222c3528672047b1f4430d440d113cc7e3d9fe7ca349909a339f2798cb19c1645e7309a71174279ed8640df637a94288f6a13d5d225a88a946d234734547d3d474b94fb6b82b8ca28be42860a6d0513389e8d11a33906798d27b3d5becd0394299a1746d1342a8e60a2e52349a3dc1cc70f6ef508398862c9a45d284175427b0f66d1ca8580826b118ab34857487b08d218f60e50677885b1e2a919f4469929909a3e91afb37dea404fb2347b1cc611bc26a42778de7dbd54ae104d3e5d22344d27cf9518e2134576483eb24cd11a4d20cc2474a5415091f4cd4c83f15dbe0929950264a8cde3e4674783291a3d93c8314ac71ccd20859bd4a4f1cc8d28c1bb1c531f4df425174141351541c731f63a22a8ca631b3cce51f5fe42d156b84f6770b84b244b5412b83db24ef4ca02236a337892c5612e14291b46499454fd40442824a9f2149a8ab1cfa8091e4cb8426b0b6b8e67f9ca81b24216c92798f172170937dea20c7310945d3337c6714e7645ce63ec742791e51c2c7b202234a51854b639922048d184a523c9b9bc1ba66061ce2eff052c5cdf42525418fa24a518c226cec30a6f031f4e52323ed4d0b1f881b7c61394a54689294aff13ce6f91170e461174c9294e61178fa6e4f40c9bc748d7fbcd96dd0a12886fa85921151e37ce28085110331cf728b2d0532471378889f21530c649ba710d464a3cd20eb13a3cc34087286a3cc992cb2c5b0f330cce4d0f6202708d5ba2c8fb219a28f0df32dee338b6218431a47996c80c0ccb1bae73451e3a586650ca34932648cb0f761996e92645b289be30c693da0a37d0b2064ca3a68a023de0a3de3ef31eee16e9ac1d26b218df808e6459d65f0861bac939c9a348f365a220eb3dde705808433ddd2712e8691e61a4f96d9d673903134f539dee85b742910466882e90d21ba4b3ade614b44689be339946e86e3eccd1e6d1374ca430ba808ca309ca1eedd0993260610edd3a4fb395e6cd3d4c70c24cb6c1d21997616d12684cb7435194ef36c431e64731cd2344e6137195ee339a2e961879b74f66b10119cf7192df4243139c6f6e91b1ada23247b9d6348dd288927a9d22fb7c3a44ec33446f32a0c04b6f8c47396c39cc718c548d9b67592d798d63add2619be4d689ee0d22d9a2df09a859a2e70f7618d643896798ce2dba59a1ee2e886691be264f33e4df2d9ee264f71945d3f4eb03566bcc819e6df349133cc7320dcf0120222e809f285a068f1d6e90f33dd0b21c7c20667259ad324d0d6738e72d89e1d8ce848e6616e9c54a1baf5334150950b1ba3a4e537db6618596699c09dc20725f12dbe3dd8612d323dc86cb0f54366a6d9d63294a74b44688a2308d11446112c9a528ca384a5618e1184e53dc690e142da230b2c345e6df19a3a54a6fb0cba3d43e5ee6f9de74b2cc31fadb1fa6fb44674c8d10f7619e6cb3d9ac218e605937cf6248ca21c444b7983392d0922cdf1edc237da26da851a142378d6528d23d8ba41986e542c3dcdf7a9ca16602202e57586f98e593da2a1b626bd5320b4a13d4de22ae96186fb6cc71cce952b84418658dc3940d9279874a0c41164418b26924e6d9ad320e235b24db3ccdedd42809cd17098673bf4c71e631dbe8188ac45ce19dea20645749d6389160868197cf309a2dbacbacd1036f9e6759eac91928504d0d4ce24808d33c5606e72146b0cef320a611ce4c96c40de6c92e833a0c23214c90ba610461696caedd0c73a4eb668df6e9bc264290c3758997c935053d4a11bc8d08d7cb2d9a3d41743915c8f19c77ca4139d64d21b946164840d9626b35be37c8f264739c2265ea72a3a7c9344ca344c8c42e9eac91bc7391a7c8ca308f964b2c264ae2e88621639648d63ad2719a15baf73e9fc950db4b4a57aa0a07d2f9b6508f68d1d236a1a929ea618cb4acdb444f58a84acacf70f3e4a50fa9f9f2528f6a37e87d36d231a4f9284f51ecf1458853e4a522af522d117b9d642492be4889eceb0673acfa114659d67b9b41acfa7b1a4517aa148a87b8ae6d7aa4a2e8ca0cb7bbd61a1fd2d728836fa947988319ceb298eb1ed860d4e21ecf73ad033e821a257c9de78cf47c93441b5ceb6fa5592194339ea439ca648ca6b28c8b0e7234f522cca83079934d6810339c31588840cfa6722d322645d404e93881f5ce87c9d1740d963fc5b135466f97c37cae0ff7a94329359164a445414e720cc2408be1646f88294cc2a11ee998d210d426b17d251113f525184f337e0a1ef19649d2712e86599c9f22c5f16c218b6573e9ec4448d204ca3d8e21747143a7e6b9052b8a17b8174f6349022b9d28f28dca0fae57abac3dcba414fd4947d7f89a284519be7ac144d194718090240c1ee90bccf6a11a479bd592285250658d45733c552320aeb22a92bddc26d0677085191e571a4df758be8a87bb84f6950e723474a0cfb23c8607485469358ae4792a7b20dee3ddd628e061ecb61062695dbe1d286bdc478f33f505389a50311e388d2308f62fb9c5b3f903438c3184519ac80b2cf30c3888ba2bba4812227f72a959a14a92bf4739ea7890a35a02649de7ca6436c5d709f2649de7d45c3da4a79a2a72a1a8ba027a913394696490945c3dbe4e7086a522e811fe8d264899f2849fd96f7033bfd9a3dc11af97bbfc93c2d2f1f317295963e47115c7f07d7cc9ca57e88cbfca57390f032166486699c5f0dca54c8f60ff3d5c24ca5e7999cf93dcfa11d0a0cec9081384ce93a8e102cd3e61697992cb027b2d06e716c739ecc206766a65092ba8c0c2a3649fa3ddfe1ee1243bac23e2e7b94a3d86949d0d10e32c8f1fc8740e2e85a4e0e2f9255057b90b7787b42d0b091f24d21a82b343490a85bad9208766b25e6df0df3ea163391a3d91f3fc873490523469264871edce065709926fb346d91a7d3fa2dbae3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_240 : Impossible 0x40802005000000000000000000 0x10007fd000000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=23) (code:=0xf939ccf3ac853ccc929c3ad021d6cf428cf1f5aa3a8676583e5aaf13adee6b9e61a5be6f0eb39d460889f4b633bdc64bac690f380b7cea689ec1aaf94e9f67a9e2799d6218433d90a871927c8ce438739be533a8898cf1139cf68b1be7594a03494a474459e53bacf522edf0f253b54889ae6a8ce6f875c4503354a337c6fa3e478def71cbce0229d131fe73a021aa8e9a4a567875215d67301bc676a9a519679ba73c0c52892f30de33a8c8b78832cfa478ce459aa889af41196df2363d9be919aa758de4f916c310b3dce73a8f2439aa196730fc876f9d6a70a77587e7b9160be28cd5ce0d28f206d5236759ec6e8cee7226f723b3df2216751233ab7d15474eb404f36887922c6f30c691aaa14fca540dc6fd1ce718f6678870fd15e027891e52b3d351c6509e2438e61cdce6f94aa71d6739be9d349a239d013c473a3a8896c6f22c8e9e2228a673a325294e06a8b15c5316c526f88b4047b374433cda22028f619a4ea0e337e0278a9c7b3c85293a799c667a47012023a9e63d94a39a6a4ebc41c7016793a794c5aa0dea50fc8722c788f29d1ec0def7258fa219ae1385a3dc722b8ce238573dc92750decf1d66b9be23cc37b87222c5f1bc7b15c731863967835354df0e46f53810c2d374b21ca2d3a690434794e3990ecb7c9030533d91e16de68198614dbe3c4f540c5719d15719d47c8731bca311e8b6e87578845c5dc6cf07b9d5e222c736fa2aa7649c440c5b29cde2b8f637435e02d13ec16c92444d129cce0dd2d9e28d94cde21b2c05b19c5f3984ef988829c043132cdedf0374652d99c3915c5f7c9c42225f14c573998e85886659e2689ec1ee6fbe4b6c33a90715c41cf27529c06a659d45729c4983bc47b93a538fa11332cde39cc5e26b9f67a84e9ea7da4e7b9bdbef91f2809edaa1f24e9bc5f1cc7b408dd35cfb47c7c8b681b7c3c60653b546f9c47b3d5923c4674287b0e76a88a733ac6f1aa710fc2fa04c9039204e6419d63d4fb3ad9230a159e9b010a730d28b23e36418de33c1de28984947d8994245b95ee6187375841d255089a2c8c242986e58084d08b11e0e3fe2675d25297e88b1cc8cb9df61168f073389f6459fae7204d57c88b16cf7444e72841a4cf4598e22dee7cb543ed4a439162f8d21e47e7c8a2df0de0a6511bcf27c90ecb0a11a45b38996c302ba1aeb3f465619197298e6f9fe289ee2263f3382326114d86433dce537a154e29ca307d64a1a0e2678c234c8430c3475a9c5249502670869030f33a4e790ce3094e618de43850c35aa3da2c40bddc6e1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_241 : Impossible 0x802005000000000000000000 0x10407fd000000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=11) (fuel:=31) (code:=0x7e91e418e471384610ef378e61cce239cfd70837bddf2222e13f5ca3d9093ca5a37c16ca335cef44c4910cfb3d8c231c5f378ef41975e28905b194ba7e871399f2969e23c4398e277b7c43438cea71ee399123c9861cf013c50323dca38b3c45dca639be338717c8de3e47b28c73465ee778df31c63b5d031befd2063d8d24198e518df73c2c6db941cc6e3083991cdef70b2438decb4488f0718585515dfa3a9ca1c602425dedf28ce70fd65a02f73acf1718a3146f119d9e1de63b543dce637a16cb1be8599c339554e0c244a8ccb33c65a9dc2dd1f24a50b23c1850737dfa86a02f917c723f4e26385f3f4f22e888bbce13c4a51f20be7321dc21c54adf0757eb954e15ce50c30f47d7e8869ca571be9f9f2fd22d0b3d87b528e415d49295fa7119ce1718e13bc61011c866f2e8fa30bc4751f2e51c59ea10fb22c6f859e610599b75468c8c323c5328c8b465be3985322c7b18681a7a6eb7ceb32dde32c83b5440dbe45b0c3ede2619ec39a2323728455badf3d420c5d3745b1bdbe5185d3d883428fb193c40dea31b48719c43429c41edee7587b21281942393ac2b6f8e2ef06d909ba7aa1ae11163d886942c36f9d640cdf3551522a51a0696b747d389d5c61ae349c51930c4360ae11c2398f23a808e3a93c571ae5f454791ce1a1a5364d3d8de4343ccf63790651a7a45bc4ba174da0b6f10f46d388fb29606df0551a4f6438de818e2c7069174710e2f73bd1540dbe07b464712db7cc730ceb51b741ec8b779ba22d2713d03859368f84350316dee5d0b688bc4dd38dbe0d27b51b546f9363d9c2186df11d3560623a2230cf6ef28ce17b87b3cc37d112e9e6ef28dc61bc9b28df6e50f72e87bb84f11ee3d9de4d8aa4185571b7d2d828fb1946f1b41cc8e268aa419c2f738dca1ae6f0de3d8e6df0dee515c37b8dba850df1e61ec6f7b8e6e51a9c6708737d8e5384e3438f76eb2d12454671157a942e13bd0506f26db61b46f0537b9cdde1f4691cde21ea39bbcf1425e6d51151549b2b9f20ba339b69b3ecf321c730e679b84f93dd967787326ccb285aa1b516e5053285de708e238c4f14c7916d161a4ce7987504d361e4711b48940c408ea228ae388e12e8f936c5479b7438bdcef39b7d4e374f113d251ef031d4f945c6b9ee789c26ea2c51a7e938f6758ce3bc0bacb21636819cceb22aa319e62215421ea026a63114147223a2e8195c43428ea659cc2e88e2a99cfa10c7340d4e285161d72522d1ee567b241c4d28c9de2e9ca08b355e27c9ae6eb7c34b1c1f7036f9bb15206eb0a340ccb778aa32ca337ce21c4d7043a06518df1d859de41b7e0a32dc203490de32d6a839b1cdf094e10f6055279ec571846f8f8d241c2d036ea9437cf12e9c21f6cb649ba368d26ab951250850b84553749b1ea6e89b3852f27cc339dca7cb2c8722d1f08e4488b3a90b409c23c9e63391520a8eb84e7374e640c671d51f4db7c0e68b225de70a120e68722c75285be1b4c9285cad50d547cba7a8f332d0310ea56f9c54e08e26bbc671847d205193e4891e4c91c4dd35c8d9420419754aef1427ab85460e133c1d030ef40ce6519bc831ed9620e7fb85034786d285aa4db948090304311e162b94a11d02f539452bbc80b844e542f951bad9e1a5053544d472f90bb0936ce57eb443386726c7137c92508e737c9b32c798be6f99ef5409ba4483cbacdd0a16f81c8ce19d4291badfa6e9e275115f206d7a99650892308b6458ea2eb44299ca35dbe3e8399b67515c7922c6950a0641be43390328467424291641eea13d5462e811bc4d737cb27da2cde1f2493a810185c0d16519b5123482e8866196c531bc298f930d168fb7d0e1ba391d4a139d013dc19084311043517c4533c298ea348d737c8af90392ba24e6470858ac4741c734582cbd4f22d8ae3e892438e51bc5d37c893f5a21ee638e7231ce8321c7512449deb070de2890639a24399ca819ce419e6022265091c7310c5b14c399a423886206471660e6ea1c518a3398de890de159167d1d441cde2b9e42c8de43a0de23dcdf1ee15a852d14271bd5f2ef0f7809ce6883787e3499e0640d961cd1b2e81f9bc690b25d224224ba339f61e4fa2c9277cc0c0522c9bca6258e61199619c75348692e85b0dd12f7788289ea673743117c6d174891d41e4ce399ba449a4448d23c8eae76f87d13cdf1968363a6c425161688887cbf4720e462732b8892e8ea225093f4169ba238de2cbe4d222c6f52479508791cc5b079164e65726c1a8a6219bc8922c2d916198a6399747503f174b2449a5e222cd708b6f923779ce5f2026d0e780b74790de8940c21a6d8e716a841bac759ae2d9ba688eb3e46972a6ca131c174e61ccfa3c91275826c878ec344730c890893790f1f0ce8b1ccd223a719368ab94376128ea1a7299e061bc873bc75344e51cd42df10631c6520cde0d5020de8b348ce1f319374eb1d637a04fb1a489238e66b9caa32066f9423498e6b9f63c47343cf7073238be439a420e5b1cd0b2b9c67bc0c379be24a85de3bc19e0e72c0c89374d7206339063e8ea298e6df07934b1d36d506da069b789be11267bc4df19eef398d511dee0df4d9ee7299cef0dd061c6ef43b2d929d) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_243 : Impossible 0x140802001000000000000000000 0x10007fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=31) (code:=0x1a499458c193b9cf91cec7204608d2738df828f2968eb9292932883badea65873c15256388e8a5053e48f9ce6b5288d060b9e0a7a9c3291d6e91e542f30278ba2c9163549ce71143aa0482a35320f3739aceb2841c5f22ea2a86ba41d8e2df52c0c32819e4ee73cc4f3ac13de675a2ac12e874b9c6952a0c0ceeb2e9021c44f194835291665b0c20c566fa52459274ad8215d4609b1c5bf05204a5475134bd250e2a306b0d8a8f2115399164694627c6d2926c95937031fc0dc811bc4f4c90b3f82b8d63ea64693891f2291f468829c54a1c4cadf7c84dc0c45a0a17c7328ce2949153f8f96f936e731c8d7a817e2e991be0e235b9e2a518ca4682fa653947e16f965885c5439c716f9164e6163f946528ca46be48c91a328a5136418e295a5f1573a3f030eac77480fecb46d3251851a94cb859d2e778843b7c8b90e278713f91b659d246c7337c4c90f274e4e94d4459fc8132c4f28e2a0be74a2ccb1fc278bedf8591b37d36e77d845b7d251bee9234f16b83a916df305fa1f6c132c9b728c13a4dd0d6519be3c9024b5f3172941828d26cae3fb9c1d5ba7ca0a1d4c17394a3883715ce713c81518739154f1e4fe4a531435173f4793e5bf0b07137d4a328f23a9fa3f4da40a1c3e5bed707135e5a3ca4a8d9eac7395e61c48b06b278be81a16c131c6389ecb11b32ce74c885a2ae760b742367aa2d03609f26598ee93f43a58ed7206f3395fe1bee732cfb22a6d31c8d902458fe1fe829f4791aa64f310e96a36279063fa94e570a4c0f5818ce751fd326088d03a8d49e2289a308b23ca5af92068791a08d3aa658e45bfdd2294991fc8340c206c13a86f4c8a63a50647d1650841a64a146bfc27d325287f3041cc7f8f932a525a6506560bf4d21297fa1ee930606f910f46cea368654b582f575894bfdca82816606a50ea3e4829f275294399eaeb1d303389ca3ac2b294fec10859e48294a7f1aa3641ca575906990eacb7388b0ea6e94a7298238c0c1d532608e2928d2949370508d45a66f503fa96060ca7f4647526ce648c3a67a73a950640c1345f3a8e26d31c4f294650e28d49824d19389d46516516f9206138cefd6f8c74fc8d19450a944b46b52be44184d195153cbfc1754246bf47c9cf05196e51d674a2dc2a720a0e6751278591a8b9f6931649b252a2a92819eaf36f80e2f58d9d47f759ca0d2eb32cf328cdf1d635ca74153d0df21e3e819ae969ba478d7277c852789c46f94e339f66b9d68d075a0635a0ef98f9f66b9e25186947c641f30b799821c47324c8340dbe7f0fe7fb94658f60ca1ca0a46df6229c5f247b843e483759ca709031cc836f9654b010eb749be17cfe798338be454d9196087f22c93464e23cd2341c24e3a103929cb2924a50bad077f9cee91072c9bea48ff041864ba298ce148eb0713eeb02e9fc8383a46818839adfe590e6523ce82f51d679a3a6fc040cb2574b051a0b28326c7f0e56582ec2dd23acea8a90b6f8f39a841394f2202e505d0abd42ea4d1a5f22a3a9eac1408f56e83cc922cb950b1c41ac35468e3013c4279e67392651a069490240c831c493206e73f8659e67394e39cd61d8e31d0ff40e52592051a0b28d8cba54a0e735a8c6f0cec737c8b08a9acba498ea3e902174591ea33a3a739aceb1f4789d5e60baa51d4cb455867f1ce278f320de218996498e746447dd67399649bc4ea295ba0ff6e94ae78a90b165213fd151166e9d6e77a9c4418ea7383139c2fbfc6720dea6ea35321d49f28cf1374e937c1353208a65528b208a35bccde17c35498a5608331243d409fc3c8ce35835a529c9ea3c8fc3114c992c8e64981fc6a59328c28d1023a8753389a235829b0de269262d9ce2b815c8d2c8d6831fc398fe8ab9c6f1e65b1ae935290b015d3d2c92c39969fe49a346f454257a80fd1a3793c8b32811ceb30cb68b26c7f18e933a9c5f29d) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_244 : Impossible 0x40802001000100000000000000 0x11007fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=29) (code:=0x192731a95c7b234e732c81a2ea51bed530c1ea7323c8328d926a91a40cf537532619cecf13209e833d44b32c5b14c276f9e211b15ce6819eea5265cea71be082934fa6b8c2528725b095b7592529cc35a8cae37cc11156f8e6519aa609f4d72f814b170f87a3287e229cd0e93038ce750a327b9ba5d40e2202ea062c8314eb9c1abac4d115158cc150138c06fc1c6a5950a07111c9e24140f9fe8194940dea9e964839eb354951d374c14846ea344148d29d1d2c982353c437e32452022028288aa1a49ba60994d224cf242cf502e84288c6d424e9ea4d4d21858622a53cd6062ca35d23c419f1d90ba4df4d408e8388a9cb9ceb82a3a6e9c61fe1e91a694c5d2c13a8819bf01484f5073174f74ebc480bf47b0e339e423a8bac102ea841b50e933d4d780a22794c42f88d4d59e174c23f885c84e74e883b9ce33de06e96a89a9d473a62679eef50eadd0754d48a3adea82c0c7ba06d511b6b9ee246679271b7fa16114d71d5ce1d50b38cf76186bbd4e76a86ab9cc31fef738ceb81ba5320fd3fd0b6798671ba50508a3abc47eb7c0bbdc1d22fa9c7f1d5be759ea4547f1f46518475718e329d9e7bc0c1a503264413ab74719be7b94e304dd37d1d14efd3accf3dc67819aa789b592709053ec1a43353a1605b818d31f4450b83826a7602df3c4105924c93a14e4c9d49a192259d4cf2746729cd21951a2349d1fba41a5928093a98a267d99e78b54194d2e106944e3e8889ad719e40d3a809ee0d74e9a44d32907061c1d9e46dee859ae991bcc93aa22dd047d1e26bac83c0d1567a026f8919d4793254e04a694ea26f50ea349fe3a4f50c46526423e8cc4cb6750f51c9a53a61a626e92b12cfb147114c4c32659e1d29aa75117bb9c3f4be16c5f1f63aa1dbe3f8de6e88e1bf0b45416dbe6f404876b81c9327a9ae3e9fa455d2329be6e97d1f1be7f23e870eb317381f9bcdf1f5053550135c7f7ba4df28b0e63d8c91eca6348ba294de215061ec393e8428ba3c54a3a47939c7b20ea52331322cd420a789d24d4c964269ba83a2665be446511739be284433dc928d689bcdc21d71939cc96e8c9355ea374d537cf332df30b3f913184851b4a506d3e4e629906529d67ab7cff14a4288a348fa509136a888cf5156f996294697cb8440d323e525648453852f2e8832851a134d241c8a91a2e9ef3f14d0f20daa42ba54e3a45315c22a9b7499513086992348aa2e309be2287bb84f135e32a50659bc994565a3a5ee6f87fa6465459cedd08ca94d578a2a6f8d7324f57c83e95dc2414a36e9326d49849b5c8392632c42e366fa06658d69341c4f0c41bccb4ca0ef77c86fa4e42dd29c46ceb298cb0f9919e64d40c45a349b7b83dd32f93fd2624dcee93a8d544c79194690f27f1346b08a53a14709b493126799ba6f8398b28528c9332cf337dc23c5aa21683b74eb3843394e3fa0a39926df7c86fa9c174de358ae6f8e6931267f3ca96021168ab9cd51e4236f74ca068588fc151511af5233034c4751aea56f8f51f4993ddce3d5d66a86f45cdf1f5e6f9116798f23aa92a0824c7f528eadf1bef320df20f9499ea508d2df6ac041a48d2f9d6379167fa4a3a8628c9363d4e70c4750ca45a4c22dce69135f2045c6df7230ff033dce73cc831bc936aba53ac7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_245 : Impossible 0x40802001010000000000000000 0x11007fd004000100000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=24) (code:=0x45cc9214333cd031ecf91d40d2a5789927c8c93ab740d2869bec13ed05719f2819e661994739e63d8fb67ba4719bb011261c93a78a024284289437526754046e94a9d74849274c11d21c93e309f661a8c4ea02df1ba1b84e3dbdc7c9eac7268dd30c6e9d260b8cf924cc73dd01329033cc749034c9ca379bef505d649d24cb744eb0c74932cf1ea7b0dd40dd20666ebdccf0b592851ca0e972cadbe37932c102487af512be4799ba749f3010f31053a729ce7b81e96c850f7618d27c93a608f606e618a2f339d324d74a94338f739481b3c51648df1a4e741d823cd9619e02653f9ac2f9924e81265f1ac534c9d525394196739d4be359ca2d99e9d1bdd20f3429ca67b24f13dc33cf74cbe41ca6bbcd264e99e4f8997b98e265ce445be35c9d4a4304e6cf7cbd49a264cf304f337cf91821ccbe619f23599ee92c82f90a9333c7c874c2cf93f9ba6499ec132874914eb35cc33743ecbef91be029b0c941cf76f8ca6b986378f71ccf9678e91cdce4ca0c2652b7b99e7894a3dc657ca2a3dc35b1c6fbe435a95d21344f28c67165c633df639c6b30c8b29409ac132a0a4c8b20fe872654a3ce2a0fb43cfe519ac6142826a8c8b73b8e1a0d630b7474a1a6522d26728269fce53dcc7184f937e02e11033947cb74428ce05942c0ca36187e28ba45335822cba5f33ca5124dd0d6016b7501338d6df1f8ba7a964694e84a4ce279ba6b60a347398e2987a9ac5319461518a3268be2d87508a308ea671346097d160a331dea6b16ccb3d85b1f2398a63e4c12744533cb616c7e659bce727cc74d92722d260c972c94324999285b749acdd22cc732c610e745a4dc2114491ac673e51a7d) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_246 : Impossible 0x40802001000000000000000000 0x11007fd004010100000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=32) (code:=0x1967b0736f9ce4ca9c6a826a4c6b0ae353ac6f4ca6c390cae11be2071f0df4d88e353ac819ce49c153260c647514e09e81982a71bcd73accf39d3646bd470926468d265a063d4df1ac7524c8d60c0411e41bdccf1eca324dfa24c351ec42cd64793109af711d2709a7b8c2df19ce733d361ad1a750a78d9bef54ca02dd1f27a9ba3e94a508d2404c10b66585f32c83748da3d94e428fa8689d50b5414ee7609e28190a0ba9d305014a4c3349d206593c050d174f13cd1340c1b9a4a745d0530c851f5314a465a06e96a86f414889be6a9d234a747b32df27f2942228ca1453b2d171a467a8c3554edf80813c837b9ac3ad033fcce3c996a721e61b3dd207f9bee93ccd541986671e4106c33cccecb1f28b9bef51f6619e67f39c3f9a4a34e87f0f788c6515508fa8d2c888a26379f6658733edbe51c043f8ca3c8f63794a678808f273b2cd5538a72692f4450737d0a0cf34c948536a84226f74acf93ee3292926509f5c227b19475294550d64b9410a536e9460c942932dd35c7c9f4e7285262c8799ad013d8285aa9d0a72e9aa65a0c7497c2e9cc6b1ea6aa02919965089a789ee859d6739e4398d53c86535a4c64a146d07c9349d64926358da750fa7b853a14a614dce3e4854186149a6414dee7b4d84539d010d2f90bed50e92e8eb075a0dd24542c37cbe279d65d1d27b269261d6359ea4d42b24399d635a9419ceb74a16429ca45d077b9ea134e91edf23a5ce65b743edca7b8a5839ea809074e907748f20ca331d6431bc6a93614b31135293dcf5648d578a2673a32194d574914ce1bc6117c6941d9615ca51cca71926f10e6b42a8440d1f3ddf2759e27385f126539d4691193744d7ba1441975d2990be4c88c94ee537c839beeb2165097d92738d519467192eb17ce717493749132646732df27d086248222df29d42659f237b54691d23a4696aa32759ce5d4e90a1f3051846f1a44ea1ad51d63e9ba854c8f6593f8a714e85a74f71ec29cea4e8b2991be4d90649862898766e94ef5354658308ba6b32ca7356067f8617984f5182e9966b19d0609edd4983f8d24ea2a591d4411e4419ed32e907f659ce3a9f4798670eceb32c433f8e51ad0a3954e5192637ce629c114493f85f3e8fb39c543f94eeb0ff07748daa1468799bc8c9427d1ba83192076398d6a137886c04736f90b1cc6f2c906174f73a532125838a2219d24508a8a5054645921c2cf93e9fc3fcd51d8f236843d1b50bcccb48d1f465056f90a308f7748c96e8f737d067c83dc9e7ca0d3242cc9144391924c9ba573ea4c979f285a4682852c4d0b24c690fa35be4e57f8a114c164a139851378ca851f4831a41a65a3386f85a2a3ea65d620e6a8fa2c9bc7f20e7320c839adee246ff106919fe348e6eb10af71e4f9355d2a770b1c355423793209a73a64a1324339746f3d8e60e505324dd0f93d44a990677ab54fa1aa4c9d2290ecf9374c1469033fccb214c130c8d11a1f24dbdc649fec73e863bfc8d42ba46491ae5059246369f27d14cce379fad50a60faa13e4c1374437bb84749c246834b84fd234993a44d26d0a1c243067235d270986993ebac264b6e705b3fcd27c8ca619926a9c2468a6870f5355ce6e90a354c94d84d374d51f4e91860730d759ca6086f7488a349ba85709cd4e3dceb1330328438542469cac30e91ac114f13e53274bf4d518685992e10e530c8681a34ce40cf93851139c5d519367d0b630c4c9ce749ca6e8a742e56619c24333946850175d69b38503608879d6819ee339c2853e8c26191a73113324854c8ba05f3a4f9239c2a306739b24fa185427b678dd10308d4e8b9e62991c8d0f76e8fa053338f630bdc219ac6f17ccf32c1adee7596c3dd1b889ae679353607eb747d679967998f032386ea8c691f46746a64ea06ecfd47339f4a129c29d0a518f6eb21c359d4175d60c228b5472368819e21c99ceb444dd1e4f74cbf4508a11eccf3e87b42915434ca0909354e21542671a45f0ce870868f1e47b7581adce7d23d460f6dd454857bb84738e91f4ce10a3e99d4227a35c616c30cb66b1bcc714c3e5461d4ce75899379f475a1c6198e0ca671f24c8d22887a638ce6b3a819ccb53964f2184791a45d304e68d4ea7c195c21922e90e3e91c695087a9f441de2739ee90841d46a1444c33ace77287d7c9012eb859e0be1aa84649aa7d3e4219c6648e30c1375923a4c16a9ca2c974513e4fa298653991c0396f9cce9509826e9ca0a2a13e4c920c791a4ca1f6869be749aa308723260a5d3eb854e05f0d46ab84cf1b4baa1324f928c2fba4dd11c2f98e238a6369f2519942e88e328c26f872324c1072859aa7cb840e4e65d2f9f5260e3349bc870164de28a85c64199c931f41a5193d5ca6e9c285a1a42dbe39d26719d2194dd1a5925d0dd16cc9174d28f0d2c31ecfe1ea78b55191822fb242e8cae903f499f4a7034b8ca73e48333886b05013a4ba0939bcce2e90674965aa3e9fd3a174e70ba035404b25d1f86230a0c17ccf338a60e51d8be613d90e328d2368e617d191a4431753a0392c8d2748966717c433fa84195f2348fe33dca0ca3f8be691747b1b5423c8793fc7288a509fc4b14c673eb04045609f4611a4be1f4a332861299ba368f27c94e9346832526e937c85b9cd51826f9947c9927f1a43dd92738c9238da218de308ba298528f0a68d0e4339820a592175260c998b04228966723cfe19cc91c867469f411e651f4e919cfe23934ea0829d26ebc49a239fc30c3911c9a0fee9374312e8c20f73d46e4b0ecd2751bc33cf17a9b4258ce591bae100d3052f89e25905638825d1bcfe0f91f8d2591051a8324d328b) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_250 : Impossible 0x40100802001000000000000000000 0x10407fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=27) (code:=0x1f5036abbc9b32c818ea1bd231d47251a6aa13746d10326cba6e8dac90a373996509fe6a82d89a5d284fea51fe6a94a2e992e105d28d4a232c132cfe949361f40898ed2477ba48aa135c2ea95091b5aa408d51fd921052e9aaa51f5c27fa4c92a0a32cc94746d1d27d1ec51c14c1355de918268fa8cbc51d0398ae3a8494623aa30ba9350d278aa76ef0733eb843e8471927f1bce621a56a590614b154ad46919e2cb83865bc61e3553f127609420ba7d518f7070fb093262607d99a4e3aa470745d0f146324fa928ea94983137a87326cc149cef758c13d4a119c8f3adfe23d1320ccb324738fa059529cc8b1bdaa474a55199623aa53548ec55098384720d92ef0de2e91e9289a658a4ca5927f819033fcef2321ceef519fe65a95ba0fe7904793a461ce1e459461d5d6464898e9fec918296c148c8d698a0e3e88bd051d28d93031ea65b84498723aa06d57eb3c224572e9026199e8a9ce26235c64989ce8ea2440cd6793d43ca0ae903a48b0382a4c206674a46d7999e06b4c66694a2b03186338fe94bcd96779266fb242a87f9822174996368723f5123fcf332d926fa84ea1ea509fc818f30f322bbc5b24c474347f099c0e3ae78c9fec11e63cca13f9062c9cedf2243a8df498f37a867326061cdfe3bd86e91e6cb528509eb0d4b5053bcff39ceb708f30baef42479b84f119464b2c8e9de52a1286b9ca11926f99efd6aa9c19cea3f9d6368949e659464cb0e784b541347f33ba54a3c88ec1c3064e0d71b22c7b28e0e28ca184bbc87a2650bd419d097abac116c1499eaff1133a87274a1e7fa3675bf4252452c9aa0671b4866b6094e3e87f28d430367a349b8ea25f293d4fe739025080daa787bccf5454c7102e733c212cf40ce643a1e63a2aef019eef3ecba3eb24e7164818e9e66e845449fc474e6a565877b2c45596fb15c29dde8a9368bc0ca148c86829d031d2941f99c5781875195097a942f30788cf2940a0e1754ae76f849936fb29449bbceb40c204a58e9921033fa948cbacf594bcc43dea33996cf0cf3d50f4cc672863aff27dd239c891ce12924b9cd63c91d3ea05463cce745c49a26fb32c398de93a466f8ce9b894c55cf030cec733c22a65c9de28b8f20e542738524398aa431b31cdf3260e02ea7f1d2948744e52f13a60632d1587bbc32c6b104ba3e912112cb1d47d649093a464a2e73c546b3c94110922d0f44d034f4ba37926f12c8219bc6b1648aa26673cd427f6a8799122e942c935507192ff142eb3d4085d207377b2c8c8fb0327c573acff64832e126b9e5aacf7e88cc74f52848eba419e06cb37c65b9c84b548d9ea63a0629dd609e59494a8ba4eb02b3f8e63689e106e916420dd24d0e4ce518f52bc0c164ba928ca3a8fe81a4c1746731d4a8994e3fb2de61aceb61816527096a881a8dcf291031fcd54193649916399ae1293389e39974d53f5461fd421fea13ac7320ccb74b3d1a9d1133a84da1b136a86b06b33c8322c671d47f21e5269126359e4df4d51a32cc1414608b28ccb47b37cd50b29389e609261aa369ace639dbe0cedf538c240841b7d0e3da343485d304d68c9f6148f67f20a3f9bea69aa89011606892ea3d4a09e539364190ecb08146a9a92857948ea3c91224b9c9194a41cfb1ac75294493f9033ec94a24754553639dae49494a46659263f964751742f8d67946b54ff4e8425aa9d5252d3d5037e88d93465a0a0d633d2c87468fe5d1ec06724e525946b542ca3c0b2e782a25c301) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_251 : Impossible 0x200100802001000000000000000000 0x410407fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=23) (code:=0x40c732062d9be39a1c9923409e5d19ca13a4ca7f2165383fc05ce7c9c21fd828328c309ec80a3c142871fc7b8587f47a32329d4788859e6231ec34a0c6f1cdbe968739ece151a243f9d2448fa328c2399823e53642c84c749b0cb291bc5b08d60a3a4cbfcc32240e909d1a9399d06378e92d946448e6216e937c993fa96062347d26d032949294a7c846c0d0147e12df05d155064f8e6a305d1fca5155063ea65ce17c5d04dbcde21c8298fea74c8ba5b0c4ea3c41d4731b51a1d5f32550a747c8739867f20d0b22c6f195034c841a16e7518f9749420736f8fe47b6c1fd8e2667d9cc8342dbe4660e20d1e0e285a2546e73bc389f223e4d42c596f90b4785733c891c5461fc418e2f930c1fb24a77491d404e977c0c3842247f39a070d3bc6d6fa854b1511e2798e5190e3d8a70a4f11751b09a754253d4b4e2194143279c48f1b2043d23c3cd8e6d974a13f8cf182a1264a314c5920dde1ce749e7291e41ccef28c6f17cf31fc6716e521367f42ccf27dd260a0433883475416088acb5d220cef518a11c4388a6df2028eb04eaf90e2418b243902204fe0e25977a94338fa20506518ca45878a0c455f273a2c9aa7ce239c711032b9ce6d9f259206813f83116c5322ca377a653a29ca13a419c7f1d2830a68b53b7c7328c0ae717c8e61c4252928fc4d3391f38c0c9f79833a5a7cca436e66734250b7481fa0f0327ca715c791b5324a51f1fc576fa7408c536fa023a4994e8f6859d423b0f74a061f2d739c471ec81424572942b93a7309d2c88f0351b3d1a0713fc2d92f51320aec11d59e3f833d8325818083012e872cf1d5ea1fc83538c20ea70a9d424744f9931333c7c932c313ef30e2730f213493a6c6d194a322c87216831d47d648671c47d1d47f07692c9c47e3b0723aa74c83fe82991d51a08ec906764c7d3d08764c54577cc0c1bc11d1d494de0e4e68b1f47f648e93e51a0cef9324eaa11d223a8b15ca0a7d1f4d410d3e418fe37b6d3213e8f9ae9926ee98594137de61ce12f54ebf41d4d246a722c846deaf31cec73044d85b204de2c8f5419cea738413c8a9028eb9cdb30cea7f1f5328483f8f699164404599ca1624b0b47e1242cf1265392725979b7ca35287110b3c501425be101388e6e751a94fd4551212581b7c454c728ca522d1d1f60634a24f564838bcc8d304fd495150ea458ce528de798fa3288aa2c831063fc045f1bc570b6f38190b2345727cf1455ea0fe408af4173a6438a24859bf091461aa3e3e8b679b253add) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_252 : Impossible 0x40000100802001000000000000000000 0x2410407fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=8) (fuel:=26) (code:=0xbe993e847dae2b9b5123391567a02d502e9262174867c3c7540c8da3a8aa3e81ba4d72068b24e9306b24daea364838a626ebcd0719279a3a4488943a0ecb035c04c947c39448ce0e5ba83c0c8e9928b0fa3ca4c1bc5544a85aa1aaf3226d73fc389ab0336c42d1f6aa846b81f4db1347daa419422785f14c8a9323e4d7c8f302d91ce23e85f2290d418d641cba1149b0305b4348a354e24189e358ba1b49a930be45b5d32175172067544d1b4e51d103678369aa4f8ba268ff2f6d9337f898c0c831345d858833be3a990554cba5ea9d0da05f6bbed167ca5e86a6e49dde989e69194e848751ec7982dcfd2651b263e08b2fa24ef29c6b1847f2167d1d5421c49942d1f8190b1b4838e6538ea338fea11ed1a38596126819f63db54db3ce02192919f2325470b0eaf336c15c878e85f4248d26c830be711ac7f21c4f45c8fa2a84a6286a4a91be6160d698c7d01464ef48de60c93ac54f96da4c2562fb25f67788980a4a98a322028a9aa5f4c86546811b2529cd643c7df221ceb0308ea165f10b418f2358e636a125d22a871d59246b2d3a13d27617096e8db4c5274d4dd41c1bca724c8b45cdd4c9d29a8f71f42445d0736d3301133150a7405328ab85eadf1aa818659fc8b2750145449d468d83abe62a8792380897c051581b55de2628ba650147d13225194148194eff36c6a9eaef32dba0359d4e651a1e84b3d0b40c8e8931cca13aa12858ba81a75153d5d2c1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_253 : Impossible 0x1000100802001000000000000000000 0x402410407fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=25) (code:=0x10cde649f45d0be41b7c799be44cdf1ccfa81a128906f37c7310b2fa2c593e877a4e7da0a89a068d9168941cba934b431d1524d12658ea4c9b442cdf47cf32649b36ce732cda9e942a70be4744737cdb0133c44d122248b264fa80824926229f45922c08b298ea85dea30fe4da167498642dce6da3a28d03448671fc99155132564ca26879f66bc5449c2ca37c8899bca337c44d46e72030332c80a2653a0637d1265a1c2e99681a0c83996931131cd3e2e89293e93a268fc2417626419323aa2cf3738de19e6d8de85c9c831ce062524b20c7365935475be24e731b50b113175ce6da167da2c2fb5c17d16df499c437929284cb83a8e4394e1662e679ce24d013ec871bc3e94273a171330d0f45813d7ca4cfa4733d0b224cb22680b9d46455be02e8be591bc731e489678af1d21d0144c89a4a219cf0781bbc448e679a2e21a168391f3cc2b90e891df070facf20e5f818879c44f114388b2359741c59e839d422a241151287658711258488e41cb280a2a8f8d65d0d633a1c17c892ec9c175b62fc4c749d4997382fc9d1317441c432381597425074b27c9c5262266f4d5427f05717542659267389315c45c9e5d0ec898b6673f82e9ccd739d014246d0ba6ba4dbe16c47202e70c333be493819033e4ea9b6a91742c51bbc77c3c3882ea4e1a8e7293ed161da266581cc5799cd53e818da01ce7649974571beaaa3ca5de46d2785c1c83a1e252831bd278590f7d8ef13985a3e6f20c794745745e06cf0fe49c7909a8367926358499962a97c2166716cfa2a81be06d5474fe2e865a168387b3c37c54218d4b219e37a8d3e17441d0b24daa7f9b617d1324dce24dae714582b9de931bc5511c5d086859aa33a2cda990737382649f6a90d353fe0e819be35435a64da0d6996d89316ca71f4791cc87ba49b42d9e751d223674ca54137c3bc6a25c1dce8188e9cedf22c735046732ca341c13d470b36877a8ce943c7f26d0367a05ea9d1010499bd0e24c893f893358f61c4e6426025d184359b4676a8e71c41127dc746d1c4936a89a2261b0b465e6174931b5324046d5390146c730fe4486713c7f3cc9a711b436a4e84a3a8fc2c3f90d939021fdea36a0c3ec3e932367abbdbe0db094b48f0ba268418b6e71ae85a4f0517c6b388e628689a16e740dde8905f31ce227a4c175130d08e26a05460ce871cc033799ac67409fc7789aa324c5d077b56066f9ea49810ce933914413f86b51a0c0ac6a15c9a6f835799860e77487287a1610a065d1546b418353a8da499c416c6b2e85d37ce90f32d8e6d538a253aa5049a2dfe1d5de11b499967ac75276f8d551883bd4d53bc8b67837e1636e2f093bcf307140cae438de891d47a9de0d596b3d1b1351330c40ceacb24e160593fcbdb66f86ac95357991f11c9320d037fa643ce2647cc336cf3819037f9029a86ab3d0b3cd263bd46269bef94e81c4cf3fa167996c671349310179a16499dedf0de33a8ea305324d093e4751aca313616818997fb1c103359fd323d826b3d46348f36f90642ca3478df47ccf2aa054add) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_254 : Impossible 0x8100802001000000000000000000 0x412410407fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=25) (code:=0x2031d484a72124d8e62a8fe38be436b8449d0980bec4045b22e3a2247531cd7174fb4d8fb26c653f86d455c29306f13c5f3263aef05f4053136a0e6d82f9122a88e258ae538858fe4cc14793ac7582e70404eac139e3a0fb609b536474753f8499b4c97790b7cc0c17c8a6b8caa11e639cd723c870ac370bea345447c0c8e9bd121d46d538a739d2732cf9418c949d0107b5190639881a0c875384b134eb1d10e6d3884250e24c745b10e7d9b4d749849c15151ec831ccf311547c73285093d8de0ba339cc83538399751b20d270d04f425066d7081961b1f0e7539f6c11cf092867da3699a560cb218fbcc3e67a0ca808e25b2e8ce2684d259f7030960bb093a5033cdce830ba32857174e21ea4c33a84fe039cf54e268db054543a4598a882974419b612932820b27da4d0b8e8f6cb285dea507ca9cc13aa3a4c90111b98982939f68ba6c5514eef15ce136a1209a3047529e4f1d424848be539b41b51d53a02ef14ee108353c34828c14746720ce940d4e808f342465114ba4747a7d9427f52bd41c2a144884a16fb4989386a06305031f260a1247d92455c2933887ca1693418454794ca4c89324c140dde305ea7d0931fc7585a3e86a4207f2791636a9dea3d851906f506dc05297abe47a9ed0b48d328487a90140c233a49e164f533a0c21220a0cda2c89e1b44f17ce6931ec1d22e91506508f67f5288322d1f294a14743e4da398e24047f17c435062e8d21a8fe389163ec25aa931d5828d10b425d249d0b24cc97da6aa087dc0ca31650b24c833a4d77c838bed1b40cdb424d7166020f93887a9340dde05f114c1469025287e4d82ea35ce65ca48abed1f01648173c2499529f636a166b8ea938998a9363c87f44c0446ba4468359ae9b1f63e2c906329464c94a0399ac6a8d1d4a514a9924c7da8dce11b4d94c673ed233cca342d42f98689b11f46a1679a03093bc306021cc2f876d70dc17e4f0113c8726df60d66ba6c7d11a3ea0c939ae35857399c5f2202a54751577a4c60932448f217c6b28c7393849b04a51290e6aa7985f49df642cfb8fa342f9e4891f71584b9c7da4639a1e519b68b9e68da068394e77a85aa09328cb29cca441d034e51a9925252983011e43ecaaa470394a2f0913994a6a6a9f68ba1ea8a3e0b31d6086d204d584a02059468e3294051f52bcc468b26aa523bd0d4c846b561246e0240c6d20487234590e2468ff091cd4adb11b84a6636a3e23535164655050d45d4a8e87da131f40582e70a13ec378da2c8fe50953468be41c6d379c846e0f3948d37818a1c0e2e8687f1642786b35cb232a346d1f4a184852942c119d032649c94681926918e67105328c7324ce240d4e8d04f2047515459124d660a6c8182367293389f64094e91c263e474ef43d3549c9ca6a93c7cd780be4948e250509164ef529360defb36c390fc328aa408d62c9061bd327f0753e83ace646524f251a1eef2723a8ce9b06a368a6a17c94911d3b4ccfb23a3aa767d8e69b28dcf157aa7422ac18ea2e40a1212693b0429677092061610146b051522b09154891fc9b05997a744360209e8f1652b4050d85a96060e64994e438fa35c24991032748da4ccb849fd314d452c9d1924f0108929cc992a9a9fa2e4ea5623e9294ea52740d592939ea4f0b7c8106a724d9309354c104f17c8b49c5527778e708d8481cce2937ca4ea99054c8992347ca74a781a471f206a8a6a7ca723e63e82a4e45d271cd1f15c938dc044ca37157a885b2539274933bc4069212673a645911f99d152110125a258209399a9e727cc7447d1d4ca92a89f28b91f4853945d1b8082871f9c933034d53a77bd5e6dd) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_255 : Impossible 0x100802001000000000000000000 0x412490407fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=30) (code:=0x6d1120931c88f2736a2c55127224ca7f6a88da941f68baa8fed54e82e9f27f424592041ad330b09a3d8ba228650ba279c48f284409ac47a0cfea50711760a276022a8cad58a83f9942662af53fc813e849d163f8fa41b551ae71ea8291d0f97a84f10584a3a269ea509fc59529371b8aba489a1213a8ab9c89996aaa7a96a027ac6c6d2854a09d508fb274c45b6a91aef00fef593a36d541449cea44e0a083939fd3249dab15738d5414f542ddedd0f58594e8c9429ea3a2960a86a0277bcc4261a09385c247b265131cd01515276e8714e8dd4549d1edea1d582828969f32713c6148d1d384143396a827be4cb7a8f660c2c1167ca4c10f2d3e50746d26a500fa3585a4c733e5aaa17093a216238ff2c8ae2e9c2328fa996e91b375eb15089659830908b498867c9ba5298284c148a8d612693a3b55455236a8e682c05de285093d5ae098a72d585a4c831cd291274ea5232e2a40a6a06d2345d1347d2747193a4c0cb52c9d3a6e8a7094a41fd39529c23ac547b85bd43049d47dea42c9d3061290a52204892944e982224c11cc9e9320d338a8dd3dbfc70a1232d3114b151cdea419123dc340fe84a2a85b05270508b3882ca3e7f499de2f8a63590639a52468399268da948d658f6f9127449824e9ea3aa3a7f9f20529cd12cb14c6ac346789817e2ea5204e1065a9489375270b20c3553a52a2b131ab0d84c048d88d9f22ba4c5320dba1fc93529151b4a56a849b2c9b19c7b20e0299738919f31544d050d53f8305aa52a746d414e24ca1644936294750d552a247d3d48d398c1354a6e735df60175f67ca84e7414c935e2a84b54a73fc1022fa6c8d7a865c8df6649ae0837ca0ef57fa321bd0777a75d20938988d3ecff4c47b7aa33293850d13946a323487b0a39acfe53ce5ea3d5ae1fd4249c2c4a4e135dea86c044694a09e659ac4724a3f9263e90653a34c9385aa102468e22e929839de9d32435a95017a82ebd543091294ea161251b1259c9124eb9c42e42a1216cb6a865c36026102ea96126ba6680c14385aa0e74b47f86a9602508fa469cde6c71de4590622a86a85123be02115435c2891d4d752899294834687342cc93e8f5404799aa7aa3e8aa3248ddee91ead72953a1368a9ea3e8ea294fe47616455f63fd1a36e0ae90a16aa2a6589ca470b7abbc3d5aa1fd1f29c3294af53bc4b5ded52349e82bcd830f25a8584760e4c91252a75391945d28315808fa24e0a14a9c936408d633a122a91af92744ca167abfd15414c90da3a93a7aa0a84a0eef6e852c050b798a526c4da4d3320d294044243762684c55011ad272252624e84c2c359df0119c84a354ad51aa2130b52932a29de8ca624260a7cbcdce13a11f7f8de40a75f21c62af53250510749a128ab546aa249974880a3ad50165f29d17455506324a4388d652c953741d131f41ac795349d3890946a2701455aa44d1d2870b4544194e0b31d3e5091d4e233d1aa582b9c33e0a1ac9b44daaef08d8093b0d10222a71155254343fd3a8d528fa4d9f2e910b4e9071d4859329d1f5aa8ebd4348e2859aa414225094563b0b1cc1d46d424d647c0484a9dce24c9b1f48321c712244b1ccff23a8d23e53c65e6414d542d09234f377b7583031ba508e239d1a08a94cda993e8f53540d6d51c51a3eb9cf93a5821091c4da228ca7317d4a0817a98e8ca12f30bed5454cb324207553a50b4181ea05411e5293e44e4b2991093e4d6459068d0ba737a849be4a58684698e831e47d6ab9c10299132d50faa3c244250233a9444c7d9ca02f9739e6dd0f91145d23529739ba1bc44c7e830de7d6a810b6e9f4e9378f28091d4189ed504e4ded5205ea226d5294453cd0b1844f49906f91150fcd689b9d8eef05089f09405e6d74e8ef085b9cef3d9263bd0939a94e91c27d1b41acef6a94a9d042e0281a4ee70d6ef52992dd00da4f738e7778f649c2daac14487ac0c40d0b17483156128ea2a779154241c48d81a168fa27010e280a3d4a1c4d54e8fa7c877a94f9414811f4528e2779f23ec55eae704d274ef5291ae943d9ea3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_261 : Impossible 0x40400802001000000000000000000 0x11407fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=25) (code:=0x226719fc6b384a71268a865214691b4733de264147b9b4e339c758e8368cb2d20ee77e83de266f94e37a143dd3703037e52a782a4c49a06fd86816cfea71bcdf474459e429c8b38ccafd88837a15157091d4c4ef3846939e4a891de7ba2e9190d524657d8f74de0629c891b47924d050593ec450b50a459267f093a2e2291a2efd899cf01126f903499e9b80a34359154a49386a7a106398d6511bc7b32c931a5de24cf2053c24ce518a71a4676f98681a0c1ae1ba8c67429866b49c4997c61027986f7359ec33a1c499e51a1ce65c048516c7f0833bc5f0dc871bd0316c2d9fcc3809e52d3c51d448df7ea9494a22658a717d0732dde32d3611d1ee690fdde7d9e28aa2c9f31c5393e63a6d124986f42849ca4869168186590b1d0df4c4bb0d7ba2494a9cda0f74fd1291c4d2937d031b4a530d097eb24426020d2fb4c50532411635989f66f1467310e929e427a0c40cda638de349adde03789e73bc4da6399298974cb1cd3609e378d4cb08b11cd231cf235974fe0c37b94e43bc40566f988e65390608e739cc6d1bc695292635830cfb3c8d698a2218a0a5d0b4511126f0de670869e88e339a437a4cfe41c89252f1126229e437cbe0c4f10a60612cf4378746d0b536037e06831f88e9186265926348673f874791751b012ca74498f240d1d38467926793f516188da1371d194e107e4592670c35312263cc451242888a62892c8932349b385f23bca70da60912928734d8be3fa4c7b9decb27c45a763fc0c40d827c9123d903368ce6593ee30473693e856485932c818a614c89778a26598e64864a4c7f19d16324e732d3f253f53a7d1133f9de53a0e8e8f61fc791654a295c24287b944c1113609d43aa9cdf226538c2168eac906545d3e45be4398d2e114e1c9928514ea50fe08744c4c6b10ca218829e23133845a26e4fc44ea0e50a52c05fa06f7c91234a2c44d1278992164e6324c280bbc37a6c2025f3486a2c88998ef922ce3324ce6f8e67f1f26b08a03b26d9e80912779bc732c86f3f4a63486f358be7907cc54ef1fd8e754e817c2b3f94e431ee5313aa308abbcde930fd29dee1cc6b649de3c86b44a7ccf38c08a8aa4cca194e6324533085f14ca2384ce17ccf38cf68b3e89d0b20ce7f14d1636c5f305bf0138c808e6a52027533c538614953724a9d24ca78994a6b8a70a76fbed033cc44cfad707f1547d1d472328d7258a8931ac2c9fca50b2359ec750739ab6e02226a340c45a4d9e0a73f91727116a31167d40cdf0ff0109e6b71be51aa1091bbd164d822cc33ec9332d1283bbc45c549b0e6a738c3d8086b3153c41cc894da7ccf06e3fa2ce33ea863a6ba121746b1bc7520ef122e730593c9c703049b1e0e79820d131d7b91545e069b1233edee539468b91b8386950a0a9f83aa858e24c4932e1eef4e8818744135c22dc64e99e7b926454fa92a84a74a4c34690929c14e732e93a07ba22c346d0f40c9e6b22a7d99e6717c33a9c87469654ae9) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_262 : Impossible 0x400802081000000000000000000 0x411407fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=25) (code:=0x7b9ac44c7d53a066e936f50de85096798ba748e9468aa2182360e7cc94a71c5137b8388ea3c9760222a7c88a9bde6a746d01708434349b44a84991eea333c6e9ea279e6436062d8e6508de3ccf51c40a671458da428737bbbc7e8723f4f5285161c5ee35b9c70b754e0d703284f544c29ce62194645bbc89b859e3d4a13e45d1b51d234235f2710ef36b74ea2126e94e4d96c8b44527284fb0b622cda799ba0b70328cdd7eb9c28d0389bbc39cda888dee10e2709ba7794e8544b0479a22658f90f9789f44929d090553591637a25ba051932899ba989b5e27d7a8519ae898085944c890733e9ba448d61ac5b0e513519f6619960e62b9f46b404dd81bc429dea818ae16d127d8d6f7778425ba7796c7cbd416d16e71ce1f9cc1b46119c471545f3e8ba2c99e279121ee73175161ba6b22c1ef01226aac34c48f94c8fbcc37b5c732d8264da39a130736cfb073030f74bd32dd206cf1e5ea117130ba3c8b67326af3738818f2671d596f13886b22c45996531bc739ae7c9eaf36384cbdc5931c7398e7a9c438a9ccb46840dce798fccb146ef33c893ddd29d1ba73992e3) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_263 : Impossible 0x2400802001000000000000000000 0x411407fd084000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=26) (code:=0x3250940429a2c9922a6f1f2648ba3694aa70f16ea6274a12892060d681c05e634a22424f97a909739f63e4f5458f541d42039224da7c89e730b26599c6f21e738ce8b29de29d1263a8fa42a06449ba226dd11b4e462f5454cb39c35ba53a40c8917c651ac611cc85454e71ea9352844d26f5414f3113224f94ec0d0d5088f942899f4a517453bd489b745923681a6a899427a82c9c4a76e8717c8dd33a75e222f0310d849e2359e6819261bb1540c794e942c72160226301284cb879fc1b5ea4c8fa16ca12247319c78a0ecb01fd4af13e5ea73912714e8818d6399123e9fdba1f61a0cb4e9baf13e62a1165d284f91fc112c716c448fa7f19e26f1434dd53c9c22afb749ba7aa06849093e87a9bb2745c5329c08b037485949c7cc0dea10334ba5f63ece9375cec74e8389f50104f1fd3a80bc5423a5329b113538d6418e687a067da2a20c671c45d32d0374a1a086a724c7322d423e82cba4f94ca343d50639a2e3e62a49889a85f629d178085349d174061eef1167a8996e9178194a32e1e22843c3c8b39cd74494235d157cbf4e307dbf4899fadd8a9098f83f889ccd03458a646a3e508d73507340d0945bf60240444a028d8898bc551f07d2266b0f21e96942fd2027ec0c40d012f9fa87c242c8ce8fa6e8ba6de622a4cc34a13ed097c88abec455fb0f2151312f4744f22dfa84c0c848a119ce77e85f0dc677d8677cc9dc6142fd0993ecfe3e917153e50d07ec9e26e30e70177b043053677a221b6127c909529fa04f4da0c4250a212f33ecef498fb819cf150be528da504f38f9164488b8890a73a9e1a1c4f34e860c24a53e4790691e4c10f63a2064982b091e4694e9327c9c44758e83a2e13534874448b31d1e4f91b53a4c87f328ea9b03086a7da1aa54990aef06d848ce818fe0259b63ae740d314ea22fd0b2869f68da568fa36020738fc1cfb4341fe1a07f53c364e449e27e8f2a522d422745f07d5394a468aaa2aa236841a0a88ce53af93f41c54ea88539b50749c48de6f94ec25332128b87345d4a9e8ea2f942f11074d906265073882c974fd50890a12713bcfd23ca12631b5288d94238a75f21f2a146c05eadf) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_264 : Impossible 0x400802001200000000000000000 0x431407fd084000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=25) (code:=0xce37b3cc91de0cf0339d061d8962d8d22988e3ea743e9d4779f2930da50a242c8670f47d9f210380932379032eca5ea425c65f1f2618d26b9eadd206538be35d26298ba6d3885940d06375173edce3dc1cd4e691f6e735d120d72fa4cfa38c65185153e47b91253a167e9ae691d49d053539123887d3e4718487121a449ba5f21d216ba4c0fa85c35ee71a867e8dd779f643c0d9270811b011c5c639a0e4bc871bd26f902170738d25404871abe47d4e89491c8f44b0c17ce61f2fd455263d8518e62aa56919f2fd16512164fee113a2750129cfb3f44de030394bd542df0df494a740cd7449d27a8779a4f519c3a5ee399ba6b89323844dee739ae19a4c4b2c82ca12dd35c5a222593ecf71c9031bc4311c7339c6a1d2cf374ea405173d4f735cef2e81c9749929c673683dd26618e61aa072b7c9c439c67818e73bdd28b9f2989ae8319273817c431848e711b4551147314d267d05a03f3be530733d112e8a25186e0dce93ec2317ca31c4d21554e1f2716b82c8da38974a373a253a003ed7399265f389740d44f7b9ae238520e9bc8708e2e9146799c498ce7f06b9de592e9ee338fe1463705f176526b9c4670717b9fd9e2a85f299a41b8aa3fce417ccf3bcd22eba424e6f43ce23de2653926438a62f86f44c933edae1c4fef90858b2ef3f4d745c432ea244e8ef20ef944cd745c7b184be37cfe17d4e7d50bc40fe90c344a3a9d2969e21de89368389f26ea9c7f7a8fa3c4298ca3e9b43de123e94edd3a437a25260e285bdcf13a62a164126f9405ba77913374df7a915748dd24dce71059499f477a2651a243fa0d3a2345f37c7d1c2778d27302ca271537c617787cc4d231bce2438fa9d0778ca6f21c86468fa39a4c0cb152182593af9388ef2f8f9339be7f02746121974de518f22a8fe39a2422526f150b1c0db310cb1723419cff154ac194fe3a8fa448e68bbec425014e94e3e99e3abd413af58da4e88a567dbf4404fe29a4c67926829ba2249d808ea202a11f4dd4687d234710e47524e1605d3ea855520ccf1d5fb03738930893e92703235272167392681beca112681bd5be0ca23c340ea7111d09274a71f4a19387f86bd48d212e70be6e8fa3294288a5e7abf437a160e29d2249336889328713e8714451b037188dc047d235292850b38df202ec554ea139cdd4f5110a74bc877eb8c14d8f0b10e73c0c0ba9d1d6923699e13ae71a46d38ccf41832b254e1fe1a1d4fa40542f57791539cc737ce31ce34a9cf90fb3e4fa6ea4c7cb3c6fbd4388e424dbe2385d39c693ecdf778a77ea25c2c1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_265 : Impossible 0x400802001000000000000000000 0x431407fd084200000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=10) (fuel:=27) (code:=0x891bd1f30d1742c8d384272893dc756e94e52a0220ca549d0135c6b1ba9b384399c428cbe649f42fa2526df1ae1f4f7224de1af351cca349d267d8931c59252bc41866fa62a3448732253a4c8df529a40393ece64d95c9938a164684adfa7d0d48912661a26418ce710ce9b24e6b6e835b7e0221684b7d9237d4b030c27191a78b2c46d03499c68685938c7d24d230e618a12499c53a3abd41e60212693a1671c04b237c6fbd513424e13886fa4a9d3850d3eb04449263e996738597a93b1a4898087d32cf5878164d27320c1cc6f14c4f92a4cc310661926cb7b8948fa358868924c92a7e8ec043ebd50b37427a66064a50110d52a0aa49c28988bbf50f4150b14e8316c3aa4a73435131f5eaf71ea21a929ccfa35a021ad131f4cf1bdf613d3303608c10dd609e28087352cecfd4540aea7528714e8232f883274c92249e214b6435c26ea4c449864393a7e8fb38c8ea0e9d4dd3f2260260c0c24d298d8f27e9e27198207338c048348c7d02cc063671be4404e61a906f14e835b04eaf56f8379f27d2246944c7a9123e8dec1294072f13e53a41bdc1ac89608b2e751bbc498e152a12468fe424871fc693d43d5213e54e70841c4cfe2162a73a12c10fe793289494ee143d032350927ac1445213890f1c44988e24ce2779b41654e3c8da86a12899ce650d6778ce438f6328f2115153f81cc6136a2a6fa4c7b214a71fc693e4e2a58086fa1c1650f090c27c9de6f8e6819fc7b90a3f82fc043d90e3fbe4c239909299de6b0b23f8e6a70de1b46f42526469de216df3f820cca809a5091fc7353b05ba0e3494a479114f91b4ea0ae37994214a23c90924c611448570a22968de32a947512d86a0e4547939ccb215e67b83890c7f047384de3f9448ea727980820e270d37d1d106798f2e11bf0939d825d06fa94858087f1cc80984709bdee10b539bec13ddde3ab741cc93405ce40cf3435be3cd4e29d01778969cdf621ae13bcde6d06bcb4556ebe5124244b2143986f8187f73a246b07344a9c3c9ee114897391a165ba9321a46a06f91d449bd4fa1c26fc7c6f0dd1c8da328ea37a15030fa708831f5ba4d87d36a4c41b9c21271215ba2c8f632a95320d693126298df2d454a701f715ae9164a8907140c697c87117e0240cf9448935390add7883e65a8e9f66d12610b448fe41a06799a44487a9314e6d6f9ee0fe49c44611d444cba369268949ddf0d1f6850858fe53984499d53d225be898651c4f92268b94e6bc2d097b8215369310d1340c8ea1681a26f777b7409387ac19ea9dde114f729c399262294e6d38842e2e9cbdd1347c7f13942deea70db096ebd41cd1221286b7cef3c4731948949894bd50a07e1195ca710925a52931ba5517c8688e38984f112642a24da7d648215ee538fa499e67f35c3c5157da6c48df653bbc3e92703748a514ca70652b8d27f14a871e27784e7524c2154a7b926308ea51a26224e710aa544e160ea3595c934d83ccde4d8d639a24fe29dc203b4d9467524cc129c39982851fc7b0d1de5281c4b21e32d154393c8d630a95262f86f964e9538454bec94752d3c47941cc13a83bc86216799bee1056ef35d266f049c866f779c2114f22ca1c9b02cbc4851b8556f936309ad125d1463a87c9ce7f0fe933a4c23890e398399f238982936f8125de3cdd27a9be7b9fd4e8d0390f3539bc649d43f99cf735c5d03895cfe9b2183c5e66f258a614d46454d722435324e90dcc10f98a8de1c4aa3c9d23a9e2329fd267d5080e29350c2c49a34834041bd0f0ec3fa9f014994641a060f20ec0448ca36ba85f6495011fcfb79b7c2432537d151f5424545186d28526418a713146a57c8a12728a9fc790fc143238e9366f933030d6a30b2533cc389424da4c8380bbc21c7f7d93241b2c11f6bc2d1b84a4293a2296a7247e06044c7e26818faf9455171098a8d281c2c3ea5a81a6dee23713444df4150349d1577841c0596dd24e419364544f1b483304e20fe389070110652a649b6e8dd03126dbe228d21f946238c2174e236c05120dd498574c937093e8871fc6b4146124d2137c7d50b9c1a86f9fc9b3bcb21be3f8df09388ea0de6d3e807a499d46f34a12710d46d21c83174289de1bcfe6ea163486f4394a590e283a066fa7279808931fc1bc872cb0542234a526c498aa3f8df40d368994a5902c8a68bca47947dbe28dde89a84096f3379034991a711be89a9c538ae4982f9ba289bcb23a9f43791a38a0df2f51177da0e49a06889f27a8cb24c5348c49c1c5f3e491a0e449f2fb0fb22c0d36378c21067b89c4b3d4f935c8a94e5d21235a4d1a1965086f44c54f741c9377ba53ac7) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_270 : Impossible 0x10802401000000000000000000 0x15407fd004000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=7) (fuel:=20) (code:=0x19c1fa81984533cce98b8ce19c7f53b941fc8f1ac8384b04eb1ea990ae710671fd0653853996499e46919c751cc89868e1435278f9279891e0fea75083994ee93885729ca177b7c7d87d8d67f24c531a54e438f61bcef0eb339fc5d0a68738409b1d3fa154224c7f36d1d3d4d73bc4552f3bcc13d61ae13286f9fc37c9a8e9b6f93bc37ca34546f174a186a5a2290ae11f6889ee3087d9eca337cba77b94a74483d48ae1089228fe358a66d850982a7269332d38838946f91de518f64490a1fc6b1ec5328e4224c6b84c2c3f932378e6a739438a0e358f639946f76e9110d23a8d6dd39451a246ea4d3ac71ca85872b84531de9940cd6418732650b53889bf4ef1ace10df1adde70b8c72b3c42b1c1ca5337a9c729547ea4d42126833bc10ea720dbe60bf4c71be71b8431dc2779faf5284ca212ef414fd09ea70ae7b926a33c41cc874994ec714e49b7ce26d) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_271 : Impossible 0x10802001000000000000000000 0x15407fd404000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=27) (code:=0x49c7b9820aec119c7f26d4e4494647867464e93bc7f0fe8f224a3868f61edbe435864d079a9cfe0f51db1cae659363d4f6455865d22e53bf41865d1ec6928d127a8a62091e8b029298ce518f608b94dee779cc5519c7ea8d1524cdf1ed422528c9f645a4e6f89e349463515512196c315cba45c6137d1e6d0a71a6a67c9d629d130df3f9ee29903538ef399343fa1619d36728623d8e2899a442d1328dee6b932779f2749be936398649c673a4df224a330c7b1a47f226182333f6168190b31cd23adbe3f5861fb133d4db7c9c471946728a2298c28a9be23a3d161cccb01ab066263bd481b0cdf060a4e16619ca6b18624d036f903264e96389975a6c6f9ee395ea358a64594675a3d0237cf71d50329c9f1037bb1c29e366fa2ceb0de8c8ea478d2893e44191e0eadf11e8b9bee50d69f455ee4587fa06678f97bb948b1cadf5388722c4132837d1e53916519d46544853b04df264a322526fd049c65063583dd06c119cc3269160818a71935926459035385235194459befd8a8df30c24c9e2e9bea7454ea37c5d1be473acd728c175be8b1acc3449543d483424411954e26841c2d0935a1a1acf630835c0c8b31d327586b7e85d3acc3394f7475be1ad9e1094c9fa85b7d261ee8cb8d0b1c689a8635b049344bbc7b882c2ce3112f73bc733d582308609ac891944d2658ee1196819ea4c86f93e779ec871eac17191623a639f2df05b2ea2c6fb0d1222c7ca3a77a16989093cdaedf3d51526a7aa168ab1c30bdd262648b23d9e7136b7415dea6d92610377a4f390931cce27e8f661224238c249994556f871264c13d45f2247b638891033a88fb8d033dca71d5be5b31c2f8a660a4cf545842e067b87a8b8b6c14143d954498e33dc932162d926659f3096fa5a6120aeb1be1be5f498d6378df478e637c934d9d4cf4087bba4f54f833b843f0399869b35873378aa154ce81224a11fa418e66d0dd476069f0de5b1ba60a2c010c6eff77b04670e69b8193e1cc9b27d967aca4398473c5166f85122c9f0f661116df1d445508ef09a638da3da227487273155ea23a61a9c831346b0e645982ef15c9f818751b48f29c6765bdc2e9427b8e6374e919cc328516479967f0df2a8b6708da459fa08e369cd96779f230411270c75be399b4c71fc8b7ba4c338861097794ecb174671ec9f444390239ecc17aa366d39873418673a4609024f8cef523dd619c6d5082f9f2369cd2602d398aa28843193e4cb2327c996810e45d1ea89a7e0620c931cd034588f1846740cfecf0df45906498ae4f845982df14cf31bccb0de6d1ec8195c9f7782d1d4933a48f3fb8dca7d23e299328481fe2ee90d6fb49c8f0fe67a84691038ba25ca3a5be6b8f51ea84a1e44889a1e378ce7d0ec8b9fe6b0fa899f68b92b4b4a18e8d67f8919adea02939bee524730dee0d667934449be96c64391848332d1526a948de508faf570b9445dcb0338c3acae113239f4751acc37b9136787d9ba890f51c9ad0930d1d194df0169f5ca3da84448facf3987d1ad0638c23a8920c531ac737b90738caee54981cb7d0eef0df359c61acdf41912499430b126719827a88a7e946713687b19c7324a2847d899d244d364960677841cae229ee43cda748ca148ce7d39b947aa8c2b94671039c0dcadd0713751e0fa7795c611948f72b8c518fb3acf716c309ec219868a9c66f72a253e0d65d1b43687b24cc1182453cdc24f9f47545cfb3ac2ab6c3786e1ac7f14c9a4c8ea0e6df3bcf744813d1544bac112df35bbc829138b946f79093e3e9171c23ea4ceb3bc9937c13d0639926778d62ba2437e167536b743d4dd44db6798da3ec5d0766144c751066f1c26b0de7fb746d4483ea2f133cceb14220f1d3e8c2e10e9374de41cfa7f23aef0ef39a667a8738984d518dafb7bb958e38431cc21ee819fe60c550945ce53bc7514c8e6b0c267a6c551ea858fe21c7b9c285946471ec3d4fb37582678f67f0dd72b0cd62a831cef306167f33c398d629932f54d93433cd64d87098e779ace51549b10942d03198d27b8de2130b619fc51a063fb3c31c9e3fa127ba4dba1ca8598e779366b0c11bc6e7f09b27932937a99502850c7509c66d8a121649a325097d1f1b5be7792526ceb44c89b6c4d609151495143689ac117d2661a128a8ce22d0926c7f1d54242cc3474f70d47d1d622df1167b9022851d41525454c14247f205bee323232b5e1a0eb0d11c6520d461065541512045a4dbe7f1cca333c6fc2d1908b2fb5cef3fd0306521e6e219ae6d9de21c6940bac3f87e498d241817cde3e914811a53926f038c881baddec71de758fa63a7c879b68d91f859962471b77a423bdee3050f38d0b3ddfe20b1923f0b6b90b28c5b8ac35d207f26b1d0b27c751a4818daf32122b881a1c7f1d68324c539d58e049b1c67858d5020cc753e8194a782c0c439a43de0a931d473368ef3dc891cceb4f83fd0349c8e328d30b1d67f45b0424e1677a0620c7f758858d232884933e51621235982398d46f19c694090530412632b060b093e515368933ab7c40dee749be106f737c811d45b3acc327dde4583e9d4fe9901fc2c57445060da57448831bcca498eaa313537cf71d61a849036da2a4fb2dba30cdd12635cc3509e62851247c558c91d81b7ccf11f0edaeeb30421adf3760614d261cd42ef1422167da1a618c3778fea11267d1468914e836f99e4c9821a4891bc3520c991d47d1be936e87fc7d033ac2ea0c751d67d0be931f2a106f859d641b5dd28b32c43e2a3bd4299a0609f0f3fd3340dd23e4894450322c6d28486c25be22dba206e9285d6db1ba1eedd1468eba44d608f240c239d26f154877582a8df033a4fa9f7e840996df19c33b6d1140c5f27c41cdf4ca2305132751be658ce32d3f251fc8b0ff3ad1d928934450b47c75c1c3ea7d038289f868fd4362ae907f3bc8382a2a269367e82fa2dbe3683f516471a4735192565a25e2036c75de931a4a10e9375294994234a6cc31ba639167488e3f8df31c4d10c7bbf44f26d4237c7f3a87f3c4b61867dca4cf284da22c7f17c9b349024f99c3f5ba7487d3bc7f3a5025098607d6794e3390efd368328fa35a3b033bd3ecb0877794e7b936890df6393e45879b1c8b05f3787f6190e359370306b475de4d8fecb448418fe34b1c1fcd223a2c39a7c14eef26d121167f11d0726dd7030fe91a2a3999e7bb2dd25d045ca1239b5123c8ea41a8dca9d) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_273 : Impossible 0x802101000000000000000000 0x15507fd004000000000000000000 :=
  checkChunk_sound (initRounds:=2) (rounds:=8) (fuel:=21) (code:=0x9332d1d00fe558ba95b67993e21c4687e2ab6c7f3ace310b93996718f6749d6358fe234e31fdb6a57cc34cf127868da3a8379c48b14c871d53a1bf010df34893b7e3e2361a49dde3be029d6d88ca2ceb36d9e37d091b62527cb7c737586d9a6120e68d7fa749f74c14218ae7d06b86a14164db404ef5287523a6390a529fd053bc3398e7c94a1d52639a9c3a94c8b37c9a3e43dd21279d4451648920286a0aef37cda4d86dbeceb28c671fd153dcc70fe71a2c7c9ee71a02df0ca3db3d1a0de3aba4df36cff074b3c933e51a8b1e4891b4fae5202468226f9465ca739d501224da848fa4e88ea34459c63abe4398ea7da2e93912368fa7cb9474c14399f6a56da2afd07c9c47f5290a73859035bbc6ef314c9b1b47122d034e89d1d4fa1f27da1687a2a75a068b1d417ca73ab949f0da3aa1472a959ef5) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_274 : Impossible 0x10000802001000000000000000000 0x15507fd104000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=9) (fuel:=21) (code:=0xf93c44d435013ac21692a8cf67b9261ece624d0e339023f91b4650a0d67b21442a24eb42484b2cde2125913c652984324d322167ba4c7f20e733d4f942485b2d4ec73f4469154b48d639f606b19502498e222a3459748da37c79a9cff28d0b38ceb234ef1fc37cc7659b6651b61a1168a94adb42c455b6659f252ba4a77e8653e826b7c28e2a6fbbc6fa2af93dc2b8de3f8d68689a2325d0f435a054e145191d2a71b4653dd0b1bc711a50ac721e679ee9f0932c8da7d22dea029e1b158c9f232bd44cd0f3e63286a4a469021cc969153e5eaa4a52f33bceb1f63c9f22cb2d4e232f524dee10722c65291b48da2cf920edb67893074db429f5ca264519ff154240b27d1bc69134994986b2341662a7d0fa46a143f9cdee2147d75b1c39c6d3ac851fdc663827a64859f491c54e9425eeef22a799fa3f5c675b6c8aa12378e69f1de7b9d2658ef718e6739e623e4195c81195d6216c73ac853e8d2a70e70ef7a91a7d36c56278d22347d499d639cf553a2dba434f73ec32a9c3ec6d8ca0a329bc1262b8c9162d90a232c732c6f43485229f4348de3987f1cc9f1256390b369ee4f9bd0a2148b3eb7512c1) (by decide +kernel)

set_option maxHeartbeats 8000000 in
private lemma chk_275 : Impossible 0x802001000000000000000000 0x115507fd104000000000000000000 :=
  checkChunk_sound (initRounds:=1) (rounds:=11) (fuel:=29) (code:=0x3b20c6b234993bc1d2cb338de1cd4e478c33a84b484fe77b7c748809fce320cef0cea761bac388711fcd70df234e28c8fe4ca4c40cfea71321468924c991ec92bbe1290a0e0de44a8ca72647f8182a9127119c7b1fc75135be0de936bc2c398e2849374ec929c50b46c89518a31ccf63f88d5383d9c47f4cbddf20a77ac6ce7424df3e449a649a8498e629b2c858b849c6d2739c671cdbe96810ca324df2754c83d966127102324dbe398d689881c247b205ce7f80b1c264ce438e63f91b424f92644051b4c9fc552358edb3f40cadf1ae0231c639be46c050949db640847612739f20ca7f3bdbe87a06166321cc932051a1fd1b26b6dd21268e9ce759e70108eb7c991644c9f66f9d69d80b6c4591acf23a7588d0df2051a37ce232a067f93340d363a90375d0c879ceef1de456d81fe71459b6590e64526c87be4ef3ad9e1268b89acc51d234816f8597d9d61028d3ee06db52ba60a414a520a52b6ce332c88a46848df0e6759e684a2641a75b67b9c68a84f28cdb37d96650f9928931d69ba022a88a77b6c8b29e0a8a8f740cdf0fe40c81419262c88d359dedb52ba61a234f333c8e8e22683fc748d828671a48d1ae1adb428691cc4193677b6ceb40d1208ab6c8a7786a511948138ce932cfa22c4591a658e3529b6124db1b4fb1911524ce36dc340cb257c86f36e0a8a9963e4e724c22d2632a2a3489a24e1a7cb6c33b2d1a0db498ea3fa35033e8499cf0952ba4897e811cfa418e6cf09a06b4ec0d151034e99e7c9547c9fc81bddc6274473e5d63ad36810fef3093ce59ee7132799fa809f28aa1e819ee29c6b39c8328c1bcb29d3dc739f45293223903359ee539353e9b493be59eef075358730a7398ce388ea4251eeb0e282ba4818e2399029d28d9e9f0e72ca3e7d8eb2167d9d6e73f4e20ea7f3e83f9a46f3f45d205d28b1de73b7c358531d46b3ed1d52a223f93a1fcfa405f20b240a2b193a41a5de205154049aa08ea9a8e219501023d453d4e63e8a8ca4d1d4717c815ce31b0ba368b238902830d6f33edce9d1e6778a6498933cc6d21c7b1747338a3a73a941bc93135474478ca04749d53a7d6fb1dea4449d1d519206712128d42c1fdea81a02389038483785a4c8c91d85a4e75a268494c469f42147d24cb236a6411d011a42c8e274a751582882a22a49a50324c5d14c47089a065b1748e89216e91b4ea13c351c4931d43aa127d0e33526ae94685923d328b0691d51647a224c881a64d608188cb6751a512035c447543917033dc3a9cc4b53a7c08728c6b1d3d4d64586b1f5261eb114153a27d034747ba0699126e93a87d0d29311e750ce2cb8c328be4fa9caa47411d84c0c6a6b14c8b0a2358ce7d1951a23cc73fa044c86b264654152f81a4e468ea22626266561f66a11527a8d1b40e163f5034248194614ca340c8945c45c6ef0d644853bace7428999ee06a69368b2a71ac44a747128c530de3582cc654e74a128a93ac7828c70e24450b4f8e6519bc03981a7e6a39a9c1a912378726d3a8fa1ce750854dbdc4dbac21536378f6c728c934c8135ef0314c9b1c4eb1ccc71f51a085a15271ef2322b1322275639138684d7594c338fb0304714cd6135150dd4e3e8be9311d8ca12749cc4e8ce47a8c1ce2e24cfa8d408206e7449d2751ce27a2a939130b093a758e75a068a90b4c519405153a9c4991d2368fa8d4588d1c459206992241d63a8680cea4a3b1181c94f50faa342498c56160ce7d46a05c639c8929c978d7031471306b888c7818c78490e3788aa8d127590a8d94f0b14e075539123491a8b888d61ad46e377bfc539be718466a688a15350aa9d1f442c546fa34269944990e7a8ce519d60ce830be33a9c5b1bcaa0a72fc653619c4946c0c0ff0b29ce744e2a519c66fbbc7a9a414eff82a3ae94083a8df170ea26a7a8e4474c9ce2990e399aceb1329b1fe268864d842a6c391a4753986910a672046f1cc42a6dd62069b1a46b1d4393fc6f7ba9c474eb29cf737a253ef31162347d49a4e4e9434ce121d51923509818751198288ac74ff46a4c84a75d240d361ad324cd071bcfe45c3aa2246c0d05264671fd137993124d334451349ce97e92716c44e124c8d6e70ea89505de11a86cd5d63fcc71fc8da067e8ff1739c8d0299a44f19cea2e83491e753f83a9a4831fc9346a2c33906468da4e8ca3a8d6994260239cfd0e27e91a23533031033f4ff3be2a3a912478e28b71b6dbac10619fd2f818e67f9fa475d68385930c8dbfc8d29cfd6785929d037b9be28d1732d113a4749c6c3126df08533a9c74830c8547c6481ba45f1ed026f9fc74a248b9d63fa36468d2fd80819d4e498d28d1fcc3103235c6538ce3a8e63fc4493bf5f220e6fc058e0a56599e4d4f5151e42049a2e8e336d0533c691b6a537cfe3adde135fee90a72ca0a6fa2286826ba4594450d3fc0431cfef90f5539f66fa1a94a0a2a9b429cfe679166392d7783fc740dba58e642c752d8c9de7f935d27506994a0a6f99e538fb29c1f2c7539fcdb37cea369948899e4588b328cf1cd0313ea73ddd214ecf36e0252bf48783f9d7016d9fe1659e9b06b718ea3f9be0ce81beccb27cf731c279c67b882df7488a3a51667a34464353f9167e8da2c82696436ccf16e32328a77ca6c0926b29ce794bbd020ce1191b90c9319ce945b3c4998e7b99e7f05d339ac7b95d1a1ccf7234930e33f88e8b0b677a04ea7d1be458da9e8b27b8ea1646d1ce2c8be459be93c143ac5982892288def71ee739f43dc7f8eb8cdb2271540414f1d3591682855479b63f8e74448b4547f36cfa0a64f9ea35a9cdf1c9d41f4fe36a023a92635a363222e7fc745707d2144d8e99681bdcdb08b46c04df0a7415e71574b7437ce73dcba47946158e645a024cc8eb7d250452e87f37dba7799e1fcdf051350a0de2797427c8f13dba6391c6b1d23782d9d2a76e81cdbaa728d17779b7053ec82c74499f66d9468898e5537cea39cef31cfa89608196e9444c32c90e2064399ca314cd63a4e634a34ef2241a98e7f4eb943892639906449d21e6539fdca758993dce513240c4f7b8be298aa889be3594e4c4df2247b1ac3aa8e16f9214db639861fc671cc638e65337c061249c6851ecfe186339fd3a0c3779f2475190b7b842ccd031fcdb639ac30d0341cf33f9ee12742dc680b0dbe51a3c0d70d1ccf7268aa33a0d02f1) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem root_impossible : Impossible 0x802000000000000000000000 0x7fc000000000000000000000 := by
  have sr0 : SymMask 0x802000000000000000000000 := sym_of_decide (by decide +kernel)
  have sb0 : SymMask 0x7fc000000000000000000000 := sym_of_decide (by decide +kernel)
  have sr1 : SymMask 0x1000802001000000000000000000 := sym_add_pair (u:=72) (by decide) sr0
  have sb2 : SymMask 0x10007fc001000000000000000000 := sym_add_pair (u:=72) (by decide) sb0
  have sr3 : SymMask 0x1400802005000000000000000000 := sym_add_pair (u:=74) (by decide) sr1
  have sb4 : SymMask 0x4007fc004000000000000000000 := sym_add_pair (u:=74) (by decide) sb0
  have sr5 : SymMask 0x1480802025000000000000000000 := sym_add_pair (u:=77) (by decide) sr3
  have sb6 : SymMask 0x807fc020000000000000000000 := sym_add_pair (u:=77) (by decide) sb0
  have sb8 : SymMask 0x400007fc000040000000000000000 := sym_add_pair (u:=66) (by decide) sb0
  have chk_15 : Impossible 0x1480802025000000000000000000 0x400007fc000040000000000000000 := sym_branch3 83 (by decide) sr5 sb8 chk_12 chk_13 chk_14
  have chk_17 : Impossible 0x1480802025000000000000000000 0x7fc000000000000000000000 := sym_branch3 66 (by decide) sr5 sb0 chk_9 chk_15 chk_16
  have sb19 : SymMask 0x100807fc020100000000000000000 := sym_add_pair (u:=68) (by decide) sb6
  have chk_26 : Impossible 0x1400802005000000000000000000 0x100807fc020100000000000000000 := sym_branch3 61 (by decide) sr3 sb19 chk_23 chk_24 chk_25
  have chk_28 : Impossible 0x1400802005000000000000000000 0x807fc020000000000000000000 := sym_branch3 68 (by decide) sr3 sb6 chk_20 chk_26 chk_27
  have chk_30 : Impossible 0x1400802005000000000000000000 0x7fc000000000000000000000 := sym_branch3 77 (by decide) sr3 sb0 chk_17 chk_28 chk_29
  have sr31 : SymMask 0x1040802041000000000000000000 := sym_add_pair (u:=78) (by decide) sr1
  have sb32 : SymMask 0x4407fc044000000000000000000 := sym_add_pair (u:=78) (by decide) sb4
  have sr33 : SymMask 0x10608020c1000000000000000000 := sym_add_pair (u:=79) (by decide) sr31
  have sb34 : SymMask 0x4207fc084000000000000000000 := sym_add_pair (u:=79) (by decide) sb4
  have chk_40 : Impossible 0x10608020c1000000000000000000 0x4007fc004000000000000000000 := sym_branch3 53 (by decide) sr33 sb4 chk_37 chk_38 chk_39
  have chk_46 : Impossible 0x1040802041000000000000000000 0x4207fc084000000000000000000 := sym_branch3 64 (by decide) sr31 sb34 chk_43 chk_44 chk_45
  have chk_48 : Impossible 0x1040802041000000000000000000 0x4007fc004000000000000000000 := sym_branch3 79 (by decide) sr31 sb4 chk_40 chk_46 chk_47
  have sr49 : SymMask 0x5000802001400000000000000000 := sym_add_pair (u:=70) (by decide) sr1
  have sb50 : SymMask 0x44407fc044400000000000000000 := sym_add_pair (u:=70) (by decide) sb32
  have chk_56 : Impossible 0x5000802001400000000000000000 0x4407fc044000000000000000000 := sym_branch3 84 (by decide) sr49 sb32 chk_53 chk_54 chk_55
  have chk_62 : Impossible 0x1000802001000000000000000000 0x44407fc044400000000000000000 := sym_branch3 66 (by decide) sr1 sb50 chk_59 chk_60 chk_61
  have chk_64 : Impossible 0x1000802001000000000000000000 0x4407fc044000000000000000000 := sym_branch3 70 (by decide) sr1 sb32 chk_56 chk_62 chk_63
  have chk_66 : Impossible 0x1000802001000000000000000000 0x4007fc004000000000000000000 := sym_branch3 78 (by decide) sr1 sb4 chk_48 chk_64 chk_65
  have chk_68 : Impossible 0x1000802001000000000000000000 0x7fc000000000000000000000 := sym_branch3 74 (by decide) sr1 sb0 chk_30 chk_66 chk_67
  have sr69 : SymMask 0x1803000000000000000000000 := sym_add_pair (u:=84) (by decide) sr0
  have sb70 : SymMask 0x10017fd001000000000000000000 := sym_add_pair (u:=84) (by decide) sb2
  have sr71 : SymMask 0x10001803000100000000000000000 := sym_add_pair (u:=68) (by decide) sr69
  have sb72 : SymMask 0x110007fc001100000000000000000 := sym_add_pair (u:=68) (by decide) sb2
  have sr73 : SymMask 0x50001803000140000000000000000 := sym_add_pair (u:=66) (by decide) sr71
  have sb74 : SymMask 0x410007fc001040000000000000000 := sym_add_pair (u:=66) (by decide) sb2
  have chk_80 : Impossible 0x50001803000140000000000000000 0x10007fc001000000000000000000 := sym_branch3 46 (by decide) sr73 sb2 chk_77 chk_78 chk_79
  have chk_86 : Impossible 0x10001803000100000000000000000 0x410007fc001040000000000000000 := sym_branch3 62 (by decide) sr71 sb74 chk_83 chk_84 chk_85
  have chk_88 : Impossible 0x10001803000100000000000000000 0x10007fc001000000000000000000 := sym_branch3 66 (by decide) sr71 sb2 chk_80 chk_86 chk_87
  have sr89 : SymMask 0x4001803000400000000000000000 := sym_add_pair (u:=70) (by decide) sr69
  have sb90 : SymMask 0x150007fc001500000000000000000 := sym_add_pair (u:=70) (by decide) sb72
  have chk_96 : Impossible 0x4001803000400000000000000000 0x110007fc001100000000000000000 := sym_branch3 62 (by decide) sr89 sb72 chk_93 chk_94 chk_95
  have chk_103 : Impossible 0x1803000000000000000000000 0x5d0007fc001540000000000000000 := branch2 109 chk_101 chk_102
  have chk_104 : Impossible 0x1803000000000000000000000 0x550007fc001540000000000000000 := branch2 111 chk_100 chk_103
  have chk_106 : Impossible 0x1803000000000000000000000 0x150007fc001500000000000000000 := sym_branch3 66 (by decide) sr69 sb90 chk_99 chk_104 chk_105
  have chk_108 : Impossible 0x1803000000000000000000000 0x110007fc001100000000000000000 := sym_branch3 70 (by decide) sr69 sb72 chk_96 chk_106 chk_107
  have chk_110 : Impossible 0x1803000000000000000000000 0x10007fc001000000000000000000 := sym_branch3 68 (by decide) sr69 sb2 chk_88 chk_108 chk_109
  have sr111 : SymMask 0x40802040000000000000000000 := sym_add_pair (u:=78) (by decide) sr0
  have sb112 : SymMask 0x10417fd041000000000000000000 := sym_add_pair (u:=78) (by decide) sb70
  have sr113 : SymMask 0x50802140000000000000000000 := sym_add_pair (u:=80) (by decide) sr111
  have sb114 : SymMask 0x10117fd101000000000000000000 := sym_add_pair (u:=80) (by decide) sb70
  have chk_120 : Impossible 0x50802140000000000000000000 0x10017fd001000000000000000000 := sym_branch3 63 (by decide) sr113 sb70 chk_117 chk_118 chk_119
  have chk_126 : Impossible 0x40802040000000000000000000 0x10117fd101000000000000000000 := sym_branch3 76 (by decide) sr111 sb114 chk_123 chk_124 chk_125
  have chk_128 : Impossible 0x40802040000000000000000000 0x10017fd001000000000000000000 := sym_branch3 80 (by decide) sr111 sb70 chk_120 chk_126 chk_127
  have sr129 : SymMask 0x8000802000200000000000000000 := sym_add_pair (u:=69) (by decide) sr0
  have sb130 : SymMask 0x90417fd041200000000000000000 := sym_add_pair (u:=69) (by decide) sb112
  have chk_136 : Impossible 0x8000802000200000000000000000 0x10417fd041000000000000000000 := sym_branch3 76 (by decide) sr129 sb112 chk_133 chk_134 chk_135
  have chk_145 : Impossible 0x802000000000000000000000 0x82490417fd041248000000000000000 := branch2 99 chk_143 chk_144
  have chk_146 : Impossible 0x802000000000000000000000 0x2490417fd041248000000000000000 := branch2 123 chk_142 chk_145
  have chk_147 : Impossible 0x802000000000000000000000 0x2490417fd041240000000000000000 := branch2 63 chk_141 chk_146
  have chk_148 : Impossible 0x802000000000000000000000 0x490417fd041240000000000000000 := branch2 117 chk_140 chk_147
  have chk_150 : Impossible 0x802000000000000000000000 0x90417fd041200000000000000000 := sym_branch3 66 (by decide) sr0 sb130 chk_139 chk_148 chk_149
  have chk_152 : Impossible 0x802000000000000000000000 0x10417fd041000000000000000000 := sym_branch3 69 (by decide) sr0 sb112 chk_136 chk_150 chk_151
  have chk_157 : Impossible 0x100802040000000000000000000 0x2090417fd001000000000000000000 := branch2 114 chk_155 chk_156
  have chk_158 : Impossible 0x100802040000000000000000000 0x90417fd001000000000000000000 := branch2 117 chk_154 chk_157
  have chk_159 : Impossible 0x100802040000000000000000000 0x10417fd001000000000000000000 := branch2 111 chk_153 chk_158
  have chk_163 : Impossible 0x400802040000000000000000000 0x11417fd011000000000000000000 := branch2 116 chk_161 chk_162
  have chk_164 : Impossible 0x400802040000000000000000000 0x11417fd001000000000000000000 := branch2 76 chk_160 chk_163
  have chk_170 : Impossible 0x10802040000000000000000000 0x15457fd211000000000000000000 := branch2 101 chk_168 chk_169
  have chk_171 : Impossible 0x10802040000000000000000000 0x15457fd011000000000000000000 := branch2 81 chk_167 chk_170
  have chk_172 : Impossible 0x10802040000000000000000000 0x15457fd001000000000000000000 := branch2 76 chk_166 chk_171
  have chk_174 : Impossible 0x802040000000000000000000 0x15457fd001000000000000000000 := branch2 100 chk_172 chk_173
  have chk_175 : Impossible 0x802040000000000000000000 0x15417fd001000000000000000000 := branch2 98 chk_165 chk_174
  have chk_176 : Impossible 0x802040000000000000000000 0x11417fd001000000000000000000 := branch2 106 chk_164 chk_175
  have chk_177 : Impossible 0x802040000000000000000000 0x10417fd001000000000000000000 := branch2 104 chk_159 chk_176
  have chk_178 : Impossible 0x802000000000000000000000 0x10017fd001000000000000000000 := sym_branch3 78 (by decide) sr0 sb70 chk_128 chk_152 chk_177
  have chk_183 : Impossible 0x10000803000000000000000000000 0x210017fc001100000000000000000 := branch2 103 chk_181 chk_182
  have chk_184 : Impossible 0x10000803000000000000000000000 0x10017fc001100000000000000000 := branch2 113 chk_180 chk_183
  have chk_185 : Impossible 0x10000803000000000000000000000 0x10017fc001000000000000000000 := branch2 68 chk_179 chk_184
  have chk_193 : Impossible 0x4000803000000000000000000000 0x14191017fc001200000000000000000 := branch2 76 chk_191 chk_192
  have chk_194 : Impossible 0x4000803000000000000000000000 0x14191017fc001000000000000000000 := branch2 69 chk_190 chk_193
  have chk_195 : Impossible 0x4000803000000000000000000000 0x14111017fc001000000000000000000 := branch2 111 chk_189 chk_194
  have chk_196 : Impossible 0x4000803000000000000000000000 0x4111017fc001000000000000000000 := branch2 120 chk_188 chk_195
  have chk_197 : Impossible 0x4000803000000000000000000000 0x4110017fc001000000000000000000 := branch2 104 chk_187 chk_196
  have chk_198 : Impossible 0x4000803000000000000000000000 0x110017fc001000000000000000000 := branch2 118 chk_186 chk_197
  have chk_206 : Impossible 0x100803000000000000000000000 0x1d0a17fc041100000000000000000 := branch2 63 chk_204 chk_205
  have chk_207 : Impossible 0x100803000000000000000000000 0x1d0217fc041100000000000000000 := branch2 103 chk_203 chk_206
  have chk_208 : Impossible 0x100803000000000000000000000 0x1d0217fc001100000000000000000 := branch2 78 chk_202 chk_207
  have chk_209 : Impossible 0x100803000000000000000000000 0x1d0217fc001000000000000000000 := branch2 68 chk_201 chk_208
  have chk_210 : Impossible 0x100803000000000000000000000 0x1d0017fc001000000000000000000 := branch2 101 chk_200 chk_209
  have chk_211 : Impossible 0x100803000000000000000000000 0x150017fc001000000000000000000 := branch2 111 chk_199 chk_210
  have chk_214 : Impossible 0x10803000000000000000000000 0x151017fc001000000000000000000 := branch2 111 chk_212 chk_213
  have chk_221 : Impossible 0x40803000000000000000000000 0x10751917fc001000000000000000000 := branch2 115 chk_219 chk_220
  have chk_222 : Impossible 0x40803000000000000000000000 0x10551917fc001000000000000000000 := branch2 113 chk_218 chk_221
  have chk_223 : Impossible 0x40803000000000000000000000 0x10551117fc001000000000000000000 := branch2 103 chk_217 chk_222
  have chk_225 : Impossible 0x803000000000000000000000 0x10551117fc001000000000000000000 := branch2 102 chk_223 chk_224
  have chk_226 : Impossible 0x803000000000000000000000 0x551117fc001000000000000000000 := branch2 120 chk_216 chk_225
  have chk_227 : Impossible 0x803000000000000000000000 0x151117fc001000000000000000000 := branch2 114 chk_215 chk_226
  have chk_228 : Impossible 0x803000000000000000000000 0x151017fc001000000000000000000 := branch2 100 chk_214 chk_227
  have chk_229 : Impossible 0x803000000000000000000000 0x150017fc001000000000000000000 := branch2 104 chk_211 chk_228
  have chk_230 : Impossible 0x803000000000000000000000 0x110017fc001000000000000000000 := branch2 110 chk_198 chk_229
  have chk_231 : Impossible 0x803000000000000000000000 0x10017fc001000000000000000000 := branch2 112 chk_185 chk_230
  have chk_232 : Impossible 0x802000000000000000000000 0x10007fc001000000000000000000 := sym_branch3 84 (by decide) sr0 sb2 chk_110 chk_178 chk_231
  have chk_237 : Impossible 0x803001000000000000000000 0x10007fc000100400000000000000 := branch2 103 chk_235 chk_236
  have chk_238 : Impossible 0x803001000000000000000000 0x10007fc000100000000000000000 := branch2 58 chk_234 chk_237
  have chk_239 : Impossible 0x803001000000000000000000 0x10007fc000000000000000000000 := branch2 68 chk_233 chk_238
  have chk_242 : Impossible 0x802005000000000000000000 0x10007fd000000000000000000000 := branch2 102 chk_240 chk_241
  have chk_247 : Impossible 0x40802001000000000000000000 0x11007fd004000100000000000000 := branch2 64 chk_245 chk_246
  have chk_248 : Impossible 0x40802001000000000000000000 0x11007fd004000000000000000000 := branch2 56 chk_244 chk_247
  have chk_249 : Impossible 0x40802001000000000000000000 0x10007fd004000000000000000000 := branch2 104 chk_243 chk_248
  have chk_256 : Impossible 0x100802001000000000000000000 0x412410407fd004000000000000000000 := branch2 111 chk_254 chk_255
  have chk_257 : Impossible 0x100802001000000000000000000 0x402410407fd004000000000000000000 := branch2 120 chk_253 chk_256
  have chk_258 : Impossible 0x100802001000000000000000000 0x2410407fd004000000000000000000 := branch2 126 chk_252 chk_257
  have chk_259 : Impossible 0x100802001000000000000000000 0x410407fd004000000000000000000 := branch2 117 chk_251 chk_258
  have chk_260 : Impossible 0x100802001000000000000000000 0x10407fd004000000000000000000 := branch2 114 chk_250 chk_259
  have chk_266 : Impossible 0x400802001000000000000000000 0x431407fd084000000000000000000 := branch2 69 chk_264 chk_265
  have chk_267 : Impossible 0x400802001000000000000000000 0x411407fd084000000000000000000 := branch2 109 chk_263 chk_266
  have chk_268 : Impossible 0x400802001000000000000000000 0x411407fd004000000000000000000 := branch2 79 chk_262 chk_267
  have chk_269 : Impossible 0x400802001000000000000000000 0x11407fd004000000000000000000 := branch2 114 chk_261 chk_268
  have chk_272 : Impossible 0x10802001000000000000000000 0x15407fd004000000000000000000 := branch2 82 chk_270 chk_271
  have chk_276 : Impossible 0x802001000000000000000000 0x15507fd104000000000000000000 := branch2 112 chk_274 chk_275
  have chk_277 : Impossible 0x802001000000000000000000 0x15507fd004000000000000000000 := branch2 80 chk_273 chk_276
  have chk_278 : Impossible 0x802001000000000000000000 0x15407fd004000000000000000000 := branch2 100 chk_272 chk_277
  have chk_279 : Impossible 0x802001000000000000000000 0x11407fd004000000000000000000 := branch2 106 chk_269 chk_278
  have chk_280 : Impossible 0x802001000000000000000000 0x10407fd004000000000000000000 := branch2 104 chk_260 chk_279
  have chk_281 : Impossible 0x802001000000000000000000 0x10007fd004000000000000000000 := branch2 102 chk_249 chk_280
  have chk_282 : Impossible 0x802001000000000000000000 0x10007fd000000000000000000000 := branch2 74 chk_242 chk_281
  have chk_283 : Impossible 0x802001000000000000000000 0x10007fc000000000000000000000 := branch2 84 chk_239 chk_282
  have chk_284 : Impossible 0x802000000000000000000000 0x7fc000000000000000000000 := sym_branch3 72 (by decide) sr0 sb0 chk_68 chk_232 chk_283
  exact chk_284

end OMA.W314H3R1H1

theorem OMA.solution : OMA.R_Green14_W_3_14_R1_H3_R1_H3_R1.H1 :=
  OMA.W314H3R1H1.prove_H1_of_root OMA.W314H3R1H1.root_impossible
