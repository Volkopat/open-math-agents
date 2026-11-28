import OMAStatements.S_oeis_a183356

namespace OMA.S_oeis_a183356

open PowerSeries






/-- The ways to add m rows below c (with p above c) and finish the scan. -/
def N (p : Option (Fin 4 → Fin 4)) (c : Fin 4 → Fin 4) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 4 → Fin 4, if okRows p c (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 4 → Fin 4) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 4 → Fin 4, f (List.ofFn x) =
      ∑ c : Fin 4 → Fin 4, ∑ y : Fin m → Fin 4 → Fin 4, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 4 → Fin 4).sum_comp]
  rw [Fintype.sum_prod_type (f := fun q : (Fin 4 → Fin 4) × (Fin m → Fin 4 → Fin 4) =>
    f (List.ofFn ((Fin.consEquiv fun _ => Fin 4 → Fin 4) q)))]
  simp [List.ofFn_succ]

theorem N_zero (p : Option (Fin 4 → Fin 4)) (c : Fin 4 → Fin 4) :
    N p c 0 = if rowOK p c none = true then 1 else 0 := by
  simp [N, okRows]

theorem N_succ (p : Option (Fin 4 → Fin 4)) (c : Fin 4 → Fin 4) (m : ℕ) :
    N p c (m + 1) = ∑ r : Fin 4 → Fin 4, if rowOK p c (some r) = true then N (some c) r m else 0 := by
  have h := sum_cons m (fun l => if okRows p c l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : rowOK p c (some r) = true
  · rw [if_pos hr]
    apply Finset.sum_congr rfl
    intro y _
    simp only [okRows, hr, Bool.true_and]
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro y _
    have hr' := Bool.eq_false_iff.mpr hr
    have hk : okRows p c (r :: List.ofFn y) = false := by
      simp only [okRows, hr', Bool.false_and]
    simp [hk]

/-- x and y differ, compared as natural numbers (cheap for the kernel). -/
def nd2 (x y : Fin 4) : Bool := !Nat.beq x.val y.val

/-- x, y, z are pairwise different. -/
def nd3 (x y z : Fin 4) : Bool := nd2 x y && nd2 x z && nd2 y z

/-- x, y, z, t are pairwise different. -/
def nd4 (x y z t : Fin 4) : Bool := nd2 x y && nd2 x z && nd2 x t && nd2 y z && nd2 y t && nd2 z t

theorem nodup2 (x y : Fin 4) : decide ([x, y].Nodup) = nd2 x y := by
  revert x y
  decide +kernel

theorem nodup3 (x y z : Fin 4) : decide ([x, y, z].Nodup) = nd3 x y z := by
  revert x y z
  decide +kernel

theorem nodup4 (x y z t : Fin 4) : decide ([x, y, z, t].Nodup) = nd4 x y z t := by
  revert x y z t
  decide +kernel

/-- The condition of the last row, for the class with u = (p0, p2) above and v = (c1, c3). -/
def baseX (u v : Fin 4 × Fin 4) : Bool := nd2 u.1 v.1 && nd3 u.2 v.1 v.2

/-- The condition of the last row, for the class with u = (p1, p3) above and v = (c0, c2). -/
def baseY (u v : Fin 4 × Fin 4) : Bool := nd3 u.1 v.1 v.2 && nd2 u.2 v.2

/-- The condition of a row with a row below it, for the class with u = (p0, p2) above,
v = (c1, c3) and w = (t0, t2) below. -/
def stepX (u v w : Fin 4 × Fin 4) : Bool := nd3 u.1 w.1 v.1 && nd4 u.2 w.2 v.1 v.2

/-- The condition of a row with a row below it, for the class with u = (p1, p3) above,
v = (c0, c2) and w = (t1, t3) below. -/
def stepY (u v w : Fin 4 × Fin 4) : Bool := nd4 u.1 w.1 v.1 v.2 && nd3 u.2 w.2 v.2

theorem rowOK_ss (p c t : Fin 4 → Fin 4) : rowOK (some p) c (some t) =
    (stepX (p 0, p 2) (c 1, c 3) (t 0, t 2) && stepY (p 1, p 3) (c 0, c 2) (t 1, t 3)) := by
  rw [Bool.eq_iff_iff]
  simp only [rowOK, stepX, stepY, ← nodup3, ← nodup4, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨⟨h 0, h 2⟩, h 1, h 3⟩
  · rintro ⟨⟨h0, h2⟩, h1, h3⟩ j
    fin_cases j
    exacts [h0, h1, h2, h3]

theorem rowOK_sn (p c : Fin 4 → Fin 4) : rowOK (some p) c none =
    (baseX (p 0, p 2) (c 1, c 3) && baseY (p 1, p 3) (c 0, c 2)) := by
  rw [Bool.eq_iff_iff]
  simp only [rowOK, baseX, baseY, ← nodup2, ← nodup3, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨⟨h 0, h 2⟩, h 1, h 3⟩
  · rintro ⟨⟨h0, h2⟩, h1, h3⟩ j
    fin_cases j
    exacts [h0, h1, h2, h3]

theorem rowOK_ns (c s : Fin 4 → Fin 4) : rowOK none c (some s) =
    (baseX (s 0, s 2) (c 1, c 3) && baseY (s 1, s 3) (c 0, c 2)) := by
  rw [Bool.eq_iff_iff]
  simp only [rowOK, baseX, baseY, ← nodup2, ← nodup3, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨⟨h 0, h 2⟩, h 1, h 3⟩
  · rintro ⟨⟨h0, h2⟩, h1, h3⟩ j
    fin_cases j
    exacts [h0, h1, h2, h3]

theorem rowOK_nn (c : Fin 4 → Fin 4) : rowOK none c none = (nd2 (c 0) (c 2) && nd2 (c 1) (c 3)) := by
  rw [Bool.eq_iff_iff]
  simp only [rowOK, ← nodup2, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h 1, h 2⟩
  · rintro ⟨h1, h2⟩ j
    fin_cases j
    exacts [List.nodup_singleton _, h1, h2, List.nodup_singleton _]

/-- The row with (x0, x2) = w and (x1, x3) = w'. -/
def mkRow (w w' : Fin 4 × Fin 4) : Fin 4 → Fin 4 := ![w.1, w'.1, w.2, w'.2]

theorem mkRow_eta (t : Fin 4 → Fin 4) : mkRow (t 0, t 2) (t 1, t 3) = t := by
  funext j
  fin_cases j <;> rfl

theorem mkRow_0 (w w' : Fin 4 × Fin 4) : mkRow w w' 0 = w.1 := rfl

theorem mkRow_1 (w w' : Fin 4 × Fin 4) : mkRow w w' 1 = w'.1 := rfl

theorem mkRow_2 (w w' : Fin 4 × Fin 4) : mkRow w w' 2 = w.2 := rfl

theorem mkRow_3 (w w' : Fin 4 × Fin 4) : mkRow w w' 3 = w'.2 := rfl

theorem mkRow_02 (w w' : Fin 4 × Fin 4) : (mkRow w w' 0, mkRow w w' 2) = w := rfl

theorem mkRow_13 (w w' : Fin 4 × Fin 4) : (mkRow w w' 1, mkRow w w' 3) = w' := rfl

/-- A row as its two column pairs, columns 0 and 2 and columns 1 and 3. -/
def rowEquiv : (Fin 4 → Fin 4) ≃ (Fin 4 × Fin 4) × (Fin 4 × Fin 4) where
  toFun t := ((t 0, t 2), (t 1, t 3))
  invFun q := mkRow q.1 q.2
  left_inv t := mkRow_eta t
  right_inv _ := rfl

theorem sum_row (g : (Fin 4 → Fin 4) → ℕ) :
    ∑ t : Fin 4 → Fin 4, g t = ∑ w : Fin 4 × Fin 4, ∑ w' : Fin 4 × Fin 4, g (mkRow w w') :=
  (Fintype.sum_equiv rowEquiv g (fun q => g (mkRow q.1 q.2)) (fun t => congrArg g (mkRow_eta t).symm)).trans
    (Fintype.sum_prod_type' (fun w w' => g (mkRow w w')))

theorem ite_and_one (x y : Bool) :
    (if (x && y) = true then 1 else 0) = (if x = true then 1 else 0) * (if y = true then (1 : ℕ) else 0) := by
  cases x <;> cases y <;> rfl

theorem ite_and_mul (x y : Bool) (f g : ℕ) :
    (if (x && y) = true then g * f else 0) = (if x = true then f else 0) * (if y = true then g else 0) := by
  cases x <;> cases y <;> simp [mul_comm]

theorem sum_row_split (P Q : Fin 4 × Fin 4 → Bool) (F G : Fin 4 × Fin 4 → ℕ) :
    ∑ t : Fin 4 → Fin 4, (if (P (t 0, t 2) && Q (t 1, t 3)) = true then G (t 1, t 3) * F (t 0, t 2) else 0) =
      (∑ w : Fin 4 × Fin 4, if P w = true then F w else 0) *
        ∑ w' : Fin 4 × Fin 4, if Q w' = true then G w' else 0 := by
  rw [sum_row, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun w' _ => ?_))
  exact ite_and_mul (P w) (Q w') (F w) (G w')

/-- The ways to finish one color class with m more rows, from the pair u of the row above and the
pair v of the current row; u holds columns 0 and 2 when b is true and columns 1 and 3 otherwise. -/
def K : ℕ → Bool → Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℕ
  | 0, true, u, v => if baseX u v = true then 1 else 0
  | 0, false, u, v => if baseY u v = true then 1 else 0
  | m + 1, true, u, v => ∑ w : Fin 4 × Fin 4, if stepX u v w = true then K m false v w else 0
  | m + 1, false, u, v => ∑ w : Fin 4 × Fin 4, if stepY u v w = true then K m true v w else 0

theorem KX (m : ℕ) (u v : Fin 4 × Fin 4) :
    K (m + 1) true u v = ∑ w : Fin 4 × Fin 4, if stepX u v w = true then K m false v w else 0 := rfl

theorem KY (m : ℕ) (u v : Fin 4 × Fin 4) :
    K (m + 1) false u v = ∑ w : Fin 4 × Fin 4, if stepY u v w = true then K m true v w else 0 := rfl

/-- The scan count is the product of the two class counts. -/
theorem N_eq (m : ℕ) : ∀ p c : Fin 4 → Fin 4,
    N (some p) c m = K m true (p 0, p 2) (c 1, c 3) * K m false (p 1, p 3) (c 0, c 2) := by
  induction m with
  | zero =>
    intro p c
    rw [N_zero, rowOK_sn]
    exact ite_and_one _ _
  | succ m ih =>
    intro p c
    rw [N_succ, KX, KY]
    simp only [rowOK_ss, ih]
    exact sum_row_split (stepX (p 0, p 2) (c 1, c 3)) (stepY (p 1, p 3) (c 0, c 2))
      (K m false (c 1, c 3)) (K m true (c 0, c 2))

/-- The index of a class state in the tables. -/
def idx (b : Bool) (u v : Fin 4 × Fin 4) : ℕ :=
  (if b then 0 else 256) + u.1.val * 64 + u.2.val * 16 + v.1.val * 4 + v.2.val

/-- The table of K 1: its value at a state is the base-16 digit of index `idx b u v`. -/
def t1 (b : Bool) (u v : Fin 4 × Fin 4) : ℕ :=
  127944125952726661392515866095850546089922561213373913214381421554275608287824209809405769709014533920555700847597744437090044394230652145847392942384150813687654117419218161686737123588172078577403145737974896599320751963373430044776446326137881907160563437992988119534827127635624798028009135280830267147816094071825513410894344855521634305680297607723568520401495178851179469026571769361362326768791702687541299118388457695689648494699815112327202904062603679877801816452576559606349590989436493654418124650979920413942922094708390050291945244323164792053740646770890100055395551970825228083821348002988032 / 16 ^ idx b u v % 16

/-- The table of K 2, as base-16 digits. -/
def t2 (b : Bool) (u v : Fin 4 × Fin 4) : ℕ :=
  127944125952726661399450137685856730267777570713557907462757582663314920282880102501187815190732844222592143549021576734393151524125110942391538384887397173369288977076952918186353616882679209932967437871900180571409518540175156416395795735013336835944857137777457841285252408863207141058639588215712680262542092448779497113266226920261162752998285987772120595992351451723327231094425755060033432830097915610288622831753805542823925275632239582660177717363632863842038858277303222890824774717555068510535804798028548654306732189435803278021119281216928542121218097218595924483890180346748325390799790877442048 / 16 ^ idx b u v % 16

/-- The table of K 3, as base-16 digits. -/
def t3 (b : Bool) (u v : Fin 4 × Fin 4) : ℕ :=
  255888251905453322791966003781707276357700131926931820677139004217590528570704312310593584899747378143147844396619321171483195918355763088238931327271547987056943094496171079873090740470851288510370583609875077170730270503548586461172242061151218743105420575770445960820079536498831939086648723496542947410358186520605010524160571775782797058678583595495689116393846630574506700120997524421395759598889618297829921950142263238513573770332054694987380621426236543719840674729879782497174365706991562164953929449008469068249654284144193328313064525540093334174958743989486024539285732317573553474621138880430080 / 16 ^ idx b u v % 16

lemma K1 (b : Bool) (u v : Fin 4 × Fin 4) : K 1 b u v = t1 b u v := by
  cases b
  · rw [KY]
    simp only [K]
    revert u v
    decide +kernel
  · rw [KX]
    simp only [K]
    revert u v
    decide +kernel

lemma K2 (b : Bool) (u v : Fin 4 × Fin 4) : K 2 b u v = t2 b u v := by
  cases b
  · rw [KY]
    simp only [K1]
    revert u v
    decide +kernel
  · rw [KX]
    simp only [K1]
    revert u v
    decide +kernel

lemma K3 (b : Bool) (u v : Fin 4 × Fin 4) : K 3 b u v = t3 b u v := by
  cases b
  · rw [KY]
    simp only [K2]
    revert u v
    decide +kernel
  · rw [KX]
    simp only [K2]
    revert u v
    decide +kernel

/-- The Fibonacci recurrence of the class counts, on every class state, from one row on. -/
theorem K_rec (m : ℕ) : ∀ b u v, K (m + 3) b u v = K (m + 2) b u v + K (m + 1) b u v := by
  induction m with
  | zero =>
    intro b u v
    rw [K3, K2, K1]
    revert b u v
    decide +kernel
  | succ m ih =>
    intro b u v
    cases b
    · rw [KY (m + 3), KY (m + 2), KY (m + 1), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      split_ifs
      · exact ih _ _ _
      · rfl
    · rw [KX (m + 3), KX (m + 2), KX (m + 1), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      split_ifs
      · exact ih _ _ _
      · rfl

/-- The number of valid n X 4 arrays. -/
def cnt (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 4 → Fin 4 => valid (List.ofFn x) = true).card

theorem a_eq (n : ℕ) : a n = cnt n / 4 := rfl

theorem cnt_succ (n : ℕ) : cnt (n + 1) = ∑ c : Fin 4 → Fin 4, N none c n := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold cnt
  rw [Finset.card_filter, h]
  rfl

theorem cnt_one : cnt 1 = 144 := by
  rw [cnt_succ]
  simp only [N_zero, rowOK_nn]
  rw [sum_row]
  simp only [mkRow_0, mkRow_1, mkRow_2, mkRow_3]
  decide +kernel

/-- The first color class, summed over its first two rows. -/
def SX (n : ℕ) : ℕ :=
  ∑ v : Fin 4 × Fin 4, ∑ w : Fin 4 × Fin 4, if baseX w v = true then K n false v w else 0

/-- The second color class, summed over its first two rows. -/
def SY (n : ℕ) : ℕ :=
  ∑ v : Fin 4 × Fin 4, ∑ w : Fin 4 × Fin 4, if baseY w v = true then K n true v w else 0

theorem cnt_add_two (n : ℕ) : cnt (n + 2) = SX n * SY n := by
  have h : ∀ c : Fin 4 → Fin 4, N none c (n + 1) =
      (∑ w : Fin 4 × Fin 4, if baseX w (c 1, c 3) = true then K n false (c 1, c 3) w else 0) *
        ∑ w' : Fin 4 × Fin 4, if baseY w' (c 0, c 2) = true then K n true (c 0, c 2) w' else 0 := by
    intro c
    rw [N_succ]
    simp only [rowOK_ns, N_eq]
    exact sum_row_split (fun w => baseX w (c 1, c 3)) (fun w' => baseY w' (c 0, c 2))
      (K n false (c 1, c 3)) (K n true (c 0, c 2))
  rw [cnt_succ]
  simp only [h]
  rw [sum_row]
  simp only [mkRow_02, mkRow_13]
  rw [SX, SY, Finset.sum_mul_sum]
  exact Finset.sum_comm

theorem SX_rec (n : ℕ) : SX (n + 3) = SX (n + 2) + SX (n + 1) := by
  unfold SX
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [K_rec]
  split_ifs <;> simp

theorem SY_rec (n : ℕ) : SY (n + 3) = SY (n + 2) + SY (n + 1) := by
  unfold SY
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [K_rec]
  split_ifs <;> simp

lemma SX_vals : SX 0 = 48 ∧ SX 1 = 72 ∧ SX 2 = 120 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SX]
    simp only [K]
    decide +kernel
  · rw [SX]
    simp only [K1]
    decide +kernel
  · rw [SX]
    simp only [K2]
    decide +kernel

lemma SY_vals : SY 0 = 48 ∧ SY 1 = 72 ∧ SY 2 = 120 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SY]
    simp only [K]
    decide +kernel
  · rw [SY]
    simp only [K1]
    decide +kernel
  · rw [SY]
    simp only [K2]
    decide +kernel

theorem SX_fib : ∀ n, SX n = 24 * Nat.fib (n + 3)
  | 0 => by rw [SX_vals.1]; rfl
  | 1 => by rw [SX_vals.2.1]; rfl
  | 2 => by rw [SX_vals.2.2]; rfl
  | n + 3 => by
    have h : Nat.fib (n + 3 + 3) = Nat.fib (n + 1 + 3) + Nat.fib (n + 2 + 3) := Nat.fib_add_two
    rw [SX_rec, SX_fib (n + 2), SX_fib (n + 1), h]
    ring

theorem SY_fib : ∀ n, SY n = 24 * Nat.fib (n + 3)
  | 0 => by rw [SY_vals.1]; rfl
  | 1 => by rw [SY_vals.2.1]; rfl
  | 2 => by rw [SY_vals.2.2]; rfl
  | n + 3 => by
    have h : Nat.fib (n + 3 + 3) = Nat.fib (n + 1 + 3) + Nat.fib (n + 2 + 3) := Nat.fib_add_two
    rw [SY_rec, SY_fib (n + 2), SY_fib (n + 1), h]
    ring

theorem a_one : a 1 = 36 := by
  rw [a_eq, cnt_one]

/-- Metcalfe's form, a(n) = (12 Fibonacci(n+1))^2 for n >= 2. -/
theorem a_fib (n : ℕ) : a (n + 2) = (12 * Nat.fib (n + 3)) ^ 2 := by
  rw [a_eq, cnt_add_two, SX_fib, SY_fib,
    show 24 * Nat.fib (n + 3) * (24 * Nat.fib (n + 3)) = 4 * (12 * Nat.fib (n + 3)) ^ 2 by ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

/-- a(n) = 2 a(n-1) + 2 a(n-2) - a(n-3), for n >= 5. -/
theorem a_rec (m : ℕ) : (a (m + 5) : ℤ) = 2 * a (m + 4) + 2 * a (m + 3) - a (m + 2) := by
  have h5 : a (m + 5) = (12 * Nat.fib (m + 6)) ^ 2 := a_fib (m + 3)
  have h4 : a (m + 4) = (12 * Nat.fib (m + 5)) ^ 2 := a_fib (m + 2)
  have h3 : a (m + 3) = (12 * Nat.fib (m + 4)) ^ 2 := a_fib (m + 1)
  have h2 : a (m + 2) = (12 * Nat.fib (m + 3)) ^ 2 := a_fib m
  have f6 : Nat.fib (m + 6) = Nat.fib (m + 4) + Nat.fib (m + 5) := Nat.fib_add_two
  have f5 : Nat.fib (m + 5) = Nat.fib (m + 3) + Nat.fib (m + 4) := Nat.fib_add_two
  rw [h5, h4, h3, h2, f6, f5]
  push_cast
  ring

/-- Barker's g.f., as A(x) (1 + x)(1 - 3x + x^2) = 36x(1 + 14x + 2x^2 - 3x^3) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 + X) * (1 - 3 * X + X ^ 2)) =
    36 * X * (1 + 14 * X + 2 * X ^ 2 - 3 * X ^ 3) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * ((1 + X) * (1 - 3 * X + X ^ 2)) = A - C 2 * (A * X ^ 1) - C 2 * (A * X ^ 2) + A * X ^ 3 := by
    simp only [map_ofNat]; ring
  have e2 : (36 * X * (1 + 14 * X + 2 * X ^ 2 - 3 * X ^ 3) : ℤ⟦X⟧) =
      X ^ 1 * C 36 + X ^ 2 * C 504 + X ^ 3 * C 72 - X ^ 4 * C 108 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v1 : a 1 = 36 := a_one
  have v2 : a 2 = 576 := (a_fib 0).trans (by norm_num)
  have v3 : a 3 = 1296 := (a_fib 1).trans (by norm_num)
  have v4 : a 4 = 3600 := (a_fib 2).trans (by norm_num)
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 5 := ⟨n - 5, by omega⟩
    simp only [show q + 5 - 1 = q + 4 by omega, show q + 5 - 2 = q + 3 by omega,
      show q + 5 - 3 = q + 2 by omega]
    simp only [show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0 by omega,
      show ¬ q + 2 = 0 by omega, show 1 ≤ q + 5 by omega, show 2 ≤ q + 5 by omega,
      show 3 ≤ q + 5 by omega, show ¬ q + 5 = 1 by omega, show ¬ q + 5 = 2 by omega,
      show ¬ q + 5 = 3 by omega, show ¬ q + 5 = 4 by omega, if_true, if_false]
    rw [a_rec q]
    ring

/-- Barker's closed form, for n > 1. -/
theorem closed (n : ℕ) (hn : 1 < n) : (a n : ℝ) = 9 / 5 * 2 ^ ((3 : ℤ) - n) *
    ((-1) ^ n * 2 ^ (2 + n) + (3 - Real.sqrt 5) ^ (1 + n) + (3 + Real.sqrt 5) ^ (1 + n)) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hZ1 : (2 : ℝ) ^ ((3 : ℤ) - n) * 2 ^ (1 + n) = 16 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      show (3 : ℤ) - n + ((1 + n : ℕ) : ℤ) = 4 by push_cast; ring]
    norm_num
  have hZ2 : (2 : ℝ) ^ ((3 : ℤ) - n) * 2 ^ (2 + n) = 32 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      show (3 : ℤ) - n + ((2 + n : ℕ) : ℤ) = 5 by push_cast; ring]
    norm_num
  have hp : (3 + Real.sqrt 5) ^ (1 + n) = 2 ^ (1 + n) * (Real.goldenRatio ^ (n + 1)) ^ 2 := by
    rw [show 3 + Real.sqrt 5 = 2 * Real.goldenRatio ^ 2 by
      rw [Real.goldenRatio_sq, Real.goldenRatio]; ring, mul_pow, ← pow_mul, ← pow_mul,
      show 2 * (1 + n) = (n + 1) * 2 by ring]
  have hq : (3 - Real.sqrt 5) ^ (1 + n) = 2 ^ (1 + n) * (Real.goldenConj ^ (n + 1)) ^ 2 := by
    rw [show 3 - Real.sqrt 5 = 2 * Real.goldenConj ^ 2 by
      rw [Real.goldenConj_sq, Real.goldenConj]; ring, mul_pow, ← pow_mul, ← pow_mul,
      show 2 * (1 + n) = (n + 1) * 2 by ring]
  have hpq : Real.goldenRatio ^ (n + 1) * Real.goldenConj ^ (n + 1) = -(-1) ^ n := by
    rw [← mul_pow, Real.goldenRatio_mul_goldenConj, pow_succ]
    ring
  have hf : (a n : ℝ) = 144 * ((Real.goldenRatio ^ (n + 1) - Real.goldenConj ^ (n + 1)) ^ 2 / 5) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [a_fib k]
    push_cast
    rw [Real.coe_fib_eq, mul_pow, div_pow, h5]
    ring
  rw [hf, hp, hq]
  linear_combination (-9 / 5 * ((Real.goldenRatio ^ (n + 1)) ^ 2 + (Real.goldenConj ^ (n + 1)) ^ 2)) * hZ1 +
    (-9 / 5 * (-1) ^ n) * hZ2 + (-288 / 5) * hpq

/-- Controls: the entry's data a(1..24). -/
theorem controls : a 1 = 36 ∧ a 2 = 576 ∧ a 3 = 1296 ∧ a 4 = 3600 ∧ a 5 = 9216 ∧ a 6 = 24336 ∧
    a 7 = 63504 ∧ a 8 = 166464 ∧ a 9 = 435600 ∧ a 10 = 1140624 ∧ a 11 = 2985984 ∧ a 12 = 7817616 ∧
    a 13 = 20466576 ∧ a 14 = 53582400 ∧ a 15 = 140280336 ∧ a 16 = 367258896 ∧ a 17 = 961496064 ∧
    a 18 = 2517229584 ∧ a 19 = 6590192400 ∧ a 20 = 17253347904 ∧ a 21 = 45169851024 ∧
    a 22 = 118256205456 ∧ a 23 = 309598765056 ∧ a 24 = 810540090000 :=
  ⟨a_one,
    (a_fib 0).trans (by norm_num),
    (a_fib 1).trans (by norm_num),
    (a_fib 2).trans (by norm_num),
    (a_fib 3).trans (by norm_num),
    (a_fib 4).trans (by norm_num),
    (a_fib 5).trans (by norm_num),
    (a_fib 6).trans (by norm_num),
    (a_fib 7).trans (by norm_num),
    (a_fib 8).trans (by norm_num),
    (a_fib 9).trans (by norm_num),
    (a_fib 10).trans (by norm_num),
    (a_fib 11).trans (by norm_num),
    (a_fib 12).trans (by norm_num),
    (a_fib 13).trans (by norm_num),
    (a_fib 14).trans (by norm_num),
    (a_fib 15).trans (by norm_num),
    (a_fib 16).trans (by norm_num),
    (a_fib 17).trans (by norm_num),
    (a_fib 18).trans (by norm_num),
    (a_fib 19).trans (by norm_num),
    (a_fib 20).trans (by norm_num),
    (a_fib 21).trans (by norm_num),
    (a_fib 22).trans (by norm_num)⟩

/-- All three conjectures: Barker's g.f. and closed form, and Metcalfe's Fibonacci form. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 + X) * (1 - 3 * X + X ^ 2)) =
      36 * X * (1 + 14 * X + 2 * X ^ 2 - 3 * X ^ 3) ∧
    (∀ n : ℕ, 1 < n → (a n : ℝ) = 9 / 5 * 2 ^ ((3 : ℤ) - n) *
      ((-1) ^ n * 2 ^ (2 + n) + (3 - Real.sqrt 5) ^ (1 + n) + (3 + Real.sqrt 5) ^ (1 + n))) ∧
    ∀ n : ℕ, 1 < n → a n = (12 * Nat.fib (n + 1)) ^ 2 :=
  ⟨gf, closed, fun n hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    exact a_fib k⟩

end OMA.S_oeis_a183356

theorem OMA.solution : type_of% @OMA.S_oeis_a183356.main :=
  OMA.S_oeis_a183356.conjecture
