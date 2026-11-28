import OMAStatements.S_oeis_a312411

namespace OMA.S_oeis_a312411






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 6

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 581824977305
  | 1 => 586406201480
  | 2 => 513409652855
  | 3 => 664287016551
  | 4 => 733005375096
  | 5 => 659705788280
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 10) : ℤ := tget 444691290230 4 8 i.val

def Bc (i : Fin 10) : ℤ := tget 810869408855 4 8 i.val

def Cc (s : Fin 6) (i : Fin 10) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 444691290230 4 i

def BcN (i : ℕ) : ℕ := tgetN 810869408855 4 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem Ac_eq (i : Fin 10) : Ac i = (AcN i.val : ℤ) - 8 := rfl

theorem Bc_eq (i : Fin 10) : Bc i = (BcN i.val : ℤ) - 8 := rfl

theorem Cc_eq (s : Fin 6) (i : Fin 10) : Cc s i = (CcN s.val i.val : ℤ) - 8 := rfl


/-- The potential of facet i at v (facets in angular order around the growth polygon). -/
def pot (v : V) (i : Fin 10) : ℤ := Ac i * v.1 + Bc i * v.2.1 + Cc v.2.2 i

/-- The largest facet potential at v. -/
def F (v : V) : ℤ := max (max (max (max (max (max (max (max (max (pot v 0) (pot v 1)) (pot v 2)) (pot v 3)) (pot v 4)) (pot v 5)) (pot v 6)) (pot v 7)) (pot v 8)) (pot v 9)

theorem le_F0 (v : V) : pot v 0 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))))))))
theorem le_F1 (v : V) : pot v 1 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))))
theorem le_F2 (v : V) : pot v 2 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))))
theorem le_F3 (v : V) : pot v 3 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))
theorem le_F4 (v : V) : pot v 4 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))
theorem le_F5 (v : V) : pot v 5 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))
theorem le_F6 (v : V) : pot v 6 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
theorem le_F7 (v : V) : pot v 7 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
theorem le_F8 (v : V) : pot v 8 ≤ F v := le_max_of_le_left (le_max_right _ _)
theorem le_F9 (v : V) : pot v 9 ≤ F v := le_max_right _ _

theorem le_F (v : V) (i : Fin 10) : pot v i ≤ F v := by
  fin_cases i
  exacts [le_F0 v, le_F1 v, le_F2 v, le_F3 v, le_F4 v, le_F5 v, le_F6 v, le_F7 v, le_F8 v, le_F9 v]

theorem F_le (v : V) (t : ℤ) (h0 : pot v 0 ≤ t) (h1 : pot v 1 ≤ t) (h2 : pot v 2 ≤ t) (h3 : pot v 3 ≤ t) (h4 : pot v 4 ≤ t) (h5 : pot v 5 ≤ t) (h6 : pot v 6 ≤ t) (h7 : pot v 7 ≤ t) (h8 : pot v 8 ≤ t) (h9 : pot v 9 ≤ t) : F v ≤ t :=
  max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9

theorem F_le_all (v : V) (t : ℤ) (h : ∀ i, pot v i ≤ t) : F v ≤ t :=
  F_le v t (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9)

theorem max_ex {v : V} {a b : ℤ} (ha : ∃ i, a = pot v i) (hb : ∃ i, b = pot v i) :
    ∃ i, max a b = pot v i := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

theorem exists_F (v : V) : ∃ i, F v = pot v i :=
  max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (⟨0, rfl⟩) ⟨1, rfl⟩) ⟨2, rfl⟩) ⟨3, rfl⟩) ⟨4, rfl⟩) ⟨5, rfl⟩) ⟨6, rfl⟩) ⟨7, rfl⟩) ⟨8, rfl⟩) ⟨9, rfl⟩

/-- A statement about every vertex class follows from the statements about each class. -/
theorem cls (P : Fin 6 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 6 × Fin 6 × ℤ × ℤ) (j : Fin 10) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 10, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 6 × Fin 6 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 6 × Fin 6 × ℤ × ℤ) (j : Fin 10) :
    pot (x + e.2.2.1, y + e.2.2.2, e.2.1) j = pot (x, y, e.1) j + dl e j := by
  simp only [pot, dl]
  ring

theorem lip (u w : V) (h : G.Adj u w) : F w ≤ F u + 1 := by
  rw [G, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · obtain ⟨e, he, h1, h2, h3, h4⟩ := h
    obtain ⟨x, y, s⟩ := u
    obtain ⟨x', y', s'⟩ := w
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    apply F_le_all
    intro j
    have hs := (E_step e he j).1
    have hu := le_F (x, y, e.1) j
    rw [shift x y e j]
    omega
  · obtain ⟨e, he, h1, h2, h3, h4⟩ := h
    obtain ⟨x, y, s⟩ := w
    obtain ⟨x', y', s'⟩ := u
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    apply F_le_all
    intro j
    have hs := (E_step e he j).2
    have hu := le_F (x + e.2.2.1, y + e.2.2.2, e.2.1) j
    rw [shift x y e j] at hu
    omega

theorem step_down (v w : V) (hadj : G.Adj v w) (h : ∀ j, pot w j ≤ F v - 1) : F w + 1 = F v := by
  have hw := F_le_all w (F v - 1) h
  have hl := lip w v hadj.symm
  omega

theorem pair_of {a f b : ℤ} (hl : a ≤ f) (hf : f = b) : a ≤ b + 0 := by omega

theorem bound_of {r f b : ℤ} (hr : r < f) (hf : f = b) : r + 1 ≤ b := by omega

theorem not_pair2 {a b : ℤ} (h : ¬ a ≤ b + (-2)) : b ≤ a + 1 := by omega

/-- Three facts pot a_k ≤ pot b_k + t_k and a bound r ≤ pot i0 at (x, y, s), with multipliers
whose x and y parts cancel and whose constants add up to a positive number, cannot hold together. -/
theorem farkas (x y : ℤ) (s : Fin 6) (a1 b1 a2 b2 a3 b3 i0 : Fin 10) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
    (hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ 0 ≤ l0 ∧
      l1 * (Ac a1 - Ac b1) + l2 * (Ac a2 - Ac b2) + l3 * (Ac a3 - Ac b3) - l0 * Ac i0 = 0 ∧
      l1 * (Bc a1 - Bc b1) + l2 * (Bc a2 - Bc b2) + l3 * (Bc a3 - Bc b3) - l0 * Bc i0 = 0 ∧
      0 < l1 * (Cc s a1 - Cc s b1 - t1) + l2 * (Cc s a2 - Cc s b2 - t2) +
        l3 * (Cc s a3 - Cc s b3 - t3) + l0 * (r - Cc s i0))
    (h1 : pot (x, y, s) a1 ≤ pot (x, y, s) b1 + t1) (h2 : pot (x, y, s) a2 ≤ pot (x, y, s) b2 + t2)
    (h3 : pot (x, y, s) a3 ≤ pot (x, y, s) b3 + t3) (h0 : r ≤ pot (x, y, s) i0) : False := by
  obtain ⟨hl1, hl2, hl3, hl0, hx, hy, hk⟩ := hc
  have e1 := mul_le_mul_of_nonneg_left h1 hl1
  have e2 := mul_le_mul_of_nonneg_left h2 hl2
  have e3 := mul_le_mul_of_nonneg_left h3 hl3
  have e0 := mul_le_mul_of_nonneg_left h0 hl0
  have hx' : (l1 * (Ac a1 - Ac b1) + l2 * (Ac a2 - Ac b2) + l3 * (Ac a3 - Ac b3) - l0 * Ac i0) * x = 0 := by
    rw [hx, zero_mul]
  have hy' : (l1 * (Bc a1 - Bc b1) + l2 * (Bc a2 - Bc b2) + l3 * (Bc a3 - Bc b3) - l0 * Bc i0) * y = 0 := by
    rw [hy, zero_mul]
  simp only [pot] at e1 e2 e3 e0
  nlinarith [e1, e2, e3, e0, hx', hy', hk]

/-- Certificates of the far facts, the same for every class: for maximal facet i and a facet j not
adjacent to i, the fields k1, k2, m1, m2, m0, mj of entry i * 10 + j give the facts pot k1 ≤ pot i,
pot k2 ≤ pot i, 10 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 333407090671613998201189341454954710626743700364528543090296173654894459737459673467140510403821291825583449496365483857512339889115673809353256097664522043554107631164373530703422096691682309691717536300339710393525298435616080521817019426483367316348224358349671980944157073427927225839694063268054284383246667827332680742215889756157854835768337505789422578633046026867805066211228599723516280990653076653513229755182443880693600228668035355580745348062685560107690481640039121388659052841615326196484182743138996942639128669522810049450095110028304828634953614110769764560580488886109401869517349409881539582419012430870131793858575950903178833171468601772000853578010320470852023760411157562104695750656 4 ((i * 10 + j) * 6 + f)

def fd (i j : Fin 10) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 10) : Fin 10 := ⟨fdN i.val j.val 0 % 10, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 10) : Fin 10 := ⟨fdN i.val j.val 1 % 10, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 10) : ℤ := fd i j 2

def fm2 (i j : Fin 10) : ℤ := fd i j 3

def fm0 (i j : Fin 10) : ℤ := fd i j 4

def fmj (i j : Fin 10) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 10 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 3372954173042843750400 3 p

def dstv (p : ℕ) : ℕ := tgetN 2602925406190240860369 3 p

def dxv (p : ℕ) : ℕ := tgetN 89410056376641 2 p

def dyv (p : ℕ) : ℕ := tgetN 93829303981317 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 5847177873954868509406260795420009397659392366130455449059785180295707063510034283737214556925966604228049583266898977765950680450670314429935828370007886817346179907160298440618743146833076186215689454440270395215887604909264401760771869304364010604810713244886909862037679864324082399095 4 (p * 10 + j)

def dlv (p : ℕ) (j : Fin 10) : ℤ := (dlvN p j.val : ℤ) - 8

theorem dlv_neg (p : ℕ) (j : Fin 10) (h : dlvN p j.val + 1 ≤ 8) : dlv p j ≤ -1 := by
  unfold dlv
  omega

theorem dlv_le (p : ℕ) (j : Fin 10) (c : ℕ) (h : dlvN p j.val + 1 ≤ c + 8) : dlv p j ≤ (c : ℤ) - 1 := by
  unfold dlv
  omega

/-- The next and the previous facet around the growth polygon. -/
def nxt (i : Fin 10) : Fin 10 := ⟨(i.val + 1) % 10, Nat.mod_lt _ (by norm_num)⟩

def prv (i : Fin 10) : Fin 10 := ⟨(i.val + 9) % 10, Nat.mod_lt _ (by norm_num)⟩

/-- The facets i and j are not equal and not adjacent sides of the growth polygon. -/
def nonadj (i j : Fin 10) : Prop := j ≠ i ∧ j ≠ nxt i ∧ j ≠ prv i

instance : DecidableRel nonadj := fun i j => by unfold nonadj; infer_instance

/-- The x and y parts of the far certificate of (i, j) cancel, in natural numbers (Ac = AcN - 8). -/
def farXYN (i j : ℕ) : Bool :=
  (fdN i j 2 * AcN (fdN i j 0 % 10) + fdN i j 3 * AcN (fdN i j 1 % 10) + fdN i j 5 * AcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * AcN i + fdN i j 5 * AcN j) &&
    (fdN i j 2 * BcN (fdN i j 0 % 10) + fdN i j 3 * BcN (fdN i j 1 % 10) + fdN i j 5 * BcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * BcN i + fdN i j 5 * BcN j)

/-- The constants of the far certificate of (i, j) at class s add up to a positive number. -/
def farCN (s i j : ℕ) : Bool :=
  Nat.blt ((fdN i j 2 + fdN i j 3 + fdN i j 4) * CcN s i + fdN i j 5 * (CcN s j + 1))
    (fdN i j 2 * CcN s (fdN i j 0 % 10) + fdN i j 3 * CcN s (fdN i j 1 % 10) + fdN i j 5 * CcN s i +
      fdN i j 4 * 18)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 10 || j == (i + 9) % 10

def farOK : Bool := (List.range 10).all fun i => (List.range 10).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 6).all fun s => (List.range 10).all fun i => (List.range 10).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 24).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 10).all fun j =>
      dlvN p j + 1 * AcN j + 8 * dxv p + 1 * BcN j + 8 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 16 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 6) (i j : Fin 10) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (10 - Cc s i)

/-- Beyond F = 9, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 6) (i j : Fin 10) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 9 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 10 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
    (pair_of (le_F _ _) h) (pair_of (le_F _ _) h) (not_pair2 hc') (bound_of hF h)

/-- The slack class of a slack d ≥ 0: 2 when d ≥ 2, else d. -/
def scl (d : ℤ) : Fin 3 := if 2 ≤ d then 2 else if d = 1 then 1 else 0

theorem scl_le (d : ℤ) (hd : 0 ≤ d) : ((scl d).val : ℤ) ≤ d := by
  have e2 : ((2 : Fin 3).val : ℤ) = 2 := rfl
  have e1 : ((1 : Fin 3).val : ℤ) = 1 := rfl
  have e0 : ((0 : Fin 3).val : ℤ) = 0 := rfl
  unfold scl
  split_ifs <;> omega

theorem scl_eq (d : ℤ) (hd : 0 ≤ d) (h1 : (scl d).val ≤ 1) : d = (scl d).val := by
  have e2 : (2 : Fin 3).val = 2 := rfl
  have e1 : (1 : Fin 3).val = 1 := rfl
  have e0 : (0 : Fin 3).val = 0 := rfl
  unfold scl at *
  split_ifs at * <;> omega

/-- Descent rules beyond F = 9, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 9 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 1104066881332505424277018609368810469488388442090207096330152997637837592555349822016343742371823571800656583763170618859519361515492103043338211665172310099985341003749529571247971166177385775441266369450319891651825421322761028328706039072899127914923116685513409191582254750266791725266090400347809967833399383838615282284630036484786026005696858499338099397862448592427328265105620240610507167883704498433078150253133584211272337152524516155704309263112828718556444898166473583961820170261247344562354004021008186153076828315511637521836781856670508644020316851888467039972728687639653154161644717086532299968247978757962739645653684047323581104854910487331382036945156455469865996389964590132946970586509061543780761801977000559707569926812434798990865672181608537197783860797503469390908428396860731870321189850961463886603913433719684131379900222732588228195893936867923131519453945850144196206642688469153792939835628705458116852118995191246508292845374148690878826529
  | 1 => 1104066887405562127799829804201323081965582240533811838635903469693371167343111095367923390634973102794441006660866558756429495662292827876095946347115338968271717337887700576537617722207328483500221447961428853943110628832155486549291586019431972859538759774420985308803968938898273285605682277367551281187819027310657117848600571287305255601705643237100554107456092897569017373718568503017741724075712816184458855488808867936551193964559710930787604325592551431076515085167234348701031093017229237425165094858287731788516911489182068949025067197709832382629455840730872941629293130824738328452014638817895640601942101974445130668728804440661337311115016074829680993197235170642193309777326217895594890814951428181463408854797008093332001292065875315496509260912089711327242629906121537215750775873727507038574763336313174433725561772860032979301605881279489296288655487584099593839590492906845033957340702185375667517928846709817876004879648281658648098301253049994065349024
  | 2 => 1104066891454266596815037267422998156950378106162881666839737117731253544980693955836486749543637012547052931453965145799064338091710402552771041201414149592417474905544347015751691734712891750112309487216213524630513507157238178763673043693705276447363913998372935724024709156257390195105945876792052477894288196707152894999507998547567343248765332568182179686028754821171637859285391195159962605138182946689960409991262200973854469793516577220907240436050748299063464349992596601496087023532752928687843838507126969674613976629036572126403404656852237282068107426488342572136418619268667631552985202583334898342841869680281688683296499278818733183925553802322325701554594914520881873361036095366746010822125976094850314841106041297811412190586153142392697742892254586131525758968734517316463949529530150756093851067164527383216883284554798193370479647885524276260038298428709557257426479512233035112106804266766585424570315396664856554948691018257506232553757078722113341473
  | 3 => 1104066903600380003860659657088023381904765703050091151451238061844900677739663546969799382711363114472577032402504765563701268422776367771554732987406333753908497006291490454832704091931496920129960516052805037975933815462319260983905584551910897541495375097124735772424458891539426279718619051766529962744680643309025141506920751842204052673562809905096922070861097710401102822301192469216537206971296211087034885001819939664623455184151789967209163039826320592039125225848609180947603938252422044222285235496367854826473455043625244088594287325066119090737708954770683632922034760740483572605247591807206891775824115450271517365990152335903286172558769650322568892666568706069683844287638701346672797090569531214129352668547040502410762539865003612648963394519270871386667596693236940393687211790745822886907089388632473537083431438903834650115993041797641917935470218007886724748551639857158460458374909960282517604020340701456424791902794218190225013251399453027597715489
  | 4 => 1104066911697788941891074583531802205134220147326873408387102634569535781057594886181642248000668290013743228666570526672859021221862233657648672305406064141803808110148218451491993494131746357329172576334849693796149833883488675755150936317742829618847977485867123547811794672883514289942573503069800835969578563249884408578446328108452717213024269496363095322380624195383448718510200806109376658551724460551991812723581146837155623820159306905533451738806867782739300313006524937972686515062727023304713769573373687794313688287245254750311293782437798713292986192800138680796967159386202789023590499460187190275317490159225950870126378651893516942681402383350962718010226210497225134433979395583157112714561114252890936236797983492398184057407691607385433450014780671579784904087209671614642691215480896021668835013121344476772155631410279918323125880429191878797425607923488750437252741982892538269335135826719128048646919530574174410921147660638037572325087595315696110752
  | 5 => 1104066915746493410906282046753048606859153299937300636062739005959837801821243427341528195397218626895351861661691940167763630377805828079018246602221896977948312162595566391737290671200154181130715631612409953363027607513554331751194234058481539737104984321551245074091041415015047853238401916368224080486972309142029551016999937401262873096077236445672335013416852301281645993275607263802095693453147971965088303998880122449867835128736140904801412348172314405278312170164645369802919635458774067839197987131889414710072642631299045071530550887946397703491921505628239115626251914201547368418323200278447679244714408198523286511940555420595522439335358321457164182385355810233363492984118842454508109714535652320532459214356308039903163479912963838021984841567390031923441178356242370482294735308786654465836985275345359994780310661152420098116493608798828490678657171909446748437984579777996318133663746264207846935936032993229346335223615253894362771156511350910195501089
  | _ => 0

def rd (s : Fin 6) (i : Fin 10) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 6 32 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 6) (i : Fin 10) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 6) (i : Fin 10) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 6) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 6) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 6) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 6) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 6) (i : Fin 10) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 24 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 9)
  else if rk s i c1 c2 = 2 then
    decide (c1.val ≤ 1 ∧ rg s i c1 c2 ∣ Ac i - Ac (nxt i) ∧ rg s i c1 c2 ∣ Bc i - Bc (nxt i) ∧
      ¬ rg s i c1 c2 ∣ (c1.val : ℤ) - (Cc s i - Cc s (nxt i)))
  else if rk s i c1 c2 = 3 then
    decide (c2.val ≤ 1 ∧ rg s i c1 c2 ∣ Ac i - Ac (prv i) ∧ rg s i c1 c2 ∣ Bc i - Bc (prv i) ∧
      ¬ rg s i c1 c2 ∣ (c2.val : ℤ) - (Cc s i - Cc s (prv i)))
  else false

/-- All the tables: the far certificates for non-adjacent facets, the edge tables and the descent
rules. -/
theorem tables_ok : farOK = true ∧ farCOK = true ∧ dlOK = true ∧ (∀ s i c1 c2, ruleOK s i c1 c2 = true) := by
  decide +kernel

/-- The far certificates hold in the integers: the natural-number checks moved across. -/
theorem far_cert (s : Fin 6) (i j : Fin 10) (hij : nonadj i j) : farCert s i j := by
  have hn : nearB i.val j.val = false := by
    obtain ⟨h1, h2, h3⟩ := hij
    have e1 : j.val ≠ i.val := fun h => h1 (Fin.ext h)
    have e2 : j.val ≠ (i.val + 1) % 10 := fun h => h2 (Fin.ext h)
    have e3 : j.val ≠ (i.val + 9) % 10 := fun h => h3 (Fin.ext h)
    simp only [nearB, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨e1, e2⟩, e3⟩
  have hxy := tables_ok.1
  have hc := tables_ok.2.1
  unfold farOK at hxy
  unfold farCOK at hc
  simp only [List.all_eq_true, List.mem_range] at hxy hc
  have hx := hxy i.val i.isLt j.val j.isLt
  have hk := hc s.val s.isLt i.val i.isLt j.val j.isLt
  rw [hn, Bool.false_or] at hx hk
  simp only [farXYN, Bool.and_eq_true, beq_iff_eq] at hx
  simp only [farCN, Nat.blt_eq] at hk
  obtain ⟨hA, hB⟩ := hx
  have cA := congrArg (Nat.cast : ℕ → ℤ) hA
  have cB := congrArg (Nat.cast : ℕ → ℤ) hB
  have ck := (Nat.cast_lt (α := ℤ)).mpr hk
  push_cast at cA cB ck
  simp only [farCert, fm1, fm2, fmj, fm0, fd, Ac_eq, Bc_eq, Cc_eq, fk1, fk2]
  refine ⟨by positivity, by positivity, by positivity, by positivity, by linear_combination cA,
    by linear_combination cB, ?_⟩
  ring_nf at ck ⊢
  linarith

theorem edge_at (p : ℕ) (hp : p < 24) :
    srcv p = (E.getD p (0, 0, 0, 0)).1.val ∧ ∀ j, dlv p j = dl (E.getD p (0, 0, 0, 0)) j := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h p hp
  refine ⟨h1.symm, fun j => ?_⟩
  have hN := congrArg (Nat.cast : ℕ → ℤ) (h5 j.val j.isLt)
  push_cast at hN
  generalize E.getD p (0, 0, 0, 0) = e at h1 h2 h3 h4 ⊢
  obtain ⟨s1, s2, dx, dy⟩ := e
  simp only at h1 h2 h3 h4
  have ex : dx = (dxv p : ℤ) - 1 := by omega
  have ey : dy = (dyv p : ℤ) - 1 := by omega
  subst ex ey
  simp only [dlv, dl, Ac_eq, Bc_eq, Cc_eq, h1, h2]
  linear_combination hN

theorem point_contra (x y : ℤ) (s : Fin 6) (i : Fin 10) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 9)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 9 < pot (x, y, s) i) : False := by
  have m1 : u1 * (pot (x, y, s) i - pot (x, y, s) (nxt i)) = u1 * c1 := by rw [e1]
  have m2 : u2 * (pot (x, y, s) i - pot (x, y, s) (prv i)) = u2 * c2 := by rw [e2]
  have key := mul_lt_mul_of_pos_left hF hu0
  have ha' : (u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i))) * x = u0 * Ac i * x := by rw [ha]
  have hb' : (u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i))) * y = u0 * Bc i * y := by rw [hb]
  simp only [pot] at m1 m2 key
  nlinarith [ha', hb', m1, m2, key, hc]

theorem dvd_contra (x y : ℤ) (a b c g : ℤ) (ha : g ∣ a) (hb : g ∣ b) (hc : ¬ g ∣ c) (e : a * x + b * y = c) :
    False :=
  hc (e ▸ dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hb y))

/-- Beyond F = 9 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 6) (i : Fin 10) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 9 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
  have p1 : 0 ≤ pot (x, y, s) i - pot (x, y, s) (nxt i) := by have := le_F (x, y, s) (nxt i); omega
  have p2 : 0 ≤ pot (x, y, s) i - pot (x, y, s) (prv i) := by have := le_F (x, y, s) (prv i); omega
  have hv := tables_ok.2.2.2 s i (scl (pot (x, y, s) i - pot (x, y, s) (nxt i)))
    (scl (pot (x, y, s) i - pot (x, y, s) (prv i)))
  have q1 := scl_le _ p1
  have q2 := scl_le _ p2
  unfold ruleOK at hv
  split_ifs at hv with k0 k1 k2 k3
  · -- an edge that descends
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hlen, hsrc, hdi, hdn, hdp⟩ := hv
    have hdi := dlv_neg _ _ hdi
    have hdn := dlv_le _ _ _ hdn
    have hdp := dlv_le _ _ _ hdp
    obtain ⟨hs0, hdl⟩ := edge_at _ hlen
    have hmem : E.getD (re s i (scl (pot (x, y, s) i - pot (x, y, s) (nxt i)))
        (scl (pot (x, y, s) i - pot (x, y, s) (prv i)))) (0, 0, 0, 0) ∈ E := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    rw [hdl] at hdi hdn hdp
    rw [hs0] at hsrc
    generalize E.getD (re s i (scl (pot (x, y, s) i - pot (x, y, s) (nxt i)))
        (scl (pot (x, y, s) i - pot (x, y, s) (prv i)))) (0, 0, 0, 0) = e at hmem hsrc hdi hdn hdp
    have hs : e.1 = s := Fin.ext hsrc
    have ha := adj_of_mem e hmem x y
    rw [hs] at ha
    refine ⟨_, ha, step_down _ _ ha (fun j => ?_)⟩
    have hsh := shift x y e j
    rw [hs] at hsh
    rw [hsh]
    have hst := (E_step e hmem j).1
    have hj := le_F (x, y, s) j
    by_cases hji : j = i
    · subst hji
      omega
    by_cases hjn : j = nxt i
    · subst hjn
      omega
    by_cases hjp : j = prv i
    · subst hjp
      omega
    have hna : nonadj i j := ⟨hji, hjn, hjp⟩
    have := far s i j (far_cert s i j hna) x y h hF
    omega
  · -- a corner point within F ≤ 9
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hc1, hc2, hu0, ha, hb, hc⟩ := hv
    exact (point_contra x y s i _ _ _ _ _ hu0 ha hb hc (scl_eq _ p1 hc1) (scl_eq _ p2 hc2) (h ▸ hF)).elim
  · -- the line of the next facet has no lattice point
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hc1, ha, hb, hc⟩ := hv
    have e1 := scl_eq _ p1 hc1
    generalize scl (pot (x, y, s) i - pot (x, y, s) (nxt i)) = c at e1 ha hb hc
    simp only [pot] at e1
    exact (dvd_contra x y _ _ _ _ ha hb hc (by linear_combination e1)).elim
  · -- the line of the previous facet has no lattice point
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hc2, ha, hb, hc⟩ := hv
    have e2 := scl_eq _ p2 hc2
    generalize scl (pot (x, y, s) i - pot (x, y, s) (prv i)) = c at e2 ha hb hc
    simp only [pot] at e2
    exact (dvd_contra x y _ _ _ _ ha hb hc (by linear_combination e2)).elim

theorem far_desc (v : V) (hF : 9 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 6) (a1 a2 a3 : Fin 10) (t l1 l2 l3 px py q lq : ℤ)
    (hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ 0 ≤ lq ∧
      l1 * Ac a1 + l2 * Ac a2 + l3 * Ac a3 + lq * px = 0 ∧
      l1 * Bc a1 + l2 * Bc a2 + l3 * Bc a3 + lq * py = 0 ∧
      0 < l1 * (Cc s a1 - t) + l2 * (Cc s a2 - t) + l3 * (Cc s a3 - t) + lq * q)
    (h1 : pot (x, y, s) a1 ≤ t) (h2 : pot (x, y, s) a2 ≤ t) (h3 : pot (x, y, s) a3 ≤ t)
    (h4 : px * x + py * y + q ≤ 0) : False := by
  obtain ⟨hl1, hl2, hl3, hlq, hx, hy, hk⟩ := hc
  have e1 := mul_le_mul_of_nonneg_left h1 hl1
  have e2 := mul_le_mul_of_nonneg_left h2 hl2
  have e3 := mul_le_mul_of_nonneg_left h3 hl3
  have e4 := mul_le_mul_of_nonneg_left h4 hlq
  have hx' : (l1 * Ac a1 + l2 * Ac a2 + l3 * Ac a3 + lq * px) * x = 0 := by rw [hx, zero_mul]
  have hy' : (l1 * Bc a1 + l2 * Bc a2 + l3 * Bc a3 + lq * py) * y = 0 := by rw [hy, zero_mul]
  simp only [pot] at e1 e2 e3
  nlinarith [e1, e2, e3, e4, hx', hy', hk]

theorem near_box0 (x y : ℤ) (hF : F (x, y, 0) ≤ 9) : -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 0) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 0 1 9 0 9 3 3 0 1 0 6 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 4 5 0 9 1 3 0 (-1) 0 6 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 2 0 0 9 1 0 0 0 1 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 7 0 0 9 1 0 0 0 (-1) 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg0 (x y : ℤ) : 0 ≤ F (x, y, 0) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 0) k).trans (show F (x, y, 0) ≤ -1 by omega)
  exact farkas_ub x y 0 4 9 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box1 (x y : ℤ) (hF : F (x, y, 1) ≤ 9) : -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 1) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 1 0 9 0 9 3 1 0 1 0 6 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 4 5 0 9 1 3 0 (-1) 0 6 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 2 0 0 9 1 0 0 0 1 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 7 0 0 9 1 0 0 0 (-1) 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg1 (x y : ℤ) : 0 ≤ F (x, y, 1) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 1) k).trans (show F (x, y, 1) ≤ -1 by omega)
  exact farkas_ub x y 1 4 9 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box2 (x y : ℤ) (hF : F (x, y, 2) ≤ 9) : -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 2) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 2 0 9 0 9 3 1 0 1 0 6 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 4 6 0 9 3 3 0 (-1) 0 6 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 2 0 0 9 1 0 0 0 1 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 7 0 0 9 1 0 0 0 (-1) 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg2 (x y : ℤ) : 0 ≤ F (x, y, 2) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 2) k).trans (show F (x, y, 2) ≤ -1 by omega)
  exact farkas_ub x y 2 4 9 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box3 (x y : ℤ) (hF : F (x, y, 3) ≤ 9) : -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 3) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 3 0 9 0 9 3 1 0 1 0 6 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 4 6 0 9 3 3 0 (-1) 0 6 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 2 0 0 9 1 0 0 0 1 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 7 0 0 9 1 0 0 0 (-1) 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg3 (x y : ℤ) : 0 ≤ F (x, y, 3) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 3) k).trans (show F (x, y, 3) ≤ -1 by omega)
  exact farkas_ub x y 3 4 9 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box4 (x y : ℤ) (hF : F (x, y, 4) ≤ 9) : -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 4) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 4 1 9 0 9 3 3 0 1 0 6 9 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 4 5 0 9 1 3 0 (-1) 0 6 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 2 0 0 9 1 0 0 0 1 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 7 0 0 9 1 0 0 0 (-1) 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg4 (x y : ℤ) : 0 ≤ F (x, y, 4) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 4) k).trans (show F (x, y, 4) ≤ -1 by omega)
  exact farkas_ub x y 4 4 9 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box5 (x y : ℤ) (hF : F (x, y, 5) ≤ 9) : -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, 5) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 5 0 9 0 9 3 1 0 1 0 6 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 4 5 0 9 1 3 0 (-1) 0 6 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 2 0 0 9 1 0 0 0 1 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 7 0 0 9 1 0 0 0 (-1) 3 4 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg5 (x y : ℤ) : 0 ≤ F (x, y, 5) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 5) k).trans (show F (x, y, 5) ≤ -1 by omega)
  exact farkas_ub x y 5 4 9 0 (-1) 2 2 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

/-- Every vertex with F at most 9 lies in the cells |x| ≤ 5, |y| ≤ 2. -/
theorem near_box (x y : ℤ) (s : Fin 6) (hF : F (x, y, s) ≤ 9) :
    -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 :=
  cls (fun s => F (x, y, s) ≤ 9 → -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2)
    (near_box0 x y) (near_box1 x y) (near_box2 x y) (near_box3 x y) (near_box4 x y) (near_box5 x y) s hF

theorem F_nonneg (v : V) : 0 ≤ F v :=
  cls (fun s => 0 ≤ F (v.1, v.2.1, s)) (F_nonneg0 v.1 v.2.1) (F_nonneg1 v.1 v.2.1) (F_nonneg2 v.1 v.2.1) (F_nonneg3 v.1 v.2.1) (F_nonneg4 v.1 v.2.1) (F_nonneg5 v.1 v.2.1) v.2.2

/-- For the cell (a - 5, b - 2) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 87310904352537230170415654101340583859980175922610955433213490505923722186916147964361770117076178354307104027159226269963500095274378647874042706878981845529635008773832751088586107509757163652433211547976885079356024119042896308624311325977497487053712374349792796503103973234509110446928366187271527194887748138876731067630443895082337324883233660652010223532305655600949812790240515943535366544839775338141900954375722397748674634935435264 >>> (5 * ((a * 5 + b) * 6 + s)) % 2 ^ 5

/-- Every vertex of the box with F at most 9, other than v0, has a neighbor where F is one less:
the edge at position hint. -/
def nearOK : Bool :=
  (List.range 11).all fun a => (List.range 5).all fun b => (List.finRange 6).all fun s =>
    decide (9 < F ((a : ℤ) - 5, (b : ℤ) - 2, s)) ||
      decide (((a : ℤ) - 5, (b : ℤ) - 2, s) = v0) ||
      decide (hint a b s.val < 24 ∧ (E.getD (hint a b s.val) (0, 0, 0, 0)).1 = s ∧
        F ((a : ℤ) - 5 + (E.getD (hint a b s.val) (0, 0, 0, 0)).2.2.1,
          (b : ℤ) - 2 + (E.getD (hint a b s.val) (0, 0, 0, 0)).2.2.2,
          (E.getD (hint a b s.val) (0, 0, 0, 0)).2.1) + 1 = F ((a : ℤ) - 5, (b : ℤ) - 2, s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 9) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 5).toNat (by omega) (y + 2).toNat (by omega) s
  have ex : (((x + 5).toNat : ℕ) : ℤ) - 5 = x := by omega
  have ey : (((y + 2).toNat : ℕ) : ℤ) - 2 = y := by omega
  rw [ex, ey] at h'
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with (h1 | h1) | ⟨hlen, hs, hfe⟩
  · omega
  · exact absurd h1 hv
  · have he : E.getD (hint (x + 5).toNat (y + 2).toNat s.val) (0, 0, 0, 0) ∈ E := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    generalize E.getD (hint (x + 5).toNat (y + 2).toNat s.val) (0, 0, 0, 0) = e at he hs hfe
    subst hs
    exact ⟨_, adj_of_mem e he x y, hfe⟩

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 9
  · exact near_desc v hF hv
  · exact far_desc v (by omega)

theorem dist_eq_of_potential {W : Type*} (H : SimpleGraph W) (w0 : W) (f : W → ℕ)
    (h0 : f w0 = 0) (hlip : ∀ u w, H.Adj u w → f w ≤ f u + 1)
    (hdesc : ∀ v, v ≠ w0 → ∃ w, H.Adj v w ∧ f w + 1 = f v) (v : W) :
    H.dist w0 v = f v := by
  have up : ∀ n, ∀ v, f v = n → ∃ p : H.Walk w0 v, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro v hv
      by_cases hv0 : v = w0
      · subst hv0
        exact ⟨SimpleGraph.Walk.nil, rfl⟩
      · obtain ⟨w, -, hw⟩ := hdesc v hv0
        omega
    | succ n ih =>
      intro v hv
      have hv0 : v ≠ w0 := by
        rintro rfl
        omega
      obtain ⟨w, hvw, hw⟩ := hdesc v hv0
      obtain ⟨p, hp⟩ := ih w (by omega)
      exact ⟨p.concat hvw.symm, by rw [SimpleGraph.Walk.length_concat, hp]⟩
  have low : ∀ (u : W) (p : H.Walk u v), f v ≤ f u + p.length := by
    intro u p
    induction p with
    | nil => simp
    | cons h p ih =>
      rw [SimpleGraph.Walk.length_cons]
      have := hlip _ _ h
      omega
  obtain ⟨p, hp⟩ := up (f v) v rfl
  apply le_antisymm
  · exact (H.dist_le p).trans hp.le
  · obtain ⟨q, hq⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist (G := H) ⟨p⟩
    have := low w0 q
    omega

/-- The graph distance from v0 is the largest facet potential. -/
theorem dist_eq (v : V) : G.dist v0 v = (F v).toNat := by
  apply dist_eq_of_potential G v0 (fun v => (F v).toNat)
  · show (F v0).toNat = 0
    decide
  · intro u w h
    have := lip u w h
    have := F_nonneg w
    have := F_nonneg u
    show (F w).toNat ≤ (F u).toNat + 1
    omega
  · intro v hv
    obtain ⟨w, hw, he⟩ := desc v hv
    refine ⟨w, hw, ?_⟩
    have := F_nonneg w
    show (F w).toNat + 1 = (F v).toNat
    omega


/-! ## Counting the spheres

The sphere F = n splits into pieces: class s and the first facet i attaining the maximum. The
gradient of facet i is gc i times the primitive vector (Ap i, Bp i), so the points of class s with
pot_i = n lie on the line Ap i x + Bp i y = c with c = lev s i n, and only when gc i divides
n - Cc s i. That line is par s i c u = (al i c + Bp i u, be i c - Ap i u), and potential j is
ka i j c + Dm i j u + Cc s j there (`pot_par`). The previous facet bounds u from above, the next one
from below, and for n ≥ 5 the other facets lie below by Farkas certificates (`cf1` .. `cf0`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`). So
each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 20 moves every quotient by an integer (`inner_shift`, `S_shift`).
The tables are fields of natural numbers (`ctab`), which the kernel reads in constant time. The
section lives in the namespace `Count`; `gf`, `recur`, `controls` and `a_step` (and `a_closed` for
a short period) are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T, each stored as value + off. -/
def ctab (T B off k : ℕ) : ℤ := ((T >>> (B * k) % 2 ^ B : ℕ) : ℤ) - (off : ℤ)

def gcN (k : ℕ) : ℤ := ctab 159683337 3 0 k

def gc (i : Fin 10) : ℤ := gcN i.val

def ApN (k : ℕ) : ℤ := ctab 21907080 3 2 k

def Ap (i : Fin 10) : ℤ := ApN i.val

def BpN (k : ℕ) : ℤ := ctab 516861002515 4 4 k

def Bp (i : Fin 10) : ℤ := BpN i.val

def alN (k : ℕ) : ℤ := ctab 550033 2 1 k

def al (i : Fin 10) : ℤ := alN i.val

def beN (k : ℕ) : ℤ := ctab 628804 2 1 k

def be (i : Fin 10) : ℤ := beN i.val

theorem prim : ∀ i : Fin 10, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧
    al i * Ap i + be i * Bp i = 1 := by
  decide +kernel

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 10) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 10) : ℤ := Ac j * al i + Bc j * be i

theorem orient : ∀ i : Fin 10, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 6) (i : Fin 10) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 6) (i j : Fin 10) (c u : ℤ) :
    pot (par s i c u) j = ka i j * c + Dm i j * u + Cc s j := by
  simp only [pot, par, ka, Dm]
  ring

theorem par_inv (v : V) (i : Fin 10) :
    v = par v.2.2 i (Ap i * v.1 + Bp i * v.2.1) (be i * v.1 - al i * v.2.1) := by
  obtain ⟨x, y, s⟩ := v
  have hb := (prim i).2.2.2
  simp only [par, Prod.mk.injEq, and_true]
  constructor
  · linear_combination (-x) * hb
  · linear_combination (-y) * hb

theorem pot_lev (v : V) (i : Fin 10) : pot v i = gc i * (Ap i * v.1 + Bp i * v.2.1) + Cc v.2.2 i := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  simp only [pot]
  rw [h1, h2]
  ring

theorem par_inj (s : Fin 6) (i : Fin 10) (c : ℤ) : Function.Injective (par s i c) := by
  intro u u' h
  simp only [par, Prod.mk.injEq] at h
  have hb := (prim i).2.2.2
  have h1 : Bp i * (u - u') = 0 := by linarith [h.1]
  have h2 : Ap i * (u - u') = 0 := by linarith [h.2.1]
  have h3 : (u - u') = (u - u') * (al i * Ap i + be i * Bp i) := by rw [hb, mul_one]
  have : u - u' = 0 := by
    rw [h3]
    linear_combination (al i) * h2 + (be i) * h1
  linarith

/-- Some facet attains the maximum. -/
theorem F_attained (v : V) : ∃ k : Fin 10, pot v k = F v := by
  by_contra hne
  have h : ∀ k, pot v k ≤ F v - 1 := fun k => by
    have h1 := le_F v k
    have h2 : pot v k ≠ F v := fun e => hne ⟨k, e⟩
    omega
  have := F_le v (F v - 1) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9)
  omega

/-- The first facet attaining the maximum. -/
noncomputable def fi (v : V) : Fin 10 := Fin.find (fun k => pot v k = F v) (F_attained v)

theorem fi_spec (v : V) : pot v (fi v) = F v ∧ ∀ j, j < fi v → pot v j < F v :=
  ⟨Fin.find_spec (F_attained v), fun j hj =>
    lt_of_le_of_ne (le_F v j) (Fin.find_min (F_attained v) hj)⟩

theorem fi_iff (v : V) (i : Fin 10) : fi v = i ↔ pot v i = F v ∧ ∀ j, j < i → pot v j < F v := by
  constructor
  · rintro rfl
    exact fi_spec v
  · rintro ⟨h1, h2⟩
    obtain ⟨g1, g2⟩ := fi_spec v
    rcases lt_trichotomy (fi v) i with h | h | h
    · exact absurd g1 (ne_of_lt (h2 _ h))
    · exact h
    · exact absurd h1 (ne_of_lt (g2 _ h))

theorem ite01 (c : Prop) [Decidable c] : (0 : ℤ) ≤ (if c then 1 else 0) ∧ (if c then 1 else 0 : ℤ) ≤ 1 := by
  split_ifs <;> norm_num

/-- On the sphere F = n, the first maximal facet is i exactly when potential i is n and every
potential j is at most n - [j < i]. -/
theorem piece_iff (v : V) (i : Fin 10) (n : ℤ) :
    (F v = n ∧ fi v = i) ↔ (pot v i = n ∧ ∀ j, pot v j ≤ n - (if j < i then 1 else 0)) := by
  rw [fi_iff]
  constructor
  · rintro ⟨rfl, h1, h2⟩
    refine ⟨h1, fun j => ?_⟩
    split_ifs with hj
    · have := h2 j hj
      omega
    · have := le_F v j
      omega
  · rintro ⟨h1, h2⟩
    have h3 : ∀ j, pot v j ≤ n := fun j => le_trans (h2 j) (sub_le_self n (ite01 _).1)
    have hF : F v = n := le_antisymm (F_le_all v n h3) (h1 ▸ le_F v i)
    refine ⟨hF, hF ▸ h1, fun j hj => ?_⟩
    have := h2 j
    rw [if_pos hj] at this
    omega

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (5 ≤ pot_i) is a contradiction, for every class. -/

def cf1N (k : ℕ) : ℤ := ctab 5339029594970769155771005988268622797693517888564823892878995318541176522266859411878368207011843827743389040234332160 4 0 k

def cf1 (i : Fin 10) (j : Fin 10) : ℤ := cf1N (j.val + 10 * i.val)

def cf2N (k : ℕ) : ℤ := ctab 677270831186294784595952672929055567246068617515285233023065290598823597935219185478323000825766712985869613762385920 4 0 k

def cf2 (i : Fin 10) (j : Fin 10) : ℤ := cf2N (j.val + 10 * i.val)

def cf3N (k : ℕ) : ℤ := ctab 17540524376543369326087159598012930682265427204801715724281277901932986605655912228895552 3 0 k

def cf3 (i : Fin 10) (j : Fin 10) : ℤ := cf3N (j.val + 10 * i.val)

def cf0N (k : ℕ) : ℤ := ctab 7092389953939868548897273438722774443031334202255094147792 2 0 k

def cf0 (i : Fin 10) (j : Fin 10) : ℤ := cf0N (j.val + 10 * i.val)


/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The class constants Cc s i, packed for the kernel. -/
def cTN (k : ℕ) : ℤ := ctab 656723674913972612674314615466003673631419570390869723 3 2 k

def cT (s : Fin 6) (i : Fin 10) : ℤ := cTN (i.val + 10 * s.val)

theorem cT_eq : ∀ s : Fin 6, ∀ i : Fin 10, cT s i = Cc s i := by
  decide +kernel

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 6) (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (cT s h - cT s i + (if h < i then 1 else 0)) +
    cf2 i j * (cT s k - cT s i + (if k < i then 1 else 0)) + cf3 i j * (cT s i - cT s j) +
    cf0 i j * (5 - cT s i)

instance (i j : Fin 10) : Decidable (certG i j) := by
  unfold certG; infer_instance

theorem certG_ok : ∀ i j : Fin 10, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

/-- certC on the indices, for the kernel: the previous facet of i is (i + 9) % 10, the next
one (i + 1) % 10. -/
def certCN (s i j : ℕ) : Prop :=
  0 < cf1N (j + 10 * i) * (cTN ((i + 9) % 10 + 10 * s) - cTN (i + 10 * s) +
      (if (i + 9) % 10 < i then 1 else 0)) +
    cf2N (j + 10 * i) * (cTN ((i + 1) % 10 + 10 * s) - cTN (i + 10 * s) +
      (if (i + 1) % 10 < i then 1 else 0)) +
    cf3N (j + 10 * i) * (cTN (i + 10 * s) - cTN (j + 10 * s)) +
    cf0N (j + 10 * i) * (5 - cTN (i + 10 * s))

instance (s i j : ℕ) : Decidable (certCN s i j) := by
  unfold certCN; infer_instance

theorem certCN_ok : ∀ s, s < 6 → ∀ i, i < 10 → ∀ j, j < 10 →
    j = (i + 9) % 10 ∨ j = i ∨ j = (i + 1) % 10 ∨ certCN s i j := by
  decide +kernel

theorem fin_prev : ∀ i : Fin 10, (i - 1).val = (i.val + 9) % 10 := by decide +kernel

theorem fin_next : ∀ i : Fin 10, (i + 1).val = (i.val + 1) % 10 := by decide +kernel

theorem certC_ok (s : Fin 6) (i j : Fin 10) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    certC s i j := by
  have a1 := fin_prev i
  have a2 := fin_next i
  rcases certCN_ok s.val s.isLt i.val i.isLt j.val j.isLt with h | h | h | h
  · exact absurd (Fin.ext (h.trans a1.symm)) e1
  · exact absurd (Fin.ext h) e2
  · exact absurd (Fin.ext (h.trans a2.symm)) e3
  · show 0 < cf1 i j * (cT s (i - 1) - cT s i + (if i - 1 < i then 1 else 0)) +
      cf2 i j * (cT s (i + 1) - cT s i + (if i + 1 < i then 1 else 0)) +
      cf3 i j * (cT s i - cT s j) + cf0 i j * (5 - cT s i)
    simp only [cf1, cf2, cf3, cf0, cT, Fin.lt_def, a1, a2]
    exact h

theorem farkas4 (v : V) (h i k j : Fin 10) (e1 e2 r l1 l2 l3 l0 : ℤ)
    (hl : 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ 0 ≤ l0)
    (hx : l1 * (Ac h - Ac i) + l2 * (Ac k - Ac i) + l3 * (Ac i - Ac j) - l0 * Ac i = 0)
    (hy : l1 * (Bc h - Bc i) + l2 * (Bc k - Bc i) + l3 * (Bc i - Bc j) - l0 * Bc i = 0)
    (hc : 0 < l1 * (Cc v.2.2 h - Cc v.2.2 i + e1) + l2 * (Cc v.2.2 k - Cc v.2.2 i + e2) +
      l3 * (Cc v.2.2 i - Cc v.2.2 j) + l0 * (r - Cc v.2.2 i))
    (f1 : pot v h ≤ pot v i - e1) (f2 : pot v k ≤ pot v i - e2) (f3 : pot v i ≤ pot v j)
    (f0 : r ≤ pot v i) : False := by
  have g1 := mul_nonpos_of_nonneg_of_nonpos hl.1 (show pot v h - pot v i + e1 ≤ 0 by linarith)
  have g2 := mul_nonpos_of_nonneg_of_nonpos hl.2.1 (show pot v k - pot v i + e2 ≤ 0 by linarith)
  have g3 := mul_nonpos_of_nonneg_of_nonpos hl.2.2.1 (show pot v i - pot v j ≤ 0 by linarith)
  have g0 := mul_nonpos_of_nonneg_of_nonpos hl.2.2.2 (show r - pot v i ≤ 0 by linarith)
  have e : l1 * (pot v h - pot v i + e1) + l2 * (pot v k - pot v i + e2) +
      l3 * (pot v i - pot v j) + l0 * (r - pot v i) =
      l1 * (Cc v.2.2 h - Cc v.2.2 i + e1) + l2 * (Cc v.2.2 k - Cc v.2.2 i + e2) +
        l3 * (Cc v.2.2 i - Cc v.2.2 j) + l0 * (r - Cc v.2.2 i) := by
    simp only [pot]
    linear_combination v.1 * hx + v.2.1 * hy
  linarith

/-- The level of the line of facet i through the points of class s with pot_i = n. -/
def lev (s : Fin 6) (i : Fin 10) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 6) (i : Fin 10) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 6) (i j : Fin 10) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 6) (i : Fin 10) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 6) (i : Fin 10) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 6) (i j : Fin 10) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 6) (i : Fin 10) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 6) (i : Fin 10) (n u : ℤ) :
    lo s i n ≤ u ↔ Dm i (i + 1) * u ≤ Rb s i (i + 1) n := by
  have hd : 0 < -Dm i (i + 1) := by linarith [(orient i).2]
  rw [lo, neg_le, Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> linarith

theorem ka_self (i : Fin 10) : ka i i = gc i := by
  obtain ⟨h1, h2, -, hb⟩ := prim i
  rw [ka, h1, h2]
  linear_combination (gc i) * hb

theorem Dm_self (i : Fin 10) : Dm i i = 0 := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  rw [Dm, h1, h2]
  ring

theorem pot_par_self (s : Fin 6) (i : Fin 10) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 5 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 6) (i : Fin 10) (n u : ℤ) (hn : 5 ≤ n)
    (hd : (n - Cc s i) % gc i = 0) (h1 : lo s i n ≤ u) (h2 : u ≤ hi s i n) :
    ∀ j, pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) := by
  have hi' := pot_par_self s i n u hd
  have hh := (pot_le_iff s i (i - 1) n u).2 ((le_hi_iff s i n u).1 h2)
  have hk := (pot_le_iff s i (i + 1) n u).2 ((lo_le_iff s i n u).1 h1)
  intro j
  by_cases e1 : j = i - 1
  · rw [e1]; exact hh
  by_cases e2 : j = i
  · simp only [e2, hi', lt_irrefl, if_false, sub_zero, le_refl]
  by_cases e3 : j = i + 1
  · rw [e3]; exact hk
  obtain ⟨c1, c2, c3, c0, cx, cy⟩ := certG_ok i j e1 e2 e3
  have cc := certC_ok s i j e1 e2 e3
  simp only [certC, cT_eq] at cc
  by_contra hne
  have f3 : pot (par s i (lev s i n) u) i ≤ pot (par s i (lev s i n) u) j := by
    have := (ite01 (j < i)).2
    rw [hi']
    linarith [not_le.1 hne]
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 5 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 2)) (1 * n + 2) ×ˢ
    (Finset.Icc (-(1 * n + 2)) (1 * n + 2) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 6, ∀ j : Fin 10, -2 ≤ Cc s j ∧ Cc s j ≤ 2 := by decide +kernel

/-- Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/
theorem box_pairs : 1 * Ac 4 + 3 * Ac 5 = 8 ∧ 1 * Bc 4 + 3 * Bc 5 = 0 ∧
    3 * Ac 0 + 1 * Ac 9 = (-8) ∧ 3 * Bc 0 + 1 * Bc 9 = 0 ∧
    1 * Ac 7 + 0 * Ac 7 = 0 ∧ 1 * Bc 7 + 0 * Bc 7 = 4 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-4) := by
  decide +kernel

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 6) :
    8 * x ≤ 4 * F (x, y, s) + 8 ∧
    8 * (-x) ≤ 4 * F (x, y, s) + 8 ∧
    4 * y ≤ 1 * F (x, y, s) + 2 ∧
    4 * (-y) ≤ 1 * F (x, y, s) + 2 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 4 + 3 * pot (x, y, s) 5 =
      8 * x + 1 * Cc s 4 + 3 * Cc s 5 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 4
  have r0 := le_F (x, y, s) 5
  have k0 := Cbound s 4
  have l0 := Cbound s 5
  have e1 : 3 * pot (x, y, s) 0 + 1 * pot (x, y, s) 9 =
      8 * (-x) + 3 * Cc s 0 + 1 * Cc s 9 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 9
  have k1 := Cbound s 0
  have l1 := Cbound s 9
  have e2 : 1 * pot (x, y, s) 7 + 0 * pot (x, y, s) 7 =
      4 * y + 1 * Cc s 7 + 0 * Cc s 7 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 7
  have r2 := le_F (x, y, s) 7
  have k2 := Cbound s 7
  have l2 := Cbound s 7
  have e3 : 1 * pot (x, y, s) 2 + 0 * pot (x, y, s) 2 =
      4 * (-y) + 1 * Cc s 2 + 0 * Cc s 2 := by
    simp only [pot]; linear_combination x * p7 + y * p8
  have q3 := le_F (x, y, s) 2
  have r3 := le_F (x, y, s) 2
  have k3 := Cbound s 2
  have l3 := Cbound s 2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_Bx (v : V) (n : ℤ) (h : F v ≤ n) : v ∈ Bx n := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  have h0 := F_nonneg (x, y, s)
  simp only [Bx, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  omega

/-- The piece of the sphere F = n with class s and first maximal facet i. -/
noncomputable def PF (s : Fin 6) (i : Fin 10) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 6) (i : Fin 10) (n : ℤ) (hn : 5 ≤ n) :
    PF s i n = if (n - Cc s i) % gc i = 0 then
      (Finset.Icc (lo s i n) (hi s i n)).image (par s i (lev s i n)) else ∅ := by
  split_ifs with hd
  · ext v
    simp only [PF, Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨-, hs, hv⟩
      obtain ⟨h1, h2⟩ := (piece_iff v i n).1 hv
      have hl : lev s i n = Ap i * v.1 + Bp i * v.2.1 := by
        rw [lev, ← h1, pot_lev, hs, Int.add_sub_cancel,
          Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
      have hv' := par_inv v i
      rw [hs, ← hl] at hv'
      refine ⟨be i * v.1 - al i * v.2.1, ⟨?_, ?_⟩, hv'.symm⟩
      · rw [lo_le_iff, ← pot_le_iff, ← hv']
        exact h2 (i + 1)
      · rw [le_hi_iff, ← pot_le_iff, ← hv']
        exact h2 (i - 1)
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      have hp := par_piece s i n u hn hd h1 h2
      have hv := (piece_iff (par s i (lev s i n) u) i n).2 ⟨pot_par_self s i n u hd, hp⟩
      exact ⟨mem_Bx _ n (le_of_eq hv.1), rfl, hv⟩
  · rw [PF]
    apply Finset.filter_false_of_mem
    rintro v - ⟨hs, hv⟩
    obtain ⟨h1, -⟩ := (piece_iff v i n).1 hv
    apply hd
    rw [← hs, ← h1, pot_lev, Int.add_sub_cancel, Int.mul_emod_right]

/-- The length of the piece (s, i) at level n, as an integer. -/
def inner (s : Fin 6) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 6) (i : Fin 10) (n : ℤ) (hn : 5 ≤ n) :
    (PF s i n).card = (inner s i n).toNat := by
  rw [piece_eq s i n hn, inner]
  split_ifs
  · rw [Finset.card_image_of_injective _ (par_inj s i _), Int.card_Icc]
  · rfl

/-- The number of points with F = n. -/
noncomputable def cnt (n : ℤ) : ℕ := Set.ncard {v : V | F v = n}

theorem cnt_eq_card (n : ℤ) : cnt n = ((Bx n).filter (fun v => F v = n)).card := by
  rw [cnt, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Finset.coe_filter]
  exact ⟨fun h => ⟨mem_Bx v n (le_of_eq h), h⟩, fun h => h.2⟩

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 6 × Fin 10, (PF p.1 p.2 n).card := by
  rw [cnt_eq_card, Finset.card_eq_sum_card_fiberwise (f := fun v => (v.2.2, fi v))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [PF, Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro v _
  constructor
  · rintro ⟨h1, h2⟩
    rw [← h2]
    exact ⟨rfl, h1, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, by rw [h1, h3]⟩

/-- The closed form of the sphere size: the sum of the piece lengths. -/
def S (n : ℤ) : ℤ := ∑ p : Fin 6 × Fin 10, inner p.1 p.2 n

/-! Shifting n by 20 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqN (k : ℕ) : ℤ := ctab 725871640581780 5 0 k

def Lq (i : Fin 10) : ℤ := LqN i.val

def mhN (k : ℕ) : ℤ := ctab 14745227146386 5 8 k

def mh (i : Fin 10) : ℤ := mhN i.val

def mkN (k : ℕ) : ℤ := ctab 638005599674784 5 8 k

def mk (i : Fin 10) : ℤ := mkN i.val

theorem shift_ok : ∀ i : Fin 10, (20 : ℤ) = gc i * Lq i ∧
    20 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    20 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 6) (i : Fin 10) (n : ℤ) :
    inner s i (n + 20) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 20 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 20 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 20) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 20) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 20) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 4 = gc i * lgq i. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 6 × Fin 10, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 20) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

def lgqN (k : ℕ) : ℤ := ctab 607275108 3 0 k

def lgq (i : Fin 10) : ℤ := lgqN i.val

theorem lg_ok : ∀ i : Fin 10, (4 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_periodic (x q : ℤ) : Gs (x + 4 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 4 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (lgq r.2 * q) := by
    linear_combination q * lg_ok r.2
  rw [e, Int.add_mul_emod_self_left]

theorem mhk_nonneg : ∀ i : Fin 10, 0 ≤ mh i + mk i := by decide +kernel

/-- The growth of the piece with index c = i + 10 s, read by the kernel from the tables. -/
def gsN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 10) = 0 then mhN (c % 10) + mkN (c % 10) else 0

theorem gsN_eq (s : Fin 6) (i : Fin 10) (n : ℤ) :
    gsN (i.val + 10 * s.val) n = (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  have hi := i.isLt
  have h : (i.val + 10 * s.val) % 10 = i.val := by omega
  rw [gsN, h, ← cT_eq]
  rfl

def GsN (n : ℤ) : ℤ := ((List.range (6 * 10)).map fun c => gsN c n).sum

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uhN (k : ℕ) : ℤ := ctab 57083598 3 2 k

def uh (i : Fin 10) : ℤ := uhN i.val

def dhN (k : ℕ) : ℤ := ctab 361138307416 4 0 k

def dh (i : Fin 10) : ℤ := dhN i.val

def ukN (k : ℕ) : ℤ := ctab 827089560 3 2 k

def uk (i : Fin 10) : ℤ := ukN i.val

def dkN (k : ℕ) : ℤ := ctab 571571982661 4 0 k

def dk (i : Fin 10) : ℤ := dkN i.val

def vhN (k : ℕ) : ℤ := ctab 449561311419457449921761510221762647 2 2 k

def vh (s : Fin 6) (i : Fin 10) : ℤ := vhN (i.val + 10 * s.val)

def vkN (k : ℕ) : ℤ := ctab 884530985896472598678304539526933482 2 2 k

def vk (s : Fin 6) (i : Fin 10) : ℤ := vkN (i.val + 10 * s.val)

def levT (s : Fin 6) (i : Fin 10) (n : ℤ) : ℤ := (n - cT s i) / gc i

def innerT (s : Fin 6) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - cT s i) % gc i = 0 then
    (uh i * levT s i n + vh s i) / dh i + (uk i * levT s i n + vk s i) / dk i + 1 else 0

theorem tab_ok : ∀ s : Fin 6, ∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  decide +kernel

theorem inner_eq (s : Fin 6) (i : Fin 10) (n : ℤ) : inner s i n = innerT s i n := by
  have hl : levT s i n = lev s i n := by rw [levT, lev, cT_eq]
  rw [inner, innerT, cT_eq, hl]
  split_ifs with hd
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := tab_ok s i
    have hc := lev_mul s i n hd
    have r1 : Rb s i (i - 1) n = uh i * lev s i n + vh s i := by
      rw [e1, e2, Rb]; linear_combination (-1 : ℤ) * hc
    have r2 : Rb s i (i + 1) n = uk i * lev s i n + vk s i := by
      rw [e4, e5, Rb]; linear_combination (-1 : ℤ) * hc
    rw [hi, lo, r1, r2, e3, e6]
    ring
  · rfl

/-- The closed form in table form. -/
def ST (n : ℤ) : ℤ := ∑ p : Fin 6 × Fin 10, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The piece length with index c = i + 10 s, read by the kernel from the tables directly. -/
def innerN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 10) = 0 then
    (uhN (c % 10) * ((n - cTN c) / gcN (c % 10)) + vhN c) / dhN (c % 10) +
      (ukN (c % 10) * ((n - cTN c) / gcN (c % 10)) + vkN c) / dkN (c % 10) + 1
  else 0

theorem innerN_eq (s : Fin 6) (i : Fin 10) (n : ℤ) :
    innerN (i.val + 10 * s.val) n = innerT s i n := by
  have hi := i.isLt
  have h : (i.val + 10 * s.val) % 10 = i.val := by omega
  rw [innerN, h]
  rfl

theorem sum_range_list (f : ℕ → ℤ) (N : ℕ) :
    ∑ c ∈ Finset.range N, f c = ((List.range N).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

/-- The closed form over the indices of the pieces. -/
def STN (n : ℤ) : ℤ := ((List.range (6 * 10)).map fun c => innerN c n).sum

theorem ST_eq_STN (n : ℤ) : ST n = STN n := by
  rw [ST, STN, Fintype.sum_equiv finProdFinEquiv (fun q : Fin 6 × Fin 10 => innerT q.1 q.2 n)
    (fun c : Fin (6 * 10) => innerN c.val n) (fun q => (innerN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => innerN c n) (6 * 10), sum_range_list]

theorem Gs_eq_GsN (n : ℤ) : Gs n = GsN n := by
  rw [Gs, GsN, Fintype.sum_equiv finProdFinEquiv
    (fun q : Fin 6 × Fin 10 => if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)
    (fun c : Fin (6 * 10) => gsN c.val n) (fun q => (gsN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => gsN c n) (6 * 10), sum_range_list]

/-- The step of the closed form at residue t mod 20. -/
def dv (t : ℕ) : ℕ := [82, 92, 82, 92, 82, 92, 82, 92, 82, 92, 82, 92, 82, 92, 82, 92, 82, 92, 82, 92].getD (t % 20) 0

/-- The sequence in closed form: b(n + 20) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then [1].getD n 0 else dv (n - 1) * ((n - 1) / 20) + [4, 8, 14, 18, 20, 26, 30, 38, 36, 44, 46, 56, 54, 62, 62, 74, 70, 82, 78, 92].getD ((n - 1) % 20) 0

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 20) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 20 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 20 - 1 = n - 1 + 20 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 20)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 20) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 20 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 20 - 1 = n - 1 + 20 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 20)]
  ring

/-- The growth of b over 20 terms is that of S, on one period of the residues. -/
theorem grow_base : ∀ t : ℕ, t < 20 → 1 * (dv t : ℤ) = GsN (1 + (t : ℤ)) := by
  decide +kernel

theorem grow (n : ℕ) (hn : 1 ≤ n) : 1 * (dv (n - 1) : ℤ) = Gs n := by
  have h1 := grow_base ((n - 1) % 20) (Nat.mod_lt _ (by norm_num))
  have e1 : dv ((n - 1) % 20) = dv (n - 1) := by
    rw [dv, dv, Nat.mod_mod_of_dvd _ (by norm_num : 20 ∣ 20)]
  rw [e1, ← Gs_eq_GsN] at h1
  rw [h1]
  have e : (((1 : ℤ) + (((n - 1) % 20 : ℕ) : ℤ)) + 4 * (5 * (((n - 1) / 20 : ℕ) : ℤ))) = n := by
    have := Nat.mod_add_div (n - 1) 20
    omega
  rw [← e, Gs_periodic]

/-- One kernel pass over n = 5, ..., 24: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 20 →
    ((List.range (6 * 10)).all fun c => decide (0 ≤ innerN c (5 + (r : ℤ)))) = true ∧
      STN (5 + (r : ℤ)) = b (5 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 5 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 6) (i : Fin 10) (n : ℤ) (hn : 5 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 5 + t := ⟨(n - 5).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 20
    · rw [inner_eq, ← innerN_eq]
      have hc : i.val + 10 * s.val < 6 * 10 := by
        have := i.isLt
        have := s.isLt
        omega
      exact of_decide_eq_true (List.all_eq_true.1 (period_ok t ht).1 _ (List.mem_range.2 hc))
    · have := ih (t - 20) (by omega) (by omega)
      have e : (5 : ℤ) + t = (5 + (t - 20 : ℕ)) + 20 := by
        push_cast [Nat.cast_sub (by omega : 20 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 5 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

theorem S_eq_b (n : ℕ) (hn : 5 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 25
    · obtain ⟨r, rfl⟩ : ∃ r, n = 5 + r := ⟨n - 5, by omega⟩
      rw [S_eq_ST, ST_eq_STN]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 20) (by omega) (by omega)
      have h2 := S_shift ((n - 20 : ℕ) : ℤ)
      have h3 := b_shift (n - 20) (by omega)
      have h4 := grow (n - 20) (by omega)
      rw [show n - 20 + 20 = n by omega] at h3
      rw [show ((n - 20 : ℕ) : ℤ) + 20 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 4 lie in the box -3 ≤ x ≤ 3, -1 ≤ y ≤ 1 (`small_box`), and
the kernel checks that those of the box are the 45 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 6) (h : F (x, y, s) ≤ 4) :
    -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 4. -/
def smallL : List V :=
  [(0, 0, 1), ((-1), 0, 2), (0, 0, 0), (0, 0, 2), (0, 0, 5), ((-1), (-1), 3), ((-1), 0, 1), (0, (-1), 4), (0, 0, 3), (0, 0, 4), (1, 0, 0), (1, 0, 1), (1, 0, 5), ((-2), 0, 2), ((-1), (-1), 4), ((-1), (-1), 5), ((-1), 0, 0), ((-1), 0, 3), ((-1), 0, 5), (0, (-1), 3), (0, (-1), 5), (0, 1, 0), (1, (-1), 4), (1, 0, 2), (1, 0, 3), (1, 0, 4), (1, 1, 0), ((-2), (-1), 2), ((-2), (-1), 3), ((-2), 0, 1), ((-1), (-1), 1), ((-1), (-1), 2), ((-1), 0, 4), ((-1), 1, 2), (0, (-1), 1), (0, 1, 1), (0, 1, 2), (1, (-1), 3), (1, (-1), 5), (1, 1, 1), (2, 0, 0), (2, 0, 1), (2, 0, 4), (2, 0, 5), (2, 1, 0)]

def smallOK : Bool :=
  (List.range 7).all fun a => (List.range 3).all fun b => (List.finRange 6).all fun s =>
    decide (4 < F ((a : ℤ) - 3, (b : ℤ) - 1, s)) ||
      decide (((a : ℤ) - 3, (b : ℤ) - 1, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 4) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 3).toNat (by omega) (y + 1).toNat (by omega) s
  have ex : (((x + 3).toNat : ℕ) : ℤ) - 3 = x := by omega
  have ey : (((y + 1).toNat : ℕ) : ℤ) - 1 = y := by omega
  rw [ex, ey] at h'
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h1 | h1
  · omega
  · exact h1

theorem cnt_small (n : ℤ) (hn : n ≤ 4) :
    cnt n = ((smallL.filter (fun v => decide (F v = n))).toFinset).card := by
  rw [cnt, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => ⟨small_mem v (by omega), h⟩, fun h => h.2⟩

/-- The small spheres in closed form. -/
theorem small_ok : ∀ n : ℕ, n < 5 →
    ((smallL.filter (fun v => decide (F v = (n : ℤ)))).toFinset).card = b n := by
  decide +kernel

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 5 are counted in
`smallL`, those from 5 on are S(n), and both agree with the closed form b (`a_eq_b`). The step
from n to n + 20, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f.
follow, their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 5 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 5 ∨ 5 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_ok n h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 20) = a(n) + dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 20) = a n + dv (n - 1) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-- The closed form per residue of n mod 20, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (20 * k + 1) = 82 * k + 4 ∧
    a (20 * k + 2) = 92 * k + 8 ∧
    a (20 * k + 3) = 82 * k + 14 ∧
    a (20 * k + 4) = 92 * k + 18 ∧
    a (20 * k + 5) = 82 * k + 20 ∧
    a (20 * k + 6) = 92 * k + 26 ∧
    a (20 * k + 7) = 82 * k + 30 ∧
    a (20 * k + 8) = 92 * k + 38 ∧
    a (20 * k + 9) = 82 * k + 36 ∧
    a (20 * k + 10) = 92 * k + 44 ∧
    a (20 * k + 11) = 82 * k + 46 ∧
    a (20 * k + 12) = 92 * k + 56 ∧
    a (20 * k + 13) = 82 * k + 54 ∧
    a (20 * k + 14) = 92 * k + 62 ∧
    a (20 * k + 15) = 82 * k + 62 ∧
    a (20 * k + 16) = 92 * k + 74 ∧
    a (20 * k + 17) = 82 * k + 70 ∧
    a (20 * k + 18) = 92 * k + 82 ∧
    a (20 * k + 19) = 82 * k + 78 ∧
    a (20 * k + 20) = 92 * k + 92 := by
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b, if_neg (show ¬ (20 * k + 1 < 1) by omega),
      show 20 * k + 1 - 1 = 20 * k by omega, dv, show (20 * k) / 20 = k by omega,
      show (20 * k) % 20 = 0 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 2 < 1) by omega),
      show 20 * k + 2 - 1 = 20 * k + 1 by omega, dv, show (20 * k + 1) / 20 = k by omega,
      show (20 * k + 1) % 20 = 1 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 3 < 1) by omega),
      show 20 * k + 3 - 1 = 20 * k + 2 by omega, dv, show (20 * k + 2) / 20 = k by omega,
      show (20 * k + 2) % 20 = 2 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 4 < 1) by omega),
      show 20 * k + 4 - 1 = 20 * k + 3 by omega, dv, show (20 * k + 3) / 20 = k by omega,
      show (20 * k + 3) % 20 = 3 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 5 < 1) by omega),
      show 20 * k + 5 - 1 = 20 * k + 4 by omega, dv, show (20 * k + 4) / 20 = k by omega,
      show (20 * k + 4) % 20 = 4 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 6 < 1) by omega),
      show 20 * k + 6 - 1 = 20 * k + 5 by omega, dv, show (20 * k + 5) / 20 = k by omega,
      show (20 * k + 5) % 20 = 5 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 7 < 1) by omega),
      show 20 * k + 7 - 1 = 20 * k + 6 by omega, dv, show (20 * k + 6) / 20 = k by omega,
      show (20 * k + 6) % 20 = 6 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 8 < 1) by omega),
      show 20 * k + 8 - 1 = 20 * k + 7 by omega, dv, show (20 * k + 7) / 20 = k by omega,
      show (20 * k + 7) % 20 = 7 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 9 < 1) by omega),
      show 20 * k + 9 - 1 = 20 * k + 8 by omega, dv, show (20 * k + 8) / 20 = k by omega,
      show (20 * k + 8) % 20 = 8 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 10 < 1) by omega),
      show 20 * k + 10 - 1 = 20 * k + 9 by omega, dv, show (20 * k + 9) / 20 = k by omega,
      show (20 * k + 9) % 20 = 9 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 11 < 1) by omega),
      show 20 * k + 11 - 1 = 20 * k + 10 by omega, dv, show (20 * k + 10) / 20 = k by omega,
      show (20 * k + 10) % 20 = 10 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 12 < 1) by omega),
      show 20 * k + 12 - 1 = 20 * k + 11 by omega, dv, show (20 * k + 11) / 20 = k by omega,
      show (20 * k + 11) % 20 = 11 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 13 < 1) by omega),
      show 20 * k + 13 - 1 = 20 * k + 12 by omega, dv, show (20 * k + 12) / 20 = k by omega,
      show (20 * k + 12) % 20 = 12 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 14 < 1) by omega),
      show 20 * k + 14 - 1 = 20 * k + 13 by omega, dv, show (20 * k + 13) / 20 = k by omega,
      show (20 * k + 13) % 20 = 13 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 15 < 1) by omega),
      show 20 * k + 15 - 1 = 20 * k + 14 by omega, dv, show (20 * k + 14) / 20 = k by omega,
      show (20 * k + 14) % 20 = 14 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 16 < 1) by omega),
      show 20 * k + 16 - 1 = 20 * k + 15 by omega, dv, show (20 * k + 15) / 20 = k by omega,
      show (20 * k + 15) % 20 = 15 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 17 < 1) by omega),
      show 20 * k + 17 - 1 = 20 * k + 16 by omega, dv, show (20 * k + 16) / 20 = k by omega,
      show (20 * k + 16) % 20 = 16 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 18 < 1) by omega),
      show 20 * k + 18 - 1 = 20 * k + 17 by omega, dv, show (20 * k + 17) / 20 = k by omega,
      show (20 * k + 17) % 20 = 17 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 19 < 1) by omega),
      show 20 * k + 19 - 1 = 20 * k + 18 by omega, dv, show (20 * k + 18) / 20 = k by omega,
      show (20 * k + 18) % 20 = 18 by omega]
    rfl
  · rw [b, if_neg (show ¬ (20 * k + 20 < 1) by omega),
      show 20 * k + 20 - 1 = 20 * k + 19 by omega, dv, show (20 * k + 19) / 20 = k by omega,
      show (20 * k + 19) % 20 = 19 by omega]
    rfl

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 14, 18, 20, 26, 30, 38, 36, 44, 46, 56, 54, 62, 62, 74, 70, 82, 78, 92, 86, 100, 96, 110, 102, 118, 112, 130, 118, 136, 128, 148, 136, 154, 144, 166, 152, 174, 160, 184, 168, 192, 178, 202, 184, 210, 194, 222, 200] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The steps satisfy the recurrence, on one period of the residues. -/
theorem drec_base : ∀ t : ℕ, t < 20 → (dv (t + 10) : ℤ) = -(dv (t + 9) : ℤ) + (dv (t + 6) : ℤ) + 2 * (dv (t + 5) : ℤ) + (dv (t + 4) : ℤ) - (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  decide +kernel

theorem drec (t : ℕ) : (dv (t + 10) : ℤ) = -(dv (t + 9) : ℤ) + (dv (t + 6) : ℤ) + 2 * (dv (t + 5) : ℤ) + (dv (t + 4) : ℤ) - (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 20 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 4, e 5, e 6, e 9, e 10]
  exact drec_base (t % 20) (Nat.mod_lt _ (by norm_num))

/-- The recurrence on its first 20 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 20 → (b (q + 11) : ℤ) = -b (q + 10) + b (q + 7) + 2 * b (q + 6) + b (q + 5) - b (q + 2) - b (q + 1) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 11) : ℤ) = -b (q + 10) + b (q + 7) + 2 * b (q + 6) + b (q + 5) - b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 20 ∨ 20 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 20 := ⟨q - 20, by omega⟩
      have h0 : (b (v + 11) : ℤ) = -b (v + 10) + b (v + 7) + 2 * b (v + 6) + b (v + 5) - b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have s1 : b (v + 21) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (by omega)
        rw [show v + 1 + 20 = v + 21 by omega,
          show v + 1 - 1 = v + 0 by omega] at h
        exact h
      have s2 : b (v + 22) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (by omega)
        rw [show v + 2 + 20 = v + 22 by omega,
          show v + 2 - 1 = v + 1 by omega] at h
        exact h
      have s5 : b (v + 25) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (by omega)
        rw [show v + 5 + 20 = v + 25 by omega,
          show v + 5 - 1 = v + 4 by omega] at h
        exact h
      have s6 : b (v + 26) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (by omega)
        rw [show v + 6 + 20 = v + 26 by omega,
          show v + 6 - 1 = v + 5 by omega] at h
        exact h
      have s7 : b (v + 27) = b (v + 7) + dv (v + 6) := by
        have h := b_step (v + 7) (by omega)
        rw [show v + 7 + 20 = v + 27 by omega,
          show v + 7 - 1 = v + 6 by omega] at h
        exact h
      have s10 : b (v + 30) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (by omega)
        rw [show v + 10 + 20 = v + 30 by omega,
          show v + 10 - 1 = v + 9 by omega] at h
        exact h
      have s11 : b (v + 31) = b (v + 11) + dv (v + 10) := by
        have h := b_step (v + 11) (by omega)
        rw [show v + 11 + 20 = v + 31 by omega,
          show v + 11 - 1 = v + 10 by omega] at h
        exact h
      have hd := drec v
      show (b (v + 31) : ℤ) = -b (v + 30) + b (v + 27) + 2 * b (v + 26) + b (v + 25) - b (v + 22) - b (v + 21)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 10 < n → (a n : ℤ) = -a (n - 1) + a (n - 4) + 2 * a (n - 5) + a (n - 6) - a (n - 9) - a (n - 10) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
  rw [show q + 11 - 1 = q + 10 by omega, show q + 11 - 4 = q + 7 by omega, show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega, show q + 11 - 9 = q + 2 by omega, show q + 11 - 10 = q + 1 by omega]
  simp only [a_eq_b]
  exact b_recur q

theorem bv0 : b 0 = 1 := by decide

theorem bv1 : b 1 = 4 := by decide

theorem bv2 : b 2 = 8 := by decide

theorem bv3 : b 3 = 14 := by decide

theorem bv4 : b 4 = 18 := by decide

theorem bv5 : b 5 = 20 := by decide

theorem bv6 : b 6 = 26 := by decide

theorem bv7 : b 7 = 30 := by decide

theorem bv8 : b 8 = 38 := by decide

theorem bv9 : b 9 = 36 := by decide

theorem bv10 : b 10 = 44 := by decide

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 + X ^ 9 - X ^ 6 - 2 * X ^ 5 - X ^ 4 + X + 1) =
      X ^ 10 + 5 * X ^ 9 + 14 * X ^ 8 + 22 * X ^ 7 + 29 * X ^ 6 + 32 * X ^ 5 + 31 * X ^ 4 + 22 * X ^ 3 + 12 * X ^ 2 + 5 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * (X ^ 10 + X ^ 9 - X ^ 6 - 2 * X ^ 5 - X ^ 4 + X + 1) = C 1 * A + C 1 * (A * X ^ 1) - C 1 * (A * X ^ 4) - C 2 * (A * X ^ 5) - C 1 * (A * X ^ 6) + C 1 * (A * X ^ 9) + C 1 * (A * X ^ 10) := by
    simp only [map_ofNat, map_one]
    ring
  have e2 : (X ^ 10 + 5 * X ^ 9 + 14 * X ^ 8 + 22 * X ^ 7 + 29 * X ^ 6 + 32 * X ^ 5 + 31 * X ^ 4 + 22 * X ^ 3 + 12 * X ^ 2 + 5 * X + 1 : ℚ⟦X⟧) = C 1 + X ^ 1 * C 5 + X ^ 2 * C 12 + X ^ 3 * C 22 + X ^ 4 * C 31 + X ^ 5 * C 32 + X ^ 6 * C 29 + X ^ 7 * C 22 + X ^ 8 * C 14 + X ^ 9 * C 5 + X ^ 10 * C 1 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> norm_num [bv0, bv1, bv2, bv3, bv4, bv5, bv6, bv7, bv8, bv9, bv10]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    have h : (b (q + 11) : ℤ) = -b (q + 10) + b (q + 7) + 2 * b (q + 6) + b (q + 5) - b (q + 2) - b (q + 1) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 4 = q + 7 by omega, show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega, show q + 11 - 9 = q + 2 by omega, show q + 11 - 10 = q + 1 by omega, show 1 ≤ q + 11 by omega, show 4 ≤ q + 11 by omega, show 5 ≤ q + 11 by omega, show 6 ≤ q + 11 by omega, show 9 ≤ q + 11 by omega, show 10 ≤ q + 11 by omega, show ¬ q + 11 = 0 by omega, show ¬ q + 11 = 1 by omega, show ¬ q + 11 = 2 by omega, show ¬ q + 11 = 3 by omega, show ¬ q + 11 = 4 by omega, show ¬ q + 11 = 5 by omega, show ¬ q + 11 = 6 by omega, show ¬ q + 11 = 7 by omega, show ¬ q + 11 = 8 by omega, show ¬ q + 11 = 9 by omega, show ¬ q + 11 = 10 by omega, if_true, if_false]
    linear_combination (1) * hq

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 + X ^ 9 - X ^ 6 - 2 * X ^ 5 - X ^ 4 + X + 1) =
      X ^ 10 + 5 * X ^ 9 + 14 * X ^ 8 + 22 * X ^ 7 + 29 * X ^ 6 + 32 * X ^ 5 + 31 * X ^ 4 + 22 * X ^ 3 + 12 * X ^ 2 + 5 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 10 < n → (a n : ℤ) = -a (n - 1) + a (n - 4) + 2 * a (n - 5) + a (n - 6) - a (n - 9) - a (n - 10) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 14, 18, 20, 26, 30, 38, 36, 44, 46, 56, 54, 62, 62, 74, 70, 82, 78, 92, 86, 100, 96, 110, 102, 118, 112, 130, 118, 136, 128, 148, 136, 154, 144, 166, 152, 174, 160, 184, 168, 192, 178, 202, 184, 210, 194, 222, 200] := Count.controls

/-- The step a(n + 20) = a(n) + Count.dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 20) = a n + Count.dv (n - 1) := Count.a_step n hn

/-- The closed form per residue of n mod 20, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (20 * k + 1) = 82 * k + 4 ∧
    a (20 * k + 2) = 92 * k + 8 ∧
    a (20 * k + 3) = 82 * k + 14 ∧
    a (20 * k + 4) = 92 * k + 18 ∧
    a (20 * k + 5) = 82 * k + 20 ∧
    a (20 * k + 6) = 92 * k + 26 ∧
    a (20 * k + 7) = 82 * k + 30 ∧
    a (20 * k + 8) = 92 * k + 38 ∧
    a (20 * k + 9) = 82 * k + 36 ∧
    a (20 * k + 10) = 92 * k + 44 ∧
    a (20 * k + 11) = 82 * k + 46 ∧
    a (20 * k + 12) = 92 * k + 56 ∧
    a (20 * k + 13) = 82 * k + 54 ∧
    a (20 * k + 14) = 92 * k + 62 ∧
    a (20 * k + 15) = 82 * k + 62 ∧
    a (20 * k + 16) = 92 * k + 74 ∧
    a (20 * k + 17) = 82 * k + 70 ∧
    a (20 * k + 18) = 92 * k + 82 ∧
    a (20 * k + 19) = 82 * k + 78 ∧
    a (20 * k + 20) = 92 * k + 92 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 + X ^ 9 - X ^ 6 - 2 * X ^ 5 - X ^ 4 + X + 1) =
      X ^ 10 + 5 * X ^ 9 + 14 * X ^ 8 + 22 * X ^ 7 + 29 * X ^ 6 + 32 * X ^ 5 + 31 * X ^ 4 + 22 * X ^ 3 + 12 * X ^ 2 + 5 * X + 1 ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = -a (n - 1) + a (n - 4) + 2 * a (n - 5) + a (n - 6) - a (n - 9) - a (n - 10) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a312411

theorem OMA.solution : type_of% @OMA.S_oeis_a312411.main :=
  OMA.S_oeis_a312411.conjecture
