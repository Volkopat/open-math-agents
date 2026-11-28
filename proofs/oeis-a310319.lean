import OMAStatements.S_oeis_a310319

namespace OMA.S_oeis_a310319






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 9

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 168875823430041
  | 1 => 150119987579016
  | 2 => 133700613797751
  | 3 => 152465324795511
  | 4 => 171221160646536
  | 5 => 112663613577606
  | 6 => 131355024923031
  | 7 => 115009202452326
  | 8 => 133773913450086
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 12) : ℤ := tget 75143066728821 4 8 i.val

def Bc (i : Fin 12) : ℤ := tget 171303587103831 4 8 i.val

def Cc (s : Fin 9) (i : Fin 12) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 75143066728821 4 i

def BcN (i : ℕ) : ℕ := tgetN 171303587103831 4 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem Ac_eq (i : Fin 12) : Ac i = (AcN i.val : ℤ) - 8 := rfl

theorem Bc_eq (i : Fin 12) : Bc i = (BcN i.val : ℤ) - 8 := rfl

theorem Cc_eq (s : Fin 9) (i : Fin 12) : Cc s i = (CcN s.val i.val : ℤ) - 8 := rfl


/-- The potential of facet i at v (facets in angular order around the growth polygon). -/
def pot (v : V) (i : Fin 12) : ℤ := Ac i * v.1 + Bc i * v.2.1 + Cc v.2.2 i

/-- The largest facet potential at v. -/
def F (v : V) : ℤ := max (max (max (max (max (max (max (max (max (max (max (pot v 0) (pot v 1)) (pot v 2)) (pot v 3)) (pot v 4)) (pot v 5)) (pot v 6)) (pot v 7)) (pot v 8)) (pot v 9)) (pot v 10)) (pot v 11)

theorem le_F0 (v : V) : pot v 0 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))))))))))
theorem le_F1 (v : V) : pot v 1 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))))))
theorem le_F2 (v : V) : pot v 2 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))))))
theorem le_F3 (v : V) : pot v 3 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))))
theorem le_F4 (v : V) : pot v 4 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))))
theorem le_F5 (v : V) : pot v 5 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))
theorem le_F6 (v : V) : pot v 6 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))
theorem le_F7 (v : V) : pot v 7 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))
theorem le_F8 (v : V) : pot v 8 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
theorem le_F9 (v : V) : pot v 9 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
theorem le_F10 (v : V) : pot v 10 ≤ F v := le_max_of_le_left (le_max_right _ _)
theorem le_F11 (v : V) : pot v 11 ≤ F v := le_max_right _ _

theorem le_F (v : V) (i : Fin 12) : pot v i ≤ F v := by
  fin_cases i
  exacts [le_F0 v, le_F1 v, le_F2 v, le_F3 v, le_F4 v, le_F5 v, le_F6 v, le_F7 v, le_F8 v, le_F9 v, le_F10 v, le_F11 v]

theorem F_le (v : V) (t : ℤ) (h0 : pot v 0 ≤ t) (h1 : pot v 1 ≤ t) (h2 : pot v 2 ≤ t) (h3 : pot v 3 ≤ t) (h4 : pot v 4 ≤ t) (h5 : pot v 5 ≤ t) (h6 : pot v 6 ≤ t) (h7 : pot v 7 ≤ t) (h8 : pot v 8 ≤ t) (h9 : pot v 9 ≤ t) (h10 : pot v 10 ≤ t) (h11 : pot v 11 ≤ t) : F v ≤ t :=
  max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11

theorem F_le_all (v : V) (t : ℤ) (h : ∀ i, pot v i ≤ t) : F v ≤ t :=
  F_le v t (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11)

theorem max_ex {v : V} {a b : ℤ} (ha : ∃ i, a = pot v i) (hb : ∃ i, b = pot v i) :
    ∃ i, max a b = pot v i := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

theorem exists_F (v : V) : ∃ i, F v = pot v i :=
  max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (⟨0, rfl⟩) ⟨1, rfl⟩) ⟨2, rfl⟩) ⟨3, rfl⟩) ⟨4, rfl⟩) ⟨5, rfl⟩) ⟨6, rfl⟩) ⟨7, rfl⟩) ⟨8, rfl⟩) ⟨9, rfl⟩) ⟨10, rfl⟩) ⟨11, rfl⟩

/-- A statement about every vertex class follows from the statements about each class. -/
theorem cls (P : Fin 9 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 9 × Fin 9 × ℤ × ℤ) (j : Fin 12) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 12, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 9 × Fin 9 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 9 × Fin 9 × ℤ × ℤ) (j : Fin 12) :
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
theorem farkas (x y : ℤ) (s : Fin 9) (a1 b1 a2 b2 a3 b3 i0 : Fin 12) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
adjacent to i, the fields k1, k2, m1, m2, m0, mj of entry i * 12 + j give the facts pot k1 ≤ pot i,
pot k2 ≤ pot i, 11 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 6153514510546089696350449531801932646386933464319361705125654343105642361232625456683284851188390798458564828264848377930454013901964038557304216383317950564178532973319005455284282503749140133708986454541121041512544635283522292636812711392251121088317790174959510499388837468313665638394464336632363310701484168018062177148558070372209543021119456637716122633379999272277215082138346121552406841775129221469449416789673287541175689729068751572161655284505835283630154149376660394862784923727281245654058674348025203449591308104471319684248985395100629897083886131990527219754665915446131627634888972157310509070936476164171539529799369064965898500986147052218240505157445811967850965284820144158534442544478719070454085600516436134095160576562735674829462712264984961145029409382392912300473710254626829008468316466040545810694938219860515266385221319802601855200332235136017962622245965721037862666740592509600947607068787228799948876173926156596959657944782066918307139900315829994303892130402515860170808824617790674625230332647517606390361615433033904421465034794367505772771985131389739416887016526606754168148266484912778070999965755827307849814426909263346495258497618390835585038330697144613283870565990945651659628066500143970227374813046833790292511355990748013438959616 5 ((i * 12 + j) * 6 + f)

def fd (i j : Fin 12) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 12) : Fin 12 := ⟨fdN i.val j.val 0 % 12, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 12) : Fin 12 := ⟨fdN i.val j.val 1 % 12, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 12) : ℤ := fd i j 2

def fm2 (i j : Fin 12) : ℤ := fd i j 3

def fm0 (i j : Fin 12) : ℤ := fd i j 4

def fmj (i j : Fin 12) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 12 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 11893730683933113775218432551079256605655040 4 p

def dstv (p : ℕ) : ℕ := tgetN 10307536397740787220671445593679585496565585 4 p

def dxv (p : ℕ) : ℕ := tgetN 1575351643976943097089 2 p

def dyv (p : ℕ) : ℕ := tgetN 1944213266868343231749 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 7060577732587153591955034177979499420439733967742186111535618315589732275207279193157811823419696891230606875512942030886819695201502223601274838877365836343787731127061183107880801094631628903780521497854652761404328404208859728668166438631184495333945294193451993849211633275914014321200778845752138267833709396212527762862722900309873689729149182414017670234903533695736547512666854976476855686745335409441938243786826839446514613056441472963927837325191084080224724949082094027623958394802512669924877996865542002551 4 (p * 12 + j)

def dlv (p : ℕ) (j : Fin 12) : ℤ := (dlvN p j.val : ℤ) - 8

theorem dlv_neg (p : ℕ) (j : Fin 12) (h : dlvN p j.val + 1 ≤ 8) : dlv p j ≤ -1 := by
  unfold dlv
  omega

theorem dlv_le (p : ℕ) (j : Fin 12) (c : ℕ) (h : dlvN p j.val + 1 ≤ c + 8) : dlv p j ≤ (c : ℤ) - 1 := by
  unfold dlv
  omega

/-- The next and the previous facet around the growth polygon. -/
def nxt (i : Fin 12) : Fin 12 := ⟨(i.val + 1) % 12, Nat.mod_lt _ (by norm_num)⟩

def prv (i : Fin 12) : Fin 12 := ⟨(i.val + 11) % 12, Nat.mod_lt _ (by norm_num)⟩

/-- The facets i and j are not equal and not adjacent sides of the growth polygon. -/
def nonadj (i j : Fin 12) : Prop := j ≠ i ∧ j ≠ nxt i ∧ j ≠ prv i

instance : DecidableRel nonadj := fun i j => by unfold nonadj; infer_instance

/-- The x and y parts of the far certificate of (i, j) cancel, in natural numbers (Ac = AcN - 8). -/
def farXYN (i j : ℕ) : Bool :=
  (fdN i j 2 * AcN (fdN i j 0 % 12) + fdN i j 3 * AcN (fdN i j 1 % 12) + fdN i j 5 * AcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * AcN i + fdN i j 5 * AcN j) &&
    (fdN i j 2 * BcN (fdN i j 0 % 12) + fdN i j 3 * BcN (fdN i j 1 % 12) + fdN i j 5 * BcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * BcN i + fdN i j 5 * BcN j)

/-- The constants of the far certificate of (i, j) at class s add up to a positive number. -/
def farCN (s i j : ℕ) : Bool :=
  Nat.blt ((fdN i j 2 + fdN i j 3 + fdN i j 4) * CcN s i + fdN i j 5 * (CcN s j + 1))
    (fdN i j 2 * CcN s (fdN i j 0 % 12) + fdN i j 3 * CcN s (fdN i j 1 % 12) + fdN i j 5 * CcN s i +
      fdN i j 4 * 19)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 12 || j == (i + 11) % 12

def farOK : Bool := (List.range 12).all fun i => (List.range 12).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 9).all fun s => (List.range 12).all fun i => (List.range 12).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 36).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 12).all fun j =>
      dlvN p j + 1 * AcN j + 8 * dxv p + 1 * BcN j + 8 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 16 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 9) (i j : Fin 12) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (11 - Cc s i)

/-- Beyond F = 10, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 9) (i j : Fin 12) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 10 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 11 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
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

/-- Descent rules beyond F = 10, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 10 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 1494295831170967784527684048097307355229593465776915189964925519324082642297752698443054281792698303230203292811261567796318781017663019083603484175490630627451222390951671271220735072845820654406925547402965901540363045963315709058739962741642090581620053934336164995731924213134314177071519727475019747899593736651768602052142939329922364850172693737798866000968968196258392207389450064594256713254596408369819248769624250853646988812245630113691880281414886967008473711948055224042242984503100061161911862588890522590922110284873096595353676843232436104797781498243736317794843076267170869530826302381745499970125375427005666549016167915428278527432137806814094094175737303950254113832542400265876969622939484007189960419269047717885777572967880506785586759393755393586164768135689882391896222165063064040832115903210686126346871386474184349818265683109385684459214607949387849273355185515335092945022419391416885749308481460529969727219530308312474987353732379414501460711149216514519981340255890244094233677661196196648754555165849390185425851403748245903382329563672323969871288114078417366703767826847199166658781537486656327854516162565695581152189077494770873682693793886426711419378245596363270025954690196101164789087337148108357771820224698169025029637185821786053811825110382585286147497228386364517988174168593312836420021260151955860071211465587040320
  | 1 => 1494295831602467474400511524939612184806096891549311117658722313830341907251934503788894252499228188925931544598676214103250507932918540918761662771117835374801841192811797216701973899243488191100060644536804346718353118165735640864255434271018785726143486737383200042321509882727590463446179686958350365697817054114063564809435817259266199875209692531781911062445848673720912047769253694228979708279169124290157252191940285217349249036945492412802363372553906959387960868590141963798355973801429069892065749977497475327192356079963398576283445136443476633472505973083278808485235033177686376186194259056610004045948394425277590024525691442145402272836326910389244557929475395231981682380506275722646964934093491196822899276700443078435669540848793221493858639892167102050612087522904533868498975365194944821745708890398601825021739010435457009125908634736123127755413602051293256535860906128922247619065456395344246759142631899599772271093640718224942937463868384091150858433362466880062638520074716749205455667618716815048111235275793986030948112980497258113314485016437247598316043146436665195828932099627592161102144821825718574613966807201243432918409951041453743798211142292976609101364878107876973229978457584266843581731903350436300420439143247410677612974726580270637954531730824920932931003622574996952049078509747319199445437183552988745623714929342161600
  | 2 => 1494295831947667226298738186212098010231063771189449109688299070188359134583314260024104561821893271726774801540605667715370380309392349292438481689987651172271753306333008798915595972141146248414841302034929447295472011599357953371615838107399997999928315506390123040096739066269849044051836118888394000842320975435993721848431844729933054342298362632552723110366012902899039784419680763357058541813545282051353890600319578253199216833046301703074977436574372729643852995224559982856974944695346472211261626602844761330335282550753872053318923800716919236365966383489850968121098145727454553943112953986569095930741183740580043188436694200041403292565902455789457264270110249756010539807122477631894737292340431862783337437829339403178245586127112622951968433306744551849092591661504855966394732420672358198402124566367502135039875965896336095238385642916546399360076574928877359802569455529203806394378130366574801009323488429297535707701911623719080888746102106128739826197807113754703934151994154655758100508160677637979263206477180840333928628918424724646525359380713539386852830517069496323156113676754859907830882375671596951780771388579474585980462027193312228495199600652418309222366896961447499104966599979137486581160391745393845605587457008864750424549657636095589419664787267610188709078778864178345541539175025437627952662770603946160120356928798860480
  | 3 => 1494295832120267102247861328015384822453612727947789980737937637047087243980105718153262620711736327408739699149021110958811696764618888942141830867495313167370718196856956296325062921302255211532350994798821312312540555533144702185630309466289903489301679606470134539384599145077978510040539442795319390427582009328684384368640891370350389612338160455232390642641687061787666524923497057631182787532399561715730068399541056620794207813070861753185334541170666733629805973255301297010890824545531092954870481148539105665479885990337143278679278696176095750433709234323948339801633224841418035714704967441012144846427123723913947648698969617589461719856948986805145233394707998779249110581896273050478474208693239776068231082593478485946453509275294421276554611690928455360193812414567666108600823286843252820988081013138332638403238945635464996233678015041500893787610585905056663139861526595325903369567223627246901638719264596666281055392861201524257896961270641832848339364691987575494662542457829591646000772669533225816341757070127998841049094868843982977825308430651631446945684512044047129077619975262885979604917328482463585733635974655937579408424430348074870362277922029504970733036601366235948980404071154318210166363243580972750323708773494130278335145508287379464546133169638830502099419511110622491436160392757597307166466259330132246582976276235036480
  | 4 => 1494295832465466854146107611621958446898710641464471722837214770764543462773688634411471415174689917391155807360168400994738580422221275320431763210517862054565954387381060536015993271304897621885883562824475312680122730856149703368508404865307732849469894621746686682732579369053601496826678414811787500219798406026881861893513899661984268706665552650948734542054661394101598641648708957233556279265882459917804010725466370796536670817418907585688402209471165433006937089781231480577329314721752868458813507043681874231263001027354703819697607308873460766211292035274209714795282284271192215744804443087113850979438668354788212749966819944208037550988006787529784111261967881238146821651307256710145649862903531949095340781821790597041300785091101991966355179584266372154809179147186180631976303140810622550683566971894656977198977535803205404684150014322907537043060586964548562969692544812345084289767175475493642921540031354793000935342830396096573778021208205213354729907768090118060247619878673247635569308177933262379476798074419639473420527963210380633164546272521454720737387332098559817744776769704905176550756140395794801037632086050873261776490938910852981430965123970318684908237305526996518036670796632427044617378342078606037340517203271000735811689271296548872697037260488419503282141502715207429851008932800473801254104551224141094983583961017493440
  | 5 => 1494295832724366668069792324326888665232534076601983029411672621052635626868875821605166766675744596931715761166004299518030123047182921514067138456081355652767558962447154330091187553268579907191805883488036643900411421985248697708076785704420258730085383654142015750492449312384024380210615316208283250693013731147893517712937761122260211368921405534081030279945562144078215358272395133914484891896344481537569260651242553578035012711794085472717589443919325632961449889773130733134082266113612556805012473933921184511883815112213969493331800575833065896614798474040794892595410723703489722016179516186539719488479632443264567831455712155492329886384171030353091394810648814840685964348183921782067690229593344092031952246364068638649659742257932232770162531376352404169893538754714642837233884159088067654670430697959538002958395853507915039049910551008579351124605285058812349963362344031445807976097705096143419900291870011461013370081720346178972527973983735213538027039877540963303226892326411300592539222103184160074031170289269935267268624431009539015912101723040478322272519117061082818505427122660523248849621126675779266859330076187971574309768070815236023399293498244390689125817822997927247358037113479651661373332887581531373479242526974119068741356319580751770640837251502482959348035475481575566023454946047225112477355122192448320375611817089575360
  | 6 => 1494295833242166295917161749736749101900180946877005642560588321628819955059250195992521695203884885887727316089512500913790460064956229062528730631541447814477339798421904412805000131745410007846404228943397757172671875686800159492059375892255389563580598318948269856602567332629965679823344233222747310123207022070728220426755438484275432745964894139428406985634088309516021631298408086044121839015899889999512500495532021935824758653945711855841056398498967675113106656383206801624923375512123978883901650044852416848254242889863233618547471332440579426195718025148972960938252419569921520366240010722003086830323952535454560122581776179182181669593758657471102122800036574645158191109900038610248398186831895567232931148616141259394351359382167573532498207157627401546733599740103486800452371203654172556481721631226464279446423532777045522276687554560741506754221563601492834505841011034703478817836977205777829707782552407325846749680862872097668999263673578229808616924883333558818556280272563154338257074931627802862416937866714115370534983980641382625850025415561144341101982809214791795395729280556617882640569128508542064518126533555546480185245189327995008369382756195029953007316368918440074598928442973447707298988971341738227457143934294790797229625707716742604277870358534269223095772831744384961690005581373587322191128769369302115672363675069459520
  | 7 => 1494295833587366047815408033343322726345278860393687384659865455346276173852833112250766264105749316330647986635887656433369073239505097392349605040874795958065388784286531232171883709969430993700980509523116802334581124429939165103641054705817956148266187284594747314997022999242454919979035455388040552298805230933007769119744381811569734877281049309115768840228311727313795557417432266609746512158307725268639742026826955057431058895791534452515231207225707952703158093965271688839556804416292548424412805250183826487687108168661933597213356646470010948076276172343744383150207707165615644631909775679303404441728015138134346633558465337303892076034497201487120209648587646153883167802557474699824893097301984501096865570780301708073611100962088287773930340083039094796450823901405303293460218115571825530032328899902539627713378532773503539813845451452647125700058334816170828412085168340879146066146003753160586266551052025255293450193388602882796210126229794896273108926190110157642960788281146072489893436546945258188494914892180538081431178558496393460799602767525288597496858513391611134176587331009172557942209905860432829574726781225582236459207424804971341444135082931567628879722594519438107643531175194818653742385678158383511524984774049103666667757714265727040077152146204752279947877000043589549861877223936140015834969913049231538352945461697044545
  | 8 => 1494295833759965923764531175146609538567827817152028255709504022205004283249624570379888548556681531552108321909075234193158379826779531557260042245581327999893417449726501390370511176589305616730570862576068712863349085223733995366726377118822660790948706535189600850881865580317440891983568539681118016220706845886647178472745893508821246480142340550527053336601184111195973862869358324718902294698668715227042352174026533924096020458783593129222579343766731489661566878851578576880761784959742835767083093975010375272919275390721416572406895198426267735701998341564622991251490242236355218062740814166738389333271316074723178551103617388657542051043548642877829135028827577551535637906534540638356926949987416442277198111822364756828634219566223536110644418559668602878579518257796446674276002777454531593337595387029129067754576225943346775989580705142560057447847620284820842903111615448768978785722018954478042171039001473884039954199678318251821977366728643043045314261934485640221330276940456097376990819723821434881854431322896923661312029671515167527593056460950538385534993146240464534751422660434519716769143281749626009752116457268151988573783611357241189595880650042209772506180930698220791391393813209820174785379982054520538222958301898937424096253093988365677173467910367759209315207722193585546629857979087816755768368149384155910756888173828124480
  | _ => 0

def rd (s : Fin 9) (i : Fin 12) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 9) (i : Fin 12) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 9) (i : Fin 12) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 9) (i : Fin 12) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 9) (i : Fin 12) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 9) (i : Fin 12) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 9) (i : Fin 12) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 9) (i : Fin 12) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 36 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 10)
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
theorem far_cert (s : Fin 9) (i j : Fin 12) (hij : nonadj i j) : farCert s i j := by
  have hn : nearB i.val j.val = false := by
    obtain ⟨h1, h2, h3⟩ := hij
    have e1 : j.val ≠ i.val := fun h => h1 (Fin.ext h)
    have e2 : j.val ≠ (i.val + 1) % 12 := fun h => h2 (Fin.ext h)
    have e3 : j.val ≠ (i.val + 11) % 12 := fun h => h3 (Fin.ext h)
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

theorem edge_at (p : ℕ) (hp : p < 36) :
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

theorem edge_tab (p : ℕ) (hp : p < 36) :
    (E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ) := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h p hp).1

theorem point_contra (x y : ℤ) (s : Fin 9) (i : Fin 12) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 10)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 10 < pot (x, y, s) i) : False := by
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

/-- Beyond F = 10 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 9) (i : Fin 12) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 10 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
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
  · -- a corner point within F ≤ 10
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

theorem far_desc (v : V) (hF : 10 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 9) (a1 a2 a3 : Fin 12) (t l1 l2 l3 px py q lq : ℤ)
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

theorem near_box0 (x y : ℤ) (hF : F (x, y, 0) ≤ 10) : -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, 0) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 0 3 11 0 10 1 4 0 1 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 5 8 0 10 4 1 0 (-1) 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 2 11 0 10 4 1 0 0 1 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 7 10 0 10 4 1 0 0 (-1) 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg0 (x y : ℤ) : 0 ≤ F (x, y, 0) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 0) k).trans (show F (x, y, 0) ≤ -1 by omega)
  exact farkas_ub x y 0 5 11 0 (-1) 4 4 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box1 (x y : ℤ) (hF : F (x, y, 1) ≤ 10) : -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, 1) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 1 3 11 0 10 1 4 0 1 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 5 9 0 10 4 1 0 (-1) 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 2 11 0 10 4 1 0 0 1 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 7 11 0 10 4 1 0 0 (-1) 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg1 (x y : ℤ) : 0 ≤ F (x, y, 1) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 1) k).trans (show F (x, y, 1) ≤ -1 by omega)
  exact farkas_ub x y 1 5 11 0 (-1) 4 4 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box2 (x y : ℤ) (hF : F (x, y, 2) ≤ 10) : -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, 2) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 2 2 11 0 10 1 4 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 5 9 0 10 4 1 0 (-1) 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 2 11 0 10 4 1 0 0 1 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 7 11 0 10 4 1 0 0 (-1) 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg2 (x y : ℤ) : 0 ≤ F (x, y, 2) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 2) k).trans (show F (x, y, 2) ≤ -1 by omega)
  exact farkas_ub x y 2 5 11 0 (-1) 4 4 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box3 (x y : ℤ) (hF : F (x, y, 3) ≤ 10) : -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, 3) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 3 2 11 0 10 1 4 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 5 9 0 10 4 1 0 (-1) 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 2 11 0 10 4 1 0 0 1 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 7 11 0 10 4 1 0 0 (-1) 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg3 (x y : ℤ) : 0 ≤ F (x, y, 3) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 3) k).trans (show F (x, y, 3) ≤ -1 by omega)
  exact farkas_ub x y 3 5 11 0 (-1) 4 4 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box4 (x y : ℤ) (hF : F (x, y, 4) ≤ 10) : -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, 4) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 4 3 11 0 10 1 4 0 1 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 5 9 0 10 4 1 0 (-1) 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 2 11 0 10 4 1 0 0 1 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 7 11 0 10 4 1 0 0 (-1) 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg4 (x y : ℤ) : 0 ≤ F (x, y, 4) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 4) k).trans (show F (x, y, 4) ≤ -1 by omega)
  exact farkas_ub x y 4 5 11 0 (-1) 4 4 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box5 (x y : ℤ) (hF : F (x, y, 5) ≤ 10) : -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, 5) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 5 2 11 0 10 1 4 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 5 9 0 10 4 1 0 (-1) 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 2 11 0 10 4 1 0 0 1 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 7 10 0 10 4 1 0 0 (-1) 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg5 (x y : ℤ) : 0 ≤ F (x, y, 5) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 5) k).trans (show F (x, y, 5) ≤ -1 by omega)
  exact farkas_ub x y 5 5 11 0 (-1) 4 4 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box6 (x y : ℤ) (hF : F (x, y, 6) ≤ 10) : -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, 6) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 6 2 11 0 10 1 4 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 5 9 0 10 4 1 0 (-1) 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 2 11 0 10 4 1 0 0 1 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 7 10 0 10 4 1 0 0 (-1) 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg6 (x y : ℤ) : 0 ≤ F (x, y, 6) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 6) k).trans (show F (x, y, 6) ≤ -1 by omega)
  exact farkas_ub x y 6 5 11 0 (-1) 4 4 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box7 (x y : ℤ) (hF : F (x, y, 7) ≤ 10) : -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, 7) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 7 2 11 0 10 1 4 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 5 9 0 10 4 1 0 (-1) 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 2 11 0 10 4 1 0 0 1 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 7 11 0 10 4 1 0 0 (-1) 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg7 (x y : ℤ) : 0 ≤ F (x, y, 7) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 7) k).trans (show F (x, y, 7) ≤ -1 by omega)
  exact farkas_ub x y 7 5 11 0 (-1) 4 4 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box8 (x y : ℤ) (hF : F (x, y, 8) ≤ 10) : -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, 8) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 8 2 11 0 10 1 4 0 1 0 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 5 9 0 10 4 1 0 (-1) 0 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 2 11 0 10 4 1 0 0 1 4 15 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 8 7 11 0 10 4 1 0 0 (-1) 4 13 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg8 (x y : ℤ) : 0 ≤ F (x, y, 8) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 8) k).trans (show F (x, y, 8) ≤ -1 by omega)
  exact farkas_ub x y 8 5 11 0 (-1) 4 4 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

/-- Every vertex with F at most 10 lies in the cells |x| ≤ 3, |y| ≤ 3. -/
theorem near_box (x y : ℤ) (s : Fin 9) (hF : F (x, y, s) ≤ 10) :
    -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3 :=
  cls (fun s => F (x, y, s) ≤ 10 → -3 ≤ x ∧ x ≤ 3 ∧ -3 ≤ y ∧ y ≤ 3)
    (near_box0 x y) (near_box1 x y) (near_box2 x y) (near_box3 x y) (near_box4 x y) (near_box5 x y) (near_box6 x y) (near_box7 x y) (near_box8 x y) s hF

theorem F_nonneg (v : V) : 0 ≤ F v :=
  cls (fun s => 0 ≤ F (v.1, v.2.1, s)) (F_nonneg0 v.1 v.2.1) (F_nonneg1 v.1 v.2.1) (F_nonneg2 v.1 v.2.1) (F_nonneg3 v.1 v.2.1) (F_nonneg4 v.1 v.2.1) (F_nonneg5 v.1 v.2.1) (F_nonneg6 v.1 v.2.1) (F_nonneg7 v.1 v.2.1) (F_nonneg8 v.1 v.2.1) v.2.2

/-- For the cell (a - 3, b - 3) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 206613642455704179117735234046803333567690497582420498249080462058718773069424066431957864718010945030977296226710815327743311500385600498536951192511818347343909319177745610920199791184988801921002817532970172540222722363837127034703274865456848691368033101723734158804184454188088592007349877241254083294262120935814735663127799973344257798402198096851979211168478085972339928546443093228793386833707758786218251174729880775827586054781733552973941166600736388701893112463345981114573188599165329692389134321061797165771137681894630048755595087555413547060761094333470093060704277456915570503661207599820512959053189607098773071115251613828038255265797920378400311353636643593399031691215946458363931286822044291476872636911546085970966783757120369580504975933440 >>> (6 * ((a * 7 + b) * 9 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 3, b - 3) and class s, potential i plus
13 + 4 a + 4 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 12) : ℕ :=
  tgetN 83072939313 4 i.val * a + tgetN 96243593314323 4 i.val * b + tgetN 2423019908910628088852230855026929518066468418925546448328636484494309813916847790767330569544179255506682673591687190692495065094265111475682584403185401335373658 5 (s * 12 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)) (fnt a b s 8)) (fnt a b s 9)) (fnt a b s 10)) (fnt a b s 11)

theorem fnt_tab : ∀ s : Fin 9, ∀ i : Fin 12, (tgetN 83072939313 4 i.val : ℤ) = Ac i + 4 ∧
    (tgetN 96243593314323 4 i.val : ℤ) = Bc i + 4 ∧
    (tgetN 2423019908910628088852230855026929518066468418925546448328636484494309813916847790767330569544179255506682673591687190692495065094265111475682584403185401335373658 5 (s.val * 12 + i.val) : ℤ) = Cc s i - Ac i * 3 - Bc i * 3 + 13 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 9) (i : Fin 12) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 3, (b : ℤ) - 3, s) i + (13 + 4 * a + 4 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 9) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 3, (b : ℤ) - 3, s) + (13 + 4 * a + 4 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 10, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (4 + 4) 1 = FN + 4 dx' + 4 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 7).all fun a => (List.range 7).all fun b => (List.range 9).all fun s =>
    Nat.blt (23 + 4 * a + 4 * b) (FN a b s) || (a == 3 && b == 3 && s == 1) ||
      (Nat.blt (hint a b s) 36 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 8 ==
          FN a b s + 4 * dxv (hint a b s) + 4 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 10) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (x + 3).toNat (by omega) (y + 3).toNat (by omega) s.val s.isLt
  have ex : (((x + 3).toNat : ℕ) : ℤ) - 3 = x := by omega
  have ey : (((y + 3).toNat : ℕ) : ℤ) - 3 = y := by omega
  generalize (x + 3).toNat = a at h' ex
  generalize (y + 3).toNat = b at h' ey
  have fv := FN_eq a b s
  rw [ex, ey] at fv
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at h'
  rcases h' with (h1 | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨⟨⟨hlen, hs⟩, hdx⟩, hdy⟩, hfe⟩
  · have c1 := (Nat.cast_lt (α := ℤ)).mpr h1
    push_cast at c1
    omega
  · exfalso
    apply hv
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    have hs0 : s = 1 := Fin.ext (by rw [h3]; rfl)
    subst hx0 hy0 hs0
    rfl
  · obtain ⟨e1, e2, e3, e4⟩ := edge_tab _ hlen
    have he : E.getD (hint a b s.val) (0, 0, 0, 0) ∈ E := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    rw [← e2] at hfe
    generalize E.getD (hint a b s.val) (0, 0, 0, 0) = e at he e1 e2 e3 e4 hfe
    obtain ⟨s1, s2, dx, dy⟩ := e
    simp only at e1 e2 e3 e4 hfe
    have hs1 : s1 = s := Fin.ext (e1.trans hs)
    have ha := adj_of_mem _ he x y
    simp only at ha
    rw [hs1] at ha
    refine ⟨_, ha, ?_⟩
    have fw := FN_eq (a + dxv (hint a b s.val) - 1) (b + dyv (hint a b s.val) - 1) s2
    have cw1 : (((a + dxv (hint a b s.val) - 1 : ℕ) : ℤ)) - 3 = x + dx := by omega
    have cw2 : (((b + dyv (hint a b s.val) - 1 : ℕ) : ℤ)) - 3 = y + dy := by omega
    rw [cw1, cw2] at fw
    have cf := congrArg (Nat.cast : ℕ → ℤ) hfe
    push_cast at cf
    omega

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 10
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
from below, and for n ≥ 7 the other facets lie below by Farkas certificates (`cf1` .. `cf0`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`). So
each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 28 moves every quotient by an integer (`inner_shift`, `S_shift`).
The tables are fields of natural numbers (`ctab`), which the kernel reads in constant time. The
section lives in the namespace `Count`; `gf`, `recur`, `controls` and `a_step` (and `a_closed` for
a short period) are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T (a table entry plus its offset). -/
def ctabN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

def gcV (k : ℕ) : ℕ := ctabN 4095 1 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 12) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 83072939313 4 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 4

def Ap (i : Fin 12) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 96243593314323 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 4

def Bp (i : Fin 12) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 4757025 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 12) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 9003540 2 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 1

def be (i : Fin 12) : ℤ := beN i.val

theorem prim : ∀ i : Fin 12, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧
    al i * Ap i + be i * Bp i = 1 := by
  decide +kernel

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 12) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 12) : ℤ := Ac j * al i + Bc j * be i

theorem orient : ∀ i : Fin 12, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 9) (i : Fin 12) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 9) (i j : Fin 12) (c u : ℤ) :
    pot (par s i c u) j = ka i j * c + Dm i j * u + Cc s j := by
  simp only [pot, par, ka, Dm]
  ring

theorem par_inv (v : V) (i : Fin 12) :
    v = par v.2.2 i (Ap i * v.1 + Bp i * v.2.1) (be i * v.1 - al i * v.2.1) := by
  obtain ⟨x, y, s⟩ := v
  have hb := (prim i).2.2.2
  simp only [par, Prod.mk.injEq, and_true]
  constructor
  · linear_combination (-x) * hb
  · linear_combination (-y) * hb

theorem pot_lev (v : V) (i : Fin 12) : pot v i = gc i * (Ap i * v.1 + Bp i * v.2.1) + Cc v.2.2 i := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  simp only [pot]
  rw [h1, h2]
  ring

theorem par_inj (s : Fin 9) (i : Fin 12) (c : ℤ) : Function.Injective (par s i c) := by
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
theorem F_attained (v : V) : ∃ k : Fin 12, pot v k = F v := by
  by_contra hne
  have h : ∀ k, pot v k ≤ F v - 1 := fun k => by
    have h1 := le_F v k
    have h2 : pot v k ≠ F v := fun e => hne ⟨k, e⟩
    omega
  have := F_le v (F v - 1) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11)
  omega

/-- The first facet attaining the maximum. -/
noncomputable def fi (v : V) : Fin 12 := Fin.find (fun k => pot v k = F v) (F_attained v)

theorem fi_spec (v : V) : pot v (fi v) = F v ∧ ∀ j, j < fi v → pot v j < F v :=
  ⟨Fin.find_spec (F_attained v), fun j hj =>
    lt_of_le_of_ne (le_F v j) (Fin.find_min (F_attained v) hj)⟩

theorem fi_iff (v : V) (i : Fin 12) : fi v = i ↔ pot v i = F v ∧ ∀ j, j < i → pot v j < F v := by
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
theorem piece_iff (v : V) (i : Fin 12) (n : ℤ) :
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
(pot_i ≤ pot_j) plus cf0 times (7 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 337165563606425686463890222944371434863527184681070720143580029739948643248492015875784225618673761244934513095910826845571269484849512816834328906013086582046079922098432 4 k

def cf1N (k : ℕ) : ℤ := (cf1V k : ℤ)

def cf1 (i : Fin 12) (j : Fin 12) : ℤ := cf1N (j.val + 12 * i.val)

def cf2V (k : ℕ) : ℕ := ctabN 143985985509174877126576409800350367606765467121460068049540904129056787040081918209391199962432155846389039122418746829405676245938961937109719501991874110357278152829184 4 k

def cf2N (k : ℕ) : ℤ := (cf2V k : ℤ)

def cf2 (i : Fin 12) (j : Fin 12) : ℤ := cf2N (j.val + 12 * i.val)

def cf3V (k : ℕ) : ℕ := ctabN 128802192814480287068432308940769674366835700358190740863882080120734417843552476833928314001852718785336376316461309220648101603314910597714449700841726347679442667713792 4 k

def cf3N (k : ℕ) : ℤ := (cf3V k : ℤ)

def cf3 (i : Fin 12) (j : Fin 12) : ℤ := cf3N (j.val + 12 * i.val)

def cf0V (k : ℕ) : ℕ := ctabN 1033940027594388998288785416427613667960907264779615789404243781534265210875964664400 2 k

def cf0N (k : ℕ) : ℤ := (cf0V k : ℤ)

def cf0 (i : Fin 12) (j : Fin 12) : ℤ := cf0N (j.val + 12 * i.val)


/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 12) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The class constants Cc s i, packed for the kernel. -/
def cTV (k : ℕ) : ℕ := ctabN 11061337864621589970077222788424703061594796059098730416126728970724348701925983226883733627413796 3 k

def cTN (k : ℕ) : ℤ := (cTV k : ℤ) - 3

def cT (s : Fin 9) (i : Fin 12) : ℤ := cTN (i.val + 12 * s.val)

theorem cT_eq : ∀ s : Fin 9, ∀ i : Fin 12, cT s i = Cc s i := by
  decide +kernel

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 9) (i j : Fin 12) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (cT s h - cT s i + (if h < i then 1 else 0)) +
    cf2 i j * (cT s k - cT s i + (if k < i then 1 else 0)) + cf3 i j * (cT s i - cT s j) +
    cf0 i j * (7 - cT s i)

instance (i j : Fin 12) : Decidable (certG i j) := by
  unfold certG; infer_instance

theorem certG_ok : ∀ i j : Fin 12, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 12 || j == (i + 11) % 12

/-- certC in natural numbers, for the kernel: Cc = cTV - 3, the negative terms moved across; the
previous facet of i is (i + 11) % 12, the next one (i + 1) % 12. -/
def certNat (s i j : ℕ) : Bool :=
  Nat.blt ((cf1V (j + 12 * i) + cf2V (j + 12 * i) + cf0V (j + 12 * i)) * cTV (i + 12 * s) +
      cf3V (j + 12 * i) * cTV (j + 12 * s))
    (cf1V (j + 12 * i) * (cTV ((i + 11) % 12 + 12 * s) + (if (i + 11) % 12 < i then 1 else 0)) +
      cf2V (j + 12 * i) * (cTV ((i + 1) % 12 + 12 * s) + (if (i + 1) % 12 < i then 1 else 0)) +
      cf3V (j + 12 * i) * cTV (i + 12 * s) + cf0V (j + 12 * i) * 10)

def certOK : Bool :=
  (List.range 9).all fun s => (List.range 12).all fun i => (List.range 12).all fun j =>
    nearB i j || certNat s i j

theorem certOK_eq : certOK = true := by
  decide +kernel

theorem fin_prev : ∀ i : Fin 12, (i - 1).val = (i.val + 11) % 12 := by decide +kernel

theorem fin_next : ∀ i : Fin 12, (i + 1).val = (i.val + 1) % 12 := by decide +kernel

/-- The constant parts of the certificates hold in the integers: the natural-number check moved
across. -/
theorem certC_ok (s : Fin 9) (i j : Fin 12) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    certC s i j := by
  have a1 := fin_prev i
  have a2 := fin_next i
  have hn : nearB i.val j.val = false := by
    have n1 : j.val ≠ i.val := fun h => e2 (Fin.ext h)
    have n2 : j.val ≠ (i.val + 1) % 12 := fun h => e3 (Fin.ext (h.trans a2.symm))
    have n3 : j.val ≠ (i.val + 11) % 12 := fun h => e1 (Fin.ext (h.trans a1.symm))
    simp only [nearB, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨n1, n2⟩, n3⟩
  have hc := certOK_eq
  unfold certOK at hc
  simp only [List.all_eq_true, List.mem_range] at hc
  have hk := hc s.val s.isLt i.val i.isLt j.val j.isLt
  rw [hn, Bool.false_or] at hk
  simp only [certNat, Nat.blt_eq] at hk
  have ck := (Nat.cast_lt (α := ℤ)).mpr hk
  show 0 < cf1 i j * (cT s (i - 1) - cT s i + (if i - 1 < i then 1 else 0)) +
    cf2 i j * (cT s (i + 1) - cT s i + (if i + 1 < i then 1 else 0)) +
    cf3 i j * (cT s i - cT s j) + cf0 i j * (7 - cT s i)
  simp only [cf1, cf2, cf3, cf0, cf1N, cf2N, cf3N, cf0N, cT, cTN, Fin.lt_def, a1, a2]
  push_cast at ck ⊢
  ring_nf at ck ⊢
  linarith

theorem farkas4 (v : V) (h i k j : Fin 12) (e1 e2 r l1 l2 l3 l0 : ℤ)
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
def lev (s : Fin 9) (i : Fin 12) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 9) (i : Fin 12) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 9) (i j : Fin 12) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 9) (i : Fin 12) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 9) (i : Fin 12) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 9) (i j : Fin 12) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 9) (i : Fin 12) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 9) (i : Fin 12) (n u : ℤ) :
    lo s i n ≤ u ↔ Dm i (i + 1) * u ≤ Rb s i (i + 1) n := by
  have hd : 0 < -Dm i (i + 1) := by linarith [(orient i).2]
  rw [lo, neg_le, Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> linarith

theorem ka_self (i : Fin 12) : ka i i = gc i := by
  obtain ⟨h1, h2, -, hb⟩ := prim i
  rw [ka, h1, h2]
  linear_combination (gc i) * hb

theorem Dm_self (i : Fin 12) : Dm i i = 0 := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  rw [Dm, h1, h2]
  ring

theorem pot_par_self (s : Fin 9) (i : Fin 12) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 7 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 9) (i : Fin 12) (n u : ℤ) (hn : 7 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 7 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 3)) (1 * n + 3) ×ˢ
    (Finset.Icc (-(1 * n + 3)) (1 * n + 3) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 9, ∀ j : Fin 12, -3 ≤ Cc s j ∧ Cc s j ≤ 3 := by decide +kernel

/-- Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/
theorem box_pairs : 1 * Ac 5 + 1 * Ac 6 = 7 ∧ 1 * Bc 5 + 1 * Bc 6 = 0 ∧
    1 * Ac 0 + 1 * Ac 11 = (-7) ∧ 1 * Bc 0 + 1 * Bc 11 = 0 ∧
    1 * Ac 7 + 1 * Ac 8 = 0 ∧ 1 * Bc 7 + 1 * Bc 8 = 7 ∧
    1 * Ac 1 + 1 * Ac 2 = 0 ∧ 1 * Bc 1 + 1 * Bc 2 = (-7) := by
  decide +kernel

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 9) :
    7 * x ≤ 2 * F (x, y, s) + 6 ∧
    7 * (-x) ≤ 2 * F (x, y, s) + 6 ∧
    7 * y ≤ 2 * F (x, y, s) + 6 ∧
    7 * (-y) ≤ 2 * F (x, y, s) + 6 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 5 + 1 * pot (x, y, s) 6 =
      7 * x + 1 * Cc s 5 + 1 * Cc s 6 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 5
  have r0 := le_F (x, y, s) 6
  have k0 := Cbound s 5
  have l0 := Cbound s 6
  have e1 : 1 * pot (x, y, s) 0 + 1 * pot (x, y, s) 11 =
      7 * (-x) + 1 * Cc s 0 + 1 * Cc s 11 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 11
  have k1 := Cbound s 0
  have l1 := Cbound s 11
  have e2 : 1 * pot (x, y, s) 7 + 1 * pot (x, y, s) 8 =
      7 * y + 1 * Cc s 7 + 1 * Cc s 8 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 7
  have r2 := le_F (x, y, s) 8
  have k2 := Cbound s 7
  have l2 := Cbound s 8
  have e3 : 1 * pot (x, y, s) 1 + 1 * pot (x, y, s) 2 =
      7 * (-y) + 1 * Cc s 1 + 1 * Cc s 2 := by
    simp only [pot]; linear_combination x * p7 + y * p8
  have q3 := le_F (x, y, s) 1
  have r3 := le_F (x, y, s) 2
  have k3 := Cbound s 1
  have l3 := Cbound s 2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_Bx (v : V) (n : ℤ) (h : F v ≤ n) : v ∈ Bx n := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  have h0 := F_nonneg (x, y, s)
  simp only [Bx, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  omega

/-- The piece of the sphere F = n with class s and first maximal facet i. -/
noncomputable def PF (s : Fin 9) (i : Fin 12) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 9) (i : Fin 12) (n : ℤ) (hn : 7 ≤ n) :
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
def inner (s : Fin 9) (i : Fin 12) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 9) (i : Fin 12) (n : ℤ) (hn : 7 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 9 × Fin 12, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 9 × Fin 12, inner p.1 p.2 n

/-! Shifting n by 28 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 1041348455773926300 5 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 12) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 16557351571215 4 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 7

def mh (i : Fin 12) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 264917625139440 4 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 7

def mk (i : Fin 12) : ℤ := mkN i.val

theorem shift_ok : ∀ i : Fin 12, (28 : ℤ) = gc i * Lq i ∧
    28 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    28 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 9) (i : Fin 12) (n : ℤ) :
    inner s i (n + 28) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 28 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 28 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 28) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 28) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 28) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 1 = gc i * lgq i. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 9 × Fin 12, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 28) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

def lgqV (k : ℕ) : ℕ := ctabN 4095 1 k

def lgqN (k : ℕ) : ℤ := (lgqV k : ℤ)

def lgq (i : Fin 12) : ℤ := lgqN i.val

theorem lg_ok : ∀ i : Fin 12, (1 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_periodic (x q : ℤ) : Gs (x + 1 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 1 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (lgq r.2 * q) := by
    linear_combination q * lg_ok r.2
  rw [e, Int.add_mul_emod_self_left]

theorem mhk_nonneg : ∀ i : Fin 12, 0 ≤ mh i + mk i := by decide +kernel

/-- The growth of the piece with index c = i + 12 s, read by the kernel from the tables. -/
def gsN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 12) = 0 then mhN (c % 12) + mkN (c % 12) else 0

theorem gsN_eq (s : Fin 9) (i : Fin 12) (n : ℤ) :
    gsN (i.val + 12 * s.val) n = (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  have hi := i.isLt
  have h : (i.val + 12 * s.val) % 12 = i.val := by omega
  rw [gsN, h, ← cT_eq]
  rfl

def GsN (n : ℤ) : ℤ := ((List.range (9 * 12)).map fun c => gsN c n).sum

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uhV (k : ℕ) : ℕ := ctabN 4363141380 3 k

def uhN (k : ℕ) : ℤ := (uhV k : ℤ) - 2

def uh (i : Fin 12) : ℤ := uhN i.val

def dhV (k : ℕ) : ℕ := ctabN 149016164140935 4 k

def dhN (k : ℕ) : ℤ := (dhV k : ℤ)

def dh (i : Fin 12) : ℤ := dhN i.val

def ukV (k : ℕ) : ℕ := ctabN 34905131040 3 k

def ukN (k : ℕ) : ℤ := (ukV k : ℤ) - 2

def uk (i : Fin 12) : ℤ := ukN i.val

def dkV (k : ℕ) : ℕ := ctabN 132458812569720 4 k

def dkN (k : ℕ) : ℤ := (dkV k : ℤ)

def dk (i : Fin 12) : ℤ := dkN i.val

def vhV (k : ℕ) : ℕ := ctabN 686732261327867508491851174953934713020431192746152125784653901042051301104083218576975535349907 3 k

def vhN (k : ℕ) : ℤ := (vhV k : ℤ) - 3

def vh (s : Fin 9) (i : Fin 12) : ℤ := vhN (i.val + 12 * s.val)

def vkV (k : ℕ) : ℕ := ctabN 10899234652007960152061692618876174826382288373861759390533856789813914897417840672163897889334546 3 k

def vkN (k : ℕ) : ℤ := (vkV k : ℤ) - 2

def vk (s : Fin 9) (i : Fin 12) : ℤ := vkN (i.val + 12 * s.val)

def levT (s : Fin 9) (i : Fin 12) (n : ℤ) : ℤ := (n - cT s i) / gc i

def innerT (s : Fin 9) (i : Fin 12) (n : ℤ) : ℤ :=
  if (n - cT s i) % gc i = 0 then
    (uh i * levT s i n + vh s i) / dh i + (uk i * levT s i n + vk s i) / dk i + 1 else 0

theorem tab_facet : ∀ i : Fin 12, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧
    uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) := by
  decide +kernel

theorem tab_class : ∀ s : Fin 9, ∀ i : Fin 12,
    vh s i = cT s i - cT s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    vk s i = cT s i - cT s (i + 1) - (if i + 1 < i then 1 else 0) := by
  decide +kernel

theorem tab_ok (s : Fin 9) (i : Fin 12) : uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  obtain ⟨f1, f2, f3, f4⟩ := tab_facet i
  obtain ⟨c1, c2⟩ := tab_class s i
  simp only [cT_eq] at c1 c2
  exact ⟨f1, c1, f2, f3, c2, f4⟩

theorem inner_eq (s : Fin 9) (i : Fin 12) (n : ℤ) : inner s i n = innerT s i n := by
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
def ST (n : ℤ) : ℤ := ∑ p : Fin 9 × Fin 12, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The piece length with index c = i + 12 s, read by the kernel from the tables directly. -/
def innerN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 12) = 0 then
    (uhN (c % 12) * ((n - cTN c) / gcN (c % 12)) + vhN c) / dhN (c % 12) +
      (ukN (c % 12) * ((n - cTN c) / gcN (c % 12)) + vkN c) / dkN (c % 12) + 1
  else 0

theorem innerN_eq (s : Fin 9) (i : Fin 12) (n : ℤ) :
    innerN (i.val + 12 * s.val) n = innerT s i n := by
  have hi := i.isLt
  have h : (i.val + 12 * s.val) % 12 = i.val := by omega
  rw [innerN, h]
  rfl

theorem sum_range_list (f : ℕ → ℤ) (N : ℕ) :
    ∑ c ∈ Finset.range N, f c = ((List.range N).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

/-- The closed form over the indices of the pieces. -/
def STN (n : ℤ) : ℤ := ((List.range (9 * 12)).map fun c => innerN c n).sum

theorem ST_eq_STN (n : ℤ) : ST n = STN n := by
  rw [ST, STN, Fintype.sum_equiv finProdFinEquiv (fun q : Fin 9 × Fin 12 => innerT q.1 q.2 n)
    (fun c : Fin (9 * 12) => innerN c.val n) (fun q => (innerN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => innerN c n) (9 * 12), sum_range_list]

theorem Gs_eq_GsN (n : ℤ) : Gs n = GsN n := by
  rw [Gs, GsN, Fintype.sum_equiv finProdFinEquiv
    (fun q : Fin 9 × Fin 12 => if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)
    (fun c : Fin (9 * 12) => gsN c.val n) (fun q => (gsN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => gsN c n) (9 * 12), sum_range_list]

/-- The closed form's tables, packed: the steps, the values on one period from 1 and below 1. -/
def dtabV (k : ℕ) : ℕ := ctabN 85408124399592002833923182073250768244290316598691745183340 7 k

def tblV (k : ℕ) : ℕ := ctabN 85389298913437268525726330283262516381786848039842378613891 7 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 28. -/
def dv (t : ℕ) : ℕ := dtabV (t % 28)

/-- The sequence in closed form: b(n + 28) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 28) + tblV ((n - 1) % 28)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 28) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 28 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 28 - 1 = n - 1 + 28 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 28)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 28) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 28 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 28 - 1 = n - 1 + 28 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 28)]
  ring

/-- b on the residue class of 1 + j mod 28. -/
theorem b_res (k j : ℕ) (hj : j < 28) : b (28 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (28 * k + (1 + j) < 1) by omega),
    show 28 * k + (1 + j) - 1 = j + 28 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 28), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The growth of S over one period at each residue mod 1. -/
def GsT : List ℤ := [108]

theorem Gs_tab : ∀ r : ℕ, r < 1 → GsN (r : ℤ) = GsT.getD r 0 := by
  decide +kernel

/-- The growth of b over 28 terms is that of S, on one period of the residues. -/
theorem grow_base : ∀ t : ℕ, t < 28 → 1 * (dv t : ℤ) = GsT.getD ((1 + t) % 1) 0 := by
  decide +kernel

theorem grow (n : ℕ) (_hn : 1 ≤ n) : 1 * (dv (n - 1) : ℤ) = Gs n := by
  have h1 := grow_base ((n - 1) % 28) (Nat.mod_lt _ (by norm_num))
  have e1 : dv ((n - 1) % 28) = dv (n - 1) := by
    rw [dv, dv, Nat.mod_mod_of_dvd _ (by norm_num : 28 ∣ 28)]
  have e2 : (1 + (n - 1) % 28) % 1 = n % 1 := by omega
  rw [e1, e2, ← Gs_tab (n % 1) (Nat.mod_lt _ (by norm_num)), ← Gs_eq_GsN] at h1
  rw [h1]
  have e3 : (((n % 1 : ℕ) : ℤ) + 1 * ((n / 1 : ℕ) : ℤ)) = n := by omega
  rw [← e3, Gs_periodic]

/-- One kernel pass over n = 7, ..., 34: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 28 →
    ((List.range (9 * 12)).all fun c => decide (0 ≤ innerN c (7 + (r : ℤ)))) = true ∧
      STN (7 + (r : ℤ)) = b (7 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 7 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 9) (i : Fin 12) (n : ℤ) (hn : 7 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 7 + t := ⟨(n - 7).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 28
    · rw [inner_eq, ← innerN_eq]
      have hc : i.val + 12 * s.val < 9 * 12 := by
        have := i.isLt
        have := s.isLt
        omega
      exact of_decide_eq_true (List.all_eq_true.1 (period_ok t ht).1 _ (List.mem_range.2 hc))
    · have := ih (t - 28) (by omega) (by omega)
      have e : (7 : ℤ) + t = (7 + (t - 28 : ℕ)) + 28 := by
        push_cast [Nat.cast_sub (by omega : 28 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 7 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

theorem S_eq_b (n : ℕ) (hn : 7 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 35
    · obtain ⟨r, rfl⟩ : ∃ r, n = 7 + r := ⟨n - 7, by omega⟩
      rw [S_eq_ST, ST_eq_STN]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 28) (by omega) (by omega)
      have h2 := S_shift ((n - 28 : ℕ) : ℤ)
      have h3 := b_shift (n - 28) (by omega)
      have h4 := grow (n - 28) (by omega)
      rw [show n - 28 + 28 = n by omega] at h3
      rw [show ((n - 28 : ℕ) : ℤ) + 28 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 6 lie in the box -2 ≤ x ≤ 2, -2 ≤ y ≤ 2 (`small_box`), and
the kernel checks that those of the box are the 85 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 9) (h : F (x, y, s) ≤ 6) :
    -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 6, with their values of F. -/
def smallV : List (V × ℤ) :=
  [((0, 0, 1), 0), ((0, 0, 0), 1), ((0, 0, 2), 1), ((0, 0, 6), 1), (((-1), (-1), 7), 2), (((-1), (-1), 8), 2), (((-1), 0, 5), 2), ((0, (-1), 3), 2), ((0, (-1), 8), 2), ((0, 0, 3), 2), ((0, 0, 5), 2), ((0, 0, 7), 2), ((0, 0, 8), 2), (((-1), (-1), 2), 3), (((-1), (-1), 3), 3), (((-1), 0, 6), 3), ((0, (-1), 2), 3), ((0, (-1), 4), 3), ((0, (-1), 7), 3), ((0, 0, 4), 3), ((0, 1, 5), 3), ((0, 1, 6), 3), ((1, 0, 0), 3), ((1, 0, 4), 3), ((1, 1, 0), 3), (((-1), (-1), 1), 4), (((-1), (-1), 4), 4), (((-1), (-1), 5), 4), (((-1), 0, 1), 4), (((-1), 0, 7), 4), ((0, (-1), 1), 4), ((0, 1, 1), 4), ((1, (-1), 4), 4), ((1, 0, 1), 4), ((1, 0, 3), 4), ((1, 1, 1), 4), ((1, 1, 4), 4), (((-2), (-1), 5), 5), (((-2), (-1), 7), 5), (((-1), (-2), 8), 5), (((-1), (-1), 0), 5), (((-1), (-1), 6), 5), (((-1), 0, 0), 5), (((-1), 0, 2), 5), (((-1), 0, 8), 5), ((0, (-1), 0), 5), ((0, (-1), 5), 5), ((0, (-1), 6), 5), ((0, 1, 0), 5), ((0, 1, 2), 5), ((0, 1, 7), 5), ((1, (-1), 3), 5), ((1, 0, 2), 5), ((1, 0, 6), 5), ((1, 0, 8), 5), ((1, 1, 2), 5), ((1, 1, 3), 5), ((1, 1, 6), 5), (((-2), (-2), 7), 6), (((-2), (-2), 8), 6), (((-2), (-1), 2), 6), (((-2), (-1), 6), 6), (((-2), (-1), 8), 6), (((-2), 0, 5), 6), (((-1), (-2), 2), 6), (((-1), (-2), 3), 6), (((-1), (-2), 7), 6), (((-1), 0, 3), 6), (((-1), 1, 5), 6), (((-1), 1, 6), 6), ((0, (-2), 3), 6), ((0, (-2), 8), 6), ((0, 1, 3), 6), ((0, 1, 8), 6), ((1, (-1), 0), 6), ((1, (-1), 2), 6), ((1, (-1), 8), 6), ((1, 0, 5), 6), ((1, 0, 7), 6), ((1, 1, 5), 6), ((1, 1, 7), 6), ((1, 1, 8), 6), ((1, 2, 0), 6), ((1, 2, 6), 6), ((2, 1, 0), 6)]

def smallL : List V := smallV.map Prod.fst

theorem smallV_ok : (smallV.all fun q => decide (F q.1 = q.2)) = true := by
  decide +kernel

/-- The potentials, packed: Ac = ATV - 4, Bc = BTV - 4. -/
def ATV (k : ℕ) : ℕ := ctabN 83072939313 4 k

def ATN (k : ℕ) : ℤ := (ATV k : ℤ) - 4

def AT (i : Fin 12) : ℤ := ATN i.val

def BTV (k : ℕ) : ℕ := ctabN 96243593314323 4 k

def BTN (k : ℕ) : ℤ := (BTV k : ℤ) - 4

def BT (i : Fin 12) : ℤ := BTN i.val

theorem AB_eq : ∀ i : Fin 12, AT i = Ac i ∧ BT i = Bc i := by
  decide +kernel

/-- Some potential exceeds 6 at the box point ((a : ℤ) - 2, (b : ℤ) - 2, s), in natural
numbers: the negative terms moved across. -/
def bigNat (a b s : ℕ) : Bool :=
  (List.range 12).any fun i =>
    Nat.blt (9 + ATV i * 2 + 4 * a + BTV i * 2 + 4 * b)
      (ATV i * a + 8 + BTV i * b + 8 + cTV (i + 12 * s))

theorem big_pot (a b : ℕ) (s : Fin 9) (h : bigNat a b s.val = true) :
    (6 : ℤ) < F ((a : ℤ) - 2, (b : ℤ) - 2, s) := by
  obtain ⟨i, hi, hb⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hi
  have hl := (Nat.cast_lt (α := ℤ)).mpr (Nat.blt_eq.mp hb)
  have hp := le_F ((a : ℤ) - 2, (b : ℤ) - 2, s) ⟨i, hi⟩
  obtain ⟨eA, eB⟩ := AB_eq ⟨i, hi⟩
  have e3 := cT_eq s ⟨i, hi⟩
  simp only [pot] at hp
  rw [← eA, ← eB, ← e3] at hp
  simp only [AT, BT, ATN, BTN, cT, cTN] at hp
  push_cast at hl hp
  ring_nf at hl hp ⊢
  linarith

def smallOK : Bool :=
  (List.range 5).all fun a => (List.range 5).all fun b => (List.finRange 9).all fun s =>
    bigNat a b s.val || decide (((a : ℤ) - 2, (b : ℤ) - 2, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 6) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 2).toNat (by omega) (y + 2).toNat (by omega) s
  have ex : (((x + 2).toNat : ℕ) : ℤ) - 2 = x := by omega
  have ey : (((y + 2).toNat : ℕ) : ℤ) - 2 = y := by omega
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h1 | h1
  · have := big_pot _ _ s h1
    rw [ex, ey] at this
    omega
  · rw [ex, ey] at h1
    exact h1

theorem cnt_small (n : ℤ) (hn : n ≤ 6) :
    cnt n = (((smallV.filter (fun q => decide (q.2 = n))).map Prod.fst).toFinset).card := by
  rw [cnt, ← Set.ncard_coe_finset]
  congr 1
  ext v
  have hv := smallV_ok
  simp only [List.all_eq_true, decide_eq_true_eq] at hv
  simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (small_mem v (by omega))
    exact ⟨q, ⟨hq, by rw [← hv q hq]; exact h⟩, rfl⟩
  · rintro ⟨q, ⟨hq, h2⟩, rfl⟩
    rw [hv q hq]
    exact h2

/-- The small spheres in closed form. -/
theorem small_ok : ∀ n : ℕ, n < 7 →
    (((smallV.filter (fun q => decide (q.2 = (n : ℤ)))).map Prod.fst).toFinset).card = b n := by
  decide +kernel

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 7 are counted in
`smallL`, those from 7 on are S(n), and both agree with the closed form b (`a_eq_b`). The step
from n to n + 28, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f.
follow, their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 7 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 7 ∨ 7 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_ok n h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

theorem dconst_base : ∀ r : ℕ, r < 28 → dtabV r = 108 := by
  decide +kernel
theorem dv_const : ∀ t : ℕ, dv t = 108 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 28) = a(n) + 108 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 28) = a n + 108 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-- The steps and the values on one period, by the kernel. -/
theorem closed_vals : dv 0 = 108 ∧ tblV 0 = 3 ∧ dv 1 = 108 ∧ tblV 1 = 9 ∧ dv 2 = 108 ∧ tblV 2 = 12 ∧ dv 3 = 108 ∧ tblV 3 = 12 ∧ dv 4 = 108 ∧ tblV 4 = 21 ∧ dv 5 = 108 ∧ tblV 5 = 27 ∧ dv 6 = 108 ∧ tblV 6 = 24 ∧ dv 7 = 108 ∧ tblV 7 = 27 ∧ dv 8 = 108 ∧ tblV 8 = 39 ∧ dv 9 = 108 ∧ tblV 9 = 42 ∧ dv 10 = 108 ∧ tblV 10 = 36 ∧ dv 11 = 108 ∧ tblV 11 = 45 ∧ dv 12 = 108 ∧ tblV 12 = 57 ∧ dv 13 = 108 ∧ tblV 13 = 54 ∧ dv 14 = 108 ∧ tblV 14 = 51 ∧ dv 15 = 108 ∧ tblV 15 = 63 ∧ dv 16 = 108 ∧ tblV 16 = 72 ∧ dv 17 = 108 ∧ tblV 17 = 66 ∧ dv 18 = 108 ∧ tblV 18 = 69 ∧ dv 19 = 108 ∧ tblV 19 = 81 ∧ dv 20 = 108 ∧ tblV 20 = 84 ∧ dv 21 = 108 ∧ tblV 21 = 81 ∧ dv 22 = 108 ∧ tblV 22 = 87 ∧ dv 23 = 108 ∧ tblV 23 = 96 ∧ dv 24 = 108 ∧ tblV 24 = 96 ∧ dv 25 = 108 ∧ tblV 25 = 99 ∧ dv 26 = 108 ∧ tblV 26 = 105 ∧ dv 27 = 108 ∧ tblV 27 = 108 := by
  decide +kernel

/-- The closed form per residue of n mod 28, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (28 * k + 1) = 108 * k + 3 ∧
    a (28 * k + 2) = 108 * k + 9 ∧
    a (28 * k + 3) = 108 * k + 12 ∧
    a (28 * k + 4) = 108 * k + 12 ∧
    a (28 * k + 5) = 108 * k + 21 ∧
    a (28 * k + 6) = 108 * k + 27 ∧
    a (28 * k + 7) = 108 * k + 24 ∧
    a (28 * k + 8) = 108 * k + 27 ∧
    a (28 * k + 9) = 108 * k + 39 ∧
    a (28 * k + 10) = 108 * k + 42 ∧
    a (28 * k + 11) = 108 * k + 36 ∧
    a (28 * k + 12) = 108 * k + 45 ∧
    a (28 * k + 13) = 108 * k + 57 ∧
    a (28 * k + 14) = 108 * k + 54 ∧
    a (28 * k + 15) = 108 * k + 51 ∧
    a (28 * k + 16) = 108 * k + 63 ∧
    a (28 * k + 17) = 108 * k + 72 ∧
    a (28 * k + 18) = 108 * k + 66 ∧
    a (28 * k + 19) = 108 * k + 69 ∧
    a (28 * k + 20) = 108 * k + 81 ∧
    a (28 * k + 21) = 108 * k + 84 ∧
    a (28 * k + 22) = 108 * k + 81 ∧
    a (28 * k + 23) = 108 * k + 87 ∧
    a (28 * k + 24) = 108 * k + 96 ∧
    a (28 * k + 25) = 108 * k + 96 ∧
    a (28 * k + 26) = 108 * k + 99 ∧
    a (28 * k + 27) = 108 * k + 105 ∧
    a (28 * k + 28) = 108 * k + 108 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55⟩ := closed_vals
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 28 * k + 1 = 28 * k + (1 + 0) from rfl, b_res k 0 (by norm_num), c0, c1]
  · rw [show 28 * k + 2 = 28 * k + (1 + 1) from rfl, b_res k 1 (by norm_num), c2, c3]
  · rw [show 28 * k + 3 = 28 * k + (1 + 2) from rfl, b_res k 2 (by norm_num), c4, c5]
  · rw [show 28 * k + 4 = 28 * k + (1 + 3) from rfl, b_res k 3 (by norm_num), c6, c7]
  · rw [show 28 * k + 5 = 28 * k + (1 + 4) from rfl, b_res k 4 (by norm_num), c8, c9]
  · rw [show 28 * k + 6 = 28 * k + (1 + 5) from rfl, b_res k 5 (by norm_num), c10, c11]
  · rw [show 28 * k + 7 = 28 * k + (1 + 6) from rfl, b_res k 6 (by norm_num), c12, c13]
  · rw [show 28 * k + 8 = 28 * k + (1 + 7) from rfl, b_res k 7 (by norm_num), c14, c15]
  · rw [show 28 * k + 9 = 28 * k + (1 + 8) from rfl, b_res k 8 (by norm_num), c16, c17]
  · rw [show 28 * k + 10 = 28 * k + (1 + 9) from rfl, b_res k 9 (by norm_num), c18, c19]
  · rw [show 28 * k + 11 = 28 * k + (1 + 10) from rfl, b_res k 10 (by norm_num), c20, c21]
  · rw [show 28 * k + 12 = 28 * k + (1 + 11) from rfl, b_res k 11 (by norm_num), c22, c23]
  · rw [show 28 * k + 13 = 28 * k + (1 + 12) from rfl, b_res k 12 (by norm_num), c24, c25]
  · rw [show 28 * k + 14 = 28 * k + (1 + 13) from rfl, b_res k 13 (by norm_num), c26, c27]
  · rw [show 28 * k + 15 = 28 * k + (1 + 14) from rfl, b_res k 14 (by norm_num), c28, c29]
  · rw [show 28 * k + 16 = 28 * k + (1 + 15) from rfl, b_res k 15 (by norm_num), c30, c31]
  · rw [show 28 * k + 17 = 28 * k + (1 + 16) from rfl, b_res k 16 (by norm_num), c32, c33]
  · rw [show 28 * k + 18 = 28 * k + (1 + 17) from rfl, b_res k 17 (by norm_num), c34, c35]
  · rw [show 28 * k + 19 = 28 * k + (1 + 18) from rfl, b_res k 18 (by norm_num), c36, c37]
  · rw [show 28 * k + 20 = 28 * k + (1 + 19) from rfl, b_res k 19 (by norm_num), c38, c39]
  · rw [show 28 * k + 21 = 28 * k + (1 + 20) from rfl, b_res k 20 (by norm_num), c40, c41]
  · rw [show 28 * k + 22 = 28 * k + (1 + 21) from rfl, b_res k 21 (by norm_num), c42, c43]
  · rw [show 28 * k + 23 = 28 * k + (1 + 22) from rfl, b_res k 22 (by norm_num), c44, c45]
  · rw [show 28 * k + 24 = 28 * k + (1 + 23) from rfl, b_res k 23 (by norm_num), c46, c47]
  · rw [show 28 * k + 25 = 28 * k + (1 + 24) from rfl, b_res k 24 (by norm_num), c48, c49]
  · rw [show 28 * k + 26 = 28 * k + (1 + 25) from rfl, b_res k 25 (by norm_num), c50, c51]
  · rw [show 28 * k + 27 = 28 * k + (1 + 26) from rfl, b_res k 26 (by norm_num), c52, c53]
  · rw [show 28 * k + 28 = 28 * k + (1 + 27) from rfl, b_res k 27 (by norm_num), c54, c55]

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 3, 9, 12, 12, 21, 27, 24, 27, 39, 42, 36, 45, 57, 54, 51, 63, 72, 66, 69, 81, 84, 81, 87, 96, 96, 99, 105, 108, 111, 117, 120, 120, 129, 135, 132, 135, 147, 150, 144, 153, 165, 162, 159, 171, 180, 174, 177, 189, 192] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The steps satisfy the recurrence, on one period of the residues. -/
theorem drec_base : ∀ t : ℕ, t < 28 → (dv (t + 10) : ℤ) = (dv (t + 9) : ℤ) - (dv (t + 8) : ℤ) + (dv (t + 7) : ℤ) + (dv (t + 3) : ℤ) - (dv (t + 2) : ℤ) + (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  decide +kernel

theorem drec (t : ℕ) : (dv (t + 10) : ℤ) = (dv (t + 9) : ℤ) - (dv (t + 8) : ℤ) + (dv (t + 7) : ℤ) + (dv (t + 3) : ℤ) - (dv (t + 2) : ℤ) + (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 28 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 2, e 3, e 7, e 8, e 9, e 10]
  exact drec_base (t % 28) (Nat.mod_lt _ (by norm_num))

/-- The recurrence on its first 28 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 28 → (b (q + 11) : ℤ) = b (q + 10) - b (q + 9) + b (q + 8) + b (q + 4) - b (q + 3) + b (q + 2) - b (q + 1) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 11) : ℤ) = b (q + 10) - b (q + 9) + b (q + 8) + b (q + 4) - b (q + 3) + b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 28 ∨ 28 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 28 := ⟨q - 28, by omega⟩
      have h0 : (b (v + 11) : ℤ) = b (v + 10) - b (v + 9) + b (v + 8) + b (v + 4) - b (v + 3) + b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have s1 : b (v + 29) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (by omega)
        rw [show v + 1 + 28 = v + 29 by omega,
          show v + 1 - 1 = v + 0 by omega] at h
        exact h
      have s2 : b (v + 30) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (by omega)
        rw [show v + 2 + 28 = v + 30 by omega,
          show v + 2 - 1 = v + 1 by omega] at h
        exact h
      have s3 : b (v + 31) = b (v + 3) + dv (v + 2) := by
        have h := b_step (v + 3) (by omega)
        rw [show v + 3 + 28 = v + 31 by omega,
          show v + 3 - 1 = v + 2 by omega] at h
        exact h
      have s4 : b (v + 32) = b (v + 4) + dv (v + 3) := by
        have h := b_step (v + 4) (by omega)
        rw [show v + 4 + 28 = v + 32 by omega,
          show v + 4 - 1 = v + 3 by omega] at h
        exact h
      have s8 : b (v + 36) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (by omega)
        rw [show v + 8 + 28 = v + 36 by omega,
          show v + 8 - 1 = v + 7 by omega] at h
        exact h
      have s9 : b (v + 37) = b (v + 9) + dv (v + 8) := by
        have h := b_step (v + 9) (by omega)
        rw [show v + 9 + 28 = v + 37 by omega,
          show v + 9 - 1 = v + 8 by omega] at h
        exact h
      have s10 : b (v + 38) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (by omega)
        rw [show v + 10 + 28 = v + 38 by omega,
          show v + 10 - 1 = v + 9 by omega] at h
        exact h
      have s11 : b (v + 39) = b (v + 11) + dv (v + 10) := by
        have h := b_step (v + 11) (by omega)
        rw [show v + 11 + 28 = v + 39 by omega,
          show v + 11 - 1 = v + 10 by omega] at h
        exact h
      have hd := drec v
      show (b (v + 39) : ℤ) = b (v + 38) - b (v + 37) + b (v + 36) + b (v + 32) - b (v + 31) + b (v + 30) - b (v + 29)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 10 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 7) - a (n - 8) + a (n - 9) - a (n - 10) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
  rw [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega, show q + 11 - 3 = q + 8 by omega, show q + 11 - 7 = q + 4 by omega, show q + 11 - 8 = q + 3 by omega, show q + 11 - 9 = q + 2 by omega, show q + 11 - 10 = q + 1 by omega]
  simp only [a_eq_b]
  exact b_recur q

/-- The coefficients of the g.f. below 11, by the kernel. -/
theorem gf_base : ∀ n : ℕ, n < 11 → 1 * (b n : ℤ) - 1 * (if 1 ≤ n then (b (n - 1) : ℤ) else 0) + 1 * (if 2 ≤ n then (b (n - 2) : ℤ) else 0) - 1 * (if 3 ≤ n then (b (n - 3) : ℤ) else 0) - 1 * (if 7 ≤ n then (b (n - 7) : ℤ) else 0) + 1 * (if 8 ≤ n then (b (n - 8) : ℤ) else 0) - 1 * (if 9 ≤ n then (b (n - 9) : ℤ) else 0) + 1 * (if 10 ≤ n then (b (n - 10) : ℤ) else 0) = (if n = 0 then (1 : ℤ) else 0) + (if n = 1 then (1 : ℤ) else 0) * 2 + (if n = 2 then (1 : ℤ) else 0) * 7 + (if n = 3 then (1 : ℤ) else 0) * 5 + (if n = 4 then (1 : ℤ) else 0) * 6 + (if n = 5 then (1 : ℤ) else 0) * 12 + (if n = 6 then (1 : ℤ) else 0) * 6 + (if n = 7 then (1 : ℤ) else 0) * 5 + (if n = 8 then (1 : ℤ) else 0) * 7 + (if n = 9 then (1 : ℤ) else 0) * 2 + (if n = 10 then (1 : ℤ) else 0) * 1 := by
  decide +kernel

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - X ^ 9 + X ^ 8 - X ^ 7 - X ^ 3 + X ^ 2 - X + 1) =
      X ^ 10 + 2 * X ^ 9 + 7 * X ^ 8 + 5 * X ^ 7 + 6 * X ^ 6 + 12 * X ^ 5 + 6 * X ^ 4 + 5 * X ^ 3 + 7 * X ^ 2 + 2 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * (X ^ 10 - X ^ 9 + X ^ 8 - X ^ 7 - X ^ 3 + X ^ 2 - X + 1) = C 1 * A - C 1 * (A * X ^ 1) + C 1 * (A * X ^ 2) - C 1 * (A * X ^ 3) - C 1 * (A * X ^ 7) + C 1 * (A * X ^ 8) - C 1 * (A * X ^ 9) + C 1 * (A * X ^ 10) := by
    simp only [map_one]
    ring
  have e2 : (X ^ 10 + 2 * X ^ 9 + 7 * X ^ 8 + 5 * X ^ 7 + 6 * X ^ 6 + 12 * X ^ 5 + 6 * X ^ 4 + 5 * X ^ 3 + 7 * X ^ 2 + 2 * X + 1 : ℚ⟦X⟧) = C 1 + X ^ 1 * C 2 + X ^ 2 * C 7 + X ^ 3 * C 5 + X ^ 4 * C 6 + X ^ 5 * C 12 + X ^ 6 * C 6 + X ^ 7 * C 5 + X ^ 8 * C 7 + X ^ 9 * C 2 + X ^ 10 * C 1 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 11 with hn | hn
  · have h := congrArg (fun z : ℤ => (z : ℚ)) (gf_base n hn)
    push_cast at h
    linarith
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    have h : (b (q + 11) : ℤ) = b (q + 10) - b (q + 9) + b (q + 8) + b (q + 4) - b (q + 3) + b (q + 2) - b (q + 1) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega, show q + 11 - 3 = q + 8 by omega, show q + 11 - 7 = q + 4 by omega, show q + 11 - 8 = q + 3 by omega, show q + 11 - 9 = q + 2 by omega, show q + 11 - 10 = q + 1 by omega, show 1 ≤ q + 11 by omega, show 2 ≤ q + 11 by omega, show 3 ≤ q + 11 by omega, show 7 ≤ q + 11 by omega, show 8 ≤ q + 11 by omega, show 9 ≤ q + 11 by omega, show 10 ≤ q + 11 by omega, show ¬ q + 11 = 0 by omega, show ¬ q + 11 = 1 by omega, show ¬ q + 11 = 2 by omega, show ¬ q + 11 = 3 by omega, show ¬ q + 11 = 4 by omega, show ¬ q + 11 = 5 by omega, show ¬ q + 11 = 6 by omega, show ¬ q + 11 = 7 by omega, show ¬ q + 11 = 8 by omega, show ¬ q + 11 = 9 by omega, show ¬ q + 11 = 10 by omega, if_true, if_false]
    linear_combination (1) * hq

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - X ^ 9 + X ^ 8 - X ^ 7 - X ^ 3 + X ^ 2 - X + 1) =
      X ^ 10 + 2 * X ^ 9 + 7 * X ^ 8 + 5 * X ^ 7 + 6 * X ^ 6 + 12 * X ^ 5 + 6 * X ^ 4 + 5 * X ^ 3 + 7 * X ^ 2 + 2 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 10 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 7) - a (n - 8) + a (n - 9) - a (n - 10) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 3, 9, 12, 12, 21, 27, 24, 27, 39, 42, 36, 45, 57, 54, 51, 63, 72, 66, 69, 81, 84, 81, 87, 96, 96, 99, 105, 108, 111, 117, 120, 120, 129, 135, 132, 135, 147, 150, 144, 153, 165, 162, 159, 171, 180, 174, 177, 189, 192] := Count.controls

/-- The step a(n + 28) = a(n) + 108 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 28) = a n + 108 := Count.a_step n hn

/-- The closed form per residue of n mod 28, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (28 * k + 1) = 108 * k + 3 ∧
    a (28 * k + 2) = 108 * k + 9 ∧
    a (28 * k + 3) = 108 * k + 12 ∧
    a (28 * k + 4) = 108 * k + 12 ∧
    a (28 * k + 5) = 108 * k + 21 ∧
    a (28 * k + 6) = 108 * k + 27 ∧
    a (28 * k + 7) = 108 * k + 24 ∧
    a (28 * k + 8) = 108 * k + 27 ∧
    a (28 * k + 9) = 108 * k + 39 ∧
    a (28 * k + 10) = 108 * k + 42 ∧
    a (28 * k + 11) = 108 * k + 36 ∧
    a (28 * k + 12) = 108 * k + 45 ∧
    a (28 * k + 13) = 108 * k + 57 ∧
    a (28 * k + 14) = 108 * k + 54 ∧
    a (28 * k + 15) = 108 * k + 51 ∧
    a (28 * k + 16) = 108 * k + 63 ∧
    a (28 * k + 17) = 108 * k + 72 ∧
    a (28 * k + 18) = 108 * k + 66 ∧
    a (28 * k + 19) = 108 * k + 69 ∧
    a (28 * k + 20) = 108 * k + 81 ∧
    a (28 * k + 21) = 108 * k + 84 ∧
    a (28 * k + 22) = 108 * k + 81 ∧
    a (28 * k + 23) = 108 * k + 87 ∧
    a (28 * k + 24) = 108 * k + 96 ∧
    a (28 * k + 25) = 108 * k + 96 ∧
    a (28 * k + 26) = 108 * k + 99 ∧
    a (28 * k + 27) = 108 * k + 105 ∧
    a (28 * k + 28) = 108 * k + 108 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - X ^ 9 + X ^ 8 - X ^ 7 - X ^ 3 + X ^ 2 - X + 1) =
      X ^ 10 + 2 * X ^ 9 + 7 * X ^ 8 + 5 * X ^ 7 + 6 * X ^ 6 + 12 * X ^ 5 + 6 * X ^ 4 + 5 * X ^ 3 + 7 * X ^ 2 + 2 * X + 1 ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 7) - a (n - 8) + a (n - 9) - a (n - 10) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a310319

theorem OMA.solution : type_of% @OMA.S_oeis_a310319.main :=
  OMA.S_oeis_a310319.conjecture
