import OMAStatements.S_oeis_a312943
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A312943.

Method: an explicit distance certificate. Every vertex outside the origin cell lies on one of the
rays through the vertices of the growth polygon or in one of the open cones between them, and is
written as base + k T + j U with a base from a finite list. The certificate gives the distance of
each code as v + L (k + j). A Boolean checker, evaluated by the kernel, verifies that every
neighbour of a coded vertex has a code of value at most one more, that every coded vertex other
than the base vertex has a neighbour of value exactly one less, and that codes are injective. So
the ball of radius n is the image of the codes of value at most n, and the coordination sequence
is a sum of explicit quasi-linear counts, which satisfies both conjectures.
The certificate data was produced by a script written with the help of an AI agent (Claude Code).
-/

namespace GalCert

/-- A target code given by affine forms in two free variables `k1 j1`. -/
structure Tgt where
  r : ℕ
  b : ℕ
  ka : ℕ
  kb : ℕ
  kc : ℕ
  ja : ℕ
  jb : ℕ
  jc : ℕ
  e : ℕ

def Tgt.dflt : Tgt := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

structure Base (m : ℕ) where
  x : ℤ
  y : ℤ
  i : Fin m
  v : ℕ
  out : List (List Tgt)
  pred : List Tgt

structure Region (m : ℕ) where
  kind : ℕ
  Tx : ℤ
  Ty : ℤ
  Ux : ℤ
  Uy : ℤ
  tests : List (ℤ × ℤ × ℤ)
  px : ℤ
  py : ℤ
  pc : ℤ
  pM : ℤ
  qx : ℤ
  qy : ℤ
  qc : ℤ
  qM : ℤ
  bases : List (Base m)

structure Cfg (m : ℕ) where
  adj : Fin m → List (ℤ × ℤ × Fin m)
  x0 : ℤ × ℤ × Fin m
  L : ℕ
  regs : List (Region m)
  certs : List (List (List (Bool × ℕ × ℕ)))
  r0 : ℕ
  b0 : ℕ

variable {m : ℕ} [NeZero m]

def Base.dflt : Base m := ⟨0, 0, 0, 0, [], []⟩
def Region.dflt : Region m := ⟨0, 0, 0, 0, 0, [], 0, 0, 0, 0, 0, 0, 0, 0, []⟩
def edflt : ℤ × ℤ × Fin m := (0, 0, 0)

def nbrs (adj : Fin m → List (ℤ × ℤ × Fin m)) (v : ℤ × ℤ × Fin m) : Finset (ℤ × ℤ × Fin m) :=
  ((adj v.2.2).map (fun d => (v.1 + d.1, v.2.1 + d.2.1, d.2.2))).toFinset

def ball (adj : Fin m → List (ℤ × ℤ × Fin m)) (x0 : ℤ × ℤ × Fin m) : ℕ → Finset (ℤ × ℤ × Fin m)
  | 0 => {x0}
  | n + 1 => ball adj x0 n ∪ (ball adj x0 n).biUnion (nbrs adj)

def sh (p d : ℤ × ℤ × Fin m) : ℤ × ℤ × Fin m := (p.1 + d.1, p.2.1 + d.2.1, d.2.2)

namespace Cfg
variable (C : Cfg m)

def reg (r : ℕ) : Region m := C.regs.getD r Region.dflt
def bas (r b : ℕ) : Base m := (C.reg r).bases.getD b Base.dflt

def dec (r b k j : ℕ) : ℤ × ℤ × Fin m :=
  ((C.bas r b).x + (k : ℤ) * (C.reg r).Tx + (j : ℤ) * (C.reg r).Ux,
   (C.bas r b).y + (k : ℤ) * (C.reg r).Ty + (j : ℤ) * (C.reg r).Uy, (C.bas r b).i)

def val (r b k j : ℕ) : ℕ := (C.bas r b).v + C.L * (k + j)

def Valid (r b k j : ℕ) : Prop :=
  r < C.regs.length ∧ b < (C.reg r).bases.length ∧ (1 ≤ (C.reg r).kind ∨ k = 0) ∧
    (2 ≤ (C.reg r).kind ∨ j = 0)

def ncases (kind : ℕ) : ℕ := if kind = 0 then 1 else if kind = 1 then 2 else 4

/-- Closure/Lipschitz rule check for source base `B` in region `R`, edge `d`, case `(kk, jj)`. -/
def okOut (R : Region m) (B : Base m) (d : ℤ × ℤ × Fin m) (kk jj : ℕ) (t : Tgt) : Bool :=
  let R' := C.reg t.r
  let B' := C.bas t.r t.b
  decide (t.r < C.regs.length) && decide (t.b < R'.bases.length) &&
  (decide (1 ≤ R'.kind) || (t.ka == 0 && t.kb == 0 && t.kc == 0)) &&
  (decide (2 ≤ R'.kind) || (t.ja == 0 && t.jb == 0 && t.jc == 0)) &&
  decide ((t.ka : ℤ) * R'.Tx + (t.ja : ℤ) * R'.Ux = (kk : ℤ) * R.Tx) &&
  decide ((t.kb : ℤ) * R'.Tx + (t.jb : ℤ) * R'.Ux = (jj : ℤ) * R.Ux) &&
  decide (B'.x + (t.kc : ℤ) * R'.Tx + (t.jc : ℤ) * R'.Ux = B.x + d.1 + (kk : ℤ) * R.Tx + (jj : ℤ) * R.Ux) &&
  decide ((t.ka : ℤ) * R'.Ty + (t.ja : ℤ) * R'.Uy = (kk : ℤ) * R.Ty) &&
  decide ((t.kb : ℤ) * R'.Ty + (t.jb : ℤ) * R'.Uy = (jj : ℤ) * R.Uy) &&
  decide (B'.y + (t.kc : ℤ) * R'.Ty + (t.jc : ℤ) * R'.Uy = B.y + d.2.1 + (kk : ℤ) * R.Ty + (jj : ℤ) * R.Uy) &&
  decide (B'.i = d.2.2) &&
  decide (C.L * (t.ka + t.ja) ≤ C.L * kk) && decide (C.L * (t.kb + t.jb) ≤ C.L * jj) &&
  decide (B'.v + C.L * (t.kc + t.jc) ≤ B.v + C.L * (kk + jj) + 1)

/-- Descending rule check: the target code is a neighbour one step closer. -/
def okPred (R : Region m) (B : Base m) (kk jj : ℕ) (t : Tgt) : Bool :=
  let R' := C.reg t.r
  let B' := C.bas t.r t.b
  let d := (C.adj B'.i).getD t.e edflt
  decide (t.r < C.regs.length) && decide (t.b < R'.bases.length) &&
  decide (t.e < (C.adj B'.i).length) &&
  (decide (1 ≤ R'.kind) || (t.ka == 0 && t.kb == 0 && t.kc == 0)) &&
  (decide (2 ≤ R'.kind) || (t.ja == 0 && t.jb == 0 && t.jc == 0)) &&
  decide ((t.ka : ℤ) * R'.Tx + (t.ja : ℤ) * R'.Ux = (kk : ℤ) * R.Tx) &&
  decide ((t.kb : ℤ) * R'.Tx + (t.jb : ℤ) * R'.Ux = (jj : ℤ) * R.Ux) &&
  decide (B'.x + (t.kc : ℤ) * R'.Tx + (t.jc : ℤ) * R'.Ux + d.1 = B.x + (kk : ℤ) * R.Tx + (jj : ℤ) * R.Ux) &&
  decide ((t.ka : ℤ) * R'.Ty + (t.ja : ℤ) * R'.Uy = (kk : ℤ) * R.Ty) &&
  decide ((t.kb : ℤ) * R'.Ty + (t.jb : ℤ) * R'.Uy = (jj : ℤ) * R.Uy) &&
  decide (B'.y + (t.kc : ℤ) * R'.Ty + (t.jc : ℤ) * R'.Uy + d.2.1 = B.y + (kk : ℤ) * R.Ty + (jj : ℤ) * R.Uy) &&
  decide (d.2.2 = B.i) &&
  decide (C.L * (t.ka + t.ja) = C.L * kk) && decide (C.L * (t.kb + t.jb) = C.L * jj) &&
  decide (B'.v + C.L * (t.kc + t.jc) + 1 = B.v + C.L * (kk + jj))

def tst (f : ℤ × ℤ × ℤ) (x y : ℤ) : Prop := f.2.2 ≤ f.1 * x + f.2.1 * y

/-- Zone membership of a base, and invariance of the zone under the region's translations. -/
def okZone (R : Region m) (B : Base m) : Bool :=
  R.tests.all (fun f => decide (f.2.2 ≤ f.1 * B.x + f.2.1 * B.y) &&
    (decide (R.kind = 0) || decide (0 ≤ f.1 * R.Tx + f.2.1 * R.Ty)) &&
    (decide (R.kind ≤ 1) || decide (0 ≤ f.1 * R.Ux + f.2.1 * R.Uy)))

def okCoord (R : Region m) (B : Base m) : Bool :=
  (decide (R.kind = 0) ||
    (decide (R.pc ≤ R.px * B.x + R.py * B.y) && decide (R.px * B.x + R.py * B.y < R.pc + R.pM))) &&
  (decide (R.kind ≤ 1) ||
    (decide (R.qc ≤ R.qx * B.x + R.qy * B.y) && decide (R.qx * B.x + R.qy * B.y < R.qc + R.qM)))

def okRegCoord (R : Region m) : Bool :=
  (decide (R.kind = 0) || (decide (0 < R.pM) && decide (R.px * R.Tx + R.py * R.Ty = R.pM))) &&
  (decide (R.kind ≤ 1) || (decide (R.px * R.Ux + R.py * R.Uy = 0) && decide (0 < R.qM) &&
    decide (R.qx * R.Ux + R.qy * R.Uy = R.qM) && decide (R.qx * R.Tx + R.qy * R.Ty = 0)))

def ci (k j : ℕ) : ℕ := (if k = 0 then 0 else 1) + (if j = 0 then 0 else 2)
def kkOf (c : ℕ) : ℕ := c % 2
def jjOf (c : ℕ) : ℕ := c / 2

def okBase (r b : ℕ) : Bool :=
  let R := C.reg r
  let B := C.bas r b
  okZone R B && okCoord R B && decide (R.kind ≤ 2) &&
  (!decide (B.v = 0) || decide (C.dec r b 0 0 = C.x0)) &&
  (List.range (C.adj B.i).length).all (fun e => (List.range (ncases R.kind)).all (fun c =>
    C.okOut R B ((C.adj B.i).getD e edflt) (kkOf c) (jjOf c) ((B.out.getD e []).getD c Tgt.dflt))) &&
  (List.range (ncases R.kind)).all (fun c =>
    (decide (kkOf c = 0 ∧ jjOf c = 0 ∧ B.v = 0)) || C.okPred R B (kkOf c) (jjOf c) (B.pred.getD c Tgt.dflt)) &&
  (List.range R.bases.length).all (fun b2 =>
    decide (b2 = b) || !(decide ((C.bas r b2).x = B.x ∧ (C.bas r b2).y = B.y ∧ (C.bas r b2).i = B.i)))

def testOf (r : ℕ) (s : Bool) (r2 idx : ℕ) : ℤ × ℤ × ℤ :=
  (C.reg (if s then r2 else r)).tests.getD idx (0, 0, 0)

def okCert (r1 r2 : ℕ) (l : List (Bool × ℕ × ℕ)) : Bool :=
  decide ((l.map (fun t => (t.2.2 : ℤ) * (C.testOf r1 t.1 r2 t.2.1).1)).sum = 0) &&
  decide ((l.map (fun t => (t.2.2 : ℤ) * (C.testOf r1 t.1 r2 t.2.1).2.1)).sum = 0) &&
  decide (0 < (l.map (fun t => (t.2.2 : ℤ) * (C.testOf r1 t.1 r2 t.2.1).2.2)).sum)

def hasCert (r1 r2 : ℕ) : Bool :=
  C.okCert r1 r2 ((C.certs.getD r1 []).getD r2 [])

def check : Bool :=
  decide (0 < C.L) &&
  decide (C.r0 < C.regs.length) && decide (C.b0 < (C.reg C.r0).bases.length) &&
  decide ((C.bas C.r0 C.b0).v = 0) && decide (C.dec C.r0 C.b0 0 0 = C.x0) &&
  (List.range C.regs.length).all (fun r => okRegCoord (C.reg r) &&
    (List.range (C.reg r).bases.length).all (fun b => C.okBase r b)) &&
  (List.range C.regs.length).all (fun r1 => (List.range C.regs.length).all (fun r2 =>
    decide (r1 = r2) || C.hasCert r1 r2))

end Cfg
end GalCert
namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] (C : Cfg m)

theorem all_range {p : ℕ → Bool} {n : ℕ} (h : (List.range n).all p = true) {i : ℕ} (hi : i < n) :
    p i = true := by
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

theorem kk_ci (k j : ℕ) : kkOf (ci k j) = if k = 0 then 0 else 1 := by
  unfold kkOf ci; split_ifs <;> simp_all

theorem jj_ci (k j : ℕ) : jjOf (ci k j) = if j = 0 then 0 else 1 := by
  unfold jjOf ci; split_ifs <;> simp_all

theorem ci_lt {K k j : ℕ} (hK : K ≤ 2) (h1 : 1 ≤ K ∨ k = 0) (h2 : 2 ≤ K ∨ j = 0) :
    ci k j < ncases K := by
  unfold ci ncases; split_ifs <;> omega

theorem kk_eq (k : ℕ) : ((k : ℤ)) = ((if k = 0 then 0 else 1 : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ) +
    ((if k = 0 then 0 else 1 : ℕ) : ℤ) := by
  split_ifs with h
  · simp [h]
  · have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h
    push_cast [Nat.cast_sub this]; ring

theorem kk_eqN (k : ℕ) : k = (if k = 0 then 0 else 1) * (k - 1) + (if k = 0 then 0 else 1) := by
  split_ifs with h <;> omega

theorem aff_le {vB vB' L ka kb kc ja jb jc kk jj K1 J1 : ℕ} (h1 : L * (ka + ja) ≤ L * kk)
    (h2 : L * (kb + jb) ≤ L * jj) (h3 : vB' + L * (kc + jc) ≤ vB + L * (kk + jj) + 1) :
    vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) ≤
      vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) + 1 := by
  have e1 : vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) =
      (vB' + L * (kc + jc)) + K1 * (L * (ka + ja)) + J1 * (L * (kb + jb)) := by ring
  have e2 : vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) + 1 =
      (vB + L * (kk + jj) + 1) + K1 * (L * kk) + J1 * (L * jj) := by ring
  rw [e1, e2]
  exact Nat.add_le_add (Nat.add_le_add h3 (Nat.mul_le_mul_left _ h1)) (Nat.mul_le_mul_left _ h2)

theorem aff_eq {vB vB' L ka kb kc ja jb jc kk jj K1 J1 : ℕ} (h1 : L * (ka + ja) = L * kk)
    (h2 : L * (kb + jb) = L * jj) (h3 : vB' + L * (kc + jc) + 1 = vB + L * (kk + jj)) :
    vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) + 1 =
      vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) := by
  have e1 : vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) + 1 =
      (vB' + L * (kc + jc) + 1) + K1 * (L * (ka + ja)) + J1 * (L * (kb + jb)) := by ring
  have e2 : vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) =
      (vB + L * (kk + jj)) + K1 * (L * kk) + J1 * (L * jj) := by ring
  rw [e1, e2, h1, h2, h3]

structure Facts (C : Cfg m) : Prop where
  Lpos : 0 < C.L
  r0 : C.r0 < C.regs.length
  b0 : C.b0 < (C.reg C.r0).bases.length
  v0 : (C.bas C.r0 C.b0).v = 0
  d0 : C.dec C.r0 C.b0 0 0 = C.x0
  reg : ∀ r < C.regs.length, okRegCoord (C.reg r) = true
  base : ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, C.okBase r b = true
  cert : ∀ r1 < C.regs.length, ∀ r2 < C.regs.length, r1 ≠ r2 → C.hasCert r1 r2 = true

theorem facts (hc : C.check = true) : Facts C := by
  unfold check at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
  · intro r hr
    have := all_range h6 hr
    simp only [Bool.and_eq_true] at this
    exact this.1
  · intro r hr b hb
    have := all_range h6 hr
    simp only [Bool.and_eq_true] at this
    exact all_range this.2 hb
  · intro r1 h1' r2 h2' hne
    have := all_range (all_range h7 h1') h2'
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    exact this.resolve_left hne

section
variable {C}

theorem okBase_parts {r b : ℕ} (h : C.okBase r b = true) :
    okZone (C.reg r) (C.bas r b) = true ∧ okCoord (C.reg r) (C.bas r b) = true ∧ (C.reg r).kind ≤ 2 ∧
    ((C.bas r b).v = 0 → C.dec r b 0 0 = C.x0) ∧
    (∀ e < (C.adj (C.bas r b).i).length, ∀ c < ncases (C.reg r).kind,
      C.okOut (C.reg r) (C.bas r b) ((C.adj (C.bas r b).i).getD e edflt) (kkOf c) (jjOf c)
        (((C.bas r b).out.getD e []).getD c Tgt.dflt) = true) ∧
    (∀ c < ncases (C.reg r).kind, (kkOf c = 0 ∧ jjOf c = 0 ∧ (C.bas r b).v = 0) ∨
      C.okPred (C.reg r) (C.bas r b) (kkOf c) (jjOf c) ((C.bas r b).pred.getD c Tgt.dflt) = true) ∧
    (∀ b2 < (C.reg r).bases.length, (C.bas r b2).x = (C.bas r b).x → (C.bas r b2).y = (C.bas r b).y →
      (C.bas r b2).i = (C.bas r b).i → b2 = b) := by
  unfold okBase at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨hz, hco⟩, hk⟩, h0⟩, ho⟩, hp⟩, hd⟩ := h
  refine ⟨hz, hco, hk, ?_, ?_, ?_, ?_⟩
  · intro hv; rcases h0 with h0 | h0
    · exact absurd hv h0
    · exact h0
  · intro e he c hc
    exact all_range (all_range ho he) hc
  · intro c hc
    have := all_range hp hc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    exact this
  · intro b2 hb2 hx hy hi
    have := all_range hd hb2
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at this
    rcases this with h | h
    · exact h
    · exact absurd ⟨hx, hy, hi⟩ h

theorem out_sound (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j) {e : ℕ}
    (he : e < (C.adj (C.bas r b).i).length) :
    ∃ r' b' k' j', C.Valid r' b' k' j' ∧
      C.dec r' b' k' j' = sh (C.dec r b k j) ((C.adj (C.bas r b).i).getD e edflt) ∧
      C.val r' b' k' j' ≤ C.val r b k j + 1 := by
  obtain ⟨hr, hb, hk1, hj1⟩ := hv
  have F := facts C hc
  obtain ⟨-, -, hK, -, ho, -, -⟩ := okBase_parts (F.base r hr b hb)
  have hci := ci_lt hK hk1 hj1
  have h := ho e he (ci k j) hci
  set t := ((C.bas r b).out.getD e []).getD (ci k j) Tgt.dflt
  set d := (C.adj (C.bas r b).i).getD e edflt
  rw [kk_ci, jj_ci] at h
  unfold okOut at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr', hb'⟩, hK1⟩, hK2⟩, ex1⟩, ex2⟩, ex3⟩, ey1⟩, ey2⟩, ey3⟩, hi⟩, hv1⟩, hv2⟩, hv3⟩ := h
  refine ⟨t.r, t.b, t.ka * (k - 1) + t.kb * (j - 1) + t.kc, t.ja * (k - 1) + t.jb * (j - 1) + t.jc,
    ⟨hr', hb', ?_, ?_⟩, ?_, ?_⟩
  · obtain h | h := hK1
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · obtain h | h := hK2
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · have ek := kk_eq k
    have ej := kk_eq j
    set kk := (if k = 0 then 0 else 1 : ℕ)
    set jj := (if j = 0 then 0 else 1 : ℕ)
    unfold dec sh
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only
      push_cast
      rw [ek, ej]
      linear_combination ex3 + ((k - 1 : ℕ) : ℤ) * ex1 + ((j - 1 : ℕ) : ℤ) * ex2
    · simp only
      push_cast
      rw [ek, ej]
      linear_combination ey3 + ((k - 1 : ℕ) : ℤ) * ey1 + ((j - 1 : ℕ) : ℤ) * ey2
    · exact hi
  · have ek := kk_eqN k
    have ej := kk_eqN j
    set kk := (if k = 0 then 0 else 1 : ℕ)
    set jj := (if j = 0 then 0 else 1 : ℕ)
    unfold val
    have := aff_le (K1 := k - 1) (J1 := j - 1) hv1 hv2 hv3
    rw [← ek, ← ej] at this
    exact this

theorem pred_sound (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j)
    (hpos : 0 < C.val r b k j) :
    ∃ r' b' k' j', C.Valid r' b' k' j' ∧ C.val r' b' k' j' + 1 = C.val r b k j ∧
      C.dec r b k j ∈ nbrs C.adj (C.dec r' b' k' j') := by
  obtain ⟨hr, hb, hk1, hj1⟩ := hv
  have F := facts C hc
  obtain ⟨-, -, hK, -, -, hp, -⟩ := okBase_parts (F.base r hr b hb)
  have hci := ci_lt hK hk1 hj1
  have h := hp (ci k j) hci
  rw [kk_ci, jj_ci] at h
  rcases h with ⟨h1, h2, h3⟩ | h
  · exfalso
    unfold val at hpos
    split_ifs at h1 h2 with hk0 hj0 <;> simp_all
  set t := (C.bas r b).pred.getD (ci k j) Tgt.dflt
  unfold okPred at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr', hb'⟩, he⟩, hK1⟩, hK2⟩, ex1⟩, ex2⟩, ex3⟩, ey1⟩, ey2⟩, ey3⟩, hi⟩, hv1⟩, hv2⟩, hv3⟩ := h
  refine ⟨t.r, t.b, t.ka * (k - 1) + t.kb * (j - 1) + t.kc, t.ja * (k - 1) + t.jb * (j - 1) + t.jc,
    ⟨hr', hb', ?_, ?_⟩, ?_, ?_⟩
  · obtain h | h := hK1
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · obtain h | h := hK2
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · have ek := kk_eqN k
    have ej := kk_eqN j
    set kk := (if k = 0 then 0 else 1 : ℕ)
    set jj := (if j = 0 then 0 else 1 : ℕ)
    unfold val
    have := aff_eq (K1 := k - 1) (J1 := j - 1) hv1 hv2 hv3
    rw [← ek, ← ej] at this
    exact this
  · unfold nbrs
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨(C.adj (C.bas t.r t.b).i).getD t.e edflt, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he
    · have ek := kk_eq k
      have ej := kk_eq j
      set kk := (if k = 0 then 0 else 1 : ℕ)
      set jj := (if j = 0 then 0 else 1 : ℕ)
      unfold dec
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp only
        push_cast
        rw [ek, ej]
        linear_combination ex3 + ((k - 1 : ℕ) : ℤ) * ex1 + ((j - 1 : ℕ) : ℤ) * ex2
      · simp only
        push_cast
        rw [ek, ej]
        linear_combination ey3 + ((k - 1 : ℕ) : ℤ) * ey1 + ((j - 1 : ℕ) : ℤ) * ey2
      · exact hi

end
end Cfg
end GalCert
namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

theorem zone_sound (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j) :
    ∀ f ∈ (C.reg r).tests, f.2.2 ≤ f.1 * (C.dec r b k j).1 + f.2.1 * (C.dec r b k j).2.1 := by
  obtain ⟨hr, hb, hk1, hj1⟩ := hv
  have F := facts C hc
  obtain ⟨hz, -, -, -, -, -, -⟩ := okBase_parts (F.base r hr b hb)
  intro f hf
  unfold okZone at hz
  rw [List.all_eq_true] at hz
  have h := hz f hf
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have t1 : 0 ≤ (k : ℤ) * (f.1 * (C.reg r).Tx + f.2.1 * (C.reg r).Ty) := by
    rcases h1 with h1 | h1
    · rcases hk1 with h | h
      · omega
      · simp [h]
    · exact mul_nonneg (by positivity) h1
  have t2 : 0 ≤ (j : ℤ) * (f.1 * (C.reg r).Ux + f.2.1 * (C.reg r).Uy) := by
    rcases h2 with h2 | h2
    · rcases hj1 with h | h
      · omega
      · simp [h]
    · exact mul_nonneg (by positivity) h2
  unfold dec
  linarith

theorem cert_sum (x y : ℤ) (l : List (Bool × ℕ × ℕ)) (tf : Bool → ℕ → ℤ × ℤ × ℤ)
    (h : ∀ t ∈ l, (tf t.1 t.2.1).2.2 ≤ (tf t.1 t.2.1).1 * x + (tf t.1 t.2.1).2.1 * y) :
    (l.map (fun t => (t.2.2 : ℤ) * (tf t.1 t.2.1).2.2)).sum ≤
      x * (l.map (fun t => (t.2.2 : ℤ) * (tf t.1 t.2.1).1)).sum +
      y * (l.map (fun t => (t.2.2 : ℤ) * (tf t.1 t.2.1).2.1)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (List.mem_cons_self ..)
    have hl := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    have : (a.2.2 : ℤ) * (tf a.1 a.2.1).2.2 ≤ (a.2.2 : ℤ) * ((tf a.1 a.2.1).1 * x + (tf a.1 a.2.1).2.1 * y) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    nlinarith [this, hl]

theorem getD_test {l : List (ℤ × ℤ × ℤ)} {x y : ℤ}
    (h : ∀ f ∈ l, f.2.2 ≤ f.1 * x + f.2.1 * y) (i : ℕ) :
    (l.getD i (0, 0, 0)).2.2 ≤ (l.getD i (0, 0, 0)).1 * x + (l.getD i (0, 0, 0)).2.1 * y := by
  rcases lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; simp

theorem no_two_zones (hc : C.check = true) {r1 r2 : ℕ} (h1 : r1 < C.regs.length)
    (h2 : r2 < C.regs.length) (hne : r1 ≠ r2) (x y : ℤ)
    (z1 : ∀ f ∈ (C.reg r1).tests, f.2.2 ≤ f.1 * x + f.2.1 * y)
    (z2 : ∀ f ∈ (C.reg r2).tests, f.2.2 ≤ f.1 * x + f.2.1 * y) : False := by
  have F := facts C hc
  have hh := F.cert r1 h1 r2 h2 hne
  unfold hasCert okCert at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨⟨s1, s2⟩, s3⟩ := hh
  have := cert_sum x y ((C.certs.getD r1 []).getD r2 []) (fun s i => C.testOf r1 s r2 i) (by
    intro t _
    unfold testOf
    split_ifs
    · exact getD_test z2 _
    · exact getD_test z1 _)
  beta_reduce at this
  rw [s1, s2] at this
  linarith

theorem coord_unique {a a' c M : ℤ} {k k' : ℕ} (hM : 0 < M) (ha : c ≤ a) (ha' : a < c + M)
    (hb : c ≤ a') (hb' : a' < c + M) (h : a + k * M = a' + k' * M) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have : (k : ℤ) + 1 ≤ k' := by exact_mod_cast hl
    nlinarith
  · have : (k' : ℤ) + 1 ≤ k := by exact_mod_cast hl
    nlinarith

theorem dec_inj (hc : C.check = true) {r b k j r' b' k' j' : ℕ} (hv : C.Valid r b k j)
    (hv' : C.Valid r' b' k' j') (h : C.dec r b k j = C.dec r' b' k' j') :
    r = r' ∧ b = b' ∧ k = k' ∧ j = j' := by
  have F := facts C hc
  by_cases hr : r = r'
  · subst hr
    refine ⟨rfl, ?_⟩
    obtain ⟨hr, hb, hk1, hj1⟩ := hv
    obtain ⟨-, hb', hk1', hj1'⟩ := hv'
    obtain ⟨-, hco, hK, -, -, -, hd⟩ := okBase_parts (F.base r hr b hb)
    obtain ⟨-, hco', -, -, -, -, -⟩ := okBase_parts (F.base r hr b' hb')
    have hrc := F.reg r hr
    unfold okRegCoord at hrc
    unfold okCoord at hco hco'
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hrc hco hco'
    unfold dec at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hx, hy, hi⟩ := h
    have hkk : k = k' := by
      rcases hrc.1 with h0 | ⟨hM, hT⟩
      · rcases hk1 with h | h
        · omega
        · rcases hk1' with h' | h'
          · omega
          · omega
      · rcases hco.1 with h0 | ⟨p1, p2⟩
        · omega
        rcases hco'.1 with h0 | ⟨q1, q2⟩
        · omega
        have hU : (j : ℤ) * ((C.reg r).px * (C.reg r).Ux + (C.reg r).py * (C.reg r).Uy) =
            (j' : ℤ) * ((C.reg r).px * (C.reg r).Ux + (C.reg r).py * (C.reg r).Uy) := by
          rcases hrc.2 with h2 | ⟨⟨⟨hU0, -⟩, -⟩, -⟩
          · rcases hj1 with h | h
            · omega
            rcases hj1' with h' | h'
            · omega
            simp [h, h']
          · rw [hU0]; simp
        refine coord_unique hM p1 p2 q1 q2 ?_
        rw [← hT]
        have := congrArg (fun z => (C.reg r).px * z) hx
        have h2 := congrArg (fun z => (C.reg r).py * z) hy
        linear_combination this + h2 - hU
    subst hkk
    have hjj : j = j' := by
      rcases hrc.2 with h0 | ⟨⟨⟨hU0, hM⟩, hQ⟩, hT0⟩
      · rcases hj1 with h | h
        · omega
        · rcases hj1' with h' | h'
          · omega
          · omega
      · rcases hco.2 with h0 | ⟨p1, p2⟩
        · omega
        rcases hco'.2 with h0 | ⟨q1, q2⟩
        · omega
        refine coord_unique hM p1 p2 q1 q2 ?_
        rw [← hQ]
        have := congrArg (fun z => (C.reg r).qx * z) hx
        have h2 := congrArg (fun z => (C.reg r).qy * z) hy
        linear_combination this + h2 - (k : ℤ) * hT0 + (k : ℤ) * hT0
    subst hjj
    refine ⟨?_, rfl, rfl⟩
    exact (hd b' hb' (by linarith) (by linarith) hi.symm).symm
  · exfalso
    have z1 := zone_sound hc hv
    have z2 := zone_sound hc hv'
    rw [← h] at z2
    exact no_two_zones hc hv.1 hv'.1 hr _ _ z1 z2

theorem val_zero (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j)
    (h0 : C.val r b k j = 0) : C.dec r b k j = C.x0 := by
  have F := facts C hc
  obtain ⟨hr, hb, -, -⟩ := hv
  obtain ⟨-, -, -, hz, -, -, -⟩ := okBase_parts (F.base r hr b hb)
  unfold val at h0
  have hv0 : (C.bas r b).v = 0 := by omega
  have hkj : C.L * (k + j) = 0 := by omega
  rcases Nat.mul_eq_zero.mp hkj with h | h
  · exact absurd h (Nat.pos_iff_ne_zero.mp F.Lpos)
  · have hk : k = 0 := by omega
    have hj : j = 0 := by omega
    subst hk hj
    exact hz hv0

theorem mem_nbrs {adj : Fin m → List (ℤ × ℤ × Fin m)} {x y : ℤ × ℤ × Fin m} :
    y ∈ nbrs adj x ↔ ∃ e < (adj x.2.2).length, y = sh x ((adj x.2.2).getD e edflt) := by
  unfold nbrs sh
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hd
    exact ⟨e, he, by rw [List.getD_eq_getElem _ _ he]⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨_, by rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he, rfl⟩

theorem ball_iff (hc : C.check = true) (n : ℕ) (x : ℤ × ℤ × Fin m) :
    x ∈ ball C.adj C.x0 n ↔ ∃ r b k j, C.Valid r b k j ∧ C.val r b k j ≤ n ∧ C.dec r b k j = x := by
  have F := facts C hc
  induction n generalizing x with
  | zero =>
    simp only [ball, Finset.mem_singleton, Nat.le_zero]
    constructor
    · rintro rfl
      refine ⟨C.r0, C.b0, 0, 0, ⟨F.r0, F.b0, Or.inr rfl, Or.inr rfl⟩, ?_, F.d0⟩
      unfold val; rw [F.v0]; simp
    · rintro ⟨r, b, k, j, hv, h0, rfl⟩
      exact val_zero hc hv h0
  | succ n ih =>
    simp only [ball, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro (h | ⟨z, hz, hxz⟩)
      · obtain ⟨r, b, k, j, hv, hle, hd⟩ := (ih x).mp h
        exact ⟨r, b, k, j, hv, by omega, hd⟩
      · obtain ⟨r, b, k, j, hv, hle, rfl⟩ := (ih z).mp hz
        obtain ⟨e, he, rfl⟩ := mem_nbrs.mp hxz
        have he' : e < (C.adj (C.bas r b).i).length := he
        obtain ⟨r', b', k', j', hv', hd', hval⟩ := out_sound hc hv he'
        exact ⟨r', b', k', j', hv', by omega, hd'⟩
    · rintro ⟨r, b, k, j, hv, hle, rfl⟩
      rcases Nat.lt_or_ge n (C.val r b k j) with hlt | hge
      · right
        obtain ⟨r', b', k', j', hv', hval, hmem⟩ := pred_sound hc hv (by omega)
        exact ⟨C.dec r' b' k' j', (ih _).mpr ⟨r', b', k', j', hv', by omega, rfl⟩, hmem⟩
      · left
        exact (ih _).mpr ⟨r, b, k, j, hv, hge, rfl⟩

end Cfg
end GalCert
namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m]

def pcard (C : Cfg m) (r b n : ℕ) : ℕ :=
  if (C.reg r).kind = 0 then (if (C.bas r b).v = n then 1 else 0)
  else if (C.bas r b).v ≤ n ∧ C.L ∣ (n - (C.bas r b).v) then
    (if (C.reg r).kind = 1 then 1 else (n - (C.bas r b).v) / C.L + 1) else 0

def A (C : Cfg m) (n : ℕ) : ℕ :=
  ((List.range C.regs.length).map (fun r =>
    ((List.range (C.reg r).bases.length).map (fun b => C.pcard r b n)).sum)).sum

theorem emb_inj (r b : ℕ) : Function.Injective (fun p : ℕ × ℕ => (r, b, p.1, p.2)) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.2.2.1 h.2.2.2

def piece (C : Cfg m) (r b n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  if (C.reg r).kind = 0 then (if (C.bas r b).v = n then {(r, b, 0, 0)} else ∅)
  else if (C.bas r b).v ≤ n ∧ C.L ∣ (n - (C.bas r b).v) then
    (if (C.reg r).kind = 1 then {(r, b, (n - (C.bas r b).v) / C.L, 0)}
     else (Finset.HasAntidiagonal.antidiagonal ((n - (C.bas r b).v) / C.L) : Finset (ℕ × ℕ)).map ⟨_, emb_inj r b⟩)
  else ∅

def Sph (C : Cfg m) (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range C.regs.length).biUnion fun r =>
    (Finset.range (C.reg r).bases.length).biUnion fun b => C.piece r b n

variable {C : Cfg m}

theorem val_iff {v L s n : ℕ} (hL : 0 < L) :
    v + L * s = n ↔ v ≤ n ∧ L ∣ (n - v) ∧ s = (n - v) / L := by
  constructor
  · rintro rfl
    refine ⟨by omega, ⟨s, by omega⟩, ?_⟩
    rw [show v + L * s - v = L * s by omega, Nat.mul_div_cancel_left _ hL]
  · rintro ⟨h1, h2, rfl⟩
    rw [Nat.mul_div_cancel' h2]; omega

theorem mem_piece (hL : 0 < C.L) {r b n r' b' k j : ℕ} :
    (r', b', k, j) ∈ C.piece r b n ↔ r' = r ∧ b' = b ∧ (1 ≤ (C.reg r).kind ∨ k = 0) ∧
      (2 ≤ (C.reg r).kind ∨ j = 0) ∧ C.val r b k j = n := by
  unfold piece val
  by_cases h0 : (C.reg r).kind = 0
  · simp only [h0, if_true]
    by_cases h1 : (C.bas r b).v = n
    · simp only [h1, if_true, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨rfl, rfl, Or.inr rfl, Or.inr rfl, by simp⟩
      · rintro ⟨rfl, rfl, hk, hj, hv⟩
        have hk' : k = 0 := by omega
        have hj' : j = 0 := by omega
        exact ⟨rfl, rfl, hk', hj'⟩
    · simp only [h1, if_false, Finset.notMem_empty, false_iff]
      rintro ⟨rfl, rfl, hk, hj, hv⟩
      have hk' : k = 0 := by omega
      have hj' : j = 0 := by omega
      subst hk' hj'
      simp at hv
      exact h1 hv
  · simp only [h0, if_false]
    by_cases h1 : (C.bas r b).v ≤ n ∧ C.L ∣ (n - (C.bas r b).v)
    · simp only [h1, and_self, if_true]
      by_cases h2 : (C.reg r).kind = 1
      · simp only [h2, if_true, Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl, rfl, rfl⟩
          refine ⟨rfl, rfl, Or.inl (by omega), Or.inr rfl, ?_⟩
          rw [add_zero]
          exact (val_iff hL).mpr ⟨h1.1, h1.2, rfl⟩
        · rintro ⟨rfl, rfl, hk, hj, hv⟩
          have hj' : j = 0 := by omega
          subst hj'
          rw [add_zero] at hv
          exact ⟨rfl, rfl, ((val_iff hL).mp hv).2.2, rfl⟩
      · simp only [h2, if_false]
        rw [Finset.mem_map]
        constructor
        · rintro ⟨⟨p1, p2⟩, hp, he⟩
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
          simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl, rfl⟩ := he
          refine ⟨rfl, rfl, Or.inl (by omega), Or.inl (by omega), ?_⟩
          exact (val_iff hL).mpr ⟨h1.1, h1.2, hp⟩
        · rintro ⟨rfl, rfl, -, -, hv⟩
          exact ⟨(k, j), Finset.HasAntidiagonal.mem_antidiagonal.mpr ((val_iff hL).mp hv).2.2, rfl⟩
    · simp only [h1, if_false, Finset.notMem_empty, false_iff]
      rintro ⟨rfl, rfl, -, -, hv⟩
      have := (val_iff hL).mp hv
      exact h1 ⟨this.1, this.2.1⟩

theorem mem_Sph (hL : 0 < C.L) {n r b k j : ℕ} :
    (r, b, k, j) ∈ C.Sph n ↔ C.Valid r b k j ∧ C.val r b k j = n := by
  unfold Sph Valid
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨r', hr', b', hb', h⟩
    obtain ⟨rfl, rfl, hk, hj, hv⟩ := (mem_piece hL).mp h
    exact ⟨⟨hr', hb', hk, hj⟩, hv⟩
  · rintro ⟨⟨hr, hb, hk, hj⟩, hv⟩
    exact ⟨r, hr, b, hb, (mem_piece hL).mpr ⟨rfl, rfl, hk, hj, hv⟩⟩

theorem piece_fst (hL : 0 < C.L) {r b n : ℕ} {c : ℕ × ℕ × ℕ × ℕ} (h : c ∈ C.piece r b n) :
    c.1 = r ∧ c.2.1 = b := by
  obtain ⟨r', b', k, j⟩ := c
  have := (mem_piece hL).mp h
  exact ⟨this.1, this.2.1⟩

theorem card_piece (r b n : ℕ) : (C.piece r b n).card = C.pcard r b n := by
  unfold piece pcard
  split_ifs <;> simp

theorem lsum_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

theorem card_Sph (hL : 0 < C.L) (n : ℕ) : (C.Sph n).card = C.A n := by
  unfold Sph A
  rw [Finset.card_biUnion, lsum_range]
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finset.card_biUnion, lsum_range]
    · apply Finset.sum_congr rfl
      intro b _
      exact card_piece r b n
    · intro b1 _ b2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro c h1 h2
      exact hne ((piece_fst hL h1).2.symm.trans (piece_fst hL h2).2)
  · intro r1 _ r2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro c h1 h2
    simp only [Finset.mem_biUnion] at h1 h2
    obtain ⟨b1, -, h1⟩ := h1
    obtain ⟨b2, -, h2⟩ := h2
    exact hne ((piece_fst hL h1).1.symm.trans (piece_fst hL h2).1)

theorem ball_mono (n : ℕ) : ball C.adj C.x0 n ⊆ ball C.adj C.x0 (n + 1) := by
  intro x hx
  simp only [ball, Finset.mem_union]
  exact Or.inl hx

theorem sphere_eq (hc : C.check = true) (n : ℕ) :
    ball C.adj C.x0 (n + 1) \ ball C.adj C.x0 n =
      (C.Sph (n + 1)).image (fun c => C.dec c.1 c.2.1 c.2.2.1 c.2.2.2) := by
  have F := facts C hc
  ext x
  rw [Finset.mem_sdiff, Finset.mem_image, ball_iff hc, ball_iff hc]
  constructor
  · rintro ⟨⟨r, b, k, j, hv, hle, rfl⟩, hn⟩
    refine ⟨(r, b, k, j), (mem_Sph F.Lpos).mpr ⟨hv, ?_⟩, rfl⟩
    by_contra hne
    exact hn ⟨r, b, k, j, hv, by omega, rfl⟩
  · rintro ⟨⟨r, b, k, j⟩, hc', rfl⟩
    obtain ⟨hv, hval⟩ := (mem_Sph F.Lpos).mp hc'
    refine ⟨⟨r, b, k, j, hv, hval.le, rfl⟩, ?_⟩
    rintro ⟨r', b', k', j', hv', hle, hd⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := dec_inj hc hv' hv hd
    omega

theorem card_step (hc : C.check = true) (n : ℕ) :
    ((ball C.adj C.x0 (n + 1)).card : ℤ) - (ball C.adj C.x0 n).card = C.A (n + 1) := by
  have F := facts C hc
  have h1 := Finset.card_sdiff_add_card_eq_card (ball_mono (C := C) n)
  have h2 : (ball C.adj C.x0 (n + 1) \ ball C.adj C.x0 n).card = C.A (n + 1) := by
    rw [sphere_eq hc, Finset.card_image_of_injOn, card_Sph F.Lpos]
    rintro ⟨r, b, k, j⟩ h1 ⟨r', b', k', j'⟩ h2 hd
    obtain ⟨hv, -⟩ := (mem_Sph F.Lpos).mp h1
    obtain ⟨hv', -⟩ := (mem_Sph F.Lpos).mp h2
    obtain ⟨rfl, rfl, rfl, rfl⟩ := dec_inj hc hv hv' hd
    rfl
  omega

theorem pcard_rec (hL : 0 < C.L) {r b n : ℕ} (hv : (C.bas r b).v < n) :
    C.pcard r b (n + 2 * C.L) + C.pcard r b n = 2 * C.pcard r b (n + C.L) := by
  unfold pcard
  set v := (C.bas r b).v
  have e2 : n + 2 * C.L - v = (n - v) + C.L * 2 := by omega
  have e1 : n + C.L - v = (n - v) + C.L * 1 := by omega
  rw [e2, e1]
  have d2 : C.L ∣ (n - v) + C.L * 2 ↔ C.L ∣ (n - v) :=
    (Nat.dvd_add_left (Dvd.intro 2 rfl))
  have d1 : C.L ∣ (n - v) + C.L * 1 ↔ C.L ∣ (n - v) :=
    (Nat.dvd_add_left (Dvd.intro 1 rfl))
  have q2 : ((n - v) + C.L * 2) / C.L = (n - v) / C.L + 2 := by
    rw [Nat.add_mul_div_left _ _ hL]
  have q1 : ((n - v) + C.L * 1) / C.L = (n - v) / C.L + 1 := by
    rw [Nat.add_mul_div_left _ _ hL]
  simp only [d2, d1, q2, q1]
  split_ifs <;> omega

theorem A_rec (hc : C.check = true) {V : ℕ}
    (hV : ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, (C.bas r b).v ≤ V) {n : ℕ}
    (hn : V < n) : C.A (n + 2 * C.L) + C.A n = 2 * C.A (n + C.L) := by
  have F := facts C hc
  unfold A
  rw [← List.sum_map_add, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [List.mem_range] at hr
  rw [← List.sum_map_add, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro b hb
  rw [List.mem_range] at hb
  exact pcard_rec F.Lpos (lt_of_le_of_lt (hV r hr b hb) hn)

end Cfg

theorem zero_of_window {g : ℕ → ℤ} {L N : ℕ} (hL0 : 0 < L) (hrec : ∀ n, N ≤ n → g (n + 2 * L) + g n = 2 * g (n + L))
    (hw : ∀ n, N ≤ n → n < N + 2 * L → g n = 0) : ∀ n, N ≤ n → g n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n (N + 2 * L) with h | h
    · exact hw n hn h
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 * L := ⟨n - 2 * L, by omega⟩
      have h1 := hrec n' (by omega)
      rw [ih n' (by omega) (by omega), ih (n' + L) (by omega) (by omega)] at h1
      linarith

open PowerSeries in
noncomputable def polyOf : List ℤ → PowerSeries ℤ
  | [] => 0
  | c :: l => PowerSeries.C c + PowerSeries.X * polyOf l

def conv (a : ℕ → ℤ) : List ℤ → ℕ → ℤ
  | [], _ => 0
  | c :: l, 0 => c * a 0
  | c :: l, n + 1 => c * a (n + 1) + conv a l n

open PowerSeries in
theorem coeff_mul_polyOf (a : ℕ → ℤ) (l : List ℤ) (n : ℕ) :
    coeff n (mk a * polyOf l) = conv a l n := by
  induction l generalizing n with
  | nil => simp [polyOf, conv]
  | cons c l ih =>
    rw [polyOf, mul_add, mul_comm (mk a) (C c), mul_left_comm, map_add, coeff_C_mul, coeff_mk]
    cases n with
    | zero => simp [conv]
    | succ n => rw [coeff_succ_X_mul, ih]; simp [conv]

open PowerSeries in
theorem coeff_polyOf (l : List ℤ) (n : ℕ) : coeff n (polyOf l) = l.getD n 0 := by
  induction l generalizing n with
  | nil => simp [polyOf]
  | cons c l ih =>
    cases n with
    | zero => simp [polyOf]
    | succ n => rw [polyOf, map_add, coeff_C, coeff_succ_X_mul, ih]; simp

open PowerSeries in
theorem gf_of_conv (a : ℕ → ℤ) (dl pl : List ℤ) (h : ∀ n, conv a dl n = pl.getD n 0) :
    mk a * polyOf dl = polyOf pl := by
  ext n
  rw [coeff_mul_polyOf, coeff_polyOf, h]

end GalCert

namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

def vbound (C : Cfg m) (V : ℕ) : Bool :=
  (List.range C.regs.length).all (fun r =>
    (List.range (C.reg r).bases.length).all (fun b => decide ((C.bas r b).v ≤ V)))

theorem vbound_spec {V : ℕ} (h : C.vbound V = true) :
    ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, (C.bas r b).v ≤ V := by
  intro r hr b hb
  have := all_range (all_range h hr) hb
  simpa using this

theorem lin_rec (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (cs : List (ℤ × ℕ))
    (hs : ∀ p ∈ cs, 1 ≤ p.2) (n : ℕ) (hn : V ≤ n) :
    (cs.map fun p => p.1 * (C.A (n + 2 * C.L + p.2) : ℤ)).sum +
      (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum =
      2 * (cs.map fun p => p.1 * (C.A (n + C.L + p.2) : ℤ)).sum := by
  induction cs with
  | nil => simp
  | cons p cs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := ih (fun q hq => hs q (List.mem_cons_of_mem _ hq))
    have hp := hs p (List.mem_cons_self ..)
    have h2 := A_rec hc (vbound_spec hV) (n := n + p.2) (by omega)
    rw [show n + p.2 + 2 * C.L = n + 2 * C.L + p.2 by omega,
      show n + p.2 + C.L = n + C.L + p.2 by omega] at h2
    have h3 : (C.A (n + 2 * C.L + p.2) : ℤ) + C.A (n + p.2) = 2 * C.A (n + C.L + p.2) := by
      exact_mod_cast h2
    linear_combination h1 + p.1 * h3

theorem lin_zero (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (cs : List (ℤ × ℕ))
    (hs : ∀ p ∈ cs, 1 ≤ p.2)
    (hw : ∀ n < V + 2 * C.L, (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0) :
    ∀ n, (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0 := by
  have F := facts C hc
  intro n
  rcases Nat.lt_or_ge n (V + 2 * C.L) with h | h
  · exact hw n h
  · refine zero_of_window (g := fun n => (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum)
      (L := C.L) (N := V) F.Lpos (fun n hn => lin_rec hc hV cs hs n hn) (fun n _ h2 => hw n h2) n
      (by omega)

end Cfg
end GalCert

namespace GalCert

theorem conv_cs (a : ℕ → ℤ) (l : List ℤ) (k : ℕ) :
    conv a l (k + l.length) = ((List.range l.length).map fun i => l.getD i 0 * a (k + l.length - i)).sum := by
  induction l generalizing k with
  | nil => simp [conv]
  | cons c l ih =>
    rw [List.length_cons, show k + (l.length + 1) = (k + l.length) + 1 by omega, conv, ih,
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [List.getD_cons_zero, Nat.sub_zero, Function.comp_def, List.getD_cons_succ]
    congr 2
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    congr 2
    omega

def csOf (l : List ℤ) : List (ℤ × ℕ) := (List.range l.length).map fun i => (l.getD i 0, l.length - i)

theorem csOf_pos (l : List ℤ) : ∀ p ∈ csOf l, 1 ≤ p.2 := by
  intro p hp
  unfold csOf at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [List.mem_range] at hi
  simp only
  omega

namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

theorem gf_from (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (a : ℕ → ℤ)
    (ha : ∀ n, 1 ≤ n → a n = C.A n) (dl pl : List ℤ) (M : ℕ) (hM : dl.length ≤ M)
    (hP : pl.length ≤ M)
    (hw : ∀ n < V + 2 * C.L, ((csOf dl).map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0)
    (hsmall : ∀ n < M, conv a dl n = pl.getD n 0) :
    PowerSeries.mk a * polyOf dl = polyOf pl := by
  apply gf_of_conv
  intro n
  rcases Nat.lt_or_ge n M with h | h
  · exact hsmall n h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + dl.length := ⟨n - dl.length, by omega⟩
    rw [List.getD_eq_default _ _ (by omega), conv_cs]
    have hz := lin_zero hc hV (csOf dl) (csOf_pos dl) hw k
    unfold csOf at hz
    rw [List.map_map] at hz
    refine Eq.trans ?_ hz
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [ha _ (by omega), show k + dl.length - i = k + (dl.length - i) by omega]

end Cfg
end GalCert

namespace GalCert

def csOfS (l : List ℤ) (s : ℕ) : List (ℤ × ℕ) :=
  (List.range l.length).map fun i => (l.getD i 0, l.length - i + s)

theorem csOfS_pos (l : List ℤ) (s : ℕ) : ∀ p ∈ csOfS l s, 1 ≤ p.2 := by
  intro p hp
  unfold csOfS at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [List.mem_range] at hi
  simp only
  omega

namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

theorem gf_from2 (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (a : ℕ → ℤ)
    (ha : ∀ n, 1 ≤ n → a n = C.A n) (dl pl : List ℤ) (s M : ℕ) (hM : dl.length + s ≤ M)
    (hP : pl.length ≤ M)
    (hw : ∀ n < V + 2 * C.L, ((csOfS dl s).map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0)
    (hsmall : ∀ n < M, conv a dl n = pl.getD n 0) :
    PowerSeries.mk a * polyOf dl = polyOf pl := by
  apply gf_of_conv
  intro n
  rcases Nat.lt_or_ge n M with h | h
  · exact hsmall n h
  · obtain ⟨k, rfl⟩ : ∃ k, n = (k + s) + dl.length := ⟨n - s - dl.length, by omega⟩
    rw [List.getD_eq_default _ _ (by omega), conv_cs]
    have hz := lin_zero hc hV (csOfS dl s) (csOfS_pos dl s) hw k
    unfold csOfS at hz
    rw [List.map_map] at hz
    refine Eq.trans ?_ hz
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [ha _ (by omega), show k + s + dl.length - i = k + (dl.length - i + s) by omega]

end Cfg
end GalCert


namespace P312943
open OMA.S_oeis_a312943

/-- A packed target code (mixed radix). -/
def tg (n : ℕ) : GalCert.Tgt := ⟨n % 13, n / 13 % 64, n / 832 % 2, n / 1664 % 2, n / 3328 % 3, n / 9984 % 2, n / 19968 % 2, n / 39936 % 3, n / 119808⟩

set_option maxRecDepth 100000 in
def regsData : List (GalCert.Region 8) := [
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 0, 0, 2,
      [[tg 6], [tg 150], [tg 13], [tg 3]],
      [tg 119821]⟩,
    ⟨0, 0, 1, 1,
      [[tg 19], [tg 0], [tg 26], [tg 16]],
      [tg 119834]⟩,
    ⟨0, 0, 2, 0,
      [[tg 32], [tg 13], [tg 52], [tg 29]],
      [tg 0]⟩,
    ⟨0, 0, 3, 5,
      [[tg 45], [tg 65], [tg 10], [tg 42]],
      [tg 239681]⟩,
    ⟨0, 0, 4, 1,
      [[tg 58], [tg 84], [tg 26], [tg 78], [tg 55]],
      [tg 239642]⟩,
    ⟨0, 0, 5, 4,
      [[tg 71], [tg 97], [tg 39], [tg 91], [tg 68]],
      [tg 359521]⟩,
    ⟨0, 0, 6, 2,
      [[tg 84], [tg 52], [tg 91], [tg 55], [tg 81]],
      [tg 359476]⟩,
    ⟨0, 0, 7, 3,
      [[tg 97], [tg 65], [tg 78], [tg 68], [tg 94]],
      [tg 239694]⟩]⟩,
  ⟨1, -1, -1, 0, 0, [(1, -1, 0), (-1, 1, 0), (-1, -1, 2)], -1, -1, 2, 2, 0, 0, 0, 0,
   [⟨-1, -1, 0, 10,
      [[tg 740, tg 50660], [tg 3478, tg 7638], [tg 14, tg 4174], [tg 111, tg 4271]],
      [tg 119822, tg 123982]⟩,
    ⟨-1, -1, 1, 9,
      [[tg 753, tg 50673], [tg 1, tg 4161], [tg 27, tg 4187], [tg 124, tg 4284]],
      [tg 119835, tg 123995]⟩,
    ⟨-1, -1, 2, 8,
      [[tg 766, tg 50686], [tg 14, tg 4174], [tg 53, tg 4213], [tg 137, tg 4297]],
      [tg 239669, tg 243829]⟩,
    ⟨-1, -1, 3, 4,
      [[tg 779, tg 50699], [tg 66, tg 4226], [tg 6, tg 10724], [tg 150, tg 4310]],
      [tg 119814, tg 130532]⟩,
    ⟨-1, -1, 4, 7,
      [[tg 792, tg 50712], [tg 818, tg 50738], [tg 27, tg 4187], [tg 79, tg 4239], [tg 163, tg 4323]],
      [tg 119887, tg 124047]⟩,
    ⟨-1, -1, 5, 5,
      [[tg 805, tg 50725], [tg 831, tg 50751], [tg 40, tg 4200], [tg 92, tg 4252], [tg 176, tg 4336]],
      [tg 119848, tg 124008]⟩,
    ⟨-1, -1, 6, 6,
      [[tg 818, tg 50738], [tg 53, tg 4213], [tg 92, tg 4252], [tg 163, tg 4323], [tg 189, tg 4349]],
      [tg 239708, tg 243868]⟩,
    ⟨-1, -1, 7, 5,
      [[tg 831, tg 50751], [tg 66, tg 4226], [tg 79, tg 4239], [tg 176, tg 4336], [tg 202, tg 4362]],
      [tg 119984, tg 124144]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 2)], 1, -1, 2, 2, 0, 0, 0, 0,
   [⟨1, -1, 0, 10,
      [[tg 111, tg 50031], [tg 40086, tg 90006], [tg 15, tg 4175], [tg 8, tg 4168]],
      [tg 119823, tg 123983]⟩,
    ⟨1, -1, 1, 9,
      [[tg 124, tg 50044], [tg 2, tg 4162], [tg 28, tg 4188], [tg 21, tg 4181]],
      [tg 119836, tg 123996]⟩,
    ⟨1, -1, 2, 8,
      [[tg 137, tg 50057], [tg 15, tg 4175], [tg 54, tg 4214], [tg 34, tg 4194]],
      [tg 239670, tg 243830]⟩,
    ⟨1, -1, 3, 4,
      [[tg 150, tg 50070], [tg 67, tg 4227], [tg 3, tg 840], [tg 47, tg 4207]],
      [tg 359574, tg 409494]⟩,
    ⟨1, -1, 4, 7,
      [[tg 163, tg 50083], [tg 189, tg 50109], [tg 28, tg 4188], [tg 80, tg 4240], [tg 60, tg 4220]],
      [tg 359613, tg 409533]⟩,
    ⟨1, -1, 5, 5,
      [[tg 176, tg 50096], [tg 202, tg 50122], [tg 41, tg 4201], [tg 93, tg 4253], [tg 73, tg 4233]],
      [tg 479408, tg 529328]⟩,
    ⟨1, -1, 6, 7,
      [[tg 189, tg 50109], [tg 54, tg 4214], [tg 93, tg 4253], [tg 60, tg 4220], [tg 86, tg 4246]],
      [tg 479421, tg 529341]⟩,
    ⟨1, -1, 7, 6,
      [[tg 202, tg 50122], [tg 67, tg 4227], [tg 80, tg 4240], [tg 73, tg 4233], [tg 99, tg 4259]],
      [tg 479434, tg 529354]⟩]⟩,
  ⟨1, 8, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 1)], 1, 0, 1, 8, 0, 0, 0, 0,
   [⟨1, 0, 0, 3,
      [[tg 0, tg 1563], [tg 41, tg 10759], [tg 16, tg 4176], [tg 107, tg 4267]],
      [tg 359424, tg 360987]⟩,
    ⟨1, 0, 1, 2,
      [[tg 13, tg 1576], [tg 3, tg 4163], [tg 29, tg 4189], [tg 120, tg 4280]],
      [tg 359437, tg 361000]⟩,
    ⟨1, 0, 2, 1,
      [[tg 26, tg 1589], [tg 16, tg 4176], [tg 55, tg 4215], [tg 133, tg 4293]],
      [tg 359450, tg 361013]⟩,
    ⟨1, 0, 3, 5,
      [[tg 39, tg 1602], [tg 68, tg 4228], [tg 4, tg 1569], [tg 146, tg 4306]],
      [tg 239684, tg 361026]⟩,
    ⟨1, 0, 4, 2,
      [[tg 52, tg 1615], [tg 78, tg 1641], [tg 29, tg 4189], [tg 81, tg 4241], [tg 159, tg 4319]],
      [tg 479284, tg 480847]⟩,
    ⟨1, 0, 5, 4,
      [[tg 65, tg 1628], [tg 91, tg 1654], [tg 42, tg 4202], [tg 94, tg 4254], [tg 172, tg 4332]],
      [tg 359515, tg 480860]⟩,
    ⟨1, 0, 6, 3,
      [[tg 78, tg 1641], [tg 55, tg 4215], [tg 94, tg 4254], [tg 159, tg 4319], [tg 185, tg 4345]],
      [tg 479310, tg 480873]⟩,
    ⟨1, 0, 7, 4,
      [[tg 91, tg 1654], [tg 68, tg 4228], [tg 81, tg 4241], [tg 172, tg 4332], [tg 198, tg 4358]],
      [tg 479323, tg 480886]⟩,
    ⟨2, 0, 0, 4,
      [[tg 3, tg 4163], [tg 47, tg 49967], [tg 120, tg 4280], [tg 211, tg 4371]],
      [tg 359427, tg 363587]⟩,
    ⟨2, 0, 1, 3,
      [[tg 16, tg 4176], [tg 107, tg 4267], [tg 133, tg 4293], [tg 224, tg 4384]],
      [tg 359440, tg 363600]⟩,
    ⟨2, 0, 2, 2,
      [[tg 29, tg 4189], [tg 120, tg 4280], [tg 159, tg 4319], [tg 237, tg 4397]],
      [tg 359453, tg 363613]⟩,
    ⟨2, 0, 3, 6,
      [[tg 42, tg 4202], [tg 172, tg 4332], [tg 9, tg 4169], [tg 250, tg 4410]],
      [tg 359466, tg 363626]⟩,
    ⟨2, 0, 4, 3,
      [[tg 55, tg 4215], [tg 81, tg 4241], [tg 133, tg 4293], [tg 185, tg 4345], [tg 263, tg 4423]],
      [tg 479287, tg 483447]⟩,
    ⟨2, 0, 5, 5,
      [[tg 68, tg 4228], [tg 94, tg 4254], [tg 146, tg 4306], [tg 198, tg 4358], [tg 276, tg 4436]],
      [tg 479300, tg 483460]⟩,
    ⟨2, 0, 6, 4,
      [[tg 81, tg 4241], [tg 159, tg 4319], [tg 198, tg 4358], [tg 263, tg 4423], [tg 289, tg 4449]],
      [tg 479313, tg 483473]⟩,
    ⟨2, 0, 7, 5,
      [[tg 94, tg 4254], [tg 172, tg 4332], [tg 185, tg 4345], [tg 276, tg 4436], [tg 302, tg 4462]],
      [tg 479326, tg 483486]⟩,
    ⟨3, 0, 0, 5,
      [[tg 107, tg 4267], [tg 151, tg 50071], [tg 224, tg 4384], [tg 315, tg 4475]],
      [tg 359531, tg 363691]⟩,
    ⟨3, 0, 1, 4,
      [[tg 120, tg 4280], [tg 211, tg 4371], [tg 237, tg 4397], [tg 328, tg 4488]],
      [tg 359544, tg 363704]⟩,
    ⟨3, 0, 2, 3,
      [[tg 133, tg 4293], [tg 224, tg 4384], [tg 263, tg 4423], [tg 341, tg 4501]],
      [tg 359557, tg 363717]⟩,
    ⟨3, 0, 3, 7,
      [[tg 146, tg 4306], [tg 276, tg 4436], [tg 113, tg 4273], [tg 354, tg 4514]],
      [tg 359570, tg 363730]⟩,
    ⟨3, 0, 4, 4,
      [[tg 159, tg 4319], [tg 185, tg 4345], [tg 237, tg 4397], [tg 289, tg 4449], [tg 367, tg 4527]],
      [tg 479391, tg 483551]⟩,
    ⟨3, 0, 5, 6,
      [[tg 172, tg 4332], [tg 198, tg 4358], [tg 250, tg 4410], [tg 302, tg 4462], [tg 380, tg 4540]],
      [tg 479404, tg 483564]⟩,
    ⟨3, 0, 6, 5,
      [[tg 185, tg 4345], [tg 263, tg 4423], [tg 302, tg 4462], [tg 367, tg 4527], [tg 393, tg 4553]],
      [tg 479417, tg 483577]⟩,
    ⟨3, 0, 7, 6,
      [[tg 198, tg 4358], [tg 276, tg 4436], [tg 289, tg 4449], [tg 380, tg 4540], [tg 406, tg 4566]],
      [tg 479430, tg 483590]⟩,
    ⟨4, 0, 0, 6,
      [[tg 211, tg 4371], [tg 255, tg 50175], [tg 328, tg 4488], [tg 419, tg 4579]],
      [tg 359635, tg 363795]⟩,
    ⟨4, 0, 1, 5,
      [[tg 224, tg 4384], [tg 315, tg 4475], [tg 341, tg 4501], [tg 432, tg 4592]],
      [tg 359648, tg 363808]⟩,
    ⟨4, 0, 2, 4,
      [[tg 237, tg 4397], [tg 328, tg 4488], [tg 367, tg 4527], [tg 445, tg 4605]],
      [tg 359661, tg 363821]⟩,
    ⟨4, 0, 3, 8,
      [[tg 250, tg 4410], [tg 380, tg 4540], [tg 217, tg 4377], [tg 458, tg 4618]],
      [tg 359674, tg 363834]⟩,
    ⟨4, 0, 4, 5,
      [[tg 263, tg 4423], [tg 289, tg 4449], [tg 341, tg 4501], [tg 393, tg 4553], [tg 471, tg 4631]],
      [tg 479495, tg 483655]⟩,
    ⟨4, 0, 5, 7,
      [[tg 276, tg 4436], [tg 302, tg 4462], [tg 354, tg 4514], [tg 406, tg 4566], [tg 484, tg 4644]],
      [tg 479508, tg 483668]⟩,
    ⟨4, 0, 6, 6,
      [[tg 289, tg 4449], [tg 367, tg 4527], [tg 406, tg 4566], [tg 471, tg 4631], [tg 497, tg 4657]],
      [tg 479521, tg 483681]⟩,
    ⟨4, 0, 7, 7,
      [[tg 302, tg 4462], [tg 380, tg 4540], [tg 393, tg 4553], [tg 484, tg 4644], [tg 510, tg 4670]],
      [tg 479534, tg 483694]⟩,
    ⟨5, 0, 0, 7,
      [[tg 315, tg 4475], [tg 359, tg 50279], [tg 432, tg 4592], [tg 523, tg 4683]],
      [tg 359739, tg 363899]⟩,
    ⟨5, 0, 1, 6,
      [[tg 328, tg 4488], [tg 419, tg 4579], [tg 445, tg 4605], [tg 536, tg 4696]],
      [tg 359752, tg 363912]⟩,
    ⟨5, 0, 2, 5,
      [[tg 341, tg 4501], [tg 432, tg 4592], [tg 471, tg 4631], [tg 549, tg 4709]],
      [tg 359765, tg 363925]⟩,
    ⟨5, 0, 3, 9,
      [[tg 354, tg 4514], [tg 484, tg 4644], [tg 321, tg 4481], [tg 562, tg 4722]],
      [tg 359778, tg 363938]⟩,
    ⟨5, 0, 4, 6,
      [[tg 367, tg 4527], [tg 393, tg 4553], [tg 445, tg 4605], [tg 497, tg 4657], [tg 575, tg 4735]],
      [tg 479599, tg 483759]⟩,
    ⟨5, 0, 5, 8,
      [[tg 380, tg 4540], [tg 406, tg 4566], [tg 458, tg 4618], [tg 510, tg 4670], [tg 588, tg 4748]],
      [tg 479612, tg 483772]⟩,
    ⟨5, 0, 6, 7,
      [[tg 393, tg 4553], [tg 471, tg 4631], [tg 510, tg 4670], [tg 575, tg 4735], [tg 601, tg 4761]],
      [tg 479625, tg 483785]⟩,
    ⟨5, 0, 7, 8,
      [[tg 406, tg 4566], [tg 484, tg 4644], [tg 497, tg 4657], [tg 588, tg 4748], [tg 614, tg 4774]],
      [tg 479638, tg 483798]⟩,
    ⟨6, 0, 0, 8,
      [[tg 419, tg 4579], [tg 463, tg 50383], [tg 536, tg 4696], [tg 627, tg 4787]],
      [tg 359843, tg 364003]⟩,
    ⟨6, 0, 1, 7,
      [[tg 432, tg 4592], [tg 523, tg 4683], [tg 549, tg 4709], [tg 640, tg 4800]],
      [tg 359856, tg 364016]⟩,
    ⟨6, 0, 2, 6,
      [[tg 445, tg 4605], [tg 536, tg 4696], [tg 575, tg 4735], [tg 653, tg 4813]],
      [tg 359869, tg 364029]⟩,
    ⟨6, 0, 3, 10,
      [[tg 458, tg 4618], [tg 588, tg 4748], [tg 425, tg 4585], [tg 666, tg 4826]],
      [tg 359882, tg 364042]⟩,
    ⟨6, 0, 4, 7,
      [[tg 471, tg 4631], [tg 497, tg 4657], [tg 549, tg 4709], [tg 601, tg 4761], [tg 679, tg 4839]],
      [tg 479703, tg 483863]⟩,
    ⟨6, 0, 5, 9,
      [[tg 484, tg 4644], [tg 510, tg 4670], [tg 562, tg 4722], [tg 614, tg 4774], [tg 692, tg 4852]],
      [tg 479716, tg 483876]⟩,
    ⟨6, 0, 6, 8,
      [[tg 497, tg 4657], [tg 575, tg 4735], [tg 614, tg 4774], [tg 679, tg 4839], [tg 705, tg 4865]],
      [tg 479729, tg 483889]⟩,
    ⟨6, 0, 7, 9,
      [[tg 510, tg 4670], [tg 588, tg 4748], [tg 601, tg 4761], [tg 692, tg 4852], [tg 718, tg 4878]],
      [tg 479742, tg 483902]⟩,
    ⟨7, 0, 0, 9,
      [[tg 523, tg 4683], [tg 567, tg 50487], [tg 640, tg 4800], [tg 731, tg 4891]],
      [tg 359947, tg 364107]⟩,
    ⟨7, 0, 1, 8,
      [[tg 536, tg 4696], [tg 627, tg 4787], [tg 653, tg 4813], [tg 744, tg 4904]],
      [tg 359960, tg 364120]⟩,
    ⟨7, 0, 2, 7,
      [[tg 549, tg 4709], [tg 640, tg 4800], [tg 679, tg 4839], [tg 757, tg 4917]],
      [tg 359973, tg 364133]⟩,
    ⟨7, 0, 3, 11,
      [[tg 562, tg 4722], [tg 692, tg 4852], [tg 529, tg 4689], [tg 770, tg 4930]],
      [tg 359986, tg 364146]⟩,
    ⟨7, 0, 4, 8,
      [[tg 575, tg 4735], [tg 601, tg 4761], [tg 653, tg 4813], [tg 705, tg 4865], [tg 783, tg 4943]],
      [tg 479807, tg 483967]⟩,
    ⟨7, 0, 5, 10,
      [[tg 588, tg 4748], [tg 614, tg 4774], [tg 666, tg 4826], [tg 718, tg 4878], [tg 796, tg 4956]],
      [tg 479820, tg 483980]⟩,
    ⟨7, 0, 6, 9,
      [[tg 601, tg 4761], [tg 679, tg 4839], [tg 718, tg 4878], [tg 783, tg 4943], [tg 809, tg 4969]],
      [tg 479833, tg 483993]⟩,
    ⟨7, 0, 7, 10,
      [[tg 614, tg 4774], [tg 692, tg 4852], [tg 705, tg 4865], [tg 796, tg 4956], [tg 822, tg 4982]],
      [tg 479846, tg 484006]⟩,
    ⟨8, 0, 0, 10,
      [[tg 627, tg 4787], [tg 671, tg 50591], [tg 744, tg 4904], [tg 3331, tg 7491]],
      [tg 360051, tg 364211]⟩,
    ⟨8, 0, 1, 9,
      [[tg 640, tg 4800], [tg 731, tg 4891], [tg 757, tg 4917], [tg 3344, tg 7504]],
      [tg 360064, tg 364224]⟩,
    ⟨8, 0, 2, 8,
      [[tg 653, tg 4813], [tg 744, tg 4904], [tg 783, tg 4943], [tg 3357, tg 7517]],
      [tg 360077, tg 364237]⟩,
    ⟨8, 0, 3, 12,
      [[tg 666, tg 4826], [tg 796, tg 4956], [tg 633, tg 4793], [tg 3370, tg 7530]],
      [tg 360090, tg 364250]⟩,
    ⟨8, 0, 4, 9,
      [[tg 679, tg 4839], [tg 705, tg 4865], [tg 757, tg 4917], [tg 809, tg 4969], [tg 3383, tg 7543]],
      [tg 479911, tg 484071]⟩,
    ⟨8, 0, 5, 11,
      [[tg 692, tg 4852], [tg 718, tg 4878], [tg 770, tg 4930], [tg 822, tg 4982], [tg 3396, tg 7556]],
      [tg 479924, tg 484084]⟩,
    ⟨8, 0, 6, 10,
      [[tg 705, tg 4865], [tg 783, tg 4943], [tg 822, tg 4982], [tg 3383, tg 7543], [tg 3409, tg 7569]],
      [tg 479937, tg 484097]⟩,
    ⟨8, 0, 7, 11,
      [[tg 718, tg 4878], [tg 796, tg 4956], [tg 809, tg 4969], [tg 3396, tg 7556], [tg 3422, tg 7582]],
      [tg 479950, tg 484110]⟩]⟩,
  ⟨1, 1, 1, 0, 0, [(-1, 1, 0), (1, -1, 0), (1, 1, 2)], 1, 1, 2, 2, 0, 0, 0, 0,
   [⟨1, 1, 0, 6,
      [[tg 10, tg 4170], [tg 42, tg 10032], [tg 17, tg 4177], [tg 9, tg 49929]],
      [tg 239658, tg 249648]⟩,
    ⟨1, 1, 1, 7,
      [[tg 23, tg 4183], [tg 4, tg 4164], [tg 30, tg 4190], [tg 22, tg 49942]],
      [tg 239620, tg 243780]⟩,
    ⟨1, 1, 2, 8,
      [[tg 36, tg 4196], [tg 17, tg 4177], [tg 56, tg 4216], [tg 35, tg 49955]],
      [tg 239633, tg 243793]⟩,
    ⟨1, 1, 3, 13,
      [[tg 49, tg 4209], [tg 69, tg 4229], [tg 3338, tg 7498], [tg 48, tg 49968]],
      [tg 239685, tg 243845]⟩,
    ⟨1, 1, 4, 9,
      [[tg 62, tg 4222], [tg 88, tg 4248], [tg 30, tg 4190], [tg 82, tg 4242], [tg 61, tg 49981]],
      [tg 239646, tg 243806]⟩,
    ⟨1, 1, 5, 12,
      [[tg 75, tg 4235], [tg 101, tg 4261], [tg 43, tg 4203], [tg 95, tg 4255], [tg 74, tg 49994]],
      [tg 359525, tg 363685]⟩,
    ⟨1, 1, 6, 10,
      [[tg 88, tg 4248], [tg 56, tg 4216], [tg 95, tg 4255], [tg 61, tg 49981], [tg 87, tg 50007]],
      [tg 359480, tg 363640]⟩,
    ⟨1, 1, 7, 11,
      [[tg 101, tg 4261], [tg 69, tg 4229], [tg 82, tg 4242], [tg 74, tg 49994], [tg 100, tg 50020]],
      [tg 239698, tg 243858]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 2)], -1, 1, 2, 2, 0, 0, 0, 0,
   [⟨-1, 1, 0, 6,
      [[tg 739, tg 4899], [tg 45, tg 1610], [tg 18, tg 4178], [tg 10, tg 49930]],
      [tg 239661, tg 241226]⟩,
    ⟨-1, 1, 1, 7,
      [[tg 752, tg 4912], [tg 5, tg 4165], [tg 31, tg 4191], [tg 23, tg 49943]],
      [tg 239621, tg 243781]⟩,
    ⟨-1, 1, 2, 8,
      [[tg 765, tg 4925], [tg 18, tg 4178], [tg 57, tg 4217], [tg 36, tg 49956]],
      [tg 239634, tg 243794]⟩,
    ⟨-1, 1, 3, 13,
      [[tg 778, tg 4938], [tg 70, tg 4230], [tg 39946, tg 89866], [tg 49, tg 49969]],
      [tg 239686, tg 243846]⟩,
    ⟨-1, 1, 4, 9,
      [[tg 791, tg 4951], [tg 817, tg 4977], [tg 31, tg 4191], [tg 83, tg 4243], [tg 62, tg 49982]],
      [tg 239647, tg 243807]⟩,
    ⟨-1, 1, 5, 12,
      [[tg 804, tg 4964], [tg 830, tg 4990], [tg 44, tg 4204], [tg 96, tg 4256], [tg 75, tg 49995]],
      [tg 360254, tg 364414]⟩,
    ⟨-1, 1, 6, 10,
      [[tg 817, tg 4977], [tg 57, tg 4217], [tg 96, tg 4256], [tg 62, tg 49982], [tg 88, tg 50008]],
      [tg 359481, tg 363641]⟩,
    ⟨-1, 1, 7, 11,
      [[tg 830, tg 4990], [tg 70, tg 4230], [tg 83, tg 4243], [tg 75, tg 49995], [tg 101, tg 50021]],
      [tg 239699, tg 243859]⟩]⟩,
  ⟨1, -8, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 1)], -1, 0, 1, 8, 0, 0, 0, 0,
   [⟨-1, 0, 0, 3,
      [[tg 110, tg 4270], [tg 40, tg 883], [tg 19, tg 4179], [tg 0, tg 1566]],
      [tg 119827, tg 123987]⟩,
    ⟨-1, 0, 1, 2,
      [[tg 123, tg 4283], [tg 6, tg 4166], [tg 32, tg 4192], [tg 13, tg 1579]],
      [tg 119840, tg 124000]⟩,
    ⟨-1, 0, 2, 1,
      [[tg 136, tg 4296], [tg 19, tg 4179], [tg 58, tg 4218], [tg 26, tg 1592]],
      [tg 26, tg 1592]⟩,
    ⟨-1, 0, 3, 5,
      [[tg 149, tg 4309], [tg 71, tg 4231], [tg 5, tg 9995], [tg 39, tg 1605]],
      [tg 239687, tg 243847]⟩,
    ⟨-1, 0, 4, 2,
      [[tg 162, tg 4322], [tg 188, tg 4348], [tg 32, tg 4192], [tg 84, tg 4244], [tg 52, tg 1618]],
      [tg 239648, tg 243808]⟩,
    ⟨-1, 0, 5, 4,
      [[tg 175, tg 4335], [tg 201, tg 4361], [tg 45, tg 4205], [tg 97, tg 4257], [tg 65, tg 1631]],
      [tg 119905, tg 124065]⟩,
    ⟨-1, 0, 6, 2,
      [[tg 188, tg 4348], [tg 58, tg 4218], [tg 97, tg 4257], [tg 52, tg 1618], [tg 78, tg 1644]],
      [tg 119860, tg 121426]⟩,
    ⟨-1, 0, 7, 3,
      [[tg 201, tg 4361], [tg 71, tg 4231], [tg 84, tg 4244], [tg 65, tg 1631], [tg 91, tg 1657]],
      [tg 239700, tg 243860]⟩,
    ⟨-2, 0, 0, 4,
      [[tg 214, tg 4374], [tg 779, tg 4939], [tg 123, tg 4283], [tg 6, tg 4166]],
      [tg 119931, tg 124091]⟩,
    ⟨-2, 0, 1, 3,
      [[tg 227, tg 4387], [tg 110, tg 4270], [tg 136, tg 4296], [tg 19, tg 4179]],
      [tg 119944, tg 124104]⟩,
    ⟨-2, 0, 2, 2,
      [[tg 240, tg 4400], [tg 123, tg 4283], [tg 162, tg 4322], [tg 32, tg 4192]],
      [tg 32, tg 4192]⟩,
    ⟨-2, 0, 3, 6,
      [[tg 253, tg 4413], [tg 175, tg 4335], [tg 739, tg 50659], [tg 45, tg 4205]],
      [tg 239791, tg 243951]⟩,
    ⟨-2, 0, 4, 3,
      [[tg 266, tg 4426], [tg 292, tg 4452], [tg 136, tg 4296], [tg 188, tg 4348], [tg 58, tg 4218]],
      [tg 239752, tg 243912]⟩,
    ⟨-2, 0, 5, 5,
      [[tg 279, tg 4439], [tg 305, tg 4465], [tg 149, tg 4309], [tg 201, tg 4361], [tg 71, tg 4231]],
      [tg 120009, tg 124169]⟩,
    ⟨-2, 0, 6, 3,
      [[tg 292, tg 4452], [tg 162, tg 4322], [tg 201, tg 4361], [tg 58, tg 4218], [tg 84, tg 4244]],
      [tg 119866, tg 124026]⟩,
    ⟨-2, 0, 7, 4,
      [[tg 305, tg 4465], [tg 175, tg 4335], [tg 188, tg 4348], [tg 71, tg 4231], [tg 97, tg 4257]],
      [tg 239804, tg 243964]⟩,
    ⟨-3, 0, 0, 5,
      [[tg 318, tg 4478], [tg 675, tg 4835], [tg 227, tg 4387], [tg 110, tg 4270]],
      [tg 120035, tg 124195]⟩,
    ⟨-3, 0, 1, 4,
      [[tg 331, tg 4491], [tg 214, tg 4374], [tg 240, tg 4400], [tg 123, tg 4283]],
      [tg 120048, tg 124208]⟩,
    ⟨-3, 0, 2, 3,
      [[tg 344, tg 4504], [tg 227, tg 4387], [tg 266, tg 4426], [tg 136, tg 4296]],
      [tg 136, tg 4296]⟩,
    ⟨-3, 0, 3, 7,
      [[tg 357, tg 4517], [tg 279, tg 4439], [tg 635, tg 50555], [tg 149, tg 4309]],
      [tg 239895, tg 244055]⟩,
    ⟨-3, 0, 4, 4,
      [[tg 370, tg 4530], [tg 396, tg 4556], [tg 240, tg 4400], [tg 292, tg 4452], [tg 162, tg 4322]],
      [tg 239856, tg 244016]⟩,
    ⟨-3, 0, 5, 6,
      [[tg 383, tg 4543], [tg 409, tg 4569], [tg 253, tg 4413], [tg 305, tg 4465], [tg 175, tg 4335]],
      [tg 120113, tg 124273]⟩,
    ⟨-3, 0, 6, 4,
      [[tg 396, tg 4556], [tg 266, tg 4426], [tg 305, tg 4465], [tg 162, tg 4322], [tg 188, tg 4348]],
      [tg 119970, tg 124130]⟩,
    ⟨-3, 0, 7, 5,
      [[tg 409, tg 4569], [tg 279, tg 4439], [tg 292, tg 4452], [tg 175, tg 4335], [tg 201, tg 4361]],
      [tg 239908, tg 244068]⟩,
    ⟨-4, 0, 0, 6,
      [[tg 422, tg 4582], [tg 571, tg 4731], [tg 331, tg 4491], [tg 214, tg 4374]],
      [tg 120139, tg 124299]⟩,
    ⟨-4, 0, 1, 5,
      [[tg 435, tg 4595], [tg 318, tg 4478], [tg 344, tg 4504], [tg 227, tg 4387]],
      [tg 120152, tg 124312]⟩,
    ⟨-4, 0, 2, 4,
      [[tg 448, tg 4608], [tg 331, tg 4491], [tg 370, tg 4530], [tg 240, tg 4400]],
      [tg 240, tg 4400]⟩,
    ⟨-4, 0, 3, 8,
      [[tg 461, tg 4621], [tg 383, tg 4543], [tg 531, tg 50451], [tg 253, tg 4413]],
      [tg 239999, tg 244159]⟩,
    ⟨-4, 0, 4, 5,
      [[tg 474, tg 4634], [tg 500, tg 4660], [tg 344, tg 4504], [tg 396, tg 4556], [tg 266, tg 4426]],
      [tg 239960, tg 244120]⟩,
    ⟨-4, 0, 5, 7,
      [[tg 487, tg 4647], [tg 513, tg 4673], [tg 357, tg 4517], [tg 409, tg 4569], [tg 279, tg 4439]],
      [tg 120217, tg 124377]⟩,
    ⟨-4, 0, 6, 5,
      [[tg 500, tg 4660], [tg 370, tg 4530], [tg 409, tg 4569], [tg 266, tg 4426], [tg 292, tg 4452]],
      [tg 120074, tg 124234]⟩,
    ⟨-4, 0, 7, 6,
      [[tg 513, tg 4673], [tg 383, tg 4543], [tg 396, tg 4556], [tg 279, tg 4439], [tg 305, tg 4465]],
      [tg 240012, tg 244172]⟩,
    ⟨-5, 0, 0, 7,
      [[tg 526, tg 4686], [tg 467, tg 4627], [tg 435, tg 4595], [tg 318, tg 4478]],
      [tg 120243, tg 124403]⟩,
    ⟨-5, 0, 1, 6,
      [[tg 539, tg 4699], [tg 422, tg 4582], [tg 448, tg 4608], [tg 331, tg 4491]],
      [tg 120256, tg 124416]⟩,
    ⟨-5, 0, 2, 5,
      [[tg 552, tg 4712], [tg 435, tg 4595], [tg 474, tg 4634], [tg 344, tg 4504]],
      [tg 344, tg 4504]⟩,
    ⟨-5, 0, 3, 9,
      [[tg 565, tg 4725], [tg 487, tg 4647], [tg 427, tg 50347], [tg 357, tg 4517]],
      [tg 240103, tg 244263]⟩,
    ⟨-5, 0, 4, 6,
      [[tg 578, tg 4738], [tg 604, tg 4764], [tg 448, tg 4608], [tg 500, tg 4660], [tg 370, tg 4530]],
      [tg 240064, tg 244224]⟩,
    ⟨-5, 0, 5, 8,
      [[tg 591, tg 4751], [tg 617, tg 4777], [tg 461, tg 4621], [tg 513, tg 4673], [tg 383, tg 4543]],
      [tg 120321, tg 124481]⟩,
    ⟨-5, 0, 6, 6,
      [[tg 604, tg 4764], [tg 474, tg 4634], [tg 513, tg 4673], [tg 370, tg 4530], [tg 396, tg 4556]],
      [tg 120178, tg 124338]⟩,
    ⟨-5, 0, 7, 7,
      [[tg 617, tg 4777], [tg 487, tg 4647], [tg 500, tg 4660], [tg 383, tg 4543], [tg 409, tg 4569]],
      [tg 240116, tg 244276]⟩,
    ⟨-6, 0, 0, 8,
      [[tg 630, tg 4790], [tg 363, tg 4523], [tg 539, tg 4699], [tg 422, tg 4582]],
      [tg 120347, tg 124507]⟩,
    ⟨-6, 0, 1, 7,
      [[tg 643, tg 4803], [tg 526, tg 4686], [tg 552, tg 4712], [tg 435, tg 4595]],
      [tg 120360, tg 124520]⟩,
    ⟨-6, 0, 2, 6,
      [[tg 656, tg 4816], [tg 539, tg 4699], [tg 578, tg 4738], [tg 448, tg 4608]],
      [tg 448, tg 4608]⟩,
    ⟨-6, 0, 3, 10,
      [[tg 669, tg 4829], [tg 591, tg 4751], [tg 323, tg 50243], [tg 461, tg 4621]],
      [tg 240207, tg 244367]⟩,
    ⟨-6, 0, 4, 7,
      [[tg 682, tg 4842], [tg 708, tg 4868], [tg 552, tg 4712], [tg 604, tg 4764], [tg 474, tg 4634]],
      [tg 240168, tg 244328]⟩,
    ⟨-6, 0, 5, 9,
      [[tg 695, tg 4855], [tg 721, tg 4881], [tg 565, tg 4725], [tg 617, tg 4777], [tg 487, tg 4647]],
      [tg 120425, tg 124585]⟩,
    ⟨-6, 0, 6, 7,
      [[tg 708, tg 4868], [tg 578, tg 4738], [tg 617, tg 4777], [tg 474, tg 4634], [tg 500, tg 4660]],
      [tg 120282, tg 124442]⟩,
    ⟨-6, 0, 7, 8,
      [[tg 721, tg 4881], [tg 591, tg 4751], [tg 604, tg 4764], [tg 487, tg 4647], [tg 513, tg 4673]],
      [tg 240220, tg 244380]⟩,
    ⟨-7, 0, 0, 9,
      [[tg 734, tg 4894], [tg 259, tg 4419], [tg 643, tg 4803], [tg 526, tg 4686]],
      [tg 120451, tg 124611]⟩,
    ⟨-7, 0, 1, 8,
      [[tg 747, tg 4907], [tg 630, tg 4790], [tg 656, tg 4816], [tg 539, tg 4699]],
      [tg 120464, tg 124624]⟩,
    ⟨-7, 0, 2, 7,
      [[tg 760, tg 4920], [tg 643, tg 4803], [tg 682, tg 4842], [tg 552, tg 4712]],
      [tg 552, tg 4712]⟩,
    ⟨-7, 0, 3, 11,
      [[tg 773, tg 4933], [tg 695, tg 4855], [tg 219, tg 50139], [tg 565, tg 4725]],
      [tg 240311, tg 244471]⟩,
    ⟨-7, 0, 4, 8,
      [[tg 786, tg 4946], [tg 812, tg 4972], [tg 656, tg 4816], [tg 708, tg 4868], [tg 578, tg 4738]],
      [tg 240272, tg 244432]⟩,
    ⟨-7, 0, 5, 10,
      [[tg 799, tg 4959], [tg 825, tg 4985], [tg 669, tg 4829], [tg 721, tg 4881], [tg 591, tg 4751]],
      [tg 120529, tg 124689]⟩,
    ⟨-7, 0, 6, 8,
      [[tg 812, tg 4972], [tg 682, tg 4842], [tg 721, tg 4881], [tg 578, tg 4738], [tg 604, tg 4764]],
      [tg 120386, tg 124546]⟩,
    ⟨-7, 0, 7, 9,
      [[tg 825, tg 4985], [tg 695, tg 4855], [tg 708, tg 4868], [tg 591, tg 4751], [tg 617, tg 4777]],
      [tg 240324, tg 244484]⟩,
    ⟨-8, 0, 0, 10,
      [[tg 3334, tg 7494], [tg 155, tg 4315], [tg 747, tg 4907], [tg 630, tg 4790]],
      [tg 120555, tg 124715]⟩,
    ⟨-8, 0, 1, 9,
      [[tg 3347, tg 7507], [tg 734, tg 4894], [tg 760, tg 4920], [tg 643, tg 4803]],
      [tg 120568, tg 124728]⟩,
    ⟨-8, 0, 2, 8,
      [[tg 3360, tg 7520], [tg 747, tg 4907], [tg 786, tg 4946], [tg 656, tg 4816]],
      [tg 656, tg 4816]⟩,
    ⟨-8, 0, 3, 12,
      [[tg 3373, tg 7533], [tg 799, tg 4959], [tg 115, tg 50035], [tg 669, tg 4829]],
      [tg 240415, tg 244575]⟩,
    ⟨-8, 0, 4, 9,
      [[tg 3386, tg 7546], [tg 3412, tg 7572], [tg 760, tg 4920], [tg 812, tg 4972], [tg 682, tg 4842]],
      [tg 240376, tg 244536]⟩,
    ⟨-8, 0, 5, 11,
      [[tg 3399, tg 7559], [tg 3425, tg 7585], [tg 773, tg 4933], [tg 825, tg 4985], [tg 695, tg 4855]],
      [tg 120633, tg 124793]⟩,
    ⟨-8, 0, 6, 9,
      [[tg 3412, tg 7572], [tg 786, tg 4946], [tg 825, tg 4985], [tg 682, tg 4842], [tg 708, tg 4868]],
      [tg 120490, tg 124650]⟩,
    ⟨-8, 0, 7, 10,
      [[tg 3425, tg 7585], [tg 799, tg 4959], [tg 812, tg 4972], [tg 695, tg 4855], [tg 721, tg 4881]],
      [tg 240428, tg 244588]⟩]⟩,
  ⟨2, -1, -1, 1, -1, [(-1, -1, 1), (1, -1, 1)], -1, -1, 1, 2, 1, -1, 1, 2,
   [⟨0, -2, 0, 18,
      [[tg 3439, tg 7599, tg 63343, tg 67503], [tg 43414, tg 47574, tg 103318, tg 107478], [tg 20, tg 4180, tg 59924, tg 64084], [tg 40047, tg 44207, tg 99951, tg 104111]],
      [tg 119828, tg 123988, tg 179732, tg 183892]⟩,
    ⟨0, -2, 1, 17,
      [[tg 3452, tg 7612, tg 63356, tg 67516], [tg 7, tg 4167, tg 59911, tg 64071], [tg 33, tg 4193, tg 59937, tg 64097], [tg 40060, tg 44220, tg 99964, tg 104124]],
      [tg 119841, tg 124001, tg 179745, tg 183905]⟩,
    ⟨0, -2, 2, 16,
      [[tg 3465, tg 7625, tg 63369, tg 67529], [tg 20, tg 4180, tg 59924, tg 64084], [tg 59, tg 4219, tg 59963, tg 64123], [tg 40073, tg 44233, tg 99977, tg 104137]],
      [tg 239675, tg 243835, tg 299579, tg 303739]⟩,
    ⟨0, -2, 3, 11,
      [[tg 3478, tg 7638, tg 63382, tg 67542], [tg 72, tg 4232, tg 59976, tg 64136], [tg 111, tg 4271, tg 60015, tg 64175], [tg 40086, tg 44246, tg 99990, tg 104150]],
      [tg 119919, tg 124079, tg 179823, tg 183983]⟩,
    ⟨0, -2, 4, 15,
      [[tg 3491, tg 7651, tg 63395, tg 67555], [tg 3517, tg 7677, tg 63421, tg 67581], [tg 33, tg 4193, tg 59937, tg 64097], [tg 85, tg 4245, tg 59989, tg 64149], [tg 40099, tg 44259, tg 100003, tg 104163]],
      [tg 362941, tg 367101, tg 422845, tg 427005]⟩,
    ⟨0, -2, 5, 12,
      [[tg 3504, tg 7664, tg 63408, tg 67568], [tg 3530, tg 7690, tg 63434, tg 67594], [tg 46, tg 4206, tg 59950, tg 64110], [tg 98, tg 4258, tg 60002, tg 64162], [tg 40112, tg 44272, tg 100016, tg 104176]],
      [tg 119854, tg 124014, tg 179758, tg 183918]⟩,
    ⟨0, -2, 6, 14,
      [[tg 3517, tg 7677, tg 63421, tg 67581], [tg 59, tg 4219, tg 59963, tg 64123], [tg 98, tg 4258, tg 60002, tg 64162], [tg 40099, tg 44259, tg 100003, tg 104163], [tg 40125, tg 44285, tg 100029, tg 104189]],
      [tg 239714, tg 243874, tg 299618, tg 303778]⟩,
    ⟨0, -2, 7, 13,
      [[tg 3530, tg 7690, tg 63434, tg 67594], [tg 72, tg 4232, tg 59976, tg 64136], [tg 85, tg 4245, tg 59989, tg 64149], [tg 40112, tg 44272, tg 100016, tg 104176], [tg 40138, tg 44298, tg 100042, tg 104202]],
      [tg 359496, tg 363656, tg 419400, tg 423560]⟩,
    ⟨0, -1, 0, 10,
      [[tg 1, tg 4161, tg 19975, tg 24135], [tg 46, tg 4206, tg 59950, tg 64110], [tg 124, tg 4284, tg 60028, tg 64188], [tg 2, tg 839, tg 4994, tg 60743]],
      [tg 119932, tg 124092, tg 179836, tg 183996]⟩,
    ⟨0, -1, 1, 9,
      [[tg 14, tg 4174, tg 19988, tg 24148], [tg 111, tg 4271, tg 60015, tg 64175], [tg 137, tg 4297, tg 60041, tg 64201], [tg 15, tg 852, tg 5007, tg 60756]],
      [tg 119945, tg 124105, tg 179849, tg 184009]⟩,
    ⟨0, -1, 2, 8,
      [[tg 27, tg 4187, tg 20001, tg 24161], [tg 124, tg 4284, tg 60028, tg 64188], [tg 163, tg 4323, tg 60067, tg 64227], [tg 28, tg 865, tg 5020, tg 60769]],
      [tg 239779, tg 243939, tg 299683, tg 303843]⟩,
    ⟨0, -1, 3, 3,
      [[tg 40, tg 4200, tg 20014, tg 24174], [tg 176, tg 4336, tg 60080, tg 64240], [tg 0, tg 833, tg 1666, tg 20807], [tg 41, tg 878, tg 5033, tg 60782]],
      [tg 119808, tg 120641, tg 121474, tg 140615]⟩,
    ⟨0, -1, 4, 7,
      [[tg 53, tg 4213, tg 20027, tg 24187], [tg 79, tg 4239, tg 20053, tg 24213], [tg 137, tg 4297, tg 60041, tg 64201], [tg 189, tg 4349, tg 60093, tg 64253], [tg 54, tg 891, tg 5046, tg 60795]],
      [tg 359503, tg 363663, tg 379477, tg 383637]⟩,
    ⟨0, -1, 5, 4,
      [[tg 66, tg 4226, tg 20040, tg 24200], [tg 92, tg 4252, tg 20066, tg 24226], [tg 150, tg 4310, tg 60054, tg 64214], [tg 202, tg 4362, tg 60106, tg 64266], [tg 67, tg 904, tg 5059, tg 60808]],
      [tg 119958, tg 124118, tg 179862, tg 184022]⟩,
    ⟨0, -1, 6, 6,
      [[tg 79, tg 4239, tg 20053, tg 24213], [tg 163, tg 4323, tg 60067, tg 64227], [tg 202, tg 4362, tg 60106, tg 64266], [tg 54, tg 891, tg 5046, tg 60795], [tg 80, tg 917, tg 5072, tg 60821]],
      [tg 239818, tg 243978, tg 299722, tg 303882]⟩,
    ⟨0, -1, 7, 5,
      [[tg 92, tg 4252, tg 20066, tg 24226], [tg 176, tg 4336, tg 60080, tg 64240], [tg 189, tg 4349, tg 60093, tg 64253], [tg 67, tg 904, tg 5059, tg 60808], [tg 93, tg 930, tg 5085, tg 60834]],
      [tg 359600, tg 363760, tg 419504, tg 423664]⟩]⟩,
  ⟨2, 1, -1, 8, 0, [(0, -8, 1), (1, 1, 1)], 0, -8, 1, 8, 1, 1, 1, 8,
   [⟨2, -1, 0, 11,
      [[tg 2, tg 4162, tg 20704, tg 24864], [tg 3369, tg 7529, tg 24071, tg 28231], [tg 21, tg 4181, tg 59925, tg 64085], [tg 112, tg 4272, tg 60016, tg 64176]],
      [tg 359426, tg 363586, tg 380128, tg 384288]⟩,
    ⟨2, -1, 1, 10,
      [[tg 15, tg 4175, tg 20717, tg 24877], [tg 8, tg 4168, tg 59912, tg 64072], [tg 34, tg 4194, tg 59938, tg 64098], [tg 125, tg 4285, tg 60029, tg 64189]],
      [tg 359439, tg 363599, tg 380141, tg 384301]⟩,
    ⟨2, -1, 2, 9,
      [[tg 28, tg 4188, tg 20730, tg 24890], [tg 21, tg 4181, tg 59925, tg 64085], [tg 60, tg 4220, tg 59964, tg 64124], [tg 138, tg 4298, tg 60042, tg 64202]],
      [tg 359452, tg 363612, tg 380154, tg 384314]⟩,
    ⟨2, -1, 3, 5,
      [[tg 41, tg 4201, tg 20743, tg 24903], [tg 73, tg 4233, tg 59977, tg 64137], [tg 107, tg 944, tg 5099, tg 60848], [tg 151, tg 4311, tg 60055, tg 64215]],
      [tg 359465, tg 363625, tg 380167, tg 384327]⟩,
    ⟨2, -1, 4, 8,
      [[tg 54, tg 4214, tg 20756, tg 24916], [tg 80, tg 4240, tg 20782, tg 24942], [tg 34, tg 4194, tg 59938, tg 64098], [tg 86, tg 4246, tg 59990, tg 64150], [tg 164, tg 4324, tg 60068, tg 64228]],
      [tg 479286, tg 483446, tg 499988, tg 504148]⟩,
    ⟨2, -1, 5, 6,
      [[tg 67, tg 4227, tg 20769, tg 24929], [tg 93, tg 4253, tg 20795, tg 24955], [tg 47, tg 4207, tg 59951, tg 64111], [tg 99, tg 4259, tg 60003, tg 64163], [tg 177, tg 4337, tg 60081, tg 64241]],
      [tg 479299, tg 483459, tg 500001, tg 504161]⟩,
    ⟨2, -1, 6, 8,
      [[tg 80, tg 4240, tg 20782, tg 24942], [tg 60, tg 4220, tg 59964, tg 64124], [tg 99, tg 4259, tg 60003, tg 64163], [tg 164, tg 4324, tg 60068, tg 64228], [tg 190, tg 4350, tg 60094, tg 64254]],
      [tg 479312, tg 483472, tg 500014, tg 504174]⟩,
    ⟨2, -1, 7, 7,
      [[tg 93, tg 4253, tg 20795, tg 24955], [tg 73, tg 4233, tg 59977, tg 64137], [tg 86, tg 4246, tg 59990, tg 64150], [tg 177, tg 4337, tg 60081, tg 64241], [tg 203, tg 4363, tg 60107, tg 64267]],
      [tg 479325, tg 483485, tg 500027, tg 504187]⟩,
    ⟨3, -1, 0, 12,
      [[tg 8, tg 4168, tg 59912, tg 64072], [tg 3375, tg 7535, tg 63279, tg 67439], [tg 125, tg 4285, tg 60029, tg 64189], [tg 216, tg 4376, tg 60120, tg 64280]],
      [tg 359432, tg 363592, tg 419336, tg 423496]⟩,
    ⟨3, -1, 1, 11,
      [[tg 21, tg 4181, tg 59925, tg 64085], [tg 112, tg 4272, tg 60016, tg 64176], [tg 138, tg 4298, tg 60042, tg 64202], [tg 229, tg 4389, tg 60133, tg 64293]],
      [tg 359445, tg 363605, tg 419349, tg 423509]⟩,
    ⟨3, -1, 2, 10,
      [[tg 34, tg 4194, tg 59938, tg 64098], [tg 125, tg 4285, tg 60029, tg 64189], [tg 164, tg 4324, tg 60068, tg 64228], [tg 242, tg 4402, tg 60146, tg 64306]],
      [tg 359458, tg 363618, tg 419362, tg 423522]⟩,
    ⟨3, -1, 3, 6,
      [[tg 47, tg 4207, tg 59951, tg 64111], [tg 177, tg 4337, tg 60081, tg 64241], [tg 211, tg 1048, tg 5203, tg 60952], [tg 255, tg 4415, tg 60159, tg 64319]],
      [tg 359471, tg 363631, tg 419375, tg 423535]⟩,
    ⟨3, -1, 4, 9,
      [[tg 60, tg 4220, tg 59964, tg 64124], [tg 86, tg 4246, tg 59990, tg 64150], [tg 138, tg 4298, tg 60042, tg 64202], [tg 190, tg 4350, tg 60094, tg 64254], [tg 268, tg 4428, tg 60172, tg 64332]],
      [tg 479292, tg 483452, tg 539196, tg 543356]⟩,
    ⟨3, -1, 5, 7,
      [[tg 73, tg 4233, tg 59977, tg 64137], [tg 99, tg 4259, tg 60003, tg 64163], [tg 151, tg 4311, tg 60055, tg 64215], [tg 203, tg 4363, tg 60107, tg 64267], [tg 281, tg 4441, tg 60185, tg 64345]],
      [tg 479305, tg 483465, tg 539209, tg 543369]⟩,
    ⟨3, -1, 6, 9,
      [[tg 86, tg 4246, tg 59990, tg 64150], [tg 164, tg 4324, tg 60068, tg 64228], [tg 203, tg 4363, tg 60107, tg 64267], [tg 268, tg 4428, tg 60172, tg 64332], [tg 294, tg 4454, tg 60198, tg 64358]],
      [tg 479318, tg 483478, tg 539222, tg 543382]⟩,
    ⟨3, -1, 7, 8,
      [[tg 99, tg 4259, tg 60003, tg 64163], [tg 177, tg 4337, tg 60081, tg 64241], [tg 190, tg 4350, tg 60094, tg 64254], [tg 281, tg 4441, tg 60185, tg 64345], [tg 307, tg 4467, tg 60211, tg 64371]],
      [tg 479331, tg 483491, tg 539235, tg 543395]⟩,
    ⟨4, -1, 0, 13,
      [[tg 112, tg 4272, tg 60016, tg 64176], [tg 3479, tg 7639, tg 63383, tg 67543], [tg 229, tg 4389, tg 60133, tg 64293], [tg 320, tg 4480, tg 60224, tg 64384]],
      [tg 359536, tg 363696, tg 419440, tg 423600]⟩,
    ⟨4, -1, 1, 12,
      [[tg 125, tg 4285, tg 60029, tg 64189], [tg 216, tg 4376, tg 60120, tg 64280], [tg 242, tg 4402, tg 60146, tg 64306], [tg 333, tg 4493, tg 60237, tg 64397]],
      [tg 359549, tg 363709, tg 419453, tg 423613]⟩,
    ⟨4, -1, 2, 11,
      [[tg 138, tg 4298, tg 60042, tg 64202], [tg 229, tg 4389, tg 60133, tg 64293], [tg 268, tg 4428, tg 60172, tg 64332], [tg 346, tg 4506, tg 60250, tg 64410]],
      [tg 359562, tg 363722, tg 419466, tg 423626]⟩,
    ⟨4, -1, 3, 7,
      [[tg 151, tg 4311, tg 60055, tg 64215], [tg 281, tg 4441, tg 60185, tg 64345], [tg 315, tg 1152, tg 5307, tg 61056], [tg 359, tg 4519, tg 60263, tg 64423]],
      [tg 359575, tg 363735, tg 419479, tg 423639]⟩,
    ⟨4, -1, 4, 10,
      [[tg 164, tg 4324, tg 60068, tg 64228], [tg 190, tg 4350, tg 60094, tg 64254], [tg 242, tg 4402, tg 60146, tg 64306], [tg 294, tg 4454, tg 60198, tg 64358], [tg 372, tg 4532, tg 60276, tg 64436]],
      [tg 479396, tg 483556, tg 539300, tg 543460]⟩,
    ⟨4, -1, 5, 8,
      [[tg 177, tg 4337, tg 60081, tg 64241], [tg 203, tg 4363, tg 60107, tg 64267], [tg 255, tg 4415, tg 60159, tg 64319], [tg 307, tg 4467, tg 60211, tg 64371], [tg 385, tg 4545, tg 60289, tg 64449]],
      [tg 479409, tg 483569, tg 539313, tg 543473]⟩,
    ⟨4, -1, 6, 10,
      [[tg 190, tg 4350, tg 60094, tg 64254], [tg 268, tg 4428, tg 60172, tg 64332], [tg 307, tg 4467, tg 60211, tg 64371], [tg 372, tg 4532, tg 60276, tg 64436], [tg 398, tg 4558, tg 60302, tg 64462]],
      [tg 479422, tg 483582, tg 539326, tg 543486]⟩,
    ⟨4, -1, 7, 9,
      [[tg 203, tg 4363, tg 60107, tg 64267], [tg 281, tg 4441, tg 60185, tg 64345], [tg 294, tg 4454, tg 60198, tg 64358], [tg 385, tg 4545, tg 60289, tg 64449], [tg 411, tg 4571, tg 60315, tg 64475]],
      [tg 479435, tg 483595, tg 539339, tg 543499]⟩,
    ⟨5, -1, 0, 14,
      [[tg 216, tg 4376, tg 60120, tg 64280], [tg 3583, tg 7743, tg 63487, tg 67647], [tg 333, tg 4493, tg 60237, tg 64397], [tg 424, tg 4584, tg 60328, tg 64488]],
      [tg 359640, tg 363800, tg 419544, tg 423704]⟩,
    ⟨5, -1, 1, 13,
      [[tg 229, tg 4389, tg 60133, tg 64293], [tg 320, tg 4480, tg 60224, tg 64384], [tg 346, tg 4506, tg 60250, tg 64410], [tg 437, tg 4597, tg 60341, tg 64501]],
      [tg 359653, tg 363813, tg 419557, tg 423717]⟩,
    ⟨5, -1, 2, 12,
      [[tg 242, tg 4402, tg 60146, tg 64306], [tg 333, tg 4493, tg 60237, tg 64397], [tg 372, tg 4532, tg 60276, tg 64436], [tg 450, tg 4610, tg 60354, tg 64514]],
      [tg 359666, tg 363826, tg 419570, tg 423730]⟩,
    ⟨5, -1, 3, 8,
      [[tg 255, tg 4415, tg 60159, tg 64319], [tg 385, tg 4545, tg 60289, tg 64449], [tg 419, tg 1256, tg 5411, tg 61160], [tg 463, tg 4623, tg 60367, tg 64527]],
      [tg 359679, tg 363839, tg 419583, tg 423743]⟩,
    ⟨5, -1, 4, 11,
      [[tg 268, tg 4428, tg 60172, tg 64332], [tg 294, tg 4454, tg 60198, tg 64358], [tg 346, tg 4506, tg 60250, tg 64410], [tg 398, tg 4558, tg 60302, tg 64462], [tg 476, tg 4636, tg 60380, tg 64540]],
      [tg 479500, tg 483660, tg 539404, tg 543564]⟩,
    ⟨5, -1, 5, 9,
      [[tg 281, tg 4441, tg 60185, tg 64345], [tg 307, tg 4467, tg 60211, tg 64371], [tg 359, tg 4519, tg 60263, tg 64423], [tg 411, tg 4571, tg 60315, tg 64475], [tg 489, tg 4649, tg 60393, tg 64553]],
      [tg 479513, tg 483673, tg 539417, tg 543577]⟩,
    ⟨5, -1, 6, 11,
      [[tg 294, tg 4454, tg 60198, tg 64358], [tg 372, tg 4532, tg 60276, tg 64436], [tg 411, tg 4571, tg 60315, tg 64475], [tg 476, tg 4636, tg 60380, tg 64540], [tg 502, tg 4662, tg 60406, tg 64566]],
      [tg 479526, tg 483686, tg 539430, tg 543590]⟩,
    ⟨5, -1, 7, 10,
      [[tg 307, tg 4467, tg 60211, tg 64371], [tg 385, tg 4545, tg 60289, tg 64449], [tg 398, tg 4558, tg 60302, tg 64462], [tg 489, tg 4649, tg 60393, tg 64553], [tg 515, tg 4675, tg 60419, tg 64579]],
      [tg 479539, tg 483699, tg 539443, tg 543603]⟩,
    ⟨6, -1, 0, 15,
      [[tg 320, tg 4480, tg 60224, tg 64384], [tg 3687, tg 7847, tg 63591, tg 67751], [tg 437, tg 4597, tg 60341, tg 64501], [tg 528, tg 4688, tg 60432, tg 64592]],
      [tg 359744, tg 363904, tg 419648, tg 423808]⟩,
    ⟨6, -1, 1, 14,
      [[tg 333, tg 4493, tg 60237, tg 64397], [tg 424, tg 4584, tg 60328, tg 64488], [tg 450, tg 4610, tg 60354, tg 64514], [tg 541, tg 4701, tg 60445, tg 64605]],
      [tg 359757, tg 363917, tg 419661, tg 423821]⟩,
    ⟨6, -1, 2, 13,
      [[tg 346, tg 4506, tg 60250, tg 64410], [tg 437, tg 4597, tg 60341, tg 64501], [tg 476, tg 4636, tg 60380, tg 64540], [tg 554, tg 4714, tg 60458, tg 64618]],
      [tg 359770, tg 363930, tg 419674, tg 423834]⟩,
    ⟨6, -1, 3, 9,
      [[tg 359, tg 4519, tg 60263, tg 64423], [tg 489, tg 4649, tg 60393, tg 64553], [tg 523, tg 1360, tg 5515, tg 61264], [tg 567, tg 4727, tg 60471, tg 64631]],
      [tg 359783, tg 363943, tg 419687, tg 423847]⟩,
    ⟨6, -1, 4, 12,
      [[tg 372, tg 4532, tg 60276, tg 64436], [tg 398, tg 4558, tg 60302, tg 64462], [tg 450, tg 4610, tg 60354, tg 64514], [tg 502, tg 4662, tg 60406, tg 64566], [tg 580, tg 4740, tg 60484, tg 64644]],
      [tg 479604, tg 483764, tg 539508, tg 543668]⟩,
    ⟨6, -1, 5, 10,
      [[tg 385, tg 4545, tg 60289, tg 64449], [tg 411, tg 4571, tg 60315, tg 64475], [tg 463, tg 4623, tg 60367, tg 64527], [tg 515, tg 4675, tg 60419, tg 64579], [tg 593, tg 4753, tg 60497, tg 64657]],
      [tg 479617, tg 483777, tg 539521, tg 543681]⟩,
    ⟨6, -1, 6, 12,
      [[tg 398, tg 4558, tg 60302, tg 64462], [tg 476, tg 4636, tg 60380, tg 64540], [tg 515, tg 4675, tg 60419, tg 64579], [tg 580, tg 4740, tg 60484, tg 64644], [tg 606, tg 4766, tg 60510, tg 64670]],
      [tg 479630, tg 483790, tg 539534, tg 543694]⟩,
    ⟨6, -1, 7, 11,
      [[tg 411, tg 4571, tg 60315, tg 64475], [tg 489, tg 4649, tg 60393, tg 64553], [tg 502, tg 4662, tg 60406, tg 64566], [tg 593, tg 4753, tg 60497, tg 64657], [tg 619, tg 4779, tg 60523, tg 64683]],
      [tg 479643, tg 483803, tg 539547, tg 543707]⟩,
    ⟨7, -1, 0, 16,
      [[tg 424, tg 4584, tg 60328, tg 64488], [tg 3791, tg 7951, tg 63695, tg 67855], [tg 541, tg 4701, tg 60445, tg 64605], [tg 632, tg 4792, tg 60536, tg 64696]],
      [tg 359848, tg 364008, tg 419752, tg 423912]⟩,
    ⟨7, -1, 1, 15,
      [[tg 437, tg 4597, tg 60341, tg 64501], [tg 528, tg 4688, tg 60432, tg 64592], [tg 554, tg 4714, tg 60458, tg 64618], [tg 645, tg 4805, tg 60549, tg 64709]],
      [tg 359861, tg 364021, tg 419765, tg 423925]⟩,
    ⟨7, -1, 2, 14,
      [[tg 450, tg 4610, tg 60354, tg 64514], [tg 541, tg 4701, tg 60445, tg 64605], [tg 580, tg 4740, tg 60484, tg 64644], [tg 658, tg 4818, tg 60562, tg 64722]],
      [tg 359874, tg 364034, tg 419778, tg 423938]⟩,
    ⟨7, -1, 3, 10,
      [[tg 463, tg 4623, tg 60367, tg 64527], [tg 593, tg 4753, tg 60497, tg 64657], [tg 627, tg 1464, tg 5619, tg 61368], [tg 671, tg 4831, tg 60575, tg 64735]],
      [tg 359887, tg 364047, tg 419791, tg 423951]⟩,
    ⟨7, -1, 4, 13,
      [[tg 476, tg 4636, tg 60380, tg 64540], [tg 502, tg 4662, tg 60406, tg 64566], [tg 554, tg 4714, tg 60458, tg 64618], [tg 606, tg 4766, tg 60510, tg 64670], [tg 684, tg 4844, tg 60588, tg 64748]],
      [tg 479708, tg 483868, tg 539612, tg 543772]⟩,
    ⟨7, -1, 5, 11,
      [[tg 489, tg 4649, tg 60393, tg 64553], [tg 515, tg 4675, tg 60419, tg 64579], [tg 567, tg 4727, tg 60471, tg 64631], [tg 619, tg 4779, tg 60523, tg 64683], [tg 697, tg 4857, tg 60601, tg 64761]],
      [tg 479721, tg 483881, tg 539625, tg 543785]⟩,
    ⟨7, -1, 6, 13,
      [[tg 502, tg 4662, tg 60406, tg 64566], [tg 580, tg 4740, tg 60484, tg 64644], [tg 619, tg 4779, tg 60523, tg 64683], [tg 684, tg 4844, tg 60588, tg 64748], [tg 710, tg 4870, tg 60614, tg 64774]],
      [tg 479734, tg 483894, tg 539638, tg 543798]⟩,
    ⟨7, -1, 7, 12,
      [[tg 515, tg 4675, tg 60419, tg 64579], [tg 593, tg 4753, tg 60497, tg 64657], [tg 606, tg 4766, tg 60510, tg 64670], [tg 697, tg 4857, tg 60601, tg 64761], [tg 723, tg 4883, tg 60627, tg 64787]],
      [tg 479747, tg 483907, tg 539651, tg 543811]⟩,
    ⟨8, -1, 0, 17,
      [[tg 528, tg 4688, tg 60432, tg 64592], [tg 3895, tg 8055, tg 63799, tg 67959], [tg 645, tg 4805, tg 60549, tg 64709], [tg 736, tg 4896, tg 60640, tg 64800]],
      [tg 359952, tg 364112, tg 419856, tg 424016]⟩,
    ⟨8, -1, 1, 16,
      [[tg 541, tg 4701, tg 60445, tg 64605], [tg 632, tg 4792, tg 60536, tg 64696], [tg 658, tg 4818, tg 60562, tg 64722], [tg 749, tg 4909, tg 60653, tg 64813]],
      [tg 359965, tg 364125, tg 419869, tg 424029]⟩,
    ⟨8, -1, 2, 15,
      [[tg 554, tg 4714, tg 60458, tg 64618], [tg 645, tg 4805, tg 60549, tg 64709], [tg 684, tg 4844, tg 60588, tg 64748], [tg 762, tg 4922, tg 60666, tg 64826]],
      [tg 359978, tg 364138, tg 419882, tg 424042]⟩,
    ⟨8, -1, 3, 11,
      [[tg 567, tg 4727, tg 60471, tg 64631], [tg 697, tg 4857, tg 60601, tg 64761], [tg 731, tg 1568, tg 5723, tg 61472], [tg 775, tg 4935, tg 60679, tg 64839]],
      [tg 359991, tg 364151, tg 419895, tg 424055]⟩,
    ⟨8, -1, 4, 14,
      [[tg 580, tg 4740, tg 60484, tg 64644], [tg 606, tg 4766, tg 60510, tg 64670], [tg 658, tg 4818, tg 60562, tg 64722], [tg 710, tg 4870, tg 60614, tg 64774], [tg 788, tg 4948, tg 60692, tg 64852]],
      [tg 479812, tg 483972, tg 539716, tg 543876]⟩,
    ⟨8, -1, 5, 12,
      [[tg 593, tg 4753, tg 60497, tg 64657], [tg 619, tg 4779, tg 60523, tg 64683], [tg 671, tg 4831, tg 60575, tg 64735], [tg 723, tg 4883, tg 60627, tg 64787], [tg 801, tg 4961, tg 60705, tg 64865]],
      [tg 479825, tg 483985, tg 539729, tg 543889]⟩,
    ⟨8, -1, 6, 14,
      [[tg 606, tg 4766, tg 60510, tg 64670], [tg 684, tg 4844, tg 60588, tg 64748], [tg 723, tg 4883, tg 60627, tg 64787], [tg 788, tg 4948, tg 60692, tg 64852], [tg 814, tg 4974, tg 60718, tg 64878]],
      [tg 479838, tg 483998, tg 539742, tg 543902]⟩,
    ⟨8, -1, 7, 13,
      [[tg 619, tg 4779, tg 60523, tg 64683], [tg 697, tg 4857, tg 60601, tg 64761], [tg 710, tg 4870, tg 60614, tg 64774], [tg 801, tg 4961, tg 60705, tg 64865], [tg 827, tg 4987, tg 60731, tg 64891]],
      [tg 479851, tg 484011, tg 539755, tg 543915]⟩,
    ⟨9, -1, 0, 18,
      [[tg 632, tg 4792, tg 60536, tg 64696], [tg 3999, tg 8159, tg 63903, tg 68063], [tg 749, tg 4909, tg 60653, tg 64813], [tg 39944, tg 44104, tg 99848, tg 104008]],
      [tg 360056, tg 364216, tg 419960, tg 424120]⟩,
    ⟨9, -1, 1, 17,
      [[tg 645, tg 4805, tg 60549, tg 64709], [tg 736, tg 4896, tg 60640, tg 64800], [tg 762, tg 4922, tg 60666, tg 64826], [tg 39957, tg 44117, tg 99861, tg 104021]],
      [tg 360069, tg 364229, tg 419973, tg 424133]⟩,
    ⟨9, -1, 2, 16,
      [[tg 658, tg 4818, tg 60562, tg 64722], [tg 749, tg 4909, tg 60653, tg 64813], [tg 788, tg 4948, tg 60692, tg 64852], [tg 39970, tg 44130, tg 99874, tg 104034]],
      [tg 360082, tg 364242, tg 419986, tg 424146]⟩,
    ⟨9, -1, 3, 12,
      [[tg 671, tg 4831, tg 60575, tg 64735], [tg 801, tg 4961, tg 60705, tg 64865], [tg 3331, tg 40776, tg 8323, tg 100680], [tg 39983, tg 44143, tg 99887, tg 104047]],
      [tg 360095, tg 364255, tg 419999, tg 424159]⟩,
    ⟨9, -1, 4, 15,
      [[tg 684, tg 4844, tg 60588, tg 64748], [tg 710, tg 4870, tg 60614, tg 64774], [tg 762, tg 4922, tg 60666, tg 64826], [tg 814, tg 4974, tg 60718, tg 64878], [tg 39996, tg 44156, tg 99900, tg 104060]],
      [tg 479916, tg 484076, tg 539820, tg 543980]⟩,
    ⟨9, -1, 5, 13,
      [[tg 697, tg 4857, tg 60601, tg 64761], [tg 723, tg 4883, tg 60627, tg 64787], [tg 775, tg 4935, tg 60679, tg 64839], [tg 827, tg 4987, tg 60731, tg 64891], [tg 40009, tg 44169, tg 99913, tg 104073]],
      [tg 479929, tg 484089, tg 539833, tg 543993]⟩,
    ⟨9, -1, 6, 15,
      [[tg 710, tg 4870, tg 60614, tg 64774], [tg 788, tg 4948, tg 60692, tg 64852], [tg 827, tg 4987, tg 60731, tg 64891], [tg 39996, tg 44156, tg 99900, tg 104060], [tg 40022, tg 44182, tg 99926, tg 104086]],
      [tg 479942, tg 484102, tg 539846, tg 544006]⟩,
    ⟨9, -1, 7, 14,
      [[tg 723, tg 4883, tg 60627, tg 64787], [tg 801, tg 4961, tg 60705, tg 64865], [tg 814, tg 4974, tg 60718, tg 64878], [tg 40009, tg 44169, tg 99913, tg 104073], [tg 40035, tg 44195, tg 99939, tg 104099]],
      [tg 479955, tg 484115, tg 539859, tg 544019]⟩]⟩,
  ⟨2, 8, 0, 1, 1, [(1, -1, 1), (0, 8, 1)], 1, -1, 1, 8, 0, 8, 1, 8,
   [⟨2, 1, 0, 7,
      [[tg 4, tg 1569, tg 4996, tg 61473], [tg 146, tg 4306, tg 20120, tg 24280], [tg 22, tg 4182, tg 59926, tg 64086], [tg 113, tg 4273, tg 60017, tg 64177]],
      [tg 359428, tg 360993, tg 364420, tg 420897]⟩,
    ⟨2, 1, 1, 8,
      [[tg 17, tg 1582, tg 5009, tg 61486], [tg 9, tg 4169, tg 59913, tg 64073], [tg 35, tg 4195, tg 59939, tg 64099], [tg 126, tg 4286, tg 60030, tg 64190]],
      [tg 359441, tg 361006, tg 364433, tg 420910]⟩,
    ⟨2, 1, 2, 9,
      [[tg 30, tg 1595, tg 5022, tg 61499], [tg 22, tg 4182, tg 59926, tg 64086], [tg 61, tg 4221, tg 59965, tg 64125], [tg 139, tg 4299, tg 60043, tg 64203]],
      [tg 359454, tg 361019, tg 364446, tg 420923]⟩,
    ⟨2, 1, 3, 13,
      [[tg 43, tg 1608, tg 5035, tg 61512], [tg 74, tg 4234, tg 59978, tg 64138], [tg 3332, tg 41505, tg 8324, tg 101409], [tg 152, tg 4312, tg 60056, tg 64216]],
      [tg 239690, tg 361032, tg 299594, tg 420936]⟩,
    ⟨2, 1, 4, 10,
      [[tg 56, tg 1621, tg 5048, tg 61525], [tg 82, tg 1647, tg 5074, tg 61551], [tg 35, tg 4195, tg 59939, tg 64099], [tg 87, tg 4247, tg 59991, tg 64151], [tg 165, tg 4325, tg 60069, tg 64229]],
      [tg 479288, tg 480853, tg 484280, tg 540757]⟩,
    ⟨2, 1, 5, 12,
      [[tg 69, tg 1634, tg 5061, tg 61538], [tg 95, tg 1660, tg 5087, tg 61564], [tg 48, tg 4208, tg 59952, tg 64112], [tg 100, tg 4260, tg 60004, tg 64164], [tg 178, tg 4338, tg 60082, tg 64242]],
      [tg 359519, tg 480866, tg 364511, tg 540770]⟩,
    ⟨2, 1, 6, 11,
      [[tg 82, tg 1647, tg 5074, tg 61551], [tg 61, tg 4221, tg 59965, tg 64125], [tg 100, tg 4260, tg 60004, tg 64164], [tg 165, tg 4325, tg 60069, tg 64229], [tg 191, tg 4351, tg 60095, tg 64255]],
      [tg 479314, tg 480879, tg 484306, tg 540783]⟩,
    ⟨2, 1, 7, 12,
      [[tg 95, tg 1660, tg 5087, tg 61564], [tg 74, tg 4234, tg 59978, tg 64138], [tg 87, tg 4247, tg 59991, tg 64151], [tg 178, tg 4338, tg 60082, tg 64242], [tg 204, tg 4364, tg 60108, tg 64268]],
      [tg 479327, tg 480892, tg 484319, tg 540796]⟩,
    ⟨3, 1, 0, 8,
      [[tg 9, tg 4169, tg 59913, tg 64073], [tg 250, tg 4410, tg 20224, tg 24384], [tg 126, tg 4286, tg 60030, tg 64190], [tg 217, tg 4377, tg 60121, tg 64281]],
      [tg 359433, tg 363593, tg 419337, tg 423497]⟩,
    ⟨3, 1, 1, 9,
      [[tg 22, tg 4182, tg 59926, tg 64086], [tg 113, tg 4273, tg 60017, tg 64177], [tg 139, tg 4299, tg 60043, tg 64203], [tg 230, tg 4390, tg 60134, tg 64294]],
      [tg 359446, tg 363606, tg 419350, tg 423510]⟩,
    ⟨3, 1, 2, 10,
      [[tg 35, tg 4195, tg 59939, tg 64099], [tg 126, tg 4286, tg 60030, tg 64190], [tg 165, tg 4325, tg 60069, tg 64229], [tg 243, tg 4403, tg 60147, tg 64307]],
      [tg 359459, tg 363619, tg 419363, tg 423523]⟩,
    ⟨3, 1, 3, 14,
      [[tg 48, tg 4208, tg 59952, tg 64112], [tg 178, tg 4338, tg 60082, tg 64242], [tg 39945, tg 44105, tg 99849, tg 104009], [tg 256, tg 4416, tg 60160, tg 64320]],
      [tg 359472, tg 363632, tg 419376, tg 423536]⟩,
    ⟨3, 1, 4, 11,
      [[tg 61, tg 4221, tg 59965, tg 64125], [tg 87, tg 4247, tg 59991, tg 64151], [tg 139, tg 4299, tg 60043, tg 64203], [tg 191, tg 4351, tg 60095, tg 64255], [tg 269, tg 4429, tg 60173, tg 64333]],
      [tg 479293, tg 483453, tg 539197, tg 543357]⟩,
    ⟨3, 1, 5, 13,
      [[tg 74, tg 4234, tg 59978, tg 64138], [tg 100, tg 4260, tg 60004, tg 64164], [tg 152, tg 4312, tg 60056, tg 64216], [tg 204, tg 4364, tg 60108, tg 64268], [tg 282, tg 4442, tg 60186, tg 64346]],
      [tg 479306, tg 483466, tg 539210, tg 543370]⟩,
    ⟨3, 1, 6, 12,
      [[tg 87, tg 4247, tg 59991, tg 64151], [tg 165, tg 4325, tg 60069, tg 64229], [tg 204, tg 4364, tg 60108, tg 64268], [tg 269, tg 4429, tg 60173, tg 64333], [tg 295, tg 4455, tg 60199, tg 64359]],
      [tg 479319, tg 483479, tg 539223, tg 543383]⟩,
    ⟨3, 1, 7, 13,
      [[tg 100, tg 4260, tg 60004, tg 64164], [tg 178, tg 4338, tg 60082, tg 64242], [tg 191, tg 4351, tg 60095, tg 64255], [tg 282, tg 4442, tg 60186, tg 64346], [tg 308, tg 4468, tg 60212, tg 64372]],
      [tg 479332, tg 483492, tg 539236, tg 543396]⟩,
    ⟨4, 1, 0, 9,
      [[tg 113, tg 4273, tg 60017, tg 64177], [tg 354, tg 4514, tg 20328, tg 24488], [tg 230, tg 4390, tg 60134, tg 64294], [tg 321, tg 4481, tg 60225, tg 64385]],
      [tg 359537, tg 363697, tg 419441, tg 423601]⟩,
    ⟨4, 1, 1, 10,
      [[tg 126, tg 4286, tg 60030, tg 64190], [tg 217, tg 4377, tg 60121, tg 64281], [tg 243, tg 4403, tg 60147, tg 64307], [tg 334, tg 4494, tg 60238, tg 64398]],
      [tg 359550, tg 363710, tg 419454, tg 423614]⟩,
    ⟨4, 1, 2, 11,
      [[tg 139, tg 4299, tg 60043, tg 64203], [tg 230, tg 4390, tg 60134, tg 64294], [tg 269, tg 4429, tg 60173, tg 64333], [tg 347, tg 4507, tg 60251, tg 64411]],
      [tg 359563, tg 363723, tg 419467, tg 423627]⟩,
    ⟨4, 1, 3, 15,
      [[tg 152, tg 4312, tg 60056, tg 64216], [tg 282, tg 4442, tg 60186, tg 64346], [tg 40049, tg 44209, tg 99953, tg 104113], [tg 360, tg 4520, tg 60264, tg 64424]],
      [tg 359576, tg 363736, tg 419480, tg 423640]⟩,
    ⟨4, 1, 4, 12,
      [[tg 165, tg 4325, tg 60069, tg 64229], [tg 191, tg 4351, tg 60095, tg 64255], [tg 243, tg 4403, tg 60147, tg 64307], [tg 295, tg 4455, tg 60199, tg 64359], [tg 373, tg 4533, tg 60277, tg 64437]],
      [tg 479397, tg 483557, tg 539301, tg 543461]⟩,
    ⟨4, 1, 5, 14,
      [[tg 178, tg 4338, tg 60082, tg 64242], [tg 204, tg 4364, tg 60108, tg 64268], [tg 256, tg 4416, tg 60160, tg 64320], [tg 308, tg 4468, tg 60212, tg 64372], [tg 386, tg 4546, tg 60290, tg 64450]],
      [tg 479410, tg 483570, tg 539314, tg 543474]⟩,
    ⟨4, 1, 6, 13,
      [[tg 191, tg 4351, tg 60095, tg 64255], [tg 269, tg 4429, tg 60173, tg 64333], [tg 308, tg 4468, tg 60212, tg 64372], [tg 373, tg 4533, tg 60277, tg 64437], [tg 399, tg 4559, tg 60303, tg 64463]],
      [tg 479423, tg 483583, tg 539327, tg 543487]⟩,
    ⟨4, 1, 7, 14,
      [[tg 204, tg 4364, tg 60108, tg 64268], [tg 282, tg 4442, tg 60186, tg 64346], [tg 295, tg 4455, tg 60199, tg 64359], [tg 386, tg 4546, tg 60290, tg 64450], [tg 412, tg 4572, tg 60316, tg 64476]],
      [tg 479436, tg 483596, tg 539340, tg 543500]⟩,
    ⟨5, 1, 0, 10,
      [[tg 217, tg 4377, tg 60121, tg 64281], [tg 458, tg 4618, tg 20432, tg 24592], [tg 334, tg 4494, tg 60238, tg 64398], [tg 425, tg 4585, tg 60329, tg 64489]],
      [tg 359641, tg 363801, tg 419545, tg 423705]⟩,
    ⟨5, 1, 1, 11,
      [[tg 230, tg 4390, tg 60134, tg 64294], [tg 321, tg 4481, tg 60225, tg 64385], [tg 347, tg 4507, tg 60251, tg 64411], [tg 438, tg 4598, tg 60342, tg 64502]],
      [tg 359654, tg 363814, tg 419558, tg 423718]⟩,
    ⟨5, 1, 2, 12,
      [[tg 243, tg 4403, tg 60147, tg 64307], [tg 334, tg 4494, tg 60238, tg 64398], [tg 373, tg 4533, tg 60277, tg 64437], [tg 451, tg 4611, tg 60355, tg 64515]],
      [tg 359667, tg 363827, tg 419571, tg 423731]⟩,
    ⟨5, 1, 3, 16,
      [[tg 256, tg 4416, tg 60160, tg 64320], [tg 386, tg 4546, tg 60290, tg 64450], [tg 40153, tg 44313, tg 100057, tg 104217], [tg 464, tg 4624, tg 60368, tg 64528]],
      [tg 359680, tg 363840, tg 419584, tg 423744]⟩,
    ⟨5, 1, 4, 13,
      [[tg 269, tg 4429, tg 60173, tg 64333], [tg 295, tg 4455, tg 60199, tg 64359], [tg 347, tg 4507, tg 60251, tg 64411], [tg 399, tg 4559, tg 60303, tg 64463], [tg 477, tg 4637, tg 60381, tg 64541]],
      [tg 479501, tg 483661, tg 539405, tg 543565]⟩,
    ⟨5, 1, 5, 15,
      [[tg 282, tg 4442, tg 60186, tg 64346], [tg 308, tg 4468, tg 60212, tg 64372], [tg 360, tg 4520, tg 60264, tg 64424], [tg 412, tg 4572, tg 60316, tg 64476], [tg 490, tg 4650, tg 60394, tg 64554]],
      [tg 479514, tg 483674, tg 539418, tg 543578]⟩,
    ⟨5, 1, 6, 14,
      [[tg 295, tg 4455, tg 60199, tg 64359], [tg 373, tg 4533, tg 60277, tg 64437], [tg 412, tg 4572, tg 60316, tg 64476], [tg 477, tg 4637, tg 60381, tg 64541], [tg 503, tg 4663, tg 60407, tg 64567]],
      [tg 479527, tg 483687, tg 539431, tg 543591]⟩,
    ⟨5, 1, 7, 15,
      [[tg 308, tg 4468, tg 60212, tg 64372], [tg 386, tg 4546, tg 60290, tg 64450], [tg 399, tg 4559, tg 60303, tg 64463], [tg 490, tg 4650, tg 60394, tg 64554], [tg 516, tg 4676, tg 60420, tg 64580]],
      [tg 479540, tg 483700, tg 539444, tg 543604]⟩,
    ⟨6, 1, 0, 11,
      [[tg 321, tg 4481, tg 60225, tg 64385], [tg 562, tg 4722, tg 20536, tg 24696], [tg 438, tg 4598, tg 60342, tg 64502], [tg 529, tg 4689, tg 60433, tg 64593]],
      [tg 359745, tg 363905, tg 419649, tg 423809]⟩,
    ⟨6, 1, 1, 12,
      [[tg 334, tg 4494, tg 60238, tg 64398], [tg 425, tg 4585, tg 60329, tg 64489], [tg 451, tg 4611, tg 60355, tg 64515], [tg 542, tg 4702, tg 60446, tg 64606]],
      [tg 359758, tg 363918, tg 419662, tg 423822]⟩,
    ⟨6, 1, 2, 13,
      [[tg 347, tg 4507, tg 60251, tg 64411], [tg 438, tg 4598, tg 60342, tg 64502], [tg 477, tg 4637, tg 60381, tg 64541], [tg 555, tg 4715, tg 60459, tg 64619]],
      [tg 359771, tg 363931, tg 419675, tg 423835]⟩,
    ⟨6, 1, 3, 17,
      [[tg 360, tg 4520, tg 60264, tg 64424], [tg 490, tg 4650, tg 60394, tg 64554], [tg 40257, tg 44417, tg 100161, tg 104321], [tg 568, tg 4728, tg 60472, tg 64632]],
      [tg 359784, tg 363944, tg 419688, tg 423848]⟩,
    ⟨6, 1, 4, 14,
      [[tg 373, tg 4533, tg 60277, tg 64437], [tg 399, tg 4559, tg 60303, tg 64463], [tg 451, tg 4611, tg 60355, tg 64515], [tg 503, tg 4663, tg 60407, tg 64567], [tg 581, tg 4741, tg 60485, tg 64645]],
      [tg 479605, tg 483765, tg 539509, tg 543669]⟩,
    ⟨6, 1, 5, 16,
      [[tg 386, tg 4546, tg 60290, tg 64450], [tg 412, tg 4572, tg 60316, tg 64476], [tg 464, tg 4624, tg 60368, tg 64528], [tg 516, tg 4676, tg 60420, tg 64580], [tg 594, tg 4754, tg 60498, tg 64658]],
      [tg 479618, tg 483778, tg 539522, tg 543682]⟩,
    ⟨6, 1, 6, 15,
      [[tg 399, tg 4559, tg 60303, tg 64463], [tg 477, tg 4637, tg 60381, tg 64541], [tg 516, tg 4676, tg 60420, tg 64580], [tg 581, tg 4741, tg 60485, tg 64645], [tg 607, tg 4767, tg 60511, tg 64671]],
      [tg 479631, tg 483791, tg 539535, tg 543695]⟩,
    ⟨6, 1, 7, 16,
      [[tg 412, tg 4572, tg 60316, tg 64476], [tg 490, tg 4650, tg 60394, tg 64554], [tg 503, tg 4663, tg 60407, tg 64567], [tg 594, tg 4754, tg 60498, tg 64658], [tg 620, tg 4780, tg 60524, tg 64684]],
      [tg 479644, tg 483804, tg 539548, tg 543708]⟩,
    ⟨7, 1, 0, 12,
      [[tg 425, tg 4585, tg 60329, tg 64489], [tg 666, tg 4826, tg 20640, tg 24800], [tg 542, tg 4702, tg 60446, tg 64606], [tg 633, tg 4793, tg 60537, tg 64697]],
      [tg 359849, tg 364009, tg 419753, tg 423913]⟩,
    ⟨7, 1, 1, 13,
      [[tg 438, tg 4598, tg 60342, tg 64502], [tg 529, tg 4689, tg 60433, tg 64593], [tg 555, tg 4715, tg 60459, tg 64619], [tg 646, tg 4806, tg 60550, tg 64710]],
      [tg 359862, tg 364022, tg 419766, tg 423926]⟩,
    ⟨7, 1, 2, 14,
      [[tg 451, tg 4611, tg 60355, tg 64515], [tg 542, tg 4702, tg 60446, tg 64606], [tg 581, tg 4741, tg 60485, tg 64645], [tg 659, tg 4819, tg 60563, tg 64723]],
      [tg 359875, tg 364035, tg 419779, tg 423939]⟩,
    ⟨7, 1, 3, 18,
      [[tg 464, tg 4624, tg 60368, tg 64528], [tg 594, tg 4754, tg 60498, tg 64658], [tg 40361, tg 44521, tg 100265, tg 104425], [tg 672, tg 4832, tg 60576, tg 64736]],
      [tg 359888, tg 364048, tg 419792, tg 423952]⟩,
    ⟨7, 1, 4, 15,
      [[tg 477, tg 4637, tg 60381, tg 64541], [tg 503, tg 4663, tg 60407, tg 64567], [tg 555, tg 4715, tg 60459, tg 64619], [tg 607, tg 4767, tg 60511, tg 64671], [tg 685, tg 4845, tg 60589, tg 64749]],
      [tg 479709, tg 483869, tg 539613, tg 543773]⟩,
    ⟨7, 1, 5, 17,
      [[tg 490, tg 4650, tg 60394, tg 64554], [tg 516, tg 4676, tg 60420, tg 64580], [tg 568, tg 4728, tg 60472, tg 64632], [tg 620, tg 4780, tg 60524, tg 64684], [tg 698, tg 4858, tg 60602, tg 64762]],
      [tg 479722, tg 483882, tg 539626, tg 543786]⟩,
    ⟨7, 1, 6, 16,
      [[tg 503, tg 4663, tg 60407, tg 64567], [tg 581, tg 4741, tg 60485, tg 64645], [tg 620, tg 4780, tg 60524, tg 64684], [tg 685, tg 4845, tg 60589, tg 64749], [tg 711, tg 4871, tg 60615, tg 64775]],
      [tg 479735, tg 483895, tg 539639, tg 543799]⟩,
    ⟨7, 1, 7, 17,
      [[tg 516, tg 4676, tg 60420, tg 64580], [tg 594, tg 4754, tg 60498, tg 64658], [tg 607, tg 4767, tg 60511, tg 64671], [tg 698, tg 4858, tg 60602, tg 64762], [tg 724, tg 4884, tg 60628, tg 64788]],
      [tg 479748, tg 483908, tg 539652, tg 543812]⟩,
    ⟨8, 1, 0, 13,
      [[tg 529, tg 4689, tg 60433, tg 64593], [tg 770, tg 4930, tg 20744, tg 24904], [tg 646, tg 4806, tg 60550, tg 64710], [tg 737, tg 4897, tg 60641, tg 64801]],
      [tg 359953, tg 364113, tg 419857, tg 424017]⟩,
    ⟨8, 1, 1, 14,
      [[tg 542, tg 4702, tg 60446, tg 64606], [tg 633, tg 4793, tg 60537, tg 64697], [tg 659, tg 4819, tg 60563, tg 64723], [tg 750, tg 4910, tg 60654, tg 64814]],
      [tg 359966, tg 364126, tg 419870, tg 424030]⟩,
    ⟨8, 1, 2, 15,
      [[tg 555, tg 4715, tg 60459, tg 64619], [tg 646, tg 4806, tg 60550, tg 64710], [tg 685, tg 4845, tg 60589, tg 64749], [tg 763, tg 4923, tg 60667, tg 64827]],
      [tg 359979, tg 364139, tg 419883, tg 424043]⟩,
    ⟨8, 1, 3, 19,
      [[tg 568, tg 4728, tg 60472, tg 64632], [tg 698, tg 4858, tg 60602, tg 64762], [tg 40465, tg 44625, tg 100369, tg 104529], [tg 776, tg 4936, tg 60680, tg 64840]],
      [tg 359992, tg 364152, tg 419896, tg 424056]⟩,
    ⟨8, 1, 4, 16,
      [[tg 581, tg 4741, tg 60485, tg 64645], [tg 607, tg 4767, tg 60511, tg 64671], [tg 659, tg 4819, tg 60563, tg 64723], [tg 711, tg 4871, tg 60615, tg 64775], [tg 789, tg 4949, tg 60693, tg 64853]],
      [tg 479813, tg 483973, tg 539717, tg 543877]⟩,
    ⟨8, 1, 5, 18,
      [[tg 594, tg 4754, tg 60498, tg 64658], [tg 620, tg 4780, tg 60524, tg 64684], [tg 672, tg 4832, tg 60576, tg 64736], [tg 724, tg 4884, tg 60628, tg 64788], [tg 802, tg 4962, tg 60706, tg 64866]],
      [tg 479826, tg 483986, tg 539730, tg 543890]⟩,
    ⟨8, 1, 6, 17,
      [[tg 607, tg 4767, tg 60511, tg 64671], [tg 685, tg 4845, tg 60589, tg 64749], [tg 724, tg 4884, tg 60628, tg 64788], [tg 789, tg 4949, tg 60693, tg 64853], [tg 815, tg 4975, tg 60719, tg 64879]],
      [tg 479839, tg 483999, tg 539743, tg 543903]⟩,
    ⟨8, 1, 7, 18,
      [[tg 620, tg 4780, tg 60524, tg 64684], [tg 698, tg 4858, tg 60602, tg 64762], [tg 711, tg 4871, tg 60615, tg 64775], [tg 802, tg 4962, tg 60706, tg 64866], [tg 828, tg 4988, tg 60732, tg 64892]],
      [tg 479852, tg 484012, tg 539756, tg 543916]⟩,
    ⟨9, 1, 0, 14,
      [[tg 633, tg 4793, tg 60537, tg 64697], [tg 3370, tg 7530, tg 23344, tg 27504], [tg 750, tg 4910, tg 60654, tg 64814], [tg 3337, tg 7497, tg 63241, tg 67401]],
      [tg 360057, tg 364217, tg 419961, tg 424121]⟩,
    ⟨9, 1, 1, 15,
      [[tg 646, tg 4806, tg 60550, tg 64710], [tg 737, tg 4897, tg 60641, tg 64801], [tg 763, tg 4923, tg 60667, tg 64827], [tg 3350, tg 7510, tg 63254, tg 67414]],
      [tg 360070, tg 364230, tg 419974, tg 424134]⟩,
    ⟨9, 1, 2, 16,
      [[tg 659, tg 4819, tg 60563, tg 64723], [tg 750, tg 4910, tg 60654, tg 64814], [tg 789, tg 4949, tg 60693, tg 64853], [tg 3363, tg 7523, tg 63267, tg 67427]],
      [tg 360083, tg 364243, tg 419987, tg 424147]⟩,
    ⟨9, 1, 3, 20,
      [[tg 672, tg 4832, tg 60576, tg 64736], [tg 802, tg 4962, tg 60706, tg 64866], [tg 40569, tg 44729, tg 100473, tg 104633], [tg 3376, tg 7536, tg 63280, tg 67440]],
      [tg 360096, tg 364256, tg 420000, tg 424160]⟩,
    ⟨9, 1, 4, 17,
      [[tg 685, tg 4845, tg 60589, tg 64749], [tg 711, tg 4871, tg 60615, tg 64775], [tg 763, tg 4923, tg 60667, tg 64827], [tg 815, tg 4975, tg 60719, tg 64879], [tg 3389, tg 7549, tg 63293, tg 67453]],
      [tg 479917, tg 484077, tg 539821, tg 543981]⟩,
    ⟨9, 1, 5, 19,
      [[tg 698, tg 4858, tg 60602, tg 64762], [tg 724, tg 4884, tg 60628, tg 64788], [tg 776, tg 4936, tg 60680, tg 64840], [tg 828, tg 4988, tg 60732, tg 64892], [tg 3402, tg 7562, tg 63306, tg 67466]],
      [tg 479930, tg 484090, tg 539834, tg 543994]⟩,
    ⟨9, 1, 6, 18,
      [[tg 711, tg 4871, tg 60615, tg 64775], [tg 789, tg 4949, tg 60693, tg 64853], [tg 828, tg 4988, tg 60732, tg 64892], [tg 3389, tg 7549, tg 63293, tg 67453], [tg 3415, tg 7575, tg 63319, tg 67479]],
      [tg 479943, tg 484103, tg 539847, tg 544007]⟩,
    ⟨9, 1, 7, 19,
      [[tg 724, tg 4884, tg 60628, tg 64788], [tg 802, tg 4962, tg 60706, tg 64866], [tg 815, tg 4975, tg 60719, tg 64879], [tg 3402, tg 7562, tg 63306, tg 67466], [tg 3428, tg 7588, tg 63332, tg 67492]],
      [tg 479956, tg 484116, tg 539860, tg 544020]⟩]⟩,
  ⟨2, 1, 1, -1, 1, [(1, 1, 1), (-1, 1, 1)], 1, 1, 1, 2, -1, 1, 1, 2,
   [⟨0, 1, 0, 6,
      [[tg 5, tg 946, tg 4997, tg 60850], [tg 39, tg 875, tg 1708, tg 20953], [tg 23, tg 4183, tg 59927, tg 64087], [tg 4, tg 4164, tg 20082, tg 24242]],
      [tg 239655, tg 240491, tg 241324, tg 260569]⟩,
    ⟨0, 1, 1, 7,
      [[tg 18, tg 959, tg 5010, tg 60863], [tg 10, tg 4170, tg 59914, tg 64074], [tg 36, tg 4196, tg 59940, tg 64100], [tg 17, tg 4177, tg 20095, tg 24255]],
      [tg 239626, tg 243786, tg 299530, tg 303690]⟩,
    ⟨0, 1, 2, 8,
      [[tg 31, tg 972, tg 5023, tg 60876], [tg 23, tg 4183, tg 59927, tg 64087], [tg 62, tg 4222, tg 59966, tg 64126], [tg 30, tg 4190, tg 20108, tg 24268]],
      [tg 239639, tg 243799, tg 299543, tg 303703]⟩,
    ⟨0, 1, 3, 13,
      [[tg 44, tg 985, tg 5036, tg 60889], [tg 75, tg 4235, tg 59979, tg 64139], [tg 114, tg 4274, tg 60018, tg 64178], [tg 43, tg 4203, tg 20121, tg 24281]],
      [tg 239691, tg 243851, tg 299595, tg 303755]⟩,
    ⟨0, 1, 4, 9,
      [[tg 57, tg 998, tg 5049, tg 60902], [tg 83, tg 1024, tg 5075, tg 60928], [tg 36, tg 4196, tg 59940, tg 64100], [tg 88, tg 4248, tg 59992, tg 64152], [tg 56, tg 4216, tg 20134, tg 24294]],
      [tg 239652, tg 243812, tg 299556, tg 303716]⟩,
    ⟨0, 1, 5, 12,
      [[tg 70, tg 1011, tg 5062, tg 60915], [tg 96, tg 1037, tg 5088, tg 60941], [tg 49, tg 4209, tg 59953, tg 64113], [tg 101, tg 4261, tg 60005, tg 64165], [tg 69, tg 4229, tg 20147, tg 24307]],
      [tg 359520, tg 360461, tg 364512, tg 420365]⟩,
    ⟨0, 1, 6, 10,
      [[tg 83, tg 1024, tg 5075, tg 60928], [tg 62, tg 4222, tg 59966, tg 64126], [tg 101, tg 4261, tg 60005, tg 64165], [tg 56, tg 4216, tg 20134, tg 24294], [tg 82, tg 4242, tg 20160, tg 24320]],
      [tg 359486, tg 363646, tg 419390, tg 423550]⟩,
    ⟨0, 1, 7, 11,
      [[tg 96, tg 1037, tg 5088, tg 60941], [tg 75, tg 4235, tg 59979, tg 64139], [tg 88, tg 4248, tg 59992, tg 64152], [tg 69, tg 4229, tg 20147, tg 24307], [tg 95, tg 4255, tg 20173, tg 24333]],
      [tg 239704, tg 243864, tg 299608, tg 303768]⟩,
    ⟨0, 2, 0, 14,
      [[tg 39946, tg 44106, tg 99850, tg 104010], [tg 49, tg 4209, tg 59953, tg 64113], [tg 127, tg 4287, tg 60031, tg 64191], [tg 3338, tg 7498, tg 63242, tg 67402]],
      [tg 239665, tg 243825, tg 299569, tg 303729]⟩,
    ⟨0, 2, 1, 15,
      [[tg 39959, tg 44119, tg 99863, tg 104023], [tg 114, tg 4274, tg 60018, tg 64178], [tg 140, tg 4300, tg 60044, tg 64204], [tg 3351, tg 7511, tg 63255, tg 67415]],
      [tg 239730, tg 243890, tg 299634, tg 303794]⟩,
    ⟨0, 2, 2, 16,
      [[tg 39972, tg 44132, tg 99876, tg 104036], [tg 127, tg 4287, tg 60031, tg 64191], [tg 166, tg 4326, tg 60070, tg 64230], [tg 3364, tg 7524, tg 63268, tg 67428]],
      [tg 239743, tg 243903, tg 299647, tg 303807]⟩,
    ⟨0, 2, 3, 21,
      [[tg 39985, tg 44145, tg 99889, tg 104049], [tg 179, tg 4339, tg 60083, tg 64243], [tg 43274, tg 47434, tg 103178, tg 107338], [tg 3377, tg 7537, tg 63281, tg 67441]],
      [tg 239795, tg 243955, tg 299699, tg 303859]⟩,
    ⟨0, 2, 4, 17,
      [[tg 39998, tg 44158, tg 99902, tg 104062], [tg 40024, tg 44184, tg 99928, tg 104088], [tg 140, tg 4300, tg 60044, tg 64204], [tg 192, tg 4352, tg 60096, tg 64256], [tg 3390, tg 7550, tg 63294, tg 67454]],
      [tg 239756, tg 243916, tg 299660, tg 303820]⟩,
    ⟨0, 2, 5, 20,
      [[tg 40011, tg 44171, tg 99915, tg 104075], [tg 40037, tg 44197, tg 99941, tg 104101], [tg 153, tg 4313, tg 60057, tg 64217], [tg 205, tg 4365, tg 60109, tg 64269], [tg 3403, tg 7563, tg 63307, tg 67467]],
      [tg 399461, tg 403621, tg 459365, tg 463525]⟩,
    ⟨0, 2, 6, 18,
      [[tg 40024, tg 44184, tg 99928, tg 104088], [tg 166, tg 4326, tg 60070, tg 64230], [tg 205, tg 4365, tg 60109, tg 64269], [tg 3390, tg 7550, tg 63294, tg 67454], [tg 3416, tg 7576, tg 63320, tg 67480]],
      [tg 359590, tg 363750, tg 419494, tg 423654]⟩,
    ⟨0, 2, 7, 19,
      [[tg 40037, tg 44197, tg 99941, tg 104101], [tg 179, tg 4339, tg 60083, tg 64243], [tg 192, tg 4352, tg 60096, tg 64256], [tg 3403, tg 7563, tg 63307, tg 67467], [tg 3429, tg 7589, tg 63333, tg 67493]],
      [tg 239808, tg 243968, tg 299712, tg 303872]⟩]⟩,
  ⟨2, -1, 1, -8, 0, [(0, 8, 1), (-1, -1, 1)], 0, 8, 1, 8, -1, -1, 1, 8,
   [⟨-9, 1, 0, 14,
      [[tg 40675, tg 44835, tg 100579, tg 104739], [tg 3373, tg 41546, tg 8365, tg 101450], [tg 24, tg 4184, tg 59928, tg 64088], [tg 115, tg 4275, tg 60019, tg 64179]],
      [tg 242989, tg 281162, tg 247981, tg 341066]⟩,
    ⟨-9, 1, 1, 15,
      [[tg 40688, tg 44848, tg 100592, tg 104752], [tg 11, tg 4171, tg 59915, tg 64075], [tg 37, tg 4197, tg 59941, tg 64101], [tg 128, tg 4288, tg 60032, tg 64192]],
      [tg 239627, tg 243787, tg 299531, tg 303691]⟩,
    ⟨-9, 1, 2, 16,
      [[tg 40701, tg 44861, tg 100605, tg 104765], [tg 24, tg 4184, tg 59928, tg 64088], [tg 63, tg 4223, tg 59967, tg 64127], [tg 141, tg 4301, tg 60045, tg 64205]],
      [tg 239640, tg 243800, tg 299544, tg 303704]⟩,
    ⟨-9, 1, 3, 20,
      [[tg 40714, tg 44874, tg 100618, tg 104778], [tg 76, tg 4236, tg 59980, tg 64140], [tg 3443, tg 7603, tg 63347, tg 67507], [tg 154, tg 4314, tg 60058, tg 64218]],
      [tg 239692, tg 243852, tg 299596, tg 303756]⟩,
    ⟨-9, 1, 4, 17,
      [[tg 40727, tg 44887, tg 100631, tg 104791], [tg 40753, tg 44913, tg 100657, tg 104817], [tg 37, tg 4197, tg 59941, tg 64101], [tg 89, tg 4249, tg 59993, tg 64153], [tg 167, tg 4327, tg 60071, tg 64231]],
      [tg 239653, tg 243813, tg 299557, tg 303717]⟩,
    ⟨-9, 1, 5, 19,
      [[tg 40740, tg 44900, tg 100644, tg 104804], [tg 40766, tg 44926, tg 100670, tg 104830], [tg 50, tg 4210, tg 59954, tg 64114], [tg 102, tg 4262, tg 60006, tg 64166], [tg 180, tg 4340, tg 60084, tg 64244]],
      [tg 119910, tg 124070, tg 179814, tg 183974]⟩,
    ⟨-9, 1, 6, 17,
      [[tg 40753, tg 44913, tg 100657, tg 104817], [tg 63, tg 4223, tg 59967, tg 64127], [tg 102, tg 4262, tg 60006, tg 64166], [tg 167, tg 4327, tg 60071, tg 64231], [tg 193, tg 4353, tg 60097, tg 64257]],
      [tg 119975, tg 124135, tg 179879, tg 184039]⟩,
    ⟨-9, 1, 7, 18,
      [[tg 40766, tg 44926, tg 100670, tg 104830], [tg 76, tg 4236, tg 59980, tg 64140], [tg 89, tg 4249, tg 59993, tg 64153], [tg 180, tg 4340, tg 60084, tg 64244], [tg 206, tg 4366, tg 60110, tg 64270]],
      [tg 239705, tg 243865, tg 299609, tg 303769]⟩,
    ⟨-8, 1, 0, 13,
      [[tg 11, tg 4171, tg 59915, tg 64075], [tg 773, tg 882, tg 5765, tg 60786], [tg 128, tg 4288, tg 60032, tg 64192], [tg 219, tg 4379, tg 60123, tg 64283]],
      [tg 240389, tg 240498, tg 245381, tg 300402]⟩,
    ⟨-8, 1, 1, 14,
      [[tg 24, tg 4184, tg 59928, tg 64088], [tg 115, tg 4275, tg 60019, tg 64179], [tg 141, tg 4301, tg 60045, tg 64205], [tg 232, tg 4392, tg 60136, tg 64296]],
      [tg 239731, tg 243891, tg 299635, tg 303795]⟩,
    ⟨-8, 1, 2, 15,
      [[tg 37, tg 4197, tg 59941, tg 64101], [tg 128, tg 4288, tg 60032, tg 64192], [tg 167, tg 4327, tg 60071, tg 64231], [tg 245, tg 4405, tg 60149, tg 64309]],
      [tg 239744, tg 243904, tg 299648, tg 303808]⟩,
    ⟨-8, 1, 3, 19,
      [[tg 50, tg 4210, tg 59954, tg 64114], [tg 180, tg 4340, tg 60084, tg 64244], [tg 3547, tg 7707, tg 63451, tg 67611], [tg 258, tg 4418, tg 60162, tg 64322]],
      [tg 239796, tg 243956, tg 299700, tg 303860]⟩,
    ⟨-8, 1, 4, 16,
      [[tg 63, tg 4223, tg 59967, tg 64127], [tg 89, tg 4249, tg 59993, tg 64153], [tg 141, tg 4301, tg 60045, tg 64205], [tg 193, tg 4353, tg 60097, tg 64257], [tg 271, tg 4431, tg 60175, tg 64335]],
      [tg 239757, tg 243917, tg 299661, tg 303821]⟩,
    ⟨-8, 1, 5, 18,
      [[tg 76, tg 4236, tg 59980, tg 64140], [tg 102, tg 4262, tg 60006, tg 64166], [tg 154, tg 4314, tg 60058, tg 64218], [tg 206, tg 4366, tg 60110, tg 64270], [tg 284, tg 4444, tg 60188, tg 64348]],
      [tg 120014, tg 124174, tg 179918, tg 184078]⟩,
    ⟨-8, 1, 6, 16,
      [[tg 89, tg 4249, tg 59993, tg 64153], [tg 167, tg 4327, tg 60071, tg 64231], [tg 206, tg 4366, tg 60110, tg 64270], [tg 271, tg 4431, tg 60175, tg 64335], [tg 297, tg 4457, tg 60201, tg 64361]],
      [tg 120079, tg 124239, tg 179983, tg 184143]⟩,
    ⟨-8, 1, 7, 17,
      [[tg 102, tg 4262, tg 60006, tg 64166], [tg 180, tg 4340, tg 60084, tg 64244], [tg 193, tg 4353, tg 60097, tg 64257], [tg 284, tg 4444, tg 60188, tg 64348], [tg 310, tg 4470, tg 60214, tg 64374]],
      [tg 239809, tg 243969, tg 299713, tg 303873]⟩,
    ⟨-7, 1, 0, 12,
      [[tg 115, tg 4275, tg 60019, tg 64179], [tg 669, tg 986, tg 5661, tg 60890], [tg 232, tg 4392, tg 60136, tg 64296], [tg 323, tg 4483, tg 60227, tg 64387]],
      [tg 240285, tg 240602, tg 245277, tg 300506]⟩,
    ⟨-7, 1, 1, 13,
      [[tg 128, tg 4288, tg 60032, tg 64192], [tg 219, tg 4379, tg 60123, tg 64283], [tg 245, tg 4405, tg 60149, tg 64309], [tg 336, tg 4496, tg 60240, tg 64400]],
      [tg 239835, tg 243995, tg 299739, tg 303899]⟩,
    ⟨-7, 1, 2, 14,
      [[tg 141, tg 4301, tg 60045, tg 64205], [tg 232, tg 4392, tg 60136, tg 64296], [tg 271, tg 4431, tg 60175, tg 64335], [tg 349, tg 4509, tg 60253, tg 64413]],
      [tg 239848, tg 244008, tg 299752, tg 303912]⟩,
    ⟨-7, 1, 3, 18,
      [[tg 154, tg 4314, tg 60058, tg 64218], [tg 284, tg 4444, tg 60188, tg 64348], [tg 3651, tg 7811, tg 63555, tg 67715], [tg 362, tg 4522, tg 60266, tg 64426]],
      [tg 239900, tg 244060, tg 299804, tg 303964]⟩,
    ⟨-7, 1, 4, 15,
      [[tg 167, tg 4327, tg 60071, tg 64231], [tg 193, tg 4353, tg 60097, tg 64257], [tg 245, tg 4405, tg 60149, tg 64309], [tg 297, tg 4457, tg 60201, tg 64361], [tg 375, tg 4535, tg 60279, tg 64439]],
      [tg 239861, tg 244021, tg 299765, tg 303925]⟩,
    ⟨-7, 1, 5, 17,
      [[tg 180, tg 4340, tg 60084, tg 64244], [tg 206, tg 4366, tg 60110, tg 64270], [tg 258, tg 4418, tg 60162, tg 64322], [tg 310, tg 4470, tg 60214, tg 64374], [tg 388, tg 4548, tg 60292, tg 64452]],
      [tg 120118, tg 124278, tg 180022, tg 184182]⟩,
    ⟨-7, 1, 6, 15,
      [[tg 193, tg 4353, tg 60097, tg 64257], [tg 271, tg 4431, tg 60175, tg 64335], [tg 310, tg 4470, tg 60214, tg 64374], [tg 375, tg 4535, tg 60279, tg 64439], [tg 401, tg 4561, tg 60305, tg 64465]],
      [tg 120183, tg 124343, tg 180087, tg 184247]⟩,
    ⟨-7, 1, 7, 16,
      [[tg 206, tg 4366, tg 60110, tg 64270], [tg 284, tg 4444, tg 60188, tg 64348], [tg 297, tg 4457, tg 60201, tg 64361], [tg 388, tg 4548, tg 60292, tg 64452], [tg 414, tg 4574, tg 60318, tg 64478]],
      [tg 239913, tg 244073, tg 299817, tg 303977]⟩,
    ⟨-6, 1, 0, 11,
      [[tg 219, tg 4379, tg 60123, tg 64283], [tg 565, tg 1090, tg 5557, tg 60994], [tg 336, tg 4496, tg 60240, tg 64400], [tg 427, tg 4587, tg 60331, tg 64491]],
      [tg 240181, tg 240706, tg 245173, tg 300610]⟩,
    ⟨-6, 1, 1, 12,
      [[tg 232, tg 4392, tg 60136, tg 64296], [tg 323, tg 4483, tg 60227, tg 64387], [tg 349, tg 4509, tg 60253, tg 64413], [tg 440, tg 4600, tg 60344, tg 64504]],
      [tg 239939, tg 244099, tg 299843, tg 304003]⟩,
    ⟨-6, 1, 2, 13,
      [[tg 245, tg 4405, tg 60149, tg 64309], [tg 336, tg 4496, tg 60240, tg 64400], [tg 375, tg 4535, tg 60279, tg 64439], [tg 453, tg 4613, tg 60357, tg 64517]],
      [tg 239952, tg 244112, tg 299856, tg 304016]⟩,
    ⟨-6, 1, 3, 17,
      [[tg 258, tg 4418, tg 60162, tg 64322], [tg 388, tg 4548, tg 60292, tg 64452], [tg 3755, tg 7915, tg 63659, tg 67819], [tg 466, tg 4626, tg 60370, tg 64530]],
      [tg 240004, tg 244164, tg 299908, tg 304068]⟩,
    ⟨-6, 1, 4, 14,
      [[tg 271, tg 4431, tg 60175, tg 64335], [tg 297, tg 4457, tg 60201, tg 64361], [tg 349, tg 4509, tg 60253, tg 64413], [tg 401, tg 4561, tg 60305, tg 64465], [tg 479, tg 4639, tg 60383, tg 64543]],
      [tg 239965, tg 244125, tg 299869, tg 304029]⟩,
    ⟨-6, 1, 5, 16,
      [[tg 284, tg 4444, tg 60188, tg 64348], [tg 310, tg 4470, tg 60214, tg 64374], [tg 362, tg 4522, tg 60266, tg 64426], [tg 414, tg 4574, tg 60318, tg 64478], [tg 492, tg 4652, tg 60396, tg 64556]],
      [tg 120222, tg 124382, tg 180126, tg 184286]⟩,
    ⟨-6, 1, 6, 14,
      [[tg 297, tg 4457, tg 60201, tg 64361], [tg 375, tg 4535, tg 60279, tg 64439], [tg 414, tg 4574, tg 60318, tg 64478], [tg 479, tg 4639, tg 60383, tg 64543], [tg 505, tg 4665, tg 60409, tg 64569]],
      [tg 120287, tg 124447, tg 180191, tg 184351]⟩,
    ⟨-6, 1, 7, 15,
      [[tg 310, tg 4470, tg 60214, tg 64374], [tg 388, tg 4548, tg 60292, tg 64452], [tg 401, tg 4561, tg 60305, tg 64465], [tg 492, tg 4652, tg 60396, tg 64556], [tg 518, tg 4678, tg 60422, tg 64582]],
      [tg 240017, tg 244177, tg 299921, tg 304081]⟩,
    ⟨-5, 1, 0, 10,
      [[tg 323, tg 4483, tg 60227, tg 64387], [tg 461, tg 1194, tg 5453, tg 61098], [tg 440, tg 4600, tg 60344, tg 64504], [tg 531, tg 4691, tg 60435, tg 64595]],
      [tg 240077, tg 240810, tg 245069, tg 300714]⟩,
    ⟨-5, 1, 1, 11,
      [[tg 336, tg 4496, tg 60240, tg 64400], [tg 427, tg 4587, tg 60331, tg 64491], [tg 453, tg 4613, tg 60357, tg 64517], [tg 544, tg 4704, tg 60448, tg 64608]],
      [tg 240043, tg 244203, tg 299947, tg 304107]⟩,
    ⟨-5, 1, 2, 12,
      [[tg 349, tg 4509, tg 60253, tg 64413], [tg 440, tg 4600, tg 60344, tg 64504], [tg 479, tg 4639, tg 60383, tg 64543], [tg 557, tg 4717, tg 60461, tg 64621]],
      [tg 240056, tg 244216, tg 299960, tg 304120]⟩,
    ⟨-5, 1, 3, 16,
      [[tg 362, tg 4522, tg 60266, tg 64426], [tg 492, tg 4652, tg 60396, tg 64556], [tg 3859, tg 8019, tg 63763, tg 67923], [tg 570, tg 4730, tg 60474, tg 64634]],
      [tg 240108, tg 244268, tg 300012, tg 304172]⟩,
    ⟨-5, 1, 4, 13,
      [[tg 375, tg 4535, tg 60279, tg 64439], [tg 401, tg 4561, tg 60305, tg 64465], [tg 453, tg 4613, tg 60357, tg 64517], [tg 505, tg 4665, tg 60409, tg 64569], [tg 583, tg 4743, tg 60487, tg 64647]],
      [tg 240069, tg 244229, tg 299973, tg 304133]⟩,
    ⟨-5, 1, 5, 15,
      [[tg 388, tg 4548, tg 60292, tg 64452], [tg 414, tg 4574, tg 60318, tg 64478], [tg 466, tg 4626, tg 60370, tg 64530], [tg 518, tg 4678, tg 60422, tg 64582], [tg 596, tg 4756, tg 60500, tg 64660]],
      [tg 120326, tg 124486, tg 180230, tg 184390]⟩,
    ⟨-5, 1, 6, 13,
      [[tg 401, tg 4561, tg 60305, tg 64465], [tg 479, tg 4639, tg 60383, tg 64543], [tg 518, tg 4678, tg 60422, tg 64582], [tg 583, tg 4743, tg 60487, tg 64647], [tg 609, tg 4769, tg 60513, tg 64673]],
      [tg 120391, tg 124551, tg 180295, tg 184455]⟩,
    ⟨-5, 1, 7, 14,
      [[tg 414, tg 4574, tg 60318, tg 64478], [tg 492, tg 4652, tg 60396, tg 64556], [tg 505, tg 4665, tg 60409, tg 64569], [tg 596, tg 4756, tg 60500, tg 64660], [tg 622, tg 4782, tg 60526, tg 64686]],
      [tg 240121, tg 244281, tg 300025, tg 304185]⟩,
    ⟨-4, 1, 0, 9,
      [[tg 427, tg 4587, tg 60331, tg 64491], [tg 357, tg 1298, tg 5349, tg 61202], [tg 544, tg 4704, tg 60448, tg 64608], [tg 635, tg 4795, tg 60539, tg 64699]],
      [tg 239973, tg 240914, tg 244965, tg 300818]⟩,
    ⟨-4, 1, 1, 10,
      [[tg 440, tg 4600, tg 60344, tg 64504], [tg 531, tg 4691, tg 60435, tg 64595], [tg 557, tg 4717, tg 60461, tg 64621], [tg 648, tg 4808, tg 60552, tg 64712]],
      [tg 240147, tg 244307, tg 300051, tg 304211]⟩,
    ⟨-4, 1, 2, 11,
      [[tg 453, tg 4613, tg 60357, tg 64517], [tg 544, tg 4704, tg 60448, tg 64608], [tg 583, tg 4743, tg 60487, tg 64647], [tg 661, tg 4821, tg 60565, tg 64725]],
      [tg 240160, tg 244320, tg 300064, tg 304224]⟩,
    ⟨-4, 1, 3, 15,
      [[tg 466, tg 4626, tg 60370, tg 64530], [tg 596, tg 4756, tg 60500, tg 64660], [tg 3963, tg 8123, tg 63867, tg 68027], [tg 674, tg 4834, tg 60578, tg 64738]],
      [tg 240212, tg 244372, tg 300116, tg 304276]⟩,
    ⟨-4, 1, 4, 12,
      [[tg 479, tg 4639, tg 60383, tg 64543], [tg 505, tg 4665, tg 60409, tg 64569], [tg 557, tg 4717, tg 60461, tg 64621], [tg 609, tg 4769, tg 60513, tg 64673], [tg 687, tg 4847, tg 60591, tg 64751]],
      [tg 240173, tg 244333, tg 300077, tg 304237]⟩,
    ⟨-4, 1, 5, 14,
      [[tg 492, tg 4652, tg 60396, tg 64556], [tg 518, tg 4678, tg 60422, tg 64582], [tg 570, tg 4730, tg 60474, tg 64634], [tg 622, tg 4782, tg 60526, tg 64686], [tg 700, tg 4860, tg 60604, tg 64764]],
      [tg 120430, tg 124590, tg 180334, tg 184494]⟩,
    ⟨-4, 1, 6, 12,
      [[tg 505, tg 4665, tg 60409, tg 64569], [tg 583, tg 4743, tg 60487, tg 64647], [tg 622, tg 4782, tg 60526, tg 64686], [tg 687, tg 4847, tg 60591, tg 64751], [tg 713, tg 4873, tg 60617, tg 64777]],
      [tg 120495, tg 124655, tg 180399, tg 184559]⟩,
    ⟨-4, 1, 7, 13,
      [[tg 518, tg 4678, tg 60422, tg 64582], [tg 596, tg 4756, tg 60500, tg 64660], [tg 609, tg 4769, tg 60513, tg 64673], [tg 700, tg 4860, tg 60604, tg 64764], [tg 726, tg 4886, tg 60630, tg 64790]],
      [tg 240225, tg 244385, tg 300129, tg 304289]⟩,
    ⟨-3, 1, 0, 8,
      [[tg 531, tg 4691, tg 60435, tg 64595], [tg 253, tg 1402, tg 5245, tg 61306], [tg 648, tg 4808, tg 60552, tg 64712], [tg 739, tg 4899, tg 60643, tg 64803]],
      [tg 239869, tg 241018, tg 244861, tg 300922]⟩,
    ⟨-3, 1, 1, 9,
      [[tg 544, tg 4704, tg 60448, tg 64608], [tg 635, tg 4795, tg 60539, tg 64699], [tg 661, tg 4821, tg 60565, tg 64725], [tg 752, tg 4912, tg 60656, tg 64816]],
      [tg 240251, tg 244411, tg 300155, tg 304315]⟩,
    ⟨-3, 1, 2, 10,
      [[tg 557, tg 4717, tg 60461, tg 64621], [tg 648, tg 4808, tg 60552, tg 64712], [tg 687, tg 4847, tg 60591, tg 64751], [tg 765, tg 4925, tg 60669, tg 64829]],
      [tg 240264, tg 244424, tg 300168, tg 304328]⟩,
    ⟨-3, 1, 3, 14,
      [[tg 570, tg 4730, tg 60474, tg 64634], [tg 700, tg 4860, tg 60604, tg 64764], [tg 4067, tg 8227, tg 63971, tg 68131], [tg 778, tg 4938, tg 60682, tg 64842]],
      [tg 240316, tg 244476, tg 300220, tg 304380]⟩,
    ⟨-3, 1, 4, 11,
      [[tg 583, tg 4743, tg 60487, tg 64647], [tg 609, tg 4769, tg 60513, tg 64673], [tg 661, tg 4821, tg 60565, tg 64725], [tg 713, tg 4873, tg 60617, tg 64777], [tg 791, tg 4951, tg 60695, tg 64855]],
      [tg 240277, tg 244437, tg 300181, tg 304341]⟩,
    ⟨-3, 1, 5, 13,
      [[tg 596, tg 4756, tg 60500, tg 64660], [tg 622, tg 4782, tg 60526, tg 64686], [tg 674, tg 4834, tg 60578, tg 64738], [tg 726, tg 4886, tg 60630, tg 64790], [tg 804, tg 4964, tg 60708, tg 64868]],
      [tg 120534, tg 124694, tg 180438, tg 184598]⟩,
    ⟨-3, 1, 6, 11,
      [[tg 609, tg 4769, tg 60513, tg 64673], [tg 687, tg 4847, tg 60591, tg 64751], [tg 726, tg 4886, tg 60630, tg 64790], [tg 791, tg 4951, tg 60695, tg 64855], [tg 817, tg 4977, tg 60721, tg 64881]],
      [tg 120599, tg 124759, tg 180503, tg 184663]⟩,
    ⟨-3, 1, 7, 12,
      [[tg 622, tg 4782, tg 60526, tg 64686], [tg 700, tg 4860, tg 60604, tg 64764], [tg 713, tg 4873, tg 60617, tg 64777], [tg 804, tg 4964, tg 60708, tg 64868], [tg 830, tg 4990, tg 60734, tg 64894]],
      [tg 240329, tg 244489, tg 300233, tg 304393]⟩,
    ⟨-2, 1, 0, 7,
      [[tg 635, tg 4795, tg 60539, tg 64699], [tg 149, tg 1506, tg 5141, tg 61410], [tg 752, tg 4912, tg 60656, tg 64816], [tg 5, tg 4165, tg 19979, tg 24139]],
      [tg 239765, tg 241122, tg 244757, tg 301026]⟩,
    ⟨-2, 1, 1, 8,
      [[tg 648, tg 4808, tg 60552, tg 64712], [tg 739, tg 4899, tg 60643, tg 64803], [tg 765, tg 4925, tg 60669, tg 64829], [tg 18, tg 4178, tg 19992, tg 24152]],
      [tg 240355, tg 244515, tg 300259, tg 304419]⟩,
    ⟨-2, 1, 2, 9,
      [[tg 661, tg 4821, tg 60565, tg 64725], [tg 752, tg 4912, tg 60656, tg 64816], [tg 791, tg 4951, tg 60695, tg 64855], [tg 31, tg 4191, tg 20005, tg 24165]],
      [tg 240368, tg 244528, tg 300272, tg 304432]⟩,
    ⟨-2, 1, 3, 13,
      [[tg 674, tg 4834, tg 60578, tg 64738], [tg 804, tg 4964, tg 60708, tg 64868], [tg 3333, tg 7493, tg 23307, tg 27467], [tg 44, tg 4204, tg 20018, tg 24178]],
      [tg 240420, tg 244580, tg 300324, tg 304484]⟩,
    ⟨-2, 1, 4, 10,
      [[tg 687, tg 4847, tg 60591, tg 64751], [tg 713, tg 4873, tg 60617, tg 64777], [tg 765, tg 4925, tg 60669, tg 64829], [tg 817, tg 4977, tg 60721, tg 64881], [tg 57, tg 4217, tg 20031, tg 24191]],
      [tg 240381, tg 244541, tg 300285, tg 304445]⟩,
    ⟨-2, 1, 5, 12,
      [[tg 700, tg 4860, tg 60604, tg 64764], [tg 726, tg 4886, tg 60630, tg 64790], [tg 778, tg 4938, tg 60682, tg 64842], [tg 830, tg 4990, tg 60734, tg 64894], [tg 70, tg 4230, tg 20044, tg 24204]],
      [tg 120638, tg 124798, tg 180542, tg 184702]⟩,
    ⟨-2, 1, 6, 10,
      [[tg 713, tg 4873, tg 60617, tg 64777], [tg 791, tg 4951, tg 60695, tg 64855], [tg 830, tg 4990, tg 60734, tg 64894], [tg 57, tg 4217, tg 20031, tg 24191], [tg 83, tg 4243, tg 20057, tg 24217]],
      [tg 119865, tg 124025, tg 139839, tg 143999]⟩,
    ⟨-2, 1, 7, 11,
      [[tg 726, tg 4886, tg 60630, tg 64790], [tg 804, tg 4964, tg 60708, tg 64868], [tg 817, tg 4977, tg 60721, tg 64881], [tg 70, tg 4230, tg 20044, tg 24204], [tg 96, tg 4256, tg 20070, tg 24230]],
      [tg 240433, tg 244593, tg 300337, tg 304497]⟩]⟩,
  ⟨2, -8, 0, -1, -1, [(-1, 1, 1), (0, -8, 1)], -1, 1, 1, 8, 0, -8, 1, 8,
   [⟨-9, -1, 0, 18,
      [[tg 4068, tg 8228, tg 63972, tg 68132], [tg 40091, tg 44251, tg 99995, tg 104155], [tg 25, tg 4185, tg 59929, tg 64089], [tg 116, tg 4276, tg 60020, tg 64180]],
      [tg 119833, tg 123993, tg 179737, tg 183897]⟩,
    ⟨-9, -1, 1, 17,
      [[tg 4081, tg 8241, tg 63985, tg 68145], [tg 12, tg 4172, tg 59916, tg 64076], [tg 38, tg 4198, tg 59942, tg 64102], [tg 129, tg 4289, tg 60033, tg 64193]],
      [tg 119846, tg 124006, tg 179750, tg 183910]⟩,
    ⟨-9, -1, 2, 16,
      [[tg 4094, tg 8254, tg 63998, tg 68158], [tg 25, tg 4185, tg 59929, tg 64089], [tg 64, tg 4224, tg 59968, tg 64128], [tg 142, tg 4302, tg 60046, tg 64206]],
      [tg 239680, tg 243840, tg 299584, tg 303744]⟩,
    ⟨-9, -1, 3, 12,
      [[tg 4107, tg 8267, tg 64011, tg 68171], [tg 77, tg 4237, tg 59981, tg 64141], [tg 3334, tg 7494, tg 24036, tg 28196], [tg 155, tg 4315, tg 60059, tg 64219]],
      [tg 123142, tg 127302, tg 143844, tg 148004]⟩,
    ⟨-9, -1, 4, 15,
      [[tg 4120, tg 8280, tg 64024, tg 68184], [tg 4146, tg 8306, tg 64050, tg 68210], [tg 38, tg 4198, tg 59942, tg 64102], [tg 90, tg 4250, tg 59994, tg 64154], [tg 168, tg 4328, tg 60072, tg 64232]],
      [tg 119898, tg 124058, tg 179802, tg 183962]⟩,
    ⟨-9, -1, 5, 13,
      [[tg 4133, tg 8293, tg 64037, tg 68197], [tg 4159, tg 8319, tg 64063, tg 68223], [tg 51, tg 4211, tg 59955, tg 64115], [tg 103, tg 4263, tg 60007, tg 64167], [tg 181, tg 4341, tg 60085, tg 64245]],
      [tg 119859, tg 124019, tg 179763, tg 183923]⟩,
    ⟨-9, -1, 6, 14,
      [[tg 4146, tg 8306, tg 64050, tg 68210], [tg 64, tg 4224, tg 59968, tg 64128], [tg 103, tg 4263, tg 60007, tg 64167], [tg 168, tg 4328, tg 60072, tg 64232], [tg 194, tg 4354, tg 60098, tg 64258]],
      [tg 239719, tg 243879, tg 299623, tg 303783]⟩,
    ⟨-9, -1, 7, 13,
      [[tg 4159, tg 8319, tg 64063, tg 68223], [tg 77, tg 4237, tg 59981, tg 64141], [tg 90, tg 4250, tg 59994, tg 64154], [tg 181, tg 4341, tg 60085, tg 64245], [tg 207, tg 4367, tg 60111, tg 64271]],
      [tg 119989, tg 124149, tg 179893, tg 184053]⟩,
    ⟨-8, -1, 0, 17,
      [[tg 12, tg 4172, tg 59916, tg 64076], [tg 40195, tg 44355, tg 100099, tg 104259], [tg 129, tg 4289, tg 60033, tg 64193], [tg 220, tg 4380, tg 60124, tg 64284]],
      [tg 119937, tg 124097, tg 179841, tg 184001]⟩,
    ⟨-8, -1, 1, 16,
      [[tg 25, tg 4185, tg 59929, tg 64089], [tg 116, tg 4276, tg 60020, tg 64180], [tg 142, tg 4302, tg 60046, tg 64206], [tg 233, tg 4393, tg 60137, tg 64297]],
      [tg 119950, tg 124110, tg 179854, tg 184014]⟩,
    ⟨-8, -1, 2, 15,
      [[tg 38, tg 4198, tg 59942, tg 64102], [tg 129, tg 4289, tg 60033, tg 64193], [tg 168, tg 4328, tg 60072, tg 64232], [tg 246, tg 4406, tg 60150, tg 64310]],
      [tg 239784, tg 243944, tg 299688, tg 303848]⟩,
    ⟨-8, -1, 3, 11,
      [[tg 51, tg 4211, tg 59955, tg 64115], [tg 181, tg 4341, tg 60085, tg 64245], [tg 734, tg 4894, tg 19980, tg 24140], [tg 259, tg 4419, tg 60163, tg 64323]],
      [tg 120542, tg 124702, tg 139788, tg 143948]⟩,
    ⟨-8, -1, 4, 14,
      [[tg 64, tg 4224, tg 59968, tg 64128], [tg 90, tg 4250, tg 59994, tg 64154], [tg 142, tg 4302, tg 60046, tg 64206], [tg 194, tg 4354, tg 60098, tg 64258], [tg 272, tg 4432, tg 60176, tg 64336]],
      [tg 120002, tg 124162, tg 179906, tg 184066]⟩,
    ⟨-8, -1, 5, 12,
      [[tg 77, tg 4237, tg 59981, tg 64141], [tg 103, tg 4263, tg 60007, tg 64167], [tg 155, tg 4315, tg 60059, tg 64219], [tg 207, tg 4367, tg 60111, tg 64271], [tg 285, tg 4445, tg 60189, tg 64349]],
      [tg 119963, tg 124123, tg 179867, tg 184027]⟩,
    ⟨-8, -1, 6, 13,
      [[tg 90, tg 4250, tg 59994, tg 64154], [tg 168, tg 4328, tg 60072, tg 64232], [tg 207, tg 4367, tg 60111, tg 64271], [tg 272, tg 4432, tg 60176, tg 64336], [tg 298, tg 4458, tg 60202, tg 64362]],
      [tg 239823, tg 243983, tg 299727, tg 303887]⟩,
    ⟨-8, -1, 7, 12,
      [[tg 103, tg 4263, tg 60007, tg 64167], [tg 181, tg 4341, tg 60085, tg 64245], [tg 194, tg 4354, tg 60098, tg 64258], [tg 285, tg 4445, tg 60189, tg 64349], [tg 311, tg 4471, tg 60215, tg 64375]],
      [tg 120093, tg 124253, tg 179997, tg 184157]⟩,
    ⟨-7, -1, 0, 16,
      [[tg 116, tg 4276, tg 60020, tg 64180], [tg 40299, tg 44459, tg 100203, tg 104363], [tg 233, tg 4393, tg 60137, tg 64297], [tg 324, tg 4484, tg 60228, tg 64388]],
      [tg 120041, tg 124201, tg 179945, tg 184105]⟩,
    ⟨-7, -1, 1, 15,
      [[tg 129, tg 4289, tg 60033, tg 64193], [tg 220, tg 4380, tg 60124, tg 64284], [tg 246, tg 4406, tg 60150, tg 64310], [tg 337, tg 4497, tg 60241, tg 64401]],
      [tg 120054, tg 124214, tg 179958, tg 184118]⟩,
    ⟨-7, -1, 2, 14,
      [[tg 142, tg 4302, tg 60046, tg 64206], [tg 233, tg 4393, tg 60137, tg 64297], [tg 272, tg 4432, tg 60176, tg 64336], [tg 350, tg 4510, tg 60254, tg 64414]],
      [tg 239888, tg 244048, tg 299792, tg 303952]⟩,
    ⟨-7, -1, 3, 10,
      [[tg 155, tg 4315, tg 60059, tg 64219], [tg 285, tg 4445, tg 60189, tg 64349], [tg 630, tg 4790, tg 20084, tg 24244], [tg 363, tg 4523, tg 60267, tg 64427]],
      [tg 120438, tg 124598, tg 139892, tg 144052]⟩,
    ⟨-7, -1, 4, 13,
      [[tg 168, tg 4328, tg 60072, tg 64232], [tg 194, tg 4354, tg 60098, tg 64258], [tg 246, tg 4406, tg 60150, tg 64310], [tg 298, tg 4458, tg 60202, tg 64362], [tg 376, tg 4536, tg 60280, tg 64440]],
      [tg 120106, tg 124266, tg 180010, tg 184170]⟩,
    ⟨-7, -1, 5, 11,
      [[tg 181, tg 4341, tg 60085, tg 64245], [tg 207, tg 4367, tg 60111, tg 64271], [tg 259, tg 4419, tg 60163, tg 64323], [tg 311, tg 4471, tg 60215, tg 64375], [tg 389, tg 4549, tg 60293, tg 64453]],
      [tg 120067, tg 124227, tg 179971, tg 184131]⟩,
    ⟨-7, -1, 6, 12,
      [[tg 194, tg 4354, tg 60098, tg 64258], [tg 272, tg 4432, tg 60176, tg 64336], [tg 311, tg 4471, tg 60215, tg 64375], [tg 376, tg 4536, tg 60280, tg 64440], [tg 402, tg 4562, tg 60306, tg 64466]],
      [tg 239927, tg 244087, tg 299831, tg 303991]⟩,
    ⟨-7, -1, 7, 11,
      [[tg 207, tg 4367, tg 60111, tg 64271], [tg 285, tg 4445, tg 60189, tg 64349], [tg 298, tg 4458, tg 60202, tg 64362], [tg 389, tg 4549, tg 60293, tg 64453], [tg 415, tg 4575, tg 60319, tg 64479]],
      [tg 120197, tg 124357, tg 180101, tg 184261]⟩,
    ⟨-6, -1, 0, 15,
      [[tg 220, tg 4380, tg 60124, tg 64284], [tg 40403, tg 44563, tg 100307, tg 104467], [tg 337, tg 4497, tg 60241, tg 64401], [tg 428, tg 4588, tg 60332, tg 64492]],
      [tg 120145, tg 124305, tg 180049, tg 184209]⟩,
    ⟨-6, -1, 1, 14,
      [[tg 233, tg 4393, tg 60137, tg 64297], [tg 324, tg 4484, tg 60228, tg 64388], [tg 350, tg 4510, tg 60254, tg 64414], [tg 441, tg 4601, tg 60345, tg 64505]],
      [tg 120158, tg 124318, tg 180062, tg 184222]⟩,
    ⟨-6, -1, 2, 13,
      [[tg 246, tg 4406, tg 60150, tg 64310], [tg 337, tg 4497, tg 60241, tg 64401], [tg 376, tg 4536, tg 60280, tg 64440], [tg 454, tg 4614, tg 60358, tg 64518]],
      [tg 239992, tg 244152, tg 299896, tg 304056]⟩,
    ⟨-6, -1, 3, 9,
      [[tg 259, tg 4419, tg 60163, tg 64323], [tg 389, tg 4549, tg 60293, tg 64453], [tg 526, tg 4686, tg 20188, tg 24348], [tg 467, tg 4627, tg 60371, tg 64531]],
      [tg 120334, tg 124494, tg 139996, tg 144156]⟩,
    ⟨-6, -1, 4, 12,
      [[tg 272, tg 4432, tg 60176, tg 64336], [tg 298, tg 4458, tg 60202, tg 64362], [tg 350, tg 4510, tg 60254, tg 64414], [tg 402, tg 4562, tg 60306, tg 64466], [tg 480, tg 4640, tg 60384, tg 64544]],
      [tg 120210, tg 124370, tg 180114, tg 184274]⟩,
    ⟨-6, -1, 5, 10,
      [[tg 285, tg 4445, tg 60189, tg 64349], [tg 311, tg 4471, tg 60215, tg 64375], [tg 363, tg 4523, tg 60267, tg 64427], [tg 415, tg 4575, tg 60319, tg 64479], [tg 493, tg 4653, tg 60397, tg 64557]],
      [tg 120171, tg 124331, tg 180075, tg 184235]⟩,
    ⟨-6, -1, 6, 11,
      [[tg 298, tg 4458, tg 60202, tg 64362], [tg 376, tg 4536, tg 60280, tg 64440], [tg 415, tg 4575, tg 60319, tg 64479], [tg 480, tg 4640, tg 60384, tg 64544], [tg 506, tg 4666, tg 60410, tg 64570]],
      [tg 240031, tg 244191, tg 299935, tg 304095]⟩,
    ⟨-6, -1, 7, 10,
      [[tg 311, tg 4471, tg 60215, tg 64375], [tg 389, tg 4549, tg 60293, tg 64453], [tg 402, tg 4562, tg 60306, tg 64466], [tg 493, tg 4653, tg 60397, tg 64557], [tg 519, tg 4679, tg 60423, tg 64583]],
      [tg 120301, tg 124461, tg 180205, tg 184365]⟩,
    ⟨-5, -1, 0, 14,
      [[tg 324, tg 4484, tg 60228, tg 64388], [tg 40507, tg 44667, tg 100411, tg 104571], [tg 441, tg 4601, tg 60345, tg 64505], [tg 532, tg 4692, tg 60436, tg 64596]],
      [tg 120249, tg 124409, tg 180153, tg 184313]⟩,
    ⟨-5, -1, 1, 13,
      [[tg 337, tg 4497, tg 60241, tg 64401], [tg 428, tg 4588, tg 60332, tg 64492], [tg 454, tg 4614, tg 60358, tg 64518], [tg 545, tg 4705, tg 60449, tg 64609]],
      [tg 120262, tg 124422, tg 180166, tg 184326]⟩,
    ⟨-5, -1, 2, 12,
      [[tg 350, tg 4510, tg 60254, tg 64414], [tg 441, tg 4601, tg 60345, tg 64505], [tg 480, tg 4640, tg 60384, tg 64544], [tg 558, tg 4718, tg 60462, tg 64622]],
      [tg 240096, tg 244256, tg 300000, tg 304160]⟩,
    ⟨-5, -1, 3, 8,
      [[tg 363, tg 4523, tg 60267, tg 64427], [tg 493, tg 4653, tg 60397, tg 64557], [tg 422, tg 4582, tg 20292, tg 24452], [tg 571, tg 4731, tg 60475, tg 64635]],
      [tg 120230, tg 124390, tg 140100, tg 144260]⟩,
    ⟨-5, -1, 4, 11,
      [[tg 376, tg 4536, tg 60280, tg 64440], [tg 402, tg 4562, tg 60306, tg 64466], [tg 454, tg 4614, tg 60358, tg 64518], [tg 506, tg 4666, tg 60410, tg 64570], [tg 584, tg 4744, tg 60488, tg 64648]],
      [tg 120314, tg 124474, tg 180218, tg 184378]⟩,
    ⟨-5, -1, 5, 9,
      [[tg 389, tg 4549, tg 60293, tg 64453], [tg 415, tg 4575, tg 60319, tg 64479], [tg 467, tg 4627, tg 60371, tg 64531], [tg 519, tg 4679, tg 60423, tg 64583], [tg 597, tg 4757, tg 60501, tg 64661]],
      [tg 120275, tg 124435, tg 180179, tg 184339]⟩,
    ⟨-5, -1, 6, 10,
      [[tg 402, tg 4562, tg 60306, tg 64466], [tg 480, tg 4640, tg 60384, tg 64544], [tg 519, tg 4679, tg 60423, tg 64583], [tg 584, tg 4744, tg 60488, tg 64648], [tg 610, tg 4770, tg 60514, tg 64674]],
      [tg 240135, tg 244295, tg 300039, tg 304199]⟩,
    ⟨-5, -1, 7, 9,
      [[tg 415, tg 4575, tg 60319, tg 64479], [tg 493, tg 4653, tg 60397, tg 64557], [tg 506, tg 4666, tg 60410, tg 64570], [tg 597, tg 4757, tg 60501, tg 64661], [tg 623, tg 4783, tg 60527, tg 64687]],
      [tg 120405, tg 124565, tg 180309, tg 184469]⟩,
    ⟨-4, -1, 0, 13,
      [[tg 428, tg 4588, tg 60332, tg 64492], [tg 40611, tg 44771, tg 100515, tg 104675], [tg 545, tg 4705, tg 60449, tg 64609], [tg 636, tg 4796, tg 60540, tg 64700]],
      [tg 120353, tg 124513, tg 180257, tg 184417]⟩,
    ⟨-4, -1, 1, 12,
      [[tg 441, tg 4601, tg 60345, tg 64505], [tg 532, tg 4692, tg 60436, tg 64596], [tg 558, tg 4718, tg 60462, tg 64622], [tg 649, tg 4809, tg 60553, tg 64713]],
      [tg 120366, tg 124526, tg 180270, tg 184430]⟩,
    ⟨-4, -1, 2, 11,
      [[tg 454, tg 4614, tg 60358, tg 64518], [tg 545, tg 4705, tg 60449, tg 64609], [tg 584, tg 4744, tg 60488, tg 64648], [tg 662, tg 4822, tg 60566, tg 64726]],
      [tg 240200, tg 244360, tg 300104, tg 304264]⟩,
    ⟨-4, -1, 3, 7,
      [[tg 467, tg 4627, tg 60371, tg 64531], [tg 597, tg 4757, tg 60501, tg 64661], [tg 318, tg 4478, tg 20396, tg 24556], [tg 675, tg 4835, tg 60579, tg 64739]],
      [tg 120126, tg 124286, tg 140204, tg 144364]⟩,
    ⟨-4, -1, 4, 10,
      [[tg 480, tg 4640, tg 60384, tg 64544], [tg 506, tg 4666, tg 60410, tg 64570], [tg 558, tg 4718, tg 60462, tg 64622], [tg 610, tg 4770, tg 60514, tg 64674], [tg 688, tg 4848, tg 60592, tg 64752]],
      [tg 120418, tg 124578, tg 180322, tg 184482]⟩,
    ⟨-4, -1, 5, 8,
      [[tg 493, tg 4653, tg 60397, tg 64557], [tg 519, tg 4679, tg 60423, tg 64583], [tg 571, tg 4731, tg 60475, tg 64635], [tg 623, tg 4783, tg 60527, tg 64687], [tg 701, tg 4861, tg 60605, tg 64765]],
      [tg 120379, tg 124539, tg 180283, tg 184443]⟩,
    ⟨-4, -1, 6, 9,
      [[tg 506, tg 4666, tg 60410, tg 64570], [tg 584, tg 4744, tg 60488, tg 64648], [tg 623, tg 4783, tg 60527, tg 64687], [tg 688, tg 4848, tg 60592, tg 64752], [tg 714, tg 4874, tg 60618, tg 64778]],
      [tg 240239, tg 244399, tg 300143, tg 304303]⟩,
    ⟨-4, -1, 7, 8,
      [[tg 519, tg 4679, tg 60423, tg 64583], [tg 597, tg 4757, tg 60501, tg 64661], [tg 610, tg 4770, tg 60514, tg 64674], [tg 701, tg 4861, tg 60605, tg 64765], [tg 727, tg 4887, tg 60631, tg 64791]],
      [tg 120509, tg 124669, tg 180413, tg 184573]⟩,
    ⟨-3, -1, 0, 12,
      [[tg 532, tg 4692, tg 60436, tg 64596], [tg 40715, tg 44875, tg 100619, tg 104779], [tg 649, tg 4809, tg 60553, tg 64713], [tg 740, tg 4900, tg 60644, tg 64804]],
      [tg 120457, tg 124617, tg 180361, tg 184521]⟩,
    ⟨-3, -1, 1, 11,
      [[tg 545, tg 4705, tg 60449, tg 64609], [tg 636, tg 4796, tg 60540, tg 64700], [tg 662, tg 4822, tg 60566, tg 64726], [tg 753, tg 4913, tg 60657, tg 64817]],
      [tg 120470, tg 124630, tg 180374, tg 184534]⟩,
    ⟨-3, -1, 2, 10,
      [[tg 558, tg 4718, tg 60462, tg 64622], [tg 649, tg 4809, tg 60553, tg 64713], [tg 688, tg 4848, tg 60592, tg 64752], [tg 766, tg 4926, tg 60670, tg 64830]],
      [tg 240304, tg 244464, tg 300208, tg 304368]⟩,
    ⟨-3, -1, 3, 6,
      [[tg 571, tg 4731, tg 60475, tg 64635], [tg 701, tg 4861, tg 60605, tg 64765], [tg 214, tg 4374, tg 20500, tg 24660], [tg 779, tg 4939, tg 60683, tg 64843]],
      [tg 120022, tg 124182, tg 140308, tg 144468]⟩,
    ⟨-3, -1, 4, 9,
      [[tg 584, tg 4744, tg 60488, tg 64648], [tg 610, tg 4770, tg 60514, tg 64674], [tg 662, tg 4822, tg 60566, tg 64726], [tg 714, tg 4874, tg 60618, tg 64778], [tg 792, tg 4952, tg 60696, tg 64856]],
      [tg 120522, tg 124682, tg 180426, tg 184586]⟩,
    ⟨-3, -1, 5, 7,
      [[tg 597, tg 4757, tg 60501, tg 64661], [tg 623, tg 4783, tg 60527, tg 64687], [tg 675, tg 4835, tg 60579, tg 64739], [tg 727, tg 4887, tg 60631, tg 64791], [tg 805, tg 4965, tg 60709, tg 64869]],
      [tg 120483, tg 124643, tg 180387, tg 184547]⟩,
    ⟨-3, -1, 6, 8,
      [[tg 610, tg 4770, tg 60514, tg 64674], [tg 688, tg 4848, tg 60592, tg 64752], [tg 727, tg 4887, tg 60631, tg 64791], [tg 792, tg 4952, tg 60696, tg 64856], [tg 818, tg 4978, tg 60722, tg 64882]],
      [tg 240343, tg 244503, tg 300247, tg 304407]⟩,
    ⟨-3, -1, 7, 7,
      [[tg 623, tg 4783, tg 60527, tg 64687], [tg 701, tg 4861, tg 60605, tg 64765], [tg 714, tg 4874, tg 60618, tg 64778], [tg 805, tg 4965, tg 60709, tg 64869], [tg 831, tg 4991, tg 60735, tg 64895]],
      [tg 120613, tg 124773, tg 180517, tg 184677]⟩,
    ⟨-2, -1, 0, 11,
      [[tg 636, tg 4796, tg 60540, tg 64700], [tg 3368, tg 40819, tg 8360, tg 100723], [tg 753, tg 4913, tg 60657, tg 64817], [tg 1, tg 844, tg 4993, tg 60748]],
      [tg 120561, tg 124721, tg 180465, tg 184625]⟩,
    ⟨-2, -1, 1, 10,
      [[tg 649, tg 4809, tg 60553, tg 64713], [tg 740, tg 4900, tg 60644, tg 64804], [tg 766, tg 4926, tg 60670, tg 64830], [tg 14, tg 857, tg 5006, tg 60761]],
      [tg 120574, tg 124734, tg 180478, tg 184638]⟩,
    ⟨-2, -1, 2, 9,
      [[tg 662, tg 4822, tg 60566, tg 64726], [tg 753, tg 4913, tg 60657, tg 64817], [tg 792, tg 4952, tg 60696, tg 64856], [tg 27, tg 870, tg 5019, tg 60774]],
      [tg 240408, tg 244568, tg 300312, tg 304472]⟩,
    ⟨-2, -1, 3, 5,
      [[tg 675, tg 4835, tg 60579, tg 64739], [tg 805, tg 4965, tg 60709, tg 64869], [tg 110, tg 4270, tg 20604, tg 24764], [tg 40, tg 883, tg 5032, tg 60787]],
      [tg 119918, tg 124078, tg 140412, tg 144572]⟩,
    ⟨-2, -1, 4, 8,
      [[tg 688, tg 4848, tg 60592, tg 64752], [tg 714, tg 4874, tg 60618, tg 64778], [tg 766, tg 4926, tg 60670, tg 64830], [tg 818, tg 4978, tg 60722, tg 64882], [tg 53, tg 896, tg 5045, tg 60800]],
      [tg 120626, tg 124786, tg 180530, tg 184690]⟩,
    ⟨-2, -1, 5, 6,
      [[tg 701, tg 4861, tg 60605, tg 64765], [tg 727, tg 4887, tg 60631, tg 64791], [tg 779, tg 4939, tg 60683, tg 64843], [tg 831, tg 4991, tg 60735, tg 64895], [tg 66, tg 909, tg 5058, tg 60813]],
      [tg 120587, tg 124747, tg 180491, tg 184651]⟩,
    ⟨-2, -1, 6, 7,
      [[tg 714, tg 4874, tg 60618, tg 64778], [tg 792, tg 4952, tg 60696, tg 64856], [tg 831, tg 4991, tg 60735, tg 64895], [tg 53, tg 896, tg 5045, tg 60800], [tg 79, tg 922, tg 5071, tg 60826]],
      [tg 240447, tg 244607, tg 300351, tg 304511]⟩,
    ⟨-2, -1, 7, 6,
      [[tg 727, tg 4887, tg 60631, tg 64791], [tg 805, tg 4965, tg 60709, tg 64869], [tg 818, tg 4978, tg 60722, tg 64882], [tg 66, tg 909, tg 5058, tg 60813], [tg 92, tg 935, tg 5084, tg 60839]],
      [tg 119874, tg 120717, tg 124866, tg 180621]⟩]⟩]

/-- A packed certificate entry: side bit, test index, coefficient. -/
def cc (n : ℕ) : Bool × ℕ × ℕ := (n % 2 == 1, n / 2 % 8, n / 16)

set_option maxRecDepth 100000 in
def certsData : List (List (List (Bool × ℕ × ℕ))) := [
  [[],[cc 16,cc 20,cc 21],[cc 18,cc 20,cc 21],[cc 18,cc 21],[cc 18,cc 22,cc 21],[cc 16,cc 22,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 17],[cc 132,cc 17],[cc 134,cc 19],[cc 16,cc 22,cc 19],[cc 134,cc 17],[cc 132,cc 19]],
  [[cc 16,cc 20,cc 37],[],[cc 18,cc 21],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 35],[cc 18,cc 19],[cc 20,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 64,cc 68,cc 17],[cc 16,cc 17]],
  [[cc 16,cc 20,cc 35],[cc 16,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 17],[cc 18,cc 19],[cc 66,cc 68,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 20,cc 17]],
  [[cc 20,cc 19],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 19],[],[cc 18,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 17],[cc 128,cc 17],[cc 130,cc 19],[cc 18,cc 20,cc 19],[cc 130,cc 17],[cc 128,cc 19]],
  [[cc 16,cc 20,cc 39],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 35],[],[cc 18,cc 21],[cc 16,cc 20,cc 33],[cc 16,cc 19],[cc 64,cc 68,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 20,cc 19],[cc 18,cc 17]],
  [[cc 16,cc 20,cc 33],[cc 18,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 17],[cc 16,cc 19],[cc 20,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 66,cc 68,cc 19]],
  [[cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 19],[],[cc 18,cc 20,cc 19],[cc 130,cc 17],[cc 128,cc 19],[cc 16,cc 20,cc 17],[cc 128,cc 17],[cc 130,cc 19]],
  [[cc 16,cc 18,cc 37],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 33],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 18,cc 35],[],[cc 16,cc 19],[cc 64,cc 66,cc 19],[cc 16,cc 17],[cc 64,cc 66,cc 17],[cc 18,cc 17]],
  [[cc 16,cc 133],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 129],[cc 16,cc 66,cc 65],[cc 18,cc 17],[cc 16,cc 131],[cc 18,cc 17],[],[cc 16,cc 19],[cc 16,cc 66,cc 67],[cc 16,cc 17],[cc 16,cc 66,cc 65]],
  [[cc 18,cc 135],[cc 16,cc 19],[cc 64,cc 18,cc 67],[cc 18,cc 131],[cc 16,cc 17],[cc 16,cc 21],[cc 18,cc 129],[cc 64,cc 18,cc 65],[cc 18,cc 17],[],[cc 16,cc 19],[cc 64,cc 18,cc 67],[cc 16,cc 17]],
  [[cc 16,cc 18,cc 39],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 18,cc 35],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 33],[cc 16,cc 17],[cc 64,cc 66,cc 17],[cc 18,cc 17],[],[cc 16,cc 19],[cc 64,cc 66,cc 19]],
  [[cc 16,cc 135],[cc 16,cc 66,cc 65],[cc 18,cc 17],[cc 16,cc 131],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 129],[cc 16,cc 66,cc 67],[cc 16,cc 17],[cc 16,cc 66,cc 65],[cc 18,cc 17],[],[cc 16,cc 19]],
  [[cc 18,cc 133],[cc 16,cc 17],[cc 16,cc 21],[cc 18,cc 129],[cc 16,cc 19],[cc 64,cc 18,cc 67],[cc 18,cc 131],[cc 16,cc 19],[cc 64,cc 18,cc 67],[cc 16,cc 17],[cc 64,cc 18,cc 65],[cc 18,cc 17],[]]]

def cfg : GalCert.Cfg 8 := ⟨adj, (0, 0, 2), 8, regsData, certsData, 0, 2⟩

theorem hc : cfg.check = true := by decide +kernel

theorem hV : cfg.vbound 21 = true := by decide +kernel

theorem hball : ∀ n, ball n = GalCert.ball cfg.adj cfg.x0 n
  | 0 => rfl
  | n + 1 => by rw [ball, GalCert.ball, hball n]; rfl

theorem ha (n : ℕ) (hn : 1 ≤ n) : a n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, hball, hball]
  exact GalCert.Cfg.card_step hc k

theorem hrec : ∀ k, (([(1, 7), (-2, 6), (1, 5), (1, 3), (-2, 2), (1, 1)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide) (by decide +kernel)

theorem hgfw : ∀ n < 21 + 2 * cfg.L, ((GalCert.csOfS [1, -2, 1, 0, 1, -2, 1] 0).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 := by
  decide +kernel

theorem hsmall : ∀ n < 7, GalCert.conv a [1, -2, 1, 0, 1, -2, 1] n = ([1, 2, 2, -1, 2, 2, 1] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [if_neg (by omega)]; exact ha n h
  rw [e]
  decide +kernel

end P312943

open PowerSeries OMA.S_oeis_a312943 in
theorem OMA.solution : type_of% @OMA.S_oeis_a312943.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    have h := P312943.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 7 - 1 = k + 6 by omega,
      show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 4 = k + 3 by omega,
      show k + 7 - 5 = k + 2 by omega,
      show k + 7 - 6 = k + 1 by omega,
      P312943.ha (k + 7) (by omega),
      P312943.ha (k + 6) (by omega),
      P312943.ha (k + 5) (by omega),
      P312943.ha (k + 3) (by omega),
      P312943.ha (k + 2) (by omega),
      P312943.ha (k + 1) (by omega)]
    linarith
  · have hD : ((X - 1)^2*(X^4 + 1) : PowerSeries ℤ) = GalCert.polyOf [1, -2, 1, 0, 1, -2, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : (X^6 + 2*X^5 + 2*X^4 - X^3 + 2*X^2 + 2*X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 2, 2, -1, 2, 2, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from2 P312943.hc P312943.hV a P312943.ha _ _ 0 7 (by decide) (by decide) P312943.hgfw P312943.hsmall
