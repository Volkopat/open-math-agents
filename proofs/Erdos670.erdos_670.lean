import FormalConjectures.ErdosProblems.«670»
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
A fixed-dimensional counterexample to the separated-distances conjecture.

John Tripodo's Lean 4 formalization is reproduced from
https://github.com/jjtripodo-lgtm/erdos-670-r29/tree/6d629227b1e8d21ab9f09d8a3a667015e78e468a .
The source modules are combined and the final statement uses the repository's pinned definition.
-/

/-
MIT License

Copyright (c) 2026 John Tripodo

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

-- From MatrixCertificates.lean
noncomputable section

open scoped Matrix BigOperators
namespace Erdos670R29

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_infinity : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(154907868127150589 / 1923304880250000 : ℝ), (1696688651775479 / 25644065070000 : ℝ), (125479651378551811 / 1923304880250000 : ℝ), (-855013526827973 / 80137703343750 : ℝ), (23678332272023071 / 384660976050000 : ℝ);
    (1696688651775479 / 25644065070000 : ℝ), (60360400398257 / 657540130000 : ℝ), (123342327356291711 / 1282203253500000 : ℝ), (-103654360977957 / 5342513556250 : ℝ), (1382104386128603 / 25644065070000 : ℝ);
    (125479651378551811 / 1923304880250000 : ℝ), (123342327356291711 / 1282203253500000 : ℝ), (65529018175226903 / 641101626750000 : ℝ), (-6486353065612211 / 240413110031250 : ℝ), (18316487478235019 / 384660976050000 : ℝ);
    (-855013526827973 / 80137703343750 : ℝ), (-103654360977957 / 5342513556250 : ℝ), (-6486353065612211 / 240413110031250 : ℝ), (18566550141185716 / 120206555015625 : ℝ), (33932098089378769 / 769321952100000 : ℝ);
    (23678332272023071 / 384660976050000 : ℝ), (1382104386128603 / 25644065070000 : ℝ), (18316487478235019 / 384660976050000 : ℝ), (33932098089378769 / 769321952100000 : ℝ), (2231708054059801 / 15386439042000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_infinity_L : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
    (127251648883160925 / 154907868127150589 : ℝ), 1, 0, 0, 0;
    (11407241034413801 / 14082533466104599 : ℝ), (940189106051962783726244985260481 / 826418379305755437956618593630400 : ℝ), 1, 0, 0;
    (-20520324643871352 / 154907868127150589 : ℝ), (-4401708670379836325207292598169 / 15495344611982914461686598630570 : ℝ), (-19823264814784431790740600874691621189601491918560 / 2857769742550140136253930920634931306700264567177 : ℝ), 1, 0;
    (118391661360115355 / 154907868127150589 : ℝ), (734725316100714292495683378729 / 8264183793057554379566185936304 : ℝ), (-19177189492590380806528344572703713557366728500700 / 2857769742550140136253930920634931306700264567177 : ℝ), (1921252513749450223033767133331831316902219064182260320967130125 / 18055884486521964222273206776163857603931042197563329670022013952 : ℝ), 1]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_infinity_D : Fin 5 → ℝ := ![(154907868127150589 / 1923304880250000 : ℝ), (3099068922396582892337319726114 / 82759738543908932041767213125 : ℝ), (2857769742550140136253930920634931306700264567177 / 3178909004094110081469881257834479769519200000000 : ℝ), (4822618719690695572188356510727526069426026227981658565711008 / 45170631923713597997851621407820009950691390253268228678125 : ℝ), (11969803639470114375654033899666963971150011319277788530276681095214814201858963 / 213704435385587440846239719024081948943425507957182994540264378823478087680000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem completion_infinity_factor :
    completion_infinity_L * Matrix.diagonal completion_infinity_D * completion_infinity_Lᵀ = completion_infinity := by
  ext i j
  change (∑ k : Fin 5, (completion_infinity_L * Matrix.diagonal completion_infinity_D) i k *
    completion_infinity_L j k) = completion_infinity i j
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [completion_infinity, completion_infinity_L, completion_infinity_D, Fin.sum_univ_succ]


set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem completion_infinity_posDef : completion_infinity.PosDef := by
  have htri : completion_infinity_L.IsLowerTriangular := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> norm_num [completion_infinity_L] at *
  have hdet : completion_infinity_L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    norm_num [completion_infinity_L, Fin.prod_univ_succ]
  have hunit : IsUnit completion_infinity_L := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdet]
    exact isUnit_one
  have hdiag : (Matrix.diagonal completion_infinity_D).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [completion_infinity_D]
  have h := hdiag.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, completion_infinity_factor] at h
  exact h



set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_k0 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(1394026811024556049 / 17309743922250000 : ℝ), (46328598787702541 / 692389756890000 : ℝ), (381882790308755381 / 5769914640750000 : ℝ), (-9863605491658714 / 1081858995140625 : ℝ), (1092251527626516371 / 17309743922250000 : ℝ);
    (46328598787702541 / 692389756890000 : ℝ), (124223500469139577 / 1331518763250000 : ℝ), (9099428306584243 / 92318634252000 : ℝ), (-68639378160196897 / 4327435980562500 : ℝ), (110547438593911493 / 1923304880250000 : ℝ);
    (381882790308755381 / 5769914640750000 : ℝ), (9099428306584243 / 92318634252000 : ℝ), (1825298239967760569 / 17309743922250000 : ℝ), (-46808311449577981 / 2163717990281250 : ℝ), (306177224272754669 / 5769914640750000 : ℝ);
    (-9863605491658714 / 1081858995140625 : ℝ), (-68639378160196897 / 4327435980562500 : ℝ), (-46808311449577981 / 2163717990281250 : ℝ), (175152359377665304 / 1081858995140625 : ℝ), (1830238021736459117 / 34619487844500000 : ℝ);
    (1092251527626516371 / 17309743922250000 : ℝ), (110547438593911493 / 1923304880250000 : ℝ), (306177224272754669 / 5769914640750000 : ℝ), (1830238021736459117 / 34619487844500000 : ℝ), (894977181933524927 / 5769914640750000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_k0_L : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
    (1158214969692563525 / 1394026811024556049 : ℝ), 1, 0, 0, 0;
    (1145648370926266143 / 1394026811024556049 : ℝ), (701001149239642661585311528660832325 / 606506437835320855794175275045360616 : ℝ), 1, 0, 0;
    (-157817687866539424 / 1394026811024556049 : ℝ), (-49988431305044237060027259593152553 / 227439914188245320922815728142010231 : ℝ), (-95808687642163620578013701553598383430821956996062360 / 14511543996807096861690871210606487595401269863065701 : ℝ), 1, 0;
    (1092251527626516371 / 1394026811024556049 : ℝ), (60946384821714233961183041071986319 / 454879828376490641845631456284020462 : ℝ), (-97249975348567947158845090161863269255545192027701580 / 14511543996807096861690871210606487595401269863065701 : ℝ), (3540868483579262142574972748292894248293979898053213181968089309757551 / 14946270143939288956934877871713144894543430749669055765832500920369152 : ℝ), 1]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_k0_D : Fin 5 → ℝ := ![(1394026811024556049 / 17309743922250000 : ℝ), (75813304729415106974271909380670077 / 2010853926632154863723518599187500 : ℝ), (14511543996807096861690871210606487595401269863065701 / 20996942252250885259923788328335306031731032212000000 : ℝ), (35928533999854059992631917960848905996498631609781384052481973366272 / 278688362242450205222619016415794913155603344743491428591552234375 : ℝ), (295064111565677587494222415859176640559512433739282003640599757740230038816292365092873 / 4422497586057431447782735798785173077500115685602524773359238496032093334331392000000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem completion_k0_factor :
    completion_k0_L * Matrix.diagonal completion_k0_D * completion_k0_Lᵀ = completion_k0 := by
  ext i j
  change (∑ k : Fin 5, (completion_k0_L * Matrix.diagonal completion_k0_D) i k *
    completion_k0_L j k) = completion_k0 i j
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [completion_k0, completion_k0_L, completion_k0_D, Fin.sum_univ_succ]


set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem completion_k0_posDef : completion_k0.PosDef := by
  have htri : completion_k0_L.IsLowerTriangular := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> norm_num [completion_k0_L] at *
  have hdet : completion_k0_L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    norm_num [completion_k0_L, Fin.prod_univ_succ]
  have hunit : IsUnit completion_k0_L := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdet]
    exact isUnit_one
  have hdiag : (Matrix.diagonal completion_k0_D).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [completion_k0_D]
  have h := hdiag.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, completion_k0_factor] at h
  exact h



set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def coarseGram : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(40846909 / 250000 : ℝ), (1576997 / 10000 : ℝ), (41367491 / 250000 : ℝ), (3749361 / 31250 : ℝ), (9827551 / 50000 : ℝ);
    (1576997 / 10000 : ℝ), (2673189 / 10000 : ℝ), (144778173 / 500000 : ℝ), (1528947 / 6250 : ℝ), (3186129 / 10000 : ℝ);
    (41367491 / 250000 : ℝ), (144778173 / 500000 : ℝ), (95402629 / 250000 : ℝ), (11540109 / 31250 : ℝ), (22033739 / 50000 : ℝ);
    (3749361 / 31250 : ℝ), (1528947 / 6250 : ℝ), (11540109 / 31250 : ℝ), (13487796 / 15625 : ℝ), (74121489 / 100000 : ℝ);
    (9827551 / 50000 : ℝ), (3186129 / 10000 : ℝ), (22033739 / 50000 : ℝ), (74121489 / 100000 : ℝ), (1884761 / 2000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def coarseGram_L : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
    (39424925 / 40846909 : ℝ), 1, 0, 0, 0;
    (41367491 / 40846909 : ℝ), (2651920397490907 / 2350925968628800 : ℝ), 1, 0, 0;
    (29994888 / 40846909 : ℝ), (16444551865119 / 14693287303930 : ℝ), (17204047980065279905440 / 11344946112641979397877 : ℝ), 1, 0;
    (49137755 / 40846909 : ℝ), (26326714551763 / 23509259686288 : ℝ), (113091931577409573265100 / 79414622788493855785139 : ℝ), (115989202024860860556311618375 / 179843218143509606247601277952 : ℝ), 1]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def coarseGram_D : Fin 5 → ℝ := ![(40846909 / 250000 : ℝ), (2938657460786 / 25529318125 : ℝ), (79414622788493855785139 / 1175462984314400000000 : ℝ), (16860301700954025585712619808 / 35452956602006185618365625 : ℝ), (271870469926137074239387919119179863 / 1198954787623397374984008519680000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem coarseGram_factor :
    coarseGram_L * Matrix.diagonal coarseGram_D * coarseGram_Lᵀ = coarseGram := by
  ext i j
  change (∑ k : Fin 5, (coarseGram_L * Matrix.diagonal coarseGram_D) i k *
    coarseGram_L j k) = coarseGram i j
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [coarseGram, coarseGram_L, coarseGram_D, Fin.sum_univ_succ]


set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem coarseGram_posDef : coarseGram.PosDef := by
  have htri : coarseGram_L.IsLowerTriangular := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> norm_num [coarseGram_L] at *
  have hdet : coarseGram_L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    norm_num [coarseGram_L, Fin.prod_univ_succ]
  have hunit : IsUnit coarseGram_L := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdet]
    exact isUnit_one
  have hdiag : (Matrix.diagonal coarseGram_D).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [coarseGram_D]
  have h := hdiag.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, coarseGram_factor] at h
  exact h



end Erdos670R29

end

-- From MatrixInterpolation.lean
section

open scoped Matrix BigOperators
namespace Erdos670R29

lemma gram_affine_identity {ι κ : Type*} [Fintype κ]
    (X Y : Matrix ι κ ℝ) (t : ℝ) :
    ((1-t) • X + t • Y) * ((1-t) • X + t • Y)ᵀ =
      (1-t) • (X*Xᵀ) + t • (Y*Yᵀ) - (t*(1-t)) • ((Y-X)*(Y-X)ᵀ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Whole-matrix endpoint certificates control every point of the affine segment. -/
theorem completion_interpolation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι ι ℝ) (X Y : Matrix ι κ ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hX : (B-X*Xᵀ).PosSemidef) (hY : (B-Y*Yᵀ).PosSemidef) :
    (B - ((1-t) • X + t • Y) * ((1-t) • X + t • Y)ᵀ).PosSemidef := by
  have hG : ((Y-X)*(Y-X)ᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (Y-X)
  have h := ((hX.smul (sub_nonneg.mpr ht1)).add (hY.smul ht0)).add
    (hG.smul (mul_nonneg ht0 (sub_nonneg.mpr ht1)))
  have heq : B - ((1-t) • X + t • Y) * ((1-t) • X + t • Y)ᵀ =
      (1-t) • (B-X*Xᵀ) + t • (B-Y*Yᵀ) + (t*(1-t)) • ((Y-X)*(Y-X)ᵀ) := by
    rw [gram_affine_identity]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact h


end Erdos670R29

end

-- From SourceMatrices.lean
noncomputable section

open scoped Matrix BigOperators

namespace Erdos670R29

set_option maxHeartbeats 3000000 in
def labels : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,3,5,7,14,15; 3,0,2,4,13,12; 5,2,0,1,11,10;
     7,4,1,0,9,8; 14,13,11,9,0,6; 15,12,10,8,6,0]
set_option maxHeartbeats 3000000 in
def sourceD (A B : Fin 6) : ℝ :=
  if A = B then 0 else 457/25 + (569/500)*labels A B
set_option maxHeartbeats 3000000 in
def sourceE (A B : Fin 6) : ℝ :=
  if A = B then 0 else (sourceD A B)^2 - 2*((507/100)^2+(1131/100)^2)
set_option maxHeartbeats 3000000 in
def sourceMacro : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (sourceE 0 i.succ + sourceE 0 j.succ - sourceE i.succ j.succ)/2
set_option maxHeartbeats 3000000 in
def PG (A B : Fin 6) : ℝ := if A.val < B.val then sourceD A B else 0
set_option maxHeartbeats 3000000 in
def PF (A B : Fin 6) : ℝ := sourceD A B - PG A B
set_option maxHeartbeats 3000000 in
def TG : Matrix (Fin 5) (Fin 6) ℝ := fun j A => PG A 0 - PG A j.succ
set_option maxHeartbeats 3000000 in
def TF : Matrix (Fin 5) (Fin 6) ℝ := fun j A => PF A 0 - PF A j.succ
set_option maxHeartbeats 3000000 in
def normalizedDirections (x : ℝ) : Matrix (Fin 5) (Fin 6) ℝ :=
  ((519/1000 : ℝ)*(507/100))⁻¹ • ((138/125 : ℝ) • TG + ((533/500)*x) • TF)
set_option maxHeartbeats 3000000 in
def sourceCompletion (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  sourceMacro - normalizedDirections x * (normalizedDirections x)ᵀ

set_option maxHeartbeats 3000000 in
theorem sourceMacro_eq : sourceMacro = coarseGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.succ, sourceMacro, sourceE, sourceD, labels, coarseGram]

set_option maxHeartbeats 3000000 in
theorem TG_entries : TG = !![(-10847/500 : ℝ), 0, 0, 0, 0, 0;
    (-2397/100 : ℝ), (-5139/250 : ℝ), 0, 0, 0, 0;
    (-13123/500 : ℝ), (-2854/125 : ℝ), (-9709/500 : ℝ), 0, 0, 0;
    (-8553/250 : ℝ), (-16537/500 : ℝ), (-15399/500 : ℝ), (-14261/500 : ℝ), 0, 0;
    (-707/20 : ℝ), (-3992/125 : ℝ), (-1483/50 : ℝ), (-3423/125 : ℝ), (-6277/250 : ℝ), 0] := by
  ext j A
  fin_cases j <;> fin_cases A <;>
    norm_num [Fin.succ, TG, PG, PF, sourceD, labels]

set_option maxHeartbeats 3000000 in
theorem TF_entries : TF = !![0, (10847/500 : ℝ), (1707/500 : ℝ), (1707/500 : ℝ), (569/500 : ℝ), (1707/500 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (1707/250 : ℝ), (1707/500 : ℝ), (569/100 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (13123/500 : ℝ), (569/100 : ℝ), (3983/500 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (13123/500 : ℝ), (8553/250 : ℝ), (5121/500 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (13123/500 : ℝ), (8553/250 : ℝ), (707/20 : ℝ)] := by
  ext j A
  fin_cases j <;> fin_cases A <;>
    norm_num [Fin.succ, TF, PG, PF, sourceD, labels]

set_option maxHeartbeats 3000000 in
theorem sourceCompletion_zero : sourceCompletion 0 = completion_infinity := by
  ext i j
  change sourceMacro i j - (∑ k : Fin 6,
    normalizedDirections 0 i k * normalizedDirections 0 j k) = completion_infinity i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceCompletion, sourceMacro_eq, coarseGram,
      normalizedDirections, TG_entries, TF_entries, completion_infinity,
      Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.add_apply, Fin.sum_univ_succ]

set_option maxHeartbeats 3000000 in
theorem sourceCompletion_endpoint : sourceCompletion (1/100) = completion_k0 := by
  ext i j
  change sourceMacro i j - (∑ k : Fin 6,
    normalizedDirections (1/100) i k * normalizedDirections (1/100) j k) = completion_k0 i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceCompletion, sourceMacro_eq, coarseGram,
      normalizedDirections, TG_entries, TF_entries, completion_k0,
      Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.add_apply, Fin.sum_univ_succ]

set_option maxHeartbeats 3000000 in
theorem sourceMacro_posDef : sourceMacro.PosDef := by
  rw [sourceMacro_eq]
  exact coarseGram_posDef

set_option maxHeartbeats 3000000 in
/-- The full actual source matrix budget holds throughout the finite-k interval. -/
theorem sourceCompletion_posSemidef (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/100) :
    (sourceCompletion x).PosSemidef := by
  have h0 : (sourceCompletion 0).PosSemidef := by
    rw [sourceCompletion_zero]
    exact completion_infinity_posDef.posSemidef
  have h1 : (sourceCompletion (1/100)).PosSemidef := by
    rw [sourceCompletion_endpoint]
    exact completion_k0_posDef.posSemidef
  have heq : (1-100*x) • normalizedDirections 0 +
      (100*x) • normalizedDirections (1/100) = normalizedDirections x := by
    ext i j
    simp only [normalizedDirections, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h := completion_interpolation sourceMacro (normalizedDirections 0)
    (normalizedDirections (1/100)) (100*x) (by positivity) (by linarith) h0 h1
  rw [heq] at h
  exact h



end Erdos670R29

end

-- From SchurTransfer.lean
section

open scoped Matrix
namespace Erdos670R29

/-- The certified five-row budget is equivalent to the six-column residual budget. -/
theorem schur_transfer {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι ι ℝ) (T : Matrix ι κ ℝ) (hB : B.PosDef)
    (h : (B-T*Tᵀ).PosSemidef) :
    ((1 : Matrix κ κ ℝ)-Tᵀ*B⁻¹*T).PosSemidef := by
  letI := hB.isUnit.invertible
  letI : Invertible (1 : Matrix κ κ ℝ) := invertibleOne
  have hblock : (Matrix.fromBlocks B T Tᴴ (1 : Matrix κ κ ℝ)).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ B T Matrix.PosDef.one).2
    simpa only [inv_one, Matrix.mul_one,
      Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hresult := (Matrix.PosDef.fromBlocks₁₁ T (1 : Matrix κ κ ℝ) hB).1 hblock
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hresult


end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.GlobalCompletion.lean
section

/-! A source-pinned kernel for the three-active-group Gram completion used in
JRL PR 2974. This module does not assert the construction's analytic bounds or
its final fixed-dimensional configuration theorem. -/

open scoped BigOperators Matrix
open Matrix

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.CompletionFactor.lean
section

/-! A fixed-coordinate-count PSD residual factor, for the global completion.
Unlike an existential finite-dimensional Gram realization, this does not hide
an unbounded auxiliary dimension. -/

open scoped BigOperators Matrix MatrixOrder
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Every real PSD matrix has a Gram factor with exactly the same index type. -/
theorem psd_same_size_gram_factor {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Q : Matrix κ κ ℝ) (hQ : Q.PosSemidef) :
    ∃ V : Matrix κ κ ℝ, Vᵀ * V = Q := by
  refine ⟨CFC.sqrt Q, ?_⟩
  have hs := (CFC.sqrt_nonneg Q).isSelfAdjoint
  have hstar : (CFC.sqrt Q)ᵀ = CFC.sqrt Q := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hs.star_eq
  rw [hstar, ← pow_two]
  exact CFC.sq_sqrt Q hQ.nonneg

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From GramCompletion.lean
section

open scoped Matrix BigOperators
namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- A whole-matrix certificate constructs one shared macro/direction/residual family. -/
theorem gram_completion {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι ι ℝ) (T : Matrix ι κ ℝ) (hB : B.PosDef)
    (hbudget : (B-T*Tᵀ).PosSemidef) :
    ∃ Q : Matrix ι ι ℝ, ∃ U : Matrix ι κ ℝ, ∃ W : Matrix κ κ ℝ,
      Qᵀ*Q = B ∧ Qᵀ*U = T ∧ Uᵀ*U + Wᵀ*W = 1 := by
  obtain ⟨Q, hQ⟩ := psd_same_size_gram_factor B hB.posSemidef
  let U := Q*(B⁻¹*T)
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).1 hB.isUnit
  have hproj : Qᵀ*U = T := by
    dsimp [U]
    rw [← Matrix.mul_assoc, hQ, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv B hdet, Matrix.one_mul]
  have hBinv : (B⁻¹)ᵀ = B⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.isHermitian.inv.eq
  have hU : Uᵀ*U = Tᵀ*B⁻¹*T := by
    calc
      Uᵀ*U = (B⁻¹*T)ᵀ*(Qᵀ*U) := by
        change (Q*(B⁻¹*T))ᵀ*U = _
        rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Tᵀ*B⁻¹*T := by
        rw [hproj, Matrix.transpose_mul, hBinv]
  have hres : ((1 : Matrix κ κ ℝ)-Uᵀ*U).PosSemidef := by
    rw [hU]
    exact schur_transfer B T hB hbudget
  obtain ⟨W, hW⟩ := psd_same_size_gram_factor _ hres
  refine ⟨Q, U, W, hQ, hproj, ?_⟩
  rw [hW]
  abel


end Erdos670R29

end

-- From FiniteKCompletion.lean
section

open scoped Matrix BigOperators
namespace Erdos670R29

lemma scale_factor {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (h : Uᵀ*U + Wᵀ*W = 1) :
    (R • U)ᵀ*(R • U) + (R • W)ᵀ*(R • W) = Matrix.diagonal (fun _ => R^2) := by
  ext i j
  have hc := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hc
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  have hU : (∑ k, (R*U k i)*(R*U k j)) = R^2*(∑ k, U k i*U k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hW : (∑ k, (R*W k i)*(R*W k j)) = R^2*(∑ k, W k i*W k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hU, hW, ← mul_add, hc]
  by_cases hij : i=j <;> simp [hij]

/-- For every finite k≥100 one shared five-dimensional macro factor and six
completed directions realize the literal source potentials and radius budget. -/
theorem finite_k_completion (k : ℝ) (hk : 100 ≤ k) :
    ∃ Q : Matrix (Fin 5) (Fin 5) ℝ,
    ∃ U : Matrix (Fin 5) (Fin 6) ℝ,
    ∃ W : Matrix (Fin 6) (Fin 6) ℝ,
      Qᵀ*Q = sourceMacro ∧
      Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF) ∧
      Uᵀ*U + Wᵀ*W = Matrix.diagonal (fun _ => ((507/100 : ℝ)*k^2)^2) := by
  have hk0 : 0 < k := by linarith
  have hrec : (1/k : ℝ) ≤ 1/100 := one_div_le_one_div_of_le (by norm_num) hk
  obtain ⟨Q,U,W,hQ,hproj,hfactor⟩ := gram_completion sourceMacro
    (normalizedDirections (1/k)) sourceMacro_posDef
    (sourceCompletion_posSemidef (1/k) (by positivity) hrec)
  let R : ℝ := (507/100)*k^2
  refine ⟨Q,R • U,R • W,hQ,?_,scale_factor U W R hfactor⟩
  have hscale : Qᵀ*(R • U) = R • normalizedDirections (1/k) := by
    calc
      Qᵀ*(R • U) = R • (Qᵀ*U) := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [hproj]
  rw [hscale]
  ext i j
  simp only [normalizedDirections, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, R]
  field_simp
  <;> ring


end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.Defs.lean
section

/-!
Definitions for the unrestricted-dimensional separated Euclidean distance problem.

The development uses an explicit construction surface first.  `Separated` records
unit separation between distances belonging to distinct unordered pairs; the
increment Gram construction is developed in later modules.
-/

namespace Erdos488.Geometry.SeparatedDistances

open scoped BigOperators

/-- An unordered pair of distinct vertices. -/
abbrev Edge (ι : Type*) := {e : Sym2 ι // ¬e.IsDiag}

/-- Distance attached to an unordered pair. -/
noncomputable def edgeDistance {ι E : Type*} [PseudoMetricSpace E]
    (p : ι → E) : Sym2 ι → ℝ :=
  Sym2.lift ⟨fun i j => dist (p i) (p j), fun i j => dist_comm _ _⟩

/-- Publication-facing unit-separation condition on the unordered edge set. -/
def SeparatedConfiguration {ι E : Type*} [PseudoMetricSpace E]
    (p : ι → E) : Prop :=
  ∀ e f : Edge ι, e ≠ f →
    1 ≤ |edgeDistance p e.1 - edgeDistance p f.1|

end Erdos488.Geometry.SeparatedDistances

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.TrigonometricChord.lean
section

/-! Actual trigonometric circle identities and uniform chord lower slope.
These provide analytic inputs, not an assumed final Euclidean configuration. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.HarmonicLocalModel.lean
section

/-! Literal two-harmonic local distance model: feature monotonicity, cone bounds,
and uniform lower separation transfer. This is independent of the global Gram construction. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.TrigonometricFeatures.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.CompletedTrigonometricFeatures.lean
section

/-! Exact global factor-to-coordinate feature identities, following C1--C3.
The matrix factor equality is supplied by the independent global PSD construction. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators Matrix
open Matrix

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.EuclideanClusterCoordinates.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators Matrix
open Matrix

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.EuclideanCrossCoordinates.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators Matrix
open Matrix

/-- Exact finite sum identity used to expand Euclidean squared distances. -/
theorem sum_sq_sub {κ : Type*} [Fintype κ] (x y : κ → ℝ) :
    (∑ q, (x q-y q)^2)=(∑ q, (x q)^2)+(∑ q, (y q)^2)-2*(x ⬝ᵥ y) := by
  have he : ∀ q, (x q-y q)^2=(x q)^2+(y q)^2-2*(x q*y q) := by
    intro q
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,dotProduct,← Finset.mul_sum]

/-- General macro-coordinate expansion, with both signed projection terms retained. -/
theorem coarse_coordinate_expansion {ι : Type*} [Fintype ι] (a b u v : ι → ℝ) (S : ℝ) :
    (∑ q, (S*a q+u q-(S*b q+v q))^2)=
      S^2*(∑ q, (a q-b q)^2)+2*S*((a-b) ⬝ᵥ (u-v))+(∑ q, (u q-v q)^2) := by
  have he : ∀ q, (S*a q+u q-(S*b q+v q))^2=
      S^2*(a q-b q)^2+2*S*((a q-b q)*(u q-v q))+(u q-v q)^2 := by
    intro q
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,dotProduct,Pi.sub_apply]

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CircleGeometry.lean
section

/-!
Orthogonal-circle geometry for the fifth-pass construction.
Source: consecutive-euclidean-distances, merge 1d8de6b,
candidate/fixed670-orthogonal-circles-pass5-20261013/orthogonal_circles.tex,
Lemma completion and equations cross-expansion and actual-point.

The old nine-block construction is not modified. The whole-matrix quadratic
budget below is the operator-norm hypothesis, not a columnwise substitute.
-/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
namespace Pass5
open scoped BigOperators Matrix
open Matrix

/-- Coordinate type of the new construction: macro space and two m-blocks. -/
abbrev CircleCoordinate (ι κ : Type*) := ι ⊕ (κ ⊕ κ)

/-- The literal circle perturbation, with the prescribed macro projection. -/
noncomputable def circlePerturbation {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (R : ℝ) (A : κ) (z : ℝ) : CircleCoordinate ι κ → ℝ :=
  Sum.elim (fun i => U i A * Real.sin z)
    (Sum.elim (fun i => W i A * Real.sin z)
      (fun i => if i = A then R * Real.cos z else 0))

/-- Actual Euclidean coordinates; all points share the same three blocks. -/
noncomputable def circlePoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (A : κ) (z : ℝ) : EuclideanSpace ℝ (CircleCoordinate ι κ) :=
  WithLp.toLp 2 (Sum.elim (fun i => S * q A i + U i A * Real.sin z)
    (Sum.elim (fun i => W i A * Real.sin z)
      (fun i => if i = A then R * Real.cos z else 0)))

/-- The factor equation gives the exact pairwise column Gram matrix. -/
theorem completed_column_dot {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2)) (A B : κ) :
    (∑ i, U i A * U i B) + (∑ i, W i A * W i B) =
      if A = B then R^2 else 0 := by
  have h := congrFun (congrFun hfactor A) B
  simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply] using h

/-- The circle planes for distinct anchors are genuinely orthogonal. -/
theorem circlePerturbation_dot {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (z w : ℝ) :
    circlePerturbation U W R A z ⬝ᵥ circlePerturbation U W R B w =
      if A = B then R^2 * (Real.sin z * Real.sin w + Real.cos z * Real.cos w)
      else 0 := by
  have hm (M : Matrix ι κ ℝ) :
      (∑ i, (M i A * Real.sin z) * (M i B * Real.sin w)) =
        (∑ i, M i A * M i B) * (Real.sin z * Real.sin w) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hw : (∑ i, (W i A * Real.sin z) * (W i B * Real.sin w)) =
      (∑ i, W i A * W i B) * (Real.sin z * Real.sin w) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [circlePerturbation, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  rw [hm, hw]
  have hc := completed_column_dot U W R hfactor A B
  by_cases hAB : A = B
  · subst B
    simp only [ite_true] at hc ⊢
    have hp : (∑ i, (if i = A then R * Real.cos z else 0) *
        (if i = A then R * Real.cos w else 0)) =
        R^2 * (Real.cos z * Real.cos w) := by
      have he (i : κ) :
          (if i = A then R * Real.cos z else 0) *
            (if i = A then R * Real.cos w else 0) =
          if i = A then R^2 * (Real.cos z * Real.cos w) else 0 := by
        by_cases hi : i = A <;> simp [hi] <;> ring
      simp_rw [he]
      simp
    rw [hp]
    linear_combination (Real.sin z * Real.sin w) * hc
  · have hp : (∑ i, (if i = A then R * Real.cos z else 0) *
        (if i = B then R * Real.cos w else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i = A
      · subst i
        simp [hAB]
      · simp [hi]
    rw [hp, if_neg hAB]
    rw [if_neg hAB] at hc
    linear_combination (Real.sin z * Real.sin w) * hc

/-- Every perturbation has the common squared norm R². -/
theorem circlePerturbation_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z : ℝ) :
    (∑ i, (circlePerturbation U W R A z i)^2) = R^2 := by
  have h := circlePerturbation_dot U W R hfactor A A z z
  simp only [ite_true, dotProduct, ← pow_two] at h
  rw [Real.sin_sq_add_cos_sq, mul_one] at h
  exact h

/-- Exact common-circle chord square, derived from the completed Gram matrix. -/
theorem circlePerturbation_same_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z w : ℝ) :
    (∑ i, (circlePerturbation U W R A z i - circlePerturbation U W R A w i)^2) =
      (2*R*Real.sin ((z-w)/2))^2 := by
  rw [sum_sq_sub, circlePerturbation_square U W R hfactor,
    circlePerturbation_square U W R hfactor, circlePerturbation_dot U W R hfactor]
  simp only [ite_true]
  have h := Real.sin_sq_eq_half_sub ((z-w)/2)
  rw [show 2*((z-w)/2)=z-w by ring, Real.cos_sub] at h
  nlinarith [congrArg (fun t : ℝ => R^2*t) h]

/-- Distinct circle planes contribute precisely 2R² to the squared distance. -/
theorem circlePerturbation_cross_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (hAB : A ≠ B) (z w : ℝ) :
    (∑ i, (circlePerturbation U W R A z i - circlePerturbation U W R B w i)^2) =
      2*R^2 := by
  rw [sum_sq_sub, circlePerturbation_square U W R hfactor,
    circlePerturbation_square U W R hfactor, circlePerturbation_dot U W R hfactor,
    if_neg hAB]
  ring

/-- Same-cluster distances are actual circle chords, with no extra correction. -/
theorem circlePoint_same_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z w : ℝ) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R A w)^2 =
      (2*R*Real.sin ((z-w)/2))^2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simpa only [circlePoint, circlePerturbation, WithLp.ofLp_toLp,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Real.dist_eq, sq_abs,
    add_sub_add_left_eq_sub] using circlePerturbation_same_square U W R hfactor A z w

/-- Exact cross expansion in the literal r+2m coordinate space. -/
theorem circlePoint_cross_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (hAB : A ≠ B) (z w : ℝ) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R B w)^2 =
      S^2*(∑ i, (q A i-q B i)^2) + 2*R^2 +
        2*S*((q A-q B) ⬝ᵥ ((fun i => U i A*Real.sin z)-(fun i => U i B*Real.sin w))) := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [circlePoint, WithLp.ofLp_toLp, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Real.dist_eq, sq_abs]
  rw [coarse_coordinate_expansion]
  have hp := circlePerturbation_cross_square U W R hfactor A B hAB z w
  simp only [circlePerturbation, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hp
  linarith

end Pass5
end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From TwoCircleGeometry.lean
section

namespace Erdos670R29
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5

abbrev TwoCircleCoordinate (ι κ : Type*) :=
  CircleCoordinate ι κ ⊕ CircleCoordinate (Fin 0) κ

noncomputable def joinPoints {α β : Type*} [Fintype α] [Fintype β]
    (x : EuclideanSpace ℝ α) (y : EuclideanSpace ℝ β) :
    EuclideanSpace ℝ (α ⊕ β) := WithLp.toLp 2 (Sum.elim x y)

theorem joinPoints_dist_sq {α β : Type*} [Fintype α] [Fintype β]
    (x x' : EuclideanSpace ℝ α) (y y' : EuclideanSpace ℝ β) :
    dist (joinPoints x y) (joinPoints x' y') ^ 2 =
      dist x x' ^ 2 + dist y y' ^ 2 := by
  simp only [EuclideanSpace.dist_sq_eq, joinPoints, WithLp.ofLp_toLp,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem private_factor {κ : Type*} [Fintype κ] [DecidableEq κ] (R : ℝ) :
    (0 : Matrix (Fin 0) κ ℝ)ᵀ * (0 : Matrix (Fin 0) κ ℝ) +
      (diagonal (fun _ : κ => R))ᵀ * diagonal (fun _ => R) =
      diagonal (fun _ => R ^ 2) := by
  simp [Matrix.diagonal_mul_diagonal, pow_two]

noncomputable def privatePoint {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℝ) (A : κ) (w : ℝ) : EuclideanSpace ℝ (CircleCoordinate (Fin 0) κ) :=
  circlePoint (fun _ _ => 0) 0 (diagonal (fun _ => R)) 0 R A w

noncomputable def twoCirclePoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R₀ R₁ : ℝ) (A : κ) (z w : ℝ) :
    EuclideanSpace ℝ (TwoCircleCoordinate ι κ) :=
  joinPoints (circlePoint q U W S R₀ A z) (privatePoint R₁ A w)

theorem twoCircle_same_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R₀ R₁ : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = diagonal (fun _ => R₀ ^ 2))
    (A : κ) (z z' w w' : ℝ) :
    dist (twoCirclePoint q U W S R₀ R₁ A z w)
      (twoCirclePoint q U W S R₀ R₁ A z' w') ^ 2 =
      (2 * R₀ * Real.sin ((z-z')/2)) ^ 2 +
      (2 * R₁ * Real.sin ((w-w')/2)) ^ 2 := by
  unfold twoCirclePoint privatePoint
  rw [joinPoints_dist_sq, circlePoint_same_square q U W S R₀ hfactor,
    circlePoint_same_square _ _ _ _ _ (private_factor R₁)]

theorem twoCircle_cross_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R₀ R₁ : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = diagonal (fun _ => R₀ ^ 2))
    (A B : κ) (hAB : A ≠ B) (z z' w w' : ℝ) :
    dist (twoCirclePoint q U W S R₀ R₁ A z w)
      (twoCirclePoint q U W S R₀ R₁ B z' w') ^ 2 =
      S^2 * (∑ i, (q A i-q B i)^2) + 2*(R₀^2+R₁^2) +
      2*S*((q A-q B) ⬝ᵥ ((fun i => U i A*Real.sin z)-
        (fun i => U i B*Real.sin z'))) := by
  unfold twoCirclePoint privatePoint
  rw [joinPoints_dist_sq, circlePoint_cross_square q U W S R₀ hfactor A B hAB,
    circlePoint_cross_square _ _ _ _ _ (private_factor R₁) A B hAB]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add]
  ring

theorem coordinate_card : Fintype.card (TwoCircleCoordinate (Fin 5) (Fin 6)) = 29 := by
  decide




end Erdos670R29

end

-- From AnchorInterface.lean
section

namespace Erdos670R29
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension

def anchor (Q : Matrix (Fin 5) (Fin 5) ℝ) (A : Fin 6) : Fin 5 → ℝ :=
  Fin.cases (fun _ => 0) (fun j i => Q i j) A

lemma sourceE_self (A : Fin 6) : sourceE A A = 0 := by simp [sourceE]
lemma sourceE_symm (A B : Fin 6) : sourceE A B = sourceE B A := by
  fin_cases A <;> fin_cases B <;> norm_num [sourceE, sourceD, labels]
lemma sourceD_self (A : Fin 6) : sourceD A A = 0 := by simp [sourceD]
lemma PG_self (A : Fin 6) : PG A A = 0 := by simp [PG]
lemma PF_self (A : Fin 6) : PF A A = 0 := by simp [PF, PG_self, sourceD_self]

lemma anchor_dot (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (hQ : Qᵀ*Q = sourceMacro) (A B : Fin 6) :
    anchor Q A ⬝ᵥ anchor Q B =
      (sourceE 0 A + sourceE 0 B - sourceE A B)/2 := by
  refine Fin.cases ?_ (fun a => ?_) A
  · simp [anchor, dotProduct, sourceE_self]
  refine Fin.cases ?_ (fun b => ?_) B
  · simp [anchor, dotProduct, sourceE_self, sourceE_symm a.succ 0]
  have h := congrFun (congrFun hQ a) b
  simpa [anchor, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, sourceMacro] using h

lemma anchor_distance_square (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (hQ : Qᵀ*Q = sourceMacro) (A B : Fin 6) :
    (∑ i, (anchor Q A i-anchor Q B i)^2) = sourceE A B := by
  rw [sum_sq_sub]
  have hA := anchor_dot Q hQ A A
  have hB := anchor_dot Q hQ B B
  have hAB := anchor_dot Q hQ A B
  simp only [sourceE_self, sub_zero, dotProduct] at hA hB hAB
  simp only [pow_two, dotProduct]
  linarith

lemma anchor_projection (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (k : ℝ)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (A J : Fin 6) :
    anchor Q J ⬝ᵥ (fun i => U i A) =
      k/(519/1000) * ((138/125*k)*(PG A 0-PG A J)+(533/500)*(PF A 0-PF A J)) := by
  refine Fin.cases ?_ (fun j => ?_) J
  · simp [anchor, dotProduct]
  have h := congrFun (congrFun hp j) A
  simpa [anchor, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
    Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, TG, TF] using h

lemma anchored_projection (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (k : ℝ)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (A B : Fin 6) :
    (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A) =
      k/(519/1000) * ((138/125*k)*PG A B+(533/500)*PF A B) := by
  rw [sub_dotProduct, anchor_projection Q U k hp, anchor_projection Q U k hp]
  rw [PG_self, PF_self]
  ring



end Erdos670R29

end

-- From ActualCoordinates.lean
section

namespace Erdos670R29
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma sourceD_symm (A B : Fin 6) : sourceD A B = sourceD B A := by
  fin_cases A <;> fin_cases B <;> norm_num [sourceD, labels]

lemma sourceE_offdiag (A B : Fin 6) (hAB : A ≠ B) :
    sourceE A B = (sourceD A B)^2 - 2*((507/100 : ℝ)^2+(1131/100 : ℝ)^2) := by
  simp [sourceE, hAB]

lemma oriented_projections (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (k : ℝ)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (A B : Fin 6) (hAB : A < B) :
    (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A) =
        k/(519/1000)*(138/125*k)*sourceD A B ∧
    (anchor Q B-anchor Q A) ⬝ᵥ (fun i => U i B) =
        k/(519/1000)*(533/500)*sourceD A B := by
  have hBA : ¬ B.val < A.val := by omega
  rw [anchored_projection Q U k hp, anchored_projection Q U k hp]
  simp only [PG, PF, show A.val < B.val from hAB, hBA, if_true, if_false,
    sub_self, mul_zero, add_zero, zero_add, sub_zero, sourceD_symm B A]
  constructor <;> ring

/-- Exact literal-coordinate cross identity for every ordered pair of anchors.
The private ruler angles are arbitrary: their contribution is exactly constant. -/
theorem actual_cross_square (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (W : Matrix (Fin 6) (Fin 6) ℝ) (k : ℝ)
    (hQ : Qᵀ*Q = sourceMacro)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (hfactor : Uᵀ*U+Wᵀ*W = diagonal (fun _ => ((507/100 : ℝ)*k^2)^2))
    (A B : Fin 6) (hAB : A < B) (z z' w w' : ℝ) :
    dist (twoCirclePoint (anchor Q) U W (k^2) ((507/100)*k^2) ((1131/100)*k^2) A z w)
      (twoCirclePoint (anchor Q) U W (k^2) ((507/100)*k^2) ((1131/100)*k^2) B z' w') ^ 2 =
      (k^2*sourceD A B)^2 + 2*(k^2*sourceD A B)*
        ((138/125*k)*(k/(519/1000)*Real.sin z)+(533/500)*(k/(519/1000)*Real.sin z')) := by
  rw [twoCircle_cross_square _ _ _ _ _ _ hfactor A B (ne_of_lt hAB),
    anchor_distance_square Q hQ, sourceE_offdiag A B (ne_of_lt hAB)]
  obtain ⟨ha,hb⟩ := oriented_projections Q U k hp A B hAB
  have hsA : (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A*Real.sin z) =
      ((anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A))*Real.sin z := by
    simp only [dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsB : (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i B*Real.sin z') =
      -((anchor Q B-anchor Q A) ⬝ᵥ (fun i => U i B))*Real.sin z' := by
    simp only [dotProduct, Pi.sub_apply]
    rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [dotProduct_sub, hsA, hsB, ha, hb]
  ring


end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.PrimeRuler.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SineDigits.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def sineDigit (θ center x : ℝ) : ℝ := Real.sin (θ*(x-center))/θ

theorem hasDerivAt_sineDigit (θ center x : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (sineDigit θ center) (Real.cos (θ*(x-center))) x := by
  have h := ((((hasDerivAt_id x).sub_const center).const_mul θ).sin).div_const θ
  have he : (Real.cos (θ*(x-center))*(θ*1))/θ=Real.cos (θ*(x-center)) := by field_simp
  convert h using 1 <;> first | rfl | exact he.symm

/-- The normalized sine digit never exceeds its centered coordinate in magnitude. -/
theorem sineDigit_abs_le (θ center x : ℝ) (hθ : 0 < θ) :
    |sineDigit θ center x| ≤ |x-center| := by
  unfold sineDigit
  rw [abs_div,abs_of_pos hθ]
  calc
    |Real.sin (θ*(x-center))|/θ ≤ |θ*(x-center)|/θ :=
      div_le_div_of_nonneg_right Real.abs_sin_le_abs hθ.le
    _ = |x-center| := by rw [abs_mul,abs_of_pos hθ]; field_simp

/-- Centered coordinate bounds apply to every digit in the full interval. -/
theorem sineDigit_centered_bound (θ center x : ℝ) (hθ : 0 < θ)
    (hx : 0 ≤ x) (hxc : x ≤ 2*center) : |sineDigit θ center x| ≤ center := by
  apply (sineDigit_abs_le θ center x hθ).trans
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Uniform adjacent and nonadjacent sine digit lower slope on the centered interval. -/
theorem sineDigit_lower_difference (θ center x y : ℝ) (hθ : 0 < θ)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2*center) :
    (1-(θ*center)^2/2)*(y-x) ≤ sineDigit θ center y-sineDigit θ center x := by
  have hc : 0 ≤ center := by linarith
  have hd (z : ℝ) := hasDerivAt_sineDigit θ center z hθ.ne'
  apply (convex_Icc (0 : ℝ) (2*center)).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) (2*center) := interior_subset hz
  have hb : |z-center| ≤ center := abs_le.mpr ⟨by linarith [hz'.1],by linarith [hz'.2]⟩
  have harg : |θ*(z-center)| ≤ |θ*center| := by
    rw [abs_mul,abs_mul,abs_of_pos hθ,abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hb hθ.le
  have hsq : (θ*(z-center))^2 ≤ (θ*center)^2 := sq_le_sq.mpr harg
  rw [(hd z).deriv]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := θ*(z-center))
  linarith

/-- Source-shaped finite digit bound, valid for all k and every legal index. -/
theorem finite_sineDigit_bound (θ : ℝ) (k i : ℕ) (hθ : 0 < θ) (hi : i < k) :
    |sineDigit θ (((k : ℝ)-1)/2) i| ≤ ((k : ℝ)-1)/2 := by
  apply sineDigit_centered_bound θ (((k : ℝ)-1)/2) i hθ (by positivity)
  have h : (i : ℝ)+1 ≤ k := by exact_mod_cast hi
  linarith

/-- Uniform lower step from the source's θ²k²≤epsilon envelope. -/
theorem finite_sineDigit_step (θ ε : ℝ) (k i : ℕ) (hθ : 0 < θ)
    (hi : i+1 < k) (hscale : θ^2*(k : ℝ)^2 ≤ ε) :
    1-ε/8 ≤ sineDigit θ (((k : ℝ)-1)/2) (i+1)-
      sineDigit θ (((k : ℝ)-1)/2) i := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hi' : (i : ℝ)+2 ≤ k := by exact_mod_cast hi
  have h := sineDigit_lower_difference θ (((k : ℝ)-1)/2) i ((i : ℝ)+1)
    hθ (by positivity) (by linarith) (by linarith)
  have hb : θ^2*((k : ℝ)-1)^2 ≤ θ^2*(k : ℝ)^2 := by
    have hsq : ((k : ℝ)-1)^2 ≤ (k : ℝ)^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg θ)
  norm_num at h
  nlinarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Ruler.lean
section

/-! Exact integer-ruler layer. Unlike a residue-only statement, these theorems
refer to the actual differences of the explicit ruler positions. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The fifth-pass ruler, with the linear spacing parameter L explicit. -/
def pass5Ruler (L p k A i : ℕ) : ℤ :=
  (L : ℤ) * (p : ℤ) * (i : ℤ) + ((i^2 + 2*k*A*i) % p : ℕ)

/-- A positive-lag difference, kept in the integers so subtraction never truncates. -/
def pass5RulerGap (L p k A i δ : ℕ) : ℤ :=
  pass5Ruler L p k A (i + δ) - pass5Ruler L p k A i

/-- Every actual ruler difference lies in its strict lag window. -/
theorem pass5RulerGap_window (L p k A i δ : ℕ) (hp : 0 < p) :
    ((L : ℤ) * (δ : ℤ) - 1) * p < pass5RulerGap L p k A i δ ∧
      pass5RulerGap L p k A i δ < ((L : ℤ) * (δ : ℤ) + 1) * p := by
  have h₀ : (0 : ℤ) ≤ ((i^2 + 2*k*A*i) % p : ℕ) := by positivity
  have h₁ : (0 : ℤ) ≤ (((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) := by positivity
  have h₂ : (((i^2 + 2*k*A*i) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  have h₃ : ((((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  dsimp [pass5RulerGap, pass5Ruler]
  push_cast at *
  constructor <;> nlinarith

/-- Different lag windows are strictly ordered for every L ≥ 2. -/
theorem pass5RulerGap_different_lag (L p k A B i j δ ε : ℕ)
    (hp : 0 < p) (hL : 2 ≤ L) (hδε : δ < ε) :
    0 < pass5RulerGap L p k B j ε - pass5RulerGap L p k A i δ := by
  have h₀ := (pass5RulerGap_window L p k A i δ hp).2
  have h₁ := (pass5RulerGap_window L p k B j ε hp).1
  have hδε' : (δ : ℤ) + 1 ≤ ε := by exact_mod_cast hδε
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hL' : (2 : ℤ) ≤ L := by exact_mod_cast hL
  have hd : (L : ℤ) * δ + 2 ≤ (L : ℤ) * ε := by
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ L) (by omega : (0 : ℤ) ≤ ε-δ-1)]
  nlinarith

/-- The actual ruler difference has exactly the stated quadratic residue. -/
theorem pass5RulerGap_residue (L p k A i δ : ℕ) :
    pass5RulerGap L p k A i δ % (p : ℤ) =
      ((δ * (2*i + δ + 2*k*A) : ℕ) : ℤ) % (p : ℤ) := by
  have hpoly : (((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
      ((i^2 + 2*k*A*i : ℕ) : ℤ) = ((δ*(2*i+δ+2*k*A) : ℕ) : ℤ) := by
    push_cast
    ring
  calc
    pass5RulerGap L p k A i δ % (p : ℤ) =
        ((((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
          ((i^2 + 2*k*A*i : ℕ) : ℤ)) % (p : ℤ) := by
      simp [pass5RulerGap, pass5Ruler, Int.add_emod, Int.sub_emod,
        Int.mul_emod, Int.natCast_emod]
    _ = _ := congrArg (fun z : ℤ => z % (p : ℤ)) hpoly

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Parameters.lean
section

/-! Exact scalar certificates for the orthogonal-circle fifth-pass manuscript.
These results prove the numerical hypotheses; they do not assert existence
of the geometric configuration supplied by the finite criterion. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5GeometryParameters.lean
section

/-! The concrete circle scales discharge the macro/completion scalar gates.
This module constructs no points; the geometry source is kept separate. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Local.lean
section

/-! Exact local-circle length bounds for the fifth-pass parameters. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5Chord (R θ D x : ℝ) : ℝ := 2*R*Real.sin (θ*x/(2*D))

theorem hasDerivAt_pass5Chord (R θ D x : ℝ) (hD : D ≠ 0) :
    HasDerivAt (pass5Chord R θ D)
      (R*θ/D*Real.cos (θ*x/(2*D))) x := by
  have h := ((((hasDerivAt_id x).const_mul θ).div_const (2*D)).sin).const_mul (2*R)
  have he : 2*R*(Real.cos (θ*x/(2*D))*(θ*1/(2*D))) =
      R*θ/D*Real.cos (θ*x/(2*D)) := by field_simp <;> ring
  convert h using 1 <;> first | rfl | exact he.symm

theorem pass5Chord_lower_difference (R θ D a Y x y : ℝ)
    (hR : 0 < R) (hθ : 0 < θ) (hD : 0 < D) (ha : 0 ≤ a)
    (hscale : θ*Y ≤ a*D) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Y) :
    (R*θ/D)*(1-a^2/8)*(y-x) ≤ pass5Chord R θ D y-pass5Chord R θ D x := by
  have hd (z : ℝ) := hasDerivAt_pass5Chord R θ D z hD.ne'
  apply (convex_Icc (0 : ℝ) Y).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) Y := interior_subset hz
  have harg0 : 0 ≤ θ*z/(2*D) :=
    div_nonneg (mul_nonneg hθ.le hz'.1) (by positivity)
  have harg : θ*z/(2*D) ≤ a/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*D)).2
    nlinarith [mul_le_mul_of_nonneg_left hz'.2 hθ.le]
  have harg2 : (θ*z/(2*D))^2 ≤ a^2/4 := by nlinarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x := θ*z/(2*D))
  have hcos' : 1-a^2/8 ≤ Real.cos (θ*z/(2*D)) := by nlinarith
  rw [(hd z).deriv]
  exact mul_le_mul_of_nonneg_left hcos' (by positivity)

theorem pass5Chord_upper (R θ D x : ℝ) (hR : 0 < R) (hθ : 0 < θ)
    (hD : 0 < D) (hx : 0 ≤ x) : pass5Chord R θ D x ≤ (R*θ/D)*x := by
  have h := Real.sin_le (show 0 ≤ θ*x/(2*D) by positivity)
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*R by positivity)
  have he : 2*R*(θ*x/(2*D)) = (R*θ/D)*x := by field_simp <;> ring
  simpa only [pass5Chord, he] using hh

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From TrigBounds.lean
section

namespace Erdos670R29

/-- Three angle doublings sharpen the elementary quadratic cosine bound.
This avoids adding an unformalized Taylor remainder estimate. -/
theorem cos_ruler_lower : (255/400 : ℝ) ≤ Real.cos (879/1000) := by
  have h0 := Real.one_sub_sq_div_two_le_cos (x := (879/8000 : ℝ))
  have h0' : (993963/1000000 : ℝ) ≤ Real.cos (879/8000) := by norm_num at h0 ⊢; linarith
  have e1 := Real.cos_two_mul (879/8000 : ℝ)
  have e2 := Real.cos_two_mul (879/4000 : ℝ)
  have e3 := Real.cos_two_mul (879/2000 : ℝ)
  norm_num at e1 e2 e3
  have h1 : (975924/1000000 : ℝ) ≤ Real.cos (879/4000) := by
    nlinarith [sq_nonneg (Real.cos (879/8000)-(993963/1000000 : ℝ))]
  have h2 : (904855/1000000 : ℝ) ≤ Real.cos (879/2000) := by
    nlinarith [sq_nonneg (Real.cos (879/4000)-(975924/1000000 : ℝ))]
  nlinarith [sq_nonneg (Real.cos (879/2000)-(904855/1000000 : ℝ))]

theorem sin_ruler_upper : Real.sin (879/1000) ≤ (78/100 : ℝ) := by
  have h := Real.sin_sq_add_cos_sq (879/1000 : ℝ)
  have hc := cos_ruler_lower
  nlinarith [sq_nonneg (Real.cos (879/1000)-(255/400 : ℝ))]




end Erdos670R29

end

-- From LocalNorm.lean
section

namespace Erdos670R29

/-- A denominator-free lower secant bound for a two-coordinate norm. -/
theorem norm_secant_lower (H x y lam : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hbudget : lam^2*H^2 ≤ (1-lam^2)*x^2) :
    lam*(y-x) ≤ Real.sqrt (H^2+y^2)-Real.sqrt (H^2+x^2) := by
  let X := Real.sqrt (H^2+x^2)
  let Y := Real.sqrt (H^2+y^2)
  have hX : X^2 = H^2+x^2 := Real.sq_sqrt (by positivity)
  have hY : Y^2 = H^2+y^2 := Real.sq_sqrt (by positivity)
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hxy2 : x^2 ≤ y^2 := sq_le_sq₀ hx (hx.trans hxy) |>.2 hxy
  have hl2 : 0 ≤ 1-lam^2 := by nlinarith
  have hby := mul_le_mul_of_nonneg_left hxy2 hl2
  have hlX : lam*X ≤ x := by nlinarith [mul_nonneg hlam hX0]
  have hlY : lam*Y ≤ y := by nlinarith [mul_nonneg hlam hY0]
  have hmono : X ≤ Y := Real.sqrt_le_sqrt (by nlinarith)
  by_cases hsum : X+Y=0
  · have : X=0 ∧ Y=0 := by constructor <;> linarith
    rcases this with ⟨hxx,hyy⟩
    have hxz : x=0 := by nlinarith [sq_nonneg H]
    have hyz : y=0 := by nlinarith [sq_nonneg H]
    change lam*(y-x) ≤ Y-X
    rw [hxz,hyz,hxx,hyy]
    simp
  have hsumpos : 0 < X+Y := by positivity
  change lam*(y-x) ≤ Y-X
  apply (mul_le_mul_iff_of_pos_right hsumpos).mp
  have hm := mul_le_mul_of_nonneg_right (add_le_add hlX hlY) (sub_nonneg.mpr hxy)
  nlinarith only [hm,hX,hY]

/-- A simple ray bound is sufficient for the local ratio budget. -/
theorem sin_ruler_ray (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 879/1000) :
    (87/100 : ℝ)*x ≤ Real.sin x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x; simp
  have hs := Real.sin_gt_sub_cube h
  have hx2 : x^2 ≤ (879/1000 : ℝ)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hx2 hx
  nlinarith



end Erdos670R29

end

-- From LocalScalar.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def localH (k d : ℝ) : ℝ :=
  pass5Chord ((507/100)*k^2) ((519/1000)/k) 1 d
noncomputable def localB (k p g : ℝ) : ℝ :=
  pass5Chord ((1131/100)*k^2) ((879/500)/k) (2*p) g
noncomputable def localLength (k p d g : ℝ) : ℝ :=
  Real.sqrt ((localH k d)^2+(localB k p g)^2)

lemma chord_lower_cos (R θ D Y x y : ℝ)
    (hR : 0 < R) (hθ : 0 < θ) (hD : 0 < D)
    (hscale : θ*Y ≤ (879/500)*D) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Y) :
    (R*θ/D)*(255/400)*(y-x) ≤ pass5Chord R θ D y-pass5Chord R θ D x := by
  have hd (z : ℝ) := hasDerivAt_pass5Chord R θ D z hD.ne'
  apply (convex_Icc (0 : ℝ) Y).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) Y := interior_subset hz
  have harg0 : 0 ≤ θ*z/(2*D) := div_nonneg (mul_nonneg hθ.le hz'.1) (by positivity)
  have harg : θ*z/(2*D) ≤ (879/1000 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*D)).2
    nlinarith [mul_le_mul_of_nonneg_left hz'.2 hθ.le]
  have hpi : (879/1000 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  have hcos := cos_ruler_lower.trans (Real.cos_le_cos_of_nonneg_of_le_pi harg0 hpi harg)
  rw [(hd z).deriv]
  exact mul_le_mul_of_nonneg_left hcos (by positivity)

lemma localB_slope (k p x y : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hpk : p ≤ (303/50)*k) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2*p*k) :
    (5229/5000 : ℝ)*(y-x) ≤ localB k p y-localB k p x := by
  have hs : ((879/500)/k)*(2*p*k) = (879/500)*(2*p) := by field_simp <;> ring
  have h := chord_lower_cos ((1131/100)*k^2) ((879/500)/k) (2*p) (2*p*k) x y
    (by positivity) (by positivity) (by positivity) hs.le hx hxy hy
  have he : (((1131/100)*k^2)*((879/500)/k)/(2*p))*(255/400) =
      (50701599/8000000 : ℝ)*k/p := by field_simp <;> ring
  rw [he] at h
  have hl : (5229/5000 : ℝ) ≤ (50701599/8000000 : ℝ)*k/p := by
    apply (le_div_iff₀ hp).2
    nlinarith
  exact (mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hxy)).trans h

lemma localH_bounds (k d : ℝ) (hk : 0 < k) (hd : 0 ≤ d) (hdk : d ≤ k) :
    0 ≤ localH k d ∧ localH k d ≤ (263133/100000 : ℝ)*k*d := by
  have harg0 : 0 ≤ ((519/1000)/k)*d/(2*1) := by positivity
  have harg : ((519/1000)/k)*d/(2*1) ≤ (519/2000 : ℝ) := by
    field_simp
    nlinarith
  constructor
  · unfold localH pass5Chord
    apply mul_nonneg (by positivity)
    exact Real.sin_nonneg_of_nonneg_of_le_pi harg0 (harg.trans (by linarith [Real.two_le_pi]))
  · have h := pass5Chord_upper ((507/100)*k^2) ((519/1000)/k) 1 d
      (by positivity) (by positivity) (by norm_num) hd
    have he : ((507/100)*k^2)*((519/1000)/k)/1*d = (263133/100000 : ℝ)*k*d := by
      field_simp; ring
    simpa only [he, localH] using h

lemma localB_ray (k p d g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hd : 0 ≤ d) (hg : p*d ≤ g) (hgup : g ≤ 2*p*k) :
    (86490963/10000000 : ℝ)*k*d ≤ localB k p g := by
  have hg0 : 0 ≤ g := (mul_nonneg hp.le hd).trans hg
  have harg0 : 0 ≤ ((879/500)/k)*g/(2*(2*p)) := by positivity
  have he : ((879/500)/k)*g/(2*(2*p)) = (879/2000)*g/(p*k) := by field_simp <;> ring
  have harg : ((879/500)/k)*g/(2*(2*p)) ≤ (879/1000 : ℝ) := by
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < p*k)).2
    nlinarith
  have h := sin_ruler_ray _ harg0 harg
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*((1131/100 : ℝ)*k^2) by positivity)
  have hs : 2*((1131/100 : ℝ)*k^2)*((87/100)*(((879/500)/k)*g/(2*(2*p)))) =
      (86490963/10000000 : ℝ)*k*g/p := by field_simp <;> ring
  rw [hs] at hm
  have hl : (86490963/10000000 : ℝ)*k*d ≤ (86490963/10000000 : ℝ)*k*g/p := by
    apply (le_div_iff₀ hp).2
    nlinarith [mul_le_mul_of_nonneg_left hg (show 0 ≤ (86490963/10000000 : ℝ)*k by positivity)]
  exact hl.trans hm




end Erdos670R29

end

-- From LocalSeparation.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma local_ratio_budget (k p d g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hd : 0 ≤ d) (hdk : d ≤ k) (hg : p*d ≤ g) (hgup : g ≤ 2*p*k) :
    (2391/2500 : ℝ)^2*(localH k d)^2 ≤
      (1-(2391/2500 : ℝ)^2)*(localB k p g)^2 := by
  obtain ⟨hH0,hH⟩ := localH_bounds k d hk hd hdk
  have hB := localB_ray k p d g hk hp hd hg hgup
  have hkd : 0 ≤ k*d := mul_nonneg hk.le hd
  have hHsq : (localH k d)^2 ≤ ((263133/100000 : ℝ)*(k*d))^2 := by
    apply (sq_le_sq₀ hH0 (by positivity)).2
    nlinarith only [hH]
  have hBsq : ((86490963/10000000 : ℝ)*(k*d))^2 ≤ (localB k p g)^2 := by
    apply (sq_le_sq₀ (by positivity) (by nlinarith only [hB,hkd])).2
    nlinarith only [hB]
  nlinarith [sq_nonneg (k*d)]

/-- Strict unit separation follows from an integer-sized ruler increment. -/
theorem local_fixed_lag_gap (k p d x y : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hpk : p ≤ (303/50)*k) (hd : 0 ≤ d) (hdk : d ≤ k)
    (hx : p*d ≤ x) (hgap : 1 ≤ y-x) (hy : y ≤ 2*p*k) :
    1 < localLength k p d y-localLength k p d x := by
  have hxy : x ≤ y := by linarith
  have hx0 : 0 ≤ x := (mul_nonneg hp.le hd).trans hx
  have hs := localB_slope k p x y hk hp hpk hx0 hxy hy
  have hbx := localB_ray k p d x hk hp hd hx (hxy.trans hy)
  have hb0 : 0 ≤ localB k p x := by nlinarith [mul_nonneg hk.le hd]
  have hbxy : localB k p x ≤ localB k p y := by linarith
  have hb := local_ratio_budget k p d x hk hp hd hdk hx (hxy.trans hy)
  have hnorm := norm_secant_lower (localH k d) (localB k p x) (localB k p y)
    (2391/2500) hb0 hbxy (by norm_num) (by norm_num) hb
  unfold localLength
  nlinarith

lemma localH_monotone (k d e : ℝ) (hk : 0 < k)
    (hd : 0 ≤ d) (hde : d ≤ e) (hek : e ≤ k) : localH k d ≤ localH k e := by
  have hscale : ((519/1000)/k)*k ≤ (519/1000 : ℝ)*1 := by
    field_simp <;> norm_num
  have h := pass5Chord_lower_difference ((507/100)*k^2) ((519/1000)/k) 1
    (519/1000) k d e (by positivity) (by positivity) (by norm_num) (by norm_num)
    hscale hd hde hek
  have hcoef : 0 ≤ (((507/100)*k^2)*((519/1000)/k)/1)*(1-(519/1000 : ℝ)^2/8) := by
    apply mul_nonneg (by positivity)
    norm_num
  have hm := mul_nonneg hcoef (sub_nonneg.mpr hde)
  exact le_of_sub_nonneg (hm.trans h)

/-- The full real local comparison permits a nondecreasing lag. -/
theorem local_ordered_gap (k p d e x y : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hpk : p ≤ (303/50)*k) (hd : 0 ≤ d) (hde : d ≤ e) (hek : e ≤ k)
    (hx : p*d ≤ x) (hgap : 1 ≤ y-x) (hy : y ≤ 2*p*k) :
    1 < localLength k p e y-localLength k p d x := by
  have h := local_fixed_lag_gap k p d x y hk hp hpk hd (hde.trans hek) hx hgap hy
  have hH := localH_monotone k d e hk hd hde hek
  have hH0 := (localH_bounds k d hk hd (hde.trans hek)).1
  have hs : (localH k d)^2 ≤ (localH k e)^2 := (sq_le_sq₀ hH0 (hH0.trans hH)).2 hH
  have hmono : localLength k p d y ≤ localLength k p e y :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith


end Erdos670R29

end

-- From LocalBounds.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma localB_bounds (k p g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hg : 0 ≤ g) (hgup : g ≤ 2*p*k) :
    0 ≤ localB k p g ∧ localB k p g ≤ (44109/2500 : ℝ)*k^2 := by
  have harg0 : 0 ≤ ((879/500)/k)*g/(2*(2*p)) := by positivity
  have he : ((879/500)/k)*g/(2*(2*p)) = (879/2000)*g/(p*k) := by field_simp <;> ring
  have harg : ((879/500)/k)*g/(2*(2*p)) ≤ (879/1000 : ℝ) := by
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < p*k)).2
    nlinarith
  have hpi : (879/1000 : ℝ) ≤ Real.pi/2 := by linarith [Real.two_le_pi]
  have hs := (Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ ((879/500)/k)*g/(2*(2*p)) by linarith [Real.pi_pos]) hpi harg).trans sin_ruler_upper
  constructor
  · unfold localB pass5Chord
    apply mul_nonneg (by positivity)
    exact Real.sin_nonneg_of_nonneg_of_le_pi harg0 (by linarith [Real.pi_pos])
  · have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*((1131/100 : ℝ)*k^2) by positivity)
    dsimp [localB,pass5Chord]
    nlinarith only [hm]

theorem localLength_upper (k p d g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hd : 0 ≤ d) (hdk : d ≤ k) (hg : 0 ≤ g) (hgup : g ≤ 2*p*k) :
    localLength k p d g < 18*k^2 := by
  obtain ⟨hH0,hH⟩ := localH_bounds k d hk hd hdk
  obtain ⟨hB0,hB⟩ := localB_bounds k p g hk hp hg hgup
  have hH' : localH k d ≤ (263133/100000 : ℝ)*k^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hdk hk.le]
  have hHsq : (localH k d)^2 ≤ ((263133/100000 : ℝ)*k^2)^2 :=
    (sq_le_sq₀ hH0 (by positivity)).2 hH'
  have hBsq : (localB k p g)^2 ≤ ((44109/2500 : ℝ)*k^2)^2 :=
    (sq_le_sq₀ hB0 (by positivity)).2 hB
  have hroot : (localLength k p d g)^2 = (localH k d)^2+(localB k p g)^2 :=
    Real.sq_sqrt (by positivity)
  have hpos : 0 < k^4 := pow_pos hk 4
  have hk2 : 0 < k^2 := sq_pos_of_pos hk
  nlinarith

theorem localLength_min (k p d g : ℝ) (hk : 100 ≤ k) (hp : 0 < p)
    (hd : 1 ≤ d) (hg : p*d ≤ g) (hgup : g ≤ 2*p*k) :
    1 < localLength k p d g := by
  have hk0 : 0 < k := by linarith
  have hb := localB_ray k p d g hk0 hp (by linarith) hg hgup
  have hkd : k ≤ k*d := by nlinarith
  have hs : (localLength k p d g)^2 = (localH k d)^2+(localB k p g)^2 :=
    Real.sq_sqrt (by positivity)
  have hn : 0 ≤ localLength k p d g := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (localH k d)]



end Erdos670R29

end

-- From SharpRulerNext.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Prime cancellation needs p > m*k, with the odd prime condition explicit. -/
theorem same_lag_residue_injective_sharp
    (p m k δ A B i j : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hδ : 0 < δ) (hδp : δ < p) (hsize : m*k < p)
    (hA : A < m) (hB : B < m) (hi : i+δ < k) (hj : j+δ < k)
    (heq : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p) :
    A = B ∧ i = j := by
  have hcop : p.Coprime δ := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hδ hδp)
  have hmod : 2*i+δ+2*k*A ≡ 2*j+δ+2*k*B [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime hcop heq
  have hmod' : 2*(i+k*A)+δ ≡ 2*(j+k*B)+δ [MOD p] := by
    have hleft : 2*(i+k*A)+δ = 2*i+δ+2*k*A := by ring
    have hright : 2*(j+k*B)+δ = 2*j+δ+2*k*B := by ring
    simpa only [hleft, hright] using hmod
  have htwo : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) hp2)
  have hs : i+k*A ≡ j+k*B [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime htwo (Nat.ModEq.add_right_cancel' δ hmod')
  have hleft : i+k*A < p := by
    have hh := Nat.mul_le_mul_left k (show A+1 ≤ m by omega)
    nlinarith
  have hright : j+k*B < p := by
    have hh := Nat.mul_le_mul_left k (show B+1 ≤ m by omega)
    nlinarith
  have he := hs.eq_of_lt_of_lt hleft hright
  have hab : A = B := by
    rcases lt_trichotomy A B with h | h | h
    · have hh := Nat.mul_le_mul_left k (show A+1 ≤ B by omega)
      nlinarith
    · exact h
    · have hh := Nat.mul_le_mul_left k (show B+1 ≤ A by omega)
      nlinarith
  exact ⟨hab, by subst B; omega⟩

/-- The actual integer gaps inherit the sharp prime-size condition. -/
theorem rulerGap_same_lag_injective_sharp (L p m k δ A B i j : ℕ)
    (hp : p.Prime) (hp2 : 2 < p) (hδ : 0 < δ) (hδp : δ < p)
    (hsize : m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+δ < k)
    (heq : pass5RulerGap L p k A i δ = pass5RulerGap L p k B j δ) :
    A = B ∧ i = j := by
  have hmod := congrArg (fun z : ℤ => z % (p : ℤ)) heq
  rw [pass5RulerGap_residue, pass5RulerGap_residue] at hmod
  have hnat : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p := by
    exact_mod_cast hmod
  exact same_lag_residue_injective_sharp p m k δ A B i j hp hp2 hδ hδp hsize
    hA hB hi hj hnat



end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From LocalRuler.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma ruler_window_real (p k A i d : ℕ) (hp : 0 < p) (hd : 0 < d) (hi : i+d < k) :
    (p : ℝ)*d ≤ (pass5RulerGap 2 p k A i d : ℝ) ∧
    (pass5RulerGap 2 p k A i d : ℝ) ≤ 2*(p : ℝ)*k := by
  obtain ⟨hl,hu⟩ := pass5RulerGap_window 2 p k A i d hp
  have hl' : (2*(d : ℝ)-1)*p < (pass5RulerGap 2 p k A i d : ℝ) := by exact_mod_cast hl
  have hu' : (pass5RulerGap 2 p k A i d : ℝ) < (2*(d : ℝ)+1)*p := by exact_mod_cast hu
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdk : (d : ℝ)+1 ≤ k := by exact_mod_cast (show d+1 ≤ k by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  constructor <;> nlinarith

lemma ruler_order_lag (p k A B i j d e : ℕ) (hp : 0 < p)
    (hgap : pass5RulerGap 2 p k A i d < pass5RulerGap 2 p k B j e) : d ≤ e := by
  by_contra h
  have he : e < d := by omega
  have hw := pass5RulerGap_different_lag 2 p k B A j i e d hp (by norm_num) he
  omega

lemma ruler_injective (p k A B i j d e : ℕ) (hp : p.Prime) (hk : 100 ≤ k)
    (hsize : 6*k < p) (hA : A < 6) (hB : B < 6)
    (hd : 0 < d) (he : 0 < e) (hi : i+d < k) (hj : j+e < k)
    (heq : pass5RulerGap 2 p k A i d = pass5RulerGap 2 p k B j e) :
    A=B ∧ i=j ∧ d=e := by
  have hde : d=e := by
    rcases lt_trichotomy d e with h | h | h
    · have hw := pass5RulerGap_different_lag 2 p k A B i j d e hp.pos (by norm_num) h
      omega
    · exact h
    · have hw := pass5RulerGap_different_lag 2 p k B A j i e d hp.pos (by norm_num) h
      omega
  subst e
  obtain ⟨hAB,hij⟩ := rulerGap_same_lag_injective_sharp 2 p 6 k d A B i j
    hp (by omega) hd (by omega) hsize hA hB hi hj heq
  exact ⟨hAB,hij,rfl⟩

noncomputable def localEdge (p k A i j : ℕ) : ℝ :=
  localLength k p ((j-i : ℕ) : ℝ) (pass5RulerGap 2 p k A i (j-i))

theorem local_edges_separated (p k A B i j u v : ℕ) (hp : p.Prime) (hk : 100 ≤ k)
    (hsize : 6*k < p) (hpup : 100*p ≤ 606*k) (hA : A < 6) (hB : B < 6)
    (hij : i < j) (huv : u < v) (hj : j < k) (hv : v < k)
    (hne : ¬ (A=B ∧ i=u ∧ j=v)) :
    1 < |localEdge p k A i j-localEdge p k B u v| := by
  have hdi : i+(j-i) < k := by omega
  have hdu : u+(v-u) < k := by omega
  have hd : 0 < j-i := by omega
  have he : 0 < v-u := by omega
  have hgneq : pass5RulerGap 2 p k A i (j-i) ≠ pass5RulerGap 2 p k B u (v-u) := by
    intro h
    obtain ⟨hAB,hi,hde⟩ := ruler_injective p k A B i u (j-i) (v-u) hp hk hsize hA hB hd he hdi hdu h
    apply hne
    exact ⟨hAB,hi,by omega⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpk : (p : ℝ) ≤ (303/50)*(k : ℝ) := by
    have h : (100 : ℝ)*p ≤ 606*k := by exact_mod_cast hpup
    linarith
  have ordered (A B i u d e : ℕ) (hd : 0 < d) (he : 0 < e)
      (hdi : i+d < k) (hdu : u+e < k)
      (hgap : pass5RulerGap 2 p k A i d < pass5RulerGap 2 p k B u e) :
      1 < localLength k p e (pass5RulerGap 2 p k B u e)-
        localLength k p d (pass5RulerGap 2 p k A i d) := by
    have hde := ruler_order_lag p k A B i u d e hp.pos hgap
    have hgap' : (1 : ℝ) ≤ (pass5RulerGap 2 p k B u e : ℝ)-(pass5RulerGap 2 p k A i d : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ pass5RulerGap 2 p k B u e-pass5RulerGap 2 p k A i d by omega)
    exact local_ordered_gap k p d e _ _ hk' hp' hpk (by positivity)
      (by exact_mod_cast hde) (by exact_mod_cast (show e ≤ k by omega))
      (ruler_window_real p k A i d hp.pos hd hdi).1 hgap'
      (ruler_window_real p k B u e hp.pos he hdu).2
  rcases lt_or_gt_of_ne hgneq with h | h
  · have hh := ordered A B i u (j-i) (v-u) hd he hdi hdu h
    unfold localEdge
    rw [abs_of_neg (by linarith)]
    linarith
  · have hh := ordered B A u i (v-u) (j-i) he hd hdu hdi h
    unfold localEdge
    rw [abs_of_pos (by linarith)]
    exact hh


end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SpectrumSeparation.lean
section

/-! The finite ordering layer only. No Euclidean realization or local-distance
geometry is assumed proved by this file. Every scalar guard is explicit. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Sum adjacent unit gaps over a bounded natural index interval. -/
theorem bounded_step_sum (f : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i) :
    ∀ i j, i ≤ j → j < N → (j : ℝ) - (i : ℝ) ≤ f j - f i := by
  intro i j
  induction j with
  | zero =>
      intro hij _
      have hi : i = 0 := by omega
      subst i
      simp
  | succ j ih =>
      intro hij hj
      by_cases h : i ≤ j
      · have h1 := ih h (by omega)
        have h2 := hstep j hj
        push_cast
        linarith
      · have hi : i = j + 1 := by omega
        subst i
        simp

/-- Adjacent unit gaps imply weak monotonicity, including equal endpoints. -/
theorem bounded_step_mono (f : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i)
    {i j : ℕ} (hij : i ≤ j) (hj : j < N) : f i ≤ f j := by
  have h := bounded_step_sum f N hstep i j hij hj
  have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

/-- A nonempty chain of adjacent unit gaps has gap at least one. -/
theorem bounded_step_gap (f : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i)
    {i j : ℕ} (hij : i < j) (hj : j < N) : 1 ≤ f j - f i := by
  have h := bounded_step_sum f N hstep i j (by omega) hj
  have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  linarith

/-- Fine-digit gaps and last-to-first carries order the entire rectangular block.
The carry hypothesis is on the last fine digit, not on equal fine digits. -/
theorem rectangular_lex_gap (F : ℕ → ℕ → ℝ) (M k : ℕ) (hk : 0 < k)
    (hfine : ∀ a, a < M → ∀ b, b + 1 < k → 1 ≤ F a (b + 1) - F a b)
    (hcarry : ∀ a, a + 1 < M → 1 ≤ F (a + 1) 0 - F a (k - 1))
    {a b a' b' : ℕ} (ha : a < M) (hb : b < k) (ha' : a' < M) (hb' : b' < k)
    (hlex : a < a' ∨ (a = a' ∧ b < b')) : 1 ≤ F a' b' - F a b := by
  have hrow (c : ℕ) (hc : c < M) {i j : ℕ} (hij : i ≤ j) (hj : j < k) :
      F c i ≤ F c j := bounded_step_mono (F c) k (hfine c hc) hij hj
  have hfirst : ∀ c, c + 1 < M → 1 ≤ F (c + 1) 0 - F c 0 := by
    intro c hc
    have h1 := hrow c (by omega) (show 0 ≤ k - 1 by omega) (by omega)
    have h2 := hcarry c hc
    linarith
  rcases hlex with haa | ⟨rfl, hbb⟩
  · have h1 := hrow a ha (show b ≤ k - 1 by omega) (by omega)
    have h2 := hcarry a (by omega)
    have h3 := bounded_step_mono (fun c => F c 0) M hfirst
      (show a + 1 ≤ a' by omega) ha'
    have h4 := hrow a' ha' (show 0 ≤ b' by omega) hb'
    linarith
  · exact bounded_step_gap (F a) k (hfine a ha) hbb hb'

/-- All distinct cells, not just adjacent cells, are separated. -/
theorem rectangular_all_pairs_separated (F : ℕ → ℕ → ℝ) (M k : ℕ) (hk : 0 < k)
    (hfine : ∀ a, a < M → ∀ b, b + 1 < k → 1 ≤ F a (b + 1) - F a b)
    (hcarry : ∀ a, a + 1 < M → 1 ≤ F (a + 1) 0 - F a (k - 1))
    {a b a' b' : ℕ} (ha : a < M) (hb : b < k) (ha' : a' < M) (hb' : b' < k)
    (hne : (a,b) ≠ (a',b')) : 1 ≤ |F a b - F a' b'| := by
  by_cases hlex : a < a' ∨ (a = a' ∧ b < b')
  · have h := rectangular_lex_gap F M k hk hfine hcarry ha hb ha' hb' hlex
    have habs := le_abs_self (F a' b' - F a b)
    rw [abs_sub_comm] at habs
    linarith
  · have hrev : a' < a ∨ (a' = a ∧ b' < b) := by
      have hn : a ≠ a' ∨ b ≠ b' := by
        by_contra h
        push Not at h
        exact hne (by rcases h with ⟨rfl,rfl⟩; rfl)
      omega
    have h := rectangular_lex_gap F M k hk hfine hcarry ha' hb' ha hb hrev
    exact h.trans (le_abs_self _)

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CrossScalar.lean
section

/-! The exact square-root metric used by the fifth-pass orthogonal circles.
All slope estimates below are algebraic secant estimates; no differentiability
or approximation error is assumed. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5Phi (ν T : ℝ) : ℝ := Real.sqrt (ν^2 + 2*ν*T)

/-- The digit budget implies strict positivity of the exact radicand. -/
theorem pass5Phi_radicand_pos (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    0 < ν^2 + 2*ν*T := by
  have hlow := (abs_le.mp hT).1
  have hb := mul_le_mul_of_nonneg_left hbudget hν.le
  have ht := mul_le_mul_of_nonneg_left hlow hν.le
  have hp : 0 < (τ*ν)^2 := sq_pos_of_pos (mul_pos hτ hν)
  nlinarith

/-- The exact metric has the square prescribed by the geometry. -/
theorem pass5Phi_sq (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    (pass5Phi ν T)^2 = ν^2 + 2*ν*T := by
  exact Real.sq_sqrt (pass5Phi_radicand_pos ν τ H T hν hτ hT hbudget).le

/-- The root lies between τν and ν/τ, with the upper bound denominator-cleared. -/
theorem pass5Phi_range (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    τ*ν ≤ pass5Phi ν T ∧ τ*pass5Phi ν T ≤ ν := by
  have hsq := pass5Phi_sq ν τ H T hν hτ hT hbudget
  have hnonneg : 0 ≤ pass5Phi ν T := Real.sqrt_nonneg _
  have hlo := (abs_le.mp hT).1
  have hhi := (abs_le.mp hT).2
  have hb := mul_le_mul_of_nonneg_left hbudget hν.le
  have hl := mul_le_mul_of_nonneg_left hlo hν.le
  have hu := mul_le_mul_of_nonneg_left hhi hν.le
  have hrootlo : (τ*ν)^2 ≤ (pass5Phi ν T)^2 := by nlinarith
  have hrootup : (pass5Phi ν T)^2 ≤ (2-τ^2)*ν^2 := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hrootup (sq_nonneg τ)
  have hrem : 0 ≤ ((1-τ^2)*ν)^2 := sq_nonneg _
  constructor
  · nlinarith [mul_pos hτ hν]
  · have hs : (τ*pass5Phi ν T)^2 ≤ ν^2 := by nlinarith only [ht, hrem]
    nlinarith [mul_nonneg hτ.le hnonneg]

/-- Uniform lower and upper secant slopes on the entire digit interval. -/
theorem pass5Phi_secant (ν τ H u v : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hu : |u| ≤ H) (hv : |v| ≤ H)
    (hbudget : 2*H ≤ (1-τ^2)*ν) (huv : u ≤ v) :
    τ*(v-u) ≤ pass5Phi ν v-pass5Phi ν u ∧
      pass5Phi ν v-pass5Phi ν u ≤ (v-u)/τ := by
  have huSq := pass5Phi_sq ν τ H u hν hτ hu hbudget
  have hvSq := pass5Phi_sq ν τ H v hν hτ hv hbudget
  obtain ⟨huLo, huHi⟩ := pass5Phi_range ν τ H u hν hτ hτ1 hu hbudget
  obtain ⟨hvLo, hvHi⟩ := pass5Phi_range ν τ H v hν hτ hτ1 hv hbudget
  have hp : 0 < τ*ν := mul_pos hτ hν
  have hmono : pass5Phi ν u ≤ pass5Phi ν v := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hid : (pass5Phi ν v-pass5Phi ν u)*(pass5Phi ν v+pass5Phi ν u) =
      2*ν*(v-u) := by nlinarith only [huSq, hvSq]
  have hsum : 0 < pass5Phi ν v+pass5Phi ν u := by linarith
  constructor
  · apply (mul_le_mul_iff_of_pos_right hsum).mp
    have hb := mul_le_mul_of_nonneg_right (show
      τ*(pass5Phi ν v+pass5Phi ν u) ≤ 2*ν by linarith) (sub_nonneg.mpr huv)
    nlinarith only [hb, hid]
  · apply (le_div_iff₀ hτ).mpr
    have hb := mul_le_mul_of_nonneg_right (show
      2*τ*ν ≤ pass5Phi ν v+pass5Phi ν u by linarith) (sub_nonneg.mpr hmono)
    have hm : (2*ν)*((pass5Phi ν v-pass5Phi ν u)*τ) ≤ (2*ν)*(v-u) := by
      nlinarith only [hb, hid]
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 2*ν)).mp hm

@[simp] theorem pass5Phi_zero (ν : ℝ) (hν : 0 ≤ ν) : pass5Phi ν 0 = ν := by
  simp [pass5Phi, Real.sqrt_sq_eq_abs, abs_of_nonneg hν]

/-- The exact baseline-displacement bound, uniform in all digit values. -/
theorem pass5Phi_displacement (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    |pass5Phi ν T-ν| ≤ H/τ := by
  have hH : 0 ≤ H := (abs_nonneg T).trans hT
  have hz : |(0 : ℝ)| ≤ H := by simpa using hH
  by_cases ht : 0 ≤ T
  · have hs := (pass5Phi_secant ν τ H 0 T hν hτ hτ1 hz hT hbudget ht).2
    rw [pass5Phi_zero ν hν.le] at hs
    have hmono : ν ≤ pass5Phi ν T := by
      have hl := (pass5Phi_secant ν τ H 0 T hν hτ hτ1 hz hT hbudget ht).1
      rw [pass5Phi_zero ν hν.le] at hl
      nlinarith [mul_nonneg hτ.le ht]
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    have hTH := (abs_le.mp hT).2
    exact hs.trans (div_le_div_of_nonneg_right (by linarith : T-0 ≤ H) hτ.le)
  · have hs := (pass5Phi_secant ν τ H T 0 hν hτ hτ1 hT hz hbudget (by linarith)).2
    rw [pass5Phi_zero ν hν.le] at hs
    have hmono : pass5Phi ν T ≤ ν := by
      have hl := (pass5Phi_secant ν τ H T 0 hν hτ hτ1 hT hz hbudget (by linarith)).1
      rw [pass5Phi_zero ν hν.le] at hl
      nlinarith [mul_nonneg hτ.le (show 0 ≤ -T by linarith)]
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    have hTH := (abs_le.mp hT).1
    have hd := div_le_div_of_nonneg_right (show 0-T ≤ H by linarith) hτ.le
    linarith



end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From PointFamily.lean
section

namespace Erdos670R29
open scoped Matrix BigOperators
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def angleZ (k i : ℕ) : ℝ := (519/1000)/(k : ℝ)*((i : ℝ)-((k : ℝ)-1)/2)
noncomputable def angleW (p k A i : ℕ) : ℝ :=
  (879/500)/(k : ℝ)*(pass5Ruler 2 p k A i : ℝ)/(2*(p : ℝ))
noncomputable def digit (k i : ℕ) : ℝ := (k : ℝ)/(519/1000)*Real.sin (angleZ k i)
noncomputable def crossLength (k : ℕ) (A B : Fin 6) (i j : ℕ) : ℝ :=
  pass5Phi ((k : ℝ)^2*sourceD A B) ((138/125)*(k : ℝ)*digit k i+(533/500)*digit k j)

noncomputable def pointFamily {k : ℕ} (p : ℕ)
    (Q : Matrix (Fin 5) (Fin 5) ℝ) (U : Matrix (Fin 5) (Fin 6) ℝ)
    (W : Matrix (Fin 6) (Fin 6) ℝ) (A : Fin 6) (i : Fin k) :
    EuclideanSpace ℝ (TwoCircleCoordinate (Fin 5) (Fin 6)) :=
  twoCirclePoint (anchor Q) U W ((k : ℝ)^2) ((507/100)*(k : ℝ)^2)
    ((1131/100)*(k : ℝ)^2) A (angleZ k i.val) (angleW p k A.val i.val)

lemma angleZ_difference (k i j : ℕ) (hij : i ≤ j) :
    angleZ k j-angleZ k i = (519/1000)/(k : ℝ)*(j-i : ℕ) := by
  simp only [angleZ, Nat.cast_sub hij]
  ring
lemma angleW_difference (p k A i j : ℕ) (hij : i ≤ j) :
    angleW p k A j-angleW p k A i =
      (879/500)/(k : ℝ)*(pass5RulerGap 2 p k A i (j-i) : ℝ)/(2*(p : ℝ)) := by
  have he : i+(j-i)=j := Nat.add_sub_of_le hij
  simp only [angleW, pass5RulerGap, he, Int.cast_sub]
  ring

theorem pointFamily_local {k : ℕ} (p : ℕ)
    (Q : Matrix (Fin 5) (Fin 5) ℝ) (U : Matrix (Fin 5) (Fin 6) ℝ)
    (W : Matrix (Fin 6) (Fin 6) ℝ)
    (hfactor : Uᵀ*U+Wᵀ*W = diagonal (fun _ => ((507/100 : ℝ)*(k : ℝ)^2)^2))
    (A : Fin 6) (i j : Fin k) (hij : i < j) :
    dist (pointFamily p Q U W A i) (pointFamily p Q U W A j) =
      localEdge p k A.val i.val j.val := by
  have hs := twoCircle_same_square (anchor Q) U W ((k : ℝ)^2)
    ((507/100)*(k : ℝ)^2) ((1131/100)*(k : ℝ)^2) hfactor A
    (angleZ k j.val) (angleZ k i.val) (angleW p k A.val j.val) (angleW p k A.val i.val)
  rw [angleZ_difference k i.val j.val hij.le, angleW_difference p k A.val i.val j.val hij.le] at hs
  have he : ((879/500)/(k : ℝ)*(pass5RulerGap 2 p k A.val i.val (j.val-i.val) : ℝ)/(2*p))/2 =
      ((879/500)/(k : ℝ))*(pass5RulerGap 2 p k A.val i.val (j.val-i.val) : ℝ)/(2*(2*p)) := by ring
  rw [he] at hs
  have hs' : dist (pointFamily p Q U W A j) (pointFamily p Q U W A i)^2 =
      (localH k ((j.val-i.val : ℕ) : ℝ))^2+(localB k p (pass5RulerGap 2 p k A.val i.val (j.val-i.val)))^2 := by
    simpa only [pointFamily, localH, localB, pass5Chord, mul_one] using hs
  unfold localEdge localLength
  rw [← hs', Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg, dist_comm]

theorem pointFamily_cross {k : ℕ} (p : ℕ)
    (Q : Matrix (Fin 5) (Fin 5) ℝ) (U : Matrix (Fin 5) (Fin 6) ℝ)
    (W : Matrix (Fin 6) (Fin 6) ℝ)
    (hQ : Qᵀ*Q = sourceMacro)
    (hp : Qᵀ*U = ((k : ℝ)/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (hfactor : Uᵀ*U+Wᵀ*W = diagonal (fun _ => ((507/100 : ℝ)*(k : ℝ)^2)^2))
    (A B : Fin 6) (hAB : A < B) (i j : Fin k) :
    dist (pointFamily p Q U W A i) (pointFamily p Q U W B j) = crossLength k A B i.val j.val := by
  have hs := actual_cross_square Q U W k hQ hp hfactor A B hAB
    (angleZ k i.val) (angleZ k j.val) (angleW p k A.val i.val) (angleW p k B.val j.val)
  have hs' : dist (pointFamily p Q U W A i) (pointFamily p Q U W B j)^2 =
      ((k : ℝ)^2*sourceD A B)^2+2*((k : ℝ)^2*sourceD A B)*
        ((138/125)*(k : ℝ)*digit k i.val+(533/500)*digit k j.val) := by
    simpa only [pointFamily, digit, mul_assoc] using hs
  unfold crossLength pass5Phi
  rw [← hs', Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]



end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CrossSeparation.lean
section

/-! Exhaustive cross-edge separation for the exact orthogonal-circle metric.
The digit arrays may vary with the cluster. The macro-edge labels only enter
through their baseline separation, so any proved injective colex code applies. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Distinct macro baselines remain separate after the two exact displacements. -/
theorem pass5_different_macro_separated (ν μ τ H T U S : ℝ)
    (hν : 0 < ν) (hμ : 0 < μ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hT : |T| ≤ H) (hU : |U| ≤ H)
    (hbν : 2*H ≤ (1-τ^2)*ν) (hbμ : 2*H ≤ (1-τ^2)*μ)
    (hbase : S ≤ |ν-μ|) (hguard : 1 ≤ S-2*H/τ) :
    1 ≤ |pass5Phi ν T-pass5Phi μ U| := by
  have hdν := pass5Phi_displacement ν τ H T hν hτ hτ1 hT hbν
  have hdμ := pass5Phi_displacement μ τ H U hμ hτ hτ1 hU hbμ
  have htri₀ := abs_sub_le ν (pass5Phi ν T) μ
  have htri₁ := abs_sub_le (pass5Phi ν T) (pass5Phi μ U) μ
  rw [abs_sub_comm ν (pass5Phi ν T)] at htri₀
  have hid : 2*H/τ = 2*(H/τ) := by ring
  linarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From CrossGeneric.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def crossDigit (sig eta : ℝ) (k : ℕ) (f g : ℕ → ℝ) (i j : ℕ) : ℝ :=
  sig*(k : ℝ)*f i + eta*g j

noncomputable def digitBudget (sig eta h : ℝ) (k : ℕ) : ℝ := (sig*(k : ℝ)+eta)*h

/-- The full two-digit perturbation is bounded by the manuscript's exact budget. -/
theorem crossDigit_bound (sig eta h : ℝ) (k : ℕ) (f g : ℕ → ℝ) (i j : ℕ)
    (hsig : 0 ≤ sig) (hs : 0 ≤ eta) (hf : |f i| ≤ h) (hg : |g j| ≤ h) :
    |crossDigit sig eta k f g i j| ≤ digitBudget sig eta h k := by
  obtain ⟨hfl,hfu⟩ := abs_le.mp hf
  obtain ⟨hgl,hgu⟩ := abs_le.mp hg
  have hc : 0 ≤ sig*(k : ℝ) := by positivity
  have h₀ := mul_le_mul_of_nonneg_left hfl hc
  have h₁ := mul_le_mul_of_nonneg_left hfu hc
  have h₂ := mul_le_mul_of_nonneg_left hgl hs
  have h₃ := mul_le_mul_of_nonneg_left hgu hs
  unfold crossDigit digitBudget
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Fine and carry steps separate all distinct digit pairs on one macro edge. -/
theorem one_macro_separated (sig eta τ h lam ν : ℝ) (k : ℕ)
    (f g : ℕ → ℝ) (hk : 0 < k) (hsig : 0 < sig) (hs : 0 < eta) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hlam : 0 ≤ lam) (hν : 0 < ν)
    (hf : ∀ i, i < k → |f i| ≤ h) (hg : ∀ j, j < k → |g j| ≤ h)
    (hfstep : ∀ i, i+1 < k → lam ≤ f (i+1)-f i)
    (hgstep : ∀ j, j+1 < k → lam ≤ g (j+1)-g j)
    (hbudget : 2*digitBudget sig eta h k ≤ (1-τ^2)*ν)
    (hfine : 1 ≤ τ*eta*lam) (hcarry : 1 ≤ τ*(sig*(k : ℝ)*lam-2*eta*h))
    {i j u v : ℕ} (hi : i < k) (hj : j < k) (hu : u < k) (hv : v < k)
    (hne : (i,j) ≠ (u,v)) :
    1 ≤ |pass5Phi ν (crossDigit sig eta k f g i j) -
      pass5Phi ν (crossDigit sig eta k f g u v)| := by
  let D : ℕ → ℕ → ℝ := fun a b => pass5Phi ν (crossDigit sig eta k f g a b)
  have hbound (a b : ℕ) (ha : a < k) (hb : b < k) :=
    crossDigit_bound sig eta h k f g a b hsig.le hs.le (hf a ha) (hg b hb)
  have hFine : ∀ a, a < k → ∀ b, b+1 < k → 1 ≤ D a (b+1)-D a b := by
    intro a ha b hb
    have hb0 : b < k := by omega
    have hd := mul_le_mul_of_nonneg_left (hgstep b hb) hs.le
    have ht : eta*lam ≤ crossDigit sig eta k f g a (b+1)-crossDigit sig eta k f g a b := by
      unfold crossDigit
      nlinarith only [hd]
    have hmono : crossDigit sig eta k f g a b ≤ crossDigit sig eta k f g a (b+1) := by
      nlinarith [mul_nonneg hs.le hlam]
    have hslope := (pass5Phi_secant ν τ (digitBudget sig eta h k)
      (crossDigit sig eta k f g a b) (crossDigit sig eta k f g a (b+1))
      hν hτ hτ1 (hbound a b ha hb0) (hbound a (b+1) ha hb) hbudget hmono).1
    have hmul := mul_le_mul_of_nonneg_left ht hτ.le
    dsimp [D]
    nlinarith only [hslope, hmul, hfine]
  have hCarry : ∀ a, a+1 < k → 1 ≤ D (a+1) 0-D a (k-1) := by
    intro a ha
    have ha0 : a < k := by omega
    have hlast : k-1 < k := by omega
    have hc : 0 ≤ sig*(k : ℝ) := by positivity
    have hfGap := mul_le_mul_of_nonneg_left (hfstep a ha) hc
    have hgLo := mul_le_mul_of_nonneg_left (abs_le.mp (hg 0 hk)).1 hs.le
    have hgHi := mul_le_mul_of_nonneg_left (abs_le.mp (hg (k-1) hlast)).2 hs.le
    have ht : sig*(k : ℝ)*lam-2*eta*h ≤
        crossDigit sig eta k f g (a+1) 0-crossDigit sig eta k f g a (k-1) := by
      unfold crossDigit
      nlinarith only [hfGap, hgLo, hgHi]
    have hguardpos : 0 < sig*(k : ℝ)*lam-2*eta*h := by nlinarith
    have hmono : crossDigit sig eta k f g a (k-1) ≤ crossDigit sig eta k f g (a+1) 0 := by
      linarith
    have hslope := (pass5Phi_secant ν τ (digitBudget sig eta h k)
      (crossDigit sig eta k f g a (k-1)) (crossDigit sig eta k f g (a+1) 0)
      hν hτ hτ1 (hbound a (k-1) ha0 hlast) (hbound (a+1) 0 ha hk) hbudget hmono).1
    have hmul := mul_le_mul_of_nonneg_left ht hτ.le
    dsimp [D]
    nlinarith only [hslope, hmul, hcarry]
  exact rectangular_all_pairs_separated D k k hk hFine hCarry hi hj hu hv hne



end Erdos670R29

end

-- From CrossDigits.lean
section

namespace Erdos670R29

open Erdos488.Geometry.SeparatedDistances.FixedDimension

set_option maxHeartbeats 1500000 in
lemma digit_eq_sineDigit (k i : ℕ) :
    digit k i = sineDigit ((519/1000)/(k : ℝ)) (((k : ℝ)-1)/2) i := by
  unfold digit angleZ sineDigit
  simp [div_eq_mul_inv, mul_comm]

set_option maxHeartbeats 1500000 in
lemma digit_bound (k i : ℕ) (hk : 0 < k) (hi : i < k) :
    |digit k i| ≤ ((k : ℝ)-1)/2 := by
  rw [digit_eq_sineDigit]
  exact finite_sineDigit_bound _ k i (by positivity) hi

set_option maxHeartbeats 1500000 in
lemma digit_step (k i : ℕ) (hk : 0 < k) (hi : i+1 < k) :
    (1-(519/1000 : ℝ)^2/8) ≤ digit k (i+1)-digit k i := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hscale : ((519/1000)/(k : ℝ))^2*(k : ℝ)^2 ≤ (519/1000 : ℝ)^2 := by
    field_simp <;> norm_num
  have h := finite_sineDigit_step ((519/1000)/(k : ℝ)) ((519/1000 : ℝ)^2) k i
    (by positivity) hi hscale
  simpa only [digit_eq_sineDigit, Nat.cast_add, Nat.cast_one] using h

set_option maxHeartbeats 1500000 in
lemma concrete_digit_budget (k : ℕ) (hk : 100 ≤ k) (D : ℝ) (hD : 9709/500 ≤ D) :
    2*digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k ≤
      (1-(971/1000 : ℝ)^2)*((k : ℝ)^2*D) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_left hD (sq_nonneg (k : ℝ))
  unfold digitBudget
  nlinarith [sq_nonneg (k : ℝ)]

set_option maxHeartbeats 1500000 in
lemma concrete_fine : (1 : ℝ) ≤ (971/1000)*(533/500)*(1-(519/1000)^2/8) := by norm_num
set_option maxHeartbeats 1500000 in
lemma concrete_carry (k : ℕ) (hk : 100 ≤ k) :
    (1 : ℝ) ≤ (971/1000)*((138/125)*(k : ℝ)*(1-(519/1000)^2/8)-
      2*(533/500)*(((k : ℝ)-1)/2)) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith
set_option maxHeartbeats 1500000 in
lemma concrete_macro_gap (k : ℕ) (hk : 100 ≤ k) :
    (1 : ℝ) ≤ (569/500)*(k : ℝ)^2-
      2*digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k/(971/1000) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  unfold digitBudget
  nlinarith [sq_nonneg (k : ℝ)]




end Erdos670R29

end

-- From MacroLabels.lean
section

namespace Erdos670R29

set_option maxHeartbeats 3000000 in
lemma sourceD_bounds (A B : Fin 6) (hAB : A < B) :
    (9709/500 : ℝ) ≤ sourceD A B ∧ sourceD A B ≤ (707/20 : ℝ) := by
  fin_cases A <;> fin_cases B <;> norm_num [sourceD,labels] at *

set_option maxHeartbeats 3000000 in
lemma sourceD_spacing (A B C D : Fin 6) (hAB : A < B) (hCD : C < D)
    (hne : (A,B) ≠ (C,D)) : (569/500 : ℝ) ≤ |sourceD A B-sourceD C D| := by
  fin_cases A <;> fin_cases B <;> norm_num at hAB
  all_goals fin_cases C <;> fin_cases D <;> norm_num at hCD
  all_goals norm_num [sourceD,labels] at *



end Erdos670R29

end

-- From CrossSpectrum.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma cross_digit_bound (k i j : ℕ) (hk : 0 < k) (hi : i < k) (hj : j < k) :
    |(138/125)*(k : ℝ)*digit k i+(533/500)*digit k j| ≤
      digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k :=
  crossDigit_bound _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (digit_bound k i hk hi) (digit_bound k j hk hj)

lemma baseline_pos (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B) :
    0 < (k : ℝ)^2*sourceD A B := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD := (sourceD_bounds A B hAB).1
  positivity

lemma cross_lower (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B)
    (i j : ℕ) (hi : i < k) (hj : j < k) :
    (37/2 : ℝ)*(k : ℝ)^2 ≤ crossLength k A B i j := by
  have hD := (sourceD_bounds A B hAB).1
  have h := (pass5Phi_range ((k : ℝ)^2*sourceD A B) (971/1000)
    (digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k)
    ((138/125)*(k : ℝ)*digit k i+(533/500)*digit k j)
    (baseline_pos k hk A B hAB) (by norm_num) (by norm_num)
    (cross_digit_bound k i j (by omega) hi hj) (concrete_digit_budget k hk _ hD)).1
  have hm := mul_le_mul_of_nonneg_left hD (sq_nonneg (k : ℝ))
  dsimp [crossLength]
  nlinarith

lemma cross_displacement (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B)
    (i j : ℕ) (hi : i < k) (hj : j < k) :
    |crossLength k A B i j-(k : ℝ)^2*sourceD A B| ≤
      digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k/(971/1000) :=
  pass5Phi_displacement _ _ _ _ (baseline_pos k hk A B hAB) (by norm_num) (by norm_num)
    (cross_digit_bound k i j (by omega) hi hj)
    (concrete_digit_budget k hk _ (sourceD_bounds A B hAB).1)

lemma cross_upper (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B)
    (i j : ℕ) (hi : i < k) (hj : j < k) :
    crossLength k A B i j < (499/500 : ℝ)*(6*(k : ℝ))^2 := by
  have h := (abs_le.mp (cross_displacement k hk A B hAB i j hi hj)).2
  have hD := (sourceD_bounds A B hAB).2
  have hm := mul_le_mul_of_nonneg_left hD (sq_nonneg (k : ℝ))
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  unfold digitBudget at h
  nlinarith [sq_nonneg (k : ℝ)]

theorem cross_edges_separated (k : ℕ) (hk : 100 ≤ k)
    (A B C D : Fin 6) (hAB : A < B) (hCD : C < D)
    (i j u v : Fin k) (hne : (A,B,i,j) ≠ (C,D,u,v)) :
    1 ≤ |crossLength k A B i.val j.val-crossLength k C D u.val v.val| := by
  by_cases hmacro : (A,B)=(C,D)
  · have hA : A=C := congrArg Prod.fst hmacro
    have hB : B=D := congrArg Prod.snd hmacro
    subst C
    subst D
    have hpair : (i.val,j.val) ≠ (u.val,v.val) := by
      intro he
      have hi : i=u := Fin.ext (congrArg Prod.fst he)
      have hj : j=v := Fin.ext (congrArg Prod.snd he)
      exact hne (by subst u; subst v; rfl)
    exact one_macro_separated (138/125) (533/500) (971/1000) (((k : ℝ)-1)/2)
      (1-(519/1000)^2/8) ((k : ℝ)^2*sourceD A B) k (digit k) (digit k)
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (baseline_pos k hk A B hAB) (fun i hi => digit_bound k i (by omega) hi)
      (fun i hi => digit_bound k i (by omega) hi)
      (fun i hi => digit_step k i (by omega) hi) (fun i hi => digit_step k i (by omega) hi)
      (concrete_digit_budget k hk _ (sourceD_bounds A B hAB).1)
      concrete_fine (concrete_carry k hk) i.isLt j.isLt u.isLt v.isLt hpair
  · apply pass5_different_macro_separated ((k : ℝ)^2*sourceD A B)
      ((k : ℝ)^2*sourceD C D) (971/1000)
      (digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k) _ _ ((569/500)*(k : ℝ)^2)
      (baseline_pos k hk A B hAB) (baseline_pos k hk C D hCD)
      (by norm_num) (by norm_num)
      (cross_digit_bound k i.val j.val (by omega) i.isLt j.isLt)
      (cross_digit_bound k u.val v.val (by omega) u.isLt v.isLt)
      (concrete_digit_budget k hk _ (sourceD_bounds A B hAB).1)
      (concrete_digit_budget k hk _ (sourceD_bounds C D hCD).1) ?_ (concrete_macro_gap k hk)
    have h := mul_le_mul_of_nonneg_left (sourceD_spacing A B C D hAB hCD hmacro)
      (sq_nonneg (k : ℝ))
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg (k : ℝ))]
    nlinarith only [h]




end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.UnorderedEdgeSeparation.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The independently proved minimum distance implies injectivity. -/
theorem injective_of_unit_minimum_distance
    {ι E : Type*} [PseudoMetricSpace E] (p : ι → E)
    (hmin : ∀ i j, i ≠ j → 1 ≤ dist (p i) (p j)) : Function.Injective p := by
  intro i j heq
  by_contra hne
  have h := hmin i j hne
  rw [heq,dist_self] at h
  norm_num at h

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.ClusterEdgeAssembly.lean
section

/-! Exhaustive genuinely unordered cluster-edge classification and assembly.
Local separation, canonical cross separation and mixed band isolation are
explicit inputs; this module constructs no Gram matrix or scalar certificate. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Each non-diagonal edge is either local with increasing local endpoints,
or cross-cluster with increasing macro endpoints. -/
theorem cluster_edge_cases {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : Edge (α × β)) :
    (∃ A i j, i < j ∧ e.val=s((A,i),(A,j))) ∨
      (∃ A B i j, A < B ∧ e.val=s((A,i),(B,j))) := by
  obtain ⟨e,he⟩ := e
  induction e using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨A,i⟩ := x
    obtain ⟨B,j⟩ := y
    by_cases hAB : A=B
    · subst B
      have hij : i ≠ j := by
        intro h
        subst j
        exact he (Sym2.mk_isDiag_iff.mpr rfl)
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Or.inl ⟨A,i,j,hij,rfl⟩
      · exact Or.inl ⟨A,j,i,hji,Sym2.eq_swap⟩
    · rcases lt_or_gt_of_ne hAB with hAB | hBA
      · exact Or.inr ⟨A,B,i,j,hAB,rfl⟩
      · exact Or.inr ⟨B,A,j,i,hBA,Sym2.eq_swap⟩

/-- All four combinations of unordered edge classes are checked. -/
theorem separatedConfiguration_of_cluster_gaps
    {α β E : Type*} [LinearOrder α] [LinearOrder β] [PseudoMetricSpace E]
    (p : α × β → E)
    (hlocal : ∀ A i j B u v, i < j → u < v → (A,i,j) ≠ (B,u,v) →
      1 ≤ |dist (p (A,i)) (p (A,j))-dist (p (B,u)) (p (B,v))|)
    (hcross : ∀ A B i j C D u v, A < B → C < D → (A,B,i,j) ≠ (C,D,u,v) →
      1 ≤ |dist (p (A,i)) (p (B,j))-dist (p (C,u)) (p (D,v))|)
    (hmixed : ∀ A i j B C u v, i < j → B < C →
      1 ≤ dist (p (B,u)) (p (C,v))-dist (p (A,i)) (p (A,j))) :
    SeparatedConfiguration p := by
  intro e f hef
  have hval : e.val ≠ f.val := fun h => hef (Subtype.ext h)
  rcases cluster_edge_cases e with ⟨A,i,j,hij,he⟩ | ⟨A,B,i,j,hAB,he⟩
  · rcases cluster_edge_cases f with ⟨B,u,v,huv,hf⟩ | ⟨B,C,u,v,hBC,hf⟩
    · have hne : (A,i,j) ≠ (B,u,v) := by
        intro h
        have hA : A=B := congrArg Prod.fst h
        have hi : i=u := congrArg (fun q => q.2.1) h
        have hj : j=v := congrArg (fun q => q.2.2) h
        apply hval
        simpa only [he,hf,hA,hi,hj]
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using hlocal A i j B u v hij huv hne
    · have h := (hmixed A i j B C u v hij hBC).trans
        (le_abs_self (dist (p (B,u)) (p (C,v))-dist (p (A,i)) (p (A,j))))
      rw [abs_sub_comm] at h
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using h
  · rcases cluster_edge_cases f with ⟨C,u,v,huv,hf⟩ | ⟨C,D,u,v,hCD,hf⟩
    · have h := (hmixed C u v A B i j huv hAB).trans (le_abs_self _)
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using h
    · have hne : (A,B,i,j) ≠ (C,D,u,v) := by
        intro h
        have hA : A=C := congrArg Prod.fst h
        have hB : B=D := congrArg (fun q => q.2.1) h
        have hi : i=u := congrArg (fun q => q.2.2.1) h
        have hj : j=v := congrArg (fun q => q.2.2.2) h
        apply hval
        simpa only [he,hf,hA,hB,hi,hj]
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using hcross A B i j C D u v hAB hCD hne

/-- The two nonzero-distance classes must each clear zero independently. -/
theorem cluster_minimum_distance
    {α β E : Type*} [LinearOrder α] [LinearOrder β] [PseudoMetricSpace E]
    (p : α × β → E)
    (hlocal : ∀ A i j, i < j → 1 ≤ dist (p (A,i)) (p (A,j)))
    (hcross : ∀ A B i j, A < B → 1 ≤ dist (p (A,i)) (p (B,j))) :
    ∀ x y, x ≠ y → 1 ≤ dist (p x) (p y) := by
  rintro ⟨A,i⟩ ⟨B,j⟩ hxy
  by_cases hAB : A=B
  · subst B
    have hij : i ≠ j := by intro h; subst j; exact hxy rfl
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlocal A i j h
    · simpa only [dist_comm] using hlocal A j i h
  · rcases lt_or_gt_of_ne hAB with h | h
    · exact hcross A B i j h
    · simpa only [dist_comm] using hcross B A j i h

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.AllNArithmetic.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.DirectCrossSpectrum.lean
section

/-! Derivative-free cross-spectrum ordering, adopting JRL PR 3002.
No adjacent quotient-error Lipschitz estimate or physical local-step H is used.
All geometric inputs are visible as scalar square identities and pointwise errors. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceCrossGuards.lean
section

/-! Universal source-parameter cross guards, not finite sampled certificates.
The hypotheses are k≥2 and K≥72247875/4, with the literal source formulas. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceCrossSpectrum.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.PrimeRulerSeparation.lean
section

/-! Exact integer-ruler layer. Unlike a residue-only statement, these theorems
refer to the actual differences of the explicit ruler positions. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.LocalRulerSeparation.lean
section

/-! All local ruler-distance models, across every cluster and lag, are separated.
Only explicit scalar guards remain; no local-separation hypothesis is assumed. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceLocalGuards.lean
section

/-! Coarse rational guards sufficient for all source local distances.
The budget600 deliberately leaves slack above the source's J² envelope. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceLocalSpectrum.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceMixedBands.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceReserveBudgets.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceFinalScalar.lean
section

/-! Scalar diameter estimates for the literal fixed-dimensional source construction. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceAllNEmbedding.lean
section

/-! Distance-preserving deletion and coordinate padding for the all-size step. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

open Erdos488.Geometry.SeparatedDistances

/-- A family restricted along an injection retains its unit minimum. -/
theorem source_minimum_restrict {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (hf : Function.Injective f)
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) :
    ∀ a b, a ≠ b → 1 ≤ dist (P (f a)) (P (f b)) := by
  intro a b hab
  exact hmin _ _ (hf.ne hab)

/-- The induced map on non-diagonal unordered edges. -/
def sourceEdgeMap {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f) :
    Edge ι → Edge κ := fun e =>
  ⟨Sym2.map f e.1, (Sym2.isDiag_map hf).not.mpr e.2⟩

theorem sourceEdgeMap_injective {ι κ : Type*} (f : ι → κ)
    (hf : Function.Injective f) : Function.Injective (sourceEdgeMap f hf) := by
  intro e₁ e₂ h
  apply Subtype.ext
  exact (Sym2.map.injective hf) (congrArg Subtype.val h)

private theorem source_edgeDistance_map {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (e : Sym2 ι) :
    edgeDistance (P ∘ f) e = edgeDistance P (Sym2.map f e) := by
  induction e using Sym2.inductionOn with
  | hf a b => rfl

/-- Restricting a family along an injection preserves edge separation. -/
theorem source_separated_restrict {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (hf : Function.Injective f)
    (hsep : SeparatedConfiguration P) : SeparatedConfiguration (P ∘ f) := by
  intro e₁ e₂ hne
  have hne' : sourceEdgeMap f hf e₁ ≠ sourceEdgeMap f hf e₂ :=
    (sourceEdgeMap_injective f hf).ne hne
  convert hsep (sourceEdgeMap f hf e₁) (sourceEdgeMap f hf e₂) hne' using 1 <;>
    simp only [sourceEdgeMap, source_edgeDistance_map]

/-- Extend coordinates by zero along a disjoint sum. -/
noncomputable def sourceSumPad {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (ι ⊕ κ) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun _ => 0))

theorem sourceSumPad_dist {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x y : EuclideanSpace ℝ ι) :
    dist (sourceSumPad (κ := κ) x) (sourceSumPad (κ := κ) y) = dist x y := by
  have hsq : dist (sourceSumPad (κ := κ) x) (sourceSumPad (κ := κ) y)^2 =
      dist x y ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
    simp [sourceSumPad, Fintype.sum_sum_type]
  nlinarith [show 0 ≤ dist (sourceSumPad (κ := κ) x) (sourceSumPad (κ := κ) y) from dist_nonneg,
    show 0 ≤ dist x y from dist_nonneg]

/-- Pad an arbitrary finite Euclidean coordinate type into `Fin D`. -/
noncomputable def sourcePadCoordinates {ι : Type*} [Fintype ι] {D : ℕ}
    (hcard : Fintype.card ι ≤ D) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (Fin D) :=
  let e₁ := Fintype.equivFin ι
  let e₂ : Fin (Fintype.card ι) ⊕ Fin (D - Fintype.card ι) ≃
      Fin (Fintype.card ι + (D - Fintype.card ι)) := finSumFinEquiv
  let e₃ := finCongr (Nat.add_sub_of_le hcard)
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e₃)
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e₂)
      (sourceSumPad (κ := Fin (D - Fintype.card ι))
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e₁) x)))

theorem sourcePadCoordinates_dist {ι : Type*} [Fintype ι] {D : ℕ}
    (hcard : Fintype.card ι ≤ D) (x y : EuclideanSpace ℝ ι) :
    dist (sourcePadCoordinates hcard x) (sourcePadCoordinates hcard y) = dist x y := by
  simp [sourcePadCoordinates, sourceSumPad_dist]

/-- Delete the surplus vertices by taking the first `n` positions of a finite
enumeration of the rectangular cluster grid. -/
noncomputable def sourceDeletionEmbedding {n m k : ℕ} (hsize : n ≤ m*k) :
    Fin n → Fin m × Fin k :=
  (Fintype.equivFinOfCardEq (α := Fin m × Fin k) (by simp)).symm ∘
    Fin.castLE hsize

theorem sourceDeletionEmbedding_injective {n m k : ℕ} (hsize : n ≤ m*k) :
    Function.Injective (sourceDeletionEmbedding hsize) := by
  exact (Fintype.equivFinOfCardEq (α := Fin m × Fin k) (by simp)).symm.injective.comp
    (Fin.castLE_injective hsize)

/-- Isometric coordinate padding preserves minimum, unordered-edge gaps and diameter. -/
theorem source_pad_properties {ι κ : Type*} [Fintype κ] {D : ℕ}
    (hcard : Fintype.card κ ≤ D) (P : ι → EuclideanSpace ℝ κ)
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b))
    (hsep : SeparatedConfiguration P) (B : ℝ)
    (hdiam : ∀ a b, dist (P a) (P b) ≤ B) :
    (∀ a b, a ≠ b → 1 ≤ dist (sourcePadCoordinates hcard (P a))
      (sourcePadCoordinates hcard (P b))) ∧
    SeparatedConfiguration (sourcePadCoordinates hcard ∘ P) ∧
    (∀ a b, dist (sourcePadCoordinates hcard (P a))
      (sourcePadCoordinates hcard (P b)) ≤ B) := by
  constructor
  · intro a b hab
    rw [sourcePadCoordinates_dist]
    exact hmin a b hab
  constructor
  · intro e₁ e₂ hne
    induction e₁ using Subtype.rec with
    | _ s hs =>
      induction e₂ using Subtype.rec with
      | _ t ht =>
        induction s using Sym2.inductionOn with
        | hf a b =>
          induction t using Sym2.inductionOn with
          | hf c d =>
            simpa only [edgeDistance, Sym2.lift_mk, Function.comp_apply,
              sourcePadCoordinates_dist] using hsep ⟨s(a,b),hs⟩ ⟨s(c,d),ht⟩ hne
  · intro a b
    rw [sourcePadCoordinates_dist]
    exact hdiam a b

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Padding.lean
section

/-! All-size rounding, deletion, and dimension padding for the fifth pass.
The final theorem here is deliberately conditional on a finite configuration
source: no geometric existence assertion is hidden in this arithmetic layer. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

open Erdos488.Geometry.SeparatedDistances

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From FiniteAssembly.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances

lemma localEdge_min (p k A i j : ℕ) (hk : 100 ≤ k) (hp : 0 < p)
    (hij : i < j) (hj : j < k) : 1 < localEdge p k A i j := by
  have hd : 0 < j-i := by omega
  have hdi : i+(j-i) < k := by omega
  obtain ⟨hl,hu⟩ := ruler_window_real p k A i (j-i) hp hd hdi
  exact localLength_min k p (j-i : ℕ) _ (by exact_mod_cast hk) (by exact_mod_cast hp)
    (by exact_mod_cast hd) hl hu

lemma localEdge_upper (p k A i j : ℕ) (hk : 100 ≤ k) (hp : 0 < p)
    (hij : i < j) (hj : j < k) : localEdge p k A i j < 18*(k : ℝ)^2 := by
  have hd : 0 < j-i := by omega
  have hdi : i+(j-i) < k := by omega
  obtain ⟨hl,hu⟩ := ruler_window_real p k A i (j-i) hp hd hdi
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  exact localLength_upper k p (j-i : ℕ) _ (by exact_mod_cast (show 0 < k by omega)) hp'
    (by positivity) (by exact_mod_cast (show j-i ≤ k by omega))
    ((by positivity : (0 : ℝ) ≤ (p : ℝ)*(j-i : ℕ)).trans hl) hu

theorem metric_properties {k p : ℕ} {E : Type*} [PseudoMetricSpace E]
    (hk : 100 ≤ k) (hp : p.Prime) (hsize : 6*k < p) (hpup : 100*p ≤ 606*k)
    (P : Fin 6 × Fin k → E)
    (hlocal : ∀ (A : Fin 6) (i j : Fin k), i < j →
      dist (P (A,i)) (P (A,j)) = localEdge p k A.val i.val j.val)
    (hcross : ∀ (A B : Fin 6), A < B → ∀ (i j : Fin k),
      dist (P (A,i)) (P (B,j)) = crossLength k A B i.val j.val) :
    (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧ SeparatedConfiguration P ∧
    (∀ a b, dist (P a) (P b) < (499/500 : ℝ)*(6*(k : ℝ))^2) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hksq : 10000 ≤ (k : ℝ)^2 := by nlinarith
  have localMin (A : Fin 6) (i j : Fin k) (hij : i < j) : 1 ≤ dist (P (A,i)) (P (A,j)) := by
    rw [hlocal A i j hij]
    exact (localEdge_min p k A.val i.val j.val hk hp.pos hij j.isLt).le
  have crossMin (A B : Fin 6) (i j : Fin k) (hAB : A < B) : 1 ≤ dist (P (A,i)) (P (B,j)) := by
    rw [hcross A B hAB i j]
    have h := cross_lower k hk A B hAB i.val j.val i.isLt j.isLt
    nlinarith
  refine ⟨cluster_minimum_distance P localMin crossMin, ?_, ?_⟩
  · apply separatedConfiguration_of_cluster_gaps P
    · intro A i j B u v hij huv hne
      rw [hlocal A i j hij, hlocal B u v huv]
      apply (local_edges_separated p k A.val B.val i.val j.val u.val v.val hp hk hsize hpup
        A.isLt B.isLt hij huv j.isLt v.isLt ?_).le
      rintro ⟨hA,hi,hj⟩
      exact hne (Prod.ext (Fin.ext hA) (Prod.ext (Fin.ext hi) (Fin.ext hj)))
    · intro A B i j C D u v hAB hCD hne
      rw [hcross A B hAB i j, hcross C D hCD u v]
      exact cross_edges_separated k hk A B C D hAB hCD i j u v hne
    · intro A i j B C u v hij hBC
      rw [hlocal A i j hij, hcross B C hBC u v]
      have hl := localEdge_upper p k A.val i.val j.val hk hp.pos hij j.isLt
      have hc := cross_lower k hk B C hBC u.val v.val u.isLt v.isLt
      nlinarith
  · have localDiam (A : Fin 6) (i j : Fin k) (hij : i < j) :
        dist (P (A,i)) (P (A,j)) < (499/500 : ℝ)*(6*(k : ℝ))^2 := by
      rw [hlocal A i j hij]
      have h := localEdge_upper p k A.val i.val j.val hk hp.pos hij j.isLt
      nlinarith
    have crossDiam (A B : Fin 6) (hAB : A < B) (i j : Fin k) :
        dist (P (A,i)) (P (B,j)) < (499/500 : ℝ)*(6*(k : ℝ))^2 := by
      rw [hcross A B hAB i j]
      exact cross_upper k hk A B hAB i.val j.val i.isLt j.isLt
    rintro ⟨A,i⟩ ⟨B,j⟩
    rcases lt_trichotomy A B with hAB | hAB | hBA
    · exact crossDiam A B hAB i j
    · subst B
      rcases lt_trichotomy i j with hij | hij | hji
      · exact localDiam A i j hij
      · subst j
        rw [dist_self]
        positivity
      · rw [dist_comm]; exact localDiam A j i hji
    · rw [dist_comm]; exact crossDiam B A hBA j i


end Erdos670R29

end

-- From PrimeFirst.lean
section

namespace Erdos670R29

/-- Arbitrarily large cluster sizes have an admissible prime, using only Euclid's theorem. -/
theorem admissible_prime_sizes_unbounded (N : ℕ) :
    ∃ k p : ℕ, max 100 N ≤ k ∧ p.Prime ∧ 6*k < p ∧ 100*p ≤ 101*(6*k) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (6*(max 100 N)+1)
  refine ⟨(p-1)/6, p, ?_, hprime, ?_, ?_⟩ <;> omega


end Erdos670R29

end

-- From R29Endpoint.lean
section

namespace Erdos670R29
open scoped Matrix BigOperators
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances

/-- Every admissible prime gives one actual separated configuration in R^29. -/
theorem finite_configuration (k p : ℕ) (hk : 100 ≤ k) (hp : p.Prime)
    (hsize : 6*k < p) (hpup : 100*p ≤ 606*k) :
    ∃ P : Fin (6*k) → EuclideanSpace ℝ (Fin 29),
      Function.Injective P ∧
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧ SeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) < (499/500 : ℝ)*((6*k : ℕ) : ℝ)^2) := by
  obtain ⟨Q,U,W,hQ,hproj,hfactor⟩ := finite_k_completion (k : ℝ) (by exact_mod_cast hk)
  let P₀ : Fin 6 × Fin k → EuclideanSpace ℝ (TwoCircleCoordinate (Fin 5) (Fin 6)) :=
    fun ai => pointFamily p Q U W ai.1 ai.2
  obtain ⟨hmin,hsep,hdiam⟩ := metric_properties hk hp hsize hpup P₀
    (fun A i j hij => pointFamily_local p Q U W hfactor A i j hij)
    (fun A B hAB i j => pointFamily_cross p Q U W hQ hproj hfactor A B hAB i j)
  have hc : Fintype.card (TwoCircleCoordinate (Fin 5) (Fin 6)) ≤ 29 := coordinate_card.le
  let P₁ := sourcePadCoordinates hc ∘ P₀
  obtain ⟨hmin₁,hsep₁,_⟩ := source_pad_properties hc P₀ hmin hsep
    ((499/500 : ℝ)*(6*(k : ℝ))^2) (fun a b => (hdiam a b).le)
  let f : Fin (6*k) → Fin 6 × Fin k := sourceDeletionEmbedding (le_refl (6*k))
  have hf : Function.Injective f := sourceDeletionEmbedding_injective _
  let P := P₁ ∘ f
  have hminP : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b) := source_minimum_restrict P₁ f hf hmin₁
  refine ⟨P,injective_of_unit_minimum_distance P hminP,hminP,
    source_separated_restrict P₁ f hf hsep₁,?_⟩
  intro a b
  dsimp [P,P₁]
  rw [sourcePadCoordinates_dist]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hdiam (f a) (f b)

lemma finite_range_diam_lt {ι E : Type*} [Fintype ι] [Nonempty ι] [PseudoMetricSpace E]
    (P : ι → E) (C : ℝ) (h : ∀ a b, dist (P a) (P b) < C) :
    Metric.diam (Set.range P) < C := by
  let s : Finset (ι × ι) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  let B := s.sup' hs (fun ab => dist (P ab.1) (P ab.2))
  have hB (a b : ι) : dist (P a) (P b) ≤ B :=
    Finset.le_sup' (s := s) (f := fun ab => dist (P ab.1) (P ab.2)) (Finset.mem_univ (a,b))
  have hBpos : 0 ≤ B := by
    let a : ι := Classical.choice inferInstance
    exact (dist_nonneg : 0 ≤ dist (P a) (P a)).trans (hB a a)
  have hBlt : B < C := by
    apply (Finset.sup'_lt_iff (s := s) hs).2
    intro ab _
    exact h ab.1 ab.2
  apply lt_of_le_of_lt ?_ hBlt
  apply Metric.diam_le_of_forall_dist_le hBpos
  intro x hx y hy
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact hB a b

/-- Prime-first endpoint: arbitrarily large finite configurations in the same R^29,
with unit minimum distance, separated unordered-edge lengths and diameter < .998 n². -/
theorem r29_unbounded_counterexamples (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 600 ≤ n ∧
    ∃ P : Fin n → EuclideanSpace ℝ (Fin 29), Function.Injective P ∧
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧ SeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) < (499/500 : ℝ)*(n : ℝ)^2) ∧
      Metric.diam (Set.range P) < (499/500 : ℝ)*(n : ℝ)^2 := by
  obtain ⟨k,p,hk,hp,hsize,hpup⟩ := admissible_prime_sizes_unbounded N
  have hk100 : 100 ≤ k := (le_max_left 100 N).trans hk
  have hkN : N ≤ k := (le_max_right 100 N).trans hk
  obtain ⟨P,hinj,hmin,hsep,hdiam⟩ := finite_configuration k p hk100 hp hsize (by omega)
  haveI : Nonempty (Fin (6*k)) := ⟨⟨0,by omega⟩⟩
  exact ⟨6*k,by omega,by omega,P,hinj,hmin,hsep,hdiam,finite_range_diam_lt P _ hdiam⟩



end Erdos670R29

end

-- From Solution.lean
section

/-!
Proofs of the two `Challenge` statements from the dimension-29 endpoint
`Erdos670R29.r29_unbounded_counterexamples`.
-/


open Filter Erdos488.Geometry.SeparatedDistances

namespace Erdos670

theorem r29_sets_600 (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 600 ≤ n ∧
    ∃ A : Finset (EuclideanSpace ℝ (Fin 29)), A.card = n ∧
      Erdos670.HasSeparatedDistances A ∧
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 29))) < (499/500 : ℝ) * (n : ℝ)^2 := by
  classical
  obtain ⟨n,hN,hn,P,hinj,_,hsep,_,hdiam⟩ := Erdos670R29.r29_unbounded_counterexamples N
  refine ⟨n,hN,hn,Finset.univ.image P,?_,?_,?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ hinj
  · intro a ha b hb c hc e he hab hce hpairs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp he
    have hij : i ≠ j := fun h => hab (congrArg P h)
    have hkl : k ≠ l := fun h => hce (congrArg P h)
    let u : Edge (Fin n) := ⟨s(i,j), by simpa only [Sym2.mk_isDiag_iff] using hij⟩
    let v : Edge (Fin n) := ⟨s(k,l), by simpa only [Sym2.mk_isDiag_iff] using hkl⟩
    have huv : u ≠ v := by
      intro h
      have huv' : s(i,j) = s(k,l) := congrArg Subtype.val h
      rcases Sym2.eq_iff.mp huv' with ⟨hik,hjl⟩ | ⟨hil,hjk⟩
      · apply hpairs
        rw [hik,hjl]
      · apply hpairs
        rw [hil,hjk]
        exact Sym2.eq_swap
    simpa only [u,v,edgeDistance,Sym2.lift_mk] using hsep u v huv
  · have heq : (Finset.univ.image P : Set (EuclideanSpace ℝ (Fin 29))) = Set.range P := by
      ext x
      simp only [Finset.mem_coe,Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range]
    rw [heq]
    exact hdiam

theorem r29_refutation :
    ¬ (∀ d : ℕ, 1 ≤ d → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n → Erdos670.HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d)))) := by
  intro h
  have hevent := h 29 (by norm_num) (1/1000) (by norm_num)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨n,hn,hn600,A,hcard,hsep,hdiam⟩ := r29_sets_600 N
  have hlower := hN n hn A hcard hsep
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2pos : 0 < (n : ℝ)^2 := sq_pos_of_pos hnpos
  norm_num at hlower
  nlinarith

end Erdos670

end

theorem OMA.disproof : ¬ (type_of% @Erdos670.erdos_670) :=
  Erdos670.r29_refutation
