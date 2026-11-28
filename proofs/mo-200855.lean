import OMAStatements.S_mo_200855
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic

open OMA.S_mo_200855

namespace OMA.MO200855

-- This graph refutes the centrality comparison in MathOverflow question 200855.
-- Bit j in row i records the edge between i and j.
def graph (i j : Fin 15) : Bool :=
  (![4750, 17097, 13601, 22595, 288, 5140, 9482, 3, 2132, 4099,
    14436, 1288, 1581, 1092, 10] i : ℕ).testBit j.val

-- The scores are verified from integer solutions to (30 I - A) v = 30 d · 1.
theorem score_from_vector (G : Fin 15 → Fin 15 → Bool) (hdiag : ∀ i, G i i = false)
    (v : Fin 15 → ℤ) (d : ℤ) (hd : d ≠ 0)
    (hv : ∀ i, 30 * v i - ∑ j, (if G i j then v j else 0) = 30 * d) :
    score G (1 / 30) = fun i => (v i : ℝ) / d := by
  let M : Matrix (Fin 15) (Fin 15) ℝ := 1 - (1 / 30 : ℝ) • realAdj G
  have hMdiag (i : Fin 15) : M i i = 1 := by
    simp [M, realAdj, hdiag i]
  have hM : M.det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro i
    have hOff (j : Fin 15) (hj : j ∈ Finset.univ.erase i) : ‖M i j‖ ≤ 1 / 30 := by
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      cases hG : G i j <;> norm_num [M, Matrix.one_apply, realAdj, hij, hG, Real.norm_eq_abs]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, (1 / 30 : ℝ) := Finset.sum_le_sum hOff
      _ < _ := by
        rw [hMdiag, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
        norm_num
  let y : Fin 15 → ℝ := fun i => (v i : ℝ) / d
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hMy : M.mulVec y = fun _ => 1 := by
    funext i
    have hi := congrArg (fun z : ℤ => (z : ℝ)) (hv i)
    push_cast at hi
    have hsum : (∑ j, (if G i j then (1 : ℝ) else 0) * y j) =
        (∑ j, (if G i j then (v j : ℝ) else 0)) / d := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      cases G i j <;> simp [y]
    change ((1 - (1 / 30 : ℝ) • realAdj G).mulVec y) i = 1
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    change y i - (1 / 30 : ℝ) * (∑ j, (if G i j then (1 : ℝ) else 0) * y j) = 1
    rw [hsum]
    change (v i : ℝ) / d - (1 / 30) * (_ / d) = 1
    rw [← mul_div_assoc, ← sub_div]
    apply (div_eq_iff hd').2
    linarith
  change M⁻¹.mulVec (fun _ => 1) = y
  rw [← hMy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),
    Matrix.one_mulVec]

def original : Fin 15 → ℤ :=
  ![8563963948337376072480, 8519839560194488733250, 8563402379206699653660, 8554629331851799541880,
    7448239561165586645400, 8019508840881106754250, 8293698519117926817600, 7484270887033108401150,
    7983354891625105378980, 7770341283882808085490, 8547188278108538569470, 7750983186801561023970,
    8582111905490990530200, 7761620409296485075650, 7483959733150255850130]

def removed : Fin 15 → ℤ :=
  ![552571235921972697481, 549528924248378108669, 571000757904709884962, 569733734396194787101,
    497222426392689930630, 535312095632177959619, 552974497058507550720, 498351979832382866158,
    532901461347384780691, 517424218248265941689, 570513297390311528458, 517386924264500875828,
    572167152476492265930, 518098259571822138091, 498924063114856935812]

def added : Fin 15 → ℤ :=
  ![4287377806869788087865, 4403447714310324005265, 4424499775344767594460, 4277958938505880197765,
    3719897744130014554785, 4010170059716546186550, 4147452588579889900935, 3742855179221397197235,
    3991932408722086633080, 3885916068383593088205, 4274047741693922894235, 3871292298146123118300,
    4291826674865876729100, 3881360998702679473785, 3742541216942600267565]

end OMA.MO200855

open OMA.MO200855

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_200855.main) := by
  intro h
  have hY := score_from_vector graph (by decide) original 6914810770082046240959 (by decide) (by decide +kernel)
  have hX := score_from_vector (edit graph 0 1 false) (by decide) removed 461615307826704505953
    (by decide) (by decide +kernel)
  have hZ := score_from_vector (edit graph 1 2 true) (by decide) added 3453160995182060127464
    (by decide) (by decide +kernel)
  have hba : score graph (1 / 30) 1 ≤ score graph (1 / 30) 0 := by
    rw [hY]
    norm_num [original, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have hca : score graph (1 / 30) 2 ≤ score graph (1 / 30) 0 := by
    rw [hY]
    norm_num [original, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have hineq := h 15 (by decide) graph 0 1 2 (1 / 30) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num) hba hca
  rw [hX, hY, hZ] at hineq
  norm_num [original, removed, added, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at hineq
