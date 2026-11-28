/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaWidth
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaMajorant
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntCurvature
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge

/-! # Certified K156 Gamma width budgets -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rounded radius weights with denominator ten to the sixteenth. -/
private def weights0 : Array Int :=
  #[1130941496969, 16455612826293, 17069240801371, 13479397401321, 9520624040723, 6333790350870,
    4063072735974, 2545636640779, 1570062434762, 958407646665, 581645940855, 356026069330,
    268999330839, 867485094703, 10426609405931, 155278831459353, 2483730326080122,
    42222936989891492, 760012550638002752, 14440238252744618857, 288804764914223505902,
    6064900063102857051031, 133427801388196465215413, 3068839431928471811494229,
    73652146366283289627996493, 1841303659157082215666385549, 47873895138084137588317869035,
    1292595168728271714869739131524, 36192664724391608016340759507336,
    1049587277007356632473872132775034, 31487618310220698974216155528146967,
    976116167616841668200700813920126446, 31235717363738933382422426038670951272,
    1030778673003384801619940059269796602054, 35046474882115083255077962015166961617770,
    1226626620874027913927728670530837573552198, 44158558351465004901398232139110146430174155,
    1633866659004205181351734589147075411382509041, 62086933042159796891365914387588865625480976962,
    2421390388644232078763270661115965759385938432122,
    96855615545769283150530826444638630375428643541046,
    3971080237376540609171763884230183845392564012841584,
    166785369969814705585214083137667721506487676142629362,
    7171770908702032340164205574919712024778970058958105221,
    315557919982889422967225045296467329090274682575141325070,
    14200106399230024033525127038341029809062360715856981036703,
    653204894364581105542155843763687371216868592929389166148944,
    30700630035135311960481324656893306447192823867681247978422900,
    1473630241686494974103103583530878709465255545648699844324924510,
    72207881842638253731052075593013056763797521736786292289934496874,
    3610394092131912686552603779650652838189876086839314614379711480785,
    184130098698727547014182792762183294747683680428805045333194878052112]

/-- Check that all rounded weights enclose the computable radius majorants. -/
private theorem weights0_checked :
    (∀ j : Fin 52,
      middleGammaRadiusWeight (1 / 2) middleK156GammaWidth j.val ≤
        ((weights0[j.val]?.getD 0 : ℤ) : ℚ) / 10 ^ 16) := by
  decide +kernel

/-- The rounded weights are nonnegative throughout the checked range. -/
private theorem weights0_nonneg : ∀ j : Fin 52, 0 ≤ weights0[j.val]?.getD 0 := by decide +kernel

/-- Transfer the rounded radius checks to the analytic coefficient widths. -/
private theorem weights0_sound (j : ℕ) (hj : j ≤ 51) :
    middleGammaWidthWeight (1 / 2) middleK156GammaRow j ≤
      ((weights0[j]?.getD 0 : ℤ) : ℚ) / 10 ^ 16 := by
  exact
    (middle_gamma_radius_weight_le (by norm_num only) middleK156GammaRow _
          middle_k156_gamma_width_le j).trans
      (weights0_checked ⟨j, Nat.lt_succ_of_le hj⟩)

/-- Rounded radius weights with denominator ten to the sixteenth. -/
private def weights1 : Array Int :=
  #[1130941496969, 16031509764929, 4886569829663, 1159073667868, 254958844229, 55359470638,
    12281068760, 2850786445, 707621326, 217137675, 350222658, 3273679235, 39085944038, 508044138865,
    7112588943540, 106688821838251, 1707021143833514, 29019359442483943, 522348469963341294,
    9924620929302746975, 198492418586054521207, 4168340790307144696170, 91703497386757183160152,
    2109180439895415212581914, 50620330557489965101896676, 1265508263937249127547367706,
    32903214862368477316231524005, 888386801283948887538251120212, 24874830435950568851071031343684,
    721370082642566496681059908948476, 21641102479276994900431797268438599,
    670874176857586841913385715321582708, 21467973659442778941228342890290634023,
    708443130761611705060535315379590910884, 24087066445894797972058200722906090958525,
    843047325606317929022037025301713183536873, 30349703721827445444793332910861674607315625,
    1122939037707615481457353317701881960470665636, 42671683432889388295379426072671514497885280618,
    1664195653882686143519797616834189065417525929036,
    66567826155307445740791904673367562616701037144209,
    2729280872367605275372468091608070067284742522892349,
    114629796639439421565643659847538942825959185961454411,
    4929081255495895127322677373444174541516244996342509810,
    216879575241819385602197804431543679826714779839070394066,
    9759580885881872352098901199419465592202165092758167684571,
    448940720750566128196549455173295417241299594266875713426524,
    21100213875276608025237824393144884610341080930543158530960782,
    1012810266013277185211415570870954461296371884666071609485999450,
    49627703034650582075359362972676768603522222348637508864813807175,
    2481385151732529103767968148633838430176111117431875443240690120964,
    126550642738358984292166375580325759938981666989025647605275195821271]

/-- Check that all rounded weights enclose the computable radius majorants. -/
private theorem weights1_checked :
    (∀ j : Fin 52,
      middleGammaRadiusWeight (1 / 8) middleK156GammaWidth j.val ≤
        ((weights1[j.val]?.getD 0 : ℤ) : ℚ) / 10 ^ 16) := by
  decide +kernel

/-- The rounded weights are nonnegative throughout the checked range. -/
private theorem weights1_nonneg : ∀ j : Fin 52, 0 ≤ weights1[j.val]?.getD 0 := by decide +kernel

/-- Transfer the rounded radius checks to the analytic coefficient widths. -/
private theorem weights1_sound (j : ℕ) (hj : j ≤ 51) :
    middleGammaWidthWeight (1 / 8) middleK156GammaRow j ≤
      ((weights1[j]?.getD 0 : ℤ) : ℚ) / 10 ^ 16 := by
  exact
    (middle_gamma_radius_weight_le (by norm_num only) middleK156GammaRow _
          middle_k156_gamma_width_le j).trans
      (weights1_checked ⟨j, Nat.lt_succ_of_le hj⟩)

/-- The centered integer dot product fits the rational allowance of this cell. -/
private theorem cell0_dot :
    middleGammaWidthDot (BData.shift 51 28 1) 51 (fun i ↦ weights0[i]?.getD 0) ≤
      26072570157316751180817717 * ((BData.shift 51 28 1).den * 10 ^ 16) := by
  decide +kernel

/-- The rational Gamma coefficient-width budget for the cell centered at `28/1`. -/
public theorem middle_k156_gamma_width_cell0 :
    middleGammaWidthBudget middleK156Profile (28 / 1) (1 / 2) middleK156GammaRow ≤
      26072570157316751180817717 := by
  have h :=
    middle_gamma_width_int_cap BData 51 28 1 (by decide) (by decide) (1 / 2) middleK156GammaRow
      (fun i ↦ weights0[i]?.getD 0) (D := 10 ^ 16) (u := 26072570157316751180817717) (v := 1)
      (by decide) (by decide) weights0_sound (fun j hj ↦ weights0_nonneg ⟨j, Nat.lt_succ_of_le hj⟩)
      (by simpa only [mul_one] using cell0_dot)
  simpa only [middleK156Profile, Int.cast_ofNat, Int.cast_one, div_one] using h

/-- The centered integer dot product fits the rational allowance of this cell. -/
private theorem cell1_dot :
    middleGammaWidthDot (BData.shift 51 29 1) 51 (fun i ↦ weights0[i]?.getD 0) ≤
      302137982844262450182834143 * ((BData.shift 51 29 1).den * 10 ^ 16) := by
  decide +kernel

/-- The rational Gamma coefficient-width budget for the cell centered at `29/1`. -/
public theorem middle_k156_gamma_width_cell1 :
    middleGammaWidthBudget middleK156Profile (29 / 1) (1 / 2) middleK156GammaRow ≤
      302137982844262450182834143 := by
  have h :=
    middle_gamma_width_int_cap BData 51 29 1 (by decide) (by decide) (1 / 2) middleK156GammaRow
      (fun i ↦ weights0[i]?.getD 0) (D := 10 ^ 16) (u := 302137982844262450182834143) (v := 1)
      (by decide) (by decide) weights0_sound (fun j hj ↦ weights0_nonneg ⟨j, Nat.lt_succ_of_le hj⟩)
      (by simpa only [mul_one] using cell1_dot)
  simpa only [middleK156Profile, Int.cast_ofNat, Int.cast_one, div_one] using h

/-- The centered integer dot product fits the rational allowance of this cell. -/
private theorem cell2_dot :
    middleGammaWidthDot (BData.shift 51 30 1) 51 (fun i ↦ weights0[i]?.getD 0) ≤
      3501279702245965746995439780 * ((BData.shift 51 30 1).den * 10 ^ 16) := by
  decide +kernel

/-- The rational Gamma coefficient-width budget for the cell centered at `30/1`. -/
public theorem middle_k156_gamma_width_cell2 :
    middleGammaWidthBudget middleK156Profile (30 / 1) (1 / 2) middleK156GammaRow ≤
      3501279702245965746995439780 := by
  have h :=
    middle_gamma_width_int_cap BData 51 30 1 (by decide) (by decide) (1 / 2) middleK156GammaRow
      (fun i ↦ weights0[i]?.getD 0) (D := 10 ^ 16) (u := 3501279702245965746995439780) (v := 1)
      (by decide) (by decide) weights0_sound (fun j hj ↦ weights0_nonneg ⟨j, Nat.lt_succ_of_le hj⟩)
      (by simpa only [mul_one] using cell2_dot)
  simpa only [middleK156Profile, Int.cast_ofNat, Int.cast_one, div_one] using h

/-- The centered integer dot product fits the rational allowance of this cell. -/
private theorem cell3_dot :
    middleGammaWidthDot (BData.shift 51 31 1) 51 (fun i ↦ weights0[i]?.getD 0) ≤
      40574043150590684037117952533 * ((BData.shift 51 31 1).den * 10 ^ 16) := by
  decide +kernel

/-- The rational Gamma coefficient-width budget for the cell centered at `31/1`. -/
public theorem middle_k156_gamma_width_cell3 :
    middleGammaWidthBudget middleK156Profile (31 / 1) (1 / 2) middleK156GammaRow ≤
      40574043150590684037117952533 := by
  have h :=
    middle_gamma_width_int_cap BData 51 31 1 (by decide) (by decide) (1 / 2) middleK156GammaRow
      (fun i ↦ weights0[i]?.getD 0) (D := 10 ^ 16) (u := 40574043150590684037117952533) (v := 1)
      (by decide) (by decide) weights0_sound (fun j hj ↦ weights0_nonneg ⟨j, Nat.lt_succ_of_le hj⟩)
      (by simpa only [mul_one] using cell3_dot)
  simpa only [middleK156Profile, Int.cast_ofNat, Int.cast_one, div_one] using h

/-- The centered integer dot product fits the rational allowance of this cell. -/
private theorem cell4_dot :
    middleGammaWidthDot (BData.shift 51 32 1) 51 (fun i ↦ weights0[i]?.getD 0) ≤
      470186079828156505382137912258 * ((BData.shift 51 32 1).den * 10 ^ 16) := by
  decide +kernel

/-- The rational Gamma coefficient-width budget for the cell centered at `32/1`. -/
public theorem middle_k156_gamma_width_cell4 :
    middleGammaWidthBudget middleK156Profile (32 / 1) (1 / 2) middleK156GammaRow ≤
      470186079828156505382137912258 := by
  have h :=
    middle_gamma_width_int_cap BData 51 32 1 (by decide) (by decide) (1 / 2) middleK156GammaRow
      (fun i ↦ weights0[i]?.getD 0) (D := 10 ^ 16) (u := 470186079828156505382137912258) (v := 1)
      (by decide) (by decide) weights0_sound (fun j hj ↦ weights0_nonneg ⟨j, Nat.lt_succ_of_le hj⟩)
      (by simpa only [mul_one] using cell4_dot)
  simpa only [middleK156Profile, Int.cast_ofNat, Int.cast_one, div_one] using h

/-- The centered integer dot product fits the rational allowance of this cell. -/
private theorem cell5_dot :
    middleGammaWidthDot (BData.shift 51 33 1) 51 (fun i ↦ weights0[i]?.getD 0) ≤
      5448679315448132185201769610053 * ((BData.shift 51 33 1).den * 10 ^ 16) := by
  decide +kernel

/-- The rational Gamma coefficient-width budget for the cell centered at `33/1`. -/
public theorem middle_k156_gamma_width_cell5 :
    middleGammaWidthBudget middleK156Profile (33 / 1) (1 / 2) middleK156GammaRow ≤
      5448679315448132185201769610053 := by
  have h :=
    middle_gamma_width_int_cap BData 51 33 1 (by decide) (by decide) (1 / 2) middleK156GammaRow
      (fun i ↦ weights0[i]?.getD 0) (D := 10 ^ 16) (u := 5448679315448132185201769610053) (v := 1)
      (by decide) (by decide) weights0_sound (fun j hj ↦ weights0_nonneg ⟨j, Nat.lt_succ_of_le hj⟩)
      (by simpa only [mul_one] using cell5_dot)
  simpa only [middleK156Profile, Int.cast_ofNat, Int.cast_one, div_one] using h

/-- The centered integer dot product fits the rational allowance of this cell. -/
private theorem cell6_dot :
    middleGammaWidthDot (BData.shift 51 269 8) 51 (fun i ↦ weights1[i]?.getD 0) ≤
      63141185056681882476601841561249 * ((BData.shift 51 269 8).den * 10 ^ 16) := by
  decide +kernel

/-- The rational Gamma coefficient-width budget for the cell centered at `269/8`. -/
public theorem middle_k156_gamma_width_cell6 :
    middleGammaWidthBudget middleK156Profile (269 / 8) (1 / 8) middleK156GammaRow ≤
      63141185056681882476601841561249 := by
  have h :=
    middle_gamma_width_int_cap BData 51 269 8 (by decide) (by decide) (1 / 8) middleK156GammaRow
      (fun i ↦ weights1[i]?.getD 0) (D := 10 ^ 16) (u := 63141185056681882476601841561249) (v := 1)
      (by decide) (by decide) weights1_sound (fun j hj ↦ weights1_nonneg ⟨j, Nat.lt_succ_of_le hj⟩)
      (by simpa only [mul_one] using cell6_dot)
  simpa only [middleK156Profile, Int.cast_ofNat, Int.cast_one, div_one] using h

/-- The Gamma width correction costs at most one millionth on this cell
after multiplication by the normalized physical exponential. -/
public theorem middle_k156_gamma_scaled0 {z : ℝ} (hz : 55 / 2 ≤ z) :
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z) *
        (middleGammaWidthBudget middleK156Profile (28 / 1) (1 / 2) middleK156GammaRow : ℝ) ≤
      1 / 10 ^ 6 := by
  have hy : (2695 : ℝ) / 40 ≤ (49 / 20 : ℝ) * z := by linarith only [hz]
  have h :=
    middle_gamma_width_scaled (κ := middleK156Norm) (cap := 26072570157316751180817717) (R :=
      1 / 10 ^ 6) 2695 (by decide +kernel) (by norm_num only) hy
      ((Rat.cast_le (K := ℝ)).mpr middle_k156_gamma_width_cell0) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow, neg_mul] using h

/-- The Gamma width correction costs at most one millionth on this cell
after multiplication by the normalized physical exponential. -/
public theorem middle_k156_gamma_scaled1 {z : ℝ} (hz : 57 / 2 ≤ z) :
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z) *
        (middleGammaWidthBudget middleK156Profile (29 / 1) (1 / 2) middleK156GammaRow : ℝ) ≤
      1 / 10 ^ 6 := by
  have hy : (2793 : ℝ) / 40 ≤ (49 / 20 : ℝ) * z := by linarith only [hz]
  have h :=
    middle_gamma_width_scaled (κ := middleK156Norm) (cap := 302137982844262450182834143) (R :=
      1 / 10 ^ 6) 2793 (by decide +kernel) (by norm_num only) hy
      ((Rat.cast_le (K := ℝ)).mpr middle_k156_gamma_width_cell1) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow, neg_mul] using h

/-- The Gamma width correction costs at most one millionth on this cell
after multiplication by the normalized physical exponential. -/
public theorem middle_k156_gamma_scaled2 {z : ℝ} (hz : 59 / 2 ≤ z) :
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z) *
        (middleGammaWidthBudget middleK156Profile (30 / 1) (1 / 2) middleK156GammaRow : ℝ) ≤
      1 / 10 ^ 6 := by
  have hy : (2891 : ℝ) / 40 ≤ (49 / 20 : ℝ) * z := by linarith only [hz]
  have h :=
    middle_gamma_width_scaled (κ := middleK156Norm) (cap := 3501279702245965746995439780) (R :=
      1 / 10 ^ 6) 2891 (by decide +kernel) (by norm_num only) hy
      ((Rat.cast_le (K := ℝ)).mpr middle_k156_gamma_width_cell2) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow, neg_mul] using h

/-- The Gamma width correction costs at most one millionth on this cell
after multiplication by the normalized physical exponential. -/
public theorem middle_k156_gamma_scaled3 {z : ℝ} (hz : 61 / 2 ≤ z) :
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z) *
        (middleGammaWidthBudget middleK156Profile (31 / 1) (1 / 2) middleK156GammaRow : ℝ) ≤
      1 / 10 ^ 6 := by
  have hy : (2989 : ℝ) / 40 ≤ (49 / 20 : ℝ) * z := by linarith only [hz]
  have h :=
    middle_gamma_width_scaled (κ := middleK156Norm) (cap := 40574043150590684037117952533) (R :=
      1 / 10 ^ 6) 2989 (by decide +kernel) (by norm_num only) hy
      ((Rat.cast_le (K := ℝ)).mpr middle_k156_gamma_width_cell3) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow, neg_mul] using h

/-- The Gamma width correction costs at most one millionth on this cell
after multiplication by the normalized physical exponential. -/
public theorem middle_k156_gamma_scaled4 {z : ℝ} (hz : 63 / 2 ≤ z) :
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z) *
        (middleGammaWidthBudget middleK156Profile (32 / 1) (1 / 2) middleK156GammaRow : ℝ) ≤
      1 / 10 ^ 6 := by
  have hy : (3087 : ℝ) / 40 ≤ (49 / 20 : ℝ) * z := by linarith only [hz]
  have h :=
    middle_gamma_width_scaled (κ := middleK156Norm) (cap := 470186079828156505382137912258) (R :=
      1 / 10 ^ 6) 3087 (by decide +kernel) (by norm_num only) hy
      ((Rat.cast_le (K := ℝ)).mpr middle_k156_gamma_width_cell4) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow, neg_mul] using h

/-- The Gamma width correction costs at most one millionth on this cell
after multiplication by the normalized physical exponential. -/
public theorem middle_k156_gamma_scaled5 {z : ℝ} (hz : 65 / 2 ≤ z) :
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z) *
        (middleGammaWidthBudget middleK156Profile (33 / 1) (1 / 2) middleK156GammaRow : ℝ) ≤
      1 / 10 ^ 6 := by
  have hy : (3185 : ℝ) / 40 ≤ (49 / 20 : ℝ) * z := by linarith only [hz]
  have h :=
    middle_gamma_width_scaled (κ := middleK156Norm) (cap := 5448679315448132185201769610053) (R :=
      1 / 10 ^ 6) 3185 (by decide +kernel) (by norm_num only) hy
      ((Rat.cast_le (K := ℝ)).mpr middle_k156_gamma_width_cell5) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow, neg_mul] using h

/-- The Gamma width correction costs at most one millionth on this cell
after multiplication by the normalized physical exponential. -/
public theorem middle_k156_gamma_scaled6 {z : ℝ} (hz : 67 / 2 ≤ z) :
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z) *
        (middleGammaWidthBudget middleK156Profile (269 / 8) (1 / 8) middleK156GammaRow : ℝ) ≤
      1 / 10 ^ 6 := by
  have hy : (3283 : ℝ) / 40 ≤ (49 / 20 : ℝ) * z := by linarith only [hz]
  have h :=
    middle_gamma_width_scaled (κ := middleK156Norm) (cap := 63141185056681882476601841561249) (R :=
      1 / 10 ^ 6) 3283 (by decide +kernel) (by norm_num only) hy
      ((Rat.cast_le (K := ℝ)).mpr middle_k156_gamma_width_cell6) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow, neg_mul] using h

/-- A common denominator for the order-zero endpoint, higher-order grid,
and exact pole contributions. -/
private def upperDen : ℕ :=
  (middleK156GammaRow 0).2.den * 10 ^ 16 * 39 ^ 52

/-- The input endpoint denominators divide the chosen scale at every retained order. -/
private theorem upper_den_dvd : ∀ j : Fin 52, (middleK156GammaRow j.val).2.den ∣ upperDen := by
  decide +kernel

/-- The derivative sum's upper polynomial as a shared integer row. -/
private def upperRow : MiddleIntRow :=
  BData.gammaUpper (middleGammaWeightRow 51 upperDen middleK156GammaRow) 51

/-- The shared row represents the upper polynomial used by the contour bound. -/
private theorem upper_row_poly :
    upperRow.poly 51 = middleGammaUpperPoly middleK156Profile middleK156GammaRow := by
  exact
    BData.gamma_upper_poly _ 51 _ (by decide) fun j hj ↦
      middle_gamma_weight_row_eq 51 upperDen _ (by decide +kernel) j hj (upper_den_dvd ⟨j, hj⟩)

/-- Both endpoint enclosures use the shared integer row for the Gamma upper polynomial. -/
private theorem upper_endpoint_contains (a b : ℤ) (hb : 0 < b) :
    let Q := (middleGammaUpperPoly middleK156Profile middleK156GammaRow).map (Rat.castHom ℝ)
    (upperRow.evalInterval 51 a b).Contains upperRow.den (Q.eval ((a : ℝ) / b)) ∧
      ((upperRow.deriv 50).evalInterval 50 a b).Contains upperRow.den
        (Q.derivative.eval ((a : ℝ) / b)) := by
  intro Q
  have hd : 0 < upperRow.den := by decide +kernel
  have h := upperRow.eval_interval_contains 51 a b hd hb
  have h' := upperRow.deriv_interval_contains 50 a b hd hb
  rw [upper_row_poly] at h
  rw [show 50 + 1 = 51 from rfl, upper_row_poly] at h'
  exact ⟨h, h'⟩

/-- Translate the shared derivative-sum row once to the left endpoint of the physical range. -/
private def upperLocalRow : MiddleIntRow :=
  upperRow.shift 51 55 2

/-- The translated upper row supplies the curvature cap at any cell right endpoint. -/
private theorem upper_curvature_le (p d : ℤ) (hp : 0 ≤ p) (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t)
    (ht' : t ≤ (p : ℝ) / d) :
    let Q :=
      (middleGammaUpperPoly middleK156Profile middleK156GammaRow).comp
        (Polynomial.X + Polynomial.C (55 / 2 : ℚ))
    |(gaussianLocalCurv (Q.map (Rat.castHom ℝ)) (49 / 20) 1).eval t| ≤
      (upperLocalRow.curvCap 51 49 20 p d : ℝ) / upperLocalRow.den := by
  intro Q
  have h := upperLocalRow.curv_cap_le 51 49 20 p d (by decide +kernel) (by decide) hp hd ht ht'
  have hq : upperLocalRow.poly 51 = Q := by
    dsimp only [upperLocalRow, Q]
    rw [upperRow.poly_shift 51 55 2 (by decide +kernel) (by decide), upper_row_poly]
    norm_num only [Int.cast_ofNat]
  rw [hq] at h
  simpa only [Int.cast_ofNat, Int.cast_one] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
