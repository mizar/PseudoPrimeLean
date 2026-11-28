/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaTailBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectedBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GammaWindowInput

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaTailBound
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GammaWindowInput
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaRational
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaCoefficients
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaPowers
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell

/-! # A single signed polynomial bound for the K186 Gamma derivatives -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Translating an iterated derivative is the same as differentiating
the translated polynomial. -/
private theorem gamma_window_translate (P : Polynomial ℝ) (j : ℕ) :
    ((Polynomial.derivative^[j]) P).comp (Polynomial.X + Polynomial.C 35) =
      (Polynomial.derivative^[j]) (P.comp (Polynomial.X + Polynomial.C 35)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply', ← ih, Polynomial.derivative_comp,
      Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
      one_mul]

/-- The signed derivative polynomial includes the conductor offset of four thirds. -/
private noncomputable def gammaWindowPoly : Polynomial ℝ :=
  let B := HighGaussianKernel.k186.realProfile
  Polynomial.C (4 / 3 : ℝ) * B +
    ∑ j ∈ Finset.range 84, Polynomial.C (highGammaCoeff .k186 j) * (Polynomial.derivative^[j]) B

/-- The real K186 profile has degree at most 83. -/
private theorem gamma_window_degree : HighGaussianKernel.k186.realProfile.natDegree ≤ 83 := by
  have h := high_rat_profile_degree .k186
  rwa [← high_comp_profile_map, Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective]

/-- Extending the sum to the fixed degree bound adds only zero derivatives. -/
private theorem gamma_window_eval (z : ℝ) :
    gammaWindowPoly.eval z = highGammaOffset .k186 (highGammaCoeff .k186) z := by
  simp only [gammaWindowPoly, highGammaOffset, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_finsetSum]
  apply congrArg ((4 / 3 : ℝ) * HighGaussianKernel.k186.realProfile.eval z + ·)
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ gamma_window_degree))
  intro j _ hj
  have h := Nat.lt_of_not_ge fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
  rw [Polynomial.iterate_derivative_eq_zero h, Polynomial.eval_zero, mul_zero]

/-- Neither the Gamma sum nor unit translation raises the degree. -/
private theorem gamma_window_degree_shift :
    (gammaWindowPoly.comp (Polynomial.X + Polynomial.C 35)).natDegree ≤ 83 := by
  apply Polynomial.natDegree_comp_le.trans
  rw [Polynomial.natDegree_X_add_C, mul_one]
  unfold gammaWindowPoly
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_C_mul_le _ _).trans gamma_window_degree
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact
      (Polynomial.natDegree_C_mul_le _ _).trans
        ((Polynomial.natDegree_iterate_derivative _ _).trans
          ((Nat.sub_le _ _).trans gamma_window_degree))

/-- The Gamma interval grid has an exact common positive scale. -/
private def gammaWindowScale : ℕ :=
  3 * 10 ^ 35

/-- The single translated coefficient uses the correct endpoint at each
derivative order, according to the sign of its integer coefficient. -/
private def gammaWindowNum (G : ℕ → ℤ × ℤ) (i : ℕ) : ℤ :=
  (4 * 10 ^ 35) * k186WindowCoeff i +
    ∑ j ∈ Finset.range (84 - i),
      let c := ((i + j).descFactorial j : ℤ) * k186WindowCoeff (i + j)
      max ((G j).1 * c) ((G j).2 * c)

/-- The positive coefficients of the verified upper row give the analytic
weighted bound on the whole half-line beginning at 35. -/
private theorem gamma_window_of_coeff (U : ℕ → ℝ)
    (hU : ∀ i ≤ 83, (gammaWindowPoly.comp (Polynomial.X + Polynomial.C 35)).coeff i ≤ U i) {z : ℝ}
    (hz : 35 ≤ z) :
    Real.exp (-(11 / 4 : ℝ) * z) * highGammaOffset .k186 (highGammaCoeff .k186) z ≤
      Real.exp (-(11 / 4 : ℝ) * 35) *
        ∑ i ∈ Finset.range 84, max 0 (U i) * ((3 / 22 : ℝ) * i) ^ i := by
  rw [← gamma_window_eval]
  have h := decay_poly_le_shifted gammaWindowPoly (by norm_num only : (0 : ℝ) < 11 / 4) hz
  dsimp only at h
  have he (i : ℕ) : (3 / 8 : ℝ) * i / (11 / 4 : ℝ) = (3 / 22 : ℝ) * i := by ring
  simp only [he] at h
  let Q := gammaWindowPoly.comp (Polynomial.X + Polynomial.C 35)
  let f := fun i : ℕ ↦ max 0 (U i) * ((3 / 22 : ℝ) * i) ^ i
  have hsub : Finset.range (Q.natDegree + 1) ⊆ Finset.range 84 :=
    Finset.range_mono (Nat.succ_le_succ gamma_window_degree_shift)
  have hw (i : ℕ) : 0 ≤ ((3 / 22 : ℝ) * i) ^ i :=
    pow_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) _
  have hcoeff (i : ℕ) (hi : i ∈ Finset.range (Q.natDegree + 1)) :
    max 0 (Q.coeff i) * ((3 / 22 : ℝ) * i) ^ i ≤ f i := by
    have hi' := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans gamma_window_degree_shift
    exact mul_le_mul_of_nonneg_right (max_le_max_left 0 (hU i hi')) (hw i)
  have hsum :=
    (Finset.sum_le_sum hcoeff).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub
        (fun i _ _ ↦ mul_nonneg (le_max_left _ _) (hw i)))
  exact h.trans (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _))

/-- A scaled interval product uses the larger signed endpoint product. -/
private theorem gamma_window_product_le {l u v : ℤ} {x : ℝ} (hl : (l : ℝ) / gammaWindowScale ≤ x)
    (hu : x ≤ (u : ℝ) / gammaWindowScale) :
    x * ((v : ℝ) / k186WindowDen) ≤
      (max (l * v) (u * v) : ℤ) / ((gammaWindowScale : ℝ) * k186WindowDen) := by
  have hd : 0 ≤ (gammaWindowScale : ℝ) * k186WindowDen :=
    mul_nonneg (Nat.cast_nonneg _) (Int.cast_nonneg k186_window_den_pos.le)
  have hu' :
    x * ((v : ℝ) / k186WindowDen) ≤
      max (((l : ℝ) / gammaWindowScale) * ((v : ℝ) / k186WindowDen))
        (((u : ℝ) / gammaWindowScale) * ((v : ℝ) / k186WindowDen)) := by
    by_cases hv : 0 ≤ (v : ℝ) / k186WindowDen
    · exact (mul_le_mul_of_nonneg_right hu hv).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hl (le_of_not_ge hv)).trans (le_max_left _ _)
  refine hu'.trans_eq ?_
  rw [div_mul_div_comm, div_mul_div_comm, Int.cast_max, Int.cast_mul, Int.cast_mul,
    max_div_div_right hd]

/-- Combining the integer intervals gives an upper bound on a translated
coefficient. Indices above the fixed profile degree contribute zero. -/
private theorem gamma_window_num_sound (G : ℕ → ℤ × ℤ)
    (hG :
      ∀ j,
        ((G j).1 : ℝ) / gammaWindowScale ≤ highGammaCoeff .k186 j ∧
          highGammaCoeff .k186 j ≤ ((G j).2 : ℝ) / gammaWindowScale)
    {i : ℕ} (hi : i ≤ 83) :
    (gammaWindowPoly.comp (Polynomial.X + Polynomial.C 35)).coeff i ≤
      (gammaWindowNum G i : ℝ) / ((gammaWindowScale : ℝ) * k186WindowDen) := by
  let B := HighGaussianKernel.k186.realProfile.comp (Polynomial.X + Polynomial.C 35)
  have hd : B.natDegree ≤ 83 := by
    exact
      Polynomial.natDegree_comp_le.trans
        (by simpa only [Polynomial.natDegree_X_add_C, mul_one] using gamma_window_degree)
  let f := fun j ↦ highGammaCoeff .k186 j * ((Polynomial.derivative^[j]) B).coeff i
  have hm : (∑ j ∈ Finset.range 84, f j) = ∑ j ∈ Finset.range (84 - i), f j := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.sub_le _ _))
    intro j _ hj
    have hij : 83 < i + j := by
      have h := Nat.le_of_not_lt (fun h ↦ hj (Finset.mem_range.mpr h))
      exact Nat.lt_of_succ_le ((Nat.sub_le_iff_le_add.mp h).trans_eq (Nat.add_comm j i))
    simp only [f, Polynomial.coeff_iterate_derivative,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hij), smul_zero, mul_zero]
  have hf (j : ℕ) (hj : j ∈ Finset.range (84 - i)) :
    f j ≤
      (max ((G j).1 * (((i + j).descFactorial j : ℤ) * k186WindowCoeff (i + j)))
            ((G j).2 * (((i + j).descFactorial j : ℤ) * k186WindowCoeff (i + j))) :
          ℤ) /
        ((gammaWindowScale : ℝ) * k186WindowDen) := by
    have hx := Nat.add_lt_add_right (Finset.mem_range.mp hj) i
    rw [Nat.sub_add_cancel (hi.trans (by decide : 83 ≤ 84)), Nat.add_comm j i] at hx
    have hij : i + j ≤ 83 := Nat.le_of_lt_succ hx
    have hv :
      ((i + j).descFactorial j : ℝ) * ((k186WindowCoeff (i + j) : ℝ) / k186WindowDen) =
        (((i + j).descFactorial j : ℤ) * k186WindowCoeff (i + j) : ℤ) / (k186WindowDen : ℝ) := by
      simp only [Int.cast_mul, Int.cast_natCast, mul_div_assoc]
    simp only [f, B, Polynomial.coeff_iterate_derivative, nsmul_eq_mul, k186_window_coeff_eq hij,
      hv]
    exact gamma_window_product_le (hG j).1 (hG j).2
  have hs := Finset.sum_le_sum (f := f) hf
  have hscale : (4 / 3 : ℝ) = ((4 * 10 ^ 35 : ℤ) : ℝ) / gammaWindowScale := by
    norm_num only [gammaWindowScale, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat]
  simp only [gammaWindowPoly, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.sum_comp, gamma_window_translate, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.finsetSum_coeff]
  change (4 / 3 : ℝ) * B.coeff i + (∑ j ∈ Finset.range 84, f j) ≤ _
  rw [hm, k186_window_coeff_eq hi, hscale, div_mul_div_comm]
  simp only [gammaWindowNum, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sum,
    add_div, Finset.sum_div]
  exact add_le_add le_rfl (by simpa only [Int.cast_max, Int.cast_mul, Int.cast_natCast] using hs)

/-- Store the finite Gamma grid so each endpoint is checked once. -/
private def gammaWindowGridCache : Array (ℤ × ℤ) :=
  #[(-441939155032679952370402239152051324, -441905220751604439037981398302147400),
    (77521324351711356011403789712437582, 99316141228987003901744333726145020),
    (-80532387083190126300861719289445412, -76173269086884298552006287445351542),
    (30337302044365952591328185937247410, 31236772047412627301892964218791055),
    (-19824230827732272406808933340825939, -19633117350372222394695324244653634),
    (10280851434671949977487238849455941, 10322556988155085036036227856362591),
    (-6088370723865050449542239255922597, -6079050806234574764537217632599490),
    (3393448304077501683922950534548518, 3395574589366613683553492044585219),
    (-1958924479844751026834130716567180, -1958430680610832941323272654448997),
    (1111871335205810141708219385773239, 1111987758446582330710749959221316),
    (-637239165345121152899202753054644, -637211363568151453719282278954799),
    (363456128209511311990627699385764, 363462839110450512079305956404899),
    (-207869538361812195752096772953999, -207867903666368590363236281757726),
    (118719961242409332015218639099893, 118720362513652106085552259668927),
    (-67857237997212924535662602213924, -67857138848117035708234919922214),
    (38769747382871293887084308191223, 38769772019570458370622996762718),
    (-22155790789585096796763774759022, -22155784638016933867542242107769),
    (12659908499191755527508389937436, 12659910041689077218452755535737),
    (-7234390756883304883800856276075, -7234390368668901005217718754314),
    (4133886625799355026113160042824, 4133886723824896428552283599011),
    (-2362235910700741456036590251372, -2362235885876854002456970330470),
    (1349844302024260011987268786208, 1349844308327018813125627560248),
    (-771341025859534975512883570346, -771341024255516196732734962197),
    (440765849355028700868765829887, 440765849764110298101173493920),
    (-251866334971704998490156643359, -251866334867172962049846930034),
    (143923577435224881154514623877, 143923577461983032305356629269),
    (-82242057094890275349817649681, -82242057088029591725102328876),
    (46995457180164090403352361493, 46995457181925775474764849679),
    (-26854548178663464044575075952, -26854548178210472449416779435),
    (15345455722589553441606236370, 15345455722706183319564706569),
    (-8768831957016526410710095705, -8768831956986462273509750470),
    (5010761082421719182568400923, 5010761082429477585285056279),
    (-2863292058048626530117045495, -2863292058046622291755055184),
    (1636166886921135041445209553, 1636166886921653306228199648),
    (-934952507849676404502670834, -934952507849542265924544661),
    (534258575593207508679312643, 534258575593242256857714634),
    (-305290614722986059435511859, -305290614722977050667296095),
    (174451779811345466654055861, 174451779811347804060691460),
    (-99686731330079385212344800, -99686731330078778307413335),
    (56963846471458059698728367, 56963846471458217390144816),
    (-32550769413143535083804632, -32550769413143494084058958),
    (18600439664381544690991837, 18600439664381555357588127),
    (-10628822665444387892737676, -10628822665444385116037202),
    (6073612951656771896106089, 6073612951656772619339559),
    (-3470635972383205645809988, -3470635972383205457330986),
    (1983220555645110078184885, 1983220555645110127329039),
    (-1133268888940811647333310, -1133268888940811634513093),
    (647582222251661776832955, 647582222251661780178944),
    (-370046984143877624897927, -370046984143877624024248),
    (211455419510765385383636, 211455419510765385611866),
    (-120831668291872647063264, -120831668291872647003616),
    (69046667595353731859565, 69046667595353731875163),
    (-39455238625917053755215, -39455238625917053751131),
    (22545850643380977945320, 22545850643380977946392),
    (-12883343224789190427803, -12883343224789190427518),
    (7361910414165233152801, 7361910414165233152880),
    (-4206805950951567498699, -4206805950951567498674),
    (2403889114829465388776, 2403889114829465388787),
    (-1373650922759695047263, -1373650922759695047256),
    (784943384434111289581, 784943384434111289587),
    (-448539076819492216548, -448539076819492216542),
    (256308043896852679450, 256308043896852679456),
    (-146461739369630107385, -146461739369630107379), (83692422496931488441, 83692422496931488447),
    (-47824241426817993859, -47824241426817993853), (27328137958181710630, 27328137958181710636),
    (-15616078833246691839, -15616078833246691833), (8923473618998109603, 8923473618998109609),
    (-5099127782284634070, -5099127782284634064), (2913787304162648033, 2913787304162648039),
    (-1665021316664370312, -1665021316664370306), (951440752379640172, 951440752379640178),
    (-543680429931222963, -543680429931222957), (310674531389270258, 310674531389270264),
    (-177528303651011583, -177528303651011577), (101444744943435184, 101444744943435190),
    (-57968425681962970, -57968425681962964), (33124814675407405, 33124814675407411),
    (-18928465528804239, -18928465528804233), (10816266016459558, 10816266016459564),
    (-6180723437976898, -6180723437976892), (3531841964558221, 3531841964558227),
    (-2018195408318991, -2018195408318985), (1153254519039417, 1153254519039423)]

/-- Each stored interval agrees with the analytic rounding rule. -/
private theorem gamma_window_grid_cache_eq :
    Array.ofFn (fun j : Fin 84 ↦ highGammaGrid .k186 1 gammaWindowScale j.val) =
      gammaWindowGridCache := by
  decide +kernel

/-- Use the cached interval at each relevant derivative order. -/
private def gammaWindowGrid (j : ℕ) : ℤ × ℤ :=
  gammaWindowGridCache[j]?.getD (highGammaGrid .k186 1 gammaWindowScale j)

/-- The cache agrees with the exact rule at every index. -/
private theorem gamma_window_grid_eq (j : ℕ) :
    gammaWindowGrid j = highGammaGrid .k186 1 gammaWindowScale j := by
  unfold gammaWindowGrid
  rw [← gamma_window_grid_cache_eq, Array.getElem?_ofFn]
  by_cases hj : j < 84
  · simp only [dite_eq_left hj, Option.getD_some]
  · simp only [dite_eq_right hj, Option.getD_none]

/-- The outward-rounded Gamma offset bound in the shifted coordinate. -/
noncomputable def k186GammaWindowBound : ℝ :=
  Real.exp (-(11 / 4 : ℝ) * 35) *
    ∑ i ∈ Finset.range 84,
      max 0 ((gammaWindowNum gammaWindowGrid i : ℝ) / ((gammaWindowScale : ℝ) * k186WindowDen)) *
        ((3 / 22 : ℝ) * i) ^ i

/-- The single signed Gamma grid bounds the offset on the entire ray
from height 35, even where the individual derivatives change sign. -/
theorem k186_gamma_offset_le_window {z : ℝ} (hz : 35 ≤ z) :
    Real.exp (-(11 / 4 : ℝ) * z) * highGammaOffset .k186 (highGammaCoeff .k186) z ≤
      k186GammaWindowBound := by
  exact
    gamma_window_of_coeff _
      (fun _ hi ↦
        gamma_window_num_sound gammaWindowGrid
          (fun j ↦ by
            simpa only [gamma_window_grid_eq] using
              high_gamma_grid .k186 1 gammaWindowScale j (by decide))
          hi)
      hz

/-- Clear the common power of 22 from the weighted coefficient sum. -/
private def gammaWindowWeightNum : ℤ :=
  ∑ i ∈ Finset.range 84,
    max 0 (gammaWindowNum gammaWindowGrid i) * (3 * (i : ℤ)) ^ i * 22 ^ (83 - i)

/-- The exact common positive denominator for the weighted coefficient sum. -/
private def gammaWindowWeightDen : ℤ :=
  (gammaWindowScale : ℤ) * k186WindowDen * 22 ^ 83

/-- The denominator is positive by the checked integer scale. -/
private theorem gamma_window_weight_den_pos : 0 < gammaWindowWeightDen := by decide +kernel

/-- Each coefficient is clipped at zero before the weighted sum. -/
private theorem gamma_window_weight_nonneg : 0 ≤ gammaWindowWeightNum := by
  unfold gammaWindowWeightNum
  apply Finset.sum_nonneg
  intro i _
  exact
    mul_nonneg
      (mul_nonneg (le_max_left _ _) (pow_nonneg (mul_nonneg (by decide) (Int.natCast_nonneg _)) _))
      (pow_nonneg (by decide) _)

/-- Rewrite one rounded coefficient over the common positive scale. -/
private theorem gamma_window_weight_term (i : ℕ) (hi : i ≤ 83) :
    max 0 ((gammaWindowNum gammaWindowGrid i : ℝ) / ((gammaWindowScale : ℝ) * k186WindowDen)) *
        ((3 / 22 : ℝ) * i) ^ i =
      (max 0 (gammaWindowNum gammaWindowGrid i) * (3 * (i : ℤ)) ^ i * 22 ^ (83 - i) : ℤ) /
        ((gammaWindowScale : ℝ) * k186WindowDen * 22 ^ 83) := by
  let D := (gammaWindowScale : ℝ) * k186WindowDen
  let u := (gammaWindowNum gammaWindowGrid i : ℝ)
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (Int.cast_nonneg k186_window_den_pos.le)
  have he : max 0 (u / D) = max 0 u / D := by rw [← max_div_div_right hD, zero_div]
  have hp : (22 : ℝ) ^ 83 = 22 ^ i * 22 ^ (83 - i) := by rw [← pow_add, Nat.add_sub_of_le hi]
  rw [show ((3 / 22 : ℝ) * i) = (3 * i) / 22 by ring, div_pow]
  change max 0 (u / D) * ((3 * (i : ℝ)) ^ i / 22 ^ i) = _ / (D * 22 ^ 83)
  rw [he, div_mul_div_comm, hp, ← mul_assoc D]
  simp only [Int.cast_mul, Int.cast_max, Int.cast_zero, Int.cast_pow, Int.cast_ofNat,
    Int.cast_natCast]
  exact (mul_div_mul_right _ _ (pow_ne_zero _ (by norm_num only : (22 : ℝ) ≠ 0))).symm

/-- The outward-rounded single integer comparison contains the weighted sum. -/
private theorem gamma_window_weight_check :
    2 * gammaWindowWeightNum * 10 ^ 7 ≤ 10 ^ 42 * gammaWindowWeightDen := by decide +kernel

/-- A left endpoint Taylor bound supplies the scalar exponential factor. -/
private theorem gamma_window_exp_bound : Real.exp (-(11 / 4 : ℝ) * 35) ≤ 2 / 10 ^ 42 := by
  have h := negative_endpoint_exp_upper_valid (by norm_num only : (0 : ℚ) ≤ 385 / 4)
  have hc : negativeEndpointExpUpper (385 / 4) ≤ 2 / 10 ^ 42 := by decide +kernel
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  rw [show -(11 / 4 : ℝ) * 35 = -(385 / 4 : ℝ) by norm_num only]
  exact
    h.trans
      (by
        simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hc)

/-- A positive denominator converts the checked scalar product into the
bound on the damped sum. -/
private theorem gamma_scaled_le {e N D : ℝ} (he : e ≤ 2 / 10 ^ 42) (hN : 0 ≤ N) (hD : 0 < D)
    (hc : 2 * N * 10 ^ 7 ≤ 10 ^ 42 * D) : e * (N / D) ≤ 1 / 10 ^ 7 := by
  refine (mul_le_mul_of_nonneg_right he (div_nonneg hN hD.le)).trans ?_
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos (by norm_num only) hD) (by norm_num only)).mpr
  rw [one_mul]
  exact hc

/-- The checked Gamma grid gives a uniform error of at most one ten-millionth
in the finite high comparison, with the conductor offset already included. -/
theorem k186_gamma_offset_ray_le {z : ℝ} (hz : 35 ≤ z) :
    Real.exp (-(11 / 4 : ℝ) * z) * highGammaOffset .k186 (highGammaCoeff .k186) z ≤ 1 / 10 ^ 7 := by
  refine (k186_gamma_offset_le_window hz).trans ?_
  unfold k186GammaWindowBound
  have hsum :
    (∑ i ∈ Finset.range 84,
        max 0 ((gammaWindowNum gammaWindowGrid i : ℝ) / ((gammaWindowScale : ℝ) * k186WindowDen)) *
          ((3 / 22 : ℝ) * i) ^ i) =
      (gammaWindowWeightNum : ℝ) / (gammaWindowWeightDen : ℝ) := by
    simp only [gammaWindowWeightDen, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast,
      gammaWindowWeightNum, Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] using
      gamma_window_weight_term i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  rw [hsum]
  apply
    gamma_scaled_le gamma_window_exp_bound (Int.cast_nonneg gamma_window_weight_nonneg)
      (Int.cast_pos.mpr gamma_window_weight_den_pos)
  have h := (Int.cast_le (R := ℝ)).mpr gamma_window_weight_check
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
