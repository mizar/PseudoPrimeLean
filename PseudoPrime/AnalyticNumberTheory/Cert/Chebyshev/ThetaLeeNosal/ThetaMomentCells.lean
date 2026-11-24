/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SincMomentQuadrature
import PseudoPrime.Analysis.PreciseLogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincPhaseRational
import all PseudoPrime.Analysis.SincMomentQuadrature
import all PseudoPrime.Analysis.ScaledRationalPhase
import all PseudoPrime.Analysis.PreciseLogTaylorBounds
import all PseudoPrime.Analysis.LogTaylorBounds

/-! # Generated Simpson nodes and finite moment budgets -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private def samples : Array (Nat × Int × Int) :=
  #[(16, 2500785, -2290007), (17, 2324976, -1988225), (18, 2174435, -1735332),
    (19, 2044239, -1521010), (20, 1929718, -1336928), (21, 1828515, -1177658),
    (22, 1738192, -1038689), (23, 1656371, -916220), (24, 1582049, -807824), (25, 1513749, -711194),
    (26, 1451055, -624860), (27, 1392652, -547179), (28, 1338125, -477116), (29, 1287062, -413766),
    (30, 1238976, -356322), (31, 1193591, -304147), (32, 1150399, -256631), (34, 1070267, -173892),
    (36, 997086, -105026), (38, 929748, -47677), (40, 867591, 1), (42, 809970, 39520),
    (44, 756511, 72105), (46, 706817, 98787), (48, 660657, 120453), (50, 617746, 137847),
    (52, 577888, 151618), (54, 540874, 162320), (56, 506505, 170426), (58, 474585, 176339),
    (60, 444919, 180400), (62, 417316, 182892), (64, 391587, 184048), (68, 345015, 183075),
    (72, 303814, 178579), (76, 266777, 171232), (80, 232925, 161452), (84, 201574, 149556),
    (88, 172317, 135865), (92, 145027, 120794), (96, 119812, 104892), (100, 96919, 88806),
    (104, 76686, 73274), (108, 59451, 59050), (112, 45477, 46824), (116, 34897, 37156),
    (120, 27683, 30412), (124, 23631, 26736), (128, 22377, 26028), (136, 26203, 32066),
    (144, 34513, 44209), (152, 42955, 57344), (160, 48702, 67514), (168, 50849, 72972),
    (176, 49965, 74028), (184, 47189, 72012), (192, 43411, 68095), (200, 38923, 62644),
    (208, 33587, 55373), (216, 27311, 46056), (224, 20456, 35239), (232, 13916, 24461),
    (240, 8826, 15813), (248, 6073, 11079), (256, 5897, 10946), (272, 10747, 20600),
    (288, 15791, 31170), (304, 16967, 34410), (320, 15556, 32346), (336, 12481, 26560),
    (352, 7635, 16601), (368, 3364, 7463), (384, 2841, 6424), (400, 5479, 12614),
    (416, 7896, 18488), (432, 8485, 20189), (448, 7880, 19035), (464, 6309, 15461),
    (480, 3752, 9320), (496, 1680, 4229), (512, 1767, 4502), (520, 2527, 6480), (528, 3438, 8869),
    (536, 4242, 11006), (544, 4786, 12490), (552, 5047, 13245), (560, 5085, 13417),
    (568, 4968, 13179), (576, 4719, 12584), (584, 4311, 11556), (592, 3712, 10001),
    (600, 2945, 7973), (608, 2119, 5764), (616, 1408, 3847), (624, 984, 2701), (632, 944, 2602),
    (640, 1264, 3502)]

private theorem samples_size : samples.size = 97 := by decide +kernel

/-- The 97 endpoint and midpoint abscissas shared by the 48 Simpson cells. -/
public def momentNode (i : Fin 97) : ℚ :=
  (samples[i.val]'(samples_size.symm ▸ i.isLt)).1 / 40

/-- Rounded upper sample for the plain or logarithmic moment, in units of one millionth. -/
public def momentSample (logarithmic : Bool) (i : Fin 97) : ℚ :=
  let p := (samples[i.val]'(samples_size.symm ▸ i.isLt)).2
  ((if logarithmic then p.2 else p.1 : Int) : ℚ) / 1000000

/-- Rational approximation to the two harmonics in the sine majorant at a grid point. -/
public def momentMajorantApprox (x : ℚ) : ℚ :=
  let c := fun v ↦ (Analysis.rationalScaledPhase (10 ^ 20) v 24 12).1
  2 / 3 - 7 * c (2 * x) / 18 - c (4 * x) / 18

/-- On the finite integration interval the combined cosine errors are below one
trillionth. Both frequencies satisfy the certified phase reduction bound. -/
public theorem momentMajorantApprox_error (x : ℚ) (hx : 0 ≤ x) (hb : x ≤ 16) :
    |Analysis.sineMajorant (x : ℝ) - (momentMajorantApprox x : ℝ)| ≤ 1 / 10 ^ 12 := by
  have hfreq (k : ℚ) (hk : 0 ≤ k) (h4 : k ≤ 4) : |((k * x : ℚ) : ℝ)| ≤ 4096 := by
    rw [abs_of_nonneg (Rat.cast_nonneg.mpr (mul_nonneg hk hx))]
    exact_mod_cast
      (mul_le_mul h4 hb hx (by decide +kernel)).trans (by decide +kernel : (4 : ℚ) * 16 ≤ 4096)
  have h₂ :=
    (Analysis.scaledPhase_trig_bounds (2 * x) (hfreq 2 (by decide +kernel) (by decide +kernel))).1
  have h₄ := (Analysis.scaledPhase_trig_bounds (4 * x) (hfreq 4 (by decide +kernel) le_rfl)).1
  simp only [Rat.cast_mul, Rat.cast_ofNat] at h₂ h₄
  simp only [Analysis.sineMajorant, momentMajorantApprox, Rat.cast_sub, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_mul]
  apply abs_le.mpr
  constructor <;>
    linarith only [(abs_le.mp h₂).1, (abs_le.mp h₂).2, (abs_le.mp h₄).1, (abs_le.mp h₄).2]

/-- Approximate the shifted numerator using the same rational majorant at the
evaluation point and at the fixed anchor. -/
public def momentNumeratorApprox (x : ℚ) : ℚ :=
  momentMajorantApprox x + (2 / 5 - momentMajorantApprox (2 / 5))

/-- For every rational point in the integration interval, the two harmonic
approximations enclose the shifted numerator with error at most two trillionths. -/
public theorem momentNumeratorApprox_error (x : ℚ) (hx : 0 ≤ x) (hb : x ≤ 16) :
    |Analysis.sincMomentNumerator (x : ℝ) - (momentNumeratorApprox x : ℝ)| ≤ 2 / 10 ^ 12 := by
  have h := abs_le.mp (momentMajorantApprox_error x hx hb)
  have ha := abs_le.mp (momentMajorantApprox_error (2 / 5) (by decide +kernel) (by decide +kernel))
  simp only [Rat.cast_div, Rat.cast_ofNat] at ha
  simp only [Analysis.sincMomentNumerator, Analysis.sineMajorantShift, momentNumeratorApprox,
    Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
  exact abs_le.mpr ⟨by linarith only [h.1, ha.2], by linarith only [h.2, ha.1]⟩

/-- The finite grid starts at 2/5 and ends at 16. -/
public theorem momentNode_ends : momentNode 0 = 2 / 5 ∧ momentNode 96 = 16 := by decide +kernel

/-- Index of the left, middle or right sample in one cell. -/
public def momentCellIndex (i : Fin 48) (j : Fin 3) : Fin 97 :=
  ⟨2 * i.val + j.val,
    Nat.lt_of_le_of_lt
      (Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ i.isLt)) (Nat.le_of_lt_succ j.isLt))
      (by decide : 2 * 47 + 2 < 97)⟩

/-- One cell has positive width and its central node is its exact midpoint. -/
public theorem momentNode_cell (i : Fin 48) :
    let l := momentCellIndex i 0
    let m := momentCellIndex i 1
    let r := momentCellIndex i 2
    momentNode l < momentNode r ∧ momentNode m = (momentNode l + momentNode r) / 2 := by
  revert i
  decide +kernel

/-- Every sample lies in the interval on which the common derivative estimate applies. -/
public theorem momentNode_range (i : Fin 97) : 2 / 5 ≤ momentNode i ∧ momentNode i ≤ 16 := by
  revert i
  decide +kernel

private theorem plainSampleBudget :
    ∀ i : Fin 97,
      momentNumeratorApprox (momentNode i) + 2 / 10 ^ 12 ≤
        momentSample false i * momentNode i ^ 2 := by
  decide +kernel

/-- Each plain sample bounds the shifted numerator divided by the squared abscissa. -/
public theorem plainSample_le (i : Fin 97) :
    Analysis.sincMomentNumerator (momentNode i : ℝ) / (momentNode i : ℝ) ^ 2 ≤
      (momentSample false i : ℝ) := by
  have hp := (show (0 : ℚ) < 2 / 5 by decide +kernel).trans_le (momentNode_range i).1
  have he := (abs_le.mp (momentNumeratorApprox_error _ hp.le (momentNode_range i).2)).2
  have hb := (Rat.cast_le (K := ℝ)).mpr (plainSampleBudget i)
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_mul] at hb
  exact (div_le_iff₀ (pow_pos (Rat.cast_pos.mpr hp) 2)).2 (by linarith only [he, hb])

private def momentLogScale (x : ℚ) : ℕ :=
  if x ≤ 1 then 0 else if x ≤ 2 then 1 else if x ≤ 4 then 2 else if x ≤ 8 then 3 else 4

private theorem logSampleBudget :
    ∀ i : Fin 97,
      let x := momentNode i
      let j := momentLogScale x
      let u := Analysis.preciseLogUpper x j 40
      let p := momentNumeratorApprox x
      |1 - x / 2 ^ j| < 1 ∧
        (if 0 ≤ u then (p + 2 / 10 ^ 12) * u else (p - 2 / 10 ^ 12) * u) ≤
          momentSample true i * x ^ 2 := by
  decide +kernel

/-- The logarithmically weighted integrand is bounded at all 97 samples, including
those with negative logarithm where the lower numerator bound controls the product. -/
public theorem logSample_le (i : Fin 97) :
    Analysis.sincMomentNumerator (momentNode i : ℝ) * Real.log (momentNode i : ℝ) /
        (momentNode i : ℝ) ^ 2 ≤
      (momentSample true i : ℝ) := by
  let x := momentNode i
  let u := Analysis.preciseLogUpper x (momentLogScale x) 40
  have hp := (show (0 : ℚ) < 2 / 5 by decide +kernel).trans_le (momentNode_range i).1
  have he := abs_le.mp (momentNumeratorApprox_error x hp.le (momentNode_range i).2)
  have hl := (Analysis.preciseLog_bounds hp (momentLogScale x) 40 (logSampleBudget i).1).2
  have hn : 0 ≤ Analysis.sincMomentNumerator (x : ℝ) :=
    add_nonneg ((abs_nonneg _).trans (Analysis.abs_sin_le_majorant _))
      Analysis.sineMajorantShift_bounds.1.le
  apply (div_le_iff₀ (pow_pos (Rat.cast_pos.mpr hp) 2)).2
  apply (mul_le_mul_of_nonneg_left hl hn).trans
  have hb := (logSampleBudget i).2
  change (if 0 ≤ u then _ else _) ≤ _ at hb
  by_cases hu : 0 ≤ u
  · rw [ite_eq_left hu] at hb
    have ht := mul_le_mul_of_nonneg_right (sub_le_iff_le_add'.mp he.2) (Rat.cast_nonneg.mpr hu)
    exact
      ht.trans
        (by
          simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using
            (Rat.cast_le (K := ℝ)).mpr hb)
  · rw [ite_eq_right hu] at hb
    have ht :=
      mul_le_mul_of_nonpos_right
        (show (momentNumeratorApprox x : ℝ) - 2 / 10 ^ 12 ≤ Analysis.sincMomentNumerator (x : ℝ) by
          linarith only [he.1])
        (Rat.cast_nonpos.mpr (le_of_not_ge hu))
    exact
      ht.trans
        (by
          simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] using
            (Rat.cast_le (K := ℝ)).mpr hb)

/-- The logarithm stays within the common fourth-derivative budget at every grid node. -/
public theorem momentNode_log_range (i : Fin 97) :
    -(3 : ℝ) ≤ Real.log (momentNode i : ℝ) ∧ Real.log (momentNode i : ℝ) ≤ 3 := by
  have hl :=
    Analysis.preciseLogCheck_sound (N := 2 / 5) (j := 0) (n := 4) (lo := -3) (hi := 3)
      (by decide +kernel)
  have hr :=
    Analysis.preciseLogCheck_sound (N := 16) (j := 4) (n := 4) (lo := -3) (hi := 3)
      (by decide +kernel)
  have h := momentNode_range i
  have hp : (0 : ℝ) < ((2 / 5 : ℚ) : ℝ) := Rat.cast_pos.mpr (by decide +kernel)
  have ha := (Rat.cast_le (K := ℝ)).mpr h.1
  have hb := (Rat.cast_le (K := ℝ)).mpr h.2
  constructor
  · exact_mod_cast hl.1.trans (Real.log_le_log hp ha)
  · exact_mod_cast (Real.log_le_log (hp.trans_le ha) hb).trans hr.2

/-- Consecutive Simpson cells share the evaluation point at their common boundary. -/
public theorem momentCell_adjacent (i : Fin 47) :
    momentCellIndex i.castSucc 2 = momentCellIndex i.succ 0 := by
  revert i
  decide +kernel

/-- The Simpson inequality at any generated cell uses the shared middle sample and
the uniform log bound at its two ends. -/
public theorem momentCell_integral_le (i : Fin 48) (s t : ℚ) :
    let a := momentNode (momentCellIndex i 0)
    let m := momentNode (momentCellIndex i 1)
    let b := momentNode (momentCellIndex i 2)
    let f := Analysis.sincMomentNumerator * Analysis.momentWeightTerm 0 (s : ℝ) (t : ℝ)
    (∫ x in (a : ℝ)..(b : ℝ), f x) ≤
      ((b : ℝ) - a) / 6 * (f a + 4 * f m + f b) +
        ((b : ℝ) - a) ^ 5 * (Analysis.momentCellBound s t a 3 : ℝ) / 2880 := by
  let l := momentCellIndex i 0
  let r := momentCellIndex i 2
  have hp := (show (0 : ℚ) < 2 / 5 by decide +kernel).trans_le (momentNode_range l).1
  have h :=
    Analysis.sincMoment_simpson_cell s t (momentNode l) (momentNode r) 3 (Rat.cast_pos.mpr hp)
      (Rat.cast_lt.mpr (momentNode_cell i).1) (by exact_mod_cast (momentNode_log_range l).1)
      (by exact_mod_cast (momentNode_log_range r).2)
  simpa only [(momentNode_cell i).2, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, l, r] using h

/-- Rational Simpson upper sum including the fourth-order allowance at every cell.
The common absolute log bound 3 covers the entire finite interval. -/
public def momentFiniteUpper (logarithmic : Bool) : ℚ :=
  ∑ i : Fin 48,
    let l := momentCellIndex i 0
    let m := momentCellIndex i 1
    let r := momentCellIndex i 2
    let h := momentNode r - momentNode l
    let M :=
      Analysis.momentCellBound (if logarithmic then 1 else 0) (if logarithmic then 0 else 1)
        (momentNode l) 3
    h / 6 *
        (momentSample logarithmic l + 4 * momentSample logarithmic m + momentSample logarithmic r) +
      h ^ 5 * M / 2880

/-- The finite scalar budgets, with the same 48 cells for both moments. -/
public theorem momentFiniteUpper_bounds :
    momentFiniteUpper false ≤ 1621 / 1000 ∧ momentFiniteUpper true ≤ 14 / 100 := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
