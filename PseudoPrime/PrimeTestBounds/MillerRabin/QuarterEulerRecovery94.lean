/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerZetaTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGamma570
import PseudoPrime.Analysis.HighPrecisionLogBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Rational prefix for the section 94 zeta moments -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Dyadic log scales and scaled centers for log n and n^(-38/25), for n < 128.
The scalar checker verifies the rational intervals extracted from these rows. -/
private def zetaRows : Array (ℕ × ℕ × ℕ) :=
  #[(0, 0, 0), (0, 0, 10000000000000), (1, 6931471805599, 3486859165876),
    (2, 10986122886681, 1882676461633), (2, 13862943611198, 1215818684265),
    (2, 16094379124341, 866095123644), (3, 17917594692280, 656462767662),
    (3, 19459101490553, 519339050004), (3, 20794415416798, 423938852327),
    (3, 21972245773362, 354447065919), (3, 23025850929940, 301995172040),
    (4, 23978952727983, 261266133742), (4, 24849066497880, 228899321848),
    (4, 25649493574615, 202677764052), (4, 26390573296152, 181086212670),
    (4, 27080502011022, 163057690282), (4, 27725887222397, 147821507300),
    (4, 28332133440562, 134808612718), (4, 28903717578961, 123590700061),
    (4, 29444389791664, 113839905497), (4, 29957322735539, 105301463367),
    (4, 30445224377234, 97774740505), (5, 30910424533583, 91099821317),
    (5, 31354942159291, 85147850556), (5, 31780538303479, 79813969844),
    (5, 32188758248682, 75012076320), (5, 32580965380214, 70670881930),
    (5, 32958368660043, 66730914790), (5, 33322045101752, 63142212046),
    (5, 33672958299864, 59862526622), (5, 34011973816621, 56855920192),
    (5, 34339872044851, 54091649514), (5, 34657359027997, 51543277764),
    (5, 34965075614664, 49187960021), (5, 35263605246161, 47005864689),
    (5, 35553480614894, 44979701872), (5, 35835189384561, 43094336532),
    (5, 36109179126442, 41336469322), (5, 36375861597263, 39694371792),
    (5, 36635616461296, 38157665567), (5, 36888794541139, 36717137272),
    (5, 37135720667043, 35364582698), (5, 37376696182833, 34092675012),
    (6, 37612001156935, 32894852814), (6, 37841896339182, 31765224696),
    (6, 38066624897703, 30698487538), (6, 38286413964890, 29689856316),
    (6, 38501476017100, 28735003603), (6, 38712010109078, 27830007231),
    (6, 38918202981106, 26971304885), (6, 39120230054281, 26155654586),
    (6, 39318256327243, 25380100199), (6, 39512437185814, 24641941241),
    (6, 39702919135521, 23938706395), (6, 39889840465642, 23268130188),
    (6, 40073331852324, 22628132440), (6, 40253516907351, 22016800082),
    (6, 40430512678345, 21432371047), (6, 40604430105464, 20873219964),
    (6, 40775374439057, 20337845429), (6, 40943445622221, 19824858645),
    (6, 41108738641733, 19332973283), (6, 41271343850450, 18860996390),
    (6, 41431347263915, 18407820249), (6, 41588830833596, 17972415051),
    (6, 41743872698956, 17553822311), (6, 41896547420264, 17151148925),
    (6, 42046926193909, 16763561802), (6, 42195077051761, 16390283014),
    (6, 42341065045972, 16030585400), (6, 42484952420493, 15683788575),
    (6, 42626798770413, 15349255310), (6, 42766661190160, 15026388233),
    (6, 42904594411483, 14714626828), (6, 43040650932041, 14413444694),
    (6, 43174881135363, 14122347042), (6, 43307333402863, 13840868411),
    (6, 43438054218536, 13568570569), (6, 43567088266895, 13305040593),
    (6, 43694478524670, 13049889107), (6, 43820266346738, 12802748664),
    (6, 43944491546724, 12563272253), (6, 44067192472642, 12331131933),
    (6, 44188406077965, 12106017561), (6, 44308167988433, 11887635635),
    (6, 44426512564903, 11675708210), (7, 44543472962535, 11469971904),
    (7, 44659081186545, 11270176980), (7, 44773368144782, 11076086489),
    (7, 44886363697321, 10887475479), (7, 44998096703302, 10704130265),
    (7, 45108595065168, 10525847743), (7, 45217885770490, 10352434763),
    (7, 45325994931532, 10183707531), (7, 45432947822700, 10019491069),
    (7, 45538768916005, 9859618702), (7, 45643481914678, 9703931580),
    (7, 45747109785033, 9552278234), (7, 45849674786705, 9404514165),
    (7, 45951198501345, 9260501452), (7, 46051701859880, 9120108393),
    (7, 46151205168412, 8983209163), (7, 46249728132842, 8849683501),
    (7, 46347289882296, 8719416406), (7, 46443908991413, 8592297868),
    (7, 46539603501575, 8468222596), (7, 46634390941120, 8347089781),
    (7, 46728288344619, 8228802859), (7, 46821312271242, 8113269301),
    (7, 46913478822291, 8000400404), (7, 47004803657924, 7890111100),
    (7, 47095302013123, 7782319779), (7, 47184988712950, 7676948117),
    (7, 47273878187123, 7573920913), (7, 47361984483944, 7473165943),
    (7, 47449321283632, 7374613815), (7, 47535901911063, 7278197835),
    (7, 47621739347977, 7183853879), (7, 47706846244656, 7091520274),
    (7, 47791234931115, 7001137686), (7, 47874917427820, 6912649008),
    (7, 47957905455967, 6825999264), (7, 48040210447332, 6741135509),
    (7, 48121843553724, 6658006742), (7, 48202815656050, 6576563814),
    (7, 48283137373023, 6496759351), (7, 48362819069514, 6418547675),
    (7, 48441870864585, 6341884731)]

/-- Convert an integer endpoint into a rational at the common precision. -/
private def scaled (n : ℕ) : ℚ :=
  (n : ℚ) / 10000000000000

/-- The two endpoint functions for the finite logarithmic moment sum.
The lower endpoint is truncated at zero, and the upper adds two units. -/
private def prefixTerm (upper : Bool) (j n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let row := zetaRows[n]?.getD (0, 0, 0)
    let endpoint := fun x : ℕ ↦ scaled (if upper then x + 2 else x - 1)
    endpoint row.2.1 ^ j * endpoint row.2.2

/-- Each nonzero row encloses both real scalar factors of the moment. -/
private def prefixRowCheck (n : ℕ) : Bool :=
  if n = 0 then true
  else
    let row := zetaRows[n]?.getD (0, 0, 0)
    Analysis.fineLogCheck n row.1 32 (scaled (row.2.1 - 1)) (scaled (row.2.1 + 2)) &&
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck n (scaled (row.2.2 - 1))
        (scaled (row.2.2 + 2)) 38 25

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Exact reduction checks 127 logarithms and rational powers.
/-- The 127 nonzero rows pass the logarithm and negative-power checks. -/
private theorem prefix_rows_checked : (List.range 128).all prefixRowCheck = true := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- A checked row bounds the corresponding term in every nonnegative
logarithmic moment, including the zero convention for the Dirichlet series. -/
private theorem prefix_term_bound (j n : ℕ) (hn : n < 128) :
    (if n = 0 then 0 else Real.log n ^ j / (n : ℝ) ^ (38 / 25 : ℝ)) ∈
      Set.Icc (prefixTerm false j n : ℝ) (prefixTerm true j n : ℝ) := by
  by_cases hzero : n = 0
  · rw [ite_eq_left hzero]
    simp only [prefixTerm, ite_eq_left hzero, Rat.cast_zero, Set.mem_Icc, le_refl, and_self]
  let row := zetaRows[n]?.getD (0, 0, 0)
  have hc := List.all_eq_true.mp prefix_rows_checked n (List.mem_range.mpr hn)
  rw [prefixRowCheck, ite_eq_right hzero] at hc
  change
    (Analysis.fineLogCheck n row.1 32 (scaled (row.2.1 - 1)) (scaled (row.2.1 + 2)) &&
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck n (scaled (row.2.2 - 1))
          (scaled (row.2.2 + 2)) 38 25) =
      true at hc
  have hl := Analysis.fineLogCheck_sound (Bool.and_eq_true_iff.mp hc).1
  have hp :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (Bool.and_eq_true_iff.mp hc).2
  simp only [Rat.cast_natCast] at hl hp
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hscaled (k : ℕ) : 0 ≤ (scaled k : ℝ) := by
    unfold scaled
    positivity
  have hl₀ := pow_le_pow_left₀ (hscaled (row.2.1 - 1)) hl.1 j
  have hl₁ := pow_le_pow_left₀ (Real.log_natCast_nonneg n) hl.2 j
  have h₀ := mul_le_mul hl₀ hp.1 (hscaled (row.2.2 - 1)) (pow_nonneg (Real.log_natCast_nonneg n) _)
  have h₁ := mul_le_mul hl₁ hp.2 (Real.rpow_nonneg hn₀ _) (pow_nonneg (hscaled (row.2.1 + 2)) _)
  simp only [prefixTerm, ite_eq_right hzero, Bool.false_eq_true, ite_true, Rat.cast_mul,
    Rat.cast_pow, Set.mem_Icc]
  rw [div_eq_mul_inv, ← Real.rpow_neg hn₀]
  norm_num only [Nat.cast_ofNat, neg_div] at h₀ h₁
  exact ⟨h₀, h₁⟩

/-- Lower and upper bounds for the four partial sums through 127. -/
private def prefixBound (upper : Bool) (j : Fin 4) : ℚ :=
  if upper then ![2.382233511, 2.584036796, 6.554851869, 20.264068740] j
  else ![2.382233509, 2.584036793, 6.554851866, 20.264068736] j

-- The four rational sums share the same endpoint table.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- Exact reduction computes the four lower and upper rational sums.
/-- Check the sum endpoints for each logarithmic degree. -/
private theorem prefix_box_checked (j : Fin 4) :
    prefixBound false j ≤ ∑ n ∈ Finset.range 128, prefixTerm false j.val n ∧
      (∑ n ∈ Finset.range 128, prefixTerm true j.val n) ≤ prefixBound true j := by
  fin_cases j <;> decide +kernel

/-- Termwise real inequalities and the rational sum enclosure bound each
finite moment prefix by its two certified endpoints. -/
private theorem zeta_prefix_bound (j : Fin 4) :
    (∑ n ∈ Finset.range 128, if n = 0 then 0 else Real.log n ^ j.val / (n : ℝ) ^ (38 / 25 : ℝ)) ∈
      Set.Icc (prefixBound false j : ℝ) (prefixBound true j : ℝ) := by
  have h := prefix_box_checked j
  have h₀ := (Rat.cast_le (K := ℝ)).mpr h.1
  have h₁ := (Rat.cast_le (K := ℝ)).mpr h.2
  simp only [Rat.cast_sum] at h₀ h₁
  exact
    ⟨h₀.trans
        (Finset.sum_le_sum (fun n hn ↦ prefix_term_bound j.val n (Finset.mem_range.mp hn) |>.1)),
      (Finset.sum_le_sum (fun n hn ↦ prefix_term_bound j.val n (Finset.mem_range.mp hn) |>.2)).trans
        h₁⟩

/-- One certified logarithm and three powers at 128 enclose every term
in the corrected tail before its small analytic remainder. -/
private theorem correction_inputs :
    Real.log 128 ∈ Set.Icc 4.8520302639195 4.8520302639198 ∧
      (128 : ℝ) ^ (-(13 / 25 : ℝ)) ∈ Set.Icc 0.0802141185975 0.0802141185978 ∧
      (128 : ℝ) ^ (-(38 / 25 : ℝ)) ∈ Set.Icc 0.0006266728014 0.0006266728017 ∧
      (128 : ℝ) ^ (-(63 / 25 : ℝ)) ∈ Set.Icc 0.0000048958811 0.0000048958814 := by
  have hl :=
    Analysis.fineLogCheck_sound (N := 128) (j := 7) (n := 32) (lo := 4.8520302639195) (hi :=
      4.8520302639198) (by decide +kernel)
  have hp :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 128) (p := 13) (d := 25)
      (lo := 0.0802141185975) (hi := 0.0802141185978) (by decide +kernel)
  have hq :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 128) (p := 38) (d := 25)
      (lo := 0.0006266728014) (hi := 0.0006266728017) (by decide +kernel)
  have hr :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 128) (p := 63) (d := 25)
      (lo := 0.0000048958811) (hi := 0.0000048958814) (by decide +kernel)
  norm_num only [Set.mem_Icc, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat,
    neg_div] at hl hp hq hr ⊢
  exact ⟨hl, hp, hq, hr⟩

/-- Add the integral and both boundary terms of the corrected tail at 128. -/
private noncomputable def zetaCorrection (j : ℕ) : ℝ :=
  (128 : ℝ) ^ (-(13 / 25 : ℝ)) * Analysis.logPowerTailPoly (13 / 25) j (Real.log 128) +
      Real.log 128 ^ j / (128 : ℝ) ^ (38 / 25 : ℝ) / 2 -
    (128 : ℝ) ^ (-(63 / 25 : ℝ)) *
        ((j : ℝ) * Real.log 128 ^ (j - 1) - (38 / 25) * Real.log 128 ^ j) /
      12

/-- Endpoint comparisons for the increasing integral polynomial, the
logarithmic powers, and the two signed parts of the derivative correction. -/
private theorem correction_bound (j : Fin 4) :
    zetaCorrection j.val ∈
      Set.Icc (![0.154571876, 1.046636862, 7.658626741, 61.798089598] j)
        (![0.154571878, 1.046636865, 7.658626745, 61.798089602] j) := by
  obtain ⟨hl, hp, hq, hr⟩ := correction_inputs
  let l := Real.log 128
  let P := Analysis.logPowerTailPoly (13 / 25) j.val
  have hl₀ : 0 ≤ l := (by norm_num only : (0 : ℝ) ≤ 4.8520302639195).trans hl.1
  have hl₁ : (4.8520302639195 : ℝ) ≤ l := hl.1
  have hl₂ : l ≤ (4.8520302639198 : ℝ) := hl.2
  have hP₁ :=
    Analysis.log_power_tail_poly_mono (by norm_num only : 0 < (13 / 25 : ℝ))
      (by norm_num only : (0 : ℝ) ≤ 4.8520302639195) hl₁ j.val
  have hP₂ := Analysis.log_power_tail_poly_mono (by norm_num only : 0 < (13 / 25 : ℝ)) hl₀ hl₂ j.val
  have hP₀ : 0 ≤ P l := Analysis.log_power_tail_poly_nonneg (by norm_num only) hl₀ j.val
  have hP₃ : 0 ≤ P 4.8520302639195 :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only) (by norm_num only) j.val
  have pow₁ (k : ℕ) := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 4.8520302639195) hl₁ k
  have pow₂ (k : ℕ) := pow_le_pow_left₀ hl₀ hl₂ k
  have hlp (k : ℕ) : 0 ≤ l ^ k := pow_nonneg hl₀ k
  have hlp' (k : ℕ) : 0 ≤ (4.8520302639198 : ℝ) ^ k := pow_nonneg (by norm_num only) k
  have PI₁ := mul_le_mul hp.1 hP₁ hP₃ (Real.rpow_nonneg (by norm_num only) _)
  have PI₂ := mul_le_mul hp.2 hP₂ hP₀ (by norm_num only)
  have Q₁ := mul_le_mul (pow₁ j.val) hq.1 (by norm_num only) (hlp _)
  have Q₂ := mul_le_mul (pow₂ j.val) hq.2 (Real.rpow_nonneg (by norm_num only) _) (hlp' _)
  have R₁ (k : ℕ) := mul_le_mul (pow₁ k) hr.1 (by norm_num only) (hlp _)
  have R₂ (k : ℕ) := mul_le_mul (pow₂ k) hr.2 (Real.rpow_nonneg (by norm_num only) _) (hlp' _)
  have Rj₁ := R₁ j.val
  have Rj₂ := R₂ j.val
  have Rk₁ := R₁ (j.val - 1)
  have Rk₂ := R₂ (j.val - 1)
  unfold zetaCorrection
  rw [div_eq_mul_inv (Real.log 128 ^ _) ((128 : ℝ) ^ (38 / 25 : ℝ)), ←
    Real.rpow_neg (by norm_num only : (0 : ℝ) ≤ 128)]
  change _ ∈ Set.Icc _ _
  fin_cases j <;>
    norm_num only [Set.mem_Icc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.reduceFinMk,
      Nat.cast_ofNat, Nat.cast_zero, Nat.reduceSub, pow_zero, pow_one, Analysis.logPowerTailPoly, P,
      l] at PI₁ PI₂ Q₁ Q₂ Rj₁ Rj₂ Rk₁ Rk₂ ⊢ <;>
    constructor <;>
    linarith only [PI₁, PI₂, Q₁, Q₂, Rj₁, Rj₂, Rk₁, Rk₂]

/-- The four certified prefix and tail enclosures yield the section 94
Euler lower bound used in the section 99 mass comparison. -/
theorem quarter_euler_total_lower_94 :
    3.7372 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n := by
  have hbox (j : Fin 4) :
    quarterZetaMoment j.val ∈
      Set.Icc (![2.53680538, 3.63067364, 14.21347859, 82.06215830] j : ℝ)
        (![2.53680540, 3.63067368, 14.21347864, 82.06215838] j : ℝ) := by
    let S :=
      ∑ n ∈ Finset.range 128, if n = 0 then 0 else Real.log n ^ j.val / (n : ℝ) ^ (38 / 25 : ℝ)
    have he : |quarterZetaMoment j.val - (S + zetaCorrection j.val)| ≤ 2 / 1000000000 := by
      convert quarter_zeta_moment_corrected j using 2
      unfold S zetaCorrection
      ring
    obtain ⟨hp₁, hp₂⟩ := zeta_prefix_bound j
    obtain ⟨hc₁, hc₂⟩ := correction_bound j
    obtain ⟨he₁, he₂⟩ := abs_le.mp he
    change _ ≤ S at hp₁
    change S ≤ _ at hp₂
    fin_cases j <;>
      norm_num only [Set.mem_Icc, prefixBound, Bool.false_eq_true, ite_false, ite_true,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
        Rat.cast_div, Rat.cast_ofNat, Fin.reduceFinMk, Fin.val_zero,
        Fin.val_ofNat] at hp₁ hp₂ hc₁ hc₂ he₁ he₂ ⊢ <;>
      exact ⟨by linarith only [hp₁, hc₁, he₁], by linarith only [hp₂, hc₂, he₂]⟩
  exact quarter_euler_lower_of_moments (hbox 0) (hbox 1) (hbox 2) (hbox 3)

/-- The sharp universal Euler bound and the three even Gamma factors supply
the recovery constant for the section 99 sixth-pole mass comparison. -/
theorem section99_euler_recovery {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.Even) (hb : b.Even) (hc : c.Even) :
    (134154 / 10000 : ℝ) ≤
      3 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
        (quarterGamma570 a + quarterGamma570 b + quarterGamma570 c) / 8 := by
  apply quarter_recovery_134154 ha hb hc
  linarith only [quarter_euler_total_lower_94]

end PseudoPrime.PrimeTestBounds.MillerRabin
