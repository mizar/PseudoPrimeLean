/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PhaseResolvent64Tail
public import PseudoPrime.Analysis.RationalHorner
public import Mathlib.Analysis.Complex.Exponential

/-! # An exact exponential certificate for all spectral heights at least five -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Output: the 43 exact rational coefficients of the cleared exponential-tail polynomial.
Definition: the shift is t=5+v and the exponential Taylor degree is 24.
Role: certify Gamma domination on the entire range |t|>=5. -/
def phase64ExpTailCoefficients : List ℚ :=
  [191510178919583140 / 1, 8317016441358350052 / 25, 395770122662322815809 / 1250,
    154808382100776723851633 / 375000, 93784638204299995055381849 / 150000000,
    10535207734053538707269095501 / 15000000000, 25469547551730611299639523321801 / 45000000000000,
    10863549722781942718808914933290353 / 31500000000000000,
    4196722913333672210611821055929100601 / 25200000000000000000,
    1496527127077850299459180895552935974113 / 22680000000000000000000,
    99830365379285936169198998124673978227157 / 4536000000000000000000000,
    22455491293277891799477431572730555463294311 / 3564000000000000000000000000,
    47054926601448097575937035842954959456554607001 / 29937600000000000000000000000000,
    13458067268959563833639746973490920326301691935297 / 38918880000000000000000000000000000,
    3691527441604607435959996433653360744312689174150281 / 54486432000000000000000000000000000000,
    17707531365963113876147898496778176784110249750731479 /
      1485993600000000000000000000000000000000,
    247658489971389626617322438360403627020520541581494055929 /
      130767436800000000000000000000000000000000000,
    3576212066974452185811088574040938031303638126731852102801 /
      13076743680000000000000000000000000000000000000,
    2060326481612367123682658051848919319873461153742537029958287 /
      57164050944000000000000000000000000000000000000000,
    3308469683508265584704332651121329968624346684136006167808100497 /
      760281877555200000000000000000000000000000000000000000,
    146844818678453573219237830167160168546990669436124315364636697413 /
      304112751022080000000000000000000000000000000000000000000,
    157689063238461942151181547370006251937957430746524466857469475391233 /
      3193183885731840000000000000000000000000000000000000000000000,
    2523117942726752321980997613878536609443463389445862236310897988977453 /
      540384965277696000000000000000000000000000000000000000000000000,
    6621289852124679924167035117959631671115073970675188618859434625216850673 /
      16157510461803110400000000000000000000000000000000000000000000000000,
    1303530321755847608100121415377923232227580204297454544057634272090321544889 /
      38778025108327464960000000000000000000000000000000000000000000000000000,
    15332296334495562375089756070717406382932083888130781704256433830052795023 /
      5875458349746585600000000000000000000000000000000000000000000000000000,
    243690355675203863401437375672782028021548492538434350892453428611580771073 /
      1242885420138700800000000000000000000000000000000000000000000000000000000,
    894892711416927622089296041849934427628823731902991920712467536340663351469 /
      60590664231761664000000000000000000000000000000000000000000000000000000000,
    5332076470228089291353752707706565094267927957800572654257608344135027079 /
      4590201835739520000000000000000000000000000000000000000000000000000000000,
    1332213407997685421960589037062888586838118884564925588001949340212719537 /
      13739379644390400000000000000000000000000000000000000000000000000000000000,
    497146547109270783889250309730209409204840604020210395129133930514947735857 /
      60590664231761664000000000000000000000000000000000000000000000000000000000000,
    6439952297650538140578430455640943187910087761227675779551702799203061 /
      10114627442535000000000000000000000000000000000000000000000000000000000000,
    708440074005716170920988756796427443991514126627567189408542561041644487 /
      16691643039052800000000000000000000000000000000000000000000000000000000000000,
    726330144928952871207376841656972128681540328242082280896113923807720539 /
      242362656927046656000000000000000000000000000000000000000000000000000000000000,
    17666058569640588095240211391264537038971944595749827006494883647736199 /
      50618767110912000000000000000000000000000000000000000000000000000000000000000,
    9594389054921958418125373706595293599837098536178974615640618184920229 /
      201968880772538880000000000000000000000000000000000000000000000000000000000000,
    3103519302215688166888970248680542734566002896615844288304843584134481 /
      637796465597491200000000000000000000000000000000000000000000000000000000000000,
    675589722449522987294331183311194124176424234731648746725767639903483 /
      2019688807725388800000000000000000000000000000000000000000000000000000000000000,
    98648954044497676257507202895595816828403532219608926341717808747343 /
      6732296025751296000000000000000000000000000000000000000000000000000000000000000,
    2109873266337635977044488294785327417204991395697317246406927507 /
      5610246688126080000000000000000000000000000000000000000000000000000000000000,
    84240387729149954651132857389213553631621980595043255550904903 /
      17486483183769600000000000000000000000000000000000000000000000000000000000000,
    11148782829544451019511866020354387845601248106573090103463 /
      425197643731660800000000000000000000000000000000000000000000000000000000000,
    60357203594430303795288378110194444543427446645930177456679 /
      242362656927046656000000000000000000000000000000000000000000000000000000000000]

/-- Claim: every displayed rational coefficient is strictly positive.
Proof: exact kernel evaluation of the finite list.
Role: remove all numerical sign assumptions from the polynomial certificate. -/
theorem phase64_exp_tail_coefficients_pos :
    phase64ExpTailCoefficients.all (fun c ↦ decide (0 < c)) = true := by decide +kernel

/-- Input: any real shift v.
Claim: the cleared Taylor-resolvent comparison equals the displayed Horner polynomial.
Proof: normalize rational constants and verify the ring identity.
Role: independently check the externally generated polynomial coefficients. -/
theorem phase64_exp_tail_identity (v : ℝ) :
    2560 * (∑ j ∈ Finset.range 25, ((157 / 100 : ℝ) * v) ^ j / (j.factorial : ℝ)) *
          finiteResolventNumerator phaseResolvent64Coefficients ((5 + v) ^ 2) -
        (251 / 100 : ℝ) * finiteResolventDenominator phaseResolvent64Coefficients ((5 + v) ^ 2) =
      rationalHorner phase64ExpTailCoefficients v := by
  norm_num only [finiteResolventNumerator, finiteResolventDenominator, phaseResolvent64Coefficients,
    phase64ExpTailCoefficients, rationalHorner, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.factorial]
  ring

/-- Input: a nonnegative shift. Claim: the certificate polynomial is strictly positive.
Proof: apply the nonempty positive-coefficient Horner lemma.
Role: establish the comparison simultaneously for every ordinate at least five. -/
theorem phase64_exp_tail_polynomial_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < rationalHorner phase64ExpTailCoefficients v := by
  exact rationalHorner_pos_of_all _ (by decide) phase64_exp_tail_coefficients_pos hv

/-- Input: an ordinate at least five.
Claim: 2560 times the degree-24 exponential Taylor polynomial times the resolvent exceeds 2.51.
Proof: clear the positive resolvent denominator and use the shifted polynomial certificate.
Role: replace an exponential comparison with exact polynomial arithmetic. -/
theorem phase64_taylor_times_resolvent_gt {t : ℝ} (ht : 5 ≤ t) :
    (251 / 100 : ℝ) <
      2560 * (∑ j ∈ Finset.range 25, ((157 / 100 : ℝ) * (t - 5)) ^ j / (j.factorial : ℝ)) *
        finiteSignedResolvent phaseResolvent64Coefficients t := by
  have he := phase64_exp_tail_identity (t - 5)
  have hs : (5 : ℝ) + (t - 5) = t := by ring
  rw [hs] at he
  exact
    finiteResolvent_weighted_gt _ (by nlinarith only [ht])
      (he.symm ▸ phase64_exp_tail_polynomial_pos (sub_nonneg.mpr ht))

/-- Claim: exp(157/20)>2560.
Proof: kernel-check a rational Taylor sum below the actual exponential.
Role: certify the exponential endpoint used in the uniform tail bound. -/
theorem phase64_exp_endpoint_lower : (2560 : ℝ) < Real.exp (157 / 20) := by
  have hq : (2560 : ℚ) < ∑ j ∈ Finset.range 25, (157 / 20 : ℚ) ^ j / (j.factorial : ℚ) := by
    decide +kernel
  have hr := (Rat.cast_lt (K := ℝ)).mpr hq
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] at hr
  exact hr.trans_le (Real.sum_le_exp_of_nonneg (by norm_num only) 25)

/-- Input: an ordinate at least five.
Claim: exp(157*t/100) times the signed resolvent exceeds 251/100.
Proof: retain resolvent positivity when replacing Taylor factors by exponentials.
Role: establish the whole unbounded-frequency majorant without a grid. -/
theorem phase64_exp_times_resolvent_gt {t : ℝ} (ht : 5 ≤ t) :
    (251 / 100 : ℝ) <
      Real.exp ((157 / 100) * t) * finiteSignedResolvent phaseResolvent64Coefficients t := by
  let T : ℝ := ∑ j ∈ Finset.range 25, ((157 / 100 : ℝ) * (t - 5)) ^ j / (j.factorial : ℝ)
  have hu : 0 ≤ (157 / 100 : ℝ) * (t - 5) := mul_nonneg (by norm_num only) (sub_nonneg.mpr ht)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ ↦ div_nonneg (pow_nonneg hu _) (Nat.cast_nonneg _))
  have hc := phase64_taylor_times_resolvent_gt ht
  change (251 / 100 : ℝ) < 2560 * T * finiteSignedResolvent phaseResolvent64Coefficients t at hc
  have hR : 0 < finiteSignedResolvent phaseResolvent64Coefficients t := by
    by_contra h
    have hb :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2560) hT)
        (le_of_not_gt h)
    linarith only [hb, hc]
  have hw : 2560 * T ≤ Real.exp ((157 / 100) * t) := by
    calc
      _ ≤ Real.exp (157 / 20) * Real.exp ((157 / 100) * (t - 5)) :=
        mul_le_mul phase64_exp_endpoint_lower.le (Real.sum_le_exp_of_nonneg hu 25) hT
          (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]; congr 1; ring
  exact hc.trans_le (mul_le_mul_of_nonneg_right hw hR.le)

/-- Input: any real ordinate.
Claim: the Gamma norm is at most (251/100)*exp(-157*|t|/100).
Proof: use Euler reflection, pi>3.14, and sqrt(2*pi)<=2.51.
Role: match the rational polynomial certificate with a certified exponential envelope. -/
theorem norm_Gamma_half_le_phase_exp (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤
      (251 / 100 : ℝ) * Real.exp (-((157 / 100) * |t|)) := by
  have hsqrt : Real.sqrt (2 * Real.pi) ≤ (251 / 100 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by linarith only [Real.pi_lt_d4]⟩
  have he : Real.exp (-|Real.pi * t| / 2) ≤ Real.exp (-((157 / 100) * |t|)) := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact Real.exp_le_exp.mpr (by nlinarith only [Real.pi_gt_d2, abs_nonneg t])
  exact
    (norm_Gamma_half_add_I_le_exp t).trans
      (mul_le_mul hsqrt he (Real.exp_pos _).le (by norm_num only))

/-- Input: an ordinate with absolute value at least five.
Claim: the rounded phase resolvent strictly exceeds the Gamma norm.
Proof: combine the exponential polynomial comparison with the Gamma envelope and evenness.
Role: remove the middle-frequency premise from actual arithmetic-sum bounds. -/
theorem phase64_norm_Gamma_lt_of_abs_ge_five {t : ℝ} (ht : 5 ≤ |t|) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ <
      finiteSignedResolvent phaseResolvent64Coefficients t := by
  have hc := phase64_exp_times_resolvent_gt ht
  have hr :
    finiteSignedResolvent phaseResolvent64Coefficients |t| =
      finiteSignedResolvent phaseResolvent64Coefficients t := by
    simp only [finiteSignedResolvent, sq_abs]
  rw [hr] at hc
  apply (norm_Gamma_half_le_phase_exp t).trans_lt
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_lt_iff₀ (Real.exp_pos _)).mpr (by linarith only [hc])

/-- Input: a positive scale and a Gamma phase majorant on |t|<=5.
Claim: the same majorant holds at every real ordinate.
Proof: outside the low interval, discard the phase and use the proved norm comparison.
Role: remove all middle- and high-frequency premises from spectral certification. -/
theorem phase64_signed_phase_le_of_low {x : ℝ} (hx : 0 < x)
    (hc :
      ∀ t : ℝ,
        |t| ≤ 5 →
          -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
            finiteSignedResolvent phaseResolvent64Coefficients t)
    (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent phaseResolvent64Coefficients t := by
  by_cases ht : |t| ≤ 5
  · exact hc t ht
  · exact
      (neg_re_mul_imaginary_power_le_norm _ hx t).trans
        (phase64_norm_Gamma_lt_of_abs_ge_five (le_of_not_ge ht)).le

end PseudoPrime.Analysis
