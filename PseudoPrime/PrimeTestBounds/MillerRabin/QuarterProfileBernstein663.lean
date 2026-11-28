/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import PseudoPrime.Analysis.Bernstein12
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCombinedEuler137

/-! # Middle support of the section 137 combined Euler profile -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The degree-twelve Taylor minorant of the middle profile. -/
private noncomputable def middlePoly (u : ℝ) : ℝ :=
  -9.917282 - 5.446822 * (0.086 + u) + 3.549579 * (0.086 + u) ^ 2 +
    250 * (21 / 8 - u) ^ 5 * (∑ k ∈ Finset.range 8, ((11 / 5) * u) ^ k / k.factorial)

/-- The original seven Bernstein intervals, listed by their shared endpoints. -/
private def endpoints (i : Fin 8) : ℚ :=
  match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 23 / 10
  | 3 => 12 / 5
  | 4 => 49 / 20
  | 5 => 5 / 2
  | 6 => 51 / 20
  | _ => 21 / 8

/-- Exact power coefficients of the affine substitutions into the middle
polynomial. The identity for every row is checked by polynomial normalization. -/
private def powerCoeff (i : Fin 7) (j : ℕ) : ℚ :=
  match i.val, j with
  | 0, 0 => 51414693635084306419 / 2016000000000000
  | 0, 1 => -731592878500129847 / 32256000000000
  | 0, 2 => -955549575739067 / 64512000000
  | 0, 3 => 86737419419209 / 10321920000
  | 0, 4 => 4371920962331 / 573440000
  | 0, 5 => 544749556863 / 1146880000
  | 0, 6 => -23569385081 / 12288000
  | 0, 7 => -3981385509959 / 3440640000
  | 0, 8 => -5240662097 / 430080000
  | 0, 9 => 24398450527 / 80640000
  | 0, 10 => 4709614393 / 50400000
  | 0, 11 => -320652541 / 12600000
  | 0, 12 => -19487171 / 1575000
  | 1, 0 => 49938275954096077 / 28000000000000
  | 1, 1 => -21573434330494217 / 6720000000000
  | 1, 2 => 656723741635849 / 358400000000
  | 1, 3 => -958112931957 / 5734400000
  | 1, 4 => -157020625108899 / 1146880000000
  | 1, 5 => 2855056122404721 / 286720000000000
  | 1, 6 => 6861368705276943 / 819200000000000
  | 1, 7 => 33278903791636437 / 57344000000000000
  | 1, 8 => -3205223789206923 / 14336000000000000
  | 1, 9 => -508741925273307 / 8960000000000000
  | 1, 10 => -331697932815843 / 56000000000000000
  | 1, 11 => -43133738696631 / 140000000000000000
  | 1, 12 => -1150697960379 / 175000000000000000
  | 2, 0 => 64613178231241679992997 / 537600000000000000000
  | 2, 1 => -264889732404596012097271 / 1612800000000000000000
  | 2, 2 => 132334840899188671588139 / 1612800000000000000000
  | 2, 3 => -5320769002123085736563 / 322560000000000000000
  | 2, 4 => 46022366226258053983 / 107520000000000000000
  | 2, 5 => 113015756214589051793 / 537600000000000000000
  | 2, 6 => 1698014508262061 / 76800000000000000000
  | 2, 7 => -333491044100046261 / 179200000000000000000
  | 2, 8 => -1441064301437651 / 8960000000000000000
  | 2, 9 => -22943355430127 / 3360000000000000000
  | 2, 10 => -2079672016477 / 12600000000000000000
  | 2, 11 => -13763257409 / 6300000000000000000
  | 2, 12 => -19487171 / 1575000000000000000
  | 3, 0 => 1937225721816484903 / 87500000000000000
  | 3, 1 => -8202905843759483347 / 350000000000000000
  | 3, 2 => 26035427509593271359 / 2800000000000000000
  | 3, 3 => -3571501805062845237 / 2240000000000000000
  | 3, 4 => 3140909630243500041 / 35840000000000000000
  | 3, 5 => 3614571435127756819 / 716800000000000000000
  | 3, 6 => -231903694237258571 / 819200000000000000000
  | 3, 7 => -611792828801533973 / 22937600000000000000000
  | 3, 8 => -6184616969700433 / 6881280000000000000000
  | 3, 9 => -28902015670319 / 1720320000000000000000
  | 3, 10 => -797584301921 / 4300800000000000000000
  | 3, 11 => -14698641617 / 12902400000000000000000
  | 3, 12 => -19487171 / 6451200000000000000000
  | 4, 0 => 21296461180852293415831 / 3276800000000000000000
  | 4, 1 => -272779816156139302439773 / 29491200000000000000000
  | 4, 2 => 150007633776902847935389 / 29491200000000000000000
  | 4, 3 => -7078436520642746829101 / 5898240000000000000000
  | 4, 4 => 211560750664920337457 / 1966080000000000000000
  | 4, 5 => 26852020536884733419 / 9830400000000000000000
  | 4, 6 => -4879868505386183243 / 9830400000000000000000
  | 4, 7 => -113015435363926227 / 3276800000000000000000
  | 4, 8 => -346848541583753 / 327680000000000000000
  | 4, 9 => -1533394579233 / 81920000000000000000
  | 4, 10 => -182643590723 / 921600000000000000000
  | 4, 11 => -2166619103 / 1843200000000000000000
  | 4, 12 => -19487171 / 6451200000000000000000
  | 5, 0 => 642986127841755889 / 516096000000000000
  | 5, 1 => -92315836798539083 / 41287680000000000
  | 5, 2 => 7104749786080469 / 3303014400000000
  | 5, 3 => -1592956403639 / 2113929216000
  | 5, 4 => 1321596688267 / 11744051200000
  | 5, 5 => -3032526845913 / 2936012800000000
  | 5, 6 => -48386665778869 / 62914560000000000
  | 5, 7 => -961300124328643 / 22020096000000000000
  | 5, 8 => -13609246157177 / 11010048000000000000
  | 5, 9 => -857351909249 / 41287680000000000000
  | 5, 10 => -21811297981 / 103219200000000000000
  | 5, 11 => -625361033 / 516096000000000000000
  | 5, 12 => -19487171 / 6451200000000000000000
  | 6, 0 => 11883322975944934299967 / 22937600000000000000000
  | 6, 1 => 16889653034444000853087 / 45875200000000000000000
  | 6, 2 => 112037232205870598524473 / 91750400000000000000000
  | 6, 3 => -40965050223031981329729 / 36700160000000000000000
  | 6, 4 => 35009459543146353997023 / 73400320000000000000000
  | 6, 5 => -36988216311813923110923 / 734003200000000000000000
  | 6, 6 => -2654118745734935298699 / 209715200000000000000000
  | 6, 7 => -2724811654668124595607 / 2936012800000000000000000
  | 6, 8 => -21560816570048065431 / 587202560000000000000000
  | 6, 9 => -258988948897676877 / 293601280000000000000000
  | 6, 10 => -37174201050591 / 2867200000000000000000
  | 6, 11 => -316930113996507 / 2936012800000000000000000
  | 6, 12 => -1150697960379 / 2936012800000000000000000
  | _, _ => 0

/-- The exact Bernstein coefficient in degree twelve. -/
private def bernCoeff (i : Fin 7) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1), powerCoeff i j * (Nat.choose k j : ℚ) / Nat.choose 12 j

set_option maxHeartbeats 4000000 in
-- The kernel reduces 91 exact rational polynomial coefficients.
/-- Each rational Bernstein coefficient is nonnegative on each of the
seven intervals. The kernel checks the 91 rational comparisons. -/
private theorem bern_check : ∀ (i : Fin 7) (k : Fin 13), 0 ≤ bernCoeff i k := by decide +kernel

set_option maxHeartbeats 4000000 in
-- Expanding the twelve powers on seven rational intervals requires normalization.
/-- The power coefficients give the middle polynomial on every cell. -/
private theorem middle_power (i : Fin 7) (t : ℝ) :
    let l := endpoints i.castSucc
    let d := endpoints i.succ - l
    middlePoly ((l : ℝ) + (d : ℝ) * t) = ∑ j : Fin 13, (powerCoeff i j : ℝ) * t ^ (j : ℕ) := by
  fin_cases i <;> dsimp only
  case' «0» =>
    rw [show endpoints ((⟨0, by decide⟩ : Fin 7).castSucc) = 1 by decide +kernel,
      show endpoints ((⟨0, by decide⟩ : Fin 7).succ) - 1 = 1 by decide +kernel]
  case' «1» =>
    rw [show endpoints ((⟨1, by decide⟩ : Fin 7).castSucc) = 2 by decide +kernel,
      show endpoints ((⟨1, by decide⟩ : Fin 7).succ) - 2 = 3 / 10 by decide +kernel]
  case' «2» =>
    rw [show endpoints ((⟨2, by decide⟩ : Fin 7).castSucc) = 23 / 10 by decide +kernel,
      show endpoints ((⟨2, by decide⟩ : Fin 7).succ) - 23 / 10 = 1 / 10 by decide +kernel]
  case' «3» =>
    rw [show endpoints ((⟨3, by decide⟩ : Fin 7).castSucc) = 12 / 5 by decide +kernel,
      show endpoints ((⟨3, by decide⟩ : Fin 7).succ) - 12 / 5 = 1 / 20 by decide +kernel]
  case' «4» =>
    rw [show endpoints ((⟨4, by decide⟩ : Fin 7).castSucc) = 49 / 20 by decide +kernel,
      show endpoints ((⟨4, by decide⟩ : Fin 7).succ) - 49 / 20 = 1 / 20 by decide +kernel]
  case' «5» =>
    rw [show endpoints ((⟨5, by decide⟩ : Fin 7).castSucc) = 5 / 2 by decide +kernel,
      show endpoints ((⟨5, by decide⟩ : Fin 7).succ) - 5 / 2 = 1 / 20 by decide +kernel]
  case' «6» =>
    rw [show endpoints ((⟨6, by decide⟩ : Fin 7).castSucc) = 51 / 20 by decide +kernel,
      show endpoints ((⟨6, by decide⟩ : Fin 7).succ) - 51 / 20 = 3 / 40 by decide +kernel]
  all_goals
    norm_num only [middlePoly, powerCoeff, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Finset.sum_range_succ, Finset.sum_range_zero, Fin.val_succ, Fin.val_zero, Fin.val_ofNat,
      Nat.reduceMod, Nat.factorial, Nat.reduceAdd, Nat.reduceSub, Rat.cast_ofNat, Rat.cast_one,
      Rat.cast_div, Rat.cast_neg, Rat.cast_natCast, add_zero]
    ring

/-- The power-to-Bernstein identity bounds the Taylor minorant throughout
a cell when the exact rational coefficients are nonnegative. -/
private theorem middle_cell (i : Fin 7) {u : ℝ}
    (hu : u ∈ Set.Icc (endpoints i.castSucc : ℝ) (endpoints i.succ : ℝ)) : 0 ≤ middlePoly u := by
  have hle : ∀ k : Fin 7, endpoints k.castSucc < endpoints k.succ := by decide +kernel
  obtain ⟨t, ht⟩ := Analysis.exists_unit_coord ((Rat.cast_lt (K := ℝ)).mpr (hle i)) hu.1 hu.2
  rw [← Rat.cast_sub] at ht
  rw [ht, middle_power i (t : ℝ)]
  let a := fun j : ℕ ↦ -(powerCoeff i j : ℝ)
  let c := fun k : Fin 13 ↦ -(bernCoeff i k : ℝ)
  have hc (k : Fin 13) : c k ≤ 0 := neg_nonpos.mpr (Rat.cast_nonneg.mpr (bern_check i k))
  have hb :=
    Analysis.bernstein12_power_le (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10)
      (a 11) (a 12) t c 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hc
  · norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_succ, Fin.val_zero, Nat.reduceAdd,
      pow_zero, pow_one, add_zero] at *
    dsimp only [a] at hb
    linarith only [hb]
  all_goals
    first
    | change -(bernCoeff i 0 : ℝ) = _
    | change -(bernCoeff i 1 : ℝ) = _
    | change -(bernCoeff i 2 : ℝ) = _
    | change -(bernCoeff i 3 : ℝ) = _
    | change -(bernCoeff i 4 : ℝ) = _
    | change -(bernCoeff i 5 : ℝ) = _
    | change -(bernCoeff i 6 : ℝ) = _
    | change -(bernCoeff i 7 : ℝ) = _
    | change -(bernCoeff i 8 : ℝ) = _
    | change -(bernCoeff i 9 : ℝ) = _
    | change -(bernCoeff i 10 : ℝ) = _
    | change -(bernCoeff i 11 : ℝ) = _
    | change -(bernCoeff i 12 : ℝ) = _
    norm_num only [a, bernCoeff, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.choose, Nat.reduceSub, Rat.cast_sum, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_zero]
    ring

/-- The seven adjacent certificates cover every point of the middle interval. -/
private theorem middle_nonneg {u : ℝ} (hu : u ∈ Set.Icc 1 (21 / 8)) : 0 ≤ middlePoly u := by
  by_cases h0 : u ≤ 2
  · apply middle_cell 0
    rw [show endpoints ((0 : Fin 7).castSucc) = 1 by decide +kernel,
      show endpoints ((0 : Fin 7).succ) = 2 by decide +kernel]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
    exact ⟨hu.1, h0⟩
  by_cases h1 : u ≤ 23 / 10
  · apply middle_cell 1
    rw [show endpoints ((1 : Fin 7).castSucc) = 2 by decide +kernel,
      show endpoints ((1 : Fin 7).succ) = 23 / 10 by decide +kernel]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
    exact ⟨(lt_of_not_ge h0).le, h1⟩
  by_cases h2 : u ≤ 12 / 5
  · apply middle_cell 2
    rw [show endpoints ((2 : Fin 7).castSucc) = 23 / 10 by decide +kernel,
      show endpoints ((2 : Fin 7).succ) = 12 / 5 by decide +kernel]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
    exact ⟨(lt_of_not_ge h1).le, h2⟩
  by_cases h3 : u ≤ 49 / 20
  · apply middle_cell 3
    rw [show endpoints ((3 : Fin 7).castSucc) = 12 / 5 by decide +kernel,
      show endpoints ((3 : Fin 7).succ) = 49 / 20 by decide +kernel]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
    exact ⟨(lt_of_not_ge h2).le, h3⟩
  by_cases h4 : u ≤ 5 / 2
  · apply middle_cell 4
    rw [show endpoints ((4 : Fin 7).castSucc) = 49 / 20 by decide +kernel,
      show endpoints ((4 : Fin 7).succ) = 5 / 2 by decide +kernel]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
    exact ⟨(lt_of_not_ge h3).le, h4⟩
  by_cases h5 : u ≤ 51 / 20
  · apply middle_cell 5
    rw [show endpoints ((5 : Fin 7).castSucc) = 5 / 2 by decide +kernel,
      show endpoints ((5 : Fin 7).succ) = 51 / 20 by decide +kernel]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
    exact ⟨(lt_of_not_ge h4).le, h5⟩
  apply middle_cell 6
  rw [show endpoints ((6 : Fin 7).castSucc) = 51 / 20 by decide +kernel,
    show endpoints ((6 : Fin 7).succ) = 21 / 8 by decide +kernel]
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
  exact ⟨(lt_of_not_ge h5).le, hu.2⟩

/-- On the unknown support, the combined profile is nonnegative at every
relative logarithm. The forward term vanishes above the main cutoff. -/
theorem quarter_profile_nonneg_663 {r u : ℝ} (hr : 328 ≤ r) (hu : 0 ≤ u) :
    0 ≤
      quarterProfile663 (2 * Real.log r + u) + if u ≤ 21 / 8 then quarterForward663 r u else 0 := by
  by_cases h : u ≤ 21 / 8
  · rw [ite_eq_left h]
    by_cases h₁ : u ≤ 1
    · exact quarter_profile_low_663 hr ⟨hu, h₁⟩
    · exact
        (middle_nonneg ⟨(lt_of_not_ge h₁).le, h⟩).trans
          (quarter_profile_middle_lower hr ⟨(lt_of_not_ge h₁).le, h⟩)
  · rw [ite_eq_right h, add_zero]
    exact (quarter_profile_beyond_663 hr (lt_of_not_ge h).le).le

/-- The common Euler coefficient loses only four copies of the reflected
profile on the unknown support, by nonnegativity of the combined weight. -/
theorem quarter_profile_euler_663 {r u a : ℝ} (hr : 328 ≤ r) (hu : 0 ≤ u) (ha : a ∈ Set.Icc 0 4) :
    let g := quarterProfile663 (2 * Real.log r + u)
    let f := (if u ≤ 21 / 8 then quarterForward663 r u else 0)
    (-4) * g ≤ (4 - a) * f - a * g := by
  intro g f
  have h := common_euler_lower ha.1 ha.2 f g
  have hfg : 0 ≤ f + g := by
    rw [add_comm]
    exact quarter_profile_nonneg_663 hr hu
  rw [max_eq_left (neg_nonpos.mpr hfg), mul_zero, sub_zero] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
