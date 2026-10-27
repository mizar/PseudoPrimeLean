/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AnchoredEulerCertificate

/-! # Kernel-certified anchor constant at 128 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The forty-four nonzero prime-power atom rows through 128. Each stores a prime,
exponent, logarithm endpoints and two negative-power lower endpoints. The indexed
checker below validates the data with kernel reduction before analytic use. -/
private def anchor128Atoms : List AnchorEulerAtom :=
  [⟨2, 1, 6931471 / 10000000, 6931472 / 10000000, 4204482076 / 10000000000,
      1486508893 / 10000000000⟩,
    ⟨3, 1, 10986122 / 10000000, 10986123 / 10000000, 2532785618 / 10000000000,
      487434819 / 10000000000⟩,
    ⟨2, 2, 6931471 / 10000000, 6931472 / 10000000, 1767766952 / 10000000000,
      220970869 / 10000000000⟩,
    ⟨5, 1, 16094379 / 10000000, 16094380 / 10000000, 1337480609 / 10000000000,
      119627902 / 10000000000⟩,
    ⟨7, 1, 19459101 / 10000000, 19459102 / 10000000, 878268789 / 10000000000,
      47422057 / 10000000000⟩,
    ⟨2, 3, 6931471 / 10000000, 6931472 / 10000000, 743254446 / 10000000000, 32847516 / 10000000000⟩,
    ⟨3, 2, 10986122 / 10000000, 10986123 / 10000000, 641500299 / 10000000000,
      23759270 / 10000000000⟩,
    ⟨11, 1, 23978952 / 10000000, 23978953 / 10000000, 499182260 / 10000000000,
      13682646 / 10000000000⟩,
    ⟨13, 1, 25649493 / 10000000, 25649494 / 10000000, 405107990 / 10000000000,
      8642826 / 10000000000⟩,
    ⟨2, 4, 6931471 / 10000000, 6931472 / 10000000, 312500000 / 10000000000, 4882812 / 10000000000⟩,
    ⟨17, 1, 28332133 / 10000000, 28332134 / 10000000, 289693565 / 10000000000,
      4133000 / 10000000000⟩,
    ⟨19, 1, 29444389 / 10000000, 29444390 / 10000000, 252091381 / 10000000000,
      3043880 / 10000000000⟩,
    ⟨23, 1, 31354942 / 10000000, 31354943 / 10000000, 198536428 / 10000000000,
      1799900 / 10000000000⟩,
    ⟨5, 2, 16094379 / 10000000, 16094380 / 10000000, 178885438 / 10000000000,
      1431083 / 10000000000⟩,
    ⟨3, 3, 10986122 / 10000000, 10986123 / 10000000, 162478273 / 10000000000,
      1158109 / 10000000000⟩,
    ⟨29, 1, 33672958 / 10000000, 33672959 / 10000000, 148594420 / 10000000000,
      951492 / 10000000000⟩,
    ⟨31, 1, 34339872 / 10000000, 34339873 / 10000000, 136709244 / 10000000000,
      792055 / 10000000000⟩,
    ⟨2, 5, 6931471 / 10000000, 6931472 / 10000000, 131390064 / 10000000000, 725834 / 10000000000⟩,
    ⟨37, 1, 36109179 / 10000000, 36109180 / 10000000, 109584175 / 10000000000,
      486906 / 10000000000⟩,
    ⟨41, 1, 37135720 / 10000000, 37135721 / 10000000, 96387380 / 10000000000, 367150 / 10000000000⟩,
    ⟨43, 1, 37612001 / 10000000, 37612002 / 10000000, 90816430 / 10000000000, 322078 / 10000000000⟩,
    ⟨47, 1, 38501476 / 10000000, 38501477 / 10000000, 81260160 / 10000000000, 252191 / 10000000000⟩,
    ⟨7, 2, 19459101 / 10000000, 19459102 / 10000000, 77135606 / 10000000000, 224885 / 10000000000⟩,
    ⟨53, 1, 39702919 / 10000000, 39702920 / 10000000, 69928653 / 10000000000, 181234 / 10000000000⟩,
    ⟨59, 1, 40775374 / 10000000, 40775375 / 10000000, 61155424 / 10000000000, 134945 / 10000000000⟩,
    ⟨61, 1, 41108738 / 10000000, 41108739 / 10000000, 58659412 / 10000000000, 123124 / 10000000000⟩,
    ⟨2, 6, 6931471 / 10000000, 6931472 / 10000000, 55242717 / 10000000000, 107895 / 10000000000⟩,
    ⟨67, 1, 42046926 / 10000000, 42046927 / 10000000, 52168277 / 10000000000, 95124 / 10000000000⟩,
    ⟨71, 1, 42626798 / 10000000, 42626799 / 10000000, 48520700 / 10000000000, 81103 / 10000000000⟩,
    ⟨73, 1, 42904594 / 10000000, 42904595 / 10000000, 46864762 / 10000000000, 75138 / 10000000000⟩,
    ⟨79, 1, 43694478 / 10000000, 43694479 / 10000000, 42458645 / 10000000000, 60467 / 10000000000⟩,
    ⟨3, 4, 10986122 / 10000000, 10986123 / 10000000, 41152263 / 10000000000, 56450 / 10000000000⟩,
    ⟨83, 1, 44188406 / 10000000, 44188407 / 10000000, 39916493 / 10000000000, 52788 / 10000000000⟩,
    ⟨89, 1, 44886363 / 10000000, 44886364 / 10000000, 36581582 / 10000000000, 43568 / 10000000000⟩,
    ⟨97, 1, 45747109 / 10000000, 45747110 / 10000000, 32849996 / 10000000000, 34385 / 10000000000⟩,
    ⟨101, 1, 46151205 / 10000000, 46151206 / 10000000, 31231891 / 10000000000, 30769 / 10000000000⟩,
    ⟨103, 1, 46347289 / 10000000, 46347290 / 10000000, 30475684 / 10000000000, 29153 / 10000000000⟩,
    ⟨107, 1, 46728288 / 10000000, 46728289 / 10000000, 29058305 / 10000000000, 26253 / 10000000000⟩,
    ⟨109, 1, 46913478 / 10000000, 46913479 / 10000000, 28393365 / 10000000000, 24950 / 10000000000⟩,
    ⟨113, 1, 47273878 / 10000000, 47273879 / 10000000, 27142631 / 10000000000, 22596 / 10000000000⟩,
    ⟨11, 2, 23978952 / 10000000, 23978953 / 10000000, 24918292 / 10000000000, 18721 / 10000000000⟩,
    ⟨5, 3, 16094379 / 10000000, 16094380 / 10000000, 23925580 / 10000000000, 17119 / 10000000000⟩,
    ⟨127, 1, 48441870 / 10000000, 48441871 / 10000000, 23455535 / 10000000000, 16388 / 10000000000⟩,
    ⟨2, 7, 6931471 / 10000000, 6931472 / 10000000, 23226701 / 10000000000, 16038 / 10000000000⟩]

/-- Look up the prime-power row with index n, using the zero default for missing
indices. Nonprime powers contribute zero in the rational aggregate. Successful
checks certify that every required prime-power index has a valid row. -/
private def anchor128Atom (n : ℕ) : AnchorEulerAtom :=
  (anchor128Atoms.find? (fun r ↦ r.p ^ r.k == n)).getD default

/-- For every prime-power index through 128, the rational atom checks succeed.
Kernel reduction verifies primality, exponent identities, Taylor logarithms and
fourth-power inequalities. This supplies all term hypotheses of the generic certificate. -/
private theorem anchor128_atom_checks :
    ∀ n ∈ Finset.Ioc 0 128, IsPrimePow n → anchorEulerAtomCheck 32 n (anchor128Atom n) = true := by
  decide +kernel

/-- The actual finite anchor constant at 128 is at least 3643/1000, unconditionally.
Verify anchor-log and fourth-power endpoints, all atom checks and the final rational
aggregate using kernel reduction, then apply certificate soundness. This replaces
the floating-point candidate with a Lean theorem. -/
theorem anchoredEulerConstant_128_ge : (3643 / 1000 : ℝ) ≤ anchoredEulerConstant 128 := by
  have hlog :=
    Analysis.rationalLogIntervalCheck_sound
      (by decide +kernel :
        Analysis.rationalLogIntervalCheck 128 8 32 0 (48520303 / 10000000 : ℚ) = true)
  have h1 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (by decide +kernel :
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 128
            (2973017787 / 10000000000 : ℚ) 1 1 4 =
          true)
  have h3 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (by decide +kernel :
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 128 0
            (262780130 / 10000000000 : ℚ) 3 4 =
          true)
  have h5 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (by decide +kernel :
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 128 0
            (23226702 / 10000000000 : ℚ) 5 4 =
          true)
  norm_num only [Rat.cast_ofNat, Nat.cast_ofNat] at hlog h1 h3 h5
  have hb :=
    anchorEulerRationalLower_le (N := 128) (terms := 32) (by norm_num only)
      (48520303 / 10000000 : ℚ) (2973017787 / 10000000000 : ℚ) (262780130 / 10000000000 : ℚ)
      (23226702 / 10000000000 : ℚ) anchor128Atom
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]
        exact hlog.2)
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div]
        exact h1.1)
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div]
        exact h3.2)
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div]
        exact h5.2)
      anchor128_atom_checks
  have hq :
    (3643 / 1000 : ℚ) ≤
      anchorEulerRationalLower 128 (48520303 / 10000000 : ℚ) (2973017787 / 10000000000 : ℚ)
        (262780130 / 10000000000 : ℚ) (23226702 / 10000000000 : ℚ) anchor128Atom := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at hb
  exact hr.trans hb

/-- Under RH and upper cutoff at least 128, the actual paired Euler prefix mass is
at least 3643/1000-5b^(-1/4). Insert the certified anchor constant into the generic
analytic tail theorem. This gives a compact explicit prefix saving at all larger cutoffs. -/
theorem pairedEulerPrefix_ge_anchor128 (hRH : RiemannHypothesis) {b : ℝ} (hb : 128 ≤ b) :
    (3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ) ≤ twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊b⌋₊) := by
  have hl := anchoredEulerConstant_sub_le_prefix hRH (by norm_num only : (1 : ℝ) < 128) hb
  linarith only [hl, anchoredEulerConstant_128_ge]

/-- For nonprincipal GRH data, an upper cutoff at least 128 and a positive variable-width
gap with the certified Euler saving, prime triviality below the ramp cutoff is impossible.
Use the closed-form identity and its nonnegative corrections before invoking the
witness theorem. No finite-anchor numerical premise remains. -/
theorem prime_trivial_false_of_certified_anchor128 {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x C b h : ℝ} (hx : 2 ≤ x) (hh : 0 < h) (hhx : h ≤ x) (hb : 128 ≤ b)
    (hcut : b ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap :
      0 <
        variableRampPrincipalLower x h - reflectedSplitUpper A C x +
          2 * ((3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ))) :
    ¬(∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  have hb0 : 0 < b := by linarith only [hb]
  have he := closedAnchoredEulerPrefix_eq_constant (a := (128 : ℝ)) hb0
  have h1 := Real.rpow_nonneg hb0.le (-3 / 4 : ℝ)
  have h2 := Real.rpow_nonneg hb0.le (-5 / 4 : ℝ)
  have hK := anchoredEulerConstant_128_ge
  apply
    prime_trivial_false_of_closedAnchoredEulerPrefix χ hne hqA hGRH hx hh hhx
      (by norm_num only : (1 : ℝ) < 128) hb hcut hC
  linarith only [hgap, he, h1, h2, hK]

end PseudoPrime.LLS
