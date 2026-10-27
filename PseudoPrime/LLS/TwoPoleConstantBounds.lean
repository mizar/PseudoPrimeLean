/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleSignedSharpBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TwoPoleGammaSignedConstant

/-! # Signed Gamma caps in parameterized two-pole witness bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under primitive GRH and a scalar Gamma-constant cap, retain both finite Euler savings in the
norm bound. The proof uses the triangle inequality and the two-pole zero-mass estimate; this
transfers signed Gamma bounds to oscillating zero sums. -/
theorem norm_gamma_oscillatingZeroSum_le_twoPole_constant {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) {C : ℝ}
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ ≤ C) (A B : Finset ℕ) :
    ‖∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ‖ ≤
      Real.log m / 2 + C -
        (∑ n ∈ A, AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (5 / 4) n) -
        (3 / 4 : ℝ) *
          (∑ n ∈ B,
            Real.log n *
              AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (11 / 4) n) := by
  have hs := MellinKernel.summable_oscillatingZeroTerm gammaMellinKernel hm hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (MellinKernel.norm_oscillatingZeroTerm gammaMellinKernel χ hx ρ).trans
      (norm_gamma_kernelZeroTerm_eq_twoPole hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  exact
    hn.trans
      (AnalyticNumberTheory.DirichletLFunction.gamma_zeroMass_le_twoPole_of_constant hm
          (hGRH m χ hp) hp hne hinv hC A B).2

/-- For a primitive nonprincipal character of conductor at most the ambient level, bound the
real smoothed sum using a scalar Gamma cap. Combine the zero-sum norm with the conductor-free
remainder; both finite Euler savings are retained for subsequent comparisons. -/
theorem gamma_primitive_sum_re_le_twoPole_constant {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) {C : ℝ}
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ ≤ C) (A B : Finset ℕ) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      Real.log m / 2 + C -
          (∑ n ∈ A, AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (5 / 4) n) -
          (3 / 4 : ℝ) *
            (∑ n ∈ B,
              Real.log n *
                AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (11 / 4) n) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hz :=
    norm_gamma_oscillatingZeroSum_le_twoPole_constant (by linarith only [hm] : 2 ≤ m) hGRH hp hne
      hinv (by linarith only [hx] : 0 < x) hC A B
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hz, hr, hn]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Given an ambient level, a scalar Gamma cap and a positive scale, define the arithmetic upper
bound by replacing the fixed Gamma constant. This is the parameterized input to the witness
comparison. -/
noncomputable def twoPoleConstantUpper (A : ℕ) (C x : ℝ) : ℝ :=
  signedTwoPoleUpper A x + C - 419 / 50

/-- Given an ambient level, a scalar Gamma cap and a scale, define the comparison gap as the
retained signed gap with its fixed Gamma cost replaced. Positivity excludes trivial values on
all primes below the cutoff. -/
noncomputable def twoPoleConstantGap (A : ℕ) (C x : ℝ) : ℝ :=
  signedTwoPoleGap A x + 419 / 50 - C

/-- For a nonprincipal character under GRH, bound its primitive smoothed sum at scale at least
two by the parameterized ambient upper bound. Enlarge the conductor to the ambient level after
applying the primitive estimate; this supplies the witness comparison. -/
theorem gamma_primitive_re_le_twoPoleConstant_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 2 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      twoPoleConstantUpper A C x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmA := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level).trans hqA
  have hb :=
    PaperStatements.gamma_primitive_sum_re_le_twoPole_constant (le_max_left 20000 A) hm
      (hmA.trans (le_max_right 20000 A)) hGRH hp hnp (inv_ne_one.mpr hnp) hx hC ∅ ∅
  simp only [Finset.sum_empty, mul_zero, sub_zero] at hb
  have hlog :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero))
      (Nat.cast_le.mpr hmA)
  dsimp only [twoPoleConstantUpper, signedTwoPoleUpper]
  linarith only [hb, hlog]

/-- For a quadratic nonprincipal character under GRH, bound the primitive sum plus its local
correction at scale at least four. Absorb the conductor saving into the local term and retain
the prime-factor cost for negative witnesses. -/
theorem gamma_primitive_add_local_le_twoPoleConstant_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 4 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        gammaQuadraticLocalCorrection χ x ≤
      twoPoleConstantUpper A C x +
        (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmA := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level).trans hqA
  have hb :=
    PaperStatements.gamma_primitive_sum_re_le_twoPole_constant (le_max_left 20000 A) hm
      (hmA.trans (le_max_right 20000 A)) hGRH hp hnp (inv_ne_one.mpr hnp)
      (by linarith only [hx] : 2 ≤ x) hC ∅ ∅
  simp only [Finset.sum_empty, mul_zero, sub_zero] at hb
  have hx0 : 0 < x := by linarith only [hx]
  have hs : 2 ≤ Real.sqrt x := by nlinarith only [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x, hx]
  have hl :=
    gammaQuadraticLocalCorrection_absorb_conductor χ hquad hx0
      (by linarith only [hx] : 1 ≤ (99 / 40 : ℝ) * x)
      (show 1 ≤ (1 / 2 : ℝ) * Real.sqrt x by linarith only [hs])
  have hlog :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))) (Nat.cast_le.mpr hqA)
  dsimp only [twoPoleConstantUpper, signedTwoPoleUpper]
  linarith only [hb, hl, hlog]

/-- For a logarithmic level at least 800 and controlled endpoint logarithms, bound the
paired-error numerator. Rational polynomial comparison gives a quadratic-linear expression used
in the parameterized gap estimate. -/
theorem twoPole_constant_error_algebra {L s A B : ℝ} (hL : 800 ≤ L) (hs : (3 / 5 : ℝ) * L ≤ s)
    (hA : A ≤ L / 40) (hB : B ≤ L / 40) :
    (3 / 2 : ℝ) * (s / 20 * (63 / 40) + (1839 / 1000) * A + 21 / 20) +
        42 *
          (((11 / 200 : ℝ) * s ^ 2 + 101 * ((2 / 25 : ℝ) * s + (1839 / 1000) * B + 21 / 20)) /
            494) ≤
      s * (s / 200 + 2) := by
  nlinarith only [hL, hs, hA, hB, sq_nonneg s]

/-- For logarithmic level at least 800 and a controlled positive root, give a linear lower bound
for the parameterized gap. Keep the Gamma cost symbolic and bound the principal, paired, pole
and left-line errors separately; later constants can be substituted without repeating the
analysis. -/
theorem twoPoleConstantGap_lower {q : ℕ} (hL : 800 ≤ Real.log q) {r C : ℝ}
    (hrange : (3 / 5 : ℝ) * Real.log q + 18 ≤ r)
    (hA : Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log q / 40)
    (hB : Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ Real.log q / 40) :
    (821 / 1000 : ℝ) * r - Real.log q / 2 - (C + 659 / 100) ≤ twoPoleConstantGap q C (r ^ 2) := by
  let L := Real.log q
  let x := r ^ 2
  let s := Real.sqrt x
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hrange, hL, sq_nonneg (r - 1)]
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hspos : 0 < s := Real.sqrt_pos.mpr hxpos
  have hs2 : s ^ 2 = x := Real.sq_sqrt hxpos.le
  have hr : 0 < r := by linarith only [hrange, hL]
  have hs : s = r := Real.sqrt_sq hr.le
  have hroot : (3 / 5 : ℝ) * L + 18 ≤ s := by
    rw [hs]; exact hrange
  have hlogx : Real.log x ≤ L / 40 :=
    (Real.log_le_log hxpos (show x ≤ (99 / 40 : ℝ) * x by linarith only [hxpos])).trans hA
  have hEa :=
    twoPole_constant_error_algebra hL (show (3 / 5 : ℝ) * L ≤ s by linarith only [hroot]) hA hB
  rw [hs2] at hEa
  have hE : gammaRampPairedErrorNumerator x / s ≤ s / 200 + 2 := by
    apply (div_le_iff₀ hspos).mpr
    dsimp only [gammaRampPairedErrorNumerator, rampSmoothedIncrementError,
      rampExtendedSmoothedError]
    rw [mul_comm x (99 / 40 : ℝ)]
    exact hEa.trans_eq (mul_comm _ _)
  have hP : (s / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / s ≤ 1 / 2 := by
    apply (div_le_iff₀ hspos).mpr
    nlinarith only [hlogx, hroot, hL]
  have hQ := twoPole_log_max_le_unconditional q
  have hPole : ((7 / 6 : ℝ) * Real.log (max 20000 q : ℕ) + 4) / s ≤ 2 := by
    apply (div_le_iff₀ hspos).mpr
    nlinarith only [hQ, hroot, hL]
  have hpow : x ^ (-9 / 16 : ℝ) ≤ s⁻¹ := by
    have h :=
      Real.rpow_le_rpow_of_exponent_le hx (show (-9 / 16 : ℝ) ≤ -(1 / 2 : ℝ) by norm_num only)
    rw [Real.rpow_neg hxpos.le, ← Real.sqrt_eq_rpow] at h
    exact h
  have hLeft : 43 * x ^ (-9 / 16 : ℝ) ≤ 9 / 100 := by
    calc
      _ ≤ 43 * s⁻¹ := mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 43)
      _ = 43 / s := by rw [div_eq_mul_inv]
      _ ≤ 9 / 100 := (div_le_iff₀ hspos).mpr (by nlinarith only [hroot, hL])
  have hmass :
    (831 / 1000 : ℝ) * s ≤
      (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * s :=
    mul_le_mul_of_nonneg_right
      ((by norm_num only : (831 / 1000 : ℝ) ≤ 83125234337 / 100000000000).trans
        Analysis.gamma_ramp_mass_lower)
      hspos.le
  dsimp only [twoPoleConstantGap, signedTwoPoleGap, signedTwoPoleUpper]
  nlinarith only [hE, hP, hPole, hLeft, hmass, hs, hL]

/-- For logarithmic level at least 800 and an additive root constant between 13 and 15, verify
the scale and endpoint conditions. A logarithmic tangent bound controls both endpoints and
supplies the hypotheses of the gap estimate. -/
theorem twoPoleConstant_root_data {L c : ℝ} (hL : 800 ≤ L) (hc : 13 ≤ c) (hc' : c ≤ 15) :
    let r := (500 / 821 : ℝ) * L + c;
    4 ≤ r ^ 2 ∧
      (3 / 5 : ℝ) * L + 18 ≤ r ∧
      Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ L / 40 ∧ Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 40 := by
  let r := (500 / 821 : ℝ) * L + c
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL, hc]
  have hlo : (3 / 5 : ℝ) * L + 18 ≤ r := by
    dsimp only [r]; linarith only [hL, hc]
  have hhi : r ≤ (63 / 100 : ℝ) * L := by
    dsimp only [r]; linarith only [hL, hc']
  have hs := mul_self_le_mul_self hr.le hhi
  have hx : 4 ≤ r ^ 2 := by nlinarith only [hlo, hL, sq_nonneg (r - 2)]
  have hLp : 0 < L := by linarith only [hL]
  have ht := twoPole_log_tangent hLp
  have hb : Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 40 := by
    have h :=
      Real.log_le_log (by nlinarith only [hx] : 0 < (101 / 40 : ℝ) * r ^ 2)
        (show (101 / 40 : ℝ) * r ^ 2 ≤ (101 / 100 : ℝ) * L ^ 2 by nlinarith only [hs])
    rw [Real.log_mul (by norm_num only : (101 / 100 : ℝ) ≠ 0) (pow_ne_zero 2 hLp.ne'),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hc0 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 101 / 100)
    linarith only [h, hc0, ht, hL]
  have ha :=
    Real.log_le_log (by nlinarith only [hx] : 0 < (99 / 40 : ℝ) * r ^ 2)
      (show (99 / 40 : ℝ) * r ^ 2 ≤ (101 / 40 : ℝ) * r ^ 2 by nlinarith only [hx])
  exact ⟨hx, hlo, ha.trans hb, hb⟩

/-- For logarithmic level at least 800 and additive constant between 13 and 15, bound the
affine-root gap by its constant margin. Substitute the root data into the linear gap bound; this
reduces witness existence to rational constant comparisons. -/
theorem twoPoleConstantGap_affine_margin {A : ℕ} (hL : 800 ≤ Real.log A) {c C : ℝ} (hc : 13 ≤ c)
    (hc' : c ≤ 15) :
    (821 / 1000 : ℝ) * c - (C + 659 / 100) ≤
      twoPoleConstantGap A C (((500 / 821 : ℝ) * Real.log A + c) ^ 2) := by
  have hd := twoPoleConstant_root_data hL hc hc'
  have h := twoPoleConstantGap_lower hL hd.2.1 hd.2.2.1 hd.2.2.2 (C := C)
  linarith only [h]

/-- For a nonprincipal character under GRH and a primitive Gamma cap, positivity of the
parameterized gap excludes triviality on all primes up to the cutoff. Compare the principal and
primitive sums and use the nonpositive local correction; this is the general-character witness
interface. -/
theorem prime_trivial_false_of_twoPoleConstantGap {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x C : ℝ} (hx : 2 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap : 0 < twoPoleConstantGap A C x) :
    ¬(∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro ht
  have hx0 : 0 < x := by linarith only [hx]
  have hb := gamma_primitive_re_le_twoPoleConstant_ambient χ hne hqA hGRH hx hC
  have hl :=
    gammaLocalCorrection_nonpos_of_level_primes_above χ hx0
      (fun p hp ↦ (level_prime_above_cutoff_of_all_prime_trivial χ ht hp).le)
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hN := gamma_ramp_no_witness_comparison_general χ hx0 (fun p hp _ hb0 ↦ ht p hp hb0)
  dsimp only [twoPoleConstantGap, signedTwoPoleGap] at hgap
  dsimp only [twoPoleConstantUpper] at hb
  linarith only [hb, hl, hP, hT, hN, hgap]

/-- For a quadratic nonprincipal character under GRH, a gap exceeding the local prime-factor
cost excludes triviality on all unit primes through the cutoff. Combine the local-corrected
primitive upper bound with the ramp comparison; this prepares negative witnesses. -/
theorem unit_prime_trivial_false_of_twoPoleConstantGap {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 4 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        twoPoleConstantGap A C x) :
    ¬(∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro ht
  have hb := gamma_primitive_add_local_le_twoPoleConstant_ambient χ hquad hne hqA hGRH hx hC
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hN := gamma_ramp_no_witness_comparison χ hquad (by linarith only [hx] : 0 < x) ht
  dsimp only [twoPoleConstantGap, signedTwoPoleGap] at hgap
  dsimp only [twoPoleConstantUpper] at hb
  linarith only [hb, hP, hT, hN, hgap]

/-- For a quadratic nonprincipal character under GRH, a gap exceeding the prime-factor cost
yields a prime not dividing the level with character value minus one. Extract a non-one unit
prime and use quadraticity to exclude zero and one; this is the negative-witness interface. -/
theorem exists_prime_neg_one_of_twoPoleConstantGap {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 4 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        twoPoleConstantGap A C x) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
    by_contra h
    apply unit_prime_trivial_false_of_twoPoleConstantGap χ hquad hne hqA hGRH hx hC hgap
    intro p hp hd hb
    exact Classical.byContradiction (fun hv ↦ h ⟨p, hp, hd, hb, hv⟩)
  obtain ⟨p, hp, hd, hb, hv⟩ := hex
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd))
  refine ⟨p, hp, hd, hb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hv h1)
  · exact hm

/-- For an even quadratic nonprincipal character of even level under GRH, an ambient logarithmic
level at least 800 yields an odd non-one prime within the displayed affine-square bound. Use the
even Gamma cap, the rational gap margin and the prime-two budget; this connects the improved
analysis to quadratic non-one witnesses. -/
theorem exists_odd_prime_ne_one_le_twoPoleConstant_even {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (heven : χ.Even) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 800 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log A + 271 / 20) ^ 2 ∧ χ p ≠ 1 := by
  let r := (500 / 821 : ℝ) * Real.log A + 271 / 20
  let x := r ^ 2
  have hd := twoPoleConstant_root_data hL (c := 271 / 20) (by norm_num only) (by norm_num only)
  have hx4 : 4 ≤ x := hd.1
  have hx : 2 ≤ x := by linarith only [hx4]
  have hxpos : 0 < x := by linarith only [hx]
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL]
  have hlocal : (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x ≤ 1 / 20 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hxpos)).mpr
    rw [Real.sqrt_sq hr.le]
    have hroot : (3 / 5 : ℝ) * Real.log A + 18 ≤ r := hd.2.1
    have hlog : Real.log ((99 / 40 : ℝ) * x) ≤ Real.log A / 40 := hd.2.2.1
    have ht := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    linarith only [hroot, hlog, ht, hL]
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      χ.primitiveCharacter ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven)
  have hsep :=
    twoPoleConstantGap_affine_margin hL (c := 271 / 20) (C := 112 / 25) (by norm_num only)
      (by norm_num only)
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hb := gamma_primitive_re_le_twoPoleConstant_ambient χ hne hqA hGRH hx hc
  apply
    exists_odd_prime_ne_one_of_gamma_ramp_gap χ hquad h2 hxpos
      (show 1 ≤ (99 / 40 : ℝ) * x by nlinarith only [hx])
  dsimp only [twoPoleConstantGap, signedTwoPoleGap] at hsep
  dsimp only [twoPoleConstantUpper] at hb
  nlinarith only [hP, hT, hb, hsep, hlocal]

end PseudoPrime.LLS
