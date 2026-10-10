/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ResidueGapNormalization

/-! Shared interval estimates for the normalized parity residue-prime gap. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Character endpoint error after parity averaging. The two real inputs are the
modulus logarithm and cutoff logarithm bound. This polynomial is nonnegative
above the modulus threshold and increases in both arguments, permitting shared
upper-endpoint estimates in normalized residue gaps. -/
noncomputable def residueCharacterEndpointError (L T : ℝ) : ℝ :=
  19 / 6 * (L - 1719 / 1000) +
    (T ^ 2 + (2 / 3 * (L - 1144 / 1000) + 4) * T + T / 2 * (693148 / 1000000 + T))

/-- For L at least 1.719 and nonnegative T, the character endpoint error is
nonnegative. Expand the polynomial and use the nonnegative product (L-1.719)*T.
This supplies the sign needed to discard the factor 1-1/h. -/
theorem residueCharacterEndpointError_nonneg {L T : ℝ} (hL : 1719 / 1000 ≤ L) (hT : 0 ≤ T) :
    0 ≤ residueCharacterEndpointError L T := by
  have hm := mul_nonneg (sub_nonneg.mpr hL) hT
  simp only [residueCharacterEndpointError]
  nlinarith only [hL, hT, hm, sq_nonneg T]

/-- For L at least 1.719 and nonnegative T, increasing either logarithm does
not decrease the endpoint error. Express its difference through nonnegative
products. This permits evaluation at the upper logarithmic endpoints. -/
theorem residueCharacterEndpointError_le {L T L₁ T₁ : ℝ} (hL : 1719 / 1000 ≤ L) (hT : 0 ≤ T)
    (hLL : L ≤ L₁) (hTT : T ≤ T₁) :
    residueCharacterEndpointError L T ≤ residueCharacterEndpointError L₁ T₁ := by
  have hp := mul_nonneg (sub_nonneg.mpr hTT) (add_nonneg (hT.trans hTT) hT)
  have hq := mul_nonneg (sub_nonneg.mpr hLL) hT
  have hr := mul_nonneg (sub_nonneg.mpr hTT) (sub_nonneg.mpr (hL.trans hLL))
  simp only [residueCharacterEndpointError]
  nlinarith only [hLL, hTT, hT, hp, hq, hr]

/-- Assume positive h and a positive lower radius s₀, with s₀≤s, and logarithms
between their admissible lower bounds and supplied upper endpoints. Drop the
factor 1-1/h using endpoint nonnegativity, then enlarge the numerator and shrink
the denominator. This bounds the normalized endpoint contribution uniformly. -/
theorem residueCharacterEndpointError_normalized_le {h s s₀ L T L₁ T₁ : ℝ} (hh : 0 < h)
    (hs₀ : 0 < s₀) (hss : s₀ ≤ s) (hL : 1719 / 1000 ≤ L) (hT : 0 ≤ T) (hLL : L ≤ L₁)
    (hTT : T ≤ T₁) :
    (1 - 1 / h) * residueCharacterEndpointError L T / s ≤
      residueCharacterEndpointError L₁ T₁ / s₀ := by
  have hc : 1 - 1 / h ≤ (1 : ℝ) := sub_le_self _ (one_div_nonneg.mpr hh.le)
  have hn := residueCharacterEndpointError_nonneg hL hT
  have hm := mul_le_mul_of_nonneg_right hc hn
  rw [one_mul] at hm
  exact
    div_le_div₀ (residueCharacterEndpointError_nonneg (hL.trans hLL) (hT.trans hTT))
      (hm.trans (residueCharacterEndpointError_le hL hT hLL hTT)) hs₀ hss

/-- For a positive lower radius s₀≤s, the prefactor 1+19/(6s) is at most its
value at s₀. Compare the positive denominators. This is used by both reciprocal
components of the interval majorant. -/
theorem residueRadiusPrefactor_le {s₀ s : ℝ} (hs₀ : 0 < s₀) (hss : s₀ ≤ s) :
    (1 : ℝ) + 19 / 6 / s ≤ 1 + 19 / 6 / s₀ := by
  exact add_le_add le_rfl (div_le_div₀ (by norm_num only) le_rfl hs₀ hss)

/-- Given positive lower bounds for h and s and an upper bound T₁ for
nonnegative T, bound the normalized reciprocal correction at those endpoints.
Compare each quotient and multiply nonnegative bounds. This shares the parity
correction throughout an interval. -/
theorem reciprocalParityInterval_le {h₀ h s₀ s T T₁ : ℝ} (hh₀ : 0 < h₀) (hhh : h₀ ≤ h)
    (hs₀ : 0 < s₀) (hss : s₀ ≤ s) (hT : 0 ≤ T) (hTT : T ≤ T₁) :
    (1 + 19 / 6 / s) * (693148 / 1000000 / h + (T + 2323148 / 1000000) / s ^ 2) ≤
      (1 + 19 / 6 / s₀) * (693148 / 1000000 / h₀ + (T₁ + 2323148 / 1000000) / s₀ ^ 2) := by
  have hsq := (sq_le_sq₀ hs₀.le (hs₀.le.trans hss)).mpr hss
  have hq := div_le_div₀ (by norm_num only : (0 : ℝ) ≤ 693148 / 1000000) le_rfl hh₀ hhh
  have ht :=
    div_le_div₀ (show 0 ≤ T₁ + 2323148 / 1000000 by linarith only [hT, hTT]) (add_le_add hTT le_rfl)
      (sq_pos_of_pos hs₀) hsq
  apply mul_le_mul (residueRadiusPrefactor_le hs₀ hss) (add_le_add hq ht)
  · exact
      add_nonneg (div_nonneg (by norm_num only) (hh₀.le.trans hhh))
        (div_nonneg (by linarith only [hT]) (sq_nonneg s))
  · exact add_nonneg zero_le_one (div_nonneg (by norm_num only) hs₀.le)

/-- For a positive lower radius s₀≤s and T≤T₁, bound the reciprocal endpoint
expression by replacing the radius with s₀ and logarithm with T₁. Compare the
squared and linear denominators. This prepares its interval prefactor estimate. -/
theorem residueReciprocalEndpoint_le {s₀ s T T₁ : ℝ} (hs₀ : 0 < s₀) (hss : s₀ ≤ s) (hTT : T ≤ T₁) :
    T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s) ≤
      T₁ - (1 + 23 / 40) + 1839 / 1000 / s₀ ^ 2 + 1 / (20 * s₀) := by
  have hsq := (sq_le_sq₀ hs₀.le (hs₀.le.trans hss)).mpr hss
  have hq := div_le_div₀ (by norm_num only : (0 : ℝ) ≤ 1839 / 1000) le_rfl (sq_pos_of_pos hs₀) hsq
  have ht :=
    div_le_div₀ (show (0 : ℝ) ≤ 1 from zero_le_one) le_rfl
      (mul_pos (by norm_num only : (0 : ℝ) < 20) hs₀)
      (mul_le_mul_of_nonneg_left hss (by norm_num only : (0 : ℝ) ≤ 20))
  exact add_le_add (add_le_add (sub_le_sub_right hTT _) hq) ht

/-- Assume positive lower totient and radius bounds, an upper logarithm bound,
and a nonnegative reciprocal endpoint expression. Bound the two prefactors and
the endpoint expression separately and multiply the nonnegative bounds.
This supplies the reciprocal endpoint term of the interval majorant. -/
theorem residueReciprocalErrorInterval_le {h₀ h s₀ s T T₁ : ℝ} (hh₀ : 0 < h₀) (hhh : h₀ ≤ h)
    (hs₀ : 0 < s₀) (hss : s₀ ≤ s) (hTT : T ≤ T₁)
    (hR : 0 ≤ T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s)) :
    2 / h * (1 + 19 / 6 / s) * (T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s)) ≤
      2 / h₀ * (1 + 19 / 6 / s₀) * (T₁ - (1 + 23 / 40) + 1839 / 1000 / s₀ ^ 2 + 1 / (20 * s₀)) := by
  have hp := add_nonneg zero_le_one (div_nonneg (by norm_num only : (0 : ℝ) ≤ 19 / 6) hs₀.le)
  have hm :=
    mul_le_mul (div_le_div₀ (by norm_num only : (0 : ℝ) ≤ 2) le_rfl hh₀ hhh)
      (residueRadiusPrefactor_le hs₀ hss)
      (add_nonneg zero_le_one (div_nonneg (by norm_num only) (hs₀.le.trans hss)))
      (div_nonneg (by norm_num only) hh₀.le)
  exact
    mul_le_mul hm (residueReciprocalEndpoint_le hs₀ hss hTT) hR
      (mul_nonneg (div_nonneg (by norm_num only) hh₀.le) hp)

/-- For positive lower bounds on totient and radius, nonnegative T and w, and
upper bounds T₁ and W, the normalized principal correction is bounded at these
endpoints. Compare the squared logarithms and their nonnegative prime-count
weights, then enlarge the numerator and shrink the denominator. -/
theorem principalResidueErrorInterval_le {h₀ h s₀ s T T₁ w W : ℝ} (hh₀ : 0 < h₀) (hhh : h₀ ≤ h)
    (hs₀ : 0 < s₀) (hss : s₀ ≤ s) (hT : 0 ≤ T) (hTT : T ≤ T₁) (hw : 0 ≤ w) (hwW : w ≤ W) :
    (1839 / 1000 * T + 1 + 1 / 20 + w * T ^ 2 / 2) / (h * s) ≤
      (1839 / 1000 * T₁ + 1 + 1 / 20 + W * T₁ ^ 2 / 2) / (h₀ * s₀) := by
  have hsq := (sq_le_sq₀ hT (hT.trans hTT)).mpr hTT
  have hm := mul_le_mul hwW hsq (sq_nonneg T) (hw.trans hwW)
  have hn : 0 ≤ 1839 / 1000 * T₁ + 1 + 1 / 20 + W * T₁ ^ 2 / 2 := by
    have hp := mul_nonneg (hw.trans hwW) (sq_nonneg T₁)
    nlinarith only [hT, hTT, hp]
  exact
    div_le_div₀ hn (by linarith only [hTT, hm]) (mul_pos hh₀ hs₀)
      (mul_le_mul hhh hss hs₀.le (hh₀.le.trans hhh))

/-- Uniform normalized parity-error bound from lower totient h₀ and radius s₀,
upper logarithms L₁ and T₁, a bound A on the prime-free contribution divided by
the radius, and an upper distinct-prime count W. Its terms are obtained by the
component interval estimates. A value below 1.719 certifies the strict gap. -/
noncomputable def residueParityIntervalMajorant (h₀ s₀ L₁ T₁ A W : ℝ) : ℝ :=
  A + (1 + 19 / 6 / s₀) * (693148 / 1000000 / h₀ + (T₁ + 2323148 / 1000000) / s₀ ^ 2) +
    residueCharacterEndpointError L₁ T₁ / s₀ +
    2 / h₀ * (1 + 19 / 6 / s₀) * (T₁ - (1 + 23 / 40) + 1839 / 1000 / s₀ ^ 2 + 1 / (20 * s₀)) +
    1 / (20 * h₀) +
    (1839 / 1000 * T₁ + 1 + 1 / 20 + W * T₁ ^ 2 / 2) / (h₀ * s₀)

/-- Assume positive lower totient and radius bounds, admissible logarithms with
upper endpoints, a nonnegative prime count with upper bound, a normalized
prime-free bound, and the reciprocal sign guard. Apply the component estimates
and add them. This bounds the normalized error majorant throughout the interval. -/
theorem residueParityNormalizedMajorant_le_interval {h₀ h s₀ s L L₁ T T₁ U A w W : ℝ} (hh₀ : 0 < h₀)
    (hhh : h₀ ≤ h) (hs₀ : 0 < s₀) (hss : s₀ ≤ s) (hL : 1719 / 1000 ≤ L) (hLL : L ≤ L₁) (hT : 0 ≤ T)
    (hTT : T ≤ T₁) (hw : 0 ≤ w) (hwW : w ≤ W) (hU : U / s ≤ A)
    (hR : 0 ≤ T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s)) :
    residueParityNormalizedMajorant h s L T U w ≤
      residueParityIntervalMajorant h₀ s₀ L₁ T₁ A W := by
  have hc := reciprocalParityInterval_le hh₀ hhh hs₀ hss hT hTT
  have he := residueCharacterEndpointError_normalized_le (hh₀.trans_le hhh) hs₀ hss hL hT hLL hTT
  have hr := residueReciprocalErrorInterval_le hh₀ hhh hs₀ hss hTT hR
  have h1 :=
    div_le_div₀ (show (0 : ℝ) ≤ 1 from zero_le_one) le_rfl
      (mul_pos (by norm_num only : (0 : ℝ) < 20) hh₀)
      (mul_le_mul_of_nonneg_left hhh (by norm_num only : (0 : ℝ) ≤ 20))
  have hp := principalResidueErrorInterval_le hh₀ hhh hs₀ hss hT hTT hw hwW
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hU hc) he) hr) h1) hp

/-- With the component interval hypotheses and h*L=s, an interval majorant
strictly below 1.719 implies the original principal-versus-character gap.
The remaining logarithmic margin is nonnegative. Combine the interval estimate
with the normalized gap equivalence to feed the least-prime comparison. -/
theorem residueParity_gap_of_interval {h₀ h s₀ s L L₁ T T₁ U A w W : ℝ} (hh₀ : 0 < h₀)
    (hhh : h₀ ≤ h) (hs₀ : 0 < s₀) (hss : s₀ ≤ s) (hL : 1719 / 1000 ≤ L) (hLL : L ≤ L₁) (hT : 0 ≤ T)
    (hTT : T ≤ T₁) (hw : 0 ≤ w) (hwW : w ≤ W) (hU : U / s ≤ A)
    (hR : 0 ≤ T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s)) (hsL : h * L = s)
    (hg : residueParityIntervalMajorant h₀ s₀ L₁ T₁ A W < 1719 / 1000) :
    h * U + residueParityIntervalUpper h (s ^ 2) s s L T <
      s ^ 2 - 1839 / 1000 * T - 1 - (s + 1) / 20 - w * T ^ 2 / 2 := by
  have hn := residueParityNormalizedMajorant_le_interval hh₀ hhh hs₀ hss hL hLL hT hTT hw hwW hU hR
  have hm : 1719 / 1000 ≤ 1719 / 1000 + (L - 1719 / 1000) / h :=
    le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hL) (hh₀.le.trans hhh))
  exact
    residueParity_gap_of_normalized_majorant (hh₀.trans_le hhh) (hs₀.trans_le hss) hT hsL
      ((hn.trans_lt hg).trans_le hm)

/-- Under GRH, a uniform parity interval certificate bounds the least prime
in a unit residue. Assume a modulus from 64 through 20000, the existing cutoff
and sign guards, lower totient and radius bounds, upper logarithm and prime-count
bounds, and a normalized prime-free Mangoldt estimate. A majorant below 1.719
implies the strict analytic gap. Apply the normalized least-prime theorem.
This is the consumer for shared interval certificates in Corollary 1.2. -/
theorem exists_least_prime_in_residue_le_of_parity_interval {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 64 ≤ q) (hu : q ≤ 20000) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {h₀ s₀ s L₁ T T₁ U A W : ℝ} (hh : (2 : ℝ) ≤ q.totient) (hh₀ : 0 < h₀) (hhh : h₀ ≤ q.totient)
    (hs₀ : 0 < s₀) (hss : s₀ ≤ s) (hs : (q.totient : ℝ) * Real.log q = s) (hx : 65536 ≤ s ^ 2)
    (hL : 1719 / 1000 ≤ Real.log q) (hLL : Real.log q ≤ L₁) (hT : 0 ≤ T)
    (hTx : Real.log (s ^ 2) ≤ T) (hTT : T ≤ T₁) (hwW : (q.primeFactors.card : ℝ) ≤ W)
    (hU : U / s ≤ A) (hC : 0 ≤ residueParityIntervalCoefficient q.totient (s ^ 2) (Real.log q) T)
    (hR : 0 ≤ T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s))
    (hfree :
      (∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ s ^ 2) →
        (∑ n ∈ (Finset.Icc 1 ⌊s ^ 2⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
            AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm (s ^ 2) n) ≤
          U)
    (hg : residueParityIntervalMajorant h₀ s₀ L₁ T₁ A W < 1719 / 1000) :
    ∃ p : ℕ, IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ s ^ 2 := by
  have hn :=
    residueParityNormalizedMajorant_le_interval hh₀ hhh hs₀ hss hL hLL hT hTT
      (Nat.cast_nonneg q.primeFactors.card) hwW hU hR
  have he :=
    residueParityNormalizedError_le_majorant (L := Real.log q) (U := U) (w := q.primeFactors.card)
      (hh₀.trans_le hhh) (hs₀.trans_le hss) hT
  have hm : 1719 / 1000 ≤ 1719 / 1000 + (Real.log q - 1719 / 1000) / q.totient :=
    le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hL) (hh₀.le.trans hhh))
  exact
    exists_least_prime_in_residue_le_of_normalized_parity_gap a hq hu hGRH hh (hs₀.trans_le hss) hs
      hx hTx hC hR hfree (((he.trans hn).trans_lt hg).trans_le hm)

end PseudoPrime.LLS.PaperStatements
