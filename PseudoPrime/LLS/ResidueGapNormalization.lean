/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ResidueGapNumerics

/-! Main-term cancellation and normalization for refined residue-prime gaps. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Remaining error numerator after cancelling the principal and parity-averaged
character main terms. Here h is the totient, s the cutoff radius, L the modulus
logarithm, T a cutoff logarithm upper bound, U a prime-free residue-sum upper bound,
and w the number of distinct modulus primes. The terms retain the character
endpoint errors, principal correction and composite prime-power contribution.
Its quotient by h*s is used for shared interval certificates. -/
noncomputable def residueParityErrorNumerator (h s L T U w : ℝ) : ℝ :=
  h * U +
    (s + 19 / 6) *
      (693148 / 1000000 +
        ((h - 1) / 20 + (h - 2) * (T + 1 + 29 / 100) + h * (693148 / 1000000 + 29 / 100)) / s ^ 2) +
    (h - 1) *
      (19 / 6 * (L - 1719 / 1000) +
        (T ^ 2 + (2 / 3 * (L - 1144 / 1000) + 4) * T + T / 2 * (693148 / 1000000 + T))) +
    2 * (s + 19 / 6) * (T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s)) +
    (1839 / 1000 * T + 1 + (s + 1) / 20 + w * T ^ 2 / 2)

/-- Error after main-term cancellation, normalized by totient times cutoff radius.
Divide the retained error numerator by h*s. For positive h and s with h*L=s,
comparison with 1719/1000+(L-1719/1000)/h is equivalent to the original strict gap.
This exposes the constant margin before applying interval estimates. -/
noncomputable def residueParityNormalizedError (h s L T U w : ℝ) : ℝ :=
  residueParityErrorNumerator h s L T U w / (h * s)

/-- Exact main-term cancellation in the parity-averaged residue gap.
Assume the radius equals totient times the modulus logarithm. Expand the parity
upper bound and cancel its principal quadratic contribution algebraically.
The remaining margin and error numerator give a reusable identity for normalization. -/
theorem residueParity_gap_balance {h s L T U w : ℝ} (hL : h * L = s) :
    s ^ 2 - 1839 / 1000 * T - 1 - (s + 1) / 20 - w * T ^ 2 / 2 -
        residueParityIntervalUpper h (s ^ 2) s s L T -
        h * U =
      h * s * (1719 / 1000) + s * (L - 1719 / 1000) - residueParityErrorNumerator h s L T U w := by
  simp only [residueParityIntervalUpper, residueParityIntervalCoefficient,
    residueParityErrorNumerator]
  rw [← hL]
  ring

/-- For positive totient and cutoff radius, the normalized main-term margin equals
1719/1000+(L-1719/1000)/h. Split the quotient and cancel its nonzero factors.
This identifies the constant margin used in interval comparisons. -/
theorem residueParity_normalized_slack {h s L : ℝ} (hh : 0 < h) (hs : 0 < s) :
    (h * s * (1719 / 1000) + s * (L - 1719 / 1000)) / (h * s) =
      1719 / 1000 + (L - 1719 / 1000) / h := by
  rw [add_div, mul_div_cancel_left₀ _ (mul_pos hh hs).ne']
  rw [mul_comm h s, mul_div_mul_left _ _ hs.ne']

/-- For positive h and s with h*L=s, the normalized error lies below its margin
exactly when the parity upper bound and prime-free contribution lie below the
principal lower expression. Divide by the positive scale and apply the cancellation
identity. This transports normalized certificates to the strict analytic gap. -/
theorem residueParity_normalized_gap_iff {h s L T U w : ℝ} (hh : 0 < h) (hs : 0 < s)
    (hL : h * L = s) :
    residueParityNormalizedError h s L T U w < 1719 / 1000 + (L - 1719 / 1000) / h ↔
      h * U + residueParityIntervalUpper h (s ^ 2) s s L T <
        s ^ 2 - 1839 / 1000 * T - 1 - (s + 1) / 20 - w * T ^ 2 / 2 := by
  rw [residueParityNormalizedError, ← residueParity_normalized_slack hh hs,
    div_lt_div_iff_of_pos_right (mul_pos hh hs)]
  have he := residueParity_gap_balance (T := T) (U := U) (w := w) hL
  constructor <;> intro hc <;> linarith only [he, hc]

/-- Under GRH, a normalized parity gap bounds the least prime in a unit residue.
Assume the modulus lies from 64 through 20000, its totient is at least two, the
positive cutoff radius is totient times log q, and its square is at least 65536.
Supply the cutoff logarithm bound, the two interval sign guards and an upper bound
for the residue Mangoldt sum in the absence of a prime below the cutoff.
Convert the normalized gap, bound the character norms and compare with the principal
lower bound. This connects shared normalized estimates to Corollary 1.2. -/
theorem exists_least_prime_in_residue_le_of_normalized_parity_gap {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 64 ≤ q) (hu : q ≤ 20000) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {s T U : ℝ} (hh : (2 : ℝ) ≤ q.totient) (hs0 : 0 < s) (hs : (q.totient : ℝ) * Real.log q = s)
    (hx : 65536 ≤ s ^ 2) (hT : Real.log (s ^ 2) ≤ T)
    (hC : 0 ≤ residueParityIntervalCoefficient q.totient (s ^ 2) (Real.log q) T)
    (hR : 0 ≤ T - (1 + 23 / 40) + (1839 / 1000 : ℝ) / s ^ 2 + 1 / (20 * s))
    (hfree :
      (∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ s ^ 2) →
        (∑ n ∈ (Finset.Icc 1 ⌊s ^ 2⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
            AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm (s ^ 2) n) ≤
          U)
    (hgap :
      residueParityNormalizedError q.totient s (Real.log q) T U q.primeFactors.card <
        1719 / 1000 + (Real.log q - 1719 / 1000) / q.totient) :
    ∃ p : ℕ, IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ s ^ 2 := by
  have hh0 : (0 : ℝ) < q.totient := lt_of_lt_of_le (by norm_num only) hh
  have hsq := Real.sqrt_sq hs0.le
  have hn :=
    (nonprincipal_residue_logWeightedNorm_sum_le_parity_explicit hq hGRH hx).trans
      (residueNonprincipalParityUpper_le_interval hq hu hh hx (sq_pos_of_pos hs0) le_rfl hs0 hsq.ge
        hsq.le le_rfl hT hC hR)
  have hg := (residueParity_normalized_gap_iff hh0 hs0 hs).mp hgap
  have hp := cosetPrincipalLower_ge_interval (q := q) hx le_rfl hsq.le hT
  have he : (q.primeFactors.card : ℝ) * T ^ 2 / 2 = (1 / 2 : ℝ) * q.primeFactors.card * T ^ 2 := by
    ring
  rw [← he] at hp
  exact
    exists_least_prime_in_residue_le_of_weighted_gap a hGRH.riemann
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 65536) hx) hfree hn (hg.trans_le hp)

/-- For a positive totient parameter and nonnegative cutoff logarithm, dividing
the reciprocal parity numerator by the totient is bounded by T+2.323148.
Cross-multiplication removes the denominator; the omitted terms are nonpositive.
This bound removes the character count from the interval error estimate. -/
theorem reciprocalParityNumerator_div_le {h T : ℝ} (hh : 0 < h) (hT : 0 ≤ T) :
    ((h - 1) / 20 + (h - 2) * (T + 1 + 29 / 100) + h * (693148 / 1000000 + 29 / 100)) / h ≤
      T + 2323148 / 1000000 := by
  apply (div_le_iff₀ hh).mpr
  nlinarith only [hT]

/-- For a positive cutoff radius, split the normalized principal error into
1/(20*h) and a remainder with denominator h*s. Cancel the radius in its linear
term. This makes separate lower bounds for the totient and radius usable. -/
theorem principalResidueError_div_eq {h s T w : ℝ} (hs : 0 < s) :
    (1839 / 1000 * T + 1 + (s + 1) / 20 + w * T ^ 2 / 2) / (h * s) =
      1 / (20 * h) + (1839 / 1000 * T + 1 + 1 / 20 + w * T ^ 2 / 2) / (h * s) := by
  have hc : (s / 20) / (h * s) = 1 / (20 * h) := by
    rw [div_div, show (20 : ℝ) * (h * s) = s * (20 * h) by ring]
    simpa only [mul_one] using mul_div_mul_left (1 : ℝ) (20 * h) hs.ne'
  rw [show
      1839 / 1000 * T + 1 + (s + 1) / 20 + w * T ^ 2 / 2 =
        s / 20 + (1839 / 1000 * T + 1 + 1 / 20 + w * T ^ 2 / 2)
      by ring,
    add_div, hc]

/-- For positive totient and radius parameters, distribute the normalized
error into its prime-power, reciprocal, character endpoint and principal terms.
Cancel the nonzero common factors and split the principal linear term.
This identity exposes the factors to be bounded by shared interval endpoints. -/
theorem residueParityNormalizedError_eq {h s L T U w : ℝ} (hh : 0 < h) (hs : 0 < s) :
    residueParityNormalizedError h s L T U w =
      U / s +
        (1 + 19 / 6 / s) *
          ((693148 / 1000000 +
              ((h - 1) / 20 + (h - 2) * (T + 1 + 29 / 100) + h * (693148 / 1000000 + 29 / 100)) /
                s ^ 2) /
            h) +
        (1 - 1 / h) *
            (19 / 6 * (L - 1719 / 1000) +
              (T ^ 2 + (2 / 3 * (L - 1144 / 1000) + 4) * T + T / 2 * (693148 / 1000000 + T))) /
          s +
        2 / h * (1 + 19 / 6 / s) * (T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s)) +
        1 / (20 * h) +
        (1839 / 1000 * T + 1 + 1 / 20 + w * T ^ 2 / 2) / (h * s) := by
  have hc (v : ℝ) : (s + 19 / 6) * v / (h * s) = (1 + 19 / 6 / s) * (v / h) := by
    rw [← div_self hs.ne', ← add_div, div_mul_div_comm, mul_comm s h]
  have hm : (h - 1) / h = 1 - 1 / h := by rw [sub_div, div_self hh.ne']
  rw [residueParityNormalizedError, residueParityErrorNumerator, add_div, add_div, add_div, add_div]
  rw [mul_div_mul_left U s hh.ne', hc, principalResidueError_div_eq hs]
  rw [show
      2 * (s + 19 / 6) * (T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s)) =
        (s + 19 / 6) * (2 * (T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s)))
      by ring,
    hc]
  rw [← div_mul_div_comm (h - 1), hm]
  ring

/-- For positive h and nonnegative T, the normalized reciprocal correction is
bounded by 0.693148/h+(T+2.323148)/s^2. Split the constant term, commute the
divisions and apply the numerator bound. This supplies the reciprocal component
of a shared interval majorant; the radius may be arbitrary. -/
theorem reciprocalParityNormalized_le {h s T : ℝ} (hh : 0 < h) (hT : 0 ≤ T) :
    (693148 / 1000000 +
          ((h - 1) / 20 + (h - 2) * (T + 1 + 29 / 100) + h * (693148 / 1000000 + 29 / 100)) /
            s ^ 2) /
        h ≤
      693148 / 1000000 / h + (T + 2323148 / 1000000) / s ^ 2 := by
  rw [add_div, div_right_comm (b := s ^ 2) (c := h)]
  exact
    add_le_add le_rfl
      (div_le_div_of_nonneg_right (reciprocalParityNumerator_div_le hh hT) (sq_nonneg s))

/-- A normalized parity-error majorant with the reciprocal character count
removed. Replace that correction by 0.693148/h+(T+2.323148)/s^2 and retain the
remaining terms. Positive h and s and nonnegative T make this an upper bound
for the normalized error, suitable for shared interval certificates. -/
noncomputable def residueParityNormalizedMajorant (h s L T U w : ℝ) : ℝ :=
  U / s + (1 + 19 / 6 / s) * (693148 / 1000000 / h + (T + 2323148 / 1000000) / s ^ 2) +
    (1 - 1 / h) *
        (19 / 6 * (L - 1719 / 1000) +
          (T ^ 2 + (2 / 3 * (L - 1144 / 1000) + 4) * T + T / 2 * (693148 / 1000000 + T))) /
      s +
    2 / h * (1 + 19 / 6 / s) * (T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s)) +
    1 / (20 * h) +
    (1839 / 1000 * T + 1 + 1 / 20 + w * T ^ 2 / 2) / (h * s)

/-- For positive h and s and nonnegative T, the simplified expression bounds
the normalized parity error. Apply the reciprocal bound under its nonnegative
prefactor and keep the remaining summands unchanged. This reduces the arithmetic
required by normalized gap certificates. -/
theorem residueParityNormalizedError_le_majorant {h s L T U w : ℝ} (hh : 0 < h) (hs : 0 < s)
    (hT : 0 ≤ T) :
    residueParityNormalizedError h s L T U w ≤ residueParityNormalizedMajorant h s L T U w := by
  rw [residueParityNormalizedError_eq hh hs, residueParityNormalizedMajorant]
  have hp : 0 ≤ (1 : ℝ) + 19 / 6 / s := add_nonneg zero_le_one (div_nonneg (by norm_num only) hs.le)
  have hc := mul_le_mul_of_nonneg_left (reciprocalParityNormalized_le (s := s) hh hT) hp
  exact
    add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl hc) le_rfl) le_rfl) le_rfl)
      le_rfl

/-- For positive h and s with h*L=s and nonnegative T, a strict bound on the
simplified normalized majorant yields the original principal-versus-character gap.
Combine its upper-bound theorem with the normalized gap equivalence.
The resulting strict gap is used by the least-prime comparison theorem. -/
theorem residueParity_gap_of_normalized_majorant {h s L T U w : ℝ} (hh : 0 < h) (hs : 0 < s)
    (hT : 0 ≤ T) (hL : h * L = s)
    (hg : residueParityNormalizedMajorant h s L T U w < 1719 / 1000 + (L - 1719 / 1000) / h) :
    h * U + residueParityIntervalUpper h (s ^ 2) s s L T <
      s ^ 2 - 1839 / 1000 * T - 1 - (s + 1) / 20 - w * T ^ 2 / 2 := by
  exact
    (residueParity_normalized_gap_iff hh hs hL).mp
      ((residueParityNormalizedError_le_majorant hh hs hT).trans_lt hg)

end PseudoPrime.LLS.PaperStatements
