/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroConjugateSum
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroEnumerationCount

/-! # Phase representation of a signed critical-line zero sum -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For a real logarithmic height and a finite list of ordinates, this is
twice the real part of the normalized critical-line exponential sum. It is
the signed head retained in the midpoint ψ estimate. -/
@[expose]
noncomputable def zeroHeadPhase {n : ℕ} (g : Fin n → ℝ) (v : ℝ) : ℝ :=
  2 *
    (∑ i,
        Complex.exp (((g i * v : ℝ) : ℂ) * Complex.I) /
          (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I)).re

/-- For a positive real base, conjugating the exponent of its complex power
does not change the real part of the quotient by that exponent. This lets
the signed zero sum be paired across the real axis. -/
theorem re_cpow_div_conj {t : ℝ} (ht : 0 < t) (ρ : ℂ) :
    (((t : ℂ) ^ ((starRingEnd ℂ) ρ)) / ((starRingEnd ℂ) ρ)).re = (((t : ℂ) ^ ρ) / ρ).re := by
  have harg : ((t : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne'.symm
  have hcp := Complex.cpow_conj (t : ℂ) ρ harg
  rw [Complex.conj_ofReal] at hcp
  rw [hcp, ← map_div₀, Complex.conj_re]

/-- A critical-line power of a positive real base factors into its square
root and an exponential with phase ordinate times logarithmic base. -/
theorem cpow_critical_phase {t : ℝ} (ht : 0 < t) (g : ℝ) :
    (t : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (g : ℂ) * Complex.I) =
      (Real.sqrt t : ℂ) * Complex.exp (((g * Real.log t : ℝ) : ℂ) * Complex.I) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [Complex.cpow_add _ _ ht0, ← Complex.ofReal_cpow ht.le, ← Real.sqrt_eq_rpow]
  congr 1
  rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le, Complex.ofReal_mul]
  congr 1
  ring

/-- Under RH, a complete simple positive-height enumeration converts the
signed head at a positive real base to twice the real part of its positive
part. Conjugation preserves both multiplicities and real parts. -/
theorem zero_head_eq_positive_sum (hRH : RiemannHypothesis) {T t : ℝ} (hT : 0 ≤ T) (ht : 0 < t)
    {n : ℕ} (z : Fin n → ℂ) (hinj : Function.Injective z)
    (hledger : (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im) = Finset.univ.image z)
    (hm : ∀ i, riemannZetaZeroMultiplicity (z i) = 1) :
    (∑ ρ ∈ zerosUpTo T, (riemannZetaZeroMultiplicity ρ : ℂ) * ((t : ℂ) ^ ρ / ρ)).re =
      2 * (∑ i, ((t : ℂ) ^ (z i) / z i)).re := by
  simp only [Complex.re_sum, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  have h :=
    zero_sum_eq_two_positive hRH hT
      (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ) * (((t : ℂ) ^ ρ) / ρ).re)
      (by
        intro ρ hρ
        have hz := (mem_zerosUpTo hT).1 hρ
        have hr :=
          RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
            (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2.1)
        have hne : ρ ≠ 1 := by
          intro he
          rw [he, Complex.one_re] at hr
          norm_num only at hr
        rw [multiplicity_conj hne, re_cpow_div_conj ht])
  rw [h, hledger, Finset.sum_image]
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hm i]
    norm_num only [Nat.cast_one, one_mul]
  · intro a ha b hb hab
    exact hinj hab

/-- Under RH, a complete simple enumeration by positive critical-line
ordinates expresses the signed zero head as the square root of the base
times its phase sum at the logarithm of the base. -/
theorem zero_head_eq_phase (hRH : RiemannHypothesis) {T t : ℝ} (hT : 0 ≤ T) (ht : 0 < t) {n : ℕ}
    (g : Fin n → ℝ) (hinj : Function.Injective (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I))
    (hledger :
      (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im) =
        Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I))
    (hm : ∀ i, riemannZetaZeroMultiplicity (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 1) :
    (∑ ρ ∈ zerosUpTo T, (riemannZetaZeroMultiplicity ρ : ℂ) * ((t : ℂ) ^ ρ / ρ)).re =
      Real.sqrt t * zeroHeadPhase g (Real.log t) := by
  rw [zero_head_eq_positive_sum hRH hT ht _ hinj hledger hm]
  simp only [cpow_critical_phase ht, mul_div_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul,
    zeroHeadPhase]
  ring

/-- Under RH, distinct positive critical-line zeros through T and a total
count at most twice their number exhaust the positive ledger and are simple.
This turns an ordinate enumeration and count bound into the phase interface. -/
theorem critical_ledger_of_count (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) {n : ℕ}
    (g : Fin n → ℝ) (hinj : Function.Injective g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ T)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount T ≤ 2 * n) :
    (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im) =
        Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) ∧
      ∀ i, riemannZetaZeroMultiplicity (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 1 := by
  let z : Fin n → ℂ := fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  have hz : ∀ i, z i ∈ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im) := by
    intro i
    have him : (z i).im = g i := by
      simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_zerosUpTo hT).2
      refine ⟨hzero i, ?_, ?_⟩
      · simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        norm_num only
      · rw [him, abs_of_pos (hpos i)]
        exact hheight i
    · rw [him]
      exact hpos i
  have hp := positive_ledger_of_count hT hRH z (critical_points_injective g hinj) hz hcount
  exact ⟨hp.1.symm, fun i ↦ hp.2 (z i) (hz i)⟩

/-- Under RH, distinct positive critical-line zeros and a matching count
bound identify the signed head with the normalized finite phase sum. -/
theorem zero_head_phase_of_count (hRH : RiemannHypothesis) {T t : ℝ} (hT : 0 ≤ T) (ht : 0 < t)
    {n : ℕ} (g : Fin n → ℝ) (hinj : Function.Injective g) (hpos : ∀ i, 0 < g i)
    (hheight : ∀ i, g i ≤ T)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount T ≤ 2 * n) :
    (∑ ρ ∈ zerosUpTo T, (riemannZetaZeroMultiplicity ρ : ℂ) * ((t : ℂ) ^ ρ / ρ)).re =
      Real.sqrt t * zeroHeadPhase g (Real.log t) := by
  have h := critical_ledger_of_count hRH hT g hinj hpos hheight hzero hcount
  exact zero_head_eq_phase hRH hT ht g (critical_points_injective g hinj) h.1 h.2

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
