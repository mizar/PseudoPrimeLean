/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxAbel656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosine656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxEuler656

/-! # Forward and reflected Euler series for the section 132 symmetric kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem quarter_symmetric_neg_656 (z : ℂ) :
    quarterSymmetricKernel656 (-z) = quarterSymmetricKernel656 z := by
  unfold quarterSymmetricKernel656
  rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm ((11 / 10 : ℂ) + z)]

/-- Reflection interchanges the two lines of real parts ±9/16 and inverts the
scale in the power weight. Evenness preserves the symmetric kernel itself. -/
theorem quarter_reflect_symmetric_line_656 (H : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    (∫ t : ℝ, H (-(l t)) * (quarterSymmetricKernel656 (l t) * (x : ℂ) ^ l t)) =
      ∫ t : ℝ, H (r t) * (quarterSymmetricKernel656 (r t) * ((x⁻¹ : ℝ) : ℂ) ^ r t) := by
  intro l r
  let F := fun t : ℝ ↦ H (r t) * (quarterSymmetricKernel656 (r t) * ((x⁻¹ : ℝ) : ℂ) ^ r t)
  have hr (t : ℝ) : r (-t) = -(l t) := by
    dsimp only [r, l]
    push_cast
    ring
  have he (t : ℝ) : H (-(l t)) * (quarterSymmetricKernel656 (l t) * (x : ℂ) ^ l t) = F (-t) := by
    simp only [F, hr, quarter_symmetric_neg_656, Complex.ofReal_inv, Complex.cpow_neg,
      Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he)]
  exact MeasureTheory.integral_neg_eq_self F MeasureTheory.volume

/-- The reflected ordinary logarithmic derivative for the symmetric kernel has
the exact forward arithmetic sum at reciprocal scale, with its minus sign. -/
theorem quarter_reflected_prime_sum_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.LFunction (-(l t) + 1 / 2) *
            (quarterSymmetricKernel656 (l t) * (x : ℂ) ^ l t)) =
      ∑' n, quarterSymmetricMellin656.summand χ x⁻¹ n := by
  intro l
  have h := quarter_reflect_symmetric_line_656 (fun s ↦ -logDeriv χ.LFunction (s + 1 / 2)) hx
  dsimp only at h
  dsimp only [l]
  rw [h]
  exact
    (LLS.PaperStatements.MellinKernel.tsum_summand_eq_integral_logDeriv quarterSymmetricMellin656 χ
        (inv_pos.mpr hx) (by norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)).symm

/-- The constant logarithmic conductor integrates on the left line to the
continuous symmetric profile at the reciprocal scale. -/
theorem quarter_left_conductor_656 (q : ℕ) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, Complex.log q * (quarterSymmetricKernel656 (l t) * (x : ℂ) ^ l t)) =
      Complex.log q * (quarterSymmetricProfile656 x⁻¹ : ℂ) := by
  intro l
  have h :=
    symmetric_line_inversion (c := -9 / 16) (by norm_num only) (by norm_num only) (inv_pos.mpr hx)
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  rw [MeasureTheory.integral_const_mul, mul_left_comm, ← h]

/-- The real symmetric arithmetic summand at any positive scale, also at n = 0
where the von Mangoldt factor vanishes. -/
theorem quarter_symmetric_summand_656 {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (n : ℕ) :
    (quarterSymmetricMellin656.summand χ x n).re =
      (χ n).re *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile656 (n / x)) := by
  by_cases hn : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re,
      ArithmeticFunction.map_zero, zero_div, zero_mul, mul_zero]
  · have hy := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
    have ht :
      quarterSymmetricMellin656.transform (n / x) = (quarterSymmetricProfile656 (n / x) : ℂ) :=
      symmetric_line_inversion (c := 0) (by norm_num only) (by norm_num only) hy
    rw [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn, ht, mul_comm _ (χ n)]
    rw [mul_assoc, ← Complex.ofReal_mul, Complex.mul_re]
    simp only [Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero]

/-- The real reflected logarithmic derivative is the von Mangoldt series at
reciprocal scale. Its profile argument is n times the original scale. -/
theorem quarter_reflected_euler_series_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.LFunction (-(l t) + 1 / 2) *
              (quarterSymmetricKernel656 (l t) * (x : ℂ) ^ l t))).re =
      ∑' n : ℕ,
        (χ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            quarterSymmetricProfile656 (n * x)) := by
  intro l
  rw [quarter_reflected_prime_sum_656 χ hx,
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand quarterSymmetricMellin656 χ
        (inv_pos.mpr hx))]
  apply tsum_congr
  intro n
  simpa only [div_inv_eq_mul] using (quarter_symmetric_summand_656 χ (inv_pos.mpr hx) n)

/-- Absolute integrability on the reflected line permits subtraction of the
character and zeta logarithmic derivatives before taking real parts. -/
theorem quarter_reflected_integrable_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        -logDeriv χ.LFunction (-(l t) + 1 / 2) *
          (quarterSymmetricKernel656 (l t) * (x : ℂ) ^ l t)) := by
  intro l
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  have h :=
    LLS.PaperStatements.MellinKernel.integrable_arithmeticMellin_logDeriv quarterSymmetricMellin656
      χ (inv_pos.mpr hx) (c := 9 / 16) (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  apply h.comp_neg.congr
  apply Filter.Eventually.of_forall
  intro t
  change
    -logDeriv χ.LFunction (r (-t) + 1 / 2) *
        (quarterSymmetricKernel656 (r (-t)) * ((x⁻¹ : ℝ) : ℂ) ^ r (-t)) =
      _
  have hr : r (-t) = -(l t) := by
    dsimp only [r, l]
    push_cast
    ring
  simp only [hr, quarter_symmetric_neg_656, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv]

/-- The reflected difference of ordinary logarithmic derivatives contributes
the principal Euler series minus the character Euler series. -/
theorem quarter_reflected_euler_difference_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let A := fun {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) (t : ℝ) ↦
      -logDeriv ψ.LFunction (-(l t) + 1 / 2) * (quarterSymmetricKernel656 (l t) * (x : ℂ) ^ l t)
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      ∑' n : ℕ,
        (ψ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile656 (n * x))
    let ψ := (1 : DirichletCharacter ℂ 1)
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, A ψ t - A χ t)).re = S ψ - S χ := by
  intro l A S ψ
  rw [MeasureTheory.integral_sub (quarter_reflected_integrable_656 ψ hx)
      (quarter_reflected_integrable_656 χ hx),
    mul_sub, Complex.sub_re]
  exact
    congrArg₂ (· - ·) (quarter_reflected_euler_series_656 ψ hx)
      (quarter_reflected_euler_series_656 χ hx)

/-- The ordinary Euler sum for the symmetric profile at positive scale y. -/
noncomputable def quarterSymmetricSum656 {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) : ℝ :=
  ∑' n : ℕ,
    (χ n).re * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile656 (n / y))

/-- When the character is one on primes through X, its symmetric Euler deficit
is supported above floor X at every positive scale. -/
theorem quarter_profile_tail_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {X y : ℝ}
    (hX : 0 ≤ X) (hy : 0 < y) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    quarterSymmetricSum656 (1 : DirichletCharacter ℂ 1) y - quarterSymmetricSum656 χ y =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        (1 - (χ n.val).re) *
          (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
            quarterSymmetricProfile656 (n.val / y)) := by
  let W := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile656 (n / y)
  have hs {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) :
    Summable (fun n : ℕ ↦ (ψ n).re * W n) := by
    have h := LLS.PaperStatements.MellinKernel.summable_summand quarterSymmetricMellin656 ψ hy
    exact
      ((Complex.hasSum_re h.hasSum).congr_fun
          (fun n ↦ (quarter_symmetric_summand_656 ψ hy n).symm)).summable
  unfold quarterSymmetricSum656
  rw [← (hs (1 : DirichletCharacter ℂ 1)).tsum_sub (hs χ)]
  let F := fun n : ℕ ↦ (1 - (χ n).re) * W n
  have he (n : ℕ) : ((1 : DirichletCharacter ℂ 1) n).re * W n - (χ n).re * W n = F n := by
    simp only [F, MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, sub_mul]
  rw [tsum_congr he]
  symm
  apply tsum_subtype_eq_of_support_subset (f := F) (s := {n : ℕ | ⌊X⌋₊ < n})
  intro n hn
  by_contra hno
  have hcut := (Nat.le_floor_iff hX).mp (le_of_not_gt hno)
  apply hn
  by_cases hm : ArithmeticFunction.vonMangoldt n = 0
  · simp only [F, W, hm, zero_div, zero_mul, mul_zero]
  simp only [F,
    AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero χ hp hcut hm,
    Complex.one_re, sub_self, zero_mul]

/-- At one positive scale the three absolutely convergent character tails
combine into one series weighted by three minus the trace. -/
theorem quarter_trace_tail_hasSum_656 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ)
    {y : ℝ} (hy : 0 < y) :
    let W := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile656 (n / y)
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) ↦
      ∑' k : { k : ℕ // ⌊X⌋₊ < k }, (1 - (χ k.val).re) * W k.val
    HasSum
      (fun k : { k : ℕ // ⌊X⌋₊ < k } ↦ (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) * W k.val)
      (E a + E b + E c) := by
  intro W E
  have hs {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Summable (fun n : ℕ ↦ (χ n).re * W n) := by
    have h := LLS.PaperStatements.MellinKernel.summable_summand quarterSymmetricMellin656 χ hy
    exact
      ((Complex.hasSum_re h.hasSum).congr_fun
          (fun n ↦ (quarter_symmetric_summand_656 χ hy n).symm)).summable
  have hW : Summable W := by
    apply (hs (1 : DirichletCharacter ℂ 1)).congr
    intro n
    simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul]
  have hE {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Summable (fun k : { k : ℕ // ⌊X⌋₊ < k } ↦ (1 - (χ k.val).re) * W k.val) := by
    apply ((hW.sub (hs χ)).subtype _).congr
    intro k
    change W k.val - (χ k.val).re * W k.val = _
    rw [sub_mul, one_mul]
  dsimp only [E]
  apply (((hE a).hasSum.add (hE b).hasSum).add (hE c).hasSum).congr_fun
  intro k
  ring

/-- Summing the trace-weighted series recovers the three individual tails. -/
theorem quarter_trace_tail_eq_656 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ)
    {y : ℝ} (hy : 0 < y) :
    let W := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile656 (n / y)
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) ↦
      ∑' k : { k : ℕ // ⌊X⌋₊ < k }, (1 - (χ k.val).re) * W k.val
    E a + E b + E c =
      ∑' k : { k : ℕ // ⌊X⌋₊ < k },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) * W k.val := by
  exact (quarter_trace_tail_hasSum_656 a b c X hy).tsum_eq.symm

private theorem symmetric_profile_value {u : ℝ} (hu : 0 < u) :
    quarterSymmetricProfile656 u =
      Real.exp (-(11 / 10) * |Real.log u|) * quarterAuxProfile656 |Real.log u| / 2 := by
  have h := symmetric_line_inversion (c := 0) (by norm_num only) (by norm_num only) hu
  change quarterSymmetricMellin656.transform u = _ at h
  rw [quarter_symmetric_transform_656 hu] at h
  have he := congrArg Complex.re h
  simp only [Complex.ofReal_re] at he
  rw [← he]
  unfold quarterAuxProfile656
  ring

/-- The two Euler profiles at reciprocal scales have the common decay
factor times the paired quadratic whenever log u exceeds the frequency. -/
theorem quarter_cosine_profile_pair_656 {u : ℝ} (hu : 0 < u) {s : ℝ} (hs : |s| ≤ Real.log u) :
    quarterSymmetricProfile656 (u / Real.exp |s|) +
        quarterSymmetricProfile656 (u / (Real.exp |s|)⁻¹) =
      Real.exp (-(11 / 10) * Real.log u) * quarterAuxPair656 s (Real.log u) := by
  have hp := Real.exp_pos |s|
  have hm : 0 ≤ Real.log u - |s| := sub_nonneg.mpr hs
  have ha : 0 ≤ Real.log u + |s| := add_nonneg ((abs_nonneg s).trans hs) (abs_nonneg s)
  rw [symmetric_profile_value (div_pos hu hp),
    symmetric_profile_value (div_pos hu (inv_pos.mpr hp)), Real.log_div hu.ne' hp.ne',
    Real.log_div hu.ne' (inv_ne_zero hp.ne'), Real.log_inv, Real.log_exp, sub_neg_eq_add,
    abs_of_nonneg hm, abs_of_nonneg ha]
  unfold quarterAuxPair656
  rw [mul_sub, mul_add, Real.exp_sub, Real.exp_add,
    show -(11 / 10 : ℝ) * |s| = -((11 / 10) * |s|) by ring, Real.exp_neg]
  simp only [div_eq_mul_inv, inv_inv]
  ring

/-- The trace-weighted Euler tail for a signed frequency uses both reciprocal
scales and only those integers beyond the tested cutoff. -/
noncomputable def quarterCosineTail656 {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X s : ℝ) : ℝ :=
  ∑' n : { n : ℕ // ⌊X⌋₊ < n },
    (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
      (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
        (quarterSymmetricProfile656 (n.val / Real.exp |s|) +
          quarterSymmetricProfile656 (n.val / (Real.exp |s|)⁻¹)))

private theorem aux_mix_tsum {ι : Type*} (F : ℝ → ι → ℝ) (hf : ∀ s, Summable (F s)) :
    quarterAuxMix656 (fun s ↦ ∑' n, F s n) = ∑' n, quarterAuxMix656 (fun s ↦ F s n) := by
  let f := fun i ↦ F (quarterAuxFrequency656 i)
  let g := fun i j ↦ F (quarterAuxFrequency656 i - quarterAuxFrequency656 j)
  let c := quarterAuxCoeff656
  have hp (i j : Fin 7) : Summable (fun n ↦ c i * c j * g i j n) := (hf _).mul_left _
  have hrow (i : Fin 7) : Summable (fun n ↦ ∑ j, c i * c j * g i j n) :=
    summable_sum (fun j _ ↦ hp i j)
  have hP : Summable (fun n ↦ ∑ i, ∑ j, c i * c j * g i j n) := summable_sum (fun i _ ↦ hrow i)
  have hS (i : Fin 7) : Summable (fun n ↦ c i * f i n) := (hf _).mul_left _
  have hSS : Summable (fun n ↦ ∑ i, c i * f i n) := summable_sum (fun i _ ↦ hS i)
  have h := Summable.tsum_sub (hP.div_const 2) hSS
  rw [tsum_div_const, Summable.tsum_finsetSum (fun i _ ↦ hrow i),
    Summable.tsum_finsetSum (fun i _ ↦ hS i)] at h
  simpa only [quarterAuxMix656, f, g, c, Summable.tsum_finsetSum (fun j _ ↦ hp _ j),
    tsum_mul_left] using h.symm

private theorem aux_frequency_abs_le (i : Fin 7) : |quarterAuxFrequency656 i| ≤ 10 := by
  have h : ∀ j : Fin 7, quarterAuxShift656 j ≤ 64 / 10 := by decide +kernel
  have hi := (Rat.cast_le (K := ℝ)).mpr (h i)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hi
  rw [abs_of_nonneg ((by norm_num only : (0 : ℝ) ≤ 21 / 8).trans (quarter_aux_frequency_ge_656 i))]
  unfold quarterAuxFrequency656
  linarith only [hi]

private theorem aux_frequency_diff_le (i j : Fin 7) :
    |quarterAuxFrequency656 i - quarterAuxFrequency656 j| ≤ 10 := by
  have hi := abs_le.mp (aux_frequency_abs_le i)
  have hj := abs_le.mp (aux_frequency_abs_le j)
  have hi' := quarter_aux_frequency_ge_656 i
  have hj' := quarter_aux_frequency_ge_656 j
  exact abs_le.mpr ⟨by linarith only [hi', hj.2], by linarith only [hj', hi.2]⟩

/-- Pairing reciprocal scales and summing all frequencies gives the auxiliary
Euler polynomial weighted by the trace deficit. -/
theorem quarter_cosine_tail_eq_656 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : (322 : ℝ) ^ 2 ≤ X) :
    quarterAuxMix656 (quarterCosineTail656 a b c X) =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
          (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
          quarterAuxPoly656 (Real.log n.val) := by
  let N := { n : ℕ // ⌊X⌋₊ < n }
  let D := fun n : N ↦ 3 - ((a n.val).re + (b n.val).re + (c n.val).re)
  let F := fun s : ℝ ↦ fun n : N ↦
    D n *
      (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
        (quarterSymmetricProfile656 (n.val / Real.exp |s|) +
          quarterSymmetricProfile656 (n.val / (Real.exp |s|)⁻¹)))
  have hF (s : ℝ) : Summable (F s) := by
    have hp := Real.exp_pos |s|
    have ha := (quarter_trace_tail_hasSum_656 a b c X hp).summable
    have hb := (quarter_trace_tail_hasSum_656 a b c X (inv_pos.mpr hp)).summable
    dsimp only at ha hb
    apply (ha.add hb).congr
    intro n
    simp only [F, D, mul_add]
  change quarterAuxMix656 (fun s ↦ ∑' n, F s n) = _
  rw [aux_mix_tsum F hF]
  apply tsum_congr
  intro n
  have hX₀ := (by norm_num only : (0 : ℝ) < 322 ^ 2).trans_le hX
  have hn := (Nat.floor_lt hX₀.le).mp n.property
  have hn₀ := hX₀.trans hn
  have hlog : 10 ≤ Real.log n.val := by
    have he : Real.exp 10 ≤ (322 : ℝ) ^ 2 := by
      rw [show (10 : ℝ) = 1 * ((10 : ℕ) : ℝ) by norm_num only, Real.exp_mul_natCast]
      exact
        (pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _).trans (by norm_num only)
    exact (Real.le_log_iff_exp_le hn₀).mpr (he.trans (hX.trans hn.le))
  have hscale :
    Real.exp (-(11 / 10) * Real.log n.val) / Real.sqrt n.val = ((n.val : ℝ) ^ (8 / 5 : ℝ))⁻¹ := by
    rw [mul_comm (-(11 / 10 : ℝ)), ← Real.rpow_def_of_pos hn₀, Real.sqrt_eq_rpow, ←
      Real.rpow_sub hn₀, show -(11 / 10 : ℝ) - 1 / 2 = -(8 / 5) by norm_num only,
      Real.rpow_neg hn₀.le]
  let K := D n * (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ))
  have he (s : ℝ) (hs : |s| ≤ 10) : F s n = K * quarterAuxPair656 s (Real.log n.val) := by
    dsimp only [F, K]
    rw [quarter_cosine_profile_pair_656 hn₀ (hs.trans hlog)]
    linear_combination
      (D n * ArithmeticFunction.vonMangoldt n.val * quarterAuxPair656 s (Real.log n.val)) * hscale
  change quarterAuxMix656 (fun s ↦ F s n) = K * quarterAuxPoly656 (Real.log n.val)
  unfold quarterAuxPoly656 quarterAuxMix656
  have h₁ (i : Fin 7) :
    quarterAuxCoeff656 i * F (quarterAuxFrequency656 i) n =
      K *
        (quarterAuxCoeff656 i * quarterAuxPair656 (quarterAuxFrequency656 i) (Real.log n.val)) := by
    rw [he _ (aux_frequency_abs_le i), mul_left_comm]
  have h₂ (i j : Fin 7) :
    quarterAuxCoeff656 i * quarterAuxCoeff656 j *
        F (quarterAuxFrequency656 i - quarterAuxFrequency656 j) n =
      K *
        (quarterAuxCoeff656 i * quarterAuxCoeff656 j *
          quarterAuxPair656 (quarterAuxFrequency656 i - quarterAuxFrequency656 j)
            (Real.log n.val)) := by
    rw [he _ (aux_frequency_diff_le i j), mul_left_comm]
  simp only [h₁, h₂, ← Finset.mul_sum]
  ring

/-- The paired Euler deficit equals the six principal-versus-character
deficits at the two reciprocal scales. This is the Euler part of the
three-character cosine contour after the completed functional equation. -/
theorem quarter_cosine_tail_deficits_656 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 0 ≤ X) (s : ℝ) (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → a n = 1)
    (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → c n = 1) :
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) y ↦
      quarterSymmetricSum656 (1 : DirichletCharacter ℂ 1) y - quarterSymmetricSum656 χ y
    let y := Real.exp |s|
    quarterCosineTail656 a b c X s = (E a y + E b y + E c y) + (E a y⁻¹ + E b y⁻¹ + E c y⁻¹) := by
  intro E y
  have hy : 0 < y := Real.exp_pos _
  have hy' := inv_pos.mpr hy
  have h₁ := quarter_trace_tail_hasSum_656 a b c X hy
  have h₂ := quarter_trace_tail_hasSum_656 a b c X hy'
  have hs :=
    (h₁.add h₂).congr_fun (g := fun n : { n : ℕ // ⌊X⌋₊ < n } ↦
      (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
        (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
          (quarterSymmetricProfile656 (n.val / y) + quarterSymmetricProfile656 (n.val / y⁻¹))))
      (fun n ↦ by
        dsimp only; simp only [mul_add])
  dsimp only [E]
  rw [quarter_profile_tail_656 a hX hy ha, quarter_profile_tail_656 b hX hy hb,
    quarter_profile_tail_656 c hX hy hc, quarter_profile_tail_656 a hX hy' ha,
    quarter_profile_tail_656 b hX hy' hb, quarter_profile_tail_656 c hX hy' hc]
  exact hs.tsum_eq

/-- Under RH the signed sum of the paired Euler deficits is bounded by
the common numerical Abel estimate for the two section 132 intervals. -/
theorem quarter_cosine_tail_cap_656 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hRH : RiemannHypothesis) {X : ℝ} (hX : (322 : ℝ) ^ 2 ≤ X)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    quarterAuxMix656 (quarterCosineTail656 a b c X) ≤ 4 * 0.038175553 := by
  let α := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hα (n : ℕ) : 0 ≤ α n ∧ α n ≤ 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [α]; linarith only [(ht n).1]⟩
  have h := quarter_aux_trace_cap_656 hRH hX α hα
  rw [quarter_cosine_tail_eq_656 a b c hX]
  have hX₀ := (by norm_num only : (0 : ℝ) ≤ 322 ^ 2).trans hX
  let F := fun n : ℕ ↦
    α n * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
      quarterAuxPoly656 (Real.log n)
  have he := tsum_subtype {n : ℕ | ⌊X⌋₊ < n} F
  change (∑' n : { n : ℕ // ⌊X⌋₊ < n }, F n) ≤ _
  apply he.le.trans
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Nat.floor_lt hX₀, F]
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
