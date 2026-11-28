/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineEuler644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosine644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta

/-! # Forward and reflected Euler series for the section 122 symmetric kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem quarter_symmetric_neg_644 (z : ℂ) :
    quarterSymmetricKernel644 (-z) = quarterSymmetricKernel644 z := by
  unfold quarterSymmetricKernel644
  rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm ((107 / 100 : ℂ) + z)]

/-- Reflection interchanges the two lines of real parts ±9/16 and inverts the
scale in the power weight. Evenness preserves the symmetric kernel itself. -/
theorem quarter_reflect_symmetric_line_644 (H : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    (∫ t : ℝ, H (-(l t)) * (quarterSymmetricKernel644 (l t) * (x : ℂ) ^ l t)) =
      ∫ t : ℝ, H (r t) * (quarterSymmetricKernel644 (r t) * ((x⁻¹ : ℝ) : ℂ) ^ r t) := by
  intro l r
  let F := fun t : ℝ ↦ H (r t) * (quarterSymmetricKernel644 (r t) * ((x⁻¹ : ℝ) : ℂ) ^ r t)
  have hr (t : ℝ) : r (-t) = -(l t) := by
    dsimp only [r, l]
    push_cast
    ring
  have he (t : ℝ) : H (-(l t)) * (quarterSymmetricKernel644 (l t) * (x : ℂ) ^ l t) = F (-t) := by
    simp only [F, hr, quarter_symmetric_neg_644, Complex.ofReal_inv, Complex.cpow_neg,
      Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he)]
  exact MeasureTheory.integral_neg_eq_self F MeasureTheory.volume

/-- The reflected ordinary logarithmic derivative for the symmetric kernel has
the exact forward arithmetic sum at reciprocal scale, with its minus sign. -/
theorem quarter_reflected_prime_sum_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.LFunction (-(l t) + 1 / 2) *
            (quarterSymmetricKernel644 (l t) * (x : ℂ) ^ l t)) =
      ∑' n, quarterSymmetricMellin644.summand χ x⁻¹ n := by
  intro l
  have h := quarter_reflect_symmetric_line_644 (fun s ↦ -logDeriv χ.LFunction (s + 1 / 2)) hx
  dsimp only at h
  dsimp only [l]
  rw [h]
  exact
    (LLS.PaperStatements.MellinKernel.tsum_summand_eq_integral_logDeriv quarterSymmetricMellin644 χ
        (inv_pos.mpr hx) (by norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)).symm

/-- The constant logarithmic conductor integrates on the left line to the
continuous symmetric profile at the reciprocal scale. -/
theorem quarter_left_conductor_644 (q : ℕ) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, Complex.log q * (quarterSymmetricKernel644 (l t) * (x : ℂ) ^ l t)) =
      Complex.log q * (quarterSymmetricProfile644 x⁻¹ : ℂ) := by
  intro l
  have h :=
    symmetric_line_inversion (c := -9 / 16) (by norm_num only) (by norm_num only) (inv_pos.mpr hx)
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  rw [MeasureTheory.integral_const_mul, mul_left_comm, ← h]

/-- The real symmetric arithmetic summand at any positive scale, also at n = 0
where the von Mangoldt factor vanishes. -/
theorem quarter_symmetric_summand_644 {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (n : ℕ) :
    (quarterSymmetricMellin644.summand χ x n).re =
      (χ n).re *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile644 (n / x)) := by
  by_cases hn : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re,
      ArithmeticFunction.map_zero, zero_div, zero_mul, mul_zero]
  · have hy := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
    have ht :
      quarterSymmetricMellin644.transform (n / x) = (quarterSymmetricProfile644 (n / x) : ℂ) :=
      symmetric_line_inversion (c := 0) (by norm_num only) (by norm_num only) hy
    rw [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn, ht, mul_comm _ (χ n)]
    rw [mul_assoc, ← Complex.ofReal_mul, Complex.mul_re]
    simp only [Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero]

/-- The real reflected logarithmic derivative is the von Mangoldt series at
reciprocal scale. Its profile argument is n times the original scale. -/
theorem quarter_reflected_euler_series_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.LFunction (-(l t) + 1 / 2) *
              (quarterSymmetricKernel644 (l t) * (x : ℂ) ^ l t))).re =
      ∑' n : ℕ,
        (χ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            quarterSymmetricProfile644 (n * x)) := by
  intro l
  rw [quarter_reflected_prime_sum_644 χ hx,
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand quarterSymmetricMellin644 χ
        (inv_pos.mpr hx))]
  apply tsum_congr
  intro n
  simpa only [div_inv_eq_mul] using (quarter_symmetric_summand_644 χ (inv_pos.mpr hx) n)

/-- Absolute integrability on the reflected line permits subtraction of the
character and zeta logarithmic derivatives before taking real parts. -/
theorem quarter_reflected_integrable_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        -logDeriv χ.LFunction (-(l t) + 1 / 2) *
          (quarterSymmetricKernel644 (l t) * (x : ℂ) ^ l t)) := by
  intro l
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  have h :=
    LLS.PaperStatements.MellinKernel.integrable_arithmeticMellin_logDeriv quarterSymmetricMellin644
      χ (inv_pos.mpr hx) (c := 9 / 16) (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  apply h.comp_neg.congr
  apply Filter.Eventually.of_forall
  intro t
  change
    -logDeriv χ.LFunction (r (-t) + 1 / 2) *
        (quarterSymmetricKernel644 (r (-t)) * ((x⁻¹ : ℝ) : ℂ) ^ r (-t)) =
      _
  have hr : r (-t) = -(l t) := by
    dsimp only [r, l]
    push_cast
    ring
  simp only [hr, quarter_symmetric_neg_644, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv]

/-- The reflected difference of ordinary logarithmic derivatives contributes
the principal Euler series minus the character Euler series. -/
theorem quarter_reflected_euler_difference_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let A := fun {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) (t : ℝ) ↦
      -logDeriv ψ.LFunction (-(l t) + 1 / 2) * (quarterSymmetricKernel644 (l t) * (x : ℂ) ^ l t)
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      ∑' n : ℕ,
        (ψ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile644 (n * x))
    let ψ := (1 : DirichletCharacter ℂ 1)
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, A ψ t - A χ t)).re = S ψ - S χ := by
  intro l A S ψ
  rw [MeasureTheory.integral_sub (quarter_reflected_integrable_644 ψ hx)
      (quarter_reflected_integrable_644 χ hx),
    mul_sub, Complex.sub_re]
  exact
    congrArg₂ (· - ·) (quarter_reflected_euler_series_644 ψ hx)
      (quarter_reflected_euler_series_644 χ hx)

/-- The ordinary Euler sum for the symmetric profile at positive scale y. -/
noncomputable def quarterSymmetricSum644 {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) : ℝ :=
  ∑' n : ℕ,
    (χ n).re * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile644 (n / y))

/-- When the character is one on primes through X, its symmetric Euler deficit
is supported above floor X at every positive scale. -/
theorem quarter_profile_tail_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {X y : ℝ}
    (hX : 0 ≤ X) (hy : 0 < y) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    quarterSymmetricSum644 (1 : DirichletCharacter ℂ 1) y - quarterSymmetricSum644 χ y =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        (1 - (χ n.val).re) *
          (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
            quarterSymmetricProfile644 (n.val / y)) := by
  let W := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile644 (n / y)
  have hs {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) :
    Summable (fun n : ℕ ↦ (ψ n).re * W n) := by
    have h := LLS.PaperStatements.MellinKernel.summable_summand quarterSymmetricMellin644 ψ hy
    exact
      ((Complex.hasSum_re h.hasSum).congr_fun
          (fun n ↦ (quarter_symmetric_summand_644 ψ hy n).symm)).summable
  unfold quarterSymmetricSum644
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
theorem quarter_trace_tail_hasSum_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ)
    {y : ℝ} (hy : 0 < y) :
    let W := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile644 (n / y)
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) ↦
      ∑' k : { k : ℕ // ⌊X⌋₊ < k }, (1 - (χ k.val).re) * W k.val
    HasSum
      (fun k : { k : ℕ // ⌊X⌋₊ < k } ↦ (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) * W k.val)
      (E a + E b + E c) := by
  intro W E
  have hs {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Summable (fun n : ℕ ↦ (χ n).re * W n) := by
    have h := LLS.PaperStatements.MellinKernel.summable_summand quarterSymmetricMellin644 χ hy
    exact
      ((Complex.hasSum_re h.hasSum).congr_fun
          (fun n ↦ (quarter_symmetric_summand_644 χ hy n).symm)).summable
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
theorem quarter_trace_tail_eq_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ)
    {y : ℝ} (hy : 0 < y) :
    let W := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * quarterSymmetricProfile644 (n / y)
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) ↦
      ∑' k : { k : ℕ // ⌊X⌋₊ < k }, (1 - (χ k.val).re) * W k.val
    E a + E b + E c =
      ∑' k : { k : ℕ // ⌊X⌋₊ < k },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) * W k.val := by
  exact (quarter_trace_tail_hasSum_644 a b c X hy).tsum_eq.symm

/-- At a positive integer argument the two reciprocal scales in the Euler tail
give the forward and reflected profiles of the cosine inversion formula. -/
private theorem quarter_tail_profile_pair_644 {u : ℝ} (hu : 0 < u) (s : ℝ) :
    quarterSymmetricProfile644 (u / (Real.exp s)⁻¹) + quarterSymmetricProfile644 (u / Real.exp s) =
      quarterSymmetricProfile644 (u * Real.exp (-s)) +
        quarterSymmetricProfile644 (u⁻¹ * Real.exp (-s)) := by
  have hinv (v : ℝ) (hv : 0 ≤ v) :
    quarterSymmetricProfile644 v⁻¹ = quarterSymmetricProfile644 v := by
    simp only [quarterSymmetricProfile644, Real.inv_rpow hv, twoShiftSymmetricProfile, Real.log_inv,
      abs_neg]
  rw [Real.exp_neg, div_inv_eq_mul, div_eq_mul_inv, ← mul_inv,
    hinv _ (mul_nonneg hu.le (Real.exp_pos _).le), add_comm]

@[expose]
noncomputable def quarterCosineTail644 {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X s : ℝ) : ℝ :=
  let F := fun (y : ℝ) (k : { k : ℕ // ⌊X⌋₊ < k }) ↦
    (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
      (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val *
        quarterSymmetricProfile644 (k.val / y))
  (∑' k, F (Real.exp s)⁻¹ k) + ∑' k, F (Real.exp s) k

/-- Collect the seven cosine-tail contributions in a single sum over prime powers
above the cutoff, retaining the common trace factor. -/
theorem quarter_weighted_tail_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ) :
    let S := quarterCosineTail644 a b c X
    let P := fun (k s : ℝ) ↦
      quarterSymmetricProfile644 (k * Real.exp (-s)) +
        quarterSymmetricProfile644 (k⁻¹ * Real.exp (-s))
    (1.54) * S (2687 / 1000) + (-1.508) * S (2707 / 1000) + (-0.0917) * S (3787 / 1000) +
        (-((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2)) * S 0 +
        ((1.54 * 1.508)) * S (1 / 50) +
        ((1.54 * 0.0917)) * S (11 / 10) +
        (-(1.508 * 0.0917)) * S (27 / 25) =
      ∑' k : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
          (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val) *
          ((1.54) * P k.val (2687 / 1000) + (-1.508) * P k.val (2707 / 1000) +
            (-0.0917) * P k.val (3787 / 1000) +
            (-((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2)) * P k.val 0 +
            ((1.54 * 1.508)) * P k.val (1 / 50) +
            ((1.54 * 0.0917)) * P k.val (11 / 10) +
            (-(1.508 * 0.0917)) * P k.val (27 / 25)) := by
  intro S P
  let F := fun (y : ℝ) (k : { n : ℕ // ⌊X⌋₊ < n }) ↦
    (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
      (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val *
        quarterSymmetricProfile644 (k.val / y))
  have hs (s : ℝ) : HasSum (fun k ↦ F (Real.exp s)⁻¹ k + F (Real.exp s) k) (S s) :=
    (quarter_trace_tail_hasSum_644 a b c X (inv_pos.mpr (Real.exp_pos s))).summable.hasSum.add
      (quarter_trace_tail_hasSum_644 a b c X (Real.exp_pos s)).summable.hasSum
  have h0 := (hs (2687 / 1000)).mul_left (1.54)
  have h1 := (hs (2707 / 1000)).mul_left (-1.508)
  have h2 := (hs (3787 / 1000)).mul_left (-0.0917)
  have h3 := (hs 0).mul_left (-((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2))
  have h4 := (hs (1 / 50)).mul_left ((1.54 * 1.508))
  have h5 := (hs (11 / 10)).mul_left ((1.54 * 0.0917))
  have h6 := (hs (27 / 25)).mul_left (-(1.508 * 0.0917))
  have hh := (((((h0.add h1).add h2).add h3).add h4).add h5).add h6
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro k
  dsimp only [F, P]
  let A := 3 - ((a k.val).re + (b k.val).re + (c k.val).re)
  let B := ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val
  have hp :=
    quarter_tail_profile_pair_644 (u := k.val)
      (Nat.cast_pos.mpr (Nat.zero_le _ |>.trans_lt k.property))
  linear_combination
    (1.54 * A * B) * hp (2687 / 1000) + (-1.508 * A * B) * hp (2707 / 1000) +
      (-0.0917 * A * B) * hp (3787 / 1000) +
      (-((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2) * A * B) * hp 0 +
      ((1.54 * 1.508) * A * B) * hp (1 / 50) +
      ((1.54 * 0.0917) * A * B) * hp (11 / 10) +
      (-(1.508 * 0.0917) * A * B) * hp (27 / 25)

private theorem symmetric_transform_profile {u : ℝ} (hu : 0 < u) :
    (quarterSymmetricMellin644.transform u).re = quarterSymmetricProfile644 u := by
  have h : quarterSymmetricMellin644.transform u = (quarterSymmetricProfile644 u : ℂ) :=
    symmetric_line_inversion (c := 0) (by norm_num only) (by norm_num only) hu
  rw [h, Complex.ofReal_re]

/-- When the logarithm of the cutoff is at least five, the combined
symmetric Euler tails of three characters equal the signed correction
with the same weight as the certified auxiliary Euler bounds. -/
theorem quarter_cosine_tail_eq_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 0 < X) (hl : 5 ≤ Real.log X) :
    let S := quarterCosineTail644 a b c X
    1.54 * S (2687 / 1000) + (-1.508) * S (2707 / 1000) + (-0.0917) * S (3787 / 1000) +
        (-((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2)) * S 0 +
        (1.54 * 1.508) * S (1 / 50) +
        (1.54 * 0.0917) * S (11 / 10) +
        (-(1.508 * 0.0917)) * S (27 / 25) =
      -(∑' n : { n : ℕ // ⌊X⌋₊ < n },
          (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (157 / 100 : ℝ) *
              threeShiftEulerPoly644 (Real.log n.val))) := by
  dsimp only
  rw [quarter_weighted_tail_644, ← tsum_neg]
  apply tsum_congr
  intro n
  have hn := hX.trans (Nat.lt_of_floor_lt n.property)
  have hv :=
    quarter_cosine_euler_poly_644 hn
      (hl.trans (Real.log_le_log hX (Nat.lt_of_floor_lt n.property).le))
  dsimp only at hv
  simp only [symmetric_transform_profile (mul_pos hn (Real.exp_pos _)),
    symmetric_transform_profile (mul_pos (inv_pos.mpr hn) (Real.exp_pos _))] at hv
  have he :
    Real.exp (-(107 / 100) * Real.log (n.val : ℝ)) / Real.sqrt n.val =
      ((n.val : ℝ) ^ (157 / 100 : ℝ))⁻¹ := by
    rw [mul_comm (-(107 / 100 : ℝ)), ← Real.rpow_def_of_pos hn, Real.sqrt_eq_rpow, ←
      Real.rpow_sub hn]
    rw [show -(107 / 100 : ℝ) - 1 / 2 = -(157 / 100) by norm_num only, Real.rpow_neg hn.le]
  let A := 3 - ((a n.val).re + (b n.val).re + (c n.val).re)
  let B := ArithmeticFunction.vonMangoldt n.val
  let P := threeShiftEulerPoly644 (Real.log n.val)
  linear_combination (A * (B / Real.sqrt n.val)) * hv - (A * B * P) * he

end PseudoPrime.PrimeTestBounds.MillerRabin
