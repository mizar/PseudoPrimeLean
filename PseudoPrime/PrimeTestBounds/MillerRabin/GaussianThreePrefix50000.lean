/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianThreeSummand50000
public import PseudoPrime.LLS.PaperStatements.MellinKernelTruncatedComparison

/-! Joint Gaussian principal-prefix comparison. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive scale, a real Gaussian character summand factors through the principal summand. -/
theorem gaussian_summand_factor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (n : ℕ) :
    (LLS.PaperStatements.gaussianGammaMellinKernel.summand χ x n).re =
      (χ n).re *
        (LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
            n).re := by
  by_cases hn : n = 0
  · simp only [hn, LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re, mul_zero]
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hi : (LLS.PaperStatements.gaussianGammaMellinKernel.transform ((n : ℝ) / x)).im = 0 :=
      LLS.PaperStatements.gaussianGammaMellinKernel.mellin_real _ (div_pos hn0 hx)
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn,
      MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hi]
    ring

/-- Three characters with a common sign bound retain four times the actual principal prefix. -/
theorem gaussian_three_principal_prefix {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {x : ℝ}
    (hx : 0 < x) (s : Finset ℕ) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    4 *
        (∑ n ∈ s,
          (LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
              n).re) ≤
      (∑' n : ℕ,
            LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
              n).re +
        (∑' n : ℕ, LLS.PaperStatements.gaussianGammaMellinKernel.summand a x n).re +
        (∑' n : ℕ, LLS.PaperStatements.gaussianGammaMellinKernel.summand b x n).re +
        (∑' n : ℕ, LLS.PaperStatements.gaussianGammaMellinKernel.summand c x n).re := by
  let f : ℕ → ℝ := fun n ↦
    (LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re
  let A : ℕ → ℝ := fun n ↦ (LLS.PaperStatements.gaussianGammaMellinKernel.summand a x n).re
  let B : ℕ → ℝ := fun n ↦ (LLS.PaperStatements.gaussianGammaMellinKernel.summand b x n).re
  let C : ℕ → ℝ := fun n ↦ (LLS.PaperStatements.gaussianGammaMellinKernel.summand c x n).re
  have hf : Summable f :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand
        LLS.PaperStatements.gaussianGammaMellinKernel (1 : DirichletCharacter ℂ 1) hx)
  have ha : Summable A :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand
        LLS.PaperStatements.gaussianGammaMellinKernel a hx)
  have hb : Summable B :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand
        LLS.PaperStatements.gaussianGammaMellinKernel b hx)
  have hc : Summable C :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand
        LLS.PaperStatements.gaussianGammaMellinKernel c hx)
  have h :=
    ((hf.add ha).add hb |>.add hc).sum_le_tsum s
      (fun n _ ↦ by
        have hw : 0 ≤ f n :=
          LLS.PaperStatements.MellinKernel.principal_summand_re_nonneg
            LLS.PaperStatements.gaussianGammaMellinKernel hx n
        have ht' := mul_le_mul_of_nonneg_right (ht n) hw
        change 0 ≤ f n + A n + B n + C n
        dsimp only [A, B, C]
        rw [gaussian_summand_factor a hx, gaussian_summand_factor b hx,
          gaussian_summand_factor c hx]
        change 0 ≤ f n + ((a n).re * f n) + ((b n).re * f n) + ((c n).re * f n)
        nlinarith only [ht'])
  have he : (∑ n ∈ s, (f n + A n + B n + C n)) = 4 * ∑ n ∈ s, f n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hz : ArithmeticFunction.vonMangoldt n = 0
    · have hfz : f n = 0 := by
        dsimp only [f, LLS.PaperStatements.MellinKernel.summand]
        split_ifs with hn0
        · rfl
        · rw [hz]
          simp only [zero_div, Complex.ofReal_zero, zero_mul, Complex.zero_re]
      dsimp only [A, B, C]
      rw [gaussian_summand_factor a hx, gaussian_summand_factor b hx, gaussian_summand_factor c hx]
      change f n + (a n).re * f n + (b n).re * f n + (c n).re * f n = 4 * f n
      rw [hfz]
      ring
    · have hs := congrArg (fun t : ℝ ↦ t * f n) (hp n hn hz)
      dsimp only [A, B, C]
      rw [gaussian_summand_factor a hx, gaussian_summand_factor b hx, gaussian_summand_factor c hx]
      change f n + (a n).re * f n + (b n).re * f n + (c n).re * f n = 4 * f n
      nlinarith only [hs]
  change (∑ n ∈ s, (f n + A n + B n + C n)) ≤ ∑' n : ℕ, (f n + A n + B n + C n) at h
  rw [he, Summable.tsum_add ((hf.add ha).add hb) hc, Summable.tsum_add (hf.add ha) hb,
    Summable.tsum_add hf ha] at h
  rw [Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand
        LLS.PaperStatements.gaussianGammaMellinKernel (1 : DirichletCharacter ℂ 1) hx),
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand
        LLS.PaperStatements.gaussianGammaMellinKernel a hx),
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand
        LLS.PaperStatements.gaussianGammaMellinKernel b hx),
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand
        LLS.PaperStatements.gaussianGammaMellinKernel c hx)]
  exact h

/-- Under GRH, the certified joint Euler gain bounds the actual Gaussian principal deficit. -/
theorem gaussian_principal_prefix_50000 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 20000 ≤ p) (hQ : 20000 ≤ q)
    (hR : 20000 ≤ r) (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1)
    (hnB : b ≠ 1) (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even)
    (heB : b.Even) (heC : c.Even) {X : ℝ} (hX : 50000 ≤ X)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 1 ≤ x) (s : Finset ℕ)
    (hS : ∀ n ∈ s, (n : ℝ) ≤ X) :
    4 *
          (∑ n ∈ s,
            (LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
                n).re) -
        (∑' n : ℕ,
            LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
              n).re <
      (20115621 / 50000000 : ℝ) * (Real.log p + Real.log q + Real.log r) + 683 / 50 - 108 / 25 -
          4 * (1129059 / 200000 : ℝ) +
        (1536 / 27 : ℝ) / x +
        (2129 / 2000 : ℝ) *
          (((7 / 6 : ℝ) * (Real.log p + Real.log q + Real.log r) + 12) / Real.sqrt x) +
        (1419 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  have hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3 := by
    intro n hn hΛ
    have ha :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) a
        (fun l hl hlX _ ↦ hA l hl hlX) (hS n hn) (Nat.coprime_one_right n) hΛ
    have hb :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) b
        (fun l hl hlX _ ↦ hB l hl hlX) (hS n hn) (Nat.coprime_one_right n) hΛ
    have hc :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) c
        (fun l hl hlX _ ↦ hC l hl hlX) (hS n hn) (Nat.coprime_one_right n) hΛ
    rw [ha, hb, hc, Complex.one_re]
    norm_num only
  have hpref := gaussian_three_principal_prefix a b c (zero_lt_one.trans_le hx) s ht hp
  have hup :=
    gaussian_three_summand_50000 hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC hx
  linarith only [hpref, hup]

end PseudoPrime.PrimeTestBounds.MillerRabin
