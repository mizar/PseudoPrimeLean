/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.ShiftedPoleKernel
import all PseudoPrime.LLS.PaperStatements.PaperDefinitions
import Mathlib.Tactic.Ring

/-! # Arithmetic weights for signed shifted-pole combinations -/

namespace PseudoPrime.LLS.PaperStatements

/-- The polynomial in the reversed logarithmic coordinate obtained from
shifted poles of orders `k i + 1` with coefficients `c i`. -/
public noncomputable def shiftedPolePolynomial {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℂ)
    (z : ℝ) : ℂ :=
  ∑ i ∈ s, c i * (z : ℂ) ^ k i / ((k i).factorial : ℂ)

/-- Inside the common support, factor the signed transform into a single
exponential weight times the logarithmic polynomial. -/
public theorem shiftedPole_transform_sum {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℂ)
    (hk : ∀ i, 1 ≤ k i) {ρ b u : ℝ} (hρ : 1 / 2 < ρ) (hu : 0 < u) (hb : u ≤ Real.exp b) :
    (∑ i ∈ s, c i * (shiftedPoleKernel (k i) ρ b (hk i) hρ).transform u) =
      (((u * Real.exp (-b)) ^ ρ : ℝ) : ℂ) * shiftedPolePolynomial s k c (b - Real.log u) := by
  rw [shiftedPolePolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [shiftedPoleKernel_transform _ _ _ _ _ hu, Analysis.shiftedPoleProfile_eq _ _ hu hb]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
  ring

/-- Outside the common support the combined transform vanishes. -/
public theorem shiftedPole_transform_sum_zero {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℂ)
    (hk : ∀ i, 1 ≤ k i) {ρ b u : ℝ} (hρ : 1 / 2 < ρ) (hb : Real.exp b ≤ u) :
    (∑ i ∈ s, c i * (shiftedPoleKernel (k i) ρ b (hk i) hρ).transform u) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [shiftedPoleKernel_transform _ _ _ _ _ ((Real.exp_pos _).trans_le hb),
    Analysis.shiftedPoleProfile_support (hk i) ρ hb, Complex.ofReal_zero, mul_zero]

/-- On a positive supported index the signed Mangoldt summand uses the
same logarithmic polynomial as the transform. -/
public theorem shiftedPole_summand_sum {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℂ)
    (hk : ∀ i, 1 ≤ k i) {ρ b x : ℝ} (hρ : 1 / 2 < ρ) (hx : 0 < x) {q n : ℕ}
    (χ : DirichletCharacter ℂ q) (hn : 0 < n) (hb : (n : ℝ) / x ≤ Real.exp b) :
    (∑ i ∈ s, c i * (shiftedPoleKernel (k i) ρ b (hk i) hρ).summand χ x n) =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
        ((((n : ℝ) / x * Real.exp (-b)) ^ ρ : ℝ) : ℂ) *
        shiftedPolePolynomial s k c (b - Real.log ((n : ℝ) / x)) := by
  let A := ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n
  let K := fun i ↦ shiftedPoleKernel (k i) ρ b (hk i) hρ
  have he :
    (∑ i ∈ s, c i * (K i).summand χ x n) = A * ∑ i ∈ s, c i * (K i).transform ((n : ℝ) / x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [MellinKernel.summand, ite_eq_right hn.ne', A]
    ring
  rw [he, shiftedPole_transform_sum s k c hk hρ (div_pos (Nat.cast_pos.mpr hn) hx) hb]
  ring

/-- The signed arithmetic series has finite support through the natural
floor of the scaled support endpoint. On that support it is the original
logarithmic polynomial times the common Mangoldt weight. -/
public theorem shiftedPole_summand_tsum {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℂ)
    (hk : ∀ i, 1 ≤ k i) {ρ b x : ℝ} (hρ : 1 / 2 < ρ) (hx : 0 < x) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, ∑ i ∈ s, c i * (shiftedPoleKernel (k i) ρ b (hk i) hρ).summand χ x n) =
      ∑ n ∈ Finset.Ioc 0 ⌊x * Real.exp b⌋₊,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
          ((((n : ℝ) / x * Real.exp (-b)) ^ ρ : ℝ) : ℂ) *
          shiftedPolePolynomial s k c (b - Real.log ((n : ℝ) / x)) := by
  let K := fun i ↦ shiftedPoleKernel (k i) ρ b (hk i) hρ
  let S := Finset.Ioc 0 ⌊x * Real.exp b⌋₊
  have hvanish (n : ℕ) (hn : n ∉ S) : (∑ i ∈ s, c i * (K i).summand χ x n) = 0 := by
    by_cases hn0 : n = 0
    · subst n
      simp only [MellinKernel.summand, ite_true, mul_zero, Finset.sum_const_zero]
    have hpos := Nat.pos_of_ne_zero hn0
    have ht : x * Real.exp b < (n : ℝ) := by
      apply (Nat.floor_lt (mul_pos hx (Real.exp_pos _)).le).mp
      exact lt_of_not_ge (fun h ↦ hn (Finset.mem_Ioc.mpr ⟨hpos, h⟩))
    have hb : Real.exp b ≤ (n : ℝ) / x :=
      (le_div_iff₀ hx).mpr ((mul_comm (Real.exp b) x).trans_le ht.le)
    have hv := shiftedPole_transform_sum_zero s k c hk hρ hb
    calc
      _ =
          (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n) *
            ∑ i ∈ s, c i * (K i).transform ((n : ℝ) / x) :=
        by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [MellinKernel.summand, ite_eq_right hn0]
        ring
      _ = 0 := by rw [hv, mul_zero]
  rw [tsum_eq_sum (s := S) hvanish]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0, hnB⟩ := Finset.mem_Ioc.mp hn
  have hb : (n : ℝ) / x ≤ Real.exp b :=
    (div_le_iff₀ hx).mpr
      ((Nat.le_floor_iff (mul_pos hx (Real.exp_pos _)).le).mp hnB |>.trans_eq (mul_comm _ _))
  exact shiftedPole_summand_sum s k c hk hρ hx χ hn0 hb

end PseudoPrime.LLS.PaperStatements
