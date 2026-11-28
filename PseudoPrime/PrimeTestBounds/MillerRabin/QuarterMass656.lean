/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaMass656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainTail656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSeries656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSplit656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineXi656

/-! # Unshifted symmetric zero mass for the section 132 kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The pair of unshifted symmetric profiles, divided by the square root
of a natural index, equals the section 132 Abel density. -/
theorem quarter_mass_weight_eq_656 {n : ℕ} (hn : 0 < n) :
    (quarterSymmetricProfile656 n + quarterSymmetricProfile656 n) / Real.sqrt n =
      eulerDensity656 n := by
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [symmetric_profile_value hn₀, abs_of_nonneg (Real.log_natCast_nonneg n), Real.sqrt_eq_rpow,
    eulerDensity656, quarterAuxProfile656]
  have he :
    Real.exp (-(11 / 10) * Real.log n) / (n : ℝ) ^ (1 / 2 : ℝ) = (n : ℝ) ^ (-(8 / 5) : ℝ) := by
    rw [Real.rpow_def_of_pos hn₀, Real.rpow_def_of_pos hn₀, ← Real.exp_sub]
    congr 1
    ring
  rw [show ∀ A P S : ℝ, (A * P / 2 + A * P / 2) / S = A / S * P from fun A P S ↦ by
      rw [← add_div, ← add_mul, mul_div_assoc, div_mul_eq_mul_div]
      ring,
    he]
  ring

/-- For cutoffs in the certified Abel range, the unshifted Euler deficit of
three characters with trace in [-1,3] is at most four times the signed tail.
Compare the nonnegative series at every index above the cutoff. -/
theorem quarter_mass_tail_cap_656 {p q s : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 103684 ≤ X) (hu : X ≤ 1000000)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    quarterCosineTail656 a b c X 0 ≤ 4 * signedTail656 X := by
  let N := { n : ℕ // ⌊X⌋₊ < n }
  let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * eulerDensity656 n
  let F := fun k : N ↦
    (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
      (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val *
        (quarterSymmetricProfile656 k.val + quarterSymmetricProfile656 k.val))
  have hF (k : N) : 0 ≤ F k ∧ F k ≤ 4 * W k.val := by
    have hpos : (0 : ℝ) < k.val := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.property)
    have hp : 0 ≤ quarterSymmetricProfile656 (k.val : ℝ) := by
      rw [symmetric_profile_value hpos]
      unfold quarterAuxProfile656
      positivity
    have hα := sub_nonneg.mpr (ht k.val).2
    have hα' : 3 - ((a k.val).re + (b k.val).re + (c k.val).re) ≤ 4 := by
      linarith only [(ht k.val).1]
    have he :=
      congrArg (ArithmeticFunction.vonMangoldt k.val * ·)
        (quarter_mass_weight_eq_656 (Nat.zero_lt_of_lt k.property))
    rw [← mul_div_assoc, ← div_mul_eq_mul_div] at he
    exact
      ⟨mul_nonneg hα
          (mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
            (add_nonneg hp hp)),
        (mul_le_mul hα' he.le
          (mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
            (add_nonneg hp hp))
          (by norm_num only))⟩
  have hW : Summable W := euler_density_summable_656
  have hWR : Summable (fun k : N ↦ 4 * W k.val) := (hW.subtype _).mul_left 4
  have hFS := Summable.of_nonneg_of_le (fun k ↦ (hF k).1) (fun k ↦ (hF k).2) hWR
  have hsum := hFS.tsum_le_tsum (fun k ↦ (hF k).2) hWR
  rw [tsum_mul_left] at hsum
  let S := Finset.Ioc 0 ⌊X⌋₊
  let e := fun k : N ↦
    (⟨k.val, fun h ↦ (not_lt_of_ge (Finset.mem_Ioc.mp h).2) k.property⟩ : { n : ℕ // n ∉ S })
  have hi : Function.Injective e := fun _ _ h ↦
    Subtype.ext (congrArg (fun k : { n : ℕ // n ∉ S } ↦ k.val) h)
  have hs :=
    Summable.tsum_le_tsum_of_inj e hi
      (fun k _ ↦ by
        change 0 ≤ W k.val
        by_cases hk : k.val = 0
        · simp only [W, hk, ArithmeticFunction.map_zero, zero_mul, le_refl]
        · have hlog := Real.log_natCast_nonneg k.val
          unfold W eulerDensity656
          positivity)
      (fun _ ↦ le_rfl) (hW.subtype _) (hW.subtype _)
  have hsplit := hW.sum_add_tsum_subtype_compl S
  have hbound := signed_tail_upper_656 hRH ((by norm_num only : (2701 : ℝ) ≤ 103684).trans hX) hu
  simp only [quarterCosineTail656, abs_zero, Real.exp_zero, inv_one, div_one]
  change (∑' k : N, F k) ≤ _
  have hcap : (∑' k : N, W k.val) ≤ signedTail656 X := by
    change (∑' n, W n) - (∑ n ∈ S, W n) ≤ _ at hbound
    exact hs.trans ((le_of_eq (eq_sub_of_add_eq' hsplit)).trans hbound)
  exact hsum.trans (mul_le_mul_of_nonneg_left hcap (by norm_num only))

/-- Under RH and prime agreement up to an admissible cutoff, the three
unshifted symmetric zero masses are bounded by the conductor, the certified
residue saving and the common Abel tail. -/
theorem quarter_even_mass_upper_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {X r : ℝ}
    (hl : 103684 ≤ X) (hu : X ≤ 1000000) (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → c n = 1) :
    quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 ≤
      3 / 4 * r - 10.9219669 + 4 * signedTail656 X := by
  have h := quarter_three_cosine_split_656 ha hb hc (by linarith only [hl] : 0 ≤ X) 0 hpa hpb hpc
  simp only [abs_zero, hL] at h
  rw [h]
  have htail := quarter_mass_tail_cap_656 a b c hRH hl hu ht
  have hxi := (abs_le.mp (quarter_xi_cosine_abs_656 hRH (b := 0) le_rfl)).2
  have hres := quarter_cosine_pole_pair_656 0
  have hprofile : quarterSymmetricProfile656 1 = 3 / 16 := by
    rw [symmetric_profile_value zero_lt_one]
    norm_num only [Real.log_one, abs_zero, mul_zero, Real.exp_zero, one_mul, quarterAuxProfile656,
      add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  dsimp only [quarterCosineCore656] at *
  simp only [abs_zero, Real.exp_zero, inv_one, hprofile] at hres ⊢
  simp only [neg_zero, zero_div, Real.exp_zero] at hres
  linarith only [htail, hxi, hres, quarter_mass_constant_656]

/-- On radii 322 through 328, substitute the bound for the three unshifted
symmetric zero masses into the main comparison. The conductor and the
explicit signed Euler tail are now independent of the three characters. -/
theorem quarter_forward_mass_gain_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 322 328)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    (∑' n, quarterKernel656.summand a x n).re + (∑' n, quarterKernel656.summand b x n).re +
        (∑' n, quarterKernel656.summand c x n).re +
        quarterAuxTheta656 r +
        quarterAuxNegPole656 / r +
        14.592123988 +
        0.00022760 * r +
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) ≤
      3 / 4 * r + 4 * signedTail656 x + 4 * r * (quarterKernel656.transform x⁻¹).re +
        3 * (quarterLevelGamma656 x).re := by
  intro x
  have h₁ : 103684 ≤ x :=
    (by norm_num only : (103684 : ℝ) ≤ 322 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have h₂ : x ≤ 1000000 :=
    (pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 322).trans hr.1) hr.2 2).trans
      (by norm_num only)
  have hM := quarter_even_mass_upper_656 ha hb hc hG.riemann h₁ h₂ hL ht hpa hpb hpc
  have h := quarter_forward_main_gain_656 ha hb hc hp hq hs hG hr hL ht hpa hpb hpc
  dsimp only [x] at hM h ⊢
  linarith only [h, hM]

/-- At the unshifted scale, the principal reflected sum minus the three
character sums is bounded by the six Abel moments. Prime agreement
through the squared radius cancels the common prefix. -/
theorem quarter_main_reflect_cap_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hRH : RiemannHypothesis) {r : ℝ} (hr : 322 ≤ r) {B : ℕ} (hB : 103684 ≤ (B : ℝ))
    (hU : (B : ℝ) ≤ 1000000) (hBr : (B : ℝ) ≤ r ^ 2)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) -
        (quarterMainEuler656 a (r ^ 2) + quarterMainEuler656 b (r ^ 2) +
          quarterMainEuler656 c (r ^ 2)) ≤
      quarterAuxReflectCap656 r (-(21 / 8)) B := by
  let α := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hr₁ : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 322).trans hr
  have hx : 1 ≤ r ^ 2 * Real.exp (-(21 / 8 + -(21 / 8))) := by
    simp only [add_neg_cancel, neg_zero, Real.exp_zero, mul_one]
    exact one_le_pow₀ hr₁
  have he := quarter_shift_euler_deficit_656 a b c (zero_lt_one.trans_le hr₁) (h := -(21 / 8)) hx
  simp only [add_neg_cancel, neg_zero, Real.exp_zero, mul_one] at he
  rw [he]
  refine quarter_aux_reflect_tail_cap_656 hRH hB hU α ?_ ?_ (zero_lt_one.trans_le hr₁) ?_
  · intro n
    exact
      ⟨sub_nonneg.mpr (ht n).2, by
        dsimp only [α]; linarith only [(ht n).1]⟩
  · intro n hn hΛ
    have hn' : (n : ℝ) ≤ B := Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2
    have hin := hn'.trans hBr
    simp only [α,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero a hpa hin hΛ,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero b hpb hin hΛ,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero c hpc hin hΛ,
      Complex.one_re]
    norm_num only
  · linarith only [Real.log_nonneg hr₁]

/-- On radii 322 through 328, incorporate the unshifted trace deficit bound
and cancel the common level-one reflected Euler term against the Gamma term.
Only the explicit moment cap and the principal contribution remain. -/
theorem quarter_forward_reflected_gain_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 322 328)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    (∑' n, quarterKernel656.summand a x n).re + (∑' n, quarterKernel656.summand b x n).re +
        (∑' n, quarterKernel656.summand c x n).re +
        quarterAuxTheta656 r +
        quarterAuxNegPole656 / r +
        14.592123988 +
        0.00022760 * r ≤
      3 / 4 * r + 4 * signedTail656 x + 4 * r * (quarterKernel656.transform x⁻¹).re +
        3 * ((quarterLevelGamma656 x).re - quarterMainEuler656 (1 : DirichletCharacter ℂ 1) x) +
        quarterAuxReflectCap656 r (-(21 / 8)) 103684 := by
  intro x
  have hX : (103684 : ℝ) ≤ x := by
    rw [show (103684 : ℝ) = 322 ^ 2 by norm_num only]
    exact pow_le_pow_left₀ (by norm_num only) hr.1 2
  have hR :=
    quarter_main_reflect_cap_656 a b c hG.riemann hr.1 (B := 103684) (by norm_num only)
      (by norm_num only) hX ht hpa hpb hpc
  have h := quarter_forward_mass_gain_656 ha hb hc hp hq hs hG hr hL ht hpa hpb hpc
  dsimp only [x] at h ⊢
  linarith only [h, hR]

/-- At scale at least one, eliminate the principal Gamma and reflected Euler
difference using the forward sum, the two residues and the RH zero mass. -/
theorem quarter_main_level_upper_656 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (quarterLevelGamma656 x).re - quarterMainEuler656 (1 : DirichletCharacter ℂ 1) x ≤
      (∑' n, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re + 1 / 2000000 -
        (quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re -
        (quarterKernel656.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re := by
  have h := quarter_main_level_cancel_656 hx
  rw [quarter_main_xi_zeros_656 hRH hx] at h
  simp only [Complex.sub_re] at h
  linarith only [h, (abs_le.mp (quarter_main_zero_abs_656 hRH hx)).2]

/-- For the section 132 radius interval, the comparison of the three forward
sums with the level-one forward sum depends only on arithmetic tails,
conductor profiles and half-point residues. -/
theorem quarter_forward_principal_gain_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 322 328)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let P := fun t : ℝ ↦ (quarterKernel656.function (t : ℂ) * (x : ℂ) ^ (t : ℂ)).re
    (∑' n, quarterKernel656.summand a x n).re + (∑' n, quarterKernel656.summand b x n).re +
            (∑' n, quarterKernel656.summand c x n).re -
          3 * (∑' n, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re +
        quarterAuxTheta656 r +
        quarterAuxNegPole656 / r +
        14.592122488 +
        0.00022760 * r ≤
      3 / 4 * r + 4 * signedTail656 x + 4 * r * (quarterKernel656.transform x⁻¹).re -
          3 * P (-1 / 2) -
          3 * P (1 / 2) +
        quarterAuxReflectCap656 r (-(21 / 8)) 103684 := by
  intro x P
  have hx : 1 ≤ x := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 322).trans hr.1)
  have h := quarter_forward_reflected_gain_656 ha hb hc hp hq hs hG hr hL ht hpa hpb hpc
  have hP := quarter_main_level_upper_656 hG.riemann hx
  dsimp only [P, x] at h hP ⊢
  linarith only [h, hP]

/-- At positive scale, the three-character forward deficit is a single
series with coefficient three minus the real trace. The principal weight
contains the full support of the Mellin kernel. -/
theorem quarter_forward_trace_deficit_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {x : ℝ}
    (hx : 0 < x) :
    3 * (∑' n, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re -
        ((∑' n, quarterKernel656.summand a x n).re + (∑' n, quarterKernel656.summand b x n).re +
          (∑' n, quarterKernel656.summand c x n).re) =
      ∑' n : ℕ,
        (3 - ((a n).re + (b n).re + (c n).re)) *
          (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  let ψ := (1 : DirichletCharacter ℂ 1)
  have h {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :=
    Complex.hasSum_re
      (LLS.PaperStatements.MellinKernel.summable_summand quarterKernel656 χ hx).hasSum
  rw [← (((h ψ).mul_left 3).sub (((h a).add (h b)).add (h c))).tsum_eq]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp only [hn, LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re, mul_zero,
      add_zero, sub_zero]
  have h₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hw : (quarterKernel656.transform ((n : ℝ) / x)).im = 0 := by
    rw [quarterKernel656, LLS.PaperStatements.rationalPole_transform _ _ _ _ (div_pos h₀ hx),
      Complex.ofReal_im]
  have hf :
    ∀ {m : ℕ} (χ : DirichletCharacter ℂ m),
      (quarterKernel656.summand χ x n).re = (χ n).re * (quarterKernel656.summand ψ x n).re := by
    intro m χ
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn, ψ,
      MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, hw, mul_one, mul_zero, zero_mul, sub_zero, add_zero]
    ring
  rw [hf a, hf b, hf c]
  ring

/-- Throughout the section 132 interval the analytic comparison gives a
lower bound for the forward trace-deficit series. The other side contains
only scalar kernel values and certified Euler tail envelopes. -/
theorem quarter_arithmetic_comparison_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 322 328)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let P := fun t : ℝ ↦ (quarterKernel656.function (t : ℂ) * (x : ℂ) ^ (t : ℂ)).re
    quarterAuxTheta656 r + quarterAuxNegPole656 / r + 14.592122488 + 0.00022760 * r -
        (3 / 4 * r + 4 * signedTail656 x + 4 * r * (quarterKernel656.transform x⁻¹).re -
            3 * P (-1 / 2) -
            3 * P (1 / 2) +
          quarterAuxReflectCap656 r (-(21 / 8)) 103684) ≤
      ∑' n : ℕ,
        (3 - ((a n).re + (b n).re + (c n).re)) *
          (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  intro x P
  have hx : 0 < x := pow_pos ((by norm_num only : (0 : ℝ) < 322).trans_le hr.1) 2
  rw [← quarter_forward_trace_deficit_656 a b c hx]
  have h := quarter_forward_principal_gain_656 ha hb hc hp hq hs hG hr hL ht hpa hpb hpc
  dsimp only [x, P] at h ⊢
  linarith only [h]

/-- Under prime agreement through the cutoff, the forward deficit series has
support only between the cutoff and the last index in the kernel support.
On that finite window the principal summand is the physical weight. -/
theorem quarter_forward_deficit_window_656 {p q s : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {x : ℝ} (hx : 0 < x)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ x → a n = 1) (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ x → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ x → c n = 1) :
    let F := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (∑' n : ℕ, F n * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp (21 / 8) * x⌋₊,
        F n * (quarterWeight656 x n * ArithmeticFunction.vonMangoldt n) := by
  intro F
  have hy : 0 ≤ Real.exp (21 / 8) * x := mul_nonneg (Real.exp_pos _).le hx.le
  refine (tsum_eq_sum ?_).trans (Finset.sum_congr rfl ?_)
  · intro n hn
    by_cases hl : (n : ℝ) ≤ x
    · by_cases hv : ArithmeticFunction.vonMangoldt n = 0
      · by_cases hn₀ : n = 0
        · simp only [hn₀, LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re,
            mul_zero]
        · simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn₀, hv, zero_div,
            Complex.ofReal_zero, zero_mul, Complex.zero_re, mul_zero]
      · simp only [F,
          AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero a ha hl hv,
          AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero b hb hl hv,
          AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero c hc hl hv,
          Complex.one_re]
        norm_num only [zero_mul]
    have hhu : ¬(n : ℝ) ≤ Real.exp (21 / 8) * x := fun hh ↦
      hn
        (Finset.mem_Ioc.mpr
          ⟨lt_of_not_ge (fun h ↦ hl ((Nat.le_floor_iff hx.le).mp h)), (Nat.le_floor_iff hy).mpr hh⟩)
    have hu := (lt_div_iff₀ hx).mpr (lt_of_not_ge hhu)
    have hp : 0 < (n : ℝ) / x := (Real.exp_pos _).trans hu
    have hn₀ : n ≠ 0 := (Nat.cast_pos.mp ((div_pos_iff_of_pos_right hx).mp hp)).ne'
    have hz :=
      Analysis.rationalPoleProfile_eq_zero 3 (5 / 11) (21 / 16)
        (by
          rw [show (2 * (21 / 16) : ℝ) = 21 / 8 by norm_num only]
          exact hu)
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn₀]
    rw [quarterKernel656, LLS.PaperStatements.rationalPole_transform _ _ _ _ hp, hz]
    simp only [Complex.ofReal_zero, mul_zero, Complex.zero_re]
  · intro n hn
    have hn₀ := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
    have hnu := (Nat.le_floor_iff hy).mp (Finset.mem_Ioc.mp hn).2
    have hnpos := div_pos (Nat.cast_pos.mpr hn₀) hx
    have hlog := (Real.log_le_iff_le_exp hnpos).mpr ((div_le_iff₀ hx).mpr hnu)
    rw [quarter_summand_656 hx hn₀ hlog]

/-- On the section 132 interval, bound the trace deficit by four at every
index in the finite forward window. The resulting comparison depends only
on the prime sum and the scalar analytic envelopes. Proper prime powers in
the window have their base below the cutoff and contribute zero. -/
theorem quarter_finite_comparison_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 322 328)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let P := fun t : ℝ ↦ (quarterKernel656.function (t : ℂ) * (x : ℂ) ^ (t : ℂ)).re
    quarterAuxTheta656 r + quarterAuxNegPole656 / r + 14.592122488 + 0.00022760 * r -
        (3 / 4 * r + 4 * signedTail656 x + 4 * r * (quarterKernel656.transform x⁻¹).re -
            3 * P (-1 / 2) -
            3 * P (1 / 2) +
          quarterAuxReflectCap656 r (-(21 / 8)) 103684) ≤
      4 *
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp (21 / 8) * x⌋₊,
          quarterWeight656 x n * (if n.Prime then Real.log n else 0) := by
  intro x P
  have hx : 0 < x := pow_pos ((by norm_num only : (0 : ℝ) < 322).trans_le hr.1) 2
  have h := quarter_arithmetic_comparison_656 ha hb hc hp hq hs hG hr hL ht hpa hpb hpc
  dsimp only [x] at h
  rw [quarter_forward_deficit_window_656 a b c hx hpa hpb hpc] at h
  refine h.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn₀ := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  have hy : 0 ≤ Real.exp (21 / 8) * x := mul_nonneg (Real.exp_pos _).le hx.le
  have hu := (Nat.le_floor_iff hy).mp (Finset.mem_Ioc.mp hn).2
  have hlog :=
    (Real.log_le_iff_le_exp (div_pos (Nat.cast_pos.mpr hn₀) hx)).mpr ((div_le_iff₀ hx).mpr hu)
  have hw : 0 ≤ quarterWeight656 x n := by
    unfold quarterWeight656
    dsimp only
    have hv := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 11 / 10) (sub_nonneg.mpr hlog)
    positivity
  have he : Real.exp (21 / 8) ≤ x := by
    have h₃ : Real.exp 3 ≤ (3 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = 1 * ((3 : ℕ) : ℝ) by norm_num only, Real.exp_mul_natCast, one_mul,
        Nat.cast_ofNat]
      exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 3
    exact
      (Real.exp_le_exp.mpr (by norm_num only)).trans
        (h₃.trans
          ((by norm_num only : (3 : ℝ) ^ 3 ≤ 322 ^ 2).trans
            (pow_le_pow_left₀ (by norm_num only) hr.1 2)))
  by_cases hp' : n.Prime
  · rw [ite_eq_left hp', ArithmeticFunction.vonMangoldt_apply_prime hp']
    have hd : 3 - ((a n).re + (b n).re + (c n).re) ≤ 4 := by linarith only [(ht n).1]
    exact mul_le_mul_of_nonneg_right hd (mul_nonneg hw (Real.log_natCast_nonneg n))
  rw [ite_eq_right hp', mul_zero, mul_zero]
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, mul_zero, le_refl]
  obtain ⟨l, k, hl, hk, rfl⟩ :=
    (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hk₂ : 2 ≤ k :=
    Nat.succ_le_of_lt
      (lt_of_le_of_ne (Nat.succ_le_of_lt hk) (fun h ↦ hp' (by simpa only [← h, pow_one] using hl)))
  have hh : (l : ℝ) ^ 2 ≤ ((l ^ k : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact pow_le_pow_right₀ (Nat.one_le_cast.mpr hl.one_lt.le) hk₂
  have hls : (l : ℝ) ≤ x :=
    le_of_not_gt
      (fun h ↦
        (not_lt_of_ge
            (hh.trans
              (hu.trans
                (by
                  rw [pow_two]
                  exact mul_le_mul_of_nonneg_right he hx.le))))
          (pow_lt_pow_left₀ h hx.le (by decide)))
  simp only [Nat.cast_pow, map_pow, hpa l hl hls, hpb l hl hls, hpc l hl hls, one_pow,
    Complex.one_re]
  norm_num only [zero_mul, le_refl]

/-- For a positive radius, the two main half-point residues are respectively
an inverse-radius term and a linear term. Evaluate the existing shifted residue
identities at displacement minus the kernel shift. -/
private theorem main_poles_656 {r : ℝ} (hr : 0 < r) :
    let P := fun t : ℝ ↦ (quarterKernel656.function (t : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ (t : ℂ)).re
    P (-1 / 2) = ((11 / 10 : ℝ) ^ 5 / (3 / 5) ^ 6) * Real.exp (-(21 / 16)) / r ∧
      P (1 / 2) = ((11 / 10 : ℝ) ^ 5 / (8 / 5) ^ 6) * Real.exp (21 / 16) * r := by
  intro P
  have hm := quarter_shifted_neg_pole_656 hr (-(21 / 8))
  have hp := quarter_shifted_half_pole_656 hr (-(21 / 8))
  norm_num only [add_neg_cancel, neg_zero, Real.exp_zero, mul_one, neg_neg] at hm hp
  constructor
  · dsimp only [P]
    rw [neg_div, hm]
    ring_nf
  · dsimp only [P]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, hp]
    ring_nf

/-- At radius at least one, evaluate the inverse-scale conductor profile
directly on its support. -/
private theorem main_conductor_656 {r : ℝ} (hr : 1 ≤ r) :
    let z := (11 / 10 : ℝ) * (21 / 8 + 2 * Real.log r)
    (quarterKernel656.transform (r ^ 2)⁻¹).re = z ^ 5 * Real.exp (-z) / 120 := by
  intro z
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have hp := inv_pos.mpr (zero_lt_one.trans_le hx)
  have h :=
    quarter_transform_656 hp
      ((Real.log_nonpos hp.le (inv_le_one_of_one_le₀ hx)).trans (by norm_num only))
  rw [h, Real.log_inv, Real.log_pow]
  dsimp only [z]
  push_cast
  ring_nf

/-- On the section 132 radius interval, express the analytic lower bound on
the finite prime sum using only real scalar functions of the radius. -/
theorem quarter_scalar_comparison_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 322 328)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let z := (11 / 10 : ℝ) * (21 / 8 + 2 * Real.log r)
    quarterAuxTheta656 r +
          (quarterAuxNegPole656 + 3 * ((11 / 10 : ℝ) ^ 5 / (3 / 5) ^ 6) * Real.exp (-(21 / 16))) /
            r +
          14.592122488 +
          (0.00022760 - 3 / 4 + 3 * ((11 / 10 : ℝ) ^ 5 / (8 / 5) ^ 6) * Real.exp (21 / 16)) * r -
        (4 * signedTail656 x + 4 * r * (z ^ 5 * Real.exp (-z) / 120) +
          quarterAuxReflectCap656 r (-(21 / 8)) 103684) ≤
      4 *
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp (21 / 8) * x⌋₊,
          quarterWeight656 x n * (if n.Prime then Real.log n else 0) := by
  intro x z
  have hr₁ : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 322).trans hr.1
  have h := quarter_finite_comparison_656 ha hb hc hp hq hs hG hr hL ht hpa hpb hpc
  have hP := main_poles_656 (zero_lt_one.trans_le hr₁)
  dsimp only at h hP
  rw [hP.1, hP.2, main_conductor_656 hr₁] at h
  dsimp only [x, z]
  convert h using 1
  ring

/-- For positive scale and index, separate the dependence on the radius
from the fifth power in the forward profile. -/
private theorem forward_weight_factor {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    quarterWeight656 x t =
      ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * x ^ (-(11 / 10) : ℝ)) *
        (t ^ (3 / 5 : ℝ) * (21 / 8 + Real.log x - Real.log t) ^ 5) := by
  unfold quarterWeight656
  dsimp only
  rw [Real.log_div ht.ne' hx.ne', Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ht, one_div, ← Real.exp_neg]
  rw [show
      -((11 / 10 : ℝ) * (21 / 8 - (Real.log t - Real.log x))) =
        -(11 / 10) * (21 / 8) + Real.log x * -(11 / 10) +
          (Real.log t * (3 / 5) + Real.log t * (1 / 2))
      by ring,
    Real.exp_add, Real.exp_add, Real.exp_add]
  rw [← mul_assoc]
  calc
    _ =
        ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) *
            Real.exp (Real.log x * -(11 / 10))) *
          (Real.exp (Real.log t * (3 / 5)) * (21 / 8 + Real.log x - Real.log t) ^ 5) *
          (Real.exp (-(Real.log t * (1 / 2))) * Real.exp (Real.log t * (1 / 2))) :=
      by ring
    _ = _ := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- The prime-window moment of degree j for the section 132 forward kernel.
The cutoff determines the prime indices and the moment itself is independent
of the scale in the weight. -/
noncomputable def quarterPrimeMoment656 (x : ℝ) (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp (21 / 8) * x⌋₊,
    (n : ℝ) ^ (3 / 5 : ℝ) * (if n.Prime then Real.log n else 0) * (12 - Real.log n) ^ j

/-- At positive scale, express the entire forward prime sum as six moments
with polynomial coefficients in the logarithm of the scale. -/
theorem quarter_prime_sum_moments_656 {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp (21 / 8) * x⌋₊,
        quarterWeight656 x n * (if n.Prime then Real.log n else 0)) =
      ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * x ^ (-(11 / 10) : ℝ)) *
        ∑ j ∈ Finset.range 6,
          (Nat.choose 5 j : ℝ) * (21 / 8 + Real.log x - 12) ^ (5 - j) *
            quarterPrimeMoment656 x j := by
  simp only [quarterPrimeMoment656, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range 6)]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1)
  rw [forward_weight_factor hx hn₀]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  ring

/-- The cumulative prime moment through the integer endpoint B.
The same summand serves both endpoints of every forward window. -/
noncomputable def quarterPrimePrefix656 (B j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 B,
    (n : ℝ) ^ (3 / 5 : ℝ) * (if n.Prime then Real.log n else 0) * (12 - Real.log n) ^ j

/-- At nonnegative scale, recover a forward window moment by subtracting
the two cumulative moments. This permits a single prime sweep for both ends. -/
theorem quarter_prime_moment_prefix_656 {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    quarterPrimeMoment656 x j =
      quarterPrimePrefix656 ⌊Real.exp (21 / 8) * x⌋₊ j - quarterPrimePrefix656 ⌊x⌋₊ j := by
  have h₁ : 1 ≤ Real.exp (21 / 8) := Real.one_le_exp_iff.mpr (by norm_num only)
  have h := Nat.floor_mono (le_mul_of_one_le_left hx h₁)
  unfold quarterPrimeMoment656 quarterPrimePrefix656
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le ⌊x⌋₊) h,
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl), add_sub_cancel_left]

/-- At positive scale the prime sum is determined by the two endpoints
of each of the six cumulative moments. -/
theorem quarter_prime_sum_prefix_656 {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp (21 / 8) * x⌋₊,
        quarterWeight656 x n * (if n.Prime then Real.log n else 0)) =
      ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * x ^ (-(11 / 10) : ℝ)) *
        ∑ j ∈ Finset.range 6,
          (Nat.choose 5 j : ℝ) * (21 / 8 + Real.log x - 12) ^ (5 - j) *
            (quarterPrimePrefix656 ⌊Real.exp (21 / 8) * x⌋₊ j - quarterPrimePrefix656 ⌊x⌋₊ j) := by
  rw [quarter_prime_sum_moments_656 hx]
  simp only [quarter_prime_moment_prefix_656 hx.le]

/-- On a scale interval with positive lower endpoint, bound the prime sum
by one enlarged window. Use the lower endpoint for the decreasing power
and the upper endpoint for the increasing fifth-power polynomial. -/
theorem quarter_prime_sum_window_le_656 {l x u : ℝ} (hl : 0 < l) (hlx : l ≤ x) (hxu : x ≤ u) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp (21 / 8) * x⌋₊,
        quarterWeight656 x n * (if n.Prime then Real.log n else 0)) ≤
      ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * l ^ (-(11 / 10) : ℝ)) *
        ∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊Real.exp (21 / 8) * u⌋₊,
          (n : ℝ) ^ (3 / 5 : ℝ) * (21 / 8 + Real.log u - Real.log n) ^ 5 *
            (if n.Prime then Real.log n else 0) := by
  let C : ℝ := (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8))
  let S := Finset.Ioc ⌊x⌋₊ ⌊Real.exp (21 / 8) * x⌋₊
  let T := Finset.Ioc ⌊l⌋₊ ⌊Real.exp (21 / 8) * u⌋₊
  let G := fun (v : ℝ) (n : ℕ) ↦
    (n : ℝ) ^ (3 / 5 : ℝ) * (21 / 8 + Real.log v - Real.log n) ^ 5 *
      (if n.Prime then Real.log n else 0)
  have hx := hl.trans_le hlx
  have hu := hx.trans_le hxu
  have hc : 0 ≤ C := by
    dsimp only [C]; positivity
  have hG {v : ℝ} (hv : 0 < v) {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊Real.exp (21 / 8) * v⌋₊) :
    0 ≤ 21 / 8 + Real.log v - Real.log n := by
    have he := Real.exp_pos (21 / 8 : ℝ)
    have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
    have hm := (Nat.le_floor_iff (mul_nonneg he.le hv.le)).mp (Finset.mem_Ioc.mp hn).2
    have hlog := Real.log_le_log hn₀ hm
    rw [Real.log_mul he.ne' hv.ne', Real.log_exp] at hlog
    exact sub_nonneg.mpr hlog
  have hln (n : ℕ) : 0 ≤ (if n.Prime then Real.log n else 0) := by
    split
    · exact Real.log_natCast_nonneg n
    · exact le_rfl
  have hs : S ⊆ T :=
    Finset.Ioc_subset_Ioc (Nat.floor_mono hlx)
      (Nat.floor_mono (mul_le_mul_of_nonneg_left hxu (Real.exp_pos _).le))
  change
    (∑ n ∈ S, quarterWeight656 x n * (if n.Prime then Real.log n else 0)) ≤
      C * l ^ (-(11 / 10) : ℝ) * ∑ n ∈ T, G u n
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum (g := fun n ↦ C * l ^ (-(11 / 10) : ℝ) * G u n) ?_).trans ?_
  · intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn'.1)
    have hnG := hG hx (Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt hn'.1, hn'.2⟩)
    have hgu : G x n ≤ G u n := by
      dsimp only [G]
      apply mul_le_mul_of_nonneg_right _ (hln n)
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      exact
        pow_le_pow_left₀ hnG (sub_le_sub_right (add_le_add_right (Real.log_le_log hx hxu) _) _) _
    have hg₀ : 0 ≤ G x n := by
      dsimp only [G]
      exact
        mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (pow_nonneg hnG _)) (hln n)
    rw [forward_weight_factor hx hn₀, mul_assoc]
    change C * x ^ (-(11 / 10) : ℝ) * G x n ≤ _
    exact
      mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hl hlx (by norm_num only)) hc) hgu
        hg₀ (mul_nonneg hc (Real.rpow_nonneg hl.le _))
  · apply Finset.sum_le_sum_of_subset_of_nonneg hs
    intro n hn _
    have hn' := Finset.mem_Ioc.mp hn
    have hnG := hG hu (Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt hn'.1, hn'.2⟩)
    dsimp only [G]
    exact
      mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hl.le _))
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (pow_nonneg hnG _))
          (hln n))

/-- The polynomial on an enlarged window also uses differences of the
same six cumulative prime moments. The two integer bounds can be chosen
independently of the polynomial argument. -/
theorem quarter_prime_poly_prefix_656 {L U : ℕ} (hLU : L ≤ U) (z : ℝ) :
    (∑ n ∈ Finset.Ioc L U,
        (n : ℝ) ^ (3 / 5 : ℝ) * (z + 12 - Real.log n) ^ 5 * (if n.Prime then Real.log n else 0)) =
      ∑ j ∈ Finset.range 6,
        (Nat.choose 5 j : ℝ) * z ^ (5 - j) *
          (quarterPrimePrefix656 U j - quarterPrimePrefix656 L j) := by
  have h (j : ℕ) :
    quarterPrimePrefix656 U j - quarterPrimePrefix656 L j =
      ∑ n ∈ Finset.Ioc L U,
        (n : ℝ) ^ (3 / 5 : ℝ) * (if n.Prime then Real.log n else 0) * (12 - Real.log n) ^ j := by
    unfold quarterPrimePrefix656
    rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le L) hLU,
      Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl), add_sub_cancel_left]
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range 6)]
  apply Finset.sum_congr rfl
  intro n _
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  ring

/-- Uniformly on a positive scale interval, bound the forward sum by the
six enlarged-window moments evaluated at the interval endpoints. -/
theorem quarter_prime_sum_cell_le_656 {l x u : ℝ} (hl : 0 < l) (hlx : l ≤ x) (hxu : x ≤ u) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp (21 / 8) * x⌋₊,
        quarterWeight656 x n * (if n.Prime then Real.log n else 0)) ≤
      ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * l ^ (-(11 / 10) : ℝ)) *
        ∑ j ∈ Finset.range 6,
          (Nat.choose 5 j : ℝ) * (21 / 8 + Real.log u - 12) ^ (5 - j) *
            (quarterPrimePrefix656 ⌊Real.exp (21 / 8) * u⌋₊ j - quarterPrimePrefix656 ⌊l⌋₊ j) := by
  have hu := (hl.trans_le (hlx.trans hxu)).le
  have hm : ⌊l⌋₊ ≤ ⌊Real.exp (21 / 8) * u⌋₊ :=
    Nat.floor_mono
      ((hlx.trans hxu).trans
        (le_mul_of_one_le_left hu (Real.one_le_exp_iff.mpr (by norm_num only))))
  have h := quarter_prime_poly_prefix_656 hm (21 / 8 + Real.log u - 12)
  rw [sub_add_cancel] at h
  rw [← h]
  exact quarter_prime_sum_window_le_656 hl hlx hxu

/-- A rational upper bound for the scale polynomial and outward integer
bounds for the prime window give a certified prime-sum upper bound. The
normalization and six cumulative-moment differences may be bounded separately. -/
theorem quarter_prime_sum_rational_le_656 {x : ℝ} (hx : 0 < x) {L U : ℕ} (hL : L ≤ ⌊x⌋₊)
    (hU : ⌊Real.exp (21 / 8) * x⌋₊ ≤ U) {z K : ℚ} (M : ℕ → ℚ) (hz₀ : 0 ≤ z)
    (hz : 21 / 8 + Real.log x - 12 ≤ (z : ℝ))
    (hK :
      (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * x ^ (-(11 / 10) : ℝ) ≤ (K : ℝ))
    (hUz : (U : ℝ) ≤ Real.exp ((z : ℝ) + 12))
    (hM : ∀ j ∈ Finset.range 6, quarterPrimePrefix656 U j - quarterPrimePrefix656 L j ≤ (M j : ℝ)) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp (21 / 8) * x⌋₊,
        quarterWeight656 x n * (if n.Prime then Real.log n else 0)) ≤
      ((K * ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℚ) * z ^ (5 - j) * M j : ℚ) : ℝ) := by
  let V := Real.exp (21 / 8) * x
  let S := Finset.Ioc ⌊x⌋₊ ⌊V⌋₊
  let T := Finset.Ioc L U
  let C := (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * x ^ (-(11 / 10) : ℝ)
  let G := fun (w : ℝ) (n : ℕ) ↦
    (n : ℝ) ^ (3 / 5 : ℝ) * (w + 12 - Real.log n) ^ 5 * (if n.Prime then Real.log n else 0)
  have hCV : 0 ≤ C := by
    dsimp only [C]; positivity
  have hKU : 0 ≤ (K : ℝ) := hCV.trans hK
  have hST : S ⊆ T := Finset.Ioc_subset_Ioc hL hU
  have hV : x ≤ V :=
    le_mul_of_one_le_left hx.le (Real.one_le_exp_iff.mpr (by norm_num only : (0 : ℝ) ≤ 21 / 8))
  have hLU := hL.trans ((Nat.floor_mono hV).trans hU)
  have hlog (n : ℕ) : 0 ≤ (if n.Prime then Real.log n else 0) := by
    split
    · exact Real.log_natCast_nonneg n
    · exact le_rfl
  have hbase {n : ℕ} (hn : n ∈ S) : 0 ≤ 21 / 8 + Real.log x - Real.log n := by
    have he := Real.exp_pos (21 / 8 : ℝ)
    have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1)
    have hu := (Nat.le_floor_iff (mul_nonneg he.le hx.le)).mp (Finset.mem_Ioc.mp hn).2
    have h := Real.log_le_log hn₀ hu
    rw [Real.log_mul he.ne' hx.ne', Real.log_exp] at h
    exact sub_nonneg.mpr h
  have hS (n : ℕ) (hn : n ∈ S) :
    quarterWeight656 x n * (if n.Prime then Real.log n else 0) ≤ (K : ℝ) * G (z : ℝ) n := by
    have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1)
    rw [forward_weight_factor hx hn₀, mul_assoc]
    have hleft : C * G (21 / 8 + Real.log x - 12) n ≤ (K : ℝ) * G (z : ℝ) n := by
      have h₀ := hbase hn
      have h₁ : 21 / 8 + Real.log x - Real.log n ≤ (z : ℝ) + 12 - Real.log n := by
        linarith only [hz]
      have hG : G (21 / 8 + Real.log x - 12) n ≤ G (z : ℝ) n := by
        simp only [G, sub_add_cancel]
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h₀ h₁ 5)
              (Real.rpow_nonneg (Nat.cast_nonneg n) _))
            (hlog n)
      have hnG : 0 ≤ G (21 / 8 + Real.log x - 12) n := by
        simp only [G, sub_add_cancel]
        exact
          mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (pow_nonneg h₀ _))
            (hlog n)
      exact mul_le_mul hK hG hnG hKU
    simpa only [C, G, sub_add_cancel] using hleft
  have hT : (∑ n ∈ S, G (z : ℝ) n) ≤ ∑ n ∈ T, G (z : ℝ) n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hST
    intro n hn _
    have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1)
    dsimp only [G]
    exact
      mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hn₀.le _)
          (pow_nonneg
            (by
              have hnU : (n : ℝ) ≤ U := Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2
              exact sub_nonneg.mpr ((Real.log_le_iff_le_exp hn₀).mpr (hnU.trans hUz)))
            _))
        (hlog n)
  have hh := Finset.sum_le_sum hS
  rw [← Finset.mul_sum] at hh
  refine (hh.trans (mul_le_mul_of_nonneg_left hT hKU)).trans ?_
  dsimp only [T, G]
  rw [quarter_prime_poly_prefix_656 hLU]
  simp only [Rat.cast_mul, Rat.cast_sum, Rat.cast_pow, Rat.cast_natCast]
  apply mul_le_mul_of_nonneg_left _ hKU
  apply Finset.sum_le_sum
  intro j hj
  exact
    mul_le_mul_of_nonneg_left (hM j hj)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Rat.cast_nonneg.mpr hz₀) _))

end PseudoPrime.PrimeTestBounds.MillerRabin
