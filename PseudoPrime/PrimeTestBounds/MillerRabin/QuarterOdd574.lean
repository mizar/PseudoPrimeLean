/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquare570

/-! # Recovery of the odd prime powers in section 62 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def oddData574 : Finset (ℕ × ℕ) :=
  {(47, 3), (53, 3), (59, 3), (61, 3), (67, 3), (71, 3), (73, 3), (79, 3),
    (83, 3), (89, 3), (97, 3), (101, 3), (103, 3), (107, 3), (109, 3), (11, 5), (13, 5), (7, 7),
    (3, 11), (2, 17), (2, 19)}

private def oddIndices574 :=
  oddData574.image (fun u ↦ u.1 ^ u.2)

private theorem odd_data (p j : ℕ) (h : (p, j) ∈ oddData574) :
    p.Prime ∧ p ≤ 285 ^ 2 ∧ 313 ^ 2 < p ^ j ∧ (p ^ j).sqrt ^ 2 ≠ p ^ j := by
  exact
    (show
        ∀ u ∈ oddData574,
          Nat.Prime u.1 ∧ u.1 ≤ 285 ^ 2 ∧ 313 ^ 2 < u.1 ^ u.2 ∧ (u.1 ^ u.2).sqrt ^ 2 ≠ u.1 ^ u.2
        by decide +kernel)
      (p, j) h

private theorem prefix_add_powers_574 (K : LLS.PaperStatements.MellinKernel) {p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) {R : ℝ} (hl : 285 ≤ R) (hu : R ≤ 313) (S : Finset ℕ)
    (hs : ∀ k ∈ S, (k : ℝ) ≤ R ^ 2 ∧ R ^ 2 < (k : ℝ) ^ 2)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → c l = 1) :
    let X := R ^ 2
    let f := fun k : ℕ ↦ (K.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ S, f (k ^ 2)) + 4 * (∑ k ∈ oddIndices574, f k) -
        (∑' k : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, K.summand a X k).re + (∑' k : ℕ, K.summand b X k).re +
        (∑' k : ℕ, K.summand c X k).re := by
  intro X f
  have hX : 0 < X := sq_pos_of_pos (by linarith only [hl])
  let P := Finset.Ioc 0 ⌊X⌋₊
  let T := S.image (fun k ↦ k ^ 2)
  have hd : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro m hm ht'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht'
    exact
      (not_lt_of_ge ((Nat.le_floor_iff hX.le).mp (Finset.mem_Ioc.mp hm).2))
        (by exact_mod_cast (hs k hk).2)
  have hodd (m : ℕ) (hm : m ∈ oddIndices574) :
    R ^ 2 < m ∧ ∃ p j : ℕ, p.Prime ∧ (p : ℝ) ≤ R ^ 2 ∧ m = p ^ j := by
    obtain ⟨⟨p, j⟩, hmem, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hp, hp', hm', _⟩ := odd_data p j hmem
    have hR : 0 ≤ R := by linarith only [hl]
    exact
      ⟨(pow_le_pow_left₀ hR hu 2).trans_lt (by exact_mod_cast hm'), p, j, hp,
        (show (p : ℝ) ≤ 285 ^ 2 by exact_mod_cast hp').trans
          (pow_le_pow_left₀ (by norm_num only) hl 2),
        rfl⟩
  have hd' : Disjoint (P ∪ T) oddIndices574 := by
    apply Finset.disjoint_left.mpr
    intro m hm hm'
    rcases Finset.mem_union.mp hm with hP | hT
    · exact (not_lt_of_ge ((Nat.le_floor_iff hX.le).mp (Finset.mem_Ioc.mp hP).2)) (hodd m hm').1
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨⟨p, j⟩, hmem, heq⟩ := Finset.mem_image.mp hm'
    have hns := (odd_data p j hmem).2.2.2
    apply hns
    rw [heq]
    simp only [Nat.sqrt_eq']
  have oneAt {d : ℕ} (χ : DirichletCharacter ℂ d)
    (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → χ l = 1) {m : ℕ} (hm : m ∈ (P ∪ T) ∪ oddIndices574)
    (hΛ : ArithmeticFunction.vonMangoldt m ≠ 0) : χ m = 1 := by
    have base {k : ℕ} (hk : (k : ℝ) ≤ R ^ 2) (hv : ArithmeticFunction.vonMangoldt k ≠ 0) :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl hlX _ ↦ hχ l hl hlX) hk (Nat.coprime_one_right k) hv
    rcases Finset.mem_union.mp hm with hm | hm'
    · rcases Finset.mem_union.mp hm with hm | hm
      · exact base ((Nat.le_floor_iff hX.le).mp (Finset.mem_Ioc.mp hm).2) hΛ
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0)] at hΛ
      rw [Nat.cast_pow, map_pow, base (hs k hk).1 hΛ, one_pow]
    obtain ⟨p, j, hp, hpX, rfl⟩ := (hodd m hm').2
    rw [Nat.cast_pow, map_pow, hχ p hp hpX, one_pow]
  have hc :=
    kernel_three_principal_prefix K a b c hX ((P ∪ T) ∪ oddIndices574) ht
      (by
        intro k hk hv
        rw [oneAt a hA hk hv, oneAt b hB hk hv, oneAt c hC hk hv, Complex.one_re]
        norm_num only)
  rw [Finset.sum_union hd', Finset.sum_union hd,
    Finset.sum_image (fun _ _ _ _ h ↦ Nat.pow_left_injective (by decide : 2 ≠ 0) h)] at hc
  dsimp only [f]
  linarith only [hc]

/-- Four times the principal mass at the twenty-one odd prime powers selected in
section 62, evaluated at the square of radius R. -/
noncomputable def oddGain574 (R : ℝ) : ℝ :=
  4 * ∑ k ∈ oddIndices574, (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (R ^ 2) k).re

/-- On the radius interval from 285 to 292, prime triviality and the trace lower bound
recover both the chosen squares and the odd prime powers above the prefix. -/
theorem square_odd_lower_584 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {R : ℝ}
    (hl : 285 ≤ R) (hu : R ≤ 292) (S : Finset ℕ)
    (hs : ∀ k ∈ S, (k : ℝ) ≤ R ^ 2 ∧ R ^ 2 < (k : ℝ) ^ 2)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → c l = 1) :
    let X := R ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ S, f (k ^ 2)) + oddGain574 R -
        (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  exact
    prefix_add_powers_574 quarterKernel570 a b c hl (hu.trans (by norm_num only)) S hs ht hA hB hC

/-- On the radius interval from 285 to 300, prime triviality and the trace lower bound
recover both the chosen squares and the odd prime powers above the prefix. -/
theorem square_odd_lower_600 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {R : ℝ}
    (hl : 285 ≤ R) (hu : R ≤ 300) (S : Finset ℕ)
    (hs : ∀ k ∈ S, (k : ℝ) ≤ R ^ 2 ∧ R ^ 2 < (k : ℝ) ^ 2)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → c l = 1) :
    let X := R ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ S, f (k ^ 2)) + oddGain574 R -
        (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  exact
    prefix_add_powers_574 quarterKernel570 a b c hl (hu.trans (by norm_num only)) S hs ht hA hB hC

/-- On the radius interval from 285 to 313, prime triviality and the trace lower bound
recover both the chosen squares and the odd prime powers above the prefix. -/
theorem square_odd_lower_626 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {R : ℝ}
    (hl : 285 ≤ R) (hu : R ≤ 313) (S : Finset ℕ)
    (hs : ∀ k ∈ S, (k : ℝ) ≤ R ^ 2 ∧ R ^ 2 < (k : ℝ) ^ 2)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → c l = 1) :
    let X := R ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ S, f (k ^ 2)) + oddGain574 R -
        (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  exact prefix_add_powers_574 quarterKernel570 a b c hl hu S hs ht hA hB hC

private theorem fifth_increasing :
    MonotoneOn (fun t : ℝ ↦ t ^ 5 * Real.exp (-t)) (Set.Icc 0 5) := by
  have hd (t : ℝ) :=
    ((hasDerivAt_pow 5 t).mul (Real.hasDerivAt_exp _ |>.comp t (hasDerivAt_id t).neg))
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun t _ ↦ (hd t).continuousAt.continuousWithinAt
  · exact fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    change 0 ≤ deriv ((fun x : ℝ ↦ x ^ 5) * Real.exp ∘ (-id)) t
    rw [(hd t).deriv]
    change 0 ≤ 5 * t ^ 4 * Real.exp (-t) + t ^ 5 * (Real.exp (-t) * -1)
    have hu : t ≤ 5 := (interior_subset ht : t ∈ Set.Icc 0 5).2
    have h :=
      mul_nonneg (sub_nonneg.mpr hu) (mul_nonneg (by positivity : 0 ≤ t ^ 4) (Real.exp_pos (-t)).le)
    linarith only [h]

private theorem power_term_mono {m U : ℕ} (hb : U ^ 2 < m ∧ m ≤ 16 * 285 ^ 2) {a r : ℝ}
    (ha0 : 285 ≤ a) (hl : a ≤ r) (hu : r ≤ U) :
    (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (a ^ 2) m).re ≤
      (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) m).re := by
  have haP : 0 < a := by linarith only [ha0]
  have hr : 0 < r := haP.trans_le hl
  have hm0 : 0 < m := Nat.zero_lt_of_lt hb.1
  have hx := pow_le_pow_left₀ haP.le hl 2
  have hm1 : r ^ 2 ≤ (m : ℝ) := (pow_le_pow_left₀ hr.le hu 2).trans (by exact_mod_cast hb.1.le)
  have ha :=
    Real.log_le_log (div_pos (Nat.cast_pos.mpr hm0) (sq_pos_of_pos hr))
      (div_le_div_of_nonneg_left (Nat.cast_nonneg m) (sq_pos_of_pos haP) hx)
  have h16 : Real.log ((m : ℝ) / a ^ 2) ≤ Real.log ((2 : ℝ) ^ 4) := by
    apply Real.log_le_log (by positivity)
    apply (div_le_iff₀ (sq_pos_of_pos haP)).mpr
    have h :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 285) ha0 2)
        (by norm_num only : (0 : ℝ) ≤ 16)
    norm_num only
    exact (show (m : ℝ) ≤ 16 * (285 : ℝ) ^ 2 by exact_mod_cast hb.2).trans h
  rw [Real.log_pow, Nat.cast_ofNat] at h16
  have hs : Real.log ((m : ℝ) / a ^ 2) ≤ 14 / 5 := by linarith only [h16, Real.log_two_lt_d9]
  have h0 := Real.log_nonneg ((one_le_div (sq_pos_of_pos hr)).mpr hm1)
  rw [quarter_summand_570 (sq_pos_of_pos haP) hm0 hs,
    quarter_summand_570 (sq_pos_of_pos hr) hm0 (ha.trans hs)]
  apply mul_le_mul_of_nonneg_right _ (ArithmeticFunction.vonMangoldt_nonneg)
  unfold quarterWeight570
  dsimp only
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num only)
  apply fifth_increasing
  · constructor <;> norm_num only <;> linarith only [hs, ha, h0]
  · constructor <;> norm_num only <;> linarith only [hs, ha, h0]
  · norm_num only
    linarith only [ha]

private theorem term_mono {m : ℕ} (hm : m ∈ oddIndices574) {a r : ℝ} (ha : 285 ≤ a) (har : a ≤ r)
    (hr : r ≤ 313) :
    (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (a ^ 2) m).re ≤
      (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) m).re := by
  have h := (show ∀ k ∈ oddIndices574, 313 ^ 2 < k ∧ k ≤ 16 * 285 ^ 2 by decide +kernel) m hm
  exact power_term_mono h ha har hr

/-- Each selected odd power remains inside the support, where its principal
weight increases from the left endpoint. Summation gives the same lower bound
throughout the radius interval from 285 to 292. -/
theorem odd_gain_endpoint_584 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 292) :
    oddGain574 285 ≤ oddGain574 r := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num only : (0 : ℝ) ≤ 4)
  exact Finset.sum_le_sum (fun k hk ↦ term_mono hk (le_refl _) hl (hu.trans (by norm_num only)))

/-- On the section 99 interval, the selected odd prime powers can be
evaluated at any earlier radius from 285 onward. -/
theorem odd_gain_mono_600 {a r : ℝ} (ha : 285 ≤ a) (h : a ≤ r) (hr : r ≤ 300) :
    oddGain574 a ≤ oddGain574 r := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num only : (0 : ℝ) ≤ 4)
  exact Finset.sum_le_sum (fun _ hk ↦ term_mono hk ha h (hr.trans (by norm_num only)))

private def expCap (v : ℚ) : ℚ :=
  (∑ k ∈ Finset.range 16, v ^ k / (k.factorial : ℚ)) + v ^ 16 / ((16 : ℕ).factorial : ℚ) * 2

private theorem exp_cap_sound {v : ℚ} (hv : 0 ≤ v) (hu : v ≤ 3) :
    Real.exp (v : ℝ) ≤ (expCap v : ℝ) := by
  have h0 : (0 : ℝ) ≤ v := by exact_mod_cast hv
  have h3 : (v : ℝ) ≤ 3 := by exact_mod_cast hu
  have h :=
    Analysis.exp_le_taylor_add_two_next (n := 16) h0
      (by
        norm_num only [Nat.reduceAdd, Nat.cast_ofNat]; linarith only [h3])
  simpa only [expCap, Rat.cast_add, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_ofNat] using h

private theorem credit_lower {R p j : ℕ} (hR : 0 < R) (hp : p.Prime) (hj : j ≠ 0)
    {lo hi vl vu root credit : ℝ} (hpLog : lo ≤ Real.log p)
    (harg : Real.log ((p : ℝ) ^ j / (R : ℝ) ^ 2) ≤ 14 / 5)
    (hvl : vl ≤ (14 / 5 - Real.log ((p : ℝ) ^ j / (R : ℝ) ^ 2)) * (51 / 50))
    (hvu : (14 / 5 - Real.log ((p : ℝ) ^ j / (R : ℝ) ^ 2)) * (51 / 50) ≤ vu) (he : Real.exp vu ≤ hi)
    (hs : Real.sqrt ((p : ℝ) ^ j) ≤ root) (hv : 0 ≤ vl) (hl : 0 ≤ lo) (hc : 0 ≤ credit)
    (hnum : credit * (root * (120 * hi)) ≤ 4 * lo * vl ^ 5) :
    credit ≤
      4 * (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) ((R : ℝ) ^ 2) (p ^ j)).re := by
  rw [quarter_summand_570 (sq_pos_of_pos (Nat.cast_pos.mpr hR)) (pow_pos hp.pos j)
      (by simpa only [Nat.cast_pow] using harg),
    ArithmeticFunction.vonMangoldt_apply_pow hj, ArithmeticFunction.vonMangoldt_apply_prime hp]
  let v := (14 / 5 - Real.log ((p : ℝ) ^ j / (R : ℝ) ^ 2)) * (51 / 50)
  have hpos : 0 < Real.sqrt ((p : ℝ) ^ j) := Real.sqrt_pos.mpr (pow_pos (Nat.cast_pos.mpr hp.pos) j)
  have hxp := (Real.exp_le_exp.mpr hvu).trans he
  have hden :=
    mul_le_mul hs (mul_le_mul_of_nonneg_left hxp (by norm_num only : (0 : ℝ) ≤ 120))
      (mul_nonneg (by norm_num only) (Real.exp_pos _).le) (hpos.le.trans hs)
  have hprod := mul_le_mul hpLog (pow_le_pow_left₀ hv hvl 5) (pow_nonneg hv 5) (hl.trans hpLog)
  simp only [quarterWeight570, Nat.cast_pow]
  rw [show (2 * (7 / 5) - Real.log ((p : ℝ) ^ j / (R : ℝ) ^ 2)) / (2 * (25 / 51)) = v by
      dsimp only [v]; ring,
    Real.exp_neg]
  have h := (mul_le_mul_of_nonneg_left hden hc).trans hnum
  change credit * (Real.sqrt ((p : ℝ) ^ j) * (120 * Real.exp v)) ≤ _ at h
  change lo * vl ^ 5 ≤ Real.log p * v ^ 5 at hprod
  calc
    credit ≤ (4 * Real.log p * v ^ 5) / (Real.sqrt ((p : ℝ) ^ j) * (120 * Real.exp v)) := by
      apply (le_div_iff₀ (mul_pos hpos (mul_pos (by norm_num only) (Real.exp_pos v)))).mpr
      linarith only [h, hprod]
    _ = _ := by ring

private structure Row where
  p : ℕ
  j : ℕ
  jp : ℕ
  jm : ℕ
  lp : ℕ
  low : ℕ
  high : ℕ
  root : ℕ
  credit : ℕ
  deriving DecidableEq

private def Row.v (n : ℕ) : ℚ :=
  (14 / 5 - n / 1000000) * (51 / 50)

private def Row.Valid (a : Row) (R : ℕ) : Prop :=
  a.p.Prime ∧
    a.j ≠ 0 ∧
    Analysis.rationalLogIntervalCheck a.p a.jp 32 (a.lp / 1000000) 7 = true ∧
    Analysis.rationalLogIntervalCheck ((a.p : ℚ) ^ a.j / (R : ℚ) ^ 2) a.jm 32 (a.low / 1000000)
        (a.high / 1000000) =
      true ∧
    (a.high : ℚ) / 1000000 ≤ 14 / 5 ∧
    0 ≤ Row.v a.high ∧
    0 ≤ Row.v a.low ∧
    Row.v a.low ≤ 3 ∧
    (a.p : ℚ) ^ a.j ≤ ((a.root : ℚ) / 1000) ^ 2 ∧
    (a.credit : ℚ) / 10000000000 * (a.root / 1000 * (120 * expCap (Row.v a.low))) ≤
      4 * (a.lp / 1000000) * Row.v a.high ^ 5

private instance (a : Row) (R : ℕ) : Decidable (a.Valid R) := by
  unfold Row.Valid; infer_instance

private theorem row_sound (a : Row) {R : ℕ} (hR : 0 < R) (ha : a.Valid R) :
    (a.credit : ℝ) / 10000000000 ≤
      4 * (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) ((R : ℝ) ^ 2) (a.p ^ a.j)).re := by
  obtain ⟨hp, hj, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ha
  have hl := (Analysis.rationalLogIntervalCheck_sound h1).1
  have hm := Analysis.rationalLogIntervalCheck_sound h2
  have ht := exp_cap_sound h5 h6
  have hn := (Rat.cast_le (K := ℝ)).mpr h8
  have hs := (Rat.cast_le (K := ℝ)).mpr h7
  have hu := (Rat.cast_le (K := ℝ)).mpr h3
  have hv := (Rat.cast_le (K := ℝ)).mpr h4
  simp only [Row.v, Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_zero] at hl hm hn hs hu hv ht
  apply credit_lower hR hp hj hl (hm.2.trans hu) _ _ ht _ hv (by positivity) (by positivity) hn
  · linarith only [hm.2]
  · linarith only [hm.1]
  · exact (Real.sqrt_le_iff.mpr ⟨by positivity, hs⟩)

private def rows : List Row :=
  [⟨47, 3, 6, 0, 3850147, 245464, 245465, 322216, 35331311⟩,
    ⟨53, 3, 6, 1, 3970291, 605897, 605898, 385846, 20541275⟩,
    ⟨59, 3, 6, 1, 4077537, 927633, 927634, 453188, 11285763⟩,
    ⟨61, 3, 6, 1, 4110873, 1027643, 1027644, 476426, 9108640⟩,
    ⟨67, 3, 6, 2, 4204692, 1309099, 1309100, 548419, 4542593⟩,
    ⟨71, 3, 6, 2, 4262679, 1483061, 1483062, 598257, 2710958⟩,
    ⟨73, 3, 6, 2, 4290459, 1566399, 1566400, 623713, 2054987⟩,
    ⟨79, 3, 6, 3, 4369447, 1803365, 1803366, 702168, 814804⟩,
    ⟨83, 3, 6, 3, 4418840, 1951543, 1951544, 756166, 397985⟩,
    ⟨89, 3, 6, 3, 4488636, 2160930, 2160931, 839625, 109282⟩,
    ⟨97, 3, 7, 3, 4574710, 2419154, 2419155, 955340, 9574⟩,
    ⟨101, 3, 7, 4, 4615120, 2540383, 2540384, 1015038, 1514⟩,
    ⟨103, 3, 7, 4, 4634728, 2599208, 2599209, 1045336, 433⟩,
    ⟨107, 3, 7, 4, 4672828, 2713508, 2713509, 1106817, 6⟩,
    ⟨109, 3, 7, 4, 4691347, 2769065, 2769066, 1137994, 0⟩,
    ⟨11, 5, 3, 1, 2397895, 684498, 684499, 401312, 10768814⟩,
    ⟨13, 5, 4, 2, 2564949, 1519768, 1519769, 609339, 1443521⟩,
    ⟨7, 7, 3, 3, 1945910, 2316392, 2316393, 907493, 12746⟩,
    ⟨3, 11, 2, 1, 1098612, 779756, 779757, 420889, 4117616⟩,
    ⟨2, 17, 1, 1, 693147, 478523, 478524, 362039, 4450428⟩,
    ⟨2, 19, 1, 3, 693147, 1864818, 1864819, 724078, 97080⟩]

private theorem rows_valid : ∀ a ∈ rows, a.Valid 285 := by decide +kernel

private theorem indices_eq : oddIndices574 = rows.toFinset.image (fun a ↦ a.p ^ a.j) := by
  decide +kernel

private theorem rows_inj :
    ∀ a ∈ rows.toFinset, ∀ b ∈ rows.toFinset, a.p ^ a.j = b.p ^ b.j → a = b := by decide +kernel

private theorem credit_total : (107700000 : ℕ) < ∑ a ∈ rows.toFinset, a.credit := by decide +kernel

attribute [local irreducible] rows oddIndices574 in
/-- On the radius interval from 285 to 292 the selected odd prime powers contribute
more than 0.01077. Certify the left endpoint term by term, then use monotonicity. -/
theorem odd_gain_lower_584 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 292) :
    1077 / 100000 < oddGain574 r := by
  apply lt_of_lt_of_le _ (odd_gain_endpoint_584 hl hu)
  have hsum :=
    Finset.sum_le_sum (s := rows.toFinset)
      (fun a ha ↦ row_sound a (by decide : 0 < 285) (rows_valid a (List.mem_toFinset.mp ha)))
  unfold oddGain574
  rw [indices_eq, Finset.sum_image rows_inj, Finset.mul_sum]
  apply lt_of_lt_of_le _ hsum
  rw [← Finset.sum_div]
  have hh : (107700000 : ℝ) < ∑ a ∈ rows.toFinset, (a.credit : ℝ) := by exact_mod_cast credit_total
  linarith only [hh]

/-- On the section 62 radius interval, prime triviality and the trace lower bound
recover both the chosen squares and the odd prime powers above the prefix. -/
theorem square_odd_lower_574 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {R : ℝ}
    (hl : 285 ≤ R) (hu : R ≤ 287) (S : Finset ℕ)
    (hs : ∀ k ∈ S, (k : ℝ) ≤ R ^ 2 ∧ R ^ 2 < (k : ℝ) ^ 2)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → c l = 1) :
    let X := R ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ S, f (k ^ 2)) + oddGain574 R -
        (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  exact square_odd_lower_584 a b c hl (hu.trans (by norm_num only)) S hs ht hA hB hC

/-- Each selected odd power remains inside the support, where its principal
weight increases from the left endpoint. Summation gives the same lower bound
throughout the section 62 radius interval. -/
theorem odd_gain_endpoint_574 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287) :
    oddGain574 285 ≤ oddGain574 r := by exact odd_gain_endpoint_584 hl (hu.trans (by norm_num only))

/-- On the entire section 62 interval the selected odd prime powers contribute
more than 0.01077. Certify the left endpoint term by term, then use monotonicity. -/
theorem odd_gain_lower_574 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287) :
    1077 / 100000 < oddGain574 r := by exact odd_gain_lower_584 hl (hu.trans (by norm_num only))

/-- On the radius interval from 285 to 288, prime triviality and the trace lower bound
recover both the chosen squares and the odd prime powers above the prefix. -/
theorem square_odd_lower_576 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {R : ℝ}
    (hl : 285 ≤ R) (hu : R ≤ 288) (S : Finset ℕ)
    (hs : ∀ k ∈ S, (k : ℝ) ≤ R ^ 2 ∧ R ^ 2 < (k : ℝ) ^ 2)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → c l = 1) :
    let X := R ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ S, f (k ^ 2)) + oddGain574 R -
        (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  exact square_odd_lower_584 a b c hl (hu.trans (by norm_num only)) S hs ht hA hB hC

/-- Each selected odd power remains inside the support, where its principal
weight increases from the left endpoint. Summation gives the same lower bound
throughout the radius interval from 285 to 288. -/
theorem odd_gain_endpoint_576 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 288) :
    oddGain574 285 ≤ oddGain574 r := by exact odd_gain_endpoint_584 hl (hu.trans (by norm_num only))

/-- On the radius interval from 285 to 288 the selected odd prime powers contribute
more than 0.01077. Certify the left endpoint term by term, then use monotonicity. -/
theorem odd_gain_lower_576 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 288) :
    1077 / 100000 < oddGain574 r := by exact odd_gain_lower_584 hl (hu.trans (by norm_num only))

/-- Sum the certified credits over the common set of prime-power indices. -/
private theorem endpoint_rows_lower {R : ℕ} (hR : 0 < R) (data : List Row)
    (hv : ∀ a ∈ data, a.Valid R) (he : oddIndices574 = data.toFinset.image (fun a ↦ a.p ^ a.j))
    (hi : ∀ a ∈ data.toFinset, ∀ b ∈ data.toFinset, a.p ^ a.j = b.p ^ b.j → a = b) {M : ℕ}
    (hm : M < ∑ a ∈ data.toFinset, a.credit) : (M : ℝ) / 10000000000 < oddGain574 R := by
  have hs :=
    Finset.sum_le_sum (s := data.toFinset)
      (fun a ha ↦ row_sound a hR (hv a (List.mem_toFinset.mp ha)))
  unfold oddGain574
  rw [he, Finset.sum_image hi, Finset.mul_sum]
  apply lt_of_lt_of_le _ hs
  rw [← Finset.sum_div]
  have hh : (M : ℝ) < ∑ a ∈ data.toFinset, (a.credit : ℝ) := by exact_mod_cast hm
  linarith only [hh]

private def rows292 : List Row :=
  [⟨47, 3, 6, 1, 3850147, 196934, 196937, 322216, 36942478⟩,
    ⟨53, 3, 6, 1, 3970291, 557367, 557370, 385846, 21808893⟩,
    ⟨59, 3, 6, 2, 4077537, 879103, 879106, 453188, 12206646⟩,
    ⟨61, 3, 6, 2, 4110873, 979112, 979115, 476426, 9922316⟩,
    ⟨67, 3, 6, 2, 4204692, 1260569, 1260572, 548419, 5074115⟩,
    ⟨71, 3, 6, 3, 4262679, 1434531, 1434534, 598257, 3091737⟩,
    ⟨73, 3, 6, 3, 4290459, 1517869, 1517872, 623713, 2371899⟩,
    ⟨79, 3, 6, 3, 4369447, 1754834, 1754837, 702168, 983549⟩,
    ⟨83, 3, 6, 3, 4418840, 1903013, 1903016, 756166, 500201⟩,
    ⟨89, 3, 6, 4, 4488636, 2112400, 2112403, 839625, 149961⟩,
    ⟨97, 3, 7, 4, 4574710, 2370624, 2370627, 955340, 16595⟩,
    ⟨101, 3, 7, 4, 4615120, 2491852, 2491855, 1015038, 3393⟩,
    ⟨103, 3, 7, 4, 4634728, 2550678, 2550681, 1045336, 1216⟩,
    ⟨107, 3, 7, 4, 4672828, 2664977, 2664980, 1106817, 58⟩,
    ⟨109, 3, 7, 4, 4691347, 2720535, 2720538, 1137994, 2⟩,
    ⟨11, 5, 3, 1, 2397895, 635967, 635970, 401312, 11479415⟩,
    ⟨13, 5, 4, 3, 2564949, 1471238, 1471241, 609339, 1654681⟩,
    ⟨7, 7, 3, 4, 1945910, 2267862, 2267865, 907493, 19565⟩,
    ⟨3, 11, 2, 2, 1098612, 731226, 731229, 420889, 4412573⟩,
    ⟨2, 17, 1, 1, 693147, 429993, 429996, 362039, 4697082⟩,
    ⟨2, 19, 1, 3, 693147, 1816287, 1816290, 724078, 118982⟩]

/-- The section 99 odd-power gain clears 0.01154 from radius 292 through 300. -/
theorem odd_gain_lower_292_300 {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) : 0.01154 < oddGain574 r := by
  have h :=
    endpoint_rows_lower (R := 292) (by decide) rows292 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (M := 115400000) (by decide +kernel)
  apply lt_of_lt_of_le _ (odd_gain_mono_600 (by norm_num only : (285 : ℝ) ≤ 292) hl hu)
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

private def rows299 : List Row :=
  [⟨47, 3, 6, 1, 3850147, 149554, 149557, 322216, 38521799⟩,
    ⟨53, 3, 6, 1, 3970291, 509987, 509990, 385846, 23069808⟩,
    ⟨59, 3, 6, 2, 4077537, 831724, 831727, 453188, 13137662⟩,
    ⟨61, 3, 6, 2, 4110873, 931733, 931736, 476426, 10749883⟩,
    ⟨67, 3, 6, 2, 4204692, 1213189, 1213192, 548419, 5625963⟩,
    ⟨71, 3, 6, 3, 4262679, 1387151, 1387154, 598257, 3493686⟩,
    ⟨73, 3, 6, 3, 4290459, 1470490, 1470493, 623713, 2709596⟩,
    ⟨79, 3, 6, 3, 4369447, 1707455, 1707458, 702168, 1169712⟩,
    ⟨83, 3, 6, 3, 4418840, 1855633, 1855636, 756166, 616496⟩,
    ⟨89, 3, 6, 3, 4488636, 2065020, 2065023, 839625, 199384⟩,
    ⟨97, 3, 7, 4, 4574710, 2323244, 2323247, 955340, 26688⟩,
    ⟨101, 3, 7, 4, 4615120, 2444473, 2444476, 1015038, 6611⟩,
    ⟨103, 3, 7, 4, 4634728, 2503298, 2503301, 1045336, 2770⟩,
    ⟨107, 3, 7, 4, 4672828, 2617598, 2617601, 1106817, 258⟩,
    ⟨109, 3, 7, 4, 4691347, 2673155, 2673158, 1137994, 41⟩,
    ⟨11, 5, 3, 1, 2397895, 588588, 588591, 401312, 12188795⟩,
    ⟨13, 5, 4, 3, 2564949, 1423858, 1423861, 609339, 1878479⟩,
    ⟨7, 7, 3, 4, 1945910, 2220482, 2220485, 907493, 28558⟩,
    ⟨3, 11, 2, 1, 1098612, 683847, 683850, 420889, 4708409⟩,
    ⟨2, 17, 1, 1, 693147, 382613, 382616, 362039, 4941088⟩,
    ⟨2, 19, 1, 3, 693147, 1768908, 1768911, 724078, 143430⟩]

/-- The section 99 odd-power gain clears 0.01232 from radius 299 through 300. -/
theorem odd_gain_lower_299_300 {r : ℝ} (hl : 299 ≤ r) (hu : r ≤ 300) : 0.01232 < oddGain574 r := by
  have h :=
    endpoint_rows_lower (R := 299) (by decide) rows299 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (M := 123200000) (by decide +kernel)
  apply lt_of_lt_of_le _ (odd_gain_mono_600 (by norm_num only : (285 : ℝ) ≤ 299) hl hu)
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

/-- Insert the two certified odd-power gains into the arithmetic comparison.
The principal and selected square contributions remain explicit inputs. -/
theorem section99_arithmetic_lower {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    {r P S : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) (roots : Finset ℕ)
    (hroots : ∀ k ∈ roots, (k : ℝ) ≤ r ^ 2 ∧ r ^ 2 < (k : ℝ) ^ 2)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    P ≤
        4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) -
          (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re →
      S ≤ 4 * (∑ k ∈ roots, f (k ^ 2)) →
      P + S + (if r ≤ 299 then 0.01154 else 0.01232) <
        (∑' k : ℕ, quarterKernel570.summand a X k).re +
          (∑' k : ℕ, quarterKernel570.summand b X k).re +
          (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  intro X f hP hS
  have h :=
    square_odd_lower_600 a b c ((by norm_num only : (285 : ℝ) ≤ 292).trans hl) hu roots hroots ht hA
      hB hC
  have ho : (if r ≤ 299 then 0.01154 else 0.01232) < oddGain574 r := by
    split_ifs with hr
    · exact odd_gain_lower_292_300 hl hu
    · exact odd_gain_lower_299_300 (le_of_not_ge hr) hu
  dsimp only [X, f] at hP hS ⊢
  dsimp only at h
  linarith only [h, hP, hS, ho]

private def squareRows600 : List Row :=
  [⟨307, 2, 9, 1, 5726846, 100186, 100189, 307000, 62713192⟩,
    ⟨311, 2, 9, 1, 5739791, 126077, 126080, 311000, 60710234⟩,
    ⟨313, 2, 9, 1, 5746202, 138897, 138900, 313000, 59731814⟩,
    ⟨317, 2, 9, 1, 5758900, 164294, 164297, 317000, 57819746⟩,
    ⟨331, 2, 9, 1, 5802117, 250728, 250731, 331000, 51574964⟩,
    ⟨337, 2, 9, 1, 5820081, 286657, 286660, 337000, 49099074⟩,
    ⟨347, 2, 9, 1, 5849323, 345140, 345143, 347000, 45220140⟩,
    ⟨349, 2, 9, 1, 5855070, 356635, 356638, 349000, 44479775⟩,
    ⟨353, 2, 9, 1, 5866467, 379427, 379430, 353000, 43033177⟩,
    ⟨359, 2, 9, 1, 5883321, 413136, 413139, 359000, 40945805⟩,
    ⟨367, 2, 9, 1, 5905360, 457215, 457218, 367000, 38309943⟩,
    ⟨373, 2, 9, 1, 5921577, 489648, 489651, 373000, 36438080⟩,
    ⟨379, 2, 9, 1, 5937535, 521563, 521566, 379000, 34651811⟩,
    ⟨383, 2, 9, 1, 5948033, 542561, 542564, 383000, 33506590⟩,
    ⟨389, 2, 9, 1, 5963578, 573650, 573653, 389000, 31854574⟩,
    ⟨397, 2, 9, 1, 5983935, 614363, 614366, 397000, 29769314⟩,
    ⟨401, 2, 9, 1, 5993960, 634414, 634417, 401000, 28774720⟩,
    ⟨409, 2, 9, 1, 6013714, 673921, 673924, 409000, 26877055⟩,
    ⟨419, 2, 9, 2, 6037869, 722233, 722236, 419000, 24667226⟩,
    ⟨421, 2, 9, 2, 6042631, 731757, 731760, 421000, 24245835⟩,
    ⟨431, 2, 9, 2, 6066107, 778707, 778710, 431000, 22236292⟩,
    ⟨433, 2, 9, 2, 6070736, 787966, 787969, 433000, 21853187⟩,
    ⟨439, 2, 9, 2, 6084498, 815490, 815493, 439000, 20739772⟩,
    ⟨443, 2, 9, 2, 6093568, 833630, 833633, 443000, 20026592⟩,
    ⟨449, 2, 9, 2, 6107021, 860537, 860540, 449000, 18998649⟩]

private def squareRoots600 : Finset ℕ :=
  squareRows600.toFinset.image Row.p

private theorem square_rows_valid : ∀ a ∈ squareRows600, a.Valid 292 := by decide +kernel

private theorem square_row_degrees : ∀ a ∈ squareRows600.toFinset, a.j = 2 := by decide +kernel

private theorem square_roots_range : ∀ k ∈ squareRoots600, 300 < k ∧ k ≤ 449 := by decide +kernel

/-- The same 25 squares clear both section 99 square budgets. Their
weights are bounded at radius 292 and increase on the whole radius interval. -/
private theorem square_gain_600 {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) :
    0.09239 <
      4 *
        ∑ k ∈ squareRoots600,
          (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (k ^ 2)).re := by
  have hmono (k : ℕ) (hk : k ∈ squareRoots600) :
    (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (292 ^ 2) (k ^ 2)).re ≤
      (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (k ^ 2)).re := by
    obtain ⟨h₁, h₂⟩ := square_roots_range k hk
    apply power_term_mono (m := k ^ 2) (U := 300) _ (by norm_num only) hl hu
    exact ⟨Nat.pow_lt_pow_left h₁ (by decide), (Nat.pow_le_pow_left h₂ 2).trans (by decide)⟩
  apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmono) (by norm_num only))
  unfold squareRoots600
  rw [Finset.sum_image
      (show ∀ a ∈ squareRows600.toFinset, ∀ b ∈ squareRows600.toFinset, a.p = b.p → a = b by
        decide +kernel),
    Finset.mul_sum]
  have hs :=
    Finset.sum_le_sum (s := squareRows600.toFinset)
      (fun a ha ↦ by
        have h := row_sound a (by decide : 0 < 292) (square_rows_valid a (List.mem_toFinset.mp ha))
        simpa only [square_row_degrees a ha, Nat.cast_ofNat] using h)
  have ht : 923900000 < ∑ a ∈ squareRows600.toFinset, a.credit := by decide +kernel
  have hh : (923900000 : ℝ) < ∑ a ∈ squareRows600.toFinset, (a.credit : ℝ) := by exact_mod_cast ht
  rw [← Finset.sum_div] at hs
  linarith only [hh, hs]

/-- The square and odd-power certificates leave only the principal
comparison as input for the section 99 arithmetic lower bound. -/
theorem section99_arithmetic_recovered {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r P : ℝ}
    (hl : 292 ≤ r) (hu : r ≤ 300) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    P ≤
        4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) -
          (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re →
      P + 0.09239 + (if r ≤ 299 then 0.01154 else 0.01232) <
        (∑' k : ℕ, quarterKernel570.summand a X k).re +
          (∑' k : ℕ, quarterKernel570.summand b X k).re +
          (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  intro X f hP
  have hroots (k : ℕ) (hk : k ∈ squareRoots600) : (k : ℝ) ≤ r ^ 2 ∧ r ^ 2 < (k : ℝ) ^ 2 := by
    obtain ⟨hk₁, hk₂⟩ := square_roots_range k hk
    have hr : 0 ≤ r := le_trans (by norm_num only) hl
    exact
      ⟨(show (k : ℝ) ≤ 449 by exact_mod_cast hk₂).trans
          ((by norm_num only : (449 : ℝ) ≤ 292 ^ 2).trans
            (pow_le_pow_left₀ (by norm_num only) hl 2)),
        pow_lt_pow_left₀ (hu.trans_lt (by exact_mod_cast hk₁)) hr (by decide)⟩
  exact
    section99_arithmetic_lower a b c hl hu squareRoots600 hroots ht hA hB hC hP
      (square_gain_600 hl hu).le

end PseudoPrime.PrimeTestBounds.MillerRabin
