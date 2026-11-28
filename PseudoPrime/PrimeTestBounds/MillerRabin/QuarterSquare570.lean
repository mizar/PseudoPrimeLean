/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMain570
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSquarePrefix

/-! # Square contributions to the three-character prime sum -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive scale, factor each real character summand through the level-one
principal summand. -/
theorem kernel_summand_factor (K : LLS.PaperStatements.MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (K.summand χ x n).re = (χ n).re * (K.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  by_cases hn : n = 0
  · simp only [hn, LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re, mul_zero]
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hi : (K.transform ((n : ℝ) / x)).im = 0 := K.mellin_real _ (div_pos hn0 hx)
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn,
      MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hi]
    ring

/-- A common sign bound and exact prefix values give a fourfold principal-prefix comparison. -/
theorem kernel_three_principal_prefix (K : LLS.PaperStatements.MellinKernel) {p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) {x : ℝ} (hx : 0 < x) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    4 * (∑ n ∈ s, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) ≤
      (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re + (∑' n : ℕ, K.summand a x n).re +
        (∑' n : ℕ, K.summand b x n).re +
        (∑' n : ℕ, K.summand c x n).re := by
  let f : ℕ → ℝ := fun n ↦ (K.summand (1 : DirichletCharacter ℂ 1) x n).re
  let A : ℕ → ℝ := fun n ↦ (K.summand a x n).re
  let B : ℕ → ℝ := fun n ↦ (K.summand b x n).re
  let C : ℕ → ℝ := fun n ↦ (K.summand c x n).re
  have hf : Summable f :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand K (1 : DirichletCharacter ℂ 1) hx)
  have ha : Summable A :=
    Complex.reCLM.summable (LLS.PaperStatements.MellinKernel.summable_summand K a hx)
  have hb : Summable B :=
    Complex.reCLM.summable (LLS.PaperStatements.MellinKernel.summable_summand K b hx)
  have hc : Summable C :=
    Complex.reCLM.summable (LLS.PaperStatements.MellinKernel.summable_summand K c hx)
  have h :=
    ((hf.add ha).add hb |>.add hc).sum_le_tsum s
      (fun n _ ↦ by
        have hw : 0 ≤ f n := LLS.PaperStatements.MellinKernel.principal_summand_re_nonneg K hx n
        have ht' := mul_le_mul_of_nonneg_right (ht n) hw
        change 0 ≤ f n + A n + B n + C n
        dsimp only [A, B, C]
        rw [kernel_summand_factor K a hx, kernel_summand_factor K b hx,
          kernel_summand_factor K c hx]
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
      rw [kernel_summand_factor K a hx, kernel_summand_factor K b hx, kernel_summand_factor K c hx]
      change f n + (a n).re * f n + (b n).re * f n + (c n).re * f n = 4 * f n
      rw [hfz]
      ring
    · have hs := congrArg (fun t : ℝ ↦ t * f n) (hp n hn hz)
      dsimp only [A, B, C]
      rw [kernel_summand_factor K a hx, kernel_summand_factor K b hx, kernel_summand_factor K c hx]
      change f n + (a n).re * f n + (b n).re * f n + (c n).re * f n = 4 * f n
      nlinarith only [hs]
  change (∑ n ∈ s, (f n + A n + B n + C n)) ≤ ∑' n : ℕ, (f n + A n + B n + C n) at h
  rw [he, Summable.tsum_add ((hf.add ha).add hb) hc, Summable.tsum_add (hf.add ha) hb,
    Summable.tsum_add hf ha] at h
  rw [Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand K (1 : DirichletCharacter ℂ 1) hx),
    Complex.re_tsum (LLS.PaperStatements.MellinKernel.summable_summand K a hx),
    Complex.re_tsum (LLS.PaperStatements.MellinKernel.summable_summand K b hx),
    Complex.re_tsum (LLS.PaperStatements.MellinKernel.summable_summand K c hx)]
  exact h

/-- Any finite set of additional prime powers above the cutoff may be recovered
when their prime bases lie in the passing prefix. The set can mix odd and
even powers, with disjointness from the principal prefix checked by size. -/
theorem kernel_recover_fixed_powers (K : LLS.PaperStatements.MellinKernel) {p q s : ℕ} [NeZero p]
    [NeZero q] [NeZero s] (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ m ∈ T, X < m ∧ ∃ l k : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ m = l ^ k)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    let f := fun k : ℕ ↦ (K.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ T, f k) -
        (∑' k : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, K.summand a X k).re + (∑' k : ℕ, K.summand b X k).re +
        (∑' k : ℕ, K.summand c X k).re := by
  intro f
  let P := Finset.Ioc 0 ⌊X⌋₊
  have hDis : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro k hk hkT
    exact (not_lt_of_ge ((Nat.le_floor_iff hX.le).mp (Finset.mem_Ioc.mp hk).2)) (hT k hkT).1
  have hOne {d : ℕ} (χ : DirichletCharacter ℂ d) (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → χ l = 1)
    {m : ℕ} (hm : m ∈ P ∪ T) (hΛ : ArithmeticFunction.vonMangoldt m ≠ 0) : χ m = 1 := by
    rcases Finset.mem_union.mp hm with hm | hm
    · exact
        AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
          (fun l hl hlX _ ↦ hχ l hl hlX) ((Nat.le_floor_iff hX.le).mp (Finset.mem_Ioc.mp hm).2)
          (Nat.coprime_one_right m) hΛ
    · obtain ⟨l, k, hl, hcut, rfl⟩ := (hT m hm).2
      rw [Nat.cast_pow, map_pow, hχ l hl hcut, one_pow]
  have h :=
    kernel_three_principal_prefix K a b c hX (P ∪ T) ht
      (by
        intro k hk hv
        rw [hOne a hA hk hv, hOne b hB hk hv, hOne c hC hk hv, Complex.one_re]
        norm_num only)
  rw [Finset.sum_union hDis] at h
  change 4 * (∑ k ∈ P, f k) + 4 * (∑ k ∈ T, f k) - _ ≤ _
  linarith only [h]

/-- Extend the principal prefix at X by the squares of roots in S. The roots
lie below X, so their Mangoldt-supported squares have trace three whenever the
three characters are one on primes up to X. The squares exceed X, so their
fourfold principal contribution is disjoint from the prefix. -/
theorem kernel_prefix_add_squares (K : LLS.PaperStatements.MellinKernel) {p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) {X : ℝ} (hX : 0 < X) (S : Finset ℕ)
    (hs : ∀ k ∈ S, (k : ℝ) ≤ X ∧ X < (k : ℝ) ^ 2)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    let f := fun k : ℕ ↦ (K.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ S, f (k ^ 2)) -
        (∑' k : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, K.summand a X k).re + (∑' k : ℕ, K.summand b X k).re +
        (∑' k : ℕ, K.summand c X k).re := by
  intro f
  let P := Finset.Ioc 0 ⌊X⌋₊
  let T := S.image (fun k ↦ k ^ 2)
  have hd : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro m hm ht'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht'
    exact
      (not_lt_of_ge ((Nat.le_floor_iff hX.le).mp (Finset.mem_Ioc.mp hm).2))
        (by exact_mod_cast (hs k hk).2)
  have oneAt {d : ℕ} (χ : DirichletCharacter ℂ d) (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → χ l = 1)
    {m : ℕ} (hm : m ∈ P ∪ T) (hΛ : ArithmeticFunction.vonMangoldt m ≠ 0) : χ m = 1 := by
    have base {k : ℕ} (hk : (k : ℝ) ≤ X) (hv : ArithmeticFunction.vonMangoldt k ≠ 0) :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl hlX _ ↦ hχ l hl hlX) hk (Nat.coprime_one_right k) hv
    rcases Finset.mem_union.mp hm with hm | hm
    · exact base ((Nat.le_floor_iff hX.le).mp (Finset.mem_Ioc.mp hm).2) hΛ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0)] at hΛ
    rw [Nat.cast_pow, map_pow, base (hs k hk).1 hΛ, one_pow]
  have hc :=
    kernel_three_principal_prefix K a b c hX (P ∪ T) ht
      (by
        intro k hk hv
        rw [oneAt a hA hk hv, oneAt b hB hk hv, oneAt c hC hk hv, Complex.one_re]
        norm_num only)
  rw [Finset.sum_union hd,
    Finset.sum_image (fun _ _ _ _ h ↦ Nat.pow_left_injective (by decide : 2 ≠ 0) h)] at hc
  dsimp only [f]
  linarith only [hc]

/-- Under the prime-triviality and trace hypotheses, the three prime sums exceed the
section 31 principal lower bound plus four times the mass of any admissible square set. -/
theorem quarter_square_lower_570 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ}
    (hl : 278 ≤ r) (hu : r ≤ 285) (hRH : RiemannHypothesis) (S : Finset ℕ)
    (hs : ∀ k ∈ S, (k : ℝ) ≤ r ^ 2 ∧ r ^ 2 < (k : ℝ) ^ 2)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    717289 / 1000000 * r - 21 / 100 +
        4 * (∑ k ∈ S, (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X (k ^ 2)).re) <
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  have hx := sq_pos_of_pos (show 0 < r by linarith only [hl])
  have h := kernel_prefix_add_squares quarterKernel570 a b c hx S hs ht hA hB hC
  have hp := quarter_principal_lower_570 hl hu hRH
  dsimp only at h hp ⊢
  rw [← Complex.re_tsum (quarterKernel570.summable_summand (1 : DirichletCharacter ℂ 1) hx)] at hp
  linarith only [h, hp]

end PseudoPrime.PrimeTestBounds.MillerRabin
