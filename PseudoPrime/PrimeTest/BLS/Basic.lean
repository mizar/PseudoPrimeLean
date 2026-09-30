/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Elementary arithmetic for the BLS primality criterion

This file records the divisor bound used by the square-root BLS criterion.
The connection from the executable BLS witnesses to the prime-divisor bound
is developed alongside the certificate verifier.
-/

namespace PseudoPrime.PrimeTest.BLS

/-- The factored part is the product of the prime powers in the list. -/
def factorProduct (factors : List (ℕ × ℕ)) : ℕ :=
  factors.foldl (fun acc qe ↦ acc * qe.1 ^ qe.2) 1

/-- Multiplying a prime power at the front factors out of the accumulator fold. -/
private theorem factorProduct_foldl_mul_left (a : ℕ) (factors : List (ℕ × ℕ)) :
    factors.foldl (fun acc qe ↦ acc * qe.1 ^ qe.2) a =
      a * factors.foldl (fun acc qe ↦ acc * qe.1 ^ qe.2) 1 := by
  induction factors generalizing a with
  | nil => simp only [List.foldl_nil, Nat.mul_one]
  | cons qe factors ih =>
    simp only [List.foldl_cons]
    rw [ih (a * qe.1 ^ qe.2), one_mul, ih (qe.1 ^ qe.2)]
    ac_rfl

/-- The product of a list factors recursively as its head prime power times its tail product. -/
theorem factorProduct_cons (qe : ℕ × ℕ) (factors : List (ℕ × ℕ)) :
    factorProduct (qe :: factors) = qe.1 ^ qe.2 * factorProduct factors := by
  simp only [factorProduct, List.foldl_cons, one_mul]
  exact factorProduct_foldl_mul_left _ _

/-- A prime absent from all factor keys cannot divide their prime-power product. -/
theorem prime_not_dvd_factorProduct_of_ne {q : ℕ} (hq : Nat.Prime q) (factors : List (ℕ × ℕ))
    (hne : ∀ qe, qe ∈ factors → ¬q ∣ qe.1) : ¬q ∣ factorProduct factors := by
  induction factors with
  | nil =>
    simp only [factorProduct, List.foldl_nil]
    exact hq.not_dvd_one
  | cons qe factors ih =>
    rw [factorProduct_cons]
    intro hdiv
    rcases hq.dvd_mul.mp hdiv with hpow | htail
    · exact hne qe List.mem_cons_self (hq.dvd_of_dvd_pow hpow)
    · apply ih
      · intro qf hmem
        exact hne qf (List.mem_cons_of_mem qe hmem)
      · exact htail

/-- Pairwise distinct prime keys let the individual prime-power divisors combine. -/
theorem factorProduct_dvd_of_pairwise_prime_powers {M : ℕ} (factors : List (ℕ × ℕ))
    (hnodup : (factors.map Prod.fst).Nodup) (hprime : ∀ qe, qe ∈ factors → Nat.Prime qe.1)
    (hdiv : ∀ qe, qe ∈ factors → qe.1 ^ qe.2 ∣ M) : factorProduct factors ∣ M := by
  induction factors with
  | nil => exact one_dvd M
  | cons qe factors ih =>
    rcases List.nodup_cons.mp hnodup with ⟨hkey, hnodupTail⟩
    have hq := hprime qe List.mem_cons_self
    have hne : ∀ qf, qf ∈ factors → ¬qe.1 ∣ qf.1 := by
      intro qf hmem hdiv
      have hqf := hprime qf (List.mem_cons_of_mem qe hmem)
      have hkeyne : qe.1 ≠ qf.1 := by
        intro heq
        apply hkey
        exact List.mem_map.mpr ⟨qf, hmem, heq.symm⟩
      have heq := (hqf.dvd_iff_eq (Nat.ne_of_gt hq.one_lt)).mp hdiv
      exact hkeyne heq.symm
    have hcop : Nat.Coprime (qe.1 ^ qe.2) (factorProduct factors) := by
      apply Nat.Coprime.pow_left
      apply hq.coprime_iff_not_dvd.mpr
      exact prime_not_dvd_factorProduct_of_ne hq factors hne
    rw [factorProduct_cons]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
    · exact hdiv qe List.mem_cons_self
    · apply ih hnodupTail
      · intro qf hmem
        exact hprime qf (List.mem_cons_of_mem qe hmem)
      · intro qf hmem
        exact hdiv qf (List.mem_cons_of_mem qe hmem)

/-- Every listed prime power divides the product represented by its factor list. -/
theorem factorPower_dvd_factorProduct (factors : List (ℕ × ℕ)) {qe : ℕ × ℕ} (hmem : qe ∈ factors) :
    qe.1 ^ qe.2 ∣ factorProduct factors := by
  induction factors with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons head factors ih =>
    rw [factorProduct_cons]
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst qe
      exact dvd_mul_of_dvd_left (dvd_refl _) _
    · exact dvd_mul_of_dvd_right (ih htail) _

/-- Raw data describing a completely factored part of `n - 1`. -/
structure PartialFactorizationData where
  factors : List (ℕ × ℕ)
  cofactor : ℕ
  deriving DecidableEq, Repr

/-- The two congruence and gcd conditions required of a BLS witness for `q`. -/
def IsBLSWitness (n q a : ℕ) : Prop :=
  2 ≤ a ∧ a ≤ n - 2 ∧ Nat.ModEq n (a ^ (n - 1)) 1 ∧ Nat.Coprime (a ^ ((n - 1) / q) - 1) n

/-- Executable gcd check using a reduced `ZMod` representative when the modulus is nonzero. -/
def checkBLSGcdCondition (n a k : ℕ) : Bool :=
  if hn : n = 0 then decide (Nat.Coprime (a ^ k - 1) n)
  else
    letI : NeZero n := ⟨hn⟩
    decide (Nat.Coprime (((a : ZMod n) ^ k - 1).val) n)

/-- Reducing a positive-base power in `ZMod` preserves the coprimality of its difference from one.
The modulus is assumed nonzero so the canonical natural representative is available. -/
theorem zmod_pow_sub_one_coprime_iff {n a k : ℕ} (hn : n ≠ 0) (ha : 1 ≤ a) :
    Nat.Coprime (a ^ k - 1) n ↔ Nat.Coprime (((a : ZMod n) ^ k - 1).val) n := by
  let _ : NeZero n := ⟨hn⟩
  rw [← ZMod.isUnit_iff_coprime, ← ZMod.isUnit_iff_coprime]
  change IsUnit ((a ^ k - 1 : ℕ) : ZMod n) ↔ IsUnit (((((a : ZMod n) ^ k - 1).val : ℕ) : ZMod n))
  rw [Nat.cast_sub (Nat.one_le_pow k a ha), Nat.cast_pow, Nat.cast_one]
  rw [ZMod.natCast_zmod_val]

/-- Executable check for the range, Fermat, and gcd conditions of one BLS witness. -/
def checkBLSWitness (n q a : ℕ) : Bool :=
  decide (2 ≤ a) && decide (a ≤ n - 2) && decide ((a : ZMod n) ^ (n - 1) = 1) &&
    checkBLSGcdCondition n a ((n - 1) / q)

/-- The Fermat check in `ZMod` is exactly the natural-number congruence in the BLS specification.
Using the quotient ring keeps the computed power reduced modulo `n` throughout evaluation. -/
theorem zmod_pow_eq_one_iff_modEq (n a k : ℕ) : (a : ZMod n) ^ k = 1 ↔ Nat.ModEq n (a ^ k) 1 := by
  rw [← ZMod.natCast_eq_natCast_iff (a ^ k) 1 n]
  simp only [Nat.cast_pow, Nat.cast_one]

/-- The executable witness check agrees with the mathematical BLS witness predicate. -/
theorem checkBLSWitness_eq_true_iff (n q a : ℕ) :
    checkBLSWitness n q a = true ↔ IsBLSWitness n q a := by
  simp only [checkBLSWitness, IsBLSWitness, Bool.and_eq_true, decide_eq_true_eq,
    zmod_pow_eq_one_iff_modEq]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩
    have hn : n ≠ 0 :=
      Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (le_trans ha (le_trans hb (Nat.sub_le n 2))))
    have hcop : Nat.Coprime (((a : ZMod n) ^ ((n - 1) / q) - 1).val) n := by
      simpa only [checkBLSGcdCondition, dite_eq_right hn, decide_eq_true_eq] using hd
    exact
      ⟨ha, hb, hc, (zmod_pow_sub_one_coprime_iff hn (Nat.le_trans (by decide : 1 ≤ 2) ha)).mpr hcop⟩
  · rintro ⟨ha, hb, hc, hd⟩
    have hn : n ≠ 0 :=
      Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (le_trans ha (le_trans hb (Nat.sub_le n 2))))
    have hcop := (zmod_pow_sub_one_coprime_iff hn (Nat.le_trans (by decide : 1 ≤ 2) ha)).mp hd
    have hgcd : checkBLSGcdCondition n a ((n - 1) / q) = true := by
      simp only [checkBLSGcdCondition, dite_eq_right hn, decide_eq_true_eq]
      exact hcop
    refine ⟨⟨⟨ha, hb⟩, hc⟩, ?_⟩
    exact hgcd

/-- Search a finite candidate list and return a BLS witness when one is found. -/
def findBLSWitness (n q : ℕ) (candidates : List ℕ) : Option ℕ :=
  candidates.find? (checkBLSWitness n q)

/-- A successful finite search returns a value satisfying the BLS specification. -/
theorem findBLSWitness_some_spec (n q : ℕ) (candidates : List ℕ) (a : ℕ)
    (h : findBLSWitness n q candidates = some a) : IsBLSWitness n q a := by
  have haBool : checkBLSWitness n q a = true := List.find?_some h
  exact (checkBLSWitness_eq_true_iff n q a).mp haBool

/-- A finite search succeeds exactly when its candidates contain a BLS witness. -/
theorem findBLSWitness_isSome_iff (n q : ℕ) (candidates : List ℕ) :
    (findBLSWitness n q candidates).isSome = true ↔ ∃ a, a ∈ candidates ∧ IsBLSWitness n q a := by
  rw [findBLSWitness, List.find?_isSome]
  simp only [checkBLSWitness_eq_true_iff]

/-- `none` means precisely that no supplied candidate passes the BLS witness check. -/
theorem findBLSWitness_none_iff (n q : ℕ) (candidates : List ℕ) :
    findBLSWitness n q candidates = none ↔ ∀ a, a ∈ candidates → ¬IsBLSWitness n q a := by
  rw [findBLSWitness, List.find?_eq_none]
  simp only [checkBLSWitness_eq_true_iff]

/-- If a positive natural power is nontrivial modulo a prime, its difference from one is coprime
to that prime. This turns the Lucas nontriviality condition into the BLS gcd condition. -/
theorem coprime_pow_sub_one_of_zmod_pow_ne_one {n a k : ℕ} (hn : Nat.Prime n) (ha : 1 ≤ a)
    (hne : (a : ZMod n) ^ k ≠ 1) : Nat.Coprime (a ^ k - 1) n := by
  apply Nat.coprime_comm.mpr
  apply hn.coprime_iff_not_dvd.mpr
  intro hdiv
  have hzero : ((a ^ k - 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff (a ^ k - 1) n).2 hdiv
  have hpos : 1 ≤ a ^ k := Nat.one_le_pow k a ha
  have hcast := congrArg (fun x : ZMod n => x + 1) hzero
  have hcast' : ((a ^ k : ℕ) : ZMod n) = 1 := by
    calc
      ((a ^ k : ℕ) : ZMod n) = ((a ^ k - 1 : ℕ) : ZMod n) + 1 := by
        rw [Nat.cast_sub hpos]
        ring
      _ = 1 := by
        rw [Nat.cast_sub hpos]
        rw [Nat.cast_sub hpos] at hcast
        simpa only [zero_add] using hcast
  have hpow : ((a ^ k : ℕ) : ZMod n) = (a : ZMod n) ^ k := by rw [Nat.cast_pow]
  exact
    hne
      (by
        rw [← hpow]
        exact hcast')

/-- Lucas power conditions for a bounded natural representative give the executable BLS witness
specification, with the prime-modulus argument supplying its gcd clause. -/
theorem isBLSWitness_of_zmod_lucas_conditions {n q a : ℕ} (hn : Nat.Prime n) (ha : 2 ≤ a)
    (hab : a ≤ n - 2) (hfermat : (a : ZMod n) ^ (n - 1) = 1)
    (hneq : (a : ZMod n) ^ ((n - 1) / q) ≠ 1) : IsBLSWitness n q a := by
  have hmod : Nat.ModEq n (a ^ (n - 1)) 1 :=
    (ZMod.natCast_eq_natCast_iff (a ^ (n - 1)) 1 n).mp
      (by simpa only [Nat.cast_pow, Nat.cast_one] using hfermat)
  exact
    ⟨ha, hab, hmod,
      coprime_pow_sub_one_of_zmod_pow_ne_one hn (Nat.le_trans (by decide : 1 ≤ 2) ha) hneq⟩

/-- Every prime `n ≥ 5` has one bounded base witnessing every prime divisor of `n - 1`.
The base is the natural representative of a Lucas generator in `ZMod n`. -/
theorem exists_common_blsWitness_base_of_prime {n : ℕ} (hn : Nat.Prime n) (hn5 : 5 ≤ n) :
    ∃ a, 2 ≤ a ∧ a ≤ n - 2 ∧ ∀ q, Nat.Prime q → q ∣ n - 1 → IsBLSWitness n q a := by
  have h01 : (0 : ZMod n) ≠ 1 := by
    intro h
    have hmod : Nat.ModEq n 0 1 := by
      apply (ZMod.natCast_eq_natCast_iff 0 1 n).mp
      exact_mod_cast h
    exact hn.not_dvd_one (Nat.ModEq.dvd' hmod)
  have hnNe : NeZero n := ⟨hn.ne_zero⟩
  obtain ⟨z, hzpow, hzq⟩ := reverse_lucas_primality n hn
  have hn1 : 0 < n - 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 5) hn5)
  have hord : orderOf z = n - 1 := orderOf_eq_of_pow_and_pow_div_prime hn1 hzpow hzq
  obtain ⟨q0, hq0, hq0div⟩ :=
    Nat.exists_prime_and_dvd
      (show n - 1 ≠ 1 by
        have htwo : 2 < n := lt_of_lt_of_le (by decide : 2 < 5) hn5
        exact Nat.ne_of_gt (Nat.lt_sub_iff_add_lt.mpr htwo))
  let a := z.val
  have hcast : (a : ZMod n) = z := @ZMod.natCast_zmod_val n hnNe z
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at hzpow
    have hexp : n - 1 ≠ 0 := Nat.ne_of_gt hn1
    rw [zero_pow hexp] at hzpow
    exact h01 hzpow
  have hz1 : z ≠ 1 := by
    intro hz
    exact (hzq q0 hq0 hq0div) (by rw [hz, one_pow])
  have ha : 2 ≤ a := by
    dsimp only [a]
    have hval0 : z.val ≠ 0 := fun h => hz0 ((ZMod.val_eq_zero z).mp h)
    have hval1 : z.val ≠ 1 := by
      intro h
      have hzvalone : (z.val : ZMod n) = 1 := by rw [h, Nat.cast_one]
      exact hz1 (ZMod.natCast_zmod_val z |>.symm.trans hzvalone)
    have hval_ge_two : 2 ≤ z.val := by
      by_contra hnot
      have hle : z.val ≤ 1 := Nat.le_of_lt_succ (Nat.not_le.mp hnot)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hzero | hone
      · exact hval0 hzero
      · exact hval1 hone
    exact hval_ge_two
  have hlt : a < n := by
    dsimp only [a]
    exact @ZMod.val_lt n hnNe z
  have hab : a ≤ n - 2 := by
    by_contra h
    have heq : a = n - 1 := by
      have hgap : n - 2 < a := Nat.lt_of_not_ge h
      have hsum : n < a + 2 :=
        (Nat.sub_lt_iff_lt_add (Nat.le_trans (by decide : 2 ≤ 5) hn5)).mp hgap
      have hnle : n ≤ a + 1 := Nat.le_of_lt_succ hsum
      have hlow : n - 1 ≤ a := Nat.sub_le_iff_le_add.mpr hnle
      exact Nat.le_antisymm (Nat.le_pred_of_lt hlt) hlow
    have hzneg : z = -1 := by
      calc
        z = (a : ZMod n) := hcast.symm
        _ = ((n - 1 : ℕ) : ZMod n) := by rw [heq]
        _ = -1 := by
          rw [Nat.cast_sub (Nat.le_trans (by decide : 1 ≤ 5) hn5), ZMod.natCast_self]
          simp only [zero_sub, Nat.cast_one]
    have hpow2 : z ^ 2 = 1 := by
      rw [hzneg]
      exact neg_one_sq
    have hdiv : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hpow2
    rw [hord] at hdiv
    have hle : n - 1 ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    have hthree : 3 < n := lt_of_lt_of_le (by decide : 3 < 5) hn5
    exact Nat.not_le_of_gt (Nat.lt_sub_iff_add_lt.mpr hthree) hle
  refine ⟨a, ha, hab, ?_⟩
  intro q hq hqdiv
  have hfermat : (a : ZMod n) ^ (n - 1) = 1 := by
    rw [hcast]
    exact hzpow
  have hneq : (a : ZMod n) ^ ((n - 1) / q) ≠ 1 := by
    rw [hcast]
    exact hzq q hq hqdiv
  exact isBLSWitness_of_zmod_lucas_conditions hn ha hab hfermat hneq

/-- A BLS gcd witness stays nontrivial modulo every prime factor of the input. -/
theorem blsWitness_ne_one_mod_prime_factor {n q a p : ℕ} (hp : Nat.Prime p) (hpn : p ∣ n)
    (hw : IsBLSWitness n q a) : ¬Nat.ModEq p (a ^ ((n - 1) / q)) 1 := by
  intro hmod
  rcases hw with ⟨_, _, _, hcop⟩
  have hdiv : p ∣ a ^ ((n - 1) / q) - 1 := Nat.ModEq.dvd' (Nat.ModEq.comm.mp hmod)
  have hpg : p ∣ Nat.gcd (a ^ ((n - 1) / q) - 1) n := Nat.dvd_gcd hdiv hpn
  have hone : p ∣ 1 := by simpa only [hcop.gcd_eq_one] using hpg
  exact hp.not_dvd_one hone

/-- Fermat's BLS condition makes the base nonzero modulo each prime divisor. -/
theorem blsWitness_coprime_base_prime_factor {n q a p : ℕ} (hn : 1 < n) (hp : Nat.Prime p)
    (hpn : p ∣ n) (hw : IsBLSWitness n q a) : Nat.Coprime a p := by
  apply Nat.coprime_comm.mpr
  apply hp.coprime_iff_not_dvd.mpr
  intro hpa
  have hmod : Nat.ModEq p (a ^ (n - 1)) 1 := Nat.ModEq.of_dvd hpn hw.2.2.1
  have hexp : n - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hn)
  have hpow : p ∣ a ^ (n - 1) := dvd_trans hpa (dvd_pow_self a hexp)
  have hone : p ∣ 1 := (Nat.ModEq.dvd_iff hmod dvd_rfl).mp hpow
  exact hp.not_dvd_one hone

/-- The unit represented by a BLS base has order dividing both exponents. -/
theorem blsWitness_order_divisors {n q a p : ℕ} (hn : 1 < n) (hp : Nat.Prime p) (hpn : p ∣ n)
    (hw : IsBLSWitness n q a) :
    ∃ x : (ZMod p)ˣ, orderOf x ∣ n - 1 ∧ orderOf x ∣ p - 1 ∧ ¬orderOf x ∣ (n - 1) / q := by
  let ha := blsWitness_coprime_base_prime_factor hn hp hpn hw
  let x : (ZMod p)ˣ := ZMod.unitOfCoprime a ha
  have hmod : Nat.ModEq p (a ^ (n - 1)) 1 := Nat.ModEq.of_dvd hpn hw.2.2.1
  have hx : x ^ (n - 1) = 1 := by
    apply Units.ext
    change ((a : ZMod p) ^ (n - 1)) = 1
    rw [← Nat.cast_pow]
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff (a ^ (n - 1)) 1 p).2 hmod
  have horderN : orderOf x ∣ n - 1 := orderOf_dvd_of_pow_eq_one hx
  have horderP : orderOf x ∣ p - 1 := by
    have : Fact (Nat.Prime p) := ⟨hp⟩
    rw [← ZMod.card_units p]
    exact orderOf_dvd_card (x := x)
  have horderNot : ¬orderOf x ∣ (n - 1) / q := by
    intro horder
    have hxq : x ^ ((n - 1) / q) = 1 := orderOf_dvd_iff_pow_eq_one.mp horder
    have hxval : (a : ZMod p) ^ ((n - 1) / q) = 1 := by
      have hv := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hxq
      change (a : ZMod p) ^ ((n - 1) / q) = 1 at hv
      exact hv
    have hmodq : Nat.ModEq p (a ^ ((n - 1) / q)) 1 :=
      (ZMod.natCast_eq_natCast_iff (a ^ ((n - 1) / q)) 1 p).mp
        (by simpa only [Nat.cast_pow, Nat.cast_one] using hxval)
    exact blsWitness_ne_one_mod_prime_factor hp hpn hw hmodq
  exact ⟨x, horderN, horderP, horderNot⟩

/-- A prime dividing `N` divides any divisor of `N` that fails to divide `N / q`. -/
theorem prime_dvd_of_dvd_not_dvd_factor {q N d r : ℕ} (hq : Nat.Prime q) (hdecomp : N = q * d)
    (hrN : r ∣ N) (hrnot : ¬r ∣ d) : q ∣ r := by
  by_contra hqr
  have hcopqr : q.Coprime r := hq.coprime_iff_not_dvd.mpr hqr
  have hcop : r.Coprime q := hcopqr.symm
  have hrmul : r ∣ q * d := by
    rw [← hdecomp]
    exact hrN
  exact hrnot ((Nat.Coprime.dvd_mul_left hcop).mp hrmul)

/-- Each BLS prime factor `q` divides the order modulo every prime divisor of `n`. -/
theorem blsWitness_prime_factor_dvd_order_mod_prime {n q a p : ℕ} (hn : 1 < n) (hq : Nat.Prime q)
    (hqN : q ∣ n - 1) (hp : Nat.Prime p) (hpn : p ∣ n) (hw : IsBLSWitness n q a) :
    ∃ x : (ZMod p)ˣ, q ∣ orderOf x ∧ orderOf x ∣ p - 1 := by
  obtain ⟨x, hxN, hxP, hxnot⟩ := blsWitness_order_divisors hn hp hpn hw
  have hdecomp : n - 1 = q * ((n - 1) / q) := (Nat.mul_div_cancel' hqN).symm
  have hqorder := prime_dvd_of_dvd_not_dvd_factor hq hdecomp hxN hxnot
  exact ⟨x, hqorder, hxP⟩

/-- A missing prime-divisor quotient forces the complete supplied prime-power into the divisor. -/
theorem prime_pow_dvd_of_dvd_not_dvd_quotient {q N r e : ℕ} (hq : Nat.Prime q) (hqpow : q ^ e ∣ N)
    (hrN : r ∣ N) (hrnot : ¬r ∣ N / q) : q ^ e ∣ r := by
  induction e generalizing N r with
  | zero => exact one_dvd r
  | succ e ih =>
    have hqN : q ∣ N := dvd_trans (dvd_pow_self q (Nat.succ_ne_zero e)) hqpow
    have hqr : q ∣ r := prime_dvd_of_dvd_not_dvd_factor hq (Nat.mul_div_cancel' hqN).symm hrN hrnot
    by_cases he : e = 0
    · subst e
      rw [Nat.zero_add, pow_one]
      exact hqr
    · let r' := r / q
      let N' := N / q
      have hrEq : q * r' = r := by exact Nat.mul_div_cancel' hqr
      have hNEq : q * N' = N := Nat.mul_div_cancel' hqN
      have hqpow' : q ^ e ∣ N' :=
        (Nat.dvd_div_iff_mul_dvd hqN).2 (by simpa only [pow_succ, Nat.mul_comm] using hqpow)
      have hqN' : q ∣ N' := dvd_trans (dvd_pow_self q he) hqpow'
      have hrN' : r' ∣ N' := by
        apply (Nat.mul_dvd_mul_iff_left hq.pos).mp
        have hmul : q * r' ∣ q * N' := by
          rw [hrEq, hNEq]
          exact hrN
        exact hmul
      have hrnot' : ¬r' ∣ N' / q := by
        intro hdiv
        have hmul : q * r' ∣ N' := (Nat.dvd_div_iff_mul_dvd hqN').mp hdiv
        have hdivN : r ∣ N / q := by
          rw [← hrEq]
          exact hmul
        exact hrnot hdivN
      have hrpow' : q ^ e ∣ r' := ih hqpow' hrN' hrnot'
      have hmul : q * q ^ e ∣ q * r' := Nat.mul_dvd_mul_left q hrpow'
      rw [hrEq] at hmul
      have hpow : q ^ (e + 1) = q * q ^ e := by rw [pow_succ, Nat.mul_comm]
      rw [hpow]
      exact hmul

/-- Every supplied prime power divides `p - 1` when its BLS witness is valid. -/
theorem blsWitness_prime_power_dvd_prime_sub_one {n q a p e : ℕ} (hn : 1 < n) (hq : Nat.Prime q)
    (hqpow : q ^ e ∣ n - 1) (hp : Nat.Prime p) (hpn : p ∣ n) (hw : IsBLSWitness n q a) :
    q ^ e ∣ p - 1 := by
  obtain ⟨x, hxN, hxP, hxnot⟩ := blsWitness_order_divisors hn hp hpn hw
  have hpowOrder := prime_pow_dvd_of_dvd_not_dvd_quotient hq hqpow hxN hxnot
  exact dvd_trans hpowOrder hxP

/-- A square-root BLS certificate consists of factorization and one witness per prime factor. -/
structure SquareCertificate where
  n : ℕ
  factorization : PartialFactorizationData
  witnesses : List (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- Executable checks for the supplied prime powers and cofactor decomposition. -/
def checkPartialFactorization (n : ℕ) (data : PartialFactorizationData) : Bool :=
  decide (1 < factorProduct data.factors) &&
    decide (n - 1 = factorProduct data.factors * data.cofactor) &&
    decide ((data.factors.map Prod.fst).Nodup) &&
    data.factors.all (fun qe ↦ decide (Nat.Prime qe.1) && decide (0 < qe.2))

/-- The factorization checker enforces prime powers and the product decomposition. -/
theorem checkPartialFactorization_eq_true_iff (n : ℕ) (data : PartialFactorizationData) :
    checkPartialFactorization n data = true ↔
      1 < factorProduct data.factors ∧
        n - 1 = factorProduct data.factors * data.cofactor ∧
        (data.factors.map Prod.fst).Nodup ∧
        ∀ qe, qe ∈ data.factors → Nat.Prime qe.1 ∧ 0 < qe.2 := by
  simp only [checkPartialFactorization, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨hprod, hdecomp⟩, hnodup⟩, hprime⟩
    exact ⟨hprod, hdecomp, hnodup, hprime⟩
  · rintro ⟨hprod, hdecomp, hnodup, hprime⟩
    exact ⟨⟨⟨hprod, hdecomp⟩, hnodup⟩, hprime⟩

/-- The factorization data has distinct prime keys and factors a nontrivial part of `n - 1`. -/
def ValidPartialFactorization (n : ℕ) (data : PartialFactorizationData) : Prop :=
  checkPartialFactorization n data = true

/-- A valid BLS partial factorization of a prime `n ≥ 5` has a common witness base in
`List.range n` for all of its prime keys. -/
theorem exists_common_blsWitness_for_valid_partialFactorization {n : ℕ} (hn : Nat.Prime n)
    (hn5 : 5 ≤ n) (data : PartialFactorizationData) (hdata : ValidPartialFactorization n data) :
    ∃ a, a ∈ List.range n ∧ ∀ qe, qe ∈ data.factors → IsBLSWitness n qe.1 a := by
  obtain ⟨a, ha, hab, hcommon⟩ := exists_common_blsWitness_base_of_prime hn hn5
  have hspec := (checkPartialFactorization_eq_true_iff n data).mp hdata
  have hlt : a < n :=
    lt_of_le_of_lt hab (Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 5) hn5) (by decide : 0 < 2))
  refine ⟨a, List.mem_range.mpr hlt, ?_⟩
  intro qe hmem
  obtain ⟨hqprime, hexp⟩ := hspec.2.2.2 qe hmem
  have hpowdvd : qe.1 ^ qe.2 ∣ factorProduct data.factors :=
    factorPower_dvd_factorProduct data.factors hmem
  have hproddiv : factorProduct data.factors ∣ n - 1 := ⟨data.cofactor, hspec.2.1⟩
  have hqdiv : qe.1 ∣ n - 1 :=
    dvd_trans (dvd_trans (dvd_pow_self qe.1 (Nat.ne_of_gt hexp)) hpowdvd) hproddiv
  exact hcommon qe.1 hqprime hqdiv

/-- The witness list has exactly the keys of the factored primes and each key is certified. -/
def checkWitnesses (n : ℕ) (data : PartialFactorizationData) (witnesses : List (ℕ × ℕ)) : Bool :=
  decide (witnesses.map Prod.fst = data.factors.map Prod.fst) &&
    witnesses.all (fun qa ↦ checkBLSWitness n qa.1 qa.2)

/-- The witness checker accepts exactly one valid witness for each listed prime. -/
theorem checkWitnesses_eq_true_iff (n : ℕ) (data : PartialFactorizationData)
    (witnesses : List (ℕ × ℕ)) :
    checkWitnesses n data witnesses = true ↔
      witnesses.map Prod.fst = data.factors.map Prod.fst ∧
        ∀ qa, qa ∈ witnesses → IsBLSWitness n qa.1 qa.2 := by
  simp only [checkWitnesses, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    checkBLSWitness_eq_true_iff]

/-- The witness list has exactly the keys of the factored primes and each key is certified. -/
def ValidWitnesses (n : ℕ) (data : PartialFactorizationData) (witnesses : List (ℕ × ℕ)) : Prop :=
  checkWitnesses n data witnesses = true

/-- Matching witness keys provide a certified base for each listed prime factor. -/
theorem exists_blsWitness_of_factor_key {n : ℕ} (data : PartialFactorizationData)
    (witnesses : List (ℕ × ℕ)) (qe : ℕ × ℕ)
    (hkeys : witnesses.map Prod.fst = data.factors.map Prod.fst)
    (hvalid : ∀ qa, qa ∈ witnesses → IsBLSWitness n qa.1 qa.2) (hmem : qe ∈ data.factors) :
    ∃ a, (qe.1, a) ∈ witnesses ∧ IsBLSWitness n qe.1 a := by
  have hkey : qe.1 ∈ witnesses.map Prod.fst := by
    rw [hkeys]
    exact List.mem_map.mpr ⟨qe, hmem, rfl⟩
  obtain ⟨qa, hqa, hfst⟩ := List.mem_map.mp hkey
  rcases qa with ⟨q', a'⟩
  change q' = qe.1 at hfst
  subst q'
  exact ⟨a', hqa, hvalid _ hqa⟩

/-- The acceptance conditions checked by the BLS verifier. -/
def checkSquareCertificate (c : SquareCertificate) : Bool :=
  decide (5 ≤ c.n) && decide (c.n < factorProduct c.factorization.factors ^ 2) &&
    checkPartialFactorization c.n c.factorization &&
    checkWitnesses c.n c.factorization c.witnesses

/-- The proof-relevant acceptance conditions checked by the BLS verifier. -/
def ValidSquareCertificate (c : SquareCertificate) : Prop :=
  checkSquareCertificate c = true

/-- Executable verifier for the raw square-root BLS certificate data. -/
def verifySquareCertificate (c : SquareCertificate) : Bool :=
  checkSquareCertificate c

/-- The Boolean verifier accepts exactly certificates satisfying the arithmetic specification. -/
theorem verifySquareCertificate_eq_true_iff (c : SquareCertificate) :
    verifySquareCertificate c = true ↔ ValidSquareCertificate c :=
  Iff.rfl

/-- Every prime divisor of `n` is congruent to `1` modulo `F`. -/
def PrimeDivisorsAbove (n F : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → F ∣ p - 1

/-- Valid factor and witness data force every prime divisor above the factored product. -/
theorem primeDivisorsAbove_of_valid_bls_data {n : ℕ} (hn : 1 < n) (data : PartialFactorizationData)
    (witnesses : List (ℕ × ℕ)) (hfactor : ValidPartialFactorization n data)
    (hwitness : ValidWitnesses n data witnesses) :
    PrimeDivisorsAbove n (factorProduct data.factors) := by
  obtain ⟨_, hdecomp, hnodup, hprime⟩ := checkPartialFactorization_eq_true_iff n data |>.mp hfactor
  obtain ⟨hkeys, hvalid⟩ := checkWitnesses_eq_true_iff n data witnesses |>.mp hwitness
  intro p hp hpn
  apply factorProduct_dvd_of_pairwise_prime_powers
  · exact hnodup
  · intro qe hmem
    exact (hprime qe hmem).1
  · intro qe hmem
    obtain ⟨a, _, ha⟩ := exists_blsWitness_of_factor_key data witnesses qe hkeys hvalid hmem
    have hpowF : factorProduct data.factors ∣ n - 1 := by
      rw [hdecomp]
      exact dvd_mul_right _ _
    have hpow : qe.1 ^ qe.2 ∣ n - 1 :=
      dvd_trans (factorPower_dvd_factorProduct data.factors hmem) hpowF
    exact blsWitness_prime_power_dvd_prime_sub_one hn (hprime qe hmem).1 hpow hp hpn ha

/-- If every prime divisor of `n` is larger than its square-root bound `F`, then `n` is prime. -/
theorem prime_of_large_prime_divisors {n F : ℕ} (hn : 2 ≤ n) (hbound : n < F ^ 2)
    (hlarge : PrimeDivisorsAbove n F) : Nat.Prime n := by
  apply Nat.prime_def_le_sqrt.mpr
  constructor
  · exact hn
  · intro m hm2 hmsqrt hmn
    have hmne : m ≠ 1 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hm2)
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hmne
    have hpn : p ∣ n := dvd_trans hpm hmn
    have hpF : F ∣ p - 1 := hlarge p hp hpn
    have hpLower : F < p := by
      have hpPrev : F ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hpF
      exact lt_of_le_of_lt hpPrev (Nat.sub_lt hp.pos (by decide))
    have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm2
    have hpmle : p ≤ m := Nat.le_of_dvd hmpos hpm
    have hFsqrt : F ≤ n.sqrt := le_trans (le_trans (Nat.le_of_lt hpLower) hpmle) hmsqrt
    have hFsq : F * F ≤ n := Nat.le_sqrt.mp hFsqrt
    exact (Nat.not_le_of_gt (by simpa only [pow_two] using hbound)) hFsq

/-- Every accepted square-root BLS certificate proves the input prime. -/
theorem prime_of_valid_square_certificate (c : SquareCertificate)
    (hcheck : verifySquareCertificate c = true) : Nat.Prime c.n := by
  simp only [verifySquareCertificate, checkSquareCertificate, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hn5, hbound⟩, hfactor⟩, hwitness⟩
  have hn2 : 2 ≤ c.n := le_trans (by decide : 2 ≤ 5) hn5
  have hn1 : 1 < c.n := lt_of_lt_of_le (by decide : 1 < 5) hn5
  apply prime_of_large_prime_divisors hn2 hbound
  exact primeDivisorsAbove_of_valid_bls_data hn1 c.factorization c.witnesses hfactor hwitness

end PseudoPrime.PrimeTest.BLS
