/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
public import PseudoPrime.Analysis.LogTaylorBounds
import all PseudoPrime.Data.Popcount
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.EnvelopeTransfer

/-! # Kernel-checked prime counts by sieving a closed integer interval -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Set bits at successive multiples of p by doubling the length of a progression. -/
private def positions (p n : ℕ) : ℕ :=
  Nat.rec 1 (fun i v => v.lor (v.shiftLeft (p.shiftLeft i))) n

private theorem positions_bit (p n k : ℕ) (hk : k < 2 ^ n) :
    (positions p n).testBit (p * k) = true := by
  induction n generalizing k with
  | zero =>
    have h : k = 0 := Nat.le_zero.mp (Nat.lt_succ_iff.mp hk)
    subst k
    simp only [Nat.mul_zero, positions]
    change (1 : ℕ).testBit 0 = true
    decide +kernel
  | succ n
    ih =>
    change ((positions p n) ||| ((positions p n) <<< (p <<< n))).testBit (p * k) = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    by_cases h : k < 2 ^ n
    · exact Or.inl (ih k h)
    · right
      have hle := Nat.le_of_not_lt h
      have hsmall : k - 2 ^ n < 2 ^ n := by
        rw [pow_succ, Nat.mul_two] at hk
        exact (Nat.sub_lt_iff_lt_add hle).2 hk
      have hpos := Nat.mul_le_mul_left p hle
      rw [Nat.testBit_shiftLeft, Nat.shiftLeft_eq]
      simpa only [decide_eq_true hpos, Bool.true_and, ← Nat.mul_sub] using ih (k - 2 ^ n) hsmall

/-- Mark the positions i for which v + i is a multiple of p, starting at its first residue. -/
private def residueMask (width p v : ℕ) : ℕ :=
  let j := (p.sub v).mod p
  (Nat.ble j (width.sub 1)).rec 0
    ((positions p (((width.sub 1).sub j).div p).log2.succ).shiftLeft j)

/-- The first marked index is congruent to every index divisible after translation by v. -/
private theorem first_congr {p v i : ℕ} (hv : v < p) (hz : p ∣ v + i) :
    Nat.ModEq p ((p - v) % p) i := by
  let j := (p - v) % p
  have hj : p ∣ v + j := by
    apply Nat.dvd_of_mod_eq_zero
    change (v + ((p - v) % p)) % p = 0
    rw [Nat.add_mod_mod, Nat.add_sub_of_le hv.le, Nat.mod_self]
  exact
    Nat.ModEq.add_left_cancel' v
      ((Nat.modEq_zero_iff_dvd.mpr hj).trans (Nat.modEq_zero_iff_dvd.mpr hz).symm)

private theorem marked_residue {width p i v : ℕ} (hp : 0 < p) (hv : v < p) (hi : i < width)
    (hz : p ∣ v + i) : (residueMask width p v).testBit i = true := by
  let j := (p - v) % p
  have eqv := first_congr hv hz
  have hij : j ≤ i :=
    ((Nat.mod_eq_of_lt (Nat.mod_lt (p - v) hp)).symm.trans eqv).le.trans (Nat.mod_le i p)
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hij).mp eqv
  have hi' : i ≤ width - 1 := Nat.le_pred_of_lt hi
  have hle : k ≤ (width - 1 - j) / p := by
    apply (Nat.le_div_iff_mul_le hp).2
    rw [Nat.mul_comm, ← hk]
    exact Nat.sub_le_sub_right hi' j
  have hjw := Nat.ble_eq_true_of_le (hij.trans hi')
  change
    (Bool.rec (motive := fun _ => ℕ) 0 ((positions p (((width - 1 - j) / p).log2 + 1)).shiftLeft j)
            (Nat.ble j (width - 1))).testBit
        i =
      true
  rw [hjw]
  change ((positions p _) <<< j).testBit i = true
  rw [Nat.testBit_shiftLeft]
  simp only [decide_eq_true hij, Bool.true_and, hk]
  exact positions_bit p _ k (hle.trans_lt Nat.lt_log2_self)

/-- Mark multiples of p among the entries a + 1 + 2i of the sampled interval. -/
private def multipleMask (a width p : ℕ) : ℕ :=
  (Nat.beq p 2).rec (residueMask width p ((a.succ.mul (p.succ.div 2)).mod p))
    ((Nat.beq (a % 2) 0).rec (positions 1 (width.log2 + 1)) 0)

private theorem marks_divisor {a width p i : ℕ} (hp : p.Prime) (hi : i < width)
    (hd : p ∣ a + 1 + 2 * i) : (multipleMask a width p).testBit i = true := by
  rcases hp.eq_two_or_odd with htwo | hodd
  · subst p
    by_cases ha : a % 2 = 0
    · have hz := Nat.mod_eq_zero_of_dvd hd
      rw [Nat.add_mul_mod_self_left, Nat.add_mod, ha] at hz
      exact False.elim (Nat.one_ne_zero hz)
    · have he := Bool.eq_false_iff.mpr (ha ∘ Nat.eq_of_beq_eq_true)
      rw [multipleMask, Nat.beq_refl, he]
      simpa only [one_mul] using positions_bit 1 _ i (hi.trans (Nat.lt_log2_self))
  have hne : p ≠ 2 := by
    intro he
    subst p
    exact Nat.zero_ne_one hodd
  let k := (p + 1) / 2
  have hk : k * 2 = p + 1 := by
    apply Nat.div_mul_cancel
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, hodd]
  have hb := dvd_mul_of_dvd_left hd k
  have he : (a + 1 + 2 * i) * k = (a + 1) * k + i + p * i := by
    calc
      _ = (a + 1) * k + (k * 2) * i := by ring
      _ = _ := by
        rw [hk]; ring
  rw [he] at hb
  have hr := (Nat.dvd_add_iff_left (Nat.dvd_mul_right p i)).2 hb
  rw [multipleMask, Bool.eq_false_iff.mpr (hne ∘ Nat.eq_of_beq_eq_true)]
  apply marked_residue hp.pos (Nat.mod_lt _ hp.pos) hi
  exact
    Nat.dvd_of_mod_eq_zero
      (by
        rw [Nat.mod_add_mod]
        exact Nat.mod_eq_zero_of_dvd hr)

private inductive Factors where
  | part (ps : List ℕ)
  | oddBlock (last : ℕ) (ps : List ℕ)
  | upperBlock (first last : ℕ) (offsets : List ℕ)
  | join (l r : Factors)

private def smallBase : ℕ :=
  let n : ℕ := 0x67bfd0
  let n := (n <<< 240) + 0x2bef01d7a4a7d3018fde15ef65434c5d2ecdecd32bdab805c5270799e540
  let n := (n <<< 240) + 0xc47d1b625175a57f3c30c90e4ef05875cab5f03c844a8a59e7e290a90a92
  let n := (n <<< 240) + 0xb39d2dfacd20556db05bb29ca1b5225b9bff9ef2ec239d08e783d4661600
  n

private theorem small_cover (m : ℕ) (hm : 2 ≤ m) (hu : m ≤ 512) : m ∣ smallBase := by
  have h : divisorBase 9 1 = smallBase := by decide +kernel
  rw [← h]
  exact dvd_divisorBase 9 1 m ((by decide : 1 ≤ 2).trans hm) (Nat.lt_succ_of_le hu)

private abbrev supported (q : ℕ) : Prop :=
  2 ≤ q ∧ (if q ≤ 512 then q.minFac = q else q < 513 * 513 ∧ q.gcd smallBase = 1)

private theorem supported_prime {q : ℕ} (h : supported q) : q.Prime := by
  obtain ⟨h2, ht⟩ := h
  by_cases hs : q ≤ 512
  · exact Nat.prime_def_minFac.mpr ⟨h2, (by simpa only [ite_eq_left hs] using ht)⟩
  rw [ite_eq_right hs] at ht
  refine Nat.prime_def_le_sqrt.mpr ⟨h2, ?_⟩
  intro m hm hroot hd
  have hu : q.sqrt ≤ 512 := Nat.le_of_lt_succ (Nat.sqrt_lt.mpr ht.1)
  have hg := Nat.dvd_gcd hd (small_cover m hm (hroot.trans hu))
  rw [ht.2] at hg
  exact (Nat.ne_of_gt hm) (Nat.eq_one_of_dvd_one hg)

private def primeWeight : List ℕ → ℕ
  | [] => 1
  | q :: qs => (if supported q then q else 1) * primeWeight qs

private def Factors.weight : Factors → ℕ
  | .part ps | .oddBlock _ ps => primeWeight ps
  | .upperBlock first _ offsets => primeWeight (offsets.map (first + ·))
  | .join l r => l.weight * r.weight

/-- Sieve only by trial divisors whose square does not exceed the right endpoint. -/
private def boundMask (a w p : ℕ) : ℕ :=
  (Nat.ble (p * p) (a + 2 * w)).rec 0 (multipleMask a w p)

private def unionMarks (a w : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => boundMask a w p ||| unionMarks a w ps

/-- For an even start, the inverse of two modulo an odd prime is its upper half. -/
private def oddMark (half w p : ℕ) : ℕ :=
  let r := (half.add (p.succ.div 2)).mod p
  let j := (Nat.beq r 0).rec (p.sub r) 0
  let u := w.pred
  (Nat.ble j u).rec 0 ((positions p ((u.sub j).div p).log2.succ).shiftLeft j)

/-- The branch at residue zero replaces a second remainder by a subtraction. -/
private theorem oddMark_eq (half w p : ℕ) (hp : 0 < p) :
    oddMark half w p = residueMask w p ((half + (p + 1) / 2) % p) := by
  let r := (half + (p + 1) / 2) % p
  have first : (Nat.beq r 0).rec (p.sub r) 0 = (p - r) % p := by
    by_cases hr : r = 0
    · rw [hr, Nat.beq_refl, Nat.sub_zero, Nat.mod_self]
    · rw [Bool.eq_false_iff.mpr (hr ∘ Nat.eq_of_beq_eq_true)]
      exact (Nat.mod_eq_of_lt (Nat.sub_lt hp (Nat.pos_of_ne_zero hr))).symm
  exact
    congrArg
      (fun j : ℕ =>
        (Nat.ble j (w - 1)).rec (motive := fun _ => ℕ) 0
          ((positions p (((w - 1 - j) / p).log2 + 1)).shiftLeft j))
      first

/-- Fold the masks of eligible odd divisors into one exclusion mask. -/
private def oddMarks (half w : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => oddMark half w p ||| oddMarks half w ps

/-- Check parity and the largest divisor once for an entire generated block. -/
private def blockMarks (a w last : ℕ) (ps : List ℕ) : ℕ :=
  if a % 2 = 0 ∧ last * last ≤ a + 2 * w then oddMarks (a / 2) w ps else unionMarks a w ps

/-- First odd-position index hit by this divisor in an even-start window. -/
private def firstIndex (half p : ℕ) : ℕ :=
  let r := (half.add (p.succ.div 2)).mod p
  (Nat.beq r 0).rec (p.sub r) 0

/-- Place a single bit when its index is inside the window. -/
private def bitAt (w j : ℕ) : ℕ :=
  (Nat.blt j w).rec 0 (Nat.shiftLeft 1 j)

/-- A window no wider than the prime contains at most one mark in its residue class. -/
private def singleMark (half w p : ℕ) : ℕ :=
  bitAt w (firstIndex half p)

/-- Set both possible in-range hits for each divisor in an active two-hit block. -/
private def pairMarks (half w first : ℕ) : List ℕ → ℕ
  | [] => 0
  | delta :: rest =>
    let p := first + delta
    let j := firstIndex half p
    bitAt w j ||| bitAt w (j + p) ||| pairMarks half w first rest

/-- Set the single possible bit for each eligible prime in a narrow window. -/
private def singleMarks (half w first : ℕ) : List ℕ → ℕ
  | [] => 0
  | delta :: rest => singleMark half w (first + delta) ||| singleMarks half w first rest

/-- Offset encoding certifies the minimum trial divisor and lets a whole block skip the sieve. -/
private def upperMarks (a w first last : ℕ) (offsets : List ℕ) : ℕ :=
  if a + 2 * w < first * first then 0
  else
    if a % 2 = 0 ∧ w ≤ first ∧ last * last ≤ a + 2 * w then singleMarks (a / 2) w first offsets
    else
      if w = 65536 ∧ a % 2 = 0 ∧ w ≤ first + first ∧ last * last ≤ a + 2 * w then
        pairMarks (a / 2) w first offsets
      else blockMarks a w last (offsets.map (first + ·))

private def Factors.excluded (a w : ℕ) : Factors → ℕ
  | .part ps => unionMarks a w ps
  | .oddBlock last ps => blockMarks a w last ps
  | .upperBlock first last offsets => upperMarks a w first last offsets
  | .join l r => l.excluded a w ||| r.excluded a w

private theorem marked_in_list {a w i p : ℕ} (hsq : p * p ≤ a + 2 * w) (hi : i < w) (hp : p.Prime)
    (hd : p ∣ a + 1 + 2 * i) (ps : List ℕ) (hm : p ∈ ps) :
    (unionMarks a w ps).testBit i = true := by
  induction ps with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons q qs ih =>
    rw [unionMarks, Nat.testBit_lor, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with h | h
    · subst q
      exact
        Or.inl (by simpa only [boundMask, Nat.ble_eq_true_of_le hsq] using marks_divisor hp hi hd)
    · exact Or.inr (ih h)

/-- For an even entrance, translate a divisor of the sampled integer to its index residue. -/
private theorem index_dvd {a p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hd : p ∣ a + 1 + 2 * i) :
    p ∣ a / 2 + (p + 1) / 2 + i := by
  have half : 2 * (a / 2) = a := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ha)
  rcases hp.eq_two_or_odd with h | h
  · subst p
    have bad := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.add_mul_mod_self_left, Nat.add_mod, ha] at bad
    exact False.elim (Nat.one_ne_zero bad)
  have twice : (p + 1) / 2 * 2 = p + 1 := by
    apply Nat.div_mul_cancel
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, h]
  have eqn : 2 * (a / 2 + (p + 1) / 2 + i) = (a + 1 + 2 * i) + p := by
    rw [Nat.mul_add, Nat.mul_add, half, Nat.mul_comm 2 ((p + 1) / 2), twice]
    ac_rfl
  have hd' : p ∣ 2 * (a / 2 + (p + 1) / 2 + i) := eqn ▸ Nat.dvd_add hd (Nat.dvd_refl p)
  have hn : ¬p ∣ 2 := by
    intro hh
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hh
    subst p
    exact Nat.zero_ne_one h
  exact (hp.dvd_mul.mp hd').resolve_left hn

/-- Divisibility of the sampled integer implies a mark at its index for an even start. -/
private theorem odd_marked {a w p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hi : i < w)
    (hd : p ∣ a + 1 + 2 * i) : (oddMark (a / 2) w p).testBit i = true := by
  rw [oddMark_eq _ _ _ hp.pos]
  apply marked_residue hp.pos (Nat.mod_lt _ hp.pos) hi
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.mod_add_mod]
  exact Nat.mod_eq_zero_of_dvd (index_dvd ha hp hd)

/-- A divisor in an eligible block excludes its composite multiple. -/
private theorem odd_list_marked {a w p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hi : i < w)
    (hd : p ∣ a + 1 + 2 * i) (ps : List ℕ) (hm : p ∈ ps) :
    (oddMarks (a / 2) w ps).testBit i = true := by
  induction ps with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons q qs ih =>
    rw [oddMarks, Nat.testBit_lor, Bool.or_eq_true]
    exact
      (List.mem_cons.mp hm).elim (fun h => Or.inl (h ▸ odd_marked ha hp hi hd))
        (fun h => Or.inr (ih h))

/-- For a divisible entry, its position reduced modulo the divisor is the first hit. -/
private theorem firstIndex_eq {a p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hd : p ∣ a + 1 + 2 * i) :
    firstIndex (a / 2) p = i % p := by
  let r := (a / 2 + (p + 1) / 2) % p
  have hz : p ∣ r + i :=
    Nat.dvd_of_mod_eq_zero
      (by
        dsimp only [r]
        rw [Nat.mod_add_mod]
        exact Nat.mod_eq_zero_of_dvd (index_dvd ha hp hd))
  have he := first_congr (Nat.mod_lt _ hp.pos) hz
  have heq := (Nat.mod_eq_of_lt (Nat.mod_lt (p - r) hp.pos)).symm.trans he
  rw [← heq]
  change (Nat.beq r 0).rec (p.sub r) 0 = (p - r) % p
  by_cases hr : r = 0
  · rw [hr, Nat.beq_refl, Nat.sub_zero, Nat.mod_self]
  · rw [Bool.eq_false_iff.mpr (hr ∘ Nat.eq_of_beq_eq_true)]
    exact (Nat.mod_eq_of_lt (Nat.sub_lt hp.pos (Nat.pos_of_ne_zero hr))).symm

/-- The guarded bit is set at every in-range requested index. -/
private theorem bitAt_self {w i : ℕ} (hi : i < w) : (bitAt w i).testBit i = true := by
  rw [bitAt, Nat.blt_eq.mpr hi]
  change ((1 : ℕ) <<< i).testBit i = true
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_self]

/-- In a narrow window the certified index is exactly the first mark. -/
private theorem single_marked {a w p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hw : w ≤ p)
    (hi : i < w) (hd : p ∣ a + 1 + 2 * i) : (singleMark (a / 2) w p).testBit i = true := by
  rw [singleMark, firstIndex_eq ha hp hd, Nat.mod_eq_of_lt (hi.trans_le hw)]
  exact bitAt_self hi

/-- Below twice the period, a divisible position is the first or the second hit. -/
private theorem pair_hit {a w p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hw : w ≤ p + p) (hi : i < w)
    (hd : p ∣ a + 1 + 2 * i) :
    ((bitAt w (firstIndex (a / 2) p)) ||| bitAt w (firstIndex (a / 2) p + p)).testBit i = true := by
  rw [Nat.testBit_lor, Bool.or_eq_true, firstIndex_eq ha hp hd]
  by_cases h : i < p
  · rw [Nat.mod_eq_of_lt h]
    exact Or.inl (bitAt_self hi)
  · have hle := Nat.le_of_not_gt h
    have hlt := (Nat.sub_lt_iff_lt_add hle).2 (hi.trans_le hw)
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt, Nat.sub_add_cancel hle]
    exact Or.inr (bitAt_self hi)

/-- Every represented divisor marks its in-range multiples in a two-hit block. -/
private theorem pair_list_marked {a w first p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime)
    (hw : w ≤ first + first) (hi : i < w) (hd : p ∣ a + 1 + 2 * i) (ds : List ℕ)
    (hm : p ∈ ds.map (first + ·)) : (pairMarks (a / 2) w first ds).testBit i = true := by
  induction ds with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons delta rest ih =>
    rw [pairMarks, Nat.testBit_lor, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with he | ht
    · subst p
      have hmin := Nat.le_add_right first delta
      exact Or.inl (pair_hit ha hp (hw.trans (Nat.add_le_add hmin hmin)) hi hd)
    · exact Or.inr (ih ht)

/-- Every represented divisor in a singleton block marks its multiple. -/
private theorem single_list_marked {a w first p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime)
    (hw : w ≤ first) (hi : i < w) (hd : p ∣ a + 1 + 2 * i) (ds : List ℕ)
    (hm : p ∈ ds.map (first + ·)) : (singleMarks (a / 2) w first ds).testBit i = true := by
  induction ds with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons delta rest ih =>
    rw [singleMarks, Nat.testBit_lor, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with he | ht
    · subst p
      exact Or.inl (single_marked ha hp (hw.trans (Nat.le_add_right first delta)) hi hd)
    · exact Or.inr (ih ht)

private theorem prime_in_weight {p : ℕ} (hp : p.Prime) (qs : List ℕ) (h : p ∣ primeWeight qs) :
    p ∈ qs := by
  induction qs with
  | nil => exact False.elim (hp.not_dvd_one h)
  | cons q qs ih =>
    rcases hp.dvd_mul.mp h with hq | ht
    · by_cases hprime : supported q
      · rw [ite_eq_left hprime] at hq
        exact
          List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (supported_prime hprime)).1 hq))
      · rw [ite_eq_right hprime] at hq
        exact False.elim (hp.not_dvd_one hq)
    · exact List.mem_cons.mpr (Or.inr (ih ht))

private theorem marked_by_factor {a w i p : ℕ} (hsq : p * p ≤ a + 2 * w) (hi : i < w) (hp : p.Prime)
    (hd : p ∣ a + 1 + 2 * i) (f : Factors) (hf : p ∣ f.weight) :
    (f.excluded a w).testBit i = true := by
  induction f with
  | part ps => exact marked_in_list hsq hi hp hd ps (prime_in_weight hp ps hf)
  | oddBlock last ps =>
    have hm := prime_in_weight hp ps hf
    by_cases h : a % 2 = 0 ∧ last * last ≤ a + 2 * w
    · simpa only [Factors.excluded, blockMarks, ite_eq_left h] using
        odd_list_marked h.1 hp hi hd ps hm
    · simpa only [Factors.excluded, blockMarks, ite_eq_right h] using
        marked_in_list hsq hi hp hd ps hm
  | upperBlock first last
    ds =>
    have hm := prime_in_weight hp (ds.map (first + ·)) hf
    obtain ⟨delta, _, he⟩ := List.mem_map.mp hm
    have hmin : first ≤ p := he ▸ Nat.le_add_right first delta
    have active := (Nat.mul_le_mul hmin hmin).trans hsq
    rw [Factors.excluded, upperMarks, ite_eq_right (Nat.not_lt_of_ge active)]
    by_cases h : a % 2 = 0 ∧ w ≤ first ∧ last * last ≤ a + 2 * w
    · rw [ite_eq_left h]
      exact single_list_marked h.1 hp h.2.1 hi hd ds hm
    · rw [ite_eq_right h]
      by_cases pair : w = 65536 ∧ a % 2 = 0 ∧ w ≤ first + first ∧ last * last ≤ a + 2 * w
      · rw [ite_eq_left pair]
        exact pair_list_marked pair.2.1 hp pair.2.2.1 hi hd ds hm
      rw [ite_eq_right pair]
      by_cases hall : a % 2 = 0 ∧ last * last ≤ a + 2 * w
      · simpa only [blockMarks, ite_eq_left hall] using odd_list_marked hall.1 hp hi hd _ hm
      · simpa only [blockMarks, ite_eq_right hall] using marked_in_list hsq hi hp hd _ hm
  | join l r ihl ihr =>
    rw [Factors.excluded, Nat.testBit_lor, Bool.or_eq_true]
    exact (hp.dvd_mul.mp hf).imp ihl ihr

private def liveBits (f : Factors) (a w : ℕ) : ℕ :=
  let top := (1 <<< w) - 1
  top ^^^ (top &&& f.excluded a w)

private theorem live_is_prime {a w B i : ℕ} (f : Factors)
    (hbase : ∀ p, p.Prime → p ≤ B → p ∣ f.weight) (ha : 1 ≤ a) (hb : a + 2 * w < (B + 1) * (B + 1))
    (hi : i < w) (hlive : (liveBits f a w).testBit i = true) : (a + 1 + 2 * i).Prime := by
  let n := a + 1 + 2 * i
  have h2 : 2 ≤ n := (Nat.add_le_add_right ha 1).trans (Nat.le_add_right _ _)
  refine Nat.prime_def_le_sqrt.mpr ⟨h2, ?_⟩
  intro m hm hs hd
  have hp := Nat.minFac_prime (Nat.ne_of_gt hm)
  have hnb : n ≤ a + 2 * w := by
    have hstep := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at hstep
    change a + 1 + 2 * i ≤ a + 2 * w
    rw [Nat.add_right_comm a 1 (2 * i), Nat.add_assoc]
    exact Nat.add_le_add_left ((Nat.le_succ (2 * i + 1)).trans hstep) a
  have hu : n.sqrt ≤ B := Nat.le_of_lt_succ (Nat.sqrt_lt.mpr (hnb.trans_lt hb))
  have hms : m.minFac ≤ n.sqrt := (Nat.minFac_le (Nat.zero_lt_of_lt hm)).trans hs
  have hsq := (Nat.mul_le_mul hms hms).trans ((Nat.sqrt_le n).trans hnb)
  have hm :=
    marked_by_factor hsq hi hp ((Nat.minFac_dvd m).trans hd) f
      (hbase _ hp ((Nat.minFac_le (Nat.zero_lt_of_lt hm)).trans (hs.trans hu)))
  simp only [liveBits, Nat.testBit_xor, Nat.testBit_and, hm, Bool.and_true,
    bne_self_eq_false] at hlive
  exact Bool.noConfusion hlive

private def nibbleCount (z : ℕ) : ℕ :=
  (Nat.shiftRight 0x4332322132212110 (4 * (z % 16))) % 16

private theorem nibble_checked (z : Fin 16) : nibbleCount z.val = Data.bitCountPrefix 4 z.val := by
  exact
    (show ∀ n : Fin 16, nibbleCount n.val = Data.bitCountPrefix 4 n.val from by decide +kernel) z

/-- Four bits per table entry store the population count of each byte. -/
private def byteCount (z : ℕ) : ℕ :=
  let t := 0x8776766576656554766565546554544376656554655454436554544354434332
  let t := (t <<< 256) + 0x7665655465545443655454435443433265545443544343325443433243323221
  let t := (t <<< 256) + 0x7665655465545443655454435443433265545443544343325443433243323221
  let t := (t <<< 256) + 0x6554544354434332544343324332322154434332433232214332322132212110
  Nat.land (Nat.shiftRight t (Nat.shiftLeft (Nat.land z 255) 2)) 15

private theorem byte_checked (z : Fin 256) : byteCount z.val = Data.bitCountPrefix 8 z.val := by
  exact (show ∀ n : Fin 256, byteCount n.val = Data.bitCountPrefix 8 n.val from by decide +kernel) z

/-- Split a packed mask into equal halves until each leaf has the given bit width. -/
private def countTree (width : ℕ) (leaf : ℕ → ℕ) (d : ℕ) : ℕ → ℕ :=
  Nat.rec leaf
    (fun i rec z =>
      let n := Nat.shiftLeft width i
      Nat.add (rec (Nat.land z ((1 <<< n) - 1))) (rec (Nat.shiftRight z n)))
    d

/-- Count one 64-bit leaf with the certified parallel population count. -/
private def wordCount (z : ℕ) : ℕ :=
  Data.popcount64 (BitVec.ofNat 64 z)

/-- Count full words in wide windows and retain byte and nibble leaves for short windows. -/
private def countMask : ℕ → ℕ → ℕ
  | 0 => nibbleCount
  | 1 => byteCount
  | 2 => countTree 8 byteCount 1
  | 3 => countTree 8 byteCount 2
  | d + 4 => countTree 64 wordCount d

private theorem prime_step {a lo : ℕ} (hp : (a + 1).Prime) (hlo : 0 < lo) (ha : lo ≤ a + 1) :
    Real.log lo ≤ Chebyshev.theta (a + 1 : ℕ) - Chebyshev.theta a := by
  have he := PseudoPrime.AnalyticNumberTheory.Arithmetic.theta_prefix_add_interval (Nat.le_succ a)
  simp only [Nat.Ioc_succ_singleton, Finset.filter_singleton, hp, ite_true,
    Finset.sum_singleton] at he
  rw [← he, add_sub_cancel_left]
  exact Real.log_le_log (Nat.cast_pos.mpr hlo) (Nat.cast_le.mpr ha)

private theorem scan_gain (a lo z n : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ i < n, z.testBit i = true → (a + 1 + 2 * i).Prime) :
    (Data.bitCountPrefix n z : ℝ) * Real.log lo ≤
      Chebyshev.theta (a + 2 * n : ℕ) - Chebyshev.theta a := by
  induction n with
  | zero =>
    simp only [Data.bitCountPrefix, Nat.cast_zero, zero_mul, Nat.mul_zero, Nat.add_zero, sub_self,
      le_refl]
  | succ n ih =>
    have h := ih (fun i hi => ok i (hi.trans (Nat.lt_succ_self n)))
    rw [Nat.mul_succ, ← Nat.add_assoc]
    have he : a + 1 + 2 * n = a + 2 * n + 1 := by rw [Nat.add_right_comm]
    have he2 := Chebyshev.theta_mono (Nat.cast_le.mpr (Nat.le_succ (a + 2 * n + 1)))
    by_cases hb : z.testBit n = true
    · have hp := he ▸ ok n (Nat.lt_succ_self n) hb
      have hg := prime_step hp hlo (ha.trans (Nat.le_add_right a (2 * n)) |>.trans (Nat.le_succ _))
      rw [Data.bitCountPrefix, ite_eq_left hb, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      linarith only [hg, h, he2]
    · have hh := Chebyshev.theta_mono (Nat.cast_le.mpr (Nat.le_add_right (a + 2 * n) 2))
      rw [Data.bitCountPrefix, ite_eq_right hb, Nat.add_zero]
      linarith only [h, hh]

/-- Each set bit in a checked byte contributes a certified prime to the theta increment. -/
private theorem byte_leaf_gain (a lo z : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ i < 8, z.testBit i = true → (a + 1 + 2 * i).Prime) :
    (byteCount z : ℝ) * Real.log lo ≤ Chebyshev.theta (a + 2 * 8 : ℕ) - Chebyshev.theta a := by
  let v : Fin 256 := ⟨z % 256, Nat.mod_lt _ (by decide)⟩
  have he : byteCount z = Data.bitCountPrefix 8 v.val := by
    rw [← byte_checked]
    have hmask (n : ℕ) : Nat.land n 255 = n % 256 := Nat.and_two_pow_sub_one_eq_mod n 8
    simp only [byteCount, v, hmask, Nat.mod_mod]
  rw [he]
  apply scan_gain a lo v.val 8 hlo ha
  intro i hi hb
  change (z % 2 ^ 8).testBit i = true at hb
  simp only [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and] at hb
  exact ok i hi hb

/-- The 64-bit SWAR equality transfers the prefix bound to an entire word. -/
private theorem word_leaf_gain (a lo z : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ i < 64, z.testBit i = true → (a + 1 + 2 * i).Prime) :
    (wordCount z : ℝ) * Real.log lo ≤ Chebyshev.theta (a + 2 * 64 : ℕ) - Chebyshev.theta a := by
  rw [wordCount, Data.popcount64_eq_prefix]
  apply scan_gain a lo _ 64 hlo ha
  intro i hi hb
  change (z % 2 ^ 64).testBit i = true at hb
  apply ok i hi
  simpa only [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and] using hb

/-- Join the theta increments from the two disjoint halves of each counting node. -/
private theorem tree_gain (width : ℕ) (leaf : ℕ → ℕ)
    (gain :
      ∀ a lo z : ℕ,
        1 ≤ lo →
          lo ≤ a →
          (∀ i < width, z.testBit i = true → (a + 1 + 2 * i).Prime) →
          (leaf z : ℝ) * Real.log lo ≤ Chebyshev.theta (a + 2 * width : ℕ) - Chebyshev.theta a)
    (a lo z d : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ i < width * 2 ^ d, z.testBit i = true → (a + 1 + 2 * i).Prime) :
    (countTree width leaf d z : ℝ) * Real.log lo ≤
      Chebyshev.theta (a + 2 * (width * 2 ^ d) : ℕ) - Chebyshev.theta a := by
  induction d generalizing a z with
  | zero =>
    change (leaf z : ℝ) * _ ≤ _
    simp only [pow_zero, Nat.mul_one] at ok ⊢
    exact gain a lo z hlo ha ok
  | succ d ih =>
    let s := width * 2 ^ d
    have he : width * 2 ^ (d + 1) = s + s := by rw [pow_succ, Nat.mul_two, Nat.mul_add]
    have hs : width <<< d = s := Nat.shiftLeft_eq _ _
    have hl :=
      ih a (z % (1 <<< s)) ha
        (by
          intro i hi hb
          rw [Nat.one_shiftLeft, Nat.testBit_mod_two_pow] at hb
          change i < s at hi
          simp only [decide_eq_true hi, Bool.true_and] at hb
          exact ok i (he ▸ hi.trans_le (Nat.le_add_right s s)) hb)
    have hr :=
      ih (a + 2 * s) (z >>> s) (ha.trans (Nat.le_add_right _ _))
        (by
          intro i hi hb
          rw [Nat.testBit_shiftRight] at hb
          have hp := ok (s + i) (he ▸ Nat.add_lt_add_left hi s) hb
          simpa only [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm 1 (2 * s)] using hp)
    change
      ((countTree width leaf d (z &&& ((1 <<< (width <<< d)) - 1)) +
                countTree width leaf d (z >>> (width <<< d)) :
              ℕ) :
            ℝ) *
          _ ≤
        _
    rw [hs, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.cast_add, add_mul, he,
      Nat.mul_add, ← Nat.add_assoc]
    rw [Nat.one_shiftLeft] at hl
    linarith only [hl, hr]

/-- Convert the count at any supported depth into a lower bound for the theta increment. -/
private theorem rank_gain (a lo z d : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ i < 4 * 2 ^ d, z.testBit i = true → (a + 1 + 2 * i).Prime) :
    (countMask d z : ℝ) * Real.log lo ≤
      Chebyshev.theta (a + 2 * (4 * 2 ^ d) : ℕ) - Chebyshev.theta a := by
  match d with
  | 0 =>
    let v : Fin 16 := ⟨z % 16, Nat.mod_lt _ (by decide)⟩
    have he : nibbleCount z = Data.bitCountPrefix 4 v.val := by
      rw [← nibble_checked]
      simp only [nibbleCount, v, Nat.mod_mod]
    rw [countMask, he]
    apply scan_gain a lo v.val 4 hlo ha
    intro i hi hb
    change (z % 2 ^ 4).testBit i = true at hb
    simp only [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and] at hb
    exact ok i hi hb
  | 1 => exact byte_leaf_gain a lo z hlo ha ok
  | 2 => exact tree_gain 8 byteCount byte_leaf_gain a lo z 1 hlo ha ok
  | 3 => exact tree_gain 8 byteCount byte_leaf_gain a lo z 2 hlo ha ok
  |
  d + 4 =>
    have width : 4 * 2 ^ (d + 4) = 64 * 2 ^ d := by
      rw [pow_add, Nat.mul_comm (2 ^ d) (2 ^ 4), ← Nat.mul_assoc]
      rfl
    rw [width] at ok ⊢
    exact tree_gain 64 wordCount word_leaf_gain a lo z d hlo ha ok

private def factors2 : Factors :=
  .part
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
      101, 103, 107, 109, 113, 127, 131]

private def factors137 : Factors :=
  .part
    [137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
      239, 241, 251]

private def factors257 : Factors :=
  .oddBlock 443
    [257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
      373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443]

private def factors449 : Factors :=
  .oddBlock 647
    [449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571,
      577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647]

private def factors653 : Factors :=
  .oddBlock 863
    [653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773,
      787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863]

private def factors877 : Factors :=
  .oddBlock 1091
    [877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009,
      1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091]

private def factors1093 : Factors :=
  .oddBlock 1307
    [1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213,
      1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303,
      1307]

private def factors1319 : Factors :=
  .oddBlock 1559
    [1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451,
      1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553,
      1559]

private def factors1567 : Factors :=
  .oddBlock 1789
    [1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667,
      1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787,
      1789]

private def factors1801 : Factors :=
  .oddBlock 2053
    [1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931,
      1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039,
      2053]

private def factors2063 : Factors :=
  .oddBlock 2297
    [2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161,
      2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293,
      2297]

private def factors2309 : Factors :=
  .oddBlock 2551
    [2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411,
      2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549,
      2551]

private def factors2557 : Factors :=
  .oddBlock 2791
    [2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687,
      2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789,
      2791]

private def factors2797 : Factors :=
  .oddBlock 3061
    [2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917,
      2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049,
      3061]

private def factors3067 : Factors :=
  .oddBlock 3331
    [3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209,
      3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329,
      3331]

private def factors3343 : Factors :=
  .oddBlock 3583
    [3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467,
      3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581,
      3583]

private def factors3593 : Factors :=
  .oddBlock 3851
    [3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709,
      3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847,
      3851]

private def factors3853 : Factors :=
  .oddBlock 4111
    [3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989,
      4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099,
      4111]

private def factors4127 : Factors :=
  .oddBlock 4391
    [4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243,
      4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373,
      4391]

private def factors4397 : Factors :=
  .oddBlock 4657
    [4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519,
      4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651,
      4657]

private def factors4663 : Factors :=
  .oddBlock 4951
    [4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799,
      4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943,
      4951]

private def factors4957 : Factors :=
  .oddBlock 5227
    [4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077,
      5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209,
      5227]

private def factors5231 : Factors :=
  .oddBlock 5501
    [5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387,
      5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483,
      5501]

private def factors5503 : Factors :=
  .oddBlock 5779
    [5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647,
      5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749,
      5779]

private def factors5783 : Factors :=
  .oddBlock 6053
    [5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879,
      5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047,
      6053]

private def factors6067 : Factors :=
  .oddBlock 6317
    [6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199,
      6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311,
      6317]

private def factors6323 : Factors :=
  .oddBlock 6607
    [6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451,
      6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599,
      6607]

private def factors6619 : Factors :=
  .oddBlock 6883
    [6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761,
      6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871,
      6883]

private def factors6899 : Factors :=
  .oddBlock 7187
    [6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013,
      7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177,
      7187]

private def factors7193 : Factors :=
  .oddBlock 7499
    [7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331,
      7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489,
      7499]

private def factors7507 : Factors :=
  .oddBlock 7741
    [7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603,
      7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727,
      7741]

private def factors7753 : Factors :=
  .oddBlock 8069
    [7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901,
      7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059,
      8069]

private def factors8081 : Factors :=
  .oddBlock 8191
    [8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191]

private def factors8209 : Factors :=
  .upperBlock 8209 8501
    [0, 10, 12, 22, 24, 28, 34, 54, 60, 64, 78, 82, 84, 88, 102, 108, 120, 144, 154, 160, 168, 178,
      180, 210, 214, 220, 222, 234, 238, 252, 258, 292]

private def factors8513 : Factors :=
  .upperBlock 8513 8753
    [0, 8, 14, 24, 26, 30, 50, 60, 68, 84, 86, 96, 110, 114, 116, 128, 134, 150, 156, 164, 168, 176,
      180, 186, 194, 200, 206, 218, 224, 228, 234, 240]

private def factors8761 : Factors :=
  .upperBlock 8761 9043
    [0, 18, 22, 42, 46, 58, 60, 70, 76, 78, 88, 100, 102, 106, 126, 132, 162, 168, 172, 180, 190,
      202, 208, 210, 238, 240, 246, 250, 252, 268, 280, 282]

private def factors9049 : Factors :=
  .upperBlock 9049 9341
    [0, 10, 18, 42, 54, 60, 78, 84, 88, 102, 108, 112, 124, 132, 138, 150, 154, 160, 172, 178, 190,
      192, 208, 228, 232, 234, 244, 262, 270, 274, 288, 292]

private def factors9343 : Factors :=
  .upperBlock 9343 9623
    [0, 6, 28, 34, 48, 54, 60, 70, 76, 78, 88, 90, 94, 96, 118, 120, 124, 130, 136, 148, 154, 168,
      178, 190, 196, 204, 208, 244, 258, 270, 276, 280]

private def factors9629 : Factors :=
  .upperBlock 9629 9887
    [0, 2, 14, 20, 32, 48, 50, 60, 68, 90, 92, 104, 110, 114, 120, 138, 140, 152, 158, 162, 174,
      182, 188, 200, 204, 210, 222, 228, 230, 242, 254, 258]

private def factors9901 : Factors :=
  .upperBlock 9901 10193
    [0, 6, 22, 28, 30, 40, 48, 66, 72, 106, 108, 136, 138, 160, 166, 168, 178, 190, 192, 198, 202,
      210, 232, 238, 240, 250, 258, 262, 268, 276, 280, 292]

private def factors10211 : Factors :=
  .upperBlock 10211 10499
    [0, 12, 32, 36, 42, 48, 56, 60, 62, 78, 90, 92, 102, 110, 120, 122, 126, 132, 146, 158, 180,
      188, 216, 218, 222, 242, 246, 248, 252, 266, 276, 288]

private def factors10501 : Factors :=
  .upperBlock 10501 10831
    [0, 12, 28, 30, 58, 66, 88, 96, 100, 106, 112, 126, 130, 138, 150, 156, 162, 166, 186, 190, 208,
      210, 222, 228, 232, 238, 252, 270, 280, 288, 298, 330]

private def factors10837 : Factors :=
  .upperBlock 10837 11119
    [0, 10, 16, 22, 24, 30, 46, 52, 54, 66, 72, 100, 102, 112, 120, 136, 142, 150, 156, 166, 190,
      210, 220, 222, 232, 234, 246, 250, 256, 276, 280, 282]

private def factors11131 : Factors :=
  .upperBlock 11131 11443
    [0, 18, 28, 30, 40, 42, 46, 66, 82, 108, 112, 120, 126, 130, 142, 148, 156, 168, 180, 186, 190,
      198, 220, 222, 238, 252, 262, 268, 280, 292, 306, 312]

private def factors11447 : Factors :=
  .upperBlock 11447 11783
    [0, 20, 24, 36, 42, 44, 50, 56, 72, 80, 102, 104, 132, 140, 146, 150, 170, 174, 186, 210, 230,
      234, 242, 252, 254, 270, 272, 284, 296, 330, 332, 336]

private def factors11789 : Factors :=
  .upperBlock 11789 12049
    [0, 12, 18, 24, 32, 38, 42, 44, 50, 74, 78, 98, 108, 114, 120, 134, 138, 144, 150, 152, 164,
      170, 180, 182, 192, 198, 218, 222, 248, 252, 254, 260]

private def factors12071 : Factors :=
  .upperBlock 12071 12373
    [0, 2, 26, 30, 36, 38, 42, 48, 72, 78, 86, 90, 92, 126, 132, 140, 156, 168, 170, 180, 182, 192,
      198, 206, 210, 218, 230, 252, 258, 272, 276, 302]

private def factors12377 : Factors :=
  .upperBlock 12377 12619
    [0, 2, 14, 24, 32, 36, 44, 56, 60, 74, 80, 96, 102, 110, 114, 120, 126, 134, 140, 150, 162, 164,
      170, 176, 192, 200, 206, 212, 224, 234, 236, 242]

private def factors12637 : Factors :=
  .upperBlock 12637 12923
    [0, 4, 10, 16, 22, 34, 52, 60, 66, 76, 84, 102, 106, 120, 126, 144, 154, 162, 172, 184, 186,
      192, 204, 216, 252, 256, 262, 270, 274, 280, 282, 286]

private def factors12941 : Factors :=
  .upperBlock 12941 13219
    [0, 12, 18, 26, 32, 38, 42, 60, 62, 66, 68, 92, 96, 102, 108, 122, 152, 158, 162, 168, 180, 186,
      206, 210, 218, 222, 230, 236, 242, 246, 276, 278]

private def factors13229 : Factors :=
  .upperBlock 13229 13553
    [0, 12, 20, 30, 38, 62, 68, 80, 84, 98, 102, 108, 110, 138, 152, 168, 170, 182, 188, 192, 212,
      222, 228, 234, 240, 248, 258, 270, 284, 294, 308, 324]

private def factors13567 : Factors :=
  .upperBlock 13567 13841
    [0, 10, 24, 30, 46, 52, 60, 66, 82, 102, 112, 114, 120, 124, 126, 130, 142, 144, 154, 156, 162,
      184, 190, 192, 196, 214, 222, 232, 240, 262, 264, 274]

private def factors13859 : Factors :=
  .upperBlock 13859 14173
    [0, 14, 18, 20, 24, 42, 44, 48, 54, 62, 72, 74, 104, 108, 138, 140, 150, 152, 170, 174, 192,
      198, 212, 222, 224, 228, 248, 284, 290, 294, 300, 314]

private def factors14177 : Factors :=
  .upperBlock 14177 14519
    [0, 20, 30, 44, 66, 72, 74, 104, 116, 126, 144, 146, 150, 164, 170, 192, 210, 212, 224, 230,
      234, 242, 246, 254, 260, 270, 272, 284, 302, 312, 326, 342]

private def factors14533 : Factors :=
  .upperBlock 14533 14779
    [0, 4, 10, 16, 18, 24, 28, 30, 58, 60, 88, 94, 96, 100, 106, 120, 124, 136, 150, 166, 180, 184,
      190, 198, 204, 208, 214, 220, 226, 234, 238, 246]

private def factors14783 : Factors :=
  .upperBlock 14783 15101
    [0, 14, 30, 38, 44, 48, 60, 68, 84, 86, 96, 104, 108, 114, 140, 146, 156, 164, 168, 174, 186,
      200, 230, 234, 248, 270, 278, 290, 294, 300, 308, 318]

private def factors15107 : Factors :=
  .upperBlock 15107 15373
    [0, 14, 24, 30, 32, 42, 54, 66, 80, 86, 92, 110, 120, 126, 134, 152, 156, 162, 164, 170, 180,
      182, 192, 200, 206, 212, 222, 224, 242, 252, 254, 266]

private def factors15377 : Factors :=
  .upperBlock 15377 15667
    [0, 6, 14, 24, 36, 50, 62, 66, 74, 84, 90, 96, 116, 120, 134, 150, 164, 174, 182, 192, 204, 206,
      224, 230, 242, 252, 264, 266, 270, 272, 284, 290]

private def factors15671 : Factors :=
  .upperBlock 15671 15971
    [0, 8, 12, 56, 60, 62, 66, 68, 78, 90, 96, 102, 116, 120, 126, 132, 138, 146, 152, 188, 206,
      210, 216, 218, 230, 236, 242, 248, 252, 266, 288, 300]

private def factors15973 : Factors :=
  .upperBlock 15973 16301
    [0, 18, 28, 34, 60, 84, 88, 90, 94, 96, 100, 114, 118, 124, 130, 138, 154, 166, 168, 210, 214,
      216, 220, 244, 250, 256, 258, 276, 280, 294, 300, 328]

private def factors16319 : Factors :=
  .upperBlock 16319 16633
    [0, 14, 20, 30, 42, 44, 50, 62, 92, 98, 102, 108, 114, 128, 132, 134, 158, 162, 168, 174, 200,
      210, 228, 234, 242, 248, 254, 284, 288, 300, 312, 314]

private def factors16649 : Factors :=
  .upperBlock 16649 16963
    [0, 2, 8, 12, 24, 42, 44, 50, 54, 80, 92, 98, 110, 114, 138, 162, 174, 180, 182, 194, 222, 230,
      234, 240, 252, 254, 272, 278, 282, 288, 294, 314]

private def factors16979 : Factors :=
  .upperBlock 16979 17293
    [0, 2, 8, 14, 32, 42, 48, 50, 54, 62, 68, 74, 98, 114, 120, 128, 138, 144, 158, 180, 188, 204,
      210, 212, 224, 228, 230, 252, 260, 278, 312, 314]

private def factors17299 : Factors :=
  .upperBlock 17299 17573
    [0, 18, 22, 28, 34, 42, 52, 60, 78, 84, 88, 90, 94, 102, 118, 120, 132, 144, 150, 168, 172, 178,
      184, 190, 192, 198, 210, 220, 240, 252, 270, 274]

private def factors17579 : Factors :=
  .upperBlock 17579 17909
    [0, 2, 18, 20, 30, 44, 48, 78, 80, 90, 102, 104, 128, 134, 150, 158, 168, 170, 182, 204, 210,
      212, 228, 248, 258, 260, 272, 284, 302, 312, 324, 330]

private def factors17911 : Factors :=
  .upperBlock 17911 18191
    [0, 10, 12, 18, 28, 46, 48, 60, 66, 70, 76, 78, 102, 130, 132, 136, 138, 148, 150, 166, 178,
      186, 208, 210, 216, 220, 222, 232, 238, 258, 270, 280]

private def factors18199 : Factors :=
  .upperBlock 18199 18461
    [0, 12, 18, 24, 30, 34, 52, 54, 58, 70, 88, 90, 102, 108, 112, 114, 130, 142, 154, 168, 172,
      180, 198, 202, 214, 228, 234, 240, 244, 252, 258, 262]

private def factors18481 : Factors :=
  .upperBlock 18481 18859
    [0, 12, 22, 36, 40, 42, 58, 60, 72, 102, 106, 112, 136, 156, 180, 190, 198, 210, 220, 232, 238,
      250, 262, 268, 276, 292, 306, 312, 316, 322, 358, 378]

private def factors18869 : Factors :=
  .upperBlock 18869 19219
    [0, 30, 42, 44, 48, 50, 78, 90, 104, 110, 132, 140, 144, 162, 168, 182, 200, 204, 210, 212, 218,
      252, 270, 272, 288, 294, 312, 314, 338, 342, 344, 350]

private def factors19231 : Factors :=
  .upperBlock 19231 19489
    [0, 6, 18, 28, 36, 42, 58, 70, 78, 88, 102, 142, 148, 150, 156, 160, 172, 186, 190, 192, 196,
      198, 202, 210, 216, 226, 232, 238, 240, 246, 252, 258]

private def factors19501 : Factors :=
  .upperBlock 19501 19841
    [0, 6, 30, 40, 42, 52, 58, 70, 76, 82, 96, 102, 108, 160, 180, 186, 196, 198, 208, 216, 226,
      238, 250, 252, 258, 262, 276, 292, 300, 312, 318, 340]

private def factors19843 : Factors :=
  .upperBlock 19843 20123
    [0, 10, 18, 24, 46, 48, 70, 76, 84, 94, 106, 118, 120, 130, 136, 148, 150, 154, 168, 178, 180,
      186, 204, 208, 220, 228, 246, 258, 264, 270, 274, 280]

private def factors20129 : Factors :=
  .upperBlock 20129 20431
    [0, 14, 18, 20, 32, 44, 48, 54, 72, 90, 102, 104, 120, 132, 140, 158, 168, 194, 198, 204, 212,
      218, 224, 228, 230, 240, 260, 264, 270, 278, 282, 302]

private def factors20441 : Factors :=
  .upperBlock 20441 20771
    [0, 2, 36, 38, 42, 66, 68, 80, 92, 102, 108, 110, 122, 152, 158, 170, 186, 198, 200, 222, 240,
      252, 266, 276, 278, 290, 302, 306, 308, 312, 318, 330]

private def factors20773 : Factors :=
  .upperBlock 20773 21101
    [0, 16, 34, 36, 76, 84, 100, 106, 114, 124, 126, 130, 148, 156, 166, 174, 186, 190, 208, 210,
      228, 238, 240, 244, 246, 250, 258, 286, 288, 294, 316, 328]

private def factors21107 : Factors :=
  .upperBlock 21107 21407
    [0, 14, 32, 36, 42, 50, 56, 62, 72, 80, 84, 86, 104, 114, 120, 140, 162, 170, 176, 206, 210,
      212, 216, 234, 240, 270, 272, 276, 284, 290, 294, 300]

private def factors21419 : Factors :=
  .upperBlock 21419 21713
    [0, 14, 48, 62, 68, 72, 74, 80, 84, 98, 102, 104, 110, 138, 140, 144, 150, 158, 168, 170, 180,
      182, 192, 194, 198, 228, 230, 242, 254, 264, 282, 294]

private def factors21727 : Factors :=
  .upperBlock 21727 22031
    [0, 10, 12, 24, 30, 40, 46, 60, 72, 76, 90, 94, 112, 114, 124, 132, 136, 144, 154, 166, 184,
      202, 210, 216, 234, 250, 264, 270, 276, 286, 300, 304]

private def factors22037 : Factors :=
  .upperBlock 22037 22307
    [0, 2, 14, 26, 30, 36, 42, 54, 56, 72, 74, 86, 92, 96, 110, 116, 120, 122, 134, 152, 156, 192,
      210, 222, 234, 236, 240, 242, 246, 254, 266, 270]

private def factors22343 : Factors :=
  .upperBlock 22343 22669
    [0, 6, 24, 26, 38, 48, 54, 66, 90, 98, 104, 110, 126, 138, 140, 158, 168, 188, 198, 200, 206,
      224, 228, 230, 270, 276, 278, 294, 296, 300, 308, 326]

private def factors22679 : Factors :=
  .upperBlock 22679 22993
    [0, 12, 18, 20, 30, 38, 42, 48, 60, 62, 72, 90, 98, 104, 108, 128, 132, 138, 174, 180, 182, 192,
      198, 222, 228, 242, 258, 264, 282, 284, 294, 314]

private def factors23003 : Factors :=
  .upperBlock 23003 23291
    [0, 8, 14, 18, 24, 26, 36, 38, 50, 54, 56, 60, 68, 78, 84, 96, 114, 128, 140, 156, 164, 170,
      186, 194, 198, 200, 206, 224, 248, 266, 276, 288]

private def factors23293 : Factors :=
  .upperBlock 23293 23623
    [0, 4, 18, 28, 34, 40, 46, 64, 76, 78, 106, 124, 138, 154, 166, 180, 204, 216, 238, 244, 246,
      256, 264, 268, 270, 274, 288, 300, 306, 310, 316, 330]

private def factors23627 : Factors :=
  .upperBlock 23627 23909
    [0, 2, 6, 36, 42, 44, 50, 60, 62, 92, 114, 116, 120, 126, 134, 140, 146, 162, 174, 186, 192,
      200, 204, 206, 230, 242, 246, 252, 260, 266, 272, 282]

private def factors23911 : Factors :=
  .upperBlock 23911 24181
    [0, 6, 18, 46, 60, 66, 70, 82, 90, 96, 108, 112, 118, 132, 138, 150, 160, 166, 172, 180, 186,
      192, 196, 198, 202, 210, 222, 226, 240, 258, 268, 270]

private def factors24197 : Factors :=
  .upperBlock 24197 24551
    [0, 6, 26, 32, 42, 50, 54, 84, 120, 132, 140, 162, 174, 176, 182, 194, 210, 216, 222, 224, 242,
      246, 272, 276, 284, 302, 312, 320, 330, 336, 350, 354]

private def factors24571 : Factors :=
  .upperBlock 24571 24943
    [0, 22, 40, 52, 60, 88, 100, 106, 112, 120, 126, 138, 162, 178, 192, 196, 210, 222, 228, 238,
      250, 270, 276, 280, 288, 306, 318, 336, 346, 348, 352, 372]

private def factors24953 : Factors :=
  .upperBlock 24953 25261
    [0, 14, 18, 24, 26, 36, 60, 78, 80, 84, 104, 120, 134, 144, 158, 164, 168, 174, 194, 200, 210,
      216, 218, 230, 236, 266, 276, 284, 290, 294, 300, 308]

private def factors25301 : Factors :=
  .upperBlock 25301 25603
    [0, 2, 6, 8, 20, 38, 42, 48, 56, 66, 72, 90, 108, 110, 122, 138, 146, 152, 156, 162, 168, 170,
      222, 236, 240, 260, 276, 278, 282, 288, 300, 302]

private def factors25609 : Factors :=
  .upperBlock 25609 25931
    [0, 12, 24, 30, 34, 48, 58, 64, 70, 84, 94, 108, 124, 132, 138, 150, 154, 162, 184, 190, 192,
      210, 232, 238, 240, 258, 264, 280, 294, 304, 310, 322]

private def factors25933 : Factors :=
  .upperBlock 25933 26249
    [0, 6, 10, 18, 36, 48, 64, 66, 70, 84, 88, 96, 108, 120, 150, 166, 174, 178, 180, 186, 208, 220,
      228, 238, 244, 250, 256, 270, 276, 294, 304, 316]

private def factors26251 : Factors :=
  .upperBlock 26251 26573
    [0, 10, 12, 16, 42, 46, 58, 66, 70, 88, 96, 106, 120, 136, 142, 148, 156, 166, 172, 180, 186,
      198, 208, 228, 238, 246, 250, 262, 288, 306, 310, 322]

private def factors26591 : Factors :=
  .upperBlock 26591 26879
    [0, 6, 36, 42, 50, 56, 78, 90, 92, 96, 102, 108, 110, 120, 122, 126, 132, 138, 140, 146, 168,
      186, 192, 210, 222, 230, 242, 248, 258, 270, 272, 288]

private def factors26881 : Factors :=
  .upperBlock 26881 27211
    [0, 10, 12, 22, 40, 46, 66, 70, 72, 78, 100, 106, 112, 130, 136, 150, 162, 178, 180, 186, 192,
      196, 210, 222, 226, 228, 246, 262, 298, 310, 316, 330]

private def factors27239 : Factors :=
  .upperBlock 27239 27583
    [0, 2, 14, 20, 32, 38, 42, 44, 60, 90, 98, 122, 128, 158, 168, 170, 188, 192, 198, 210, 218,
      240, 242, 248, 270, 288, 290, 300, 302, 312, 342, 344]

private def factors27611 : Factors :=
  .upperBlock 27611 27893
    [0, 6, 20, 36, 42, 62, 78, 80, 86, 90, 122, 126, 128, 132, 138, 140, 152, 156, 162, 168, 180,
      182, 188, 192, 198, 206, 212, 216, 236, 240, 272, 282]

private def factors27901 : Factors :=
  .upperBlock 27901 28219
    [0, 16, 18, 40, 42, 46, 52, 60, 66, 82, 96, 100, 118, 126, 130, 150, 156, 168, 180, 186, 196,
      198, 208, 210, 222, 250, 262, 280, 282, 300, 310, 318]

private def factors28229 : Factors :=
  .upperBlock 28229 28571
    [0, 48, 50, 54, 60, 68, 78, 80, 90, 120, 122, 158, 164, 174, 180, 182, 200, 204, 210, 218, 234,
      248, 264, 270, 284, 288, 308, 312, 318, 320, 330, 342]

private def factors28573 : Factors :=
  .upperBlock 28573 28837
    [0, 6, 18, 24, 30, 34, 46, 48, 54, 58, 70, 76, 84, 88, 90, 96, 114, 124, 130, 138, 150, 156,
      178, 180, 186, 198, 216, 220, 234, 240, 244, 264]

private def factors28843 : Factors :=
  .upperBlock 28843 29179
    [0, 16, 24, 28, 36, 58, 66, 78, 84, 90, 106, 118, 136, 166, 174, 178, 180, 184, 190, 216, 220,
      234, 258, 280, 286, 288, 294, 304, 310, 324, 330, 336]

private def factors29191 : Factors :=
  .upperBlock 29191 29501
    [0, 10, 16, 18, 30, 40, 52, 60, 78, 96, 106, 112, 120, 136, 142, 148, 156, 172, 192, 196, 198,
      208, 210, 220, 232, 238, 246, 252, 262, 282, 292, 310]

private def factors29527 : Factors :=
  .upperBlock 29527 29873
    [0, 4, 10, 40, 42, 46, 54, 60, 72, 84, 102, 106, 114, 136, 142, 144, 156, 190, 196, 214, 226,
      232, 234, 262, 276, 292, 306, 310, 324, 336, 340, 346]

private def factors29879 : Factors :=
  .upperBlock 29879 30211
    [0, 2, 38, 42, 48, 68, 80, 104, 110, 132, 134, 150, 168, 180, 192, 210, 212, 218, 224, 230, 234,
      240, 254, 258, 260, 282, 290, 302, 308, 318, 324, 332]

private def factors30223 : Factors :=
  .upperBlock 30223 30559
    [0, 18, 30, 36, 46, 48, 70, 84, 90, 96, 100, 118, 124, 144, 166, 168, 180, 204, 208, 226, 244,
      246, 268, 270, 274, 286, 294, 306, 316, 330, 334, 336]

private def factors30577 : Factors :=
  .upperBlock 30577 30893
    [0, 16, 54, 60, 66, 72, 84, 94, 100, 112, 120, 126, 130, 136, 150, 180, 186, 196, 204, 226, 232,
      240, 252, 262, 264, 274, 276, 282, 292, 294, 304, 316]

private def factors30911 : Factors :=
  .upperBlock 30911 31223
    [0, 20, 26, 30, 38, 60, 66, 72, 102, 108, 122, 128, 140, 152, 158, 168, 170, 180, 210, 212, 228,
      236, 240, 242, 248, 266, 270, 272, 278, 282, 308, 312]

private def factors31231 : Factors :=
  .upperBlock 31231 31547
    [0, 6, 16, 18, 22, 28, 36, 40, 46, 76, 88, 90, 96, 102, 106, 126, 148, 156, 160, 162, 166, 238,
      246, 250, 258, 280, 282, 286, 300, 310, 312, 316]

private def factors31567 : Factors :=
  .upperBlock 31567 31957
    [0, 6, 16, 34, 40, 60, 76, 82, 90, 96, 100, 120, 132, 154, 156, 160, 162, 174, 184, 202, 204,
      226, 232, 250, 280, 282, 292, 306, 316, 324, 340, 390]

private def factors31963 : Factors :=
  .upperBlock 31963 32257
    [0, 10, 18, 28, 40, 46, 64, 66, 88, 94, 96, 100, 106, 114, 120, 126, 136, 154, 156, 178, 180,
      196, 210, 220, 226, 228, 240, 250, 270, 274, 288, 294]

private def factors32261 : Factors :=
  .upperBlock 32261 32537
    [0, 36, 38, 42, 48, 60, 62, 66, 80, 92, 98, 102, 108, 110, 116, 120, 140, 150, 152, 162, 168,
      180, 182, 206, 218, 230, 236, 242, 246, 270, 272, 276]

private def factors32561 : Factors :=
  .upperBlock 32561 32749
    [0, 2, 8, 12, 18, 26, 42, 48, 50, 60, 72, 86, 92, 126, 132, 146, 152, 156, 158, 188]

private def basis : Factors :=
  (.join
    (.join
      (.join
        (.join
          (.join (.join (.join factors2 factors137) (.join factors257 factors449))
            (.join (.join factors653 factors877) (.join factors1093 factors1319)))
          (.join (.join (.join factors1567 factors1801) (.join factors2063 factors2309))
            (.join (.join factors2557 factors2797) (.join factors3067 factors3343))))
        (.join
          (.join (.join (.join factors3593 factors3853) (.join factors4127 factors4397))
            (.join (.join factors4663 factors4957) (.join factors5231 factors5503)))
          (.join (.join (.join factors5783 factors6067) (.join factors6323 factors6619))
            (.join (.join factors6899 factors7193) (.join factors7507 factors7753)))))
      (.join
        (.join
          (.join (.join (.join factors8081 factors8209) (.join factors8513 factors8761))
            (.join (.join factors9049 factors9343) (.join factors9629 factors9901)))
          (.join (.join (.join factors10211 factors10501) (.join factors10837 factors11131))
            (.join (.join factors11447 factors11789) (.join factors12071 factors12377))))
        (.join
          (.join (.join (.join factors12637 factors12941) (.join factors13229 factors13567))
            (.join (.join factors13859 factors14177) (.join factors14533 factors14783)))
          (.join (.join (.join factors15107 factors15377) (.join factors15671 factors15973))
            (.join (.join factors16319 factors16649) (.join factors16979 factors17299))))))
    (.join
      (.join
        (.join
          (.join (.join (.join factors17579 factors17911) (.join factors18199 factors18481))
            (.join (.join factors18869 factors19231) (.join factors19501 factors19843)))
          (.join (.join (.join factors20129 factors20441) (.join factors20773 factors21107))
            (.join (.join factors21419 factors21727) (.join factors22037 factors22343))))
        (.join
          (.join (.join (.join factors22679 factors23003) (.join factors23293 factors23627))
            (.join (.join factors23911 factors24197) (.join factors24571 factors24953)))
          (.join (.join (.join factors25301 factors25609) (.join factors25933 factors26251))
            (.join (.join factors26591 factors26881) (.join factors27239 factors27611)))))
      (.join
        (.join (.join (.join factors27901 factors28229) (.join factors28573 factors28843))
          (.join (.join factors29191 factors29527) (.join factors29879 factors30223)))
        (.join (.join (.join factors30577 factors30911) (.join factors31231 factors31567))
          (.join (.join factors31963 factors32261) factors32561)))))

private theorem coversPacked {p : ℕ} (hp : p.Prime) (hb : p ≤ 32768) : p ∣ basis.weight := by
  have h : divisorBase 15 1 ∣ basis.weight ^ 15 := by decide +kernel
  exact hp.dvd_of_dvd_pow ((dvd_divisorBase 15 1 p hp.one_lt.le (Nat.lt_succ_of_le hb)).trans h)

/-- Count certified primes among alternating integers in a window of width eight times
a power of two.
Every counted position is certified prime below the square of the next divisor. -/
def packedCount32768 (a d : ℕ) : ℕ :=
  countMask d (liveBits basis a (4 * 2 ^ d))

/-- Apply a verified prime count to the lower theta bound across this closed real interval. -/
theorem packedTile32768 (a b d k r j : ℕ) (e f q u : ℚ) (ha : 1000000 ≤ a)
    (hb : b < (32768 + 1) * (32768 + 1)) (he : a + 8 * 2 ^ d = b) (hc : packedCount32768 a d = k)
    (hs : r ^ 2 ≤ a) (hl : PseudoPrime.Analysis.rationalLogIntervalCheck a j 20 q u = true)
    (hf : f ≤ e + k * q) (hw : (b : ℚ) ≤ e + 5 * r) : ThetaLowerSegment a b e f := by
  have ha1 : 1 ≤ a := (by decide : 1 ≤ 1000000).trans ha
  have hwid : 2 * (4 * 2 ^ d) = 8 * 2 ^ d := (Nat.mul_assoc 2 4 (2 ^ d)).symm
  have hend : a + 2 * (4 * 2 ^ d) = b := hwid ▸ he
  have hg :=
    rank_gain a a (liveBits basis a (4 * 2 ^ d)) d ha1 le_rfl
      (fun _ hi => live_is_prime basis (fun _ => coversPacked) ha1 (hend ▸ hb) hi)
  change (packedCount32768 a d : ℝ) * Real.log a ≤ _ at hg
  rw [hend, hc] at hg
  have hq : (q : ℝ) ≤ Real.log a := by
    simpa only [Rat.cast_natCast] using (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1
  intro hentry
  have hk := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg (α := ℝ) k)
  have hf' := (Rat.cast_le (K := ℝ)).2 hf
  have hw' := (Rat.cast_le (K := ℝ)).2 hw
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at hf' hw'
  refine ⟨by linarith only [hf', hk, hg, hentry], fun x hax hxb => ?_⟩
  have hx : 1000000 ≤ x := (show (1000000 : ℝ) ≤ a by exact_mod_cast ha).trans hax
  have hr := Real.le_sqrt_of_sq_le ((show (r : ℝ) ^ 2 ≤ a by exact_mod_cast hs).trans hax)
  have ht : (5 : ℝ) ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) :=
    Joint.coefficient_from_ticks (n := 1000000) (m := 13000) (by decide) hx (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only)
  apply le_trans _ ht
  apply (div_le_iff₀ (Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num only) hx))).2
  linarith only [hw', hr, hxb, hentry, Chebyshev.theta_mono hax]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
