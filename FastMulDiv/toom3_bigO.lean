-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
/- add the following to lakefile.toml:
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.30.0-rc2"

[[require]]
name = "cslib"
scope = "leanprover"
rev = "v4.30.0-rc2"
-/

import Mathlib
import Cslib.Algorithms.Lean.TimeM
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM.Toom3

open Nat (clog)

/-! ## Helper lemmas for ToomCook3 termination proof -/
/-- x % b + x / b ≤ x for b ≥ 1 -/
lemma Nat.mod_add_div_le (x b : ℕ) (hb : 1 ≤ b) : x % b + x / b ≤ x := by
  have h := Nat.div_add_mod x b
  have : x / b ≤ b * (x / b) := Nat.le_mul_of_pos_left _ (by omega)
  omega
/-- Three-part digit sum ≤ original number -/
lemma Nat.three_part_sum_le (a i : ℕ) :
    a % 2^i + (a / 2^i) % 2^i + a / 2^i / 2^i ≤ a := by
  have hpow : 1 ≤ 2^i := Nat.one_le_two_pow
  have h1 : (a / 2^i) % 2^i + a / 2^i / 2^i ≤ a / 2^i := Nat.mod_add_div_le _ _ hpow
  have h2 : a % 2^i + a / 2^i ≤ a := Nat.mod_add_div_le _ _ hpow
  omega
lemma Nat.three_part_sum_lt (a i : ℕ) (hi : 1 ≤ i) (ha : 2^i ≤ a) :
    a % 2^i + (a / 2^i) % 2^i + a / 2^i / 2^i < a := by
  have hi_ge_1 : 1 ≤ a / 2^i := by
    exact Nat.div_pos ha ( by positivity );
  have h1 : a = 2^i * (a / 2^i) + (a % 2^i) := by
    rw [ Nat.div_add_mod ]
  have h2 : a / 2^i = 2^i * (a / 2^i / 2^i) + (a / 2^i % 2^i) := by
    rw [ Nat.div_add_mod ];
  nlinarith [ Nat.zero_le ( a / 2 ^ i % 2 ^ i ), Nat.zero_le ( a / 2 ^ i / 2 ^ i ), Nat.mod_lt a ( by positivity : 0 < ( 2 ^ i : ℕ ) ), Nat.mod_lt ( a / 2 ^ i ) ( by positivity : 0 < ( 2 ^ i : ℕ ) ), pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hi, pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( show i ≥ 1 by linarith ) ]
lemma Nat.weighted_sum_le (a i : ℕ) (hi : 2 ≤ i) :
    a % 2^i + 2 * ((a / 2^i) % 2^i) + 4 * (a / 2^i / 2^i) ≤ a := by
  have h_div_mod : a = 2^i * (a / 2^i) + (a % 2^i) := by
    rw [ Nat.div_add_mod ];
  set q := a / 2^i
  set r := a % 2^i
  have hq : q = 2^i * (q / 2^i) + (q % 2^i) := by
    rw [ Nat.div_add_mod ];
  nlinarith [ Nat.zero_le ( q % 2 ^ i ), Nat.zero_le ( q / 2 ^ i ), Nat.mod_lt q ( by positivity : 0 < ( 2 ^ i ) ), Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) hi, mul_le_mul_left' ( show 2 ^ i ≥ 4 by exact le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) hi ) ) ( q / 2 ^ i ) ]
lemma Nat.weighted_sum_lt (a i : ℕ) (hi : 2 ≤ i) (ha : 2^i ≤ a) :
    a % 2^i + 2 * ((a / 2^i) % 2^i) + 4 * (a / 2^i / 2^i) < a := by
  have h_ge : a / 2^i ≥ 1 := by
    exact Nat.div_pos ha ( by positivity );
  have h_ineq : (a / 2^i % 2^i) * 2^i + (a / 2^i / 2^i) * 2^(2*i) ≤ a / 2^i * 2^i := by
    rw [ two_mul, pow_add ] ; nlinarith [ Nat.zero_le ( a / 2 ^ i % 2 ^ i ), Nat.zero_le ( a / 2 ^ i / 2 ^ i ), Nat.mod_add_div ( a / 2 ^ i ) ( 2 ^ i ), pow_pos ( zero_lt_two' ℕ ) i ] ;
  have h_ineq : 2 * (a / 2^i % 2^i) + 4 * (a / 2^i / 2^i) < (a / 2^i % 2^i) * 2^i + (a / 2^i / 2^i) * 2^(2*i) := by
    rcases n : a / 2 ^ i % 2 ^ i with ( _ | _ | n ) <;> rcases m : a / 2 ^ i / 2 ^ i with ( _ | _ | m ) <;> simp_all +decide [ Nat.pow_succ' ];
    any_goals nlinarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) hi, Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( show 2 * i ≥ 2 by linarith ) ];
    · rw [ Nat.mod_eq_of_lt ] at n <;> linarith;
    · exact lt_of_lt_of_le ( by decide ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.mul_le_mul_left 2 hi ) );
    · nlinarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( show 2 * i ≥ 4 by linarith ) ];
  linarith [ Nat.mod_add_div a ( 2 ^ i ) ]
lemma Nat.max_ge_two_pow_i (a b : ℕ) (hn : ¬ Nat.size (max a b) ≤ 3) :
    2 ^ (((max a b).size + 2) / 3) ≤ max a b := by
  have h_max_ge_2i : 2 ^ ((Nat.size (max a b)) - 1) ≤ max a b := by
    rcases i : Nat.size ( Max.max a b ) with ( _ | _ | i ) <;> simp_all +decide [ Nat.pow_succ' ];
    have := Nat.lt_size.mp ( by linarith : Nat.size ( Max.max a b ) > ‹_› + 1 ) ; simp_all +decide [ Nat.pow_succ' ];
  exact le_trans ( pow_le_pow_right₀ ( by decide ) ( Nat.div_le_of_le_mul <| by omega ) ) h_max_ge_2i
/-- Bitwise AND with mask equals mod -/
lemma Nat.and_mask_eq_mod (a i : ℕ) :
    a &&& ((1 <<< i) - 1) = a % 2^i := by
  rw [Nat.one_shiftLeft]
  exact Nat.and_two_pow_sub_one_eq_mod a i
lemma Nat.shiftRight_double (a i : ℕ) :
    a >>> (i <<< 1) = a / 2^i / 2^i := by
  simp +decide [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ];
  rw [ Nat.div_div_eq_div_mul, pow_mul ];
  ring
/-- n <<< 1 = 2 * n for Nat -/
lemma Nat.shiftLeft_one_eq_mul_two (n : ℕ) : n <<< 1 = 2 * n := by
  simp [Nat.shiftLeft_eq]; ring
/-- n <<< 2 = 4 * n for Nat -/
lemma Nat.shiftLeft_two_eq_mul_four (n : ℕ) : n <<< 2 = 4 * n := by
  simp [Nat.shiftLeft_eq]; ring
/-! ## The 5 decreasing lemmas -/
lemma ToomCook3.decreasing_w0 (a b : ℕ) (hn : ¬ Nat.size (max a b) ≤ 3) :
    (↑(a &&& ((1 <<< (((max a b).size + 2) / 3)) - 1)) : ℤ).natAbs +
    (↑(b &&& ((1 <<< (((max a b).size + 2) / 3)) - 1)) : ℤ).natAbs < a + b := by
  have h_max_ge_two_pow_i : 2 ^ (((max a b).size + 2) / 3) ≤ max a b := by
    exact?
  have h_sum_lt : (a &&& ((1 <<< ((Nat.size (max a b) + 2) / 3)) - 1)) + (b &&& ((1 <<< ((Nat.size (max a b) + 2) / 3)) - 1)) < a + b := by
    cases max_cases a b <;> simp_all +decide [ Nat.shiftLeft_eq ];
    · refine' add_lt_add_of_lt_of_le _ _;
      · exact lt_of_lt_of_le ( Nat.mod_lt _ ( by positivity ) ) h_max_ge_two_pow_i;
      · exact Nat.mod_le _ _;
    · exact add_lt_add_of_le_of_lt ( Nat.mod_le _ _ ) ( Nat.mod_lt _ ( by positivity ) |> LT.lt.trans_le <| by linarith );
  grind
lemma ToomCook3.decreasing_w1 (a b : ℕ) (hn : ¬ Nat.size (max a b) ≤ 3) :
    let i := ((max a b).size + 2) / 3
    let mask := (1 <<< i) - 1
    (↑((a &&& mask) + (a >>> (i <<< 1))) + ↑((a >>> i) &&& mask) : ℤ).natAbs +
    (↑((b &&& mask) + (b >>> (i <<< 1))) + ↑((b >>> i) &&& mask) : ℤ).natAbs < a + b := by
  have h_ineq : ∀ (x : ℕ), x ≥ 2 ^ (((max a b).size + 2) / 3) → x % 2 ^ (((max a b).size + 2) / 3) + (x / 2 ^ (((max a b).size + 2) / 3)) % 2 ^ (((max a b).size + 2) / 3) + x / 2 ^ (((max a b).size + 2) / 3) / 2 ^ (((max a b).size + 2) / 3) < x := by
    intros x hx
    apply Nat.three_part_sum_lt x (((max a b).size + 2) / 3) (by
    omega) hx;
  have h_ineq_a : a % 2 ^ (((max a b).size + 2) / 3) + (a / 2 ^ (((max a b).size + 2) / 3)) % 2 ^ (((max a b).size + 2) / 3) + a / 2 ^ (((max a b).size + 2) / 3) / 2 ^ (((max a b).size + 2) / 3) ≤ a := by
    exact?
  have h_ineq_b : b % 2 ^ (((max a b).size + 2) / 3) + (b / 2 ^ (((max a b).size + 2) / 3)) % 2 ^ (((max a b).size + 2) / 3) + b / 2 ^ (((max a b).size + 2) / 3) / 2 ^ (((max a b).size + 2) / 3) ≤ b := by
    exact?;
  have h_ineq_max : max a b ≥ 2 ^ (((max a b).size + 2) / 3) := by
    apply Nat.max_ge_two_pow_i; exact hn;
  cases max_choice a b <;> simp_all +decide [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ];
  · norm_cast;
    convert add_lt_add_of_lt_of_le ( h_ineq a h_ineq_max ) h_ineq_b using 1 ; ring;
    norm_num [ Nat.pow_mul, Nat.div_div_eq_div_mul ] ; ring;
  · norm_cast;
    rw [ show ( b.size + 2 ) / 3 * 2 = ( b.size + 2 ) / 3 + ( b.size + 2 ) / 3 by ring ] ; simp_all +decide [ Nat.pow_add, Nat.div_div_eq_div_mul ] ;
    linarith [ h_ineq b h_ineq_max ]
lemma ToomCook3.decreasing_w_neg_1 (a b : ℕ) (hn : ¬ Nat.size (max a b) ≤ 3) :
    let i := ((max a b).size + 2) / 3
    let mask := (1 <<< i) - 1
    (↑((a &&& mask) + (a >>> (i <<< 1))) - ↑((a >>> i) &&& mask) : ℤ).natAbs +
    (↑((b &&& mask) + (b >>> (i <<< 1))) - ↑((b >>> i) &&& mask) : ℤ).natAbs < a + b := by
  refine' lt_of_le_of_lt ( add_le_add ( _ : _ ≤ _ ) ( _ : _ ≤ _ ) ) _;
  exact ( a % 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) + a / 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) / 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) ) + ( a / 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) % 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) );
  exact b % 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) + b / 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) / 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) + b / 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) % 2 ^ ( ( ( max a b ).size + 2 ) / 3 );
  · refine' le_trans ( Int.natAbs_sub_le _ _ ) _ ; norm_cast;
    simp +decide [ Nat.and_mask_eq_mod, Nat.shiftRight_eq_div_pow ];
    rw [ Nat.div_div_eq_div_mul ] ; norm_num [ Nat.shiftLeft_eq ] ; ring_nf ; norm_num;
  · refine' le_trans ( Int.natAbs_sub_le _ _ ) _ ; norm_cast ; simp +arith +decide [ Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq_mul_pow ];
    rw [ Nat.div_div_eq_div_mul ] ; ring_nf ; norm_num;
  · have h_max_ge_two_pow_i : 2 ^ (( (max a b).size + 2 ) / 3) ≤ max a b := by
      exact?;
    have h_three_part_sum_lt : ∀ x : ℕ, 2 ^ (( (max a b).size + 2 ) / 3) ≤ x → x % 2 ^ (( (max a b).size + 2 ) / 3) + (x / 2 ^ (( (max a b).size + 2 ) / 3)) % 2 ^ (( (max a b).size + 2 ) / 3) + x / 2 ^ (( (max a b).size + 2 ) / 3) / 2 ^ (( (max a b).size + 2 ) / 3) < x := by
      intros x hx
      apply Nat.three_part_sum_lt x (( (max a b).size + 2 ) / 3) (by
      omega) hx;
    cases max_cases a b <;> simp_all +decide [ add_comm, add_left_comm, add_assoc ];
    · have := h_three_part_sum_lt a h_max_ge_two_pow_i;
      have := Nat.three_part_sum_le b ( ( a.size + 2 ) / 3 ) ; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
      linarith [ h_three_part_sum_lt a h_max_ge_two_pow_i ];
    · have h_three_part_sum_lt_a : a % 2 ^ ((b.size + 2) / 3) + (a / 2 ^ ((b.size + 2) / 3)) % 2 ^ ((b.size + 2) / 3) + a / 2 ^ ((b.size + 2) / 3) / 2 ^ ((b.size + 2) / 3) ≤ a := by
        convert Nat.three_part_sum_le a ( ( b.size + 2 ) / 3 ) using 1;
      grind
lemma ToomCook3.decreasing_w2 (a b : ℕ) (hn : ¬ Nat.size (max a b) ≤ 3) :
    let i := ((max a b).size + 2) / 3
    let mask := (1 <<< i) - 1
    (↑(a &&& mask) + ↑(((a >>> i) &&& mask) <<< 1) + ↑((a >>> (i <<< 1)) <<< 2) : ℤ).natAbs +
    (↑(b &&& mask) + ↑(((b >>> i) &&& mask) <<< 1) + ↑((b >>> (i <<< 1)) <<< 2) : ℤ).natAbs < a + b := by
  have h_le : ∀ x : ℕ, x % 2^(((max a b).size + 2) / 3) + 2 * ((x / 2^(((max a b).size + 2) / 3)) % 2^(((max a b).size + 2) / 3)) + 4 * (x / 2^(((max a b).size + 2) / 3) / 2^(((max a b).size + 2) / 3)) < x ∨ x < 2^(((max a b).size + 2) / 3) := by
    intro x; by_cases hx : x < 2 ^ (((Max.max a b).size + 2) / 3) <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ] ;
    exact Or.inl ( Nat.weighted_sum_lt _ _ ( by omega ) hx );
  cases h_le a <;> cases h_le b <;> simp_all +decide [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ];
  · norm_cast;
    convert add_lt_add ‹a % 2 ^ _ + 2 * ( a / 2 ^ _ % 2 ^ _ ) + 4 * ( a / 2 ^ _ / 2 ^ _ ) < a› ‹b % 2 ^ _ + 2 * ( b / 2 ^ _ % 2 ^ _ ) + 4 * ( b / 2 ^ _ / 2 ^ _ ) < b› using 1 ; ring;
    norm_num [ Nat.pow_mul, Nat.div_div_eq_div_mul ] ; ring;
  · norm_cast;
    simp_all +decide [ Nat.div_eq_of_lt, Nat.mod_eq_of_lt ];
    rw [ Nat.div_eq_of_lt ( show b < 2 ^ ( ( ( max a b ).size + 2 ) / 3 * 2 ) from lt_of_lt_of_le ‹_› ( Nat.pow_le_pow_right ( by decide ) ( by linarith [ Nat.div_add_mod ( ( max a b ).size + 2 ) 3, Nat.mod_lt ( ( max a b ).size + 2 ) zero_lt_three ] ) ) ) ] ; simp +arith +decide [ *, Nat.div_div_eq_div_mul ];
    convert ‹a % 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) + 2 * ( a / 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) % 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) ) + 4 * ( a / 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) / 2 ^ ( ( ( max a b ).size + 2 ) / 3 ) ) < a› using 1 ; ring;
    rw [ Nat.div_div_eq_div_mul ] ; ring;
  · norm_cast at *;
    simp_all +decide [ Nat.div_eq_of_lt, Nat.mod_eq_of_lt ];
    rw [ Nat.div_eq_of_lt ] <;> norm_num;
    · convert ‹_› using 1 ; ring;
      rw [ Nat.div_div_eq_div_mul ] ; ring;
    · exact lt_of_lt_of_le ‹_› ( Nat.pow_le_pow_right ( by decide ) ( by omega ) );
  · cases max_cases a b <;> simp_all +decide [ Nat.div_eq_of_lt ];
    · have h_sum_ge : a < 2 ^ ((a.size + 2) / 3) → a.size ≤ (a.size + 2) / 3 := by
        rw [ Nat.size_le ] ; aesop;
      grind;
    · have := @Nat.max_ge_two_pow_i b b ; simp_all +decide [ Nat.pow_succ' ];
      grind
lemma ToomCook3.decreasing_w_inf (a b : ℕ) (hn : ¬ Nat.size (max a b) ≤ 3) :
    let i := ((max a b).size + 2) / 3
    (↑(a >>> (i <<< 1)) : ℤ).natAbs + (↑(b >>> (i <<< 1)) : ℤ).natAbs < a + b := by
  have h_ge_4 : 4 ≤ max a b := by
    contrapose! hn; interval_cases max a b <;> revert hn <;> decide;
  cases max_cases a b <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ];
  · refine' add_lt_add_of_lt_of_le ( Nat.div_lt_self ( by linarith ) ( one_lt_pow₀ ( by decide ) ( by omega ) ) ) ( Nat.div_le_self _ _ );
  · refine' add_lt_add_of_le_of_lt _ _;
    · exact Nat.div_le_self _ _;
    · exact Nat.div_lt_self ( by linarith ) ( one_lt_pow₀ ( by decide ) ( by norm_num; omega ) )

-- TIME MODELING:
-- the time model is necessarily inexact. we trade some precision for clarity/generality.
-- we are modeling the time taken by arithmetic operations. it is reasonable to assume that
-- the shift, add, mask, etc. operations done within ToomCook3 take place in time linear
-- in the bit length of the operands to each such operation.

-- for instance, we model an addition of ≈ i-bit operands - an O(i) operation - with a `tick (i)`.
-- this is done on a per-line basis: a block of O(1) such O(i) operations on a given line
-- also gets a `tick i` (as opposed to, say, a `tick (3 * i)` for 3 additions).
-- so we tally up the **asymptotic** complexity of each **line**, on a **per-line basis**.
-- it could even be argued that to do this on a per-line basis is not needed,
-- as there are a constant number of lines. but we think this might be going too far.

-- can we be more precise than this? probably, yes. but if we tried to, then we'd probably
-- end up making our model too specific to be processor-agnostic. still, we will continue
-- to try and make our model more specific without losing its wide applicability.
def ToomCook3 (a_raw b_raw : ℤ) : TimeM ℕ ℤ := do
  let a := a_raw.natAbs; tick 1;
  let b := b_raw.natAbs; tick 1;
  let n := Nat.size (max a b); tick n;
  if n ≤ 3 then
    tick 1; -- operands sufficiently small that cost is negligible
    return a_raw * b_raw
  else
    let i    : ℕ := (n + 3 - 1) / 3;  tick 1;
    let mask : ℕ := (1 <<< i) - 1;    tick i;

    -- Decomposition: shift + mask on n-bit inputs
    let a0   : ℕ := a &&& mask;              tick n
    let a1   : ℕ := (a >>> i) &&& mask;      tick n
    let a2   : ℕ := a >>> (i <<< 1);         tick n
    let b0   : ℕ := b &&& mask;              tick n
    let b1   : ℕ := (b >>> i) &&& mask;      tick n
    let b2   : ℕ := b >>> (i <<< 1);         tick n

    -- Evaluation: adds/subs on ≈ i-bit digits
    let a02  : ℕ := a0 + a2;                 tick i
    let b02  : ℕ := b0 + b2;                 tick i
    let a_sub : ℤ := (a02 : ℤ) - (a1 : ℤ);   tick i
    let b_sub : ℤ := (b02 : ℤ) - (b1 : ℤ);   tick i

    -- 5 recursive multiplications (ticks propagate via ←)
    -- w1/w2 evaluation-point preparation ticked at call boundary
    let w0      ← ToomCook3 a0 b0
    tick (2 * i)   -- a02 + a1, b02 + b1
    let w1      ← ToomCook3 (a02 + a1) (b02 + b1)
    let w_neg_1 ← ToomCook3 a_sub b_sub
    tick (4 * i)   -- 2 shifts + 2 adds per operand for w2 args
    let w2      ← ToomCook3
                          (a0 + (a1 <<< 1) + (a2 <<< 2))
                          (b0 + (b1 <<< 1) + (b2 <<< 2))
    let w_inf   ← ToomCook3 a2 b2

    -- Interpolation: wi values are ~2i bits
    let t1 : ℤ := (3 * w0 + (w_neg_1 <<< 1) + w2) / 6 - (w_inf <<< 1)
    tick (2 * i)   -- mul-by-3, shift, add, div-by-6, shift, sub
    let t2 : ℤ := (w1 + w_neg_1) >>> 1
    tick (2 * i)   -- add + right-shift
    let r0 : ℤ := w0
    let r1 : ℤ := w1 - t1;              tick (2 * i)
    let r2 : ℤ := t2 - w0 - w_inf;      tick (2 * i)
    let r3 : ℤ := t1 - t2;              tick (2 * i)
    let r4 : ℤ := w_inf

    -- Recomposition: 4 left-shifts + 4 additions on 2n-bit result
    tick (2 * n)

    return a_raw.sign * b_raw.sign *
      ( r0
      + (r1 <<< i)
      + (r2 <<< (i <<< 1))
      + (r3 <<< (i + (i <<< 1)))
      + (r4 <<< (i <<< 2)))
termination_by a_raw.natAbs + b_raw.natAbs
decreasing_by
  all_goals (simp only [show (Nat.size (max a_raw.natAbs b_raw.natAbs) + 3 - 1) =
    (Nat.size (max a_raw.natAbs b_raw.natAbs) + 2) from by omega])
  · exact ToomCook3.decreasing_w0 _ _ ‹_›
  · exact ToomCook3.decreasing_w1 _ _ ‹_›
  · exact ToomCook3.decreasing_w_neg_1 _ _ ‹_›
  · exact ToomCook3.decreasing_w2 _ _ ‹_›
  · exact ToomCook3.decreasing_w_inf _ _ ‹_›

/-! ## Helper lemmas for the correctness proof -/
lemma int_sign_mul_abs (a b : ℤ) : a.sign * b.sign * (|a| * |b|) = a * b := by
  calc a.sign * b.sign * (|a| * |b|)
      = (a.sign * |a|) * (b.sign * |b|) := by ring
    _ = a * b := by rw [Int.sign_mul_abs, Int.sign_mul_abs]

set_option maxRecDepth 1024 in
lemma int_shr_int_one' (x : ℤ) : x >>> (1 : ℤ) = x / 2 := by
  cases x with
  | ofNat n =>
    change (↑(n >>> 1) : ℤ) = ↑n / 2
    rw [Nat.shiftRight_eq_div_pow]; norm_num
  | negSucc n =>
    change Int.negSucc (n >>> 1) = Int.negSucc n / 2
    rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 1 = 2 from rfl]
    rw [Int.negSucc_ediv _ (by norm_num : (0 : ℤ) < 2)]
    rw [show (↑n : ℤ).ediv 2 = ↑(n / 2) from (Int.natCast_ediv n 2).symm]
    omega

lemma toom3_identity (a0 a1 a2 b0 b1 b2 : ℤ) (i : ℕ) :
    a0 * b0 +
    ((a0 + a1 + a2) * (b0 + b1 + b2) -
      ((3 * (a0 * b0) + 2 * ((a0 - a1 + a2) * (b0 - b1 + b2)) +
        (a0 + a1 * 2 + a2 * 4) * (b0 + b1 * 2 + b2 * 4)) / 6 -
       2 * (a2 * b2))) * (2:ℤ)^i +
    (((a0 + a1 + a2) * (b0 + b1 + b2) + (a0 - a1 + a2) * (b0 - b1 + b2)) / 2 -
      a0 * b0 - a2 * b2) * (2:ℤ)^(i*2) +
    ((3 * (a0 * b0) + 2 * ((a0 - a1 + a2) * (b0 - b1 + b2)) +
        (a0 + a1 * 2 + a2 * 4) * (b0 + b1 * 2 + b2 * 4)) / 6 -
       2 * (a2 * b2) -
      ((a0 + a1 + a2) * (b0 + b1 + b2) + (a0 - a1 + a2) * (b0 - b1 + b2)) / 2) * (2:ℤ)^(i+i*2) +
    a2 * b2 * (2:ℤ)^(i*4) =
    (a0 + a1 * (2:ℤ)^i + a2 * (2:ℤ)^(i*2)) * (b0 + b1 * (2:ℤ)^i + b2 * (2:ℤ)^(i*2)) := by
  have h6 : 3 * (a0 * b0) + 2 * ((a0 - a1 + a2) * (b0 - b1 + b2)) +
     (a0 + a1 * 2 + a2 * 4) * (b0 + b1 * 2 + b2 * 4) =
     6 * (a0*b0 + a0*b2 + a1*b1 + a1*b2 + a2*b0 + a2*b1 + 3*a2*b2) := by ring
  have h2 : (a0 + a1 + a2) * (b0 + b1 + b2) + (a0 - a1 + a2) * (b0 - b1 + b2) =
     2 * (a0*b0 + a0*b2 + a1*b1 + a2*b0 + a2*b2) := by ring
  rw [h6, Int.mul_ediv_cancel_left _ (by norm_num : (6:ℤ) ≠ 0),
      h2, Int.mul_ediv_cancel_left _ (by norm_num : (2:ℤ) ≠ 0)]
  ring

lemma nat_digit_decomp (x i : ℕ) :
    (x : ℤ) = ↑(x % 2^i) + ↑((x / 2^i) % 2^i) * (2:ℤ)^i + ↑(x / 2^i / 2^i) * (2:ℤ)^(i*2) := by
  rw_mod_cast [ ← Nat.mod_add_div x ( 2 ^ i ) ];
  norm_num [ mul_assoc, pow_mul ];
  norm_num [ Nat.add_mul_div_left, Nat.mul_div_assoc, Nat.pow_succ' ];
  nlinarith [ Nat.mod_add_div ( x / 2 ^ i ) ( 2 ^ i ), pow_pos ( zero_lt_two' ℕ ) i ]

lemma Int.shiftLeft_one' (x : ℤ) : x <<< (1 : ℤ) = x * 2 := by
  have := Int.shiftLeft_eq_mul_pow x 1; simp at this; exact this

lemma Int.shiftLeft_natCast' (x : ℤ) (n : ℕ) : x <<< (n : ℤ) = x * (2:ℤ)^n :=
  Int.shiftLeft_eq_mul_pow x n

lemma ToomCook3_step (a_raw b_raw : ℤ) (N : ℕ)
    (IH : ∀ m < N, ∀ (x y : ℤ), x.natAbs + y.natAbs = m → (ToomCook3 x y).ret = x * y)
    (hN : a_raw.natAbs + b_raw.natAbs = N)
    (h : ¬ (max a_raw.natAbs b_raw.natAbs).size ≤ 3) :
    (ToomCook3 a_raw b_raw).ret = a_raw * b_raw := by
  rw [ToomCook3.eq_def]
  simp only [if_neg h]
  simp only [TimeM.ret_bind, TimeM.ret_tick, TimeM.ret_pure]
  set a := a_raw.natAbs with ha_def
  set b := b_raw.natAbs with hb_def
  simp only [show (max a b).size + 3 - 1 = (max a b).size + 2 from by omega]
  set i := ((max a b).size + 2) / 3 with hi_def
  set mask := (1 <<< i) - 1 with hmask_def
  set a0 := a &&& mask with ha0_def
  set a1 := (a >>> i) &&& mask with ha1_def
  set a2 := a >>> (i <<< 1) with ha2_def
  set b0 := b &&& mask with hb0_def
  set b1 := (b >>> i) &&& mask with hb1_def
  set b2 := b >>> (i <<< 1) with hb2_def
  have e0 : (ToomCook3 (↑a0) (↑b0)).ret = ↑a0 * ↑b0 := by
    apply IH _ _ (↑a0) (↑b0) rfl
    have hd := ToomCook3.decreasing_w0 a b h
    rw [ha0_def, hb0_def, hmask_def, hi_def]; omega
  have e1 : (ToomCook3 (↑(a0 + a2) + ↑a1) (↑(b0 + b2) + ↑b1)).ret
      = (↑(a0 + a2) + ↑a1) * (↑(b0 + b2) + ↑b1) := by
    apply IH _ _ _ _ rfl
    have hd := ToomCook3.decreasing_w1 a b h
    simp only [ha0_def, ha1_def, ha2_def, hb0_def, hb1_def, hb2_def, hmask_def, hi_def] at hd ⊢
    omega
  have em1 : (ToomCook3 (↑(a0 + a2) - ↑a1) (↑(b0 + b2) - ↑b1)).ret
      = (↑(a0 + a2) - ↑a1) * (↑(b0 + b2) - ↑b1) := by
    apply IH _ _ _ _ rfl
    have hd := ToomCook3.decreasing_w_neg_1 a b h
    simp only [ha0_def, ha1_def, ha2_def, hb0_def, hb1_def, hb2_def, hmask_def, hi_def] at hd ⊢
    omega
  have e2 : (ToomCook3 (↑a0 + ↑(a1 <<< 1) + ↑(a2 <<< 2)) (↑b0 + ↑(b1 <<< 1) + ↑(b2 <<< 2))).ret
      = (↑a0 + ↑(a1 <<< 1) + ↑(a2 <<< 2)) * (↑b0 + ↑(b1 <<< 1) + ↑(b2 <<< 2)) := by
    apply IH _ _ _ _ rfl
    have hd := ToomCook3.decreasing_w2 a b h
    simp only [ha0_def, ha1_def, ha2_def, hb0_def, hb1_def, hb2_def, hmask_def, hi_def] at hd ⊢
    omega
  have einf : (ToomCook3 (↑a2) (↑b2)).ret = ↑a2 * ↑b2 := by
    apply IH _ _ (↑a2) (↑b2) rfl
    have hd := ToomCook3.decreasing_w_inf a b h
    simp only [ha2_def, hb2_def, hi_def] at hd ⊢
    omega
  rw [e0, e1, em1, e2, einf]
  convert int_sign_mul_abs a_raw b_raw using 1
  convert congr_arg _ ( toom3_identity ( a0 : ℤ ) ( a1 : ℤ ) ( a2 : ℤ ) ( b0 : ℤ ) ( b1 : ℤ ) ( b2 : ℤ ) i ) using 2
  · -- Step 1: normalize Nat shifts, push casts, normalize Int shifts
    simp only [Nat.shiftLeft_one_eq_mul_two, Nat.shiftLeft_two_eq_mul_four,
               Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    push_cast
    simp only [Int.shiftLeft_one', int_shr_int_one',
               Int.shiftLeft_eq_mul_pow, pow_one]
    -- Step 2: the LHS has /6 with numerator in one commutative form,
    -- the RHS in another. Prove they're equal and unify.
    have h6 : ∀ (x0 x1 x2 y0 y1 y2 : ℤ),
        (3 * (x0 * y0) + (x0 + x2 - x1) * (y0 + y2 - y1) * 2 +
         (x0 + 2 * x1 + 4 * x2) * (y0 + 2 * y1 + 4 * y2)) / 6 =
        (3 * (x0 * y0) + 2 * ((x0 - x1 + x2) * (y0 - y1 + y2)) +
         (x0 + x1 * 2 + x2 * 4) * (y0 + y1 * 2 + y2 * 4)) / 6 := by
      intros; congr 1; ring
    have h2 : ∀ (x0 x1 x2 y0 y1 y2 : ℤ),
        ((x0 + x2 + x1) * (y0 + y2 + y1) +
         (x0 + x2 - x1) * (y0 + y2 - y1)) / 2 =
        ((x0 + x1 + x2) * (y0 + y1 + y2) +
         (x0 - x1 + x2) * (y0 - y1 + y2)) / 2 := by
      intros; congr 1; ring
    -- Rewrite all LHS-form /6 and /2 to RHS form
    simp only [h6, h2]
    -- Step 3: abstract the now-unified division expressions so ring ignores them
    set Q₆ := (3 * ((↑a0 : ℤ) * ↑b0) +
         2 * (((↑a0 : ℤ) - ↑a1 + ↑a2) * ((↑b0 : ℤ) - ↑b1 + ↑b2)) +
         ((↑a0 : ℤ) + ↑a1 * 2 + ↑a2 * 4) *
         ((↑b0 : ℤ) + ↑b1 * 2 + ↑b2 * 4)) / 6
    set Q₂ := (((↑a0 : ℤ) + ↑a1 + ↑a2) * ((↑b0 : ℤ) + ↑b1 + ↑b2) +
         ((↑a0 : ℤ) - ↑a1 + ↑a2) * ((↑b0 : ℤ) - ↑b1 + ↑b2)) / 2
    -- Step 4: division-free polynomial identity
    simp only [show ∀ (x : ℤ) (n : ℕ), x <<< n = x * (2 : ℤ) ^ n from by
      intro x n; exact Int.shiftLeft_eq x n]
    ring
  · convert congr_arg₂ ( · * · ) ( nat_digit_decomp a i ) ( nat_digit_decomp b i ) using 1
    · norm_num [ ha_def, hb_def ]
    · simp +decide [ ha0_def, ha1_def, ha2_def, hb0_def, hb1_def, hb2_def, Nat.and_mask_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftRight_double ]
      congr! 2
      · congr! 2
        · exact_mod_cast Nat.and_mask_eq_mod a i
        · convert congr_arg _ ( Nat.and_mask_eq_mod ( a / 2 ^ i ) i ) using 1
      · norm_num [ Nat.shiftLeft_eq, pow_mul ]
        rw [ Int.ediv_ediv ]
        norm_cast ; norm_num [ sq ]
      · congr! 2
        · rw_mod_cast [ Nat.and_mask_eq_mod ]
        · convert congr_arg Int.ofNat ( Nat.and_mask_eq_mod ( b / 2 ^ i ) i ) using 1
      · norm_num [ Nat.shiftLeft_eq, pow_mul ]
        rw [ Int.ediv_ediv ]
        norm_cast ; norm_num [ ← sq ]

theorem ToomCook3_correct (a_raw b_raw : ℤ) :
    (ToomCook3 a_raw b_raw).ret = (a_raw * b_raw) := by
  suffices H : ∀ N : ℕ, ∀ a_raw b_raw : ℤ, a_raw.natAbs + b_raw.natAbs = N →
      (ToomCook3 a_raw b_raw).ret = a_raw * b_raw by
    exact H _ a_raw b_raw rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro a_raw b_raw hN
    by_cases h : (max a_raw.natAbs b_raw.natAbs).size ≤ 3
    · rw [ToomCook3.eq_def]; simp [h]
    · exact ToomCook3_step a_raw b_raw N IH hN h

/-!
# Abstract master-theorem lemmas for Toom-Cook 3 complexity
These lemmas are stated purely in terms of an abstract "cost" structure on some type `α`
(a size function, a cost function, a termination measure `μ`, and a children function `ch`).
They are completely independent of the `TimeM` monad / cslib, so that they can be reused
to derive both the upper and lower asymptotic bounds for `ToomCook3`.
-/
namespace Toom3Master
open Real
/-
Eventually, `n ^ q` dominates any constant `b`, for a positive exponent `q`.
-/
lemma eventually_le_rpow (q b : ℝ) (hq : 0 < q) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → b ≤ (n : ℝ) ^ q := by
  obtain ⟨ n0, hn0 ⟩ := pow_unbounded_of_one_lt b ( Real.one_lt_rpow ( by norm_num : ( 1 : ℝ ) < 2 ) hq );
  refine' ⟨ 2 ^ n0, fun n hn => hn0.le.trans _ ⟩;
  rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_comm, Real.rpow_mul ( by positivity ), Real.rpow_natCast ];
  gcongr ; norm_cast
/-
The shifted-power bound: `(n+K)^p ≤ n^p + C·n^{p-1}` for suitable `C`, when `1 ≤ p ≤ 2`.
-/
lemma rpow_shift_bound (p K : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 1 ≤ n → (n + K) ^ p ≤ n ^ p + C * n ^ (p - 1) := by
  -- Let's choose $C = 2K + K^2$. We need to show that for all $n \geq 1$, $(n + K)^p \leq n^p + C n^{p-1}$.
  use 2 * K + K^2;
  refine' ⟨ by positivity, fun n hn => _ ⟩
  have h_bound : (n + K)^p ≤ n^p * (1 + K / n)^(2 : ℝ) := by
    have h_bound : (n + K)^p ≤ n^p * (1 + K / n)^p := by
      rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ), mul_add, mul_one, mul_div_cancel₀ _ ( by positivity ) ];
    exact h_bound.trans ( mul_le_mul_of_nonneg_left ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith [ div_nonneg hK ( by linarith : 0 ≤ n ) ] ) hp2 ) ( by norm_num ) ) ( by positivity ) );
  rw [ Real.rpow_sub ] <;> try positivity;
  convert h_bound.trans _ using 1 ; ring_nf;
  norm_num ; ring_nf ; norm_num;
  exact mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( by nlinarith ) ) ( by positivity )
/-
A convexity bound: for `g x = c·x^p - e·x` with `c ≥ 0`, `1 ≤ p`, on `[0, s]` the value at
any `t ∈ [0,s]` is at most `max (g 0) (g s) = max 0 (g s)`.
-/
lemma phi_convex_bound (p c e : ℝ) (hp : 1 ≤ p) (hc : 0 ≤ c)
    (t s : ℝ) (ht0 : 0 ≤ t) (hts : t ≤ s) :
    c * t ^ p - e * t ≤ max 0 (c * s ^ p - e * s) := by
  by_cases hs : s = 0 <;> by_cases ht : t = 0 <;> simp_all +decide [ le_max_iff ];
  · exact False.elim <| ht <| le_antisymm hts ht0;
  · norm_num [ show p ≠ 0 by linarith ];
  · -- By convexity, we have $g(t) \leq (1 - \lambda) g(0) + \lambda g(s)$ for $\lambda = t / s$.
    set lambda := t / s with hlambda
    have h_convex : c * t ^ p - e * t ≤ (1 - lambda) * (c * 0 ^ p - e * 0) + lambda * (c * s ^ p - e * s) := by
      have h_convex : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => c * x ^ p - e * x) := by
        apply_rules [ ConvexOn.sub, ConvexOn.smul, convexOn_rpow ];
        exact ⟨ convex_Ici _, fun x hx y hy a b ha hb hab => by simp [ mul_add, add_mul, mul_assoc, mul_comm e ] ⟩;
      have := h_convex.2 ( show 0 ∈ Set.Ici 0 by norm_num ) ( show s ∈ Set.Ici 0 by exact Set.mem_Ici.mpr ( by linarith ) );
      convert @this ( 1 - lambda ) ( lambda ) ( sub_nonneg.2 <| div_le_one_of_le₀ hts <| by linarith ) ( div_nonneg ht0 <| by linarith ) ( by ring ) using 1 ; norm_num [ hlambda, hs ];
    norm_num [ show p ≠ 0 by linarith ] at *;
    exact Classical.or_iff_not_imp_left.2 fun h => by nlinarith [ show 0 < t / s by exact div_pos ( lt_of_le_of_ne ht0 ( Ne.symm ht ) ) ( lt_of_le_of_ne ( by linarith ) ( Ne.symm hs ) ), show t / s ≤ 1 by rw [ div_le_iff₀ ( lt_of_le_of_ne ( by linarith ) ( Ne.symm hs ) ) ] ; linarith ] ;
/-
The core analytic inequality of the master theorem upper bound.
For the recurrence `T(n) ≤ overhead + 5·T((n+11)/3)` with `3^p = 5`, choosing the linear
correction coefficient `e = 30` and `c ≥ 31`, the bound `Φ(n) = A + c·n^p - e·n` is
eventually self-absorbing.
-/
lemma master_step_ineq (p : ℝ) (hp : (3:ℝ) ^ p = 5) (hp1 : 1 < p) (hp2 : p < 2)
    (A c e : ℝ) (hA : 0 ≤ A) (he : e = 30) (hce : e + 1 ≤ c) :
    ∃ n0 : ℕ, 6 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      (16 * (n:ℝ) + 17) + 5 * (A + c * (((n:ℝ) + 11) / 3) ^ p - e * (((n:ℝ) + 11) / 3))
        ≤ A + c * (n:ℝ) ^ p - e * (n:ℝ) := by
  -- Apply `rpow_shift_bound` to obtain the bound for $(n+11)^p$.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 1 ≤ n → (n + 11) ^ p ≤ n ^ p + C * n ^ (p - 1) := by
    convert rpow_shift_bound p 11 ( by linarith ) ( by linarith ) ( by linarith ) using 1;
  -- Apply `eventually_le_rpow` to obtain the bound for $c * C * n^{p-1}$.
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n → c * C * (n : ℝ) ^ (p - 1) ≤ 2 * n := by
    have h_eventually_le : ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n → (c * C / 2) ≤ (n : ℝ) ^ (2 - p) := by
      convert eventually_le_rpow ( 2 - p ) ( c * C / 2 ) ( by linarith : 0 < 2 - p ) using 1;
    obtain ⟨ n1, hn1 ⟩ := h_eventually_le; use n1 + 1; intros n hn; specialize hn1 n ( by linarith ) ; rw [ show ( 2 - p ) = 1 - ( p - 1 ) by ring, Real.rpow_sub' ] at hn1 <;> norm_num at *;
    · rw [ le_div_iff₀ ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ] at hn1 ; linarith;
    · linarith;
  refine' ⟨ n1 + 6 + ⌈2 * A⌉₊ + 1, _, _ ⟩ <;> norm_num;
  · linarith;
  · intro n hn; have := hn1 n ( by linarith ) ; have := hC.2 n ( by norm_cast; linarith ) ; norm_num [ Real.div_rpow ( show ( 0:ℝ ) ≤ n + 11 by positivity ) ( show ( 0:ℝ ) ≤ 3 by positivity ) ] at *;
    rw [ hp ] ; nlinarith [ Nat.le_ceil ( 2 * A ), ( by norm_cast : ( n1:ℝ ) + 6 + ⌈2 * A⌉₊ + 1 ≤ n ) ] ;
/-
The core analytic step inequality with the linear correction coefficient coupled to the
leading coefficient (`e = c`). The threshold `N0` is independent of `A` and `c`; only the
required size `c0` of the leading coefficient depends on `A`.
-/
lemma master_step_ineq2 (p : ℝ) (hp : (3:ℝ) ^ p = 5) (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ N0 : ℕ, 6 ≤ N0 ∧ ∀ A : ℝ, 0 ≤ A → ∃ c0 : ℝ, 0 < c0 ∧ ∀ c : ℝ, c0 ≤ c →
      ∀ n : ℕ, N0 ≤ n →
      (16 * (n:ℝ) + 17) + 5 * (A + c * (((n:ℝ) + 11) / 3) ^ p - c * (((n:ℝ) + 11) / 3))
        ≤ A + c * (n:ℝ) ^ p - c * (n:ℝ) := by
  -- Set `N0 := max 6 (max n1 1)`. Provide it; `6 ≤ N0`.
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n → 3 * (rpow_shift_bound p 11 hp1.le hp2.le (by norm_num)).choose ≤ (n : ℝ) ^ (2 - p) := by
    convert eventually_le_rpow ( 2 - p ) ( 3 * ( rpow_shift_bound p 11 hp1.le hp2.le ( by norm_num ) ).choose ) ( by linarith ) using 1;
  refine' ⟨ n1 + 6, by linarith, fun A hA => _ ⟩;
  refine' ⟨ 48 + 3 * ( 17 + 4 * A ) / ( n1 + 6 ) + 1, _, _ ⟩ <;> norm_num at *;
  · positivity;
  · intro c hc n hn
    have h_bound : c * ((n : ℝ) ^ p + (rpow_shift_bound p 11 hp1.le hp2.le (by norm_num)).choose * (n : ℝ) ^ (p - 1)) - (5 / 3) * c * (n + 11) + 16 * n + 17 + 5 * A ≤ A + c * (n : ℝ) ^ p - c * n := by
      have h_bound : (rpow_shift_bound p 11 hp1.le hp2.le (by norm_num)).choose * (n : ℝ) ^ (p - 1) ≤ (1 / 3) * n := by
        have := hn1 n ( by linarith ) ; rw [ show ( 2 - p ) = 1 - ( p - 1 ) by ring, Real.rpow_sub ] at this <;> norm_num at *;
        · rw [ le_div_iff₀ ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ] at this ; linarith;
        · linarith;
      rw [ add_div', div_add_one, div_le_iff₀ ] at * <;> nlinarith [ ( by norm_cast : ( n1:ℝ ) + 6 ≤ n ) ];
    have := Exists.choose_spec ( rpow_shift_bound p 11 hp1.le hp2.le ( by norm_num ) );
    have := this.2 n ( by norm_cast; linarith ) ; rw [ Real.div_rpow ( by positivity ) ( by positivity ) ] ; ring_nf at *; norm_num at *;
    rw [ hp ] ; nlinarith [ show 0 ≤ c by exact le_trans ( by positivity ) hc ] ;
/-
Over the bounded region `sz x < N`, with the value measure satisfying `μ x < 2^(sz x + 1)`,
the cost is bounded by a (huge but finite) constant. Proved by a geometric strong induction on `μ`.
-/
lemma geometric_region_bound
    {α : Type*} (sz : α → ℕ) (cost : α → ℝ) (μ : α → ℕ) (ch : α → List α)
    (N : ℕ) (hN : 6 ≤ N)
    (hpos : ∀ x, 0 ≤ cost x)
    (hbase3 : ∀ x, sz x ≤ 3 → cost x ≤ 6)
    (hrec : ∀ x, ¬ sz x ≤ 3 → cost x ≤ (16 * (sz x : ℝ) + 17) + ((ch x).map cost).sum)
    (hchild_sz : ∀ x, ¬ sz x ≤ 3 → ∀ y ∈ ch x, 3 * sz y ≤ sz x + 11)
    (hchild_len : ∀ x, ¬ sz x ≤ 3 → (ch x).length ≤ 5)
    (hchild_mu : ∀ x, ¬ sz x ≤ 3 → ∀ y ∈ ch x, μ y < μ x)
    (hμ : ∀ x, μ x < 2 ^ (sz x + 1)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, sz x < N → cost x ≤ A := by
  -- Set `D := 16 * (N:ℝ) + 17` (note `D > 0`).
  set D : ℝ := 16 * (N:ℝ) + 17 with hD_def;
  -- Define the geometric bound `B k := D * (5 ^ (k+1) - 1)` for `k : ℕ` (as a real).
  set B : ℕ → ℝ := fun k => D * (5 ^ (k + 1) - 1) with hB_def;
  -- Prove the key claim by strong induction on `k`:
  have claim : ∀ k, ∀ x, μ x = k → sz x < N → cost x ≤ B k := by
    intro k x hk hN; induction' k using Nat.strong_induction_on with k ih generalizing x; by_cases hx : sz x ≤ 3 <;> simp_all +decide ;
    · exact le_trans ( hbase3 x hx ) ( by nlinarith [ show ( 5 : ℝ ) ^ ( k + 1 ) ≥ 5 by exact le_self_pow₀ ( by norm_num ) ( by linarith ), show ( N : ℝ ) ≥ 6 by norm_cast ] );
    · -- For the sum: every element of `(ch x).map cost` is `cost y` for some `y ∈ ch x`; by `hchild_mu` `μ y < μ x = k`, and by `hchild_sz` together with `sz x < N` and `N ≥ 6` we get `sz y < N` (since `3 * sz y ≤ sz x + 11 ≤ (N-1) + 11 = N + 10 < 3*N`, so `sz y < N`).
      have hsum_bound : (List.map cost (ch x)).sum ≤ 5 * D * (5 ^ k - 1) := by
        have hsum_bound : ∀ y ∈ ch x, cost y ≤ D * (5 ^ k - 1) := by
          intro y hy; specialize ih ( μ y ) ( by linarith [ hchild_mu x hx y hy ] ) y rfl; simp_all +decide ;
          exact le_trans ( ih ( by linarith [ hchild_sz x hx y hy ] ) ) ( mul_le_mul_of_nonneg_left ( sub_le_sub_right ( pow_le_pow_right₀ ( by norm_num ) ( by linarith [ hchild_mu x hx y hy ] ) ) _ ) ( by positivity ) );
        refine' le_trans ( List.sum_le_sum hsum_bound ) _;
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, List.sum_map_mul_left ];
        exact mul_le_mul_of_nonneg_right ( mod_cast hchild_len x hx ) ( mul_nonneg ( sub_nonneg.2 <| one_le_pow₀ <| by norm_num ) <| by positivity );
      refine le_trans ( hrec x hx ) ?_;
      refine' le_trans ( add_le_add ( show ( 16 * sz x + 17 : ℝ ) ≤ D by push_cast [ hD_def ] ; linarith [ show ( sz x : ℝ ) + 1 ≤ N by norm_cast ] ) hsum_bound ) _ ; ring_nf ; norm_num;
      nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 5 ) ( show k ≥ 0 by norm_num ) ];
  refine' ⟨ D * ( 5 ^ ( 2 ^ ( N + 1 ) + 1 ) - 1 ), _, _ ⟩;
  · exact mul_nonneg ( by positivity ) ( sub_nonneg_of_le ( one_le_pow₀ ( by norm_num ) ) );
  · intro x hx
    specialize claim (μ x) x rfl hx;
    exact claim.trans ( mul_le_mul_of_nonneg_left ( sub_le_sub_right ( pow_le_pow_right₀ ( by norm_num ) ( by linarith [ hμ x, Nat.pow_le_pow_right ( by norm_num : 1 ≤ 2 ) ( by linarith : sz x + 1 ≤ N + 1 ) ] ) ) _ ) ( by positivity ) )
/-
Abstract master theorem (upper bound). If a cost function on a type `α` obeys the base
identity for small sizes and a `5`-way branching recurrence with branch sizes `≤ (n+11)/3`,
a strictly decreasing termination measure `μ` bounded by `2^(size+1)`, then the cost is
`O(size^p)` where `3^p = 5`.
-/
theorem abstract_master_upper
    {α : Type*} (sz : α → ℕ) (cost : α → ℝ) (μ : α → ℕ) (ch : α → List α)
    (p : ℝ) (hp : (3:ℝ) ^ p = 5) (hp1 : 1 < p) (hp2 : p < 2)
    (hpos : ∀ x, 0 ≤ cost x)
    (hbase3 : ∀ x, sz x ≤ 3 → cost x ≤ 6)
    (hrec : ∀ x, ¬ sz x ≤ 3 → cost x ≤ (16 * (sz x : ℝ) + 17) + ((ch x).map cost).sum)
    (hchild_sz : ∀ x, ¬ sz x ≤ 3 → ∀ y ∈ ch x, 3 * sz y ≤ sz x + 11)
    (hchild_len : ∀ x, ¬ sz x ≤ 3 → (ch x).length ≤ 5)
    (hchild_mu : ∀ x, ¬ sz x ≤ 3 → ∀ y ∈ ch x, μ y < μ x)
    (hμ : ∀ x, μ x < 2 ^ (sz x + 1)) :
    ∃ (c : ℝ) (n0 : ℕ), 0 < c ∧ 0 < n0 ∧ ∀ x, n0 ≤ sz x → cost x ≤ c * (sz x : ℝ) ^ p := by
  -- Obtain $N_0$ and $A$ from `geometric_region_bound`.
  obtain ⟨N0, hN0, hA⟩ := master_step_ineq2 p hp hp1 hp2
  obtain ⟨A, hA0, hAbound⟩ := geometric_region_bound sz cost μ ch N0 hN0 hpos hbase3 hrec hchild_sz hchild_len hchild_mu hμ;
  obtain ⟨c0, hc0, hstep⟩ := hA A hA0
  set c := max c0 1 with hc
  have hc_pos : 0 < c := by
    positivity;
  -- Show that `cost x ≤ A + c * (sz x : ℝ) ^ p - c * (sz x : ℝ)` for all `x`.
  have key : ∀ x, cost x ≤ A + c * (sz x : ℝ) ^ p - c * (sz x : ℝ) := by
    intro x
    induction' m : μ x using Nat.strong_induction_on with m ih generalizing x;
    by_cases h : sz x < N0;
    · refine' le_trans ( hAbound x h ) _;
      by_cases hsz : sz x = 0;
      · simp +decide [ hsz, show p ≠ 0 by linarith ];
      · nlinarith [ show ( sz x : ℝ ) ^ p ≥ sz x by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr hsz ) hp1.le ) ];
    · -- For every `y ∈ ch x`: by IH at `μ y` (which is `< μ x = m` via `hchild_mu x (by omega) y hy`), `cost y ≤ A + c*(sz y:ℝ)^p - c*(sz y:ℝ)`. Also `(sz y:ℝ) ≤ s` from `hchild_sz` (`3 * sz y ≤ sz x + 11`, cast and divide).
      have hchild_bound : ∀ y ∈ ch x, cost y ≤ A + c * ((sz x + 11) / 3 : ℝ) ^ p - c * ((sz x + 11) / 3 : ℝ) := by
        intro y hy
        have hchild_bound : cost y ≤ A + c * (sz y : ℝ) ^ p - c * (sz y : ℝ) := by
          grind;
        have hchild_bound : c * (sz y : ℝ) ^ p - c * (sz y : ℝ) ≤ max 0 (c * ((sz x + 11) / 3 : ℝ) ^ p - c * ((sz x + 11) / 3 : ℝ)) := by
          apply phi_convex_bound p c c (by linarith) (by linarith) (sz y : ℝ) ((sz x + 11) / 3 : ℝ) (by positivity) (by
          rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ hchild_sz x ( by linarith ) y hy ]);
        rw [ max_eq_right ] at hchild_bound;
        · linarith;
        · exact sub_nonneg_of_le ( mul_le_mul_of_nonneg_left ( by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le ( by linarith [ show ( sz x : ℝ ) ≥ 6 by norm_cast; linarith ] ) hp1.le ) ) hc_pos.le );
      -- Combine with `hrec x (by omega)`: `cost x ≤ (16*(sz x:ℝ)+17) + ((ch x).map cost).sum ≤ (16*(sz x:ℝ)+17) + 5*Φs = (16*(sz x:ℝ)+17) + 5*(A + c*s^p - c*s)`.
      have hsum_bound : ((ch x).map cost).sum ≤ 5 * (A + c * ((sz x + 11) / 3 : ℝ) ^ p - c * ((sz x + 11) / 3 : ℝ)) := by
        refine' le_trans ( List.sum_le_sum hchild_bound ) _;
        simp +zetaDelta at *;
        exact mul_le_mul_of_nonneg_right ( mod_cast hchild_len x ( by linarith ) ) ( sub_nonneg_of_le <| by nlinarith [ show ( max c0 1 : ℝ ) ≥ 1 by exact le_max_right _ _, show ( ( sz x + 11 ) / 3 : ℝ ) ^ p ≥ ( sz x + 11 ) / 3 by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le ( by linarith [ show ( sz x : ℝ ) ≥ 6 by norm_cast; linarith ] ) hp1.le ) ] );
      linarith [ hrec x ( by linarith ), hstep c ( le_max_left _ _ ) ( sz x ) ( by linarith ) ];
  refine' ⟨ c, ⌈A / c⌉₊ + N0 + 1, hc_pos, by positivity, fun x hx => le_trans ( key x ) _ ⟩;
  nlinarith [ Nat.le_ceil ( A / c ), show ( sz x : ℝ ) ≥ ⌈A / c⌉₊ + N0 + 1 by exact_mod_cast hx, mul_div_cancel₀ A hc_pos.ne' ]
end Toom3Master


/-!
# Supporting Nat / size / logb facts for the Toom-Cook 3 complexity bounds
These are all independent of the `TimeM` monad. `a` and `b` play the role of `|a_raw|`, `|b_raw|`.
-/
namespace Toom3ChildBounds
open Nat
/-- Basic facts about `i = (n+2)/3`. -/
lemma three_mul_i (n : ℕ) : n ≤ 3 * ((n + 2) / 3) ∧ 3 * ((n + 2) / 3) ≤ n + 2 := by omega
/-- Each operand is below `2 ^ size`. -/
lemma operand_lt (a b : ℕ) : a < 2 ^ (max a b).size :=
  lt_of_le_of_lt (le_max_left a b) (Nat.lt_size_self _)
/-- `logb 3 5 > 1`. -/
lemma logb35_gt1 : (1:ℝ) < Real.logb 3 5 := by
  rw [show (1:ℝ) = Real.logb 3 3 by simp]
  apply Real.logb_lt_logb <;> norm_num
/-- `logb 3 5 < 2`. -/
lemma logb35_lt2 : Real.logb 3 5 < 2 := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
  rw [show (3:ℝ) ^ (2:ℝ) = 9 by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num]
  norm_num
/-- `3 ^ (logb 3 5) = 5`. -/
lemma three_rpow_logb35 : (3:ℝ) ^ (Real.logb 3 5) = 5 := by
  rw [Real.rpow_logb] <;> norm_num
/-
Value-sum bound for the measure: `a + b < 2 ^ (size + 1)`.
-/
lemma mu_lt (a b : ℕ) : a + b < 2 ^ ((max a b).size + 1) := by
  rw [ Nat.pow_succ' ];
  linarith [ show a ≤ max a b from le_max_left a b, show b ≤ max a b from le_max_right a b, show max a b < 2 ^ ( Nat.size ( max a b ) ) from Nat.lt_size_self ( max a b ) ]
/-
Size bound for the low digit `a &&& mask`.
-/
lemma digit_low_size (a i : ℕ) : (a &&& ((1 <<< i) - 1)).size ≤ i := by
  rw [ Nat.size_le ];
  refine' lt_of_le_of_lt ( Nat.and_le_right ) _;
  norm_num [ Nat.shiftLeft_eq ]
/-
The high digit `a >>> (i <<< 1)` is below `2 ^ i` provided `a < 2 ^ (3 * i)`.
-/
lemma digit_high_lt (a i : ℕ) (ha : a < 2 ^ (3 * i)) : a >>> (i <<< 1) < 2 ^ i := by
  norm_num [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ] at *;
  rw [ Nat.div_lt_iff_lt_mul <| by positivity ] ; convert ha using 1 ; ring
/-! ## The five child-size bounds.
For `n = (max a b).size`, `i = (n+2)/3`, the children of the recursion have sizes bounded so
that `3 * childsize ≤ n + 11`. -/
lemma child_w0_size (a b : ℕ) :
    3 * (max ((((a &&& ((1 <<< (((max a b).size + 2) / 3)) - 1)) : ℕ) : ℤ).natAbs)
             ((((b &&& ((1 <<< (((max a b).size + 2) / 3)) - 1)) : ℕ) : ℤ).natAbs)).size
      ≤ (max a b).size + 11 := by
  -- By `digit_low_size`, we have `(a &&& mask).size ≤ i` and `(b &&& mask).size ≤ i`.
  have h_digit_low_size : (a &&& ((1 <<< (((max a b).size + 2) / 3)) - 1)).size ≤ ((max a b).size + 2) / 3 ∧ (b &&& ((1 <<< (((max a b).size + 2) / 3)) - 1)).size ≤ ((max a b).size + 2) / 3 := by
    exact ⟨ digit_low_size _ _, digit_low_size _ _ ⟩;
  grind +locals
lemma child_w1_size (a b : ℕ) :
    let i := ((max a b).size + 2) / 3
    let mask := (1 <<< i) - 1
    3 * (max ((↑((a &&& mask) + (a >>> (i <<< 1))) + ↑((a >>> i) &&& mask) : ℤ).natAbs)
             ((↑((b &&& mask) + (b >>> (i <<< 1))) + ↑((b >>> i) &&& mask) : ℤ).natAbs)).size
      ≤ (max a b).size + 11 := by
  -- Let n := (max a b).size, i := (n+2)/3, mask := (1<<<i)-1.
  set n := (max a b).size
  set i := (n + 2) / 3
  set mask := (1 <<< i) - 1;
  have h_bound : (a &&& mask) + (a >>> (i <<< 1)) + (a >>> i &&& mask) < 2 ^ (i + 2) ∧ (b &&& mask) + (b >>> (i <<< 1)) + (b >>> i &&& mask) < 2 ^ (i + 2) := by
    have h_bound : (a &&& mask) < 2 ^ i ∧ (a >>> (i <<< 1)) < 2 ^ i ∧ (a >>> i &&& mask) < 2 ^ i ∧ (b &&& mask) < 2 ^ i ∧ (b >>> (i <<< 1)) < 2 ^ i ∧ (b >>> i &&& mask) < 2 ^ i := by
      have h_bound : (a &&& mask) < 2 ^ i ∧ (a >>> i &&& mask) < 2 ^ i ∧ (b &&& mask) < 2 ^ i ∧ (b >>> i &&& mask) < 2 ^ i := by
        have h_bound : ∀ x : ℕ, x &&& mask < 2 ^ i := by
          intro x
          have h_lt : x &&& mask ≤ 2 ^ i - 1 := by
            convert Nat.and_le_right using 1;
            norm_num [ mask, Nat.shiftLeft_eq ];
          exact lt_of_le_of_lt h_lt ( Nat.sub_lt ( by norm_num ) ( by norm_num ) );
        exact ⟨ h_bound a, h_bound _, h_bound b, h_bound _ ⟩;
      have h_bound : a < 2 ^ n ∧ b < 2 ^ n := by
        exact ⟨ operand_lt a b, operand_lt b a |> fun h => by simpa [ max_comm ] using h ⟩;
      have h_bound : a < 2 ^ (3 * i) ∧ b < 2 ^ (3 * i) := by
        exact ⟨ h_bound.1.trans_le ( Nat.pow_le_pow_right ( by decide ) ( by omega ) ), h_bound.2.trans_le ( Nat.pow_le_pow_right ( by decide ) ( by omega ) ) ⟩;
      exact ⟨ by tauto, by exact digit_high_lt a i h_bound.1, by tauto, by tauto, by exact digit_high_lt b i h_bound.2, by tauto ⟩;
    exact ⟨ by rw [ pow_add ] ; norm_num; linarith, by rw [ pow_add ] ; norm_num; linarith ⟩;
  -- So `max m_a m_b < 2^(i+2)`, `(max _ _).size ≤ i+2`, and `3*(i+2) = 3*i + 6 ≤ (n+2)+6 = n+8 ≤ n+11` via `three_mul_i`.
  have h_max_bound : (max ((a &&& mask) + (a >>> (i <<< 1)) + (a >>> i &&& mask)) ((b &&& mask) + (b >>> (i <<< 1)) + (b >>> i &&& mask))).size ≤ i + 2 := by
    rw [ Nat.size_le ];
    exact max_lt h_bound.1 h_bound.2;
  grind
lemma child_wn1_size (a b : ℕ) :
    let i := ((max a b).size + 2) / 3
    let mask := (1 <<< i) - 1
    3 * (max ((↑((a &&& mask) + (a >>> (i <<< 1))) - ↑((a >>> i) &&& mask) : ℤ).natAbs)
             ((↑((b &&& mask) + (b >>> (i <<< 1))) - ↑((b >>> i) &&& mask) : ℤ).natAbs)).size
      ≤ (max a b).size + 11 := by
  -- Let `n := (max a b).size`, `i := (n+2)/3`, `mask := (1<<<i)-1`.
  set n := (max a b).size
  set i := (n + 2) / 3
  set mask := (1 <<< i) - 1;
  -- The natAbs of the difference is bounded by $3 \cdot 2^i$.
  have h_diff_bound : ∀ x ∈ [a, b], ((↑((x &&& mask) + (x >>> (i <<< 1))) - ↑((x >>> i) &&& mask) : ℤ).natAbs) ≤ 3 * 2 ^ i := by
    -- Using the bounds for the low and high digits: $a &&& mask < 2^i$, $(a >>> i) &&& mask < 2^i$, and $a >>> (i <<< 1) < 2^i$.
    have h_digit_bounds : ∀ x ∈ [a, b], (x &&& mask) < 2 ^ i ∧ (x >>> i &&& mask) < 2 ^ i ∧ x >>> (i <<< 1) < 2 ^ i := by
      intro x hx; refine' ⟨ _, _, _ ⟩;
      · refine' lt_of_le_of_lt ( Nat.and_le_right ) _;
        exact Nat.sub_lt ( by norm_num [ Nat.shiftLeft_eq ] ) ( by norm_num ) |> LT.lt.trans_le <| by norm_num [ Nat.shiftLeft_eq ] ;
      · -- By definition of `mask`, we know that `mask < 2^i`.
        have h_mask_lt : mask < 2 ^ i := by
          exact Nat.sub_lt ( by norm_num [ Nat.shiftLeft_eq ] ) ( by norm_num [ Nat.shiftLeft_eq ] ) |> lt_of_lt_of_le <| by norm_num [ Nat.shiftLeft_eq ] ;
        exact lt_of_le_of_lt ( Nat.and_le_right ) h_mask_lt;
      · refine' digit_high_lt _ _ _;
        refine' lt_of_lt_of_le ( operand_lt _ _ ) _;
        exact max a b;
        gcongr;
        · norm_num;
        · grind;
    grind;
  -- Therefore, the size of the difference is at most $i + 2$.
  have h_diff_size : ∀ x ∈ [a, b], ((↑((x &&& mask) + (x >>> (i <<< 1))) - ↑((x >>> i) &&& mask) : ℤ).natAbs).size ≤ i + 2 := by
    intro x hx; specialize h_diff_bound x hx; rw [ Nat.size_le ] ;
    exact lt_of_le_of_lt h_diff_bound ( by rw [ pow_add ] ; linarith [ pow_pos ( by decide : 0 < 2 ) i ] );
  grind
lemma child_w2_size (a b : ℕ) :
    let i := ((max a b).size + 2) / 3
    let mask := (1 <<< i) - 1
    3 * (max ((↑(a &&& mask) + ↑(((a >>> i) &&& mask) <<< 1) + ↑((a >>> (i <<< 1)) <<< 2) : ℤ).natAbs)
             ((↑(b &&& mask) + ↑(((b >>> i) &&& mask) <<< 1) + ↑((b >>> (i <<< 1)) <<< 2) : ℤ).natAbs)).size
      ≤ (max a b).size + 11 := by
  refine' le_trans _ ( show 3 * ( ( ( max a b ).size + 2 ) / 3 + 3 ) ≤ ( max a b ).size + 11 from by omega );
  refine' Nat.mul_le_mul_left _ _;
  refine' Nat.size_le.mpr _;
  refine' max_lt _ _ <;> norm_cast <;> norm_num [ Nat.shiftLeft_eq ];
  · refine' lt_of_lt_of_le ( add_lt_add_of_lt_of_le ( add_lt_add_of_lt_of_le ( Nat.mod_lt _ ( by positivity ) ) ( Nat.mul_le_mul_right _ ( Nat.mod_lt _ ( by positivity ) |> Nat.le_of_lt ) ) ) ( Nat.mul_le_mul_right _ ( Nat.le_refl _ ) ) ) _;
    have h_shift : a >>> (((max a b).size + 2) / 3 * 2) < 2 ^ (((max a b).size + 2) / 3) := by
      convert digit_high_lt a _ _ using 1;
      · norm_num [ Nat.shiftLeft_eq ];
      · exact lt_of_lt_of_le ( operand_lt a b ) ( Nat.pow_le_pow_right ( by decide ) ( by linarith [ three_mul_i ( max a b |> Nat.size ) ] ) );
    grind;
  · -- Apply the digit size bounds to each term in the sum.
    have h_digit_bounds : b % 2 ^ ((Nat.size (max a b) + 2) / 3) < 2 ^ ((Nat.size (max a b) + 2) / 3) ∧ b >>> ((Nat.size (max a b) + 2) / 3) % 2 ^ ((Nat.size (max a b) + 2) / 3) < 2 ^ ((Nat.size (max a b) + 2) / 3) ∧ b >>> ((Nat.size (max a b) + 2) / 3 * 2) < 2 ^ ((Nat.size (max a b) + 2) / 3) := by
      refine' ⟨ Nat.mod_lt _ ( by positivity ), Nat.mod_lt _ ( by positivity ), _ ⟩;
      rw [ Nat.shiftRight_eq_div_pow ];
      refine' Nat.div_lt_of_lt_mul _;
      rw [ ← pow_add ];
      have := Nat.lt_size_self b;
      refine' this.trans_le _;
      gcongr <;> norm_num;
      linarith [ Nat.div_add_mod ( Nat.size ( max a b ) + 2 ) 3, Nat.mod_lt ( Nat.size ( max a b ) + 2 ) three_pos, show Nat.size b ≤ Nat.size ( max a b ) from Nat.size_le_size ( le_max_right a b ) ];
    grind
lemma child_winf_size (a b : ℕ) :
    let i := ((max a b).size + 2) / 3
    3 * (max (((a >>> (i <<< 1) : ℕ) : ℤ).natAbs) (((b >>> (i <<< 1) : ℕ) : ℤ).natAbs)).size
      ≤ (max a b).size + 11 := by
  refine' le_trans ( Nat.mul_le_mul_left _ <| Nat.size_le.mpr _ ) _;
  exact ( ( max a b ).size + 2 ) / 3;
  · refine' max_lt _ _;
    · refine' digit_high_lt _ _ _;
      refine' lt_of_lt_of_le ( operand_lt a b ) _;
      exact pow_le_pow_right₀ ( by decide ) ( by omega );
    · refine' digit_high_lt _ _ _;
      exact lt_of_lt_of_le ( operand_lt b a ) ( Nat.pow_le_pow_right ( by decide ) ( by simpa [ max_comm ] using three_mul_i _ |>.1 ) );
  · omega
end Toom3ChildBounds

/-! ## Time recurrence lemmas -/
/-- In the base case the cost is exactly `n + 3` where `n` is the bit-size. -/
lemma time_base (a b : ℤ) (h : (max a.natAbs b.natAbs).size ≤ 3) :
    (ToomCook3 a b).time = (max a.natAbs b.natAbs).size + 3 := by
  rw [ToomCook3.eq_def]
  simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, if_pos h]
  omega
/-- The recursive cost: a linear overhead `9n + 21i + 3` plus the five sub-multiplications. -/
lemma time_step (a b : ℤ) (h : ¬ (max a.natAbs b.natAbs).size ≤ 3) :
    (ToomCook3 a b).time =
      let A := a.natAbs
      let B := b.natAbs
      let n := (max A B).size
      let i := (n + 2) / 3
      let mask := (1 <<< i) - 1
      let a0 := A &&& mask
      let a1 := (A >>> i) &&& mask
      let a2 := A >>> (i <<< 1)
      let b0 := B &&& mask
      let b1 := (B >>> i) &&& mask
      let b2 := B >>> (i <<< 1)
      9 * n + 21 * i + 3
        + (ToomCook3 (↑a0) (↑b0)).time
        + (ToomCook3 (↑(a0 + a2) + ↑a1) (↑(b0 + b2) + ↑b1)).time
        + (ToomCook3 (↑(a0 + a2) - ↑a1) (↑(b0 + b2) - ↑b1)).time
        + (ToomCook3 (↑a0 + ↑(a1 <<< 1) + ↑(a2 <<< 2)) (↑b0 + ↑(b1 <<< 1) + ↑(b2 <<< 2))).time
        + (ToomCook3 (↑a2) (↑b2)).time := by
  rw [ToomCook3.eq_def]
  simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, if_neg h]
  simp only [show (max a.natAbs b.natAbs).size + 3 - 1 = (max a.natAbs b.natAbs).size + 2 from by omega]
  ring_nf

theorem ToomCook3_big_O :
    ∃ (c : ℝ) (n0 : ℕ), c > 0 ∧ n0 > 0 ∧
    ∀ (a_raw b_raw : ℤ),
      let n : ℝ := Nat.size (max a_raw.natAbs b_raw.natAbs)
      (n ≥ n0) → ((ToomCook3 a_raw b_raw).time : ℝ) ≤ c * n ^ Real.logb 3 5 := by
  obtain ⟨c, n0, hc, hn0, hbound⟩ := Toom3Master.abstract_master_upper
    (fun x : ℤ × ℤ => (max x.1.natAbs x.2.natAbs).size)
    (fun x : ℤ × ℤ => ((ToomCook3 x.1 x.2).time : ℝ))
    (fun x : ℤ × ℤ => x.1.natAbs + x.2.natAbs)
    (fun x : ℤ × ℤ =>
      let a := x.1.natAbs; let b := x.2.natAbs
      let i := ((max a b).size + 2) / 3
      let mask := (1 <<< i) - 1
      let a0 := a &&& mask; let a1 := (a >>> i) &&& mask; let a2 := a >>> (i <<< 1)
      let b0 := b &&& mask; let b1 := (b >>> i) &&& mask; let b2 := b >>> (i <<< 1)
      [((a0 : ℤ), (b0 : ℤ)),
       ((↑(a0 + a2) + ↑a1 : ℤ), (↑(b0 + b2) + ↑b1 : ℤ)),
       ((↑(a0 + a2) - ↑a1 : ℤ), (↑(b0 + b2) - ↑b1 : ℤ)),
       ((↑a0 + ↑(a1 <<< 1) + ↑(a2 <<< 2) : ℤ), (↑b0 + ↑(b1 <<< 1) + ↑(b2 <<< 2) : ℤ)),
       ((a2 : ℤ), (b2 : ℤ))])
    (Real.logb 3 5)
    Toom3ChildBounds.three_rpow_logb35
    Toom3ChildBounds.logb35_gt1
    Toom3ChildBounds.logb35_lt2
    (fun x => by positivity)
    (fun x hx => by
      dsimp only at hx ⊢
      rw [time_base x.1 x.2 hx]
      have h3 : ((max x.1.natAbs x.2.natAbs).size : ℝ) ≤ 3 := by exact_mod_cast hx
      push_cast; linarith)
    (fun x hx => by
      dsimp only at hx ⊢
      have hstep := time_step x.1 x.2 hx
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hstep]
      have hov : 9 * (max x.1.natAbs x.2.natAbs).size
            + 21 * (((max x.1.natAbs x.2.natAbs).size + 2) / 3) + 3
          ≤ 16 * (max x.1.natAbs x.2.natAbs).size + 17 := by omega
      have hcc := (Nat.cast_le (α := ℝ)).2 hov
      push_cast at hcc ⊢
      linarith [hcc])
    (fun x hx y hy => by
      dsimp only at hx ⊢
      simp only at hy
      fin_cases hy
      · exact Toom3ChildBounds.child_w0_size x.1.natAbs x.2.natAbs
      · exact Toom3ChildBounds.child_w1_size x.1.natAbs x.2.natAbs
      · exact Toom3ChildBounds.child_wn1_size x.1.natAbs x.2.natAbs
      · exact Toom3ChildBounds.child_w2_size x.1.natAbs x.2.natAbs
      · exact Toom3ChildBounds.child_winf_size x.1.natAbs x.2.natAbs)
    (fun x hx => by dsimp only; simp only [List.length_cons, List.length_nil]; omega)
    (fun x hx y hy => by
      dsimp only at hx ⊢
      simp only at hy
      fin_cases hy
      · exact ToomCook3.decreasing_w0 x.1.natAbs x.2.natAbs hx
      · exact ToomCook3.decreasing_w1 x.1.natAbs x.2.natAbs hx
      · exact ToomCook3.decreasing_w_neg_1 x.1.natAbs x.2.natAbs hx
      · exact ToomCook3.decreasing_w2 x.1.natAbs x.2.natAbs hx
      · exact ToomCook3.decreasing_w_inf x.1.natAbs x.2.natAbs hx)
    (fun x => Toom3ChildBounds.mu_lt x.1.natAbs x.2.natAbs)
  refine ⟨c, n0, hc, hn0, fun a_raw b_raw => ?_⟩
  intro n hn
  have hh : (n0 : ℝ) ≤ ((max a_raw.natAbs b_raw.natAbs).size : ℝ) := hn
  exact hbound (a_raw, b_raw) (by exact_mod_cast hh)

end Cslib.Algorithms.Lean.TimeM.Toom3
