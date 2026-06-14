-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

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
    contrapose! hn; interval_cases max a b <;> revert hn <;> native_decide;
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
  let a := a_raw.natAbs
  let b := b_raw.natAbs
  let n := Nat.size (max a b)
  if n ≤ 3 then return a_raw * b_raw
  else
    let i    : ℕ := (n + 3 - 1) / 3
    let mask : ℕ := (1 <<< i) - 1

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

    -- Recomposition: 4 left-shifts + 4 additions on n-bit result
    tick n

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

theorem ToomCook3_time :
    ∃ (c : ℝ), c > 0 ∧
    ∀ (a_raw b_raw : ℤ),
      let n : ℝ := Nat.size (max a_raw.natAbs b_raw.natAbs)
      ((ToomCook3 a_raw b_raw).time : ℝ) ≤ c * n ^ Real.logb 3 5 := by
  sorry

theorem ToomCook3_time_lower_witness :
    ∃ (c : ℝ), c > 0 ∧
    ∀ (n : ℕ), n ≥ 4 →
      ∃ (a b : ℤ), Nat.size (max a.natAbs b.natAbs) = n ∧
        c * (n : ℝ) ^ Real.logb 3 5 ≤ ((ToomCook3 a b).time : ℝ) := by
  sorry

end Cslib.Algorithms.Lean.TimeM.Toom3
