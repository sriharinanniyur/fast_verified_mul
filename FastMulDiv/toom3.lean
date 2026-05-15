-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

import Mathlib
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option autoImplicit false

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
/-
Three-part digit sum < original when a ≥ 2^i and i ≥ 1
-/
lemma Nat.three_part_sum_lt (a i : ℕ) (hi : 1 ≤ i) (ha : 2^i ≤ a) :
    a % 2^i + (a / 2^i) % 2^i + a / 2^i / 2^i < a := by
  -- We'll use the fact that $a / 2^i \geq 1$ to simplify the expressions involving the modulo operation.
  have hi_ge_1 : 1 ≤ a / 2^i := by
    exact Nat.div_pos ha ( by positivity );
  -- We'll use that $a \geq 2^i$ and $1 \leq i$ to simplify the expressions.
  have h1 : a = 2^i * (a / 2^i) + (a % 2^i) := by
    rw [ Nat.div_add_mod ]
  have h2 : a / 2^i = 2^i * (a / 2^i / 2^i) + (a / 2^i % 2^i) := by
    rw [ Nat.div_add_mod ];
  nlinarith [ Nat.zero_le ( a / 2 ^ i % 2 ^ i ), Nat.zero_le ( a / 2 ^ i / 2 ^ i ), Nat.mod_lt a ( by positivity : 0 < ( 2 ^ i : ℕ ) ), Nat.mod_lt ( a / 2 ^ i ) ( by positivity : 0 < ( 2 ^ i : ℕ ) ), pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hi, pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( show i ≥ 1 by linarith ) ]
/-
Weighted three-part sum ≤ a for i ≥ 2 (evaluation at x=2)
-/
lemma Nat.weighted_sum_le (a i : ℕ) (hi : 2 ≤ i) :
    a % 2^i + 2 * ((a / 2^i) % 2^i) + 4 * (a / 2^i / 2^i) ≤ a := by
  -- By definition of division and modulo, we can write $a$ as $a = 2^i * (a / 2^i) + (a % 2^i)$.
  have h_div_mod : a = 2^i * (a / 2^i) + (a % 2^i) := by
    rw [ Nat.div_add_mod ];
  -- Let $q = a / 2^i$ and $r = a % 2^i$.
  set q := a / 2^i
  set r := a % 2^i
  have hq : q = 2^i * (q / 2^i) + (q % 2^i) := by
    rw [ Nat.div_add_mod ];
  nlinarith [ Nat.zero_le ( q % 2 ^ i ), Nat.zero_le ( q / 2 ^ i ), Nat.mod_lt q ( by positivity : 0 < ( 2 ^ i ) ), Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) hi, mul_le_mul_left' ( show 2 ^ i ≥ 4 by exact le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) hi ) ) ( q / 2 ^ i ) ]
/-
Weighted three-part sum < a for i ≥ 2 when a ≥ 2^i
-/
lemma Nat.weighted_sum_lt (a i : ℕ) (hi : 2 ≤ i) (ha : 2^i ≤ a) :
    a % 2^i + 2 * ((a / 2^i) % 2^i) + 4 * (a / 2^i / 2^i) < a := by
  -- Use the fact that $a \geq 2^i$ to apply the previous lemma
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
/-
max(a,b) ≥ 2^i where i = ceil(n/3) and n = Nat.size(max a b) > 3
-/
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
/-
a >>> (i <<< 1) = a / 2^i / 2^i
-/
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
/-
Decreasing proof for the ToomCook3 w0 call
-/
lemma ToomCook3.decreasing_w0 (a b : ℕ) (hn : ¬ Nat.size (max a b) ≤ 3) :
    (↑(a &&& ((1 <<< (((max a b).size + 2) / 3)) - 1)) : ℤ).natAbs +
    (↑(b &&& ((1 <<< (((max a b).size + 2) / 3)) - 1)) : ℤ).natAbs < a + b := by
  -- By Nat.max_ge_two_pow_i, we know that max(a,b) ≥ 2^i.
  have h_max_ge_two_pow_i : 2 ^ (((max a b).size + 2) / 3) ≤ max a b := by
    exact?
  -- We need to show that (a &&& mask) + (b &&& mask) < a + b.
  have h_sum_lt : (a &&& ((1 <<< ((Nat.size (max a b) + 2) / 3)) - 1)) + (b &&& ((1 <<< ((Nat.size (max a b) + 2) / 3)) - 1)) < a + b := by
    cases max_cases a b <;> simp_all +decide [ Nat.shiftLeft_eq ];
    · refine' add_lt_add_of_lt_of_le _ _;
      · exact lt_of_lt_of_le ( Nat.mod_lt _ ( by positivity ) ) h_max_ge_two_pow_i;
      · exact Nat.mod_le _ _;
    · exact add_lt_add_of_le_of_lt ( Nat.mod_le _ _ ) ( Nat.mod_lt _ ( by positivity ) |> LT.lt.trans_le <| by linarith );
  grind
/-
Decreasing proof for the ToomCook3 w1 call
-/
lemma ToomCook3.decreasing_w1 (a b : ℕ) (hn : ¬ Nat.size (max a b) ≤ 3) :
    let i := ((max a b).size + 2) / 3
    let mask := (1 <<< i) - 1
    (↑((a &&& mask) + (a >>> (i <<< 1))) + ↑((a >>> i) &&& mask) : ℤ).natAbs +
    (↑((b &&& mask) + (b >>> (i <<< 1))) + ↑((b >>> i) &&& mask) : ℤ).natAbs < a + b := by
  -- By definition of $i$ and $mask$, we know that $a \% 2^i + (a / 2^i) \% 2^i + a / 2^i / 2^i < a$ and $b \% 2^i + (b / 2^i) \% 2^i + b / 2^i / 2^i < b$.
  have h_ineq : ∀ (x : ℕ), x ≥ 2 ^ (((max a b).size + 2) / 3) → x % 2 ^ (((max a b).size + 2) / 3) + (x / 2 ^ (((max a b).size + 2) / 3)) % 2 ^ (((max a b).size + 2) / 3) + x / 2 ^ (((max a b).size + 2) / 3) / 2 ^ (((max a b).size + 2) / 3) < x := by
    intros x hx
    apply Nat.three_part_sum_lt x (((max a b).size + 2) / 3) (by
    omega) hx;
  -- Apply the inequality to both $a$ and $b$.
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
/-
Decreasing proof for the ToomCook3 w_neg_1 call
-/
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
/-
Decreasing proof for the ToomCook3 w2 call
-/
lemma ToomCook3.decreasing_w2 (a b : ℕ) (hn : ¬ Nat.size (max a b) ≤ 3) :
    let i := ((max a b).size + 2) / 3
    let mask := (1 <<< i) - 1
    (↑(a &&& mask) + ↑(((a >>> i) &&& mask) <<< 1) + ↑((a >>> (i <<< 1)) <<< 2) : ℤ).natAbs +
    (↑(b &&& mask) + ↑(((b >>> i) &&& mask) <<< 1) + ↑((b >>> (i <<< 1)) <<< 2) : ℤ).natAbs < a + b := by
  -- Apply the fact that for any number x, x % 2^i + 2 * ((x / 2^i) % 2^i) + 4 * (x / 2^i / 2^i) ≤ x.
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
/-
Decreasing proof for the ToomCook3 w_inf call
-/
lemma ToomCook3.decreasing_w_inf (a b : ℕ) (hn : ¬ Nat.size (max a b) ≤ 3) :
    let i := ((max a b).size + 2) / 3
    (↑(a >>> (i <<< 1)) : ℤ).natAbs + (↑(b >>> (i <<< 1)) : ℤ).natAbs < a + b := by
  -- By Nat.shiftRight_le, each ≤ original. For strict: max(a,b) ≥ 2^i ≥ 4 (i ≥ 2 since n ≥ 4). So at least one of a,b is ≥ 4.
  have h_ge_4 : 4 ≤ max a b := by
    contrapose! hn; interval_cases max a b <;> revert hn <;> native_decide;
  cases max_cases a b <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ];
  · refine' add_lt_add_of_lt_of_le ( Nat.div_lt_self ( by linarith ) ( one_lt_pow₀ ( by decide ) ( by omega ) ) ) ( Nat.div_le_self _ _ );
  · refine' add_lt_add_of_le_of_lt _ _;
    · exact Nat.div_le_self _ _;
    · exact Nat.div_lt_self ( by linarith ) ( one_lt_pow₀ ( by decide ) ( by norm_num; omega ) )



-- Following the pseudocode given in *Modern Computer Arithmetic*
-- (Brent and Zimmermann)
-- Working in base 2 so we can optimize with bit shifts (as in practice)
def ToomCook3 (a_raw b_raw : ℤ) : ℤ :=
  let a := a_raw.natAbs
  let b := b_raw.natAbs
  let n := Nat.size (max a b)
  if n ≤ 3 then a_raw * b_raw
  else
    let i    : ℕ := (n + 3 - 1) / 3
    let mask : ℕ := (1 <<< i) - 1
    let a0   : ℕ := a &&& mask
    let a1   : ℕ := (a >>> i) &&& mask
    let a2   : ℕ := a >>> (i <<< 1)
    let b0   : ℕ := b &&& mask
    let b1   : ℕ := (b >>> i) &&& mask
    let b2   : ℕ := b >>> (i <<< 1)
    let a02  : ℕ := a0 + a2
    let b02  : ℕ := b0 + b2
    let a_sub : ℤ := (a02 : ℤ) - (a1 : ℤ)
    let b_sub : ℤ := (b02 : ℤ) - (b1 : ℤ)

    let w0      : ℤ := ToomCook3 a0 b0
    let w1      : ℤ := ToomCook3 (a02 + a1) (b02 + b1)
    let w_neg_1 : ℤ := ToomCook3 a_sub b_sub
    let w2      : ℤ := ToomCook3
                          (a0 + (a1 <<< 1) + (a2 <<< 2))
                          (b0 + (b1 <<< 1) + (b2 <<< 2))
    let w_inf   : ℤ := ToomCook3 a2 b2

    let t1 : ℤ := (3 * w0 + (w_neg_1 <<< 1) + w2) / 6 - (w_inf <<< 1)
    let t2 : ℤ := (w1 + w_neg_1) >>> 1
    let r0 : ℤ := w0
    let r1 : ℤ := w1 - t1
    let r2 : ℤ := t2 - w0 - w_inf
    let r3 : ℤ := t1 - t2
    let r4 : ℤ := w_inf

    a_raw.sign * b_raw.sign *
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
/-- Sign-absolute-value factoring for integer multiplication. -/
lemma int_sign_mul_abs (a b : ℤ) : a.sign * b.sign * (|a| * |b|) = a * b := by
  calc a.sign * b.sign * (|a| * |b|)
      = (a.sign * |a|) * (b.sign * |b|) := by ring
    _ = a * b := by rw [Int.sign_mul_abs, Int.sign_mul_abs]


set_option maxRecDepth 1024 in
/-- Right shift by 1 (ℤ) equals division by 2 -/
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
/-- The core Toom-Cook-3 algebraic identity: after exact interpolation,
    the reconstruction equals the product of the digit polynomials. -/
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
/-- Helper: x <<< (1 : ℤ) = x * 2 -/
lemma Int.shiftLeft_one' (x : ℤ) : x <<< (1 : ℤ) = x * 2 := by
  have := Int.shiftLeft_eq_mul_pow x 1; simp at this; exact this
/-- Helper: x <<< (n : ℤ) = x * 2^n for ℕ coercion -/
lemma Int.shiftLeft_natCast' (x : ℤ) (n : ℕ) : x <<< (n : ℤ) = x * (2:ℤ)^n :=
  Int.shiftLeft_eq_mul_pow x n

set_option maxHeartbeats 128000000 in
theorem ToomCook3_correct (a_raw b_raw : ℤ) : ToomCook3 a_raw b_raw = (a_raw * b_raw) := by
  induction a_raw, b_raw using ToomCook3.induct with
  | case1 a_raw b_raw a b n hn =>
    have h := ToomCook3.eq_def a_raw b_raw
    rw [h]; dsimp only; simp [hn]; intro h; exact absurd (show n > 3 from h) (by omega)
  | case2 a_raw b_raw a b n hn i mask a0 a1 a2 b0 b1 b2 a02 b02 a_sub b_sub ih_w0 ih_w1 ih_wm1 ih_w2 ih_winf =>
    rw [ToomCook3.eq_def]
    simp only [show ¬(Nat.size (max a_raw.natAbs b_raw.natAbs) ≤ 3) from hn, ↓reduceIte]
    simp only [
      show a_raw.natAbs = a from rfl,
      show b_raw.natAbs = b from rfl,
      show (max a b).size = n from rfl,
      show (n + 3 - 1) / 3 = i from rfl,
      show 1 <<< i - 1 = mask from rfl,
      show a &&& mask = a0 from rfl,
      show b &&& mask = b0 from rfl,
      show a >>> i &&& mask = a1 from rfl,
      show b >>> i &&& mask = b1 from rfl,
      show a >>> (i <<< 1) = a2 from rfl,
      show b >>> (i <<< 1) = b2 from rfl,
      show a0 + a2 = a02 from rfl,
      show b0 + b2 = b02 from rfl,
      show (↑a02 : ℤ) - (↑a1 : ℤ) = a_sub from rfl,
      show (↑b02 : ℤ) - (↑b1 : ℤ) = b_sub from rfl
    ]
    rw [ih_w0, ih_w1, ih_wm1, ih_w2, ih_winf]
    -- Convert all shifts to arithmetic
    simp only [
      Nat.shiftLeft_one_eq_mul_two,
      Nat.shiftLeft_two_eq_mul_four,
      Int.shiftLeft_one',        -- x <<< (1:ℤ) = x * 2
      Int.shiftLeft_eq_mul_pow,   -- x <<< ↑n = x * ↑(2^n)
      Int.shiftRight_eq_div_pow,  -- x >>> n = x / ↑(2^n)
      Nat.cast_pow, Nat.cast_ofNat, pow_one
    ]
    convert congr_arg ( fun x : ℤ => a_raw.sign * b_raw.sign * x ) ( toom3_identity ( a0 : ℤ ) ( a1 : ℤ ) ( a2 : ℤ ) ( b0 : ℤ ) ( b1 : ℤ ) ( b2 : ℤ ) i ) using 1;
    · simp +decide [ Int.shiftLeft_eq, Int.shiftRight_eq_div_pow ] ; ring;
      grind +suggestions;
    · have h_digit_decomp : (a : ℤ) = a0 + a1 * 2^i + a2 * 2^(i*2) ∧ (b : ℤ) = b0 + b1 * 2^i + b2 * 2^(i*2) := by
        apply And.intro;
        · convert nat_digit_decomp a i using 1;
          congr! 1;
          · congr! 1;
            · exact mod_cast Nat.and_mask_eq_mod _ _;
            · simp +zetaDelta at *;
              norm_num [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ];
          · simp +zetaDelta at *;
            norm_num [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ];
            rw [ Int.shiftRight_eq_div_pow ] ; ring;
            rw [ Int.ediv_ediv ] ; ring;
            lia;
        · convert nat_digit_decomp b i using 1;
          simp +zetaDelta at *;
          congr! 1;
          · congr! 1;
            · convert congr_arg Int.ofNat ( Nat.and_mask_eq_mod _ _ ) using 1;
              grind +qlia;
            · norm_num [ Nat.shiftRight_eq_div_pow ];
              norm_num [ Nat.shiftLeft_eq, Nat.mod_eq_of_lt ];
          · norm_num [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ];
            rw [ Int.shiftRight_eq_div_pow ] ; ring;
            rw [ Int.ediv_ediv ] ; ring;
            norm_cast ; norm_num;
      grind
