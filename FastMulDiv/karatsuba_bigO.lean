-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

import Mathlib
import Cslib.Algorithms.Lean.TimeM
set_option maxHeartbeats 800000

namespace Cslib.Algorithms.Lean.TimeM.Algorithms.Karatsuba


lemma band_mask_eq_mod (x k : ℕ) : x &&& ((1 <<< k) - 1) = x % 2 ^ k := by
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.and_two_pow_sub_one_eq_mod x k

lemma max_mod_lt_of_size_ge_two (x y : ℕ) (n : ℕ) (hn : n = Nat.size (max x y))
    (hn2 : ¬ n ≤ 1) :
    max (x % 2 ^ (n / 2)) (y % 2 ^ (n / 2)) < max x y := by
  have h_max_ge : 2^(n-1) ≤ Nat.max x y := by
    convert Nat.lt_size.mp ( show n - 1 < ( Nat.max x y ).size from ?_ ) using 1;
    exact hn ▸ Nat.pred_lt ( ne_bot_of_gt ( not_le.mp hn2 ) );
  have h_pow_le : 2^(n/2) ≤ Nat.max x y := by
    exact le_trans ( pow_le_pow_right₀ ( by decide ) ( Nat.div_le_of_le_mul <| by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ n ) ] ) ) h_max_ge;
  exact max_lt ( lt_of_lt_of_le ( Nat.mod_lt _ ( by positivity ) ) h_pow_le ) ( lt_of_lt_of_le ( Nat.mod_lt _ ( by positivity ) ) h_pow_le )


lemma max_div_lt_of_size_ge_two (x y : ℕ) (n : ℕ) (hn : n = Nat.size (max x y))
    (hn2 : ¬ n ≤ 1) :
    max (x / 2 ^ (n / 2)) (y / 2 ^ (n / 2)) < max x y := by
  have h_exp : 2 ^ (n / 2) ≥ 2 := by
    exact le_self_pow ( by decide ) ( Nat.ne_of_gt ( Nat.div_pos ( by linarith ) ( by decide ) ) );
  have h_max_pos : 0 < max x y := by
    contrapose! hn2; aesop;
  exact max_lt ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.le_max_left x y ] ) ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.le_max_right x y ] )


lemma max_sum_lt_of_size_ge_two (x y : ℕ) (n : ℕ) (hn : n = Nat.size (max x y))
    (hn2 : ¬ n ≤ 1) :
    max (x / 2 ^ (n / 2) + x % 2 ^ (n / 2))
        (y / 2 ^ (n / 2) + y % 2 ^ (n / 2)) < max x y := by
  have h_k_ge_1 : 1 ≤ n / 2 := by
    omega;
  have h_case1 : ∀ z, z / 2 ^ (n / 2) ≥ 1 → z / 2 ^ (n / 2) + z % 2 ^ (n / 2) < z := by
    intro z hz; nlinarith [ Nat.mod_add_div z ( 2 ^ ( n / 2 ) ), Nat.mod_lt z ( show 0 < 2 ^ ( n / 2 ) by positivity ), Nat.pow_le_pow_right ( show 1 ≤ 2 by decide ) h_k_ge_1 ] ;
  by_cases hx : x / 2 ^ (n / 2) ≥ 1 <;> by_cases hy : y / 2 ^ (n / 2) ≥ 1 <;> simp_all +decide [ Nat.div_eq_of_lt ];
  · grind;
  · exact Or.inl ( by rw [ Nat.mod_eq_of_lt hy ] ; exact lt_of_lt_of_le hy ( Nat.le_of_not_lt fun h => by have := Nat.div_eq_of_lt h; aesop ) );
  · rw [ Nat.mod_eq_of_lt hx ];
    contrapose! hy;
    rw [ Nat.div_lt_iff_lt_mul <| by positivity ] ; linarith;
  · have := Nat.size_le.2 ( show Max.max x y < 2 ^ ( ( Max.max x y ).size / 2 ) from max_lt hx hy ) ; omega;


-- TIME MODELING:
-- Same philosophy as ToomCook3: we count shifts and linear-time arithmetic
-- operations, tallying the asymptotic cost per line.
-- Additions/subtractions on k-bit operands cost O(k), modeled as `tick k`.
-- Shifts and masks on n-bit operands cost O(n), modeled as `tick n`.

def karatsuba (x_raw y_raw : ℤ) : TimeM ℕ ℤ := do
  let x := x_raw.natAbs; tick 1;
  let y := y_raw.natAbs; tick 1;
  let n := Nat.size (max x y); tick n;
  if n ≤ 1 then
    tick 1
    return x_raw * y_raw
  else
    let k := n >>> 1;           tick 1;
    let mask := (1 <<< k) - 1;  tick k;

    -- Decomposition: shift + mask on n-bit inputs
    let x1 := x >>> k;                    tick n
    let x0 := x &&& mask;                 tick n
    let y1 := y >>> k;                    tick n
    let y0 := y &&& mask;                 tick n

    -- 3 recursive multiplications (ticks propagate via ←)
    let z0 ← karatsuba x0 y0
    let z2 ← karatsuba x1 y1
    let z1 ← karatsuba (x1 + x0) (y1 + y0); tick k; -- two additions of ≈ k-bit operands

    -- each operation in the final line takes place on operands of size at most 2n bits
    tick (2 * n)
    return x_raw.sign * y_raw.sign * ((z2 <<< (k <<< 1)) + ((z1 - z2 - z0) <<< k) + z0)
termination_by (max x_raw.natAbs y_raw.natAbs)
decreasing_by
  all_goals simp only [band_mask_eq_mod, Nat.shiftRight_eq_div_pow, pow_one,
    Int.natAbs_natCast, Int.natAbs_add_of_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
  · exact max_mod_lt_of_size_ge_two _ _ _ rfl ‹_›
  · exact max_div_lt_of_size_ge_two _ _ _ rfl ‹_›
  · exact max_sum_lt_of_size_ge_two _ _ _ rfl ‹_›

lemma karatsuba_algebra_int (x1 x0 y1 y0 k : ℕ) :
    (↑(x1 * y1) : ℤ) * 2 ^ (k + k) +
    ((↑((x1 + x0) * (y1 + y0)) : ℤ) - ↑(x1 * y1) - ↑(x0 * y0)) * 2 ^ k +
    ↑(x0 * y0) =
    ↑((x1 * 2 ^ k + x0) * (y1 * 2 ^ k + y0)) := by
  push_cast; ring
lemma sign_nat_cast_mul_eq (x y : ℕ) (z : ℤ) (h : x = 0 ∨ y = 0 → z = 0) :
    (↑x : ℤ).sign * (↑y : ℤ).sign * z = z := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [h (Or.inl rfl)]
  · rcases eq_or_ne y 0 with rfl | hy
    · simp [h (Or.inr rfl)]
    · simp [Int.sign_natCast_of_ne_zero hx, Int.sign_natCast_of_ne_zero hy]
lemma karatsuba_z2_zero_of_x_zero (x1 y1 k : ℕ) (hx1 : x1 = 0) :
    (↑(x1 * y1) : ℤ) * 2 ^ (k + k) = 0 := by
  simp [hx1]

theorem karatsuba_correct (x y : ℤ) : (karatsuba x y).ret = x * y := by
  induction' n : Nat.max x.natAbs y.natAbs using Nat.strong_induction_on with n ih generalizing x y;
  unfold karatsuba;
  by_cases h : Nat.size ( Max.max x.natAbs y.natAbs ) ≤ 1 <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ];
  split_ifs <;> simp_all +decide [ TimeM.ret_bind, TimeM.ret_tick, TimeM.ret_pure ];
  rw [ ih _ _ _ _ rfl, ih _ _ _ _ rfl, ih _ _ _ _ rfl ];
  · have h_algebra : (x.natAbs / 2 ^ (Nat.size (Max.max x.natAbs y.natAbs) / 2) * 2 ^ (Nat.size (Max.max x.natAbs y.natAbs) / 2) + (x.natAbs &&& 1 <<< (Nat.size (Max.max x.natAbs y.natAbs) / 2) - 1)) * (y.natAbs / 2 ^ (Nat.size (Max.max x.natAbs y.natAbs) / 2) * 2 ^ (Nat.size (Max.max x.natAbs y.natAbs) / 2) + (y.natAbs &&& 1 <<< (Nat.size (Max.max x.natAbs y.natAbs) / 2) - 1)) = x.natAbs * y.natAbs := by
      rw [ band_mask_eq_mod, band_mask_eq_mod ];
      rw [ Nat.div_add_mod', Nat.div_add_mod' ];
    convert congr_arg ( fun z : ℕ => x.sign * y.sign * z ) h_algebra using 1;
    · norm_num [ Int.shiftLeft_eq, Nat.shiftLeft_eq ] ; ring;
      grind;
    · grind;
  · convert max_mod_lt_of_size_ge_two _ _ _ rfl _ using 1;
    rotate_left;
    exact n.symm;
    · aesop;
    · rw [ band_mask_eq_mod, band_mask_eq_mod ];
      lia;
  · convert max_sum_lt_of_size_ge_two _ _ _ rfl _ using 1;
    rotate_left;
    exact n.symm;
    · aesop;
    · rw [ ← band_mask_eq_mod, ← band_mask_eq_mod ];
      grind +locals;
  · convert max_div_lt_of_size_ge_two _ _ _ rfl _ using 1;
    rotate_left;
    exact n.symm;
    · aesop;
    · grind


/-! ### Time upper bound infrastructure -/
open Real in
/-- The exponent `log₂ 3`. -/
noncomputable def kp : ℝ := Real.logb 2 3
/-- The bound function `f(m) = 120 m^p - 160 m`. -/
noncomputable def fb (m : ℕ) : ℝ := 120 * (m : ℝ) ^ kp - 160 * (m : ℝ)
/-- The bound function for the revised cost model, `g(m) = 2 f(m) = 240 m^p - 320 m`. -/
noncomputable def gb (m : ℕ) : ℝ := 2 * fb m
/-- The time cost as a function of the (nonnegative) natural arguments. -/
def ktau (a b : ℕ) : ℕ := (karatsuba (a : ℤ) (b : ℤ)).time
lemma two_rpow_kp : (2 : ℝ) ^ kp = 3 := by
  rw [kp, Real.rpow_logb] <;> norm_num
lemma kp_ge : (3 : ℝ) / 2 ≤ kp := by
  rw [ show kp = Real.logb 2 3 by rfl, Real.le_logb_iff_rpow_le ] <;> norm_num;
  rw [ show ( 2 : ℝ ) ^ ( 3 / 2 : ℝ ) = 2 * Real.sqrt 2 by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]
lemma kp_le : kp ≤ 8 / 5 := by
  have h_kp_le : kp ≤ 8 / 5 := by
    rw [kp, Real.logb_le_iff_le_rpow] <;> norm_num
    rw [ Real.le_rpow_iff_log_le ] <;> norm_num;
    rw [ div_mul_eq_mul_div, le_div_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_le_log ]
  exact h_kp_le
lemma kp_pos : 0 < kp := by
  have := kp_ge; linarith
lemma time_eq_ktau (x y : ℤ) : (karatsuba x y).time = ktau x.natAbs y.natAbs := by
  unfold ktau;
  unfold karatsuba;
  norm_cast;
  simp +decide [ Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod, Nat.add_mod ];
  split_ifs <;> norm_cast
lemma ktau_base (a b : ℕ) (h : Nat.size (max a b) ≤ 1) : ktau a b = 3 + Nat.size (max a b) := by
  unfold ktau;
  unfold karatsuba;
  simp +decide [h];
  omega
lemma ktau_rec (a b : ℕ) (h : ¬ Nat.size (max a b) ≤ 1) :
    ktau a b =
      (3 + 2 * (Nat.size (max a b) / 2) + 7 * Nat.size (max a b))
      + ktau (a % 2 ^ (Nat.size (max a b) / 2)) (b % 2 ^ (Nat.size (max a b) / 2))
      + ktau (a / 2 ^ (Nat.size (max a b) / 2)) (b / 2 ^ (Nat.size (max a b) / 2))
      + ktau (a / 2 ^ (Nat.size (max a b) / 2) + a % 2 ^ (Nat.size (max a b) / 2))
             (b / 2 ^ (Nat.size (max a b) / 2) + b % 2 ^ (Nat.size (max a b) / 2)) := by
  unfold ktau;
  convert congr_arg _ ( karatsuba.eq_def ( a : ℤ ) ( b : ℤ ) ) using 1;
  simp +decide [ *, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq_mul_pow ];
  ring
/-- A fuel-based, structurally recursive version of `ktau`.  Because it recurses
structurally on the fuel argument it reduces in the kernel, so finite base-case
bounds can be discharged by `decide` (without `native_decide`). -/
def ktF : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | (f + 1), a, b =>
    if Nat.size (max a b) ≤ 1 then 3 + Nat.size (max a b)
    else
      (3 + 2 * (Nat.size (max a b) / 2) + 7 * Nat.size (max a b))
      + ktF f (a % 2 ^ (Nat.size (max a b) / 2)) (b % 2 ^ (Nat.size (max a b) / 2))
      + ktF f (a / 2 ^ (Nat.size (max a b) / 2)) (b / 2 ^ (Nat.size (max a b) / 2))
      + ktF f (a / 2 ^ (Nat.size (max a b) / 2) + a % 2 ^ (Nat.size (max a b) / 2))
             (b / 2 ^ (Nat.size (max a b) / 2) + b % 2 ^ (Nat.size (max a b) / 2))
/-- `ktF` agrees with `ktau` once the fuel exceeds `max a b`. -/
lemma ktau_eq_ktF : ∀ (f a b : ℕ), max a b < f → ktau a b = ktF f a b := by
  intro f
  induction f with
  | zero => intro a b h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro a b h
    by_cases hN : Nat.size (max a b) ≤ 1
    · rw [ktau_base a b hN, ktF]; simp [hN]
    · rw [ktau_rec a b hN, ktF]
      have hle : max a b ≤ f := Nat.lt_succ_iff.mp h
      have e1 := ih _ _ (lt_of_lt_of_le (max_mod_lt_of_size_ge_two a b _ rfl hN) hle)
      have e2 := ih _ _ (lt_of_lt_of_le (max_div_lt_of_size_ge_two a b _ rfl hN) hle)
      have e3 := ih _ _ (lt_of_lt_of_le (max_sum_lt_of_size_ge_two a b _ rfl hN) hle)
      simp only [hN, if_false, e1, e2, e3]
lemma size_mod_le (a b k : ℕ) : Nat.size (max (a % 2 ^ k) (b % 2 ^ k)) ≤ k := by
  rw [ Nat.size_le ];
  exact max_lt ( Nat.mod_lt _ ( by positivity ) ) ( Nat.mod_lt _ ( by positivity ) )
lemma size_div_le (a b : ℕ) (n : ℕ) (hn : n = Nat.size (max a b)) :
    Nat.size (max (a / 2 ^ (n / 2)) (b / 2 ^ (n / 2))) ≤ n - n / 2 := by
  rw [ Nat.size_le ];
  -- Since $a$ and $b$ are both less than $2^n$, we have $a / 2^{n/2} < 2^{n - n/2}$ and $b / 2^{n/2} < 2^{n - n/2}$.
  have h_div_lt : a < 2 ^ n ∧ b < 2 ^ n := by
    have h_lt : max a b < 2 ^ n := by
      rw [ hn ] ; exact Nat.lt_size_self _;
    exact ⟨ lt_of_le_of_lt ( le_max_left _ _ ) h_lt, lt_of_le_of_lt ( le_max_right _ _ ) h_lt ⟩;
  exact max_lt ( Nat.div_lt_of_lt_mul <| by rw [ mul_comm, ← pow_add, Nat.sub_add_cancel ( Nat.div_le_self _ _ ) ] ; linarith ) ( Nat.div_lt_of_lt_mul <| by rw [ mul_comm, ← pow_add, Nat.sub_add_cancel ( Nat.div_le_self _ _ ) ] ; linarith )
lemma size_sum_le (a b : ℕ) (n : ℕ) (hn : n = Nat.size (max a b)) (hn2 : 2 ≤ n) :
    Nat.size (max (a / 2 ^ (n / 2) + a % 2 ^ (n / 2)) (b / 2 ^ (n / 2) + b % 2 ^ (n / 2)))
      ≤ n - n / 2 + 1 := by
  rw [ Nat.size_le ];
  -- Since $a$ and $b$ are both less than $2^n$, we have $a / 2^{n/2} < 2^{n - n/2}$ and $b / 2^{n/2} < 2^{n - n/2}$, and $a % 2^{n/2} < 2^{n/2}$ and $b % 2^{n/2} < 2^{n/2}$.
  have h_div_lt : a / 2 ^ (n / 2) < 2 ^ (n - n / 2) ∧ b / 2 ^ (n / 2) < 2 ^ (n - n / 2) := by
    have h_div_lt : a < 2 ^ n ∧ b < 2 ^ n := by
      exact ⟨ lt_of_le_of_lt ( le_max_left _ _ ) ( hn ▸ Nat.lt_size_self _ ), lt_of_le_of_lt ( le_max_right _ _ ) ( hn ▸ Nat.lt_size_self _ ) ⟩;
    exact ⟨ Nat.div_lt_of_lt_mul <| by rw [ mul_comm, ← pow_add, Nat.sub_add_cancel ( Nat.div_le_self _ _ ) ] ; linarith, Nat.div_lt_of_lt_mul <| by rw [ mul_comm, ← pow_add, Nat.sub_add_cancel ( Nat.div_le_self _ _ ) ] ; linarith ⟩
  have h_mod_lt : a % 2 ^ (n / 2) < 2 ^ (n / 2) ∧ b % 2 ^ (n / 2) < 2 ^ (n / 2) := by
    exact ⟨ Nat.mod_lt _ ( by positivity ), Nat.mod_lt _ ( by positivity ) ⟩;
  rw [ pow_succ' ];
  exact max_lt ( by linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( show n / 2 ≤ n - n / 2 from Nat.le_sub_of_add_le ( by linarith [ Nat.div_mul_le_self n 2 ] ) ) ] ) ( by linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( show n / 2 ≤ n - n / 2 from Nat.le_sub_of_add_le ( by linarith [ Nat.div_mul_le_self n 2 ] ) ) ] )
lemma fb_nonneg (m : ℕ) (h : 2 ≤ m) : 0 ≤ fb m := by
  refine' sub_nonneg.mpr _;
  -- Divide both sides by $m$ and simplify.
  suffices h_div : 160 ≤ 120 * (m : ℝ) ^ (kp - 1) by
    convert mul_le_mul_of_nonneg_right h_div ( Nat.cast_nonneg m ) using 1 ; rw [ mul_assoc, ← Real.rpow_add_one ] <;> norm_num ; linarith [ ( by norm_cast : ( 2 :ℝ ) ≤ m ) ] ;
  -- Since $kp - 1 \geq 1/2$, we have $m^{kp - 1} \geq m^{1/2}$.
  have h_exp : (m : ℝ) ^ (kp - 1) ≥ (m : ℝ) ^ (1 / 2 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( by linarith [ show kp ≥ 3 / 2 by exact kp_ge ] );
  exact le_trans ( by rw [ ← Real.sqrt_eq_rpow ] ; nlinarith [ Real.sqrt_nonneg m, Real.sq_sqrt ( Nat.cast_nonneg m ), ( by norm_cast : ( 2 : ℝ ) ≤ m ) ] ) ( mul_le_mul_of_nonneg_left h_exp <| by norm_num )
lemma fb_rpow_step (m : ℕ) (hm : 2 ≤ m) :
    (4 : ℝ) / 3 ≤ ((m : ℝ) + 1) ^ kp - (m : ℝ) ^ kp := by
  rw [ show ( m + 1 : ℝ ) ^ kp = ( m : ℝ ) ^ kp * ( 1 + 1 / ( m : ℝ ) ) ^ kp by rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ), mul_add, mul_one_div_cancel ( by positivity ), mul_one ] ];
  -- By Bernoulli's inequality, we have $(1 + 1/m)^kp \geq 1 + kp \cdot (1/m)$.
  have h_bernoulli : (1 + 1 / (m : ℝ)) ^ kp ≥ 1 + kp * (1 / (m : ℝ)) := by
    have h_bernoulli : ∀ {x : ℝ}, -1 ≤ x → 1 ≤ kp → (1 + x) ^ kp ≥ 1 + kp * x := by
      grind +suggestions;
    exact h_bernoulli ( by linarith [ show ( 0 : ℝ ) ≤ 1 / m by positivity ] ) ( by linarith [ show ( 3 : ℝ ) / 2 ≤ kp by exact kp_ge ] );
  -- We'll use that $kp \geq 3/2$ and $m \geq 2$ to simplify the expression.
  have h_simplify : kp * (m : ℝ) ^ (kp - 1) ≥ 4 / 3 := by
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( show kp - 1 ≥ 1 / 2 by linarith [ show kp ≥ 3 / 2 by exact kp_ge ] ) ) ( by exact le_of_lt ( show 0 < kp by exact Real.logb_pos ( by norm_num ) ( by norm_num ) ) ) ) ; norm_num [ two_rpow_kp ];
    rw [ ← Real.sqrt_eq_rpow ] ; nlinarith [ show ( m : ℝ ) ≥ 2 by norm_cast, Real.sqrt_nonneg m, Real.sq_sqrt ( Nat.cast_nonneg m ), show kp ≥ 3 / 2 by exact kp_ge ];
  rw [ Real.rpow_sub ( by positivity ), Real.rpow_one ] at *;
  ring_nf at *; nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ m ), inv_mul_cancel₀ ( by positivity : ( m : ℝ ) ≠ 0 ), Real.rpow_pos_of_pos ( by positivity : 0 < ( m : ℝ ) ) kp ] ;
lemma fb_step (m : ℕ) (hm : 2 ≤ m) : fb m ≤ fb (m + 1) := by
  have hstep := fb_rpow_step m hm
  unfold fb
  push_cast
  nlinarith [hstep]
lemma fb_mono (m₁ m₂ : ℕ) (h1 : 2 ≤ m₁) (h : m₁ ≤ m₂) : fb m₁ ≤ fb m₂ := by
  induction m₂, h using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact ih.trans (fb_step n (le_trans h1 hn))
lemma fb_two_ge : (30 : ℝ) ≤ fb 2 := by
  unfold fb;
  norm_num [ kp, two_rpow_kp ]
lemma fb_three_ge : (102 : ℝ) ≤ fb 3 := by
  -- By definition of $fb$, we have $fb 3 = 120 * (3 : ℝ) ^ kp - 160 * 3$.
  unfold fb;
  -- We know that $kp = \log_2(3)$, so $2^{kp} = 3$.
  have h_exp : (3 : ℝ) ^ kp ≥ (3 : ℝ) ^ (3 / 2 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le ( by norm_num ) ( show kp ≥ 3 / 2 by exact kp_ge );
  rw [ show ( 3 : ℝ ) ^ ( 3 / 2 : ℝ ) = 3 * Real.sqrt 3 by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] at h_exp ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ]
lemma gb_nonneg (m : ℕ) (h : 2 ≤ m) : 0 ≤ gb m := by
  unfold gb; have := fb_nonneg m h; linarith
lemma gb_mono (m₁ m₂ : ℕ) (h1 : 2 ≤ m₁) (h : m₁ ≤ m₂) : gb m₁ ≤ gb m₂ := by
  unfold gb; have := fb_mono m₁ m₂ h1 h; linarith
lemma ktau_size_bound_aux (a b : ℕ) (n B : ℕ) (h : Nat.size (max a b) = n)
    (hB : 2 ^ n = B) : a < B ∧ b < B := by
  have hm : max a b < B := by
    have := Nat.lt_size_self (max a b); rw [h, hB] at this; exact this
  exact ⟨lt_of_le_of_lt (le_max_left a b) hm, lt_of_le_of_lt (le_max_right a b) hm⟩
-- Finite base-case bounds (sizes 2–5), discharged by `decide` on the kernel-reducible
-- fuel function `ktF` (no `native_decide`).
lemma ktau_size2 (a b : ℕ) (h : Nat.size (max a b) = 2) : ktau a b ≤ 58 := by
  obtain ⟨ha, hb⟩ := ktau_size_bound_aux a b 2 4 h (by norm_num)
  rw [ktau_eq_ktF 4 a b (by omega)]
  exact (by decide :
    ∀ a' < 4, ∀ b' < 4, Nat.size (max a' b') = 2 → ktF 4 a' b' ≤ 58) a ha b hb h
lemma ktau_size3 (a b : ℕ) (h : Nat.size (max a b) = 3) : ktau a b ≤ 179 := by
  obtain ⟨ha, hb⟩ := ktau_size_bound_aux a b 3 8 h (by norm_num)
  rw [ktau_eq_ktF 8 a b (by omega)]
  exact (by decide :
    ∀ a' < 8, ∀ b' < 8, Nat.size (max a' b') = 3 → ktF 8 a' b' ≤ 179) a ha b hb h
lemma ktau_size4 (a b : ℕ) (h : Nat.size (max a b) = 4) : ktau a b ≤ 297 := by
  obtain ⟨ha, hb⟩ := ktau_size_bound_aux a b 4 16 h (by norm_num)
  rw [ktau_eq_ktF 16 a b (by omega)]
  exact (by decide :
    ∀ a' < 16, ∀ b' < 16, Nat.size (max a' b') = 4 → ktF 16 a' b' ≤ 297) a ha b hb h
lemma ktau_size5 (a b : ℕ) (h : Nat.size (max a b) = 5) : ktau a b ≤ 494 := by
  obtain ⟨ha, hb⟩ := ktau_size_bound_aux a b 5 32 h (by norm_num)
  rw [ktau_eq_ktF 32 a b (by omega)]
  exact (by decide :
    ∀ a' < 32, ∀ b' < 32, Nat.size (max a' b') = 5 → ktF 32 a' b' ≤ 494) a ha b hb h
/-
Tangent (convexity) bound: an increment of `x^kp` is at most `kp * d * (x+d)^(kp-1)`.
-/
lemma rpow_incr_le (x d : ℝ) (hx : 1 ≤ x) (hd : 0 ≤ d) :
    (x + d) ^ kp - x ^ kp ≤ kp * d * (x + d) ^ (kp - 1) := by
  have h_bernoulli : 1 + kp * (-d / (x + d)) ≤ (1 - d / (x + d)) ^ kp := by
    convert one_add_mul_self_le_rpow_one_add ( show -1 ≤ -d / ( x + d ) by rw [ le_div_iff₀ ] <;> linarith ) ( show 1 ≤ kp by linarith [ show kp ≥ 3 / 2 by exact kp_ge ] ) using 1 ; ring;
  rw [ one_sub_div ( by linarith ) ] at h_bernoulli ; rw [ Real.div_rpow ( by linarith ) ( by linarith ) ] at h_bernoulli ; rw [ Real.rpow_sub_one ( by linarith ) ] at * ; ring_nf at * ;
  nlinarith [ show 0 < ( x + d ) ^ kp by positivity, mul_inv_cancel_left₀ ( show ( x + d ) ^ kp ≠ 0 by positivity ) ( x ^ kp ), mul_inv_cancel₀ ( show ( x + d ) ≠ 0 by linarith ) ]
/-
Even-`n` core inequality.
-/
lemma fb_core_even (m : ℕ) (hm : 2 ≤ m) :
    120 * (((m : ℝ) + 1) ^ kp - (m : ℝ) ^ kp) ≤ 146 * (m : ℝ) + 159 := by
  -- By Lemma 2, we have $kp * ((m + 1) ^ (kp - 1)) \leq (8 / 5) * ((m + 1) ^ (3 / 5))$.
  have h_lemma2 : kp * ((m + 1 : ℝ) ^ (kp - 1)) ≤ (8 / 5) * ((m + 1 : ℝ) ^ (3 / 5 : ℝ)) := by
    exact mul_le_mul ( show kp ≤ 8 / 5 by exact kp_le ) ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( show kp - 1 ≤ 3 / 5 by linarith [ show kp ≤ 8 / 5 by exact kp_le ] ) ) ( by positivity ) ( by positivity );
  -- By raising both sides to the power of 5, we can eliminate the fractional exponent.
  have h_pow : (192 : ℝ) ^ 5 * ((m + 1 : ℝ) ^ 3) ≤ (146 * m + 159) ^ 5 := by
    nlinarith only [ sq ( ( m : ℝ ) ^ 2 - 1 ), show ( m : ℝ ) ≥ 2 by norm_cast ];
  -- Taking the fifth root of both sides of the inequality.
  have h_root : (192 : ℝ) * ((m + 1 : ℝ) ^ (3 / 5 : ℝ)) ≤ (146 * m + 159) := by
    contrapose! h_pow;
    convert pow_lt_pow_left₀ h_pow ( by positivity ) ( by norm_num : ( 5 : ℕ ) ≠ 0 ) using 1 ; norm_num only [ mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity : 0 ≤ ( m : ℝ ) + 1 ) ];
  have := rpow_incr_le ( m : ℝ ) 1 ( by norm_cast; linarith ) ( by norm_num ) ; norm_num at * ; linarith
/-
Lower tangent bound: an increment of `x^kp` is at least `kp * d * x^(kp-1)`.
-/
lemma rpow_incr_ge (x d : ℝ) (hx : 0 < x) (hd : 0 ≤ d) :
    kp * d * x ^ (kp - 1) ≤ (x + d) ^ kp - x ^ kp := by
  rw [ show ( x + d ) ^ kp = ( x : ℝ ) ^ kp * ( 1 + d / x ) ^ kp by rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ), mul_add, mul_one, mul_div_cancel₀ _ hx.ne' ] ];
  have h_bernoulli : 1 + kp * (d / x) ≤ (1 + d / x) ^ kp := by
    convert one_add_mul_self_le_rpow_one_add ( show -1 ≤ d / x by exact le_trans ( by norm_num ) ( div_nonneg hd hx.le ) ) ( show 1 ≤ kp by exact le_trans ( by norm_num ) kp_ge ) using 1;
  rw [ Real.rpow_sub_one hx.ne' ];
  field_simp at *;
  grind
/-
Odd-`n` core inequality (asymptotic regime `m ≥ 5`).
-/
lemma fb_core_odd (m : ℕ) (hm : 5 ≤ m) :
    120 * ((m : ℝ) ^ kp + ((m : ℝ) + 1) ^ kp + ((m : ℝ) + 2) ^ kp - (2 * (m : ℝ) + 1) ^ kp)
      ≤ 146 * (m : ℝ) + 312 := by
  -- Let $N := 2m + 1$ (real). Identities: $m = (N-1)/2$, $m+1 = (N+1)/2$, $m+2 = (N+3)/2$, and $(c/2)^kp = c^kp/3$ (since $(1/2)^kp = 1/2^kp = 1/3$ via `two_rpow_kp`, `Real.div_rpow`).
  set N : ℝ := 2 * m + 1
  have hN : m = (N - 1) / 2 := by
    ring
  have hN1 : m + 1 = (N + 1) / 2 := by
    ring
  have hN2 : m + 2 = (N + 3) / 2 := by
    grind
  have hN3 : (m : ℝ) ^ kp = ((N - 1) : ℝ) ^ kp / 3 := by
    rw [ hN, Real.div_rpow ] <;> norm_num [ two_rpow_kp ];
    exact le_add_of_nonneg_left ( by positivity )
  have hN4 : (m + 1 : ℝ) ^ kp = ((N + 1) : ℝ) ^ kp / 3 := by
    rw [ hN1, Real.div_rpow ] <;> norm_num [ two_rpow_kp ];
    positivity
  have hN5 : (m + 2 : ℝ) ^ kp = ((N + 3) : ℝ) ^ kp / 3 := by
    rw [ hN2, Real.div_rpow ( by positivity ) ( by positivity ), two_rpow_kp ]
  have hN6 : (2 * m + 1 : ℝ) ^ kp = N ^ kp := by
    rfl;
  -- Increment bounds:
  have h_inc1 : (N - 1 : ℝ) ^ kp - N ^ kp ≤ -kp * (N - 1) ^ (kp - 1) := by
    have := rpow_incr_ge ( N - 1 ) 1 ( by linarith [ show ( m : ℝ ) ≥ 5 by norm_cast ] ) ( by linarith ) ; norm_num at * ; linarith;
  have h_inc2 : (N + 1 : ℝ) ^ kp - N ^ kp ≤ kp * (N + 1) ^ (kp - 1) := by
    have := rpow_incr_le ( N : ℝ ) 1 ( by linarith [ show ( m : ℝ ) ≥ 5 by norm_cast ] ) ( by linarith [ show ( m : ℝ ) ≥ 5 by norm_cast ] ) ; norm_num at * ; linarith;
  have h_inc3 : (N + 3 : ℝ) ^ kp - N ^ kp ≤ 3 * kp * (N + 3) ^ (kp - 1) := by
    convert rpow_incr_le N 3 ( by linarith [ ( by norm_cast : ( 5 :ℝ ) ≤ m ) ] ) ( by linarith ) using 1 ; ring;
  -- Bound the difference $(N+1)^{kp-1} - (N-1)^{kp-1} \leq 6/5$.
  have h_diff : (N + 1 : ℝ) ^ (kp - 1) - (N - 1) ^ (kp - 1) ≤ 6 / 5 := by
    -- By the mean value theorem on $t \mapsto t^{kp-1}$ over $[N-1, N+1]$, there exists $c \in (N-1, N+1)$ such that $(N+1)^{kp-1} - (N-1)^{kp-1} = (kp-1)c^{kp-2} \cdot 2$.
    obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo (N - 1) (N + 1), (N + 1 : ℝ) ^ (kp - 1) - (N - 1) ^ (kp - 1) = (kp - 1) * c ^ (kp - 2) * 2 := by
      have := exists_deriv_eq_slope ( f := fun x => x ^ ( kp - 1 ) ) ( show ( N - 1 : ℝ ) < N + 1 by linarith ) ; norm_num at *;
      obtain ⟨ c, hc₁, hc₂ ⟩ := this ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( m : ℝ ) ≥ 5 by norm_cast ] ) ( by exact fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) <| by linarith [ hx.1, show ( m : ℝ ) ≥ 5 by norm_cast ] ) ; use c; norm_num [ show c ≠ 0 by linarith [ show ( m : ℝ ) ≥ 5 by norm_cast ] ] at *;
      grind;
    -- Since $c \in (N-1, N+1)$ and $kp-2 < 0$, we have $c^{kp-2} \leq (N-1)^{kp-2} \leq 1$.
    have h_c_le_one : c ^ (kp - 2) ≤ 1 := by
      rw [ Real.rpow_le_one_iff_of_pos ] <;> norm_num;
      · exact Or.inl ⟨ by linarith [ hc.1.1, show ( m : ℝ ) ≥ 5 by norm_cast ], by linarith [ show kp ≤ 8 / 5 by exact kp_le ] ⟩;
      · grind;
    nlinarith [ show kp ≤ 8 / 5 by exact kp_le, show 0 ≤ kp - 1 by exact sub_nonneg_of_le ( by linarith [ show kp ≥ 3 / 2 by exact kp_ge ] ) ];
  -- Therefore, $120 * bracket \leq 40 * (6 / 5) * kp + 120 * kp * (N + 3) ^ (kp - 1) \leq 76.8 + 192 * (N + 3) ^ (3 / 5)$.
  have h_bound : 120 * ((N - 1 : ℝ) ^ kp + (N + 1) ^ kp + (N + 3) ^ kp - 3 * N ^ kp) / 3 ≤ 76.8 + 192 * (N + 3) ^ (3 / 5 : ℝ) := by
    have h_bound : kp ≤ 8 / 5 ∧ (N + 3 : ℝ) ^ (kp - 1) ≤ (N + 3 : ℝ) ^ (3 / 5 : ℝ) := by
      exact ⟨ kp_le, Real.rpow_le_rpow_of_exponent_le ( by linarith [ show ( m : ℝ ) ≥ 5 by norm_cast ] ) ( by linarith [ show kp ≤ 8 / 5 by exact kp_le ] ) ⟩;
    nlinarith [ show 0 < kp by exact Real.logb_pos ( by norm_num ) ( by norm_num ), show ( N + 3 : ℝ ) ^ ( kp - 1 ) > 0 by positivity ];
  -- Finally, $192 * (N + 3) ^ (3 / 5) \leq 73 * N + 162$ for $N \geq 11$ (i.e., $m \geq 5$).
  have h_final : 192 * (N + 3) ^ (3 / 5 : ℝ) ≤ 73 * N + 162 := by
    -- Raise both sides to the power of 5 to eliminate the fractional exponent.
    have h_pow : (192 * (N + 3) ^ (3 / 5 : ℝ)) ^ 5 ≤ (73 * N + 162) ^ 5 := by
      rw [ mul_pow, ← Real.rpow_natCast _ 5, ← Real.rpow_natCast _ 5, ← Real.rpow_mul ( by positivity ) ] ; norm_num ; ring_nf;
      nlinarith only [ show ( m : ℝ ) ≥ 5 by norm_cast, pow_pos ( by positivity : 0 < ( m : ℝ ) ) 3, pow_pos ( by positivity : 0 < ( m : ℝ ) ) 4, pow_pos ( by positivity : 0 < ( m : ℝ ) ) 5 ];
    contrapose! h_pow; gcongr;
  grind
/-! ### Tight rational bounds on `kp = log₂ 3` and on small powers `m ^ kp`.
These replace the previous `native_decide` base cases for `n ∈ {7, 9}`: the odd-`n`
core inequality is verified analytically from rational enclosures of `kp` obtained by
comparing integer powers (`decide`/`norm_num` on naturals only). -/
/-- `19/12 ≤ kp` (from `2 ^ 19 ≤ 3 ^ 12`). -/
lemma kp_lo : (19 : ℝ) / 12 ≤ kp := by
  rw [kp, Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
  rw [show (3 : ℝ) = ((3 : ℝ) ^ (12 : ℕ)) ^ ((1 : ℝ) / 12) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
  rw [show ((19 : ℝ) / 12) = (19 : ℝ) * ((1 : ℝ) / 12) by ring, Real.rpow_mul (by norm_num)]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity); norm_num
/-- `kp ≤ 65/41` (from `3 ^ 41 ≤ 2 ^ 65`). -/
lemma kp_hi : kp ≤ (65 : ℝ) / 41 := by
  rw [kp, Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
  rw [show (3 : ℝ) = ((3 : ℝ) ^ (41 : ℕ)) ^ ((1 : ℝ) / 41) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
  rw [show ((65 : ℝ) / 41) = (65 : ℝ) * ((1 : ℝ) / 41) by ring, Real.rpow_mul (by norm_num)]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity); norm_num
lemma seven_kp_ge : (2177 : ℝ) / 100 ≤ (7 : ℝ) ^ kp := by
  refine le_trans ?_ (Real.rpow_le_rpow_of_exponent_le (by norm_num) kp_lo)
  rw [show ((19 : ℝ) / 12) = (19 : ℝ) * ((1 : ℝ) / 12) by ring, Real.rpow_mul (by norm_num)]
  rw [show (2177 : ℝ) / 100 = (((2177 : ℝ) / 100) ^ (12 : ℕ)) ^ ((1 : ℝ) / 12) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity); norm_num
lemma nine_kp_ge : (3242 : ℝ) / 100 ≤ (9 : ℝ) ^ kp := by
  refine le_trans ?_ (Real.rpow_le_rpow_of_exponent_le (by norm_num) kp_lo)
  rw [show ((19 : ℝ) / 12) = (19 : ℝ) * ((1 : ℝ) / 12) by ring, Real.rpow_mul (by norm_num)]
  rw [show (3242 : ℝ) / 100 = (((3242 : ℝ) / 100) ^ (12 : ℕ)) ^ ((1 : ℝ) / 12) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity); norm_num
lemma three_kp_le : (3 : ℝ) ^ kp ≤ (571 : ℝ) / 100 := by
  refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) kp_hi) ?_
  rw [show ((65 : ℝ) / 41) = (65 : ℝ) * ((1 : ℝ) / 41) by ring, Real.rpow_mul (by norm_num)]
  rw [show (571 : ℝ) / 100 = (((571 : ℝ) / 100) ^ (41 : ℕ)) ^ ((1 : ℝ) / 41) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity); norm_num
lemma five_kp_le : (5 : ℝ) ^ kp ≤ (1283 : ℝ) / 100 := by
  refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) kp_hi) ?_
  rw [show ((65 : ℝ) / 41) = (65 : ℝ) * ((1 : ℝ) / 41) by ring, Real.rpow_mul (by norm_num)]
  rw [show (1283 : ℝ) / 100 = (((1283 : ℝ) / 100) ^ (41 : ℕ)) ^ ((1 : ℝ) / 41) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity); norm_num
lemma four_rpow_kp : (4 : ℝ) ^ kp = 9 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num), two_rpow_kp]
  norm_num
lemma six_rpow_kp : (6 : ℝ) ^ kp = 3 * (3 : ℝ) ^ kp := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.mul_rpow (by norm_num) (by norm_num), two_rpow_kp]
/-- Odd core inequality at `n = 7` (the `m = 3` case excluded by `fb_core_odd`). -/
lemma fb_core_7 : (1 + 7 * (7 : ℝ)) + fb 3 + fb 4 + fb 5 ≤ fb 7 := by
  unfold fb; push_cast
  rw [four_rpow_kp]
  nlinarith [seven_kp_ge, three_kp_le, five_kp_le]
/-- Odd core inequality at `n = 9` (the `m = 4` case excluded by `fb_core_odd`). -/
lemma fb_core_9 : (1 + 7 * (9 : ℝ)) + fb 4 + fb 5 + fb 6 ≤ fb 9 := by
  unfold fb; push_cast
  rw [four_rpow_kp, six_rpow_kp]
  nlinarith [nine_kp_ge, three_kp_le, five_kp_le]
/-
The core recurrence inequality (used for `n ≥ 6`).
-/
lemma fb_core (n : ℕ) (h : 6 ≤ n) :
    (1 + 7 * (n : ℝ)) + fb (n / 2) + fb (n - n / 2) + fb (n - n / 2 + 1) ≤ fb n := by
  rcases Nat.even_or_odd' n with ⟨ m, rfl | rfl ⟩;
  · norm_num [ fb ];
    norm_num [ two_mul ];
    rw [ show ( m + m : ℝ ) = 2 * m by ring, Real.mul_rpow ( by positivity ) ( by positivity ), two_rpow_kp ] ; linarith [ fb_core_even m ( by linarith ) ];
  · rcases Nat.lt_or_ge m 5 with hm5 | hm5
    · have hm3 : 3 ≤ m := by omega
      interval_cases m
      · -- n = 7
        norm_num [ Nat.add_div ]
        have h7 := fb_core_7
        norm_num [ fb ] at h7 ⊢
        linarith
      · -- n = 9
        norm_num [ Nat.add_div ]
        have h9 := fb_core_9
        norm_num [ fb ] at h9 ⊢
        linarith
    · norm_num [ Nat.add_div ];
      norm_num [ two_mul, add_assoc ];
      unfold fb;
      have := fb_core_odd m hm5 ; norm_num at * ; ring_nf at * ; linarith
/-
The core recurrence inequality for the revised cost model (`gb = 2 fb`).
The per-call cost is now `3 + 2*(n/2) + 7*n ≤ 3 + 8*n ≤ 2*(1 + 7*n)`.
-/
lemma gb_core (n : ℕ) (h : 6 ≤ n) :
    (3 + 8 * (n : ℝ)) + gb (n / 2) + gb (n - n / 2) + gb (n - n / 2 + 1) ≤ gb n := by
  have hc := fb_core n h
  unfold gb
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  nlinarith [hc, hn1]
/-
Loose lower bound on `fb` from `kp ≥ 3/2`.
-/
lemma fb_ge_pow32 (n : ℕ) (hn : 1 ≤ n) :
    120 * (n : ℝ) ^ ((3 : ℝ) / 2) - 160 * (n : ℝ) ≤ fb n := by
  exact sub_le_sub_right ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_exponent_le ( mod_cast hn ) ( show ( 3:ℝ ) / 2 ≤ kp by linarith [ show kp ≥ 3 / 2 by exact kp_ge ] ) ) <| by positivity ) _
/-
Small-`n` bound (`2 ≤ n ≤ 5`), handled by direct computation on the fuel function `ktF`.
-/
lemma ktau_small (a b : ℕ) (h2 : 2 ≤ Nat.size (max a b)) (h5 : Nat.size (max a b) ≤ 5) :
    (ktau a b : ℝ) ≤ gb (Nat.size (max a b)) := by
  unfold gb
  interval_cases hs : Nat.size (max a b)
  · have hb : (ktau a b : ℝ) ≤ 58 := by exact_mod_cast ktau_size2 a b hs
    nlinarith [fb_two_ge, hb]
  · have hb : (ktau a b : ℝ) ≤ 179 := by exact_mod_cast ktau_size3 a b hs
    nlinarith [fb_three_ge, hb]
  · have hb : (ktau a b : ℝ) ≤ 297 := by exact_mod_cast ktau_size4 a b hs
    have hf : fb 4 = 440 := by unfold fb; push_cast; rw [four_rpow_kp]; norm_num
    nlinarith [hb, hf]
  · have hb : (ktau a b : ℝ) ≤ 494 := by exact_mod_cast ktau_size5 a b hs
    have hf : (520 : ℝ) ≤ fb 5 := by
      unfold fb
      push_cast
      have h5kp : (5 : ℝ) ^ ((3 : ℝ) / 2) ≤ (5 : ℝ) ^ kp :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) kp_ge
      have h532 : (11 : ℝ) ≤ (5 : ℝ) ^ ((3 : ℝ) / 2) := by
        rw [show (5 : ℝ) ^ ((3 : ℝ) / 2) = 5 * Real.sqrt 5 by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add'] <;> norm_num]
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      nlinarith [h5kp, h532]
    nlinarith [hb, hf]
lemma ktau_le_gb (a b : ℕ) (h : 2 ≤ Nat.size (max a b)) :
    (ktau a b : ℝ) ≤ gb (Nat.size (max a b)) := by
  induction' n : Nat.max a b using Nat.strong_induction_on with n ih generalizing a b;
  by_cases hn : Nat.size ( Max.max a b ) ≤ 5;
  · exact ktau_small a b h hn;
  · -- Apply the key sub-bound to each recursive argument.
    have h_sub_bounds : ∀ a' b', max a' b' < max a b → ∀ s, Nat.size (max a' b') ≤ s → 2 ≤ s → (ktau a' b' : ℝ) ≤ gb s := by
      intros a' b' h_max_lt s hs_le hs_ge_two
      by_cases hs : Nat.size (max a' b') ≤ 1;
      · rw [ ktau_base ] <;> try exact hs
        have hsz1 : (Nat.size (max a' b') : ℝ) ≤ 1 := by exact_mod_cast hs
        have : (3 : ℝ) + Nat.size (max a' b') ≤ gb 2 := by
          have := gb_nonneg 2 (by norm_num); unfold gb fb at *; push_cast;
          nlinarith [two_rpow_kp, hsz1]
        push_cast; refine le_trans ?_ (le_trans this (gb_mono 2 s (by norm_num) hs_ge_two));
        linarith [hsz1]
      · exact le_trans ( ih _ ( by aesop ) _ _ ( by linarith ) rfl ) ( gb_mono _ _ ( by linarith ) hs_le );
    rw [ ktau_rec a b ( by omega ) ];
    have h_sub_bounds : (ktau (a % 2 ^ (Nat.size (max a b) / 2)) (b % 2 ^ (Nat.size (max a b) / 2)) : ℝ) ≤ gb (Nat.size (max a b) / 2) ∧ (ktau (a / 2 ^ (Nat.size (max a b) / 2)) (b / 2 ^ (Nat.size (max a b) / 2)) : ℝ) ≤ gb (Nat.size (max a b) - Nat.size (max a b) / 2) ∧ (ktau (a / 2 ^ (Nat.size (max a b) / 2) + a % 2 ^ (Nat.size (max a b) / 2)) (b / 2 ^ (Nat.size (max a b) / 2) + b % 2 ^ (Nat.size (max a b) / 2)) : ℝ) ≤ gb (Nat.size (max a b) - Nat.size (max a b) / 2 + 1) := by
      refine' ⟨ h_sub_bounds _ _ _ _ _ _, h_sub_bounds _ _ _ _ _ _, h_sub_bounds _ _ _ _ _ _ ⟩;
      any_goals omega;
      exact max_mod_lt_of_size_ge_two a b _ rfl ( by omega );
      · exact size_mod_le _ _ _;
      · exact max_div_lt_of_size_ge_two a b _ rfl ( by omega );
      · exact size_div_le _ _ _ rfl;
      · exact max_sum_lt_of_size_ge_two a b _ rfl ( by omega );
      · exact size_sum_le _ _ _ rfl ( by omega );
    obtain ⟨ hb1, hb2, hb3 ⟩ := h_sub_bounds
    have hcore := gb_core ( Nat.size ( Max.max a b ) ) ( by omega )
    have hk : (2 : ℝ) * ((Nat.size (Max.max a b) / 2 : ℕ) : ℝ) ≤ (Nat.size (Max.max a b) : ℝ) := by
      norm_cast; linarith [ Nat.div_mul_le_self ( Nat.size ( Max.max a b ) ) 2 ]
    push_cast
    nlinarith [ hcore, hb1, hb2, hb3, hk ]


theorem karatsuba_time_bigO :
    ∃ (c : ℝ) (n0 : ℕ), c > 0 ∧ n0 > 0 ∧
    ∀ (x y : ℤ),
      let n : ℝ := Nat.size (max x.natAbs y.natAbs)
      (n ≥ n0) → ((karatsuba x y).time : ℝ) ≤ c * n ^ Real.logb 2 3 := by
  refine ⟨240, 2, by norm_num, by norm_num, ?_⟩
  intro x y n hn
  rw [show n = (Nat.size (max x.natAbs y.natAbs) : ℝ) from rfl] at hn ⊢
  rw [ time_eq_ktau ]
  have hsize : 2 ≤ Nat.size ( Max.max x.natAbs y.natAbs ) := by
    have h2 : ((2 : ℕ) : ℝ) ≤ (Nat.size ( Max.max x.natAbs y.natAbs ) : ℝ) := hn
    exact_mod_cast h2
  refine le_trans ( ktau_le_gb _ _ hsize ) ?_
  unfold gb fb
  have hpos : (0 : ℝ) ≤ 160 * (Nat.size ( Max.max x.natAbs y.natAbs ) : ℝ) := by positivity
  rw [ show Real.logb 2 3 = kp from rfl ]
  nlinarith [ hpos ]

end Cslib.Algorithms.Lean.TimeM.Algorithms.Karatsuba
