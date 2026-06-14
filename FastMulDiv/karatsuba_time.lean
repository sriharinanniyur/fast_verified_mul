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
  let x := x_raw.natAbs
  let y := y_raw.natAbs
  let n := Nat.size (max x y)
  if n ≤ 1 then return x_raw * y_raw
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
  sorry

/-- Upper bound: T(n) = O(n^{log₂ 3}).
    Since log₂ 3 ≈ 1.585 is irrational, the exponent requires `Real.logb`. -/
theorem karatsuba_time_upper :
    ∃ (c : ℝ), c > 0 ∧
    ∀ (x y : ℤ),
      let n : ℝ := Nat.size (max x.natAbs y.natAbs)
      ((karatsuba x y).time : ℝ) ≤ c * n ^ Real.logb 2 3 := by
  sorry

/-- Lower bound witness: there exist inputs of each size achieving Ω(n^{log₂ 3}).
    (The bound does not hold for all inputs — sparse inputs like 2^(n-1)
    can make one recursive call trivial, reducing effective arity to 2.) -/
theorem karatsuba_time_lower_witness :
    ∃ (c : ℝ), c > 0 ∧
    ∀ (n : ℕ), n ≥ 2 →
      ∃ (x y : ℤ), Nat.size (max x.natAbs y.natAbs) = n ∧
        c * (n : ℝ) ^ Real.logb 2 3 ≤ ((karatsuba x y).time : ℝ) := by
  sorry

end Cslib.Algorithms.Lean.TimeM.Algorithms.Karatsuba
