-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

import Mathlib
set_option maxHeartbeats 800000


lemma band_mask_eq_mod (x k : ℕ) : x &&& ((1 <<< k) - 1) = x % 2 ^ k := by
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.and_two_pow_sub_one_eq_mod x k

lemma max_mod_lt_of_size_ge_two (x y : ℕ) (n : ℕ) (hn : n = Nat.size (max x y))
    (hn2 : ¬ n ≤ 1) :
    max (x % 2 ^ (n / 2)) (y % 2 ^ (n / 2)) < max x y := by
  have h_max_ge : 2^(n-1) ≤ Nat.max x y := by
    convert Nat.lt_size.mp ( show n - 1 < ( Nat.max x y ).size from ?_ ) using 1;
    exact hn ▸ Nat.pred_lt ( ne_bot_of_gt ( not_le.mp hn2 ) );
  -- Since $n/2 \leq n-1$, we have $2^(n/2) \leq 2^(n-1) \leq max x y$.
  have h_pow_le : 2^(n/2) ≤ Nat.max x y := by
    exact le_trans ( pow_le_pow_right₀ ( by decide ) ( Nat.div_le_of_le_mul <| by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ n ) ] ) ) h_max_ge;
  exact max_lt ( lt_of_lt_of_le ( Nat.mod_lt _ ( by positivity ) ) h_pow_le ) ( lt_of_lt_of_le ( Nat.mod_lt _ ( by positivity ) ) h_pow_le )


lemma max_div_lt_of_size_ge_two (x y : ℕ) (n : ℕ) (hn : n = Nat.size (max x y))
    (hn2 : ¬ n ≤ 1) :
    max (x / 2 ^ (n / 2)) (y / 2 ^ (n / 2)) < max x y := by
  -- Since $n \geq 2$, we have $2^{n/2} \geq 2$.
  have h_exp : 2 ^ (n / 2) ≥ 2 := by
    exact le_self_pow ( by decide ) ( Nat.ne_of_gt ( Nat.div_pos ( by linarith ) ( by decide ) ) );
  -- Since $max x y \geq 2^{n-1}$, we have $max x y > 0$.
  have h_max_pos : 0 < max x y := by
    contrapose! hn2; aesop;
  exact max_lt ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.le_max_left x y ] ) ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.le_max_right x y ] )


lemma max_sum_lt_of_size_ge_two (x y : ℕ) (n : ℕ) (hn : n = Nat.size (max x y))
    (hn2 : ¬ n ≤ 1) :
    max (x / 2 ^ (n / 2) + x % 2 ^ (n / 2))
        (y / 2 ^ (n / 2) + y % 2 ^ (n / 2)) < max x y := by
  -- Consider the case when $2^k \geq 2$. Here, $k \geq 1$.
  have h_k_ge_1 : 1 ≤ n / 2 := by
    omega;
  -- For any z, z / 2^k + z % 2^k ≤ z when z / 2^k ≥ 1.
  have h_case1 : ∀ z, z / 2 ^ (n / 2) ≥ 1 → z / 2 ^ (n / 2) + z % 2 ^ (n / 2) < z := by
    intro z hz; nlinarith [ Nat.mod_add_div z ( 2 ^ ( n / 2 ) ), Nat.mod_lt z ( show 0 < 2 ^ ( n / 2 ) by positivity ), Nat.pow_le_pow_right ( show 1 ≤ 2 by decide ) h_k_ge_1 ] ;
  by_cases hx : x / 2 ^ (n / 2) ≥ 1 <;> by_cases hy : y / 2 ^ (n / 2) ≥ 1 <;> simp_all +decide [ Nat.div_eq_of_lt ];
  · grind;
  · exact Or.inl ( by rw [ Nat.mod_eq_of_lt hy ] ; exact lt_of_lt_of_le hy ( Nat.le_of_not_lt fun h => by have := Nat.div_eq_of_lt h; aesop ) );
  · rw [ Nat.mod_eq_of_lt hx ];
    contrapose! hy;
    rw [ Nat.div_lt_iff_lt_mul <| by positivity ] ; linarith;
  · have := Nat.size_le.2 ( show Max.max x y < 2 ^ ( ( Max.max x y ).size / 2 ) from max_lt hx hy ) ; omega;


def karatsuba (x_raw y_raw : ℤ) : ℤ :=
  let x := x_raw.natAbs
  let y := y_raw.natAbs
  let n := Nat.size (max x y)
  if n ≤ 1 then x_raw * y_raw
  else
    let k := n >>> 1
    let mask := (1 <<< k) - 1
    let x1 := x >>> k
    let x0 := x &&& mask
    let y1 := y >>> k
    let y0 := y &&& mask
    let z0 := karatsuba x0 y0
    let z2 := karatsuba x1 y1
    let z1 := karatsuba (x1 + x0) (y1 + y0)
    x_raw.sign * y_raw.sign * ((z2 <<< (k <<< 1)) + ((z1 - z2 - z0) <<< k) + z0)
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

theorem karatsuba_correct (x y : ℤ) : karatsuba x y = x * y := by
  -- By definition of `karatsuba`, we know that
  have h_karatsuba_def : ∀ (x y : ℤ), karatsuba x y = x.natAbs * y.natAbs * (x.sign * y.sign) := by
    intros x y
    induction' n : Nat.max x.natAbs y.natAbs using Nat.strong_induction_on with n ih generalizing x y;
    unfold karatsuba;
    by_cases hn : Nat.size (Nat.max x.natAbs y.natAbs) ≤ 1;
    · grind;
    · -- By the induction hypothesis, we know that the recursive calls return the correct products.
      have h_ind : karatsuba (x.natAbs >>> (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) (y.natAbs >>> (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) = (x.natAbs >>> (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) * (y.natAbs >>> (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) ∧
                   karatsuba (x.natAbs % 2 ^ (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) (y.natAbs % 2 ^ (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) = (x.natAbs % 2 ^ (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) * (y.natAbs % 2 ^ (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) ∧
                   karatsuba ((x.natAbs >>> (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) + (x.natAbs % 2 ^ (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1))) ((y.natAbs >>> (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) + (y.natAbs % 2 ^ (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1))) = ((x.natAbs >>> (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) + (x.natAbs % 2 ^ (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1))) * ((y.natAbs >>> (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1)) + (y.natAbs % 2 ^ (Nat.size (Nat.max x.natAbs y.natAbs) >>> 1))) := by
                     refine' ⟨ _, _, _ ⟩;
                     · convert ih _ _ _ _ rfl using 1;
                       · grind;
                       · convert max_div_lt_of_size_ge_two _ _ _ rfl hn using 1;
                         · norm_num [ Nat.shiftRight_eq_div_pow ];
                           norm_num [ ← Int.ofNat_inj, Int.natAbs_ediv ];
                         · exact n.symm;
                     · convert ih _ _ _ _ rfl using 1;
                       · grind +qlia;
                       · convert max_mod_lt_of_size_ge_two _ _ _ rfl hn using 1;
                         exact n.symm;
                     · convert ih _ _ _ _ rfl using 1;
                       · grind;
                       · convert max_sum_lt_of_size_ge_two _ _ _ rfl hn using 1;
                         · norm_cast;
                           norm_num [ Nat.shiftRight_eq_div_pow ];
                         · exact n.symm;
      simp_all +decide [ Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq_mul_pow ];
      rw [ if_neg ( not_le_of_gt hn ) ] ; norm_num [ Int.shiftLeft_eq ] ; ring;
      rw [ ← Int.emod_add_mul_ediv |x| ( 2 ^ ( _ / 2 ) ), ← Int.emod_add_mul_ediv |y| ( 2 ^ ( _ / 2 ) ) ] ; ring;
      norm_num [ Int.add_mul_ediv_right ] ; ring;
      rw [ Int.ediv_eq_zero_of_lt, Int.ediv_eq_zero_of_lt ] <;> norm_num;
      · exact Int.emod_nonneg _ ( by positivity );
      · exact Int.emod_lt_of_pos _ ( by positivity );
      · exact Int.emod_nonneg _ ( by positivity );
      · exact Int.emod_lt_of_pos _ ( by positivity );
  grind +extAll
