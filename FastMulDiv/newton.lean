import Mathlib

def M : ℝ → ℝ → ℝ
  | x, y => x * y

def newton_raphson_division
    (N D R0 : ℝ)
    (_hD : 0.5 ≤ D ∧ D ≤ 1)
    (_hR0 : |1 - D * R0| ≤ 0.5)
    (n : ℕ)
    : ℝ := Id.run do
  let mut R : ℝ := R0
  for _ in [:n] do
    R := M R (2 - D * R)
  return N * R

-- Pure versions for reasoning
noncomputable def nr_step (D : ℝ) (R : ℝ) : ℝ := R * (2 - D * R)
noncomputable def nr_iter (D : ℝ) (R : ℝ) (n : ℕ) : ℝ := (nr_step D)^[n] R
/-
The monadic function equals the pure iteration
-/
lemma newton_raphson_eq_nr_iter
    (N D R0 : ℝ) (hD : 0.5 ≤ D ∧ D ≤ 1) (hR0 : |1 - D * R0| ≤ 0.5) (n : ℕ) :
    newton_raphson_division N D R0 hD hR0 n = N * nr_iter D R0 n := by
  -- By definition of `newton_raphson_division`, we can unfold it to show that it matches the pure iteration.
  unfold newton_raphson_division nr_iter;
  induction n <;> simp_all +decide [ Function.iterate_succ_apply' ];
  simp_all +decide [ List.range'_concat ];
  unfold nr_step; aesop;
-- Key algebraic identity: error squares each step
lemma nr_error_sq (D R : ℝ) : 1 - D * nr_step D R = (1 - D * R) ^ 2 := by
  unfold nr_step; ring
/-
After n iterations, error is e0^(2^n)
-/
lemma nr_error_iter (D R : ℝ) (n : ℕ) :
    1 - D * nr_iter D R n = (1 - D * R) ^ (2 ^ n) := by
  induction n <;> simp_all +decide [ Function.iterate_succ_apply', pow_succ, pow_mul, nr_iter ];
  rw [ ← ‹1 - D * ( nr_step D ) ^[ _ ] R = ( 1 - D * R ) ^ 2 ^ _› ] ; unfold nr_step ; ring;
/-
Main error bound on the pure iteration
-/
lemma nr_iter_error_bound (N D R0 : ℝ) (hD : 0.5 ≤ D ∧ D ≤ 1)
    (hR0 : |1 - D * R0| ≤ 0.5) (n : ℕ) :
    |N * nr_iter D R0 n - N / D| ≤ |N / D| / 2 ^ (2 ^ n) := by
  -- By nr_error_iter, this equals |N/D| * |(1 - D * R0)^(2^n)| = |N/D| * |1 - D * R0|^(2^n).
  have nr_error_iter : abs ((N * nr_iter D R0 n) - (N / D)) = abs (N / D) * abs ((1 - D * R0) ^ (2 ^ n)) := by
    rw [ ← abs_mul ];
    rw [ ← nr_error_iter ];
    grind +splitImp;
  convert mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( abs_nonneg _ ) hR0 _ ) ( abs_nonneg _ ) using 1 <;> norm_num [ nr_error_iter ] ; ring;
  rw [ mul_comm ];
  ring;
  norm_num

theorem newton_raphson_division_error
    (N D R0 : ℝ)
    (hD : 0.5 ≤ D ∧ D ≤ 1)
    (hR0 : |1 - D * R0| ≤ 0.5)
    (n : ℕ)
    : |newton_raphson_division N D R0 hD hR0 n - N / D| ≤ |N / D| / 2 ^ (2 ^ n) := by
  rw [newton_raphson_eq_nr_iter]
  exact nr_iter_error_bound N D R0 hD hR0 n
