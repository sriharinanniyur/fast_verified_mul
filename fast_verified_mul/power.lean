-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

import Mathlib
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option autoImplicit false


def nat_exp (x : ℚ) (n : ℕ) : ℚ :=
  if n = 0 then 1
  else if x = 0 then 0
  else if Even n then
    nat_exp (x * x) (n / 2)
  else
    x * (nat_exp (x * x) ((n - 1) / 2))
termination_by n
decreasing_by
  · omega
  · omega


def int_exp (x : ℚ) (n : ℤ) : ℚ :=
  if n = 0 then
    1
  else if x = 0 then
    0
  else if n < 0 then
    nat_exp (1 / x) n.natAbs
  else
    nat_exp x n.natAbs


theorem nat_exp_correct (x : ℚ) (n : ℕ) :
    nat_exp x n = x ^ n := by
  induction' n using Nat.strong_induction_on with n ih generalizing x;
  unfold nat_exp;
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ pow_succ', pow_mul ];
  · rcases k with ( _ | k ) <;> simp_all;
  · split_ifs <;> simp_all +decide ;
    exact ih _ ( by linarith ) _


theorem int_exp_correct (x : ℚ) (n : ℤ) :
    int_exp x n = x ^ n := by
  by_cases hx : x = 0;
  · unfold int_exp;
    cases n <;> aesop;
  · cases n <;> simp_all +decide [ int_exp ];
    · split_ifs <;> simp_all +decide [ nat_exp_correct ];
      linarith;
    · rw [ nat_exp_correct, inv_pow ]
