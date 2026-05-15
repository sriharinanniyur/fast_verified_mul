import Mathlib
set_option maxHeartbeats 800000

def M : ℝ → ℝ → ℝ
  | x, y => x * y

def goldschmidt (N D : ℝ) (_hD : 0.5 ≤ D ∧ D ≤ 1) (n : ℕ) : ℝ := Id.run do
  let mut N' := N
  let mut D' := D
  for _ in [:n] do
    let R := 2 - D'
    N' := M N' R
    D' := M D' R
  return N'

-- aristotle from this point forwards.
-- aristotle specifies a recursive version, proves congruence between the iterative version
-- and the recursive version, and then uses this to verify the precision bound of the iterative
-- version.

/-- Clean recursive version of the Goldschmidt step.
  Returns `(D_n, N_n)` where the state is tracked as an `MProd`. -/
noncomputable def gsStep (N D : ℝ) : ℕ → ℝ × ℝ
  | 0 => (D, N)
  | n + 1 =>
    let (D', N') := gsStep N D n
    (D' * (2 - D'), N' * (2 - D'))
/-- The N-component of gsStep. -/
noncomputable def gsN (N D : ℝ) (n : ℕ) : ℝ := (gsStep N D n).2
/-- The D-component of gsStep. -/
noncomputable def gsD (N D : ℝ) (n : ℕ) : ℝ := (gsStep N D n).1
/-! ## Linking the imperative and recursive definitions -/
/-- `forIn` on a list in the `Id` monad with a function that always yields
    is the same as `List.foldl`. -/
lemma forIn_list_yield_eq_foldl {α β : Type} (l : List α) (init : β)
    (f : α → β → β) :
    (forIn (m := Id) l init (fun a b => ForInStep.yield (f a b))) =
      l.foldl (fun b a => f a b) init := by
  induction l generalizing init with
  | nil => simp [List.forIn_nil, pure, Pure.pure]
  | cons hd tl ih =>
    simp [List.forIn_cons, ih, List.foldl_cons, bind, Bind.bind]
/-
`forIn` on `[:n]` in `Id` equals `forIn` on `List.range n`.
-/
lemma forIn_range_eq_list {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    forIn (m := Id) [:n] init f = forIn (m := Id) (List.range n) init f := by
  induction' n with n ih generalizing init <;> simp_all +decide [ List.range_succ ];
  -- By definition of `List.range'`, we have `List.range' 0 (n + 1) = List.range' 0 n ++ [n]`.
  have h_range' : List.range' 0 (n + 1) = List.range' 0 n ++ [n] := by
    exact Nat.recOn n ( by simp +decide ) fun n ih => by simp_all +decide [ List.range'_concat ] ;
  convert congr_arg ( fun l => forIn l init f ) h_range' using 1;
  congr! 2;
  exact?
/-
Goldschmidt equals the second component of gsStep.
-/
theorem goldschmidt_eq_gsN (N D : ℝ) (hD : 0.5 ≤ D ∧ D ≤ 1) (n : ℕ) :
    goldschmidt N D hD n = gsN N D n := by
  unfold goldschmidt gsN;
  induction n <;> simp_all +decide [ List.range_succ ];
  · rfl;
  · simp_all +decide [ List.range'_concat ];
    congr;
    rename_i k hk;
    simp [M]
    exact Nat.recOn k rfl fun n ih => by rw [ List.range'_concat ] ; simp +decide [ ih, gsStep ] ;
/-! ## Mathematical properties of gsStep -/
/-
gsD does not depend on N.
-/
lemma gsD_independent_of_N (N₁ N₂ D : ℝ) (n : ℕ) :
    gsD N₁ D n = gsD N₂ D n := by
  unfold gsD;
  induction' n with n ih generalizing N₁ N₂ <;> simp +decide [ *, gsStep ];
  rw [ ih N₁ N₂ ]
/-
Error term: `1 - gsD`. We show it satisfies `e_{n+1} = e_n^2`.
-/
lemma gsD_error_sq (N D : ℝ) (n : ℕ) :
    1 - gsD N D (n + 1) = (1 - gsD N D n) ^ 2 := by
  rw [ show gsD N D ( n + 1 ) = gsD N D n * ( 2 - gsD N D n ) by
        exact? ] ; ring
/-
The error term after n steps is `(1 - D) ^ (2^n)`.
-/
lemma gsD_error_pow (N D : ℝ) (n : ℕ) :
    1 - gsD N D n = (1 - D) ^ (2 ^ n) := by
  induction' n with n ih;
  · aesop;
  · rw [ pow_succ, pow_mul, ← ih, gsD_error_sq ]
/-
gsD is nonzero when D ∈ [0.5, 1].
-/
lemma gsD_pos (N D : ℝ) (hD : 0.5 ≤ D ∧ D ≤ 1) (n : ℕ) :
    0 < gsD N D n := by
  -- By induction on n, we can show that gsD N D n is positive.
  have h_pos : ∀ n, 0 < gsD N D n ∧ gsD N D n ≤ 1 := by
    intro n;
    induction' n with n ih;
    · exact ⟨ by erw [ show gsD N D 0 = D by rfl ] ; norm_num at *; linarith, by erw [ show gsD N D 0 = D by rfl ] ; norm_num at *; linarith ⟩;
    · exact ⟨ by rw [ show gsD N D ( n + 1 ) = gsD N D n * ( 2 - gsD N D n ) by exact? ] ; nlinarith, by rw [ show gsD N D ( n + 1 ) = gsD N D n * ( 2 - gsD N D n ) by exact? ] ; nlinarith ⟩;
  exact h_pos n |>.1
/-
The N-component equals N/D * gsD.
-/
lemma gsN_eq (N D : ℝ) (hD : D ≠ 0) (n : ℕ) :
    gsN N D n = (N / D) * gsD N D n := by
  induction' n with n ih generalizing N D;
  · exact?;
  · -- By definition of `gsN` and `gsD`, we have:
    have h_step : gsN N D (n + 1) = gsN N D n * (2 - gsD N D n) ∧ gsD N D (n + 1) = gsD N D n * (2 - gsD N D n) := by
      exact?;
    rw [ h_step.1, h_step.2, ih N D hD ] ; ring
/-
The error of gsN is |N/D| * |1 - gsD|.
-/
lemma gsN_error (N D : ℝ) (hD : D ≠ 0) (n : ℕ) :
    gsN N D n - N / D = -(N / D) * (1 - gsD N D n) := by
  rw [ gsN_eq N D hD ] ; ring


/-
After `n` iterations, the relative error is at most `2^(−2ⁿ)`.
-/
theorem goldschmidt_error (N D : ℝ) (hD : 0.5 ≤ D ∧ D ≤ 1) (n : ℕ) :
    |goldschmidt N D hD n - N / D| ≤ |N / D| / 2 ^ (2 ^ n) := by
  rw [ goldschmidt_eq_gsN N D hD n ];
  -- By Lemma 2, we have |gsN N D n - N / D| = |N / D| * |1 - gsD N D n|.
  have h_error : abs (gsN N D n - N / D) = abs (N / D) * abs (1 - gsD N D n) := by
    rw [ ← abs_mul, gsN_error ];
    · norm_num [ abs_mul ];
    · linarith;
  -- By Lemma 3, we have |1 - gsD N D n| = (1 - D) ^ (2 ^ n).
  have h_error_pow : abs (1 - gsD N D n) = (1 - D) ^ (2 ^ n) := by
    rw [ gsD_error_pow, abs_of_nonneg ( pow_nonneg ( by linarith ) _ ) ];
  rw [ h_error, h_error_pow ];
  exact mul_le_mul_of_nonneg_left ( by simpa using pow_le_pow_left₀ ( by linarith ) ( show 1 - D ≤ 1 / 2 by linarith ) _ ) ( abs_nonneg _ )
