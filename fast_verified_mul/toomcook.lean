-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

import Mathlib


set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise


--- GENERAL UTILITY FUNCTIONS AND LEMMAS
def digits (b : ℕ) (x : ℤ) : ℕ :=
  (b.digits (Int.natAbs x)).length

def eval_vec_as_poly {K : ℕ} (split : Vector ℕ K) (x : ℤ) : ℤ :=
  ∑ i : Fin K, (split.get i : ℤ) * x ^ (i.1)

def eval_vec_as_poly_Q {K : ℕ} (split : Vector ℚ K) (x : ℚ) : ℚ :=
  ∑ i : Fin K, (split.get i : ℚ) * x ^ (i.1)

-- aristotle
lemma digits_mul_ub (a b : ℕ) (BASE : Nat) (hBASE : BASE > 1) :
  (Nat.digits BASE (a*b)).length ≤ (Nat.digits BASE a).length + (Nat.digits BASE b).length := by
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all [Int.natAbs_mul]
    rw [ Nat.length_digits, Nat.length_digits, Nat.length_digits ] <;> try positivity
    · refine' Nat.log_lt_of_lt_pow _ _
      · positivity
      · rw [ pow_add ]
        exact mul_lt_mul'' ( Nat.lt_pow_succ_log_self hBASE _ ) ( Nat.lt_pow_succ_log_self hBASE _ ) ( by positivity ) ( by positivity )
    · linarith
    · linarith
    · linarith

lemma digits_abs (BASE : ℕ) (x : ℤ) : digits BASE (abs x) = digits BASE x := by
  simp [digits, Int.natAbs_abs]

---------------------------------------------------------------------
-- SHARED VARIABLES AND CONSTRAINTS
---------------------------------------------------------------------
def toomcook_P (BASE : ℕ) (a b : ℤ) : ℕ :=
  (digits BASE (max a.natAbs b.natAbs))

def toomcook_i (KA KB BASE : ℕ) (a b : ℤ) : ℕ :=
  (max
    (((digits BASE a) + KA - 1) / KA) -- ceiling-division trick
    (((digits BASE b) + KB - 1) / KB))

def toomcook_B (KA KB BASE : ℕ) (a b : ℤ) : ℕ :=
  BASE ^ (toomcook_i KA KB BASE a b)

def toomcook_split (KA KB KZ BASE : ℕ) (a b : ℕ) (z : ℕ) : Vector ℕ KZ :=
  Vector.ofFn (fun i : Fin KZ =>
    (z / (toomcook_B KA KB BASE a b) ^ i.1) % (toomcook_B KA KB BASE a b))

-- sanity check
#eval (toomcook_split 3 3 3 10 123 456 456)
#eval (eval_vec_as_poly (toomcook_split 3 3 3 10 123 456 456) 1500) -- 9007506

-- aristotle
-- prove that a vector with (KA + KB - 1) elements is nonempty given KA > 1 ∧ KB > 1
lemma points_maximum_isSome
  (KA KB : ℕ)
  (POINTS : Vector ℤ (KA + KB - 1))
  (hk : 1 < KA ∧ 1 < KB) :
  (POINTS.toList.maximum).isSome := by
  -- Since the list is non-empty, the maximum must exist.
  have h_nonempty : POINTS.toList ≠ [] := by
    -- Since KA and KB are both greater than 1, their sum minus 1 is at least 2. Therefore, the list can't be empty.
    have h_len_pos : 0 < KA + KB - 1 := by
      omega;
    -- Since the length of POINTS is positive, the list POINTS.toList must also be non-empty.
    have h_nonempty : POINTS.toList.length > 0 := by
      simpa using h_len_pos;
    exact List.ne_nil_of_length_pos h_nonempty;
  -- Since the list is non-empty, we can apply the lemma that states the maximum of a non-empty list is some value.
  have h_max_some : ∀ {l : List ℤ}, l ≠ [] → Option.isSome l.maximum := by
    intros l hl_nonempty
    induction' l with hd tl ih;
    · contradiction;
    · by_cases h : tl = [] <;> simp_all +decide [ List.maximum_cons ];
      · exact rfl
      · cases h' : tl.maximum <;> aesop;
  exact h_max_some h_nonempty

-- deriving the convergence point and the C constant
def toomcook_vmax
  (KA KB : ℕ) (POINTS : Vector ℤ (KA+KB-1)) : ℕ :=
  POINTS.toList.foldl (fun acc z => max acc z.natAbs) 0

def toomcook_CA
  (BASE KA KB : ℕ)
  (POINTS : Vector ℤ (KA+KB-1))
: ℕ :=
  let v_max := toomcook_vmax KA KB POINTS
  digits BASE ((∑ i ∈ Finset.range KA, v_max ^ i) : ℤ)

def toomcook_CB
  (BASE KA KB : ℕ)
  (POINTS : Vector ℤ (KA+KB-1))
: ℕ :=
  let v_max := toomcook_vmax KA KB POINTS
  digits BASE ((∑ i ∈ Finset.range KB, v_max ^ i) : ℤ)

-- upper bound on constant factor in recurrence
def toomcook_C
  (BASE KA KB : ℕ)
  (POINTS : Vector ℤ (KA+KB-1))
: ℕ :=
  (max (toomcook_CA BASE KA KB POINTS) (toomcook_CB BASE KA KB POINTS)) + 1

-- upper bound on subproblem size
def toomcook_P_PRIME_UB
  (BASE KA KB : ℕ)
  (a b : ℕ)
  (POINTS : Vector ℤ (KA+KB-1))
: ℕ :=
  ((toomcook_P BASE a b) / (min KA KB)) + (toomcook_C BASE KA KB POINTS)

-- upper bound on asymptotic problem size convergence point
def toomcook_THETA
  (BASE KA KB : ℕ)
  (POINTS : Vector ℤ (KA+KB-1))
: ℚ :=
  let C := ((toomcook_C BASE KA KB POINTS) : ℚ)
  let K_MIN := ((min KA KB) : ℚ)
  (C * K_MIN) / (K_MIN - (1 : ℚ))

-------------------------------------------------------------
-- PROGRESSION FOR TERMINATION PROOF
-------------------------------------------------------------
-- all aristotle except where specified

theorem toomcook_B_correct (KA KB BASE : ℕ) (a b : ℤ)
    (hBASE : BASE > 1) (hKA : KA > 0) (hKB : KB > 0) :
    digits (toomcook_B KA KB BASE a b) a ≤ KA ∧ digits (toomcook_B KA KB BASE a b) b ≤ KB := by
  -- By definition of $toomcook_B$, we know that $toomcook_B^{KA} > |a|$ and $toomcook_B^{KB} > |b|$.
  have h_bound_a : (toomcook_B KA KB BASE a b) ^ KA > a.natAbs := by
    -- By definition of $toomcook_B$, we know that $toomcook_B^{KA} > |a|$.
    have h_bound_a : (BASE ^ (toomcook_i KA KB BASE a b)) ^ KA > a.natAbs := by
      have h_digits_a : (BASE ^ (toomcook_i KA KB BASE a b)) ^ KA ≥ BASE ^ (digits BASE a.natAbs) := by
        -- By definition of $toomcook_i$, we know that $toomcook_i \geq \frac{digits(BASE, a.natAbs) + KA - 1}{KA}$.
        have h_toomcook_i_ge : toomcook_i KA KB BASE a b * KA ≥ digits BASE a.natAbs := by
          exact Nat.le_of_lt_succ <| by nlinarith! [ Nat.div_add_mod ( digits BASE a.natAbs + KA - 1 ) KA, Nat.mod_lt ( digits BASE a.natAbs + KA - 1 ) hKA, Nat.sub_add_cancel ( show 1 ≤ digits BASE a.natAbs + KA from Nat.succ_le_of_lt <| add_pos_of_nonneg_of_pos ( Nat.zero_le _ ) hKA ), show toomcook_i KA KB BASE a b ≥ ( digits BASE a.natAbs + KA - 1 ) / KA from le_max_left _ _ ] ;
        generalize_proofs at *; (
        rw [ ← pow_mul ] ; exact pow_le_pow_right₀ hBASE.le h_toomcook_i_ge;)
      have h_digits_a : digits BASE a.natAbs = (Nat.digits BASE a.natAbs).length := by
        exact?
      generalize_proofs at *; (
      by_cases ha : a.natAbs = 0 <;> simp_all +decide [ Nat.length_digits ];
      · positivity;
      · exact lt_of_lt_of_le ( Nat.lt_pow_succ_log_self hBASE _ ) ‹_›)
    generalize_proofs at *; (
    exact h_bound_a)
  have h_bound_b : (toomcook_B KA KB BASE a b) ^ KB > b.natAbs := by
    -- By definition of $toomcook_i$, we know that $BASE^{toomcook_i} \geq BASE^{(digits BASE b + KB - 1) / KB}$.
    have h_bound_b : (toomcook_B KA KB BASE a b) ^ KB ≥ BASE ^ ((digits BASE b + KB - 1) / KB * KB) := by
      -- By definition of $toomcook_i$, we know that $toomcook_i \geq ((digits BASE b + KB - 1) / KB)$.
      have h_tki_ge : toomcook_i KA KB BASE a b ≥ ((digits BASE b + KB - 1) / KB) := by
        exact le_max_right _ _
      generalize_proofs at *; (
      exact le_trans ( by rw [ pow_mul ] ) ( Nat.pow_le_pow_left ( pow_le_pow_right₀ hBASE.le h_tki_ge ) _ ))
    generalize_proofs at *; (
    refine' lt_of_lt_of_le _ h_bound_b
    generalize_proofs at *; (
    -- By definition of `digits`, we know that `b.natAbs < BASE^(digits BASE b)`.
    have h_digits_b : b.natAbs < BASE^(digits BASE b) := by
      by_cases hb : b = 0 <;> simp_all +decide [ digits ];
      exact Nat.lt_base_pow_length_digits hBASE;
    generalize_proofs at *; (
    exact h_digits_b.trans_le ( pow_le_pow_right₀ hBASE.le <| by nlinarith [ Nat.div_add_mod ( digits BASE b + KB - 1 ) KB, Nat.mod_lt ( digits BASE b + KB - 1 ) hKB, Nat.sub_add_cancel ( show 1 ≤ digits BASE b + KB from by linarith ), Nat.div_add_mod ( digits BASE b ) KB, Nat.mod_lt ( digits BASE b ) hKB ] ) ;)))
  generalize_proofs at *; (
  -- Applying the bound on the number of digits, we get the desired result.
  have h_digits_bound : ∀ {n : ℕ} {b : ℕ}, b > 1 → n > 0 → (Nat.digits b n).length ≤ Nat.log b n + 1 := by
    intro n b hb hn; rw [ Nat.length_digits ] <;> aesop;
  generalize_proofs at *; (
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide [ digits ];
  · exact le_trans ( h_digits_bound ( show 1 < toomcook_B KA KB BASE 0 b from lt_of_le_of_ne ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by aesop ) ) ) ( Ne.symm <| by aesop ) ) ( Nat.pos_of_ne_zero <| by aesop ) ) ( Nat.log_lt_of_lt_pow ( by aesop ) h_bound_b ) |> le_trans <| by norm_num;
  · refine' le_trans ( h_digits_bound _ _ ) _ <;> norm_num [ hBASE, hKA, hKB, ha, hb ];
    · contrapose! h_bound_a; interval_cases _ : toomcook_B KA KB BASE a 0 <;> simp_all +decide ;
      exact Int.natAbs_pos.mpr ha;
    · exact Nat.log_lt_of_lt_pow ( by positivity ) h_bound_a;
  · refine' ⟨ le_trans ( h_digits_bound _ _ ) _, le_trans ( h_digits_bound _ _ ) _ ⟩ <;> norm_num [ ha, hb ];
    · contrapose! h_bound_a; interval_cases _ : toomcook_B KA KB BASE a b <;> simp_all +decide ;
    · exact Nat.log_lt_of_lt_pow ( by positivity ) h_bound_a |> Nat.lt_of_lt_of_le <| by norm_num;
    · contrapose! h_bound_a; interval_cases _ : toomcook_B KA KB BASE a b <;> simp_all +decide ;
    · exact Nat.log_lt_of_lt_pow ( by positivity ) h_bound_b |> Nat.lt_of_lt_of_le <| by norm_num;))

lemma piece_i_bound (KA KB KZ BASE : ℕ) (h_base : 1 < BASE) (a b z : ℕ)
: ∀ e ∈ (toomcook_split KA KB KZ BASE a b z), (digits BASE e) ≤ toomcook_i KA KB BASE a b := by
  intros e he
  have h_lt : e < toomcook_B KA KB BASE a b := by
    revert e he;
    unfold toomcook_split;
    simp +zetaDelta at *;
    intro a; exact Nat.mod_lt _ (by
    exact pow_pos ( by positivity ) _);
  unfold digits;
  by_cases he_zero : e = 0 <;> simp_all +decide [ Nat.length_digits ];
  refine' Nat.log_lt_of_lt_pow _ _;
  · assumption;
  · exact h_lt

lemma toomcook_i_le (KA KB BASE : ℕ) (a b : ℤ) (hk : 1 < KA ∧ 1 < KB) :
  toomcook_i KA KB BASE a b ≤ (toomcook_P BASE a b) / (min KA KB) + 1 := by
  refine' max_le _ _;
  · have h_digits_le : digits BASE a ≤ toomcook_P BASE a b := by
      unfold toomcook_P;
      unfold digits;
      cases max_choice ( Int.natAbs a ) ( Int.natAbs b ) <;> simp_all +decide [ Int.natAbs_abs ];
      · cases max_cases |a| |b| <;> simp_all +decide [ Int.natAbs_abs ];
        cases abs_cases a <;> cases abs_cases b <;> linarith [ abs_le.mp ( by linarith : |a| ≤ |b| ) ];
      · cases max_choice |a| |b| <;> simp_all +decide [ Int.natAbs_abs ];
        exact?;
    rw [ Nat.div_le_iff_le_mul_add_pred ] <;> norm_num [ hk ];
    · cases min_cases KA KB <;> nlinarith [ Nat.div_add_mod ( toomcook_P BASE a b ) ( Min.min KA KB ), Nat.mod_lt ( toomcook_P BASE a b ) ( by linarith : 0 < Min.min KA KB ), Nat.sub_add_cancel ( by linarith : 1 ≤ KA ) ];
    · grind;
  · -- Since `digits BASE b ≤ bits("digits BASE (max |a| |b|))`, we know `digits BASE b ≤ toomcook_P BASE a b`.
    have h_digits_le_toomcook_P : digits BASE b ≤ toomcook_P BASE a b := by
      unfold toomcook_P; cases max_cases a.natAbs b.natAbs <;> simp_all +decide ;
      · cases max_cases |a| |b| <;> simp_all +decide [ abs_of_nonneg, digits ];
        · cases abs_cases a <;> cases abs_cases b <;> simp_all +decide [ Int.natAbs_abs ];
          · exact?;
          · exact?;
          · exact?;
          · exact?;
        · cases abs_cases a <;> cases abs_cases b <;> omega;
      · cases max_cases |a| |b| <;> simp_all +decide [ digits ];
        · cases abs_cases a <;> cases abs_cases b <;> linarith [ abs_of_nonneg ( by linarith : 0 ≤ a ), abs_of_nonneg ( by linarith : 0 ≤ b ) ];
        · cases abs_cases b <;> simp +decide [ * ];
    rw [ Nat.div_le_iff_le_mul_add_pred ];
    · cases min_cases KA KB <;> nlinarith [ Nat.div_add_mod ( toomcook_P BASE a b ) ( Min.min KA KB ), Nat.mod_lt ( toomcook_P BASE a b ) ( by linarith : 0 < Min.min KA KB ), Nat.sub_add_cancel ( by linarith : 1 ≤ digits BASE b + KB ), Nat.sub_add_cancel ( by linarith : 1 ≤ KB ) ];
    · linarith

lemma eval_bound_b
  (KA KB BASE : ℕ)
  (h_base : 1 < BASE)
  (hk : 1 < KA ∧ 1 < KB)
  (a b : ℕ)
  (POINTS : Vector ℤ (KA+KB-1))
: ∀ p ∈ POINTS, (digits BASE (eval_vec_as_poly (toomcook_split KA KB KB BASE a b b) p))
≤ ((toomcook_P BASE a b) / (min KA KB)) + (toomcook_C BASE KA KB POINTS) := by
  intro p hp
  have h_poly_bound : ∀ i : Fin KB, digits BASE ((toomcook_split KA KB KB BASE a b b).get i) ≤ (toomcook_P BASE a b) / (min KA KB) + 1 := by
    intro i
    have h_poly_bound : digits BASE ((toomcook_split KA KB KB BASE a b b).get i) ≤ (toomcook_P BASE a b) / (min KA KB) + 1 := by
      refine' le_trans _ ( toomcook_i_le KA KB BASE a b hk );
      apply piece_i_bound KA KB KB BASE h_base a b b (toomcook_split KA KB KB BASE a b b |>.get i) (by
      simp +decide [ Vector.get ])
    exact h_poly_bound;
  -- Since each coefficient of the polynomial is bounded by PUB, their sum is also bounded by PUB. Therefore, the polynomial evaluated at any point is also bounded by PUB.
  have h_sum_bound : ∀ p ∈ POINTS, digits BASE (eval_vec_as_poly (toomcook_split KA KB KB BASE a b b) p) ≤ (toomcook_P BASE a b) / (min KA KB) + 1 + digits BASE ((∑ i ∈ Finset.range KB, (toomcook_vmax KA KB POINTS) ^ i) : ℤ) := by
    intros p hp
    have h_sum_bound : |eval_vec_as_poly (toomcook_split KA KB KB BASE a b b) p| ≤ (∑ i ∈ Finset.range KB, (toomcook_vmax KA KB POINTS) ^ i) * (BASE ^ ((toomcook_P BASE a b) / (min KA KB) + 1)) := by
      have h_sum_bound : ∀ i : Fin KB, |((toomcook_split KA KB KB BASE a b b).get i : ℤ) * p ^ (i.1)| ≤ (toomcook_vmax KA KB POINTS) ^ (i.1) * (BASE ^ ((toomcook_P BASE a b) / (min KA KB) + 1)) := by
        intros i
        have h_coeff_bound : |((toomcook_split KA KB KB BASE a b b).get i : ℤ)| ≤ BASE ^ ((toomcook_P BASE a b) / (min KA KB) + 1) := by
          have := h_poly_bound i;
          unfold digits at this;
          have := @Nat.length_digits BASE ( Int.natAbs ( ( toomcook_split KA KB KB BASE a b b ).get i ) );
          by_cases hi : ( toomcook_split KA KB KB BASE a b b ).get i = 0 <;> simp_all +decide [ Nat.log_eq_iff ];
          exact_mod_cast Nat.le_of_lt ( Nat.lt_pow_of_log_lt h_base ( by linarith ) );
        have h_p_bound : |p| ≤ toomcook_vmax KA KB POINTS := by
          have h_p_bound : ∀ p ∈ POINTS.toList, |p| ≤ List.foldl (fun acc z => max acc z.natAbs) 0 POINTS.toList := by
            induction' POINTS.toList using List.reverseRecOn with p POINTS ih <;> aesop;
          exact h_p_bound p <| by simpa using hp;
        simpa only [ abs_mul, abs_pow, mul_comm ] using mul_le_mul ( pow_le_pow_left₀ ( by positivity ) h_p_bound _ ) h_coeff_bound ( by positivity ) ( by positivity );
      convert Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun i _ => h_sum_bound i using 1 ; norm_num [ Finset.sum_range, eval_vec_as_poly ] ; ring!;
      simp +decide only [Finset.sum_mul _ _ _];
    -- The number of digits of a number $n$ in base $b$ is given by $\lfloor \log_b(n) \rfloor + 1$.
    have h_digits_formula : ∀ n : ℕ, n > 0 → digits BASE n = Nat.log BASE n + 1 := by
      intro n hn; have := Nat.length_digits BASE n; aesop;
    by_cases h : 0 < ∑ i ∈ Finset.range KB, ( toomcook_vmax KA KB POINTS : ℕ ) ^ i <;> simp_all +decide [ add_comm ];
    · have h_digits_bound : digits BASE (Int.natAbs (eval_vec_as_poly (toomcook_split KA KB KB BASE a b b) p)) ≤ Nat.log BASE ((∑ i ∈ Finset.range KB, (toomcook_vmax KA KB POINTS) ^ i) * (BASE ^ ((toomcook_P BASE a b) / (min KA KB) + 1))) + 1 := by
        by_cases h_abs : Int.natAbs (eval_vec_as_poly (toomcook_split KA KB KB BASE a b b) p) = 0 <;> simp_all +decide [ digits ];
        refine' Nat.log_mono_right _;
        rw [ ← Int.ofNat_le ] ; aesop;
      have h_log_bound : Nat.log BASE ((∑ i ∈ Finset.range KB, (toomcook_vmax KA KB POINTS) ^ i) * (BASE ^ ((toomcook_P BASE a b) / (min KA KB) + 1))) ≤ Nat.log BASE (∑ i ∈ Finset.range KB, (toomcook_vmax KA KB POINTS) ^ i) + ((toomcook_P BASE a b) / (min KA KB) + 1) := by
        refine' Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow _ _ );
        · positivity;
        · rw [ Nat.pow_succ ];
          rw [ Nat.pow_succ, mul_comm ];
          have := Nat.lt_pow_succ_log_self h_base ( ∑ i ∈ Finset.range KB, toomcook_vmax KA KB POINTS ^ i ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
          exact mul_lt_mul_of_pos_left ( by convert mul_lt_mul_of_pos_right this ( pow_pos ( zero_lt_one.trans h_base ) ( toomcook_P BASE a b / Min.min KA KB ) ) using 1 ; ring ) ( zero_lt_one.trans h_base );
      have h_digits_sum : digits BASE (∑ i ∈ Finset.range KB, (toomcook_vmax KA KB POINTS) ^ i) = Nat.log BASE (∑ i ∈ Finset.range KB, (toomcook_vmax KA KB POINTS) ^ i) + 1 := by
        exact_mod_cast h_digits_formula _ h;
      convert h_digits_bound.trans ( Nat.succ_le_succ h_log_bound ) using 1 ; ring!;
      linarith! [ Nat.succ_le_succ ( Nat.zero_le ( Nat.log BASE ( ∑ i ∈ Finset.range KB, toomcook_vmax KA KB POINTS ^ i ) ) ) ] ;
    · specialize h 0 ; aesop;
  refine le_trans ( h_sum_bound p hp ) ?_;
  unfold toomcook_C; ring_nf; aesop;

lemma decrease_property_aux
  (KA KB BASE : ℕ)
  (h_base : 1 < BASE)
  (hk : 1 < KA ∧ 1 < KB)
  (a b : ℕ)
  (POINTS : Vector ℤ (KA+KB-1))
  (h_THETA : (toomcook_P BASE a b) > (toomcook_THETA BASE KA KB POINTS))
: ((toomcook_P BASE a b) / (min KA KB)) + (toomcook_C BASE KA KB POINTS) < (toomcook_P BASE a b) := by
  unfold toomcook_THETA at h_THETA;
  -- By multiplying both sides of the inequality by $(min KA KB - 1)$, we can eliminate the denominator and simplify the expression.
  have h_mul : (toomcook_P BASE a b : ℚ) * (min KA KB - 1) > toomcook_C BASE KA KB POINTS * min KA KB := by
    rw [ gt_iff_lt, div_lt_iff₀ ] at h_THETA <;> aesop;
  norm_cast at h_mul;
  rw [ Int.subNatNat_eq_coe ] at h_mul
  norm_num at h_mul
  nlinarith [ Nat.div_mul_le_self ( toomcook_P BASE a b ) ( Min.min KA KB ), show 0 < Min.min KA KB from lt_min hk.1.le hk.2.le ]

lemma digits_eval_bound (K : ℕ) (coeffs : Vector ℕ K) (p : ℤ) (B V : ℕ) (BASE : ℕ) (hBASE : BASE > 1)
  (h_coeffs : ∀ i, coeffs.get i < B)
  (h_p : p.natAbs ≤ V)
  : digits BASE (eval_vec_as_poly coeffs p) ≤ digits BASE B + digits BASE ((∑ i ∈ Finset.range K, V ^ i) : ℤ) := by
  -- By the properties of digit lengths, we have:
  have h_digit_length : digits BASE (eval_vec_as_poly coeffs p) ≤ digits BASE (B * ∑ i ∈ Finset.range K, V ^ i) := by
    -- By the properties of digit lengths, we have that $|eval_vec_as_poly coeffs p| \leq B \cdot \sum_{i=0}^{K-1} V^i$.
    have h_eval_bound : |eval_vec_as_poly coeffs p| ≤ B * ∑ i ∈ Finset.range K, V ^ i := by
      norm_num [ eval_vec_as_poly ];
      rw [ Finset.mul_sum _ _ _, Finset.sum_range ];
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i _ => by rw [ abs_mul, abs_pow ] ; exact mul_le_mul ( mod_cast Nat.le_of_lt ( h_coeffs i ) ) ( pow_le_pow_left₀ ( by positivity ) ( mod_cast by linarith ) _ ) ( by positivity ) ( by positivity ) );
    -- Since the number of digits of a number is determined by its absolute value, if |a| ≤ |b|, then the number of digits of a is less than or equal to the number of digits of b.
    have h_digit_length : ∀ a b : ℤ, |a| ≤ |b| → digits BASE a ≤ digits BASE b := by
      -- The number of digits of an integer is determined by its absolute value. If |a| ≤ |b|, then the number of digits of a is less than or equal to the number of digits of b.
      intros a b hab
      have h_digits : (Nat.digits BASE (Int.natAbs a)).length ≤ (Nat.digits BASE (Int.natAbs b)).length := by
        by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide [ Nat.length_digits ];
        exact Nat.log_mono_right ( by linarith [ abs_nonneg a, abs_nonneg b ] );
      exact h_digits;
    exact h_digit_length _ _ ( le_trans h_eval_bound ( le_abs_self _ ) );
  refine le_trans h_digit_length ?_;
  convert digits_mul_ub B ( ∑ i ∈ Finset.range K, V ^ i ) BASE hBASE using 1 ; norm_cast

lemma eval_bound_a
  (KA KB BASE : ℕ)
  (h_base : 1 < BASE)
  (hk : 1 < KA ∧ 1 < KB)
  (a b : ℕ)
  (POINTS : Vector ℤ (KA+KB-1))
: ∀ p ∈ POINTS, (digits BASE (eval_vec_as_poly (toomcook_split KA KB KA BASE a b a) p))
≤ ((toomcook_P BASE a b) / (min KA KB)) + (toomcook_C BASE KA KB POINTS) := by
  intro p hp
  have h_poly_bound : ∀ i : Fin KA, digits BASE ((toomcook_split KA KB KA BASE a b a).get i) ≤ (toomcook_P BASE a b) / (min KA KB) + 1 := by
    intro i
    have h_poly_bound : digits BASE ((toomcook_split KA KB KA BASE a b a).get i) ≤ (toomcook_P BASE a b) / (min KA KB) + 1 := by
      refine' le_trans _ ( toomcook_i_le KA KB BASE a b hk );
      apply piece_i_bound KA KB KA BASE h_base a b a (toomcook_split KA KB KA BASE a b a |>.get i) (by
      simp +decide [ Vector.get ])
    exact h_poly_bound;
  -- Since each coefficient of the polynomial is bounded by PUB, their sum is also bounded by PUB. Therefore, the polynomial evaluated at any point is also bounded by PUB.
  have h_sum_bound : ∀ p ∈ POINTS, digits BASE (eval_vec_as_poly (toomcook_split KA KB KA BASE a b a) p) ≤ (toomcook_P BASE a b) / (min KA KB) + 1 + digits BASE ((∑ i ∈ Finset.range KA, (toomcook_vmax KA KB POINTS) ^ i) : ℤ) := by
    intros p hp
    have h_sum_bound : |eval_vec_as_poly (toomcook_split KA KB KA BASE a b a) p| ≤ (∑ i ∈ Finset.range KA, (toomcook_vmax KA KB POINTS) ^ i) * (BASE ^ ((toomcook_P BASE a b) / (min KA KB) + 1)) := by
      have h_sum_bound : ∀ i : Fin KA, |((toomcook_split KA KB KA BASE a b a).get i : ℤ) * p ^ (i.1)| ≤ (toomcook_vmax KA KB POINTS) ^ (i.1) * (BASE ^ ((toomcook_P BASE a b) / (min KA KB) + 1)) := by
        intros i
        have h_coeff_bound : |((toomcook_split KA KB KA BASE a b a).get i : ℤ)| ≤ BASE ^ ((toomcook_P BASE a b) / (min KA KB) + 1) := by
          have := h_poly_bound i;
          unfold digits at this;
          have := @Nat.length_digits BASE ( Int.natAbs ( ( toomcook_split KA KB KA BASE a b a ).get i ) );
          by_cases hi : ( toomcook_split KA KB KA BASE a b a ).get i = 0 <;> simp_all +decide [ Nat.log_eq_iff ];
          exact_mod_cast Nat.le_of_lt ( Nat.lt_pow_of_log_lt h_base ( by linarith ) );
        have h_p_bound : |p| ≤ toomcook_vmax KA KB POINTS := by
          have h_p_bound : ∀ p ∈ POINTS.toList, |p| ≤ List.foldl (fun acc z => max acc z.natAbs) 0 POINTS.toList := by
            induction' POINTS.toList using List.reverseRecOn with p POINTS ih <;> aesop;
          exact h_p_bound p <| by simpa using hp;
        simpa only [ abs_mul, abs_pow, mul_comm ] using mul_le_mul ( pow_le_pow_left₀ ( by positivity ) h_p_bound _ ) h_coeff_bound ( by positivity ) ( by positivity );
      convert Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun i _ => h_sum_bound i using 1 ; norm_num [ Finset.sum_range, eval_vec_as_poly ] ; ring!;
      simp +decide only [Finset.sum_mul _ _ _];
    -- The number of digits of a number $n$ in base $b$ is given by $\lfloor \log_b(n) \rfloor + 1$.
    have h_digits_formula : ∀ n : ℕ, n > 0 → digits BASE n = Nat.log BASE n + 1 := by
      intro n hn; have := Nat.length_digits BASE n; aesop;
    by_cases h : 0 < ∑ i ∈ Finset.range KA, ( toomcook_vmax KA KB POINTS : ℕ ) ^ i <;> simp_all +decide [ add_comm ];
    · have h_digits_bound : digits BASE (Int.natAbs (eval_vec_as_poly (toomcook_split KA KB KA BASE a b a) p)) ≤ Nat.log BASE ((∑ i ∈ Finset.range KA, (toomcook_vmax KA KB POINTS) ^ i) * (BASE ^ ((toomcook_P BASE a b) / (min KA KB) + 1))) + 1 := by
        by_cases h_abs : Int.natAbs (eval_vec_as_poly (toomcook_split KA KB KA BASE a b a) p) = 0 <;> simp_all +decide [ digits ];
        refine' Nat.log_mono_right _;
        rw [ ← Int.ofNat_le ] ; aesop;
      have h_log_bound : Nat.log BASE ((∑ i ∈ Finset.range KA, (toomcook_vmax KA KB POINTS) ^ i) * (BASE ^ ((toomcook_P BASE a b) / (min KA KB) + 1))) ≤ Nat.log BASE (∑ i ∈ Finset.range KA, (toomcook_vmax KA KB POINTS) ^ i) + ((toomcook_P BASE a b) / (min KA KB) + 1) := by
        refine' Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow _ _ );
        · positivity;
        · rw [ Nat.pow_succ ];
          rw [ Nat.pow_succ, mul_comm ];
          have := Nat.lt_pow_succ_log_self h_base ( ∑ i ∈ Finset.range KA, toomcook_vmax KA KB POINTS ^ i ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
          exact mul_lt_mul_of_pos_left ( by convert mul_lt_mul_of_pos_right this ( pow_pos ( zero_lt_one.trans h_base ) ( toomcook_P BASE a b / Min.min KA KB ) ) using 1 ; ring ) ( zero_lt_one.trans h_base );
      have h_digits_sum : digits BASE (∑ i ∈ Finset.range KA, (toomcook_vmax KA KB POINTS) ^ i) = Nat.log BASE (∑ i ∈ Finset.range KA, (toomcook_vmax KA KB POINTS) ^ i) + 1 := by
        exact_mod_cast h_digits_formula _ h;
      convert h_digits_bound.trans ( Nat.succ_le_succ h_log_bound ) using 1 ; ring!;
      linarith! [ Nat.succ_le_succ ( Nat.zero_le ( Nat.log BASE ( ∑ i ∈ Finset.range KA, toomcook_vmax KA KB POINTS ^ i ) ) ) ] ;
    · specialize h 0 ; aesop;
  refine le_trans ( h_sum_bound p hp ) ?_;
  unfold toomcook_C; ring_nf; aesop;

lemma digits_pow_mul_eq (BASE k m : ℕ) (hBASE : 1 < BASE) (hm : 0 < m) :
  digits BASE (BASE ^ k * m) = k + digits BASE m := by
    -- By induction on $k$, we can show that multiplying by $BASE^k$ adds $k$ zeros to the number, which increases the digit count by $k$.
    have h_ind : ∀ k : ℕ, digits BASE (BASE^k * m) = digits BASE m + k := by
      intro k; exact (by
      unfold digits; norm_cast; induction' k with k ih <;> simp_all +decide [ pow_succ', mul_assoc ] ;
      rcases BASE with ( _ | _ | BASE ) <;> simp_all +decide [ Nat.pow_succ', mul_assoc ] ; ring;);
    rw [ h_ind, add_comm ]

lemma toomcook_P_le_of_digits_le
  (BASE P : ℕ) (a b : ℤ)
  (ha : digits BASE a ≤ P)
  (hb : digits BASE b ≤ P) :
  toomcook_P BASE a b ≤ P := by
  -- put toomcook_P into the “max |a| |b|” form your goals are using
  simp [toomcook_P, digits] at *  -- leaves goal in terms of (BASE.digits (max |a| |b|).natAbs).length
  by_cases h : (abs a) ≤ (abs b)
  · have hmax : max (abs a) (abs b) = abs b := max_eq_right h
    -- reduce to hb using digits(BASE, |b|) = digits(BASE, b)
    simpa [hmax, digits, Int.natAbs_abs] using hb
  · have h' : (abs b) ≤ (abs a) := le_of_not_ge h
    have hmax : max (abs a) (abs b) = abs a := max_eq_left h'
    simpa [hmax, digits, Int.natAbs_abs] using ha


-- GPT-5 assisted
lemma decrease_property
  (KA KB BASE : ℕ)
  (h_base : 1 < BASE)
  (hk : 1 < KA ∧ 1 < KB)
  (a b : ℤ)
  (POINTS : Vector ℤ (KA+KB-1))
  (i : Fin (KA+KB - 1))
  (h_THETA : (toomcook_P BASE a b) > (toomcook_THETA BASE KA KB POINTS))
: toomcook_P BASE
    |(eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i))|
    |(eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i))|
  < toomcook_P BASE a b := by

  have h_memb : POINTS.get i ∈ POINTS := by
    simp [Vector.get, Vector.toList]

  set P_PRIME : ℕ := (toomcook_P BASE a b) / (min KA KB) + toomcook_C BASE KA KB POINTS

  have h_P_abs : toomcook_P BASE |a| |b| = toomcook_P BASE a b := by
    simp [toomcook_P]

  have h_m:
  digits BASE |(eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i))|
  ≤ P_PRIME := by
    simpa [P_PRIME, h_P_abs, digits_abs] using (eval_bound_a KA KB BASE h_base hk a.natAbs b.natAbs POINTS (POINTS.get i) h_memb)

  have h_n:
  digits BASE |(eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i))|
  ≤ P_PRIME := by
    simpa [P_PRIME, h_P_abs, digits_abs] using (eval_bound_b KA KB BASE h_base hk a.natAbs b.natAbs POINTS (POINTS.get i) h_memb)

  have:
  toomcook_P BASE |(eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i))|
            |(eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i))|
  ≤ P_PRIME := by
    exact toomcook_P_le_of_digits_le
            BASE
            P_PRIME
            |(eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i))|
            |(eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i))|
            h_m
            h_n

  have : P_PRIME < toomcook_P BASE a b := by
    simpa [P_PRIME, h_P_abs] using
      (decrease_property_aux KA KB BASE h_base hk a.natAbs b.natAbs POINTS
          (by simpa [h_P_abs] using h_THETA))

  linarith

-- END TERMINATION LEMMAS
-- ----------------------------------------------------------------------
-- BEGIN RECURSIVE DEFINITION

-- ======== interpolate ========
-- this is an "unsafe" definition, as it doesn't assume injectivity.
-- the algorithm definition below does, and uses that to prove correctness.
noncomputable def interpolate
  (KA KB : ℕ)
  (POINTS_Q : Fin (KA+KB-1) → ℚ)
  (evaluated_pq_pts : Fin (KA+KB - 1) → ℚ)
: Vector ℚ (KA+KB-1) :=
  let VQ := Matrix.vandermonde (R := ℚ) POINTS_Q
  Vector.ofFn ((VQ)⁻¹.mulVec evaluated_pq_pts)

noncomputable def toomcook
(BASE KA KB : ℕ)
(h_base : 1 < BASE)
(h_k : 1 < KA ∧ 1 < KB)
(a b : ℤ)
(POINTS : Vector ℤ (KA + KB - 1))
(h_inj : Function.Injective POINTS.get)
: ℚ :=
  if h : (toomcook_P BASE a b ≤ (toomcook_THETA BASE KA KB POINTS)) then
    a * b
  else

    let a_abs : ℕ := (a.natAbs)
    let b_abs : ℕ := (b.natAbs)

    let B := toomcook_B KA KB BASE a_abs b_abs
    let pcoeffs := toomcook_split KA KB KA BASE a_abs b_abs a_abs
    let qcoeffs := toomcook_split KA KB KB BASE a_abs b_abs b_abs

    let p_vec := fun i => eval_vec_as_poly pcoeffs (POINTS.get i)
    let q_vec := fun i => eval_vec_as_poly qcoeffs (POINTS.get i)

    let evaluated_pq : Fin (KA + KB - 1) → ℚ :=
      fun i =>
        let aa := p_vec i
        let bb := q_vec i
        let absprod := toomcook BASE KA KB h_base h_k (aa.natAbs : ℤ) (bb.natAbs : ℤ) POINTS h_inj
        if (Xor' (aa < 0) (bb < 0)) then -absprod else absprod

    let POINTS_Q := fun i => (POINTS.get i : ℚ)
    let r := interpolate KA KB POINTS_Q evaluated_pq
    let absprod := eval_vec_as_poly_Q r B

    if (Xor' (a < 0) (b < 0)) then -absprod else absprod
termination_by
  toomcook_P BASE a b
decreasing_by
  simpa [p_vec, q_vec] using (decrease_property KA KB BASE h_base h_k a b POINTS i (lt_of_not_ge h))

-----------------------------------------------------------
-- CORRECTNESS ARGUMENT: ALL ARISTOTLE!
-----------------------------------------------------------
/-
Helper lemma: The polynomial constructed by splitting `z` into digits in base `toomcook_B` evaluates to `z` at `toomcook_B`.
-/
lemma eval_toomcook_split_correct (KA KB KZ BASE : ℕ) (a b z : ℕ)
  (hBASE : BASE > 1)
  (hz : z < (toomcook_B KA KB BASE a b) ^ KZ) :
  eval_vec_as_poly (toomcook_split KA KB KZ BASE a b z) (toomcook_B KA KB BASE a b) = z := by
  -- By definition of `toomcook_split`, the polynomial constructed by splitting `z` into digits in base `toomcook_B` evaluates to `z` at `toomcook_B`.
  have h_eval_poly : ∀ (n : ℕ) (B K : ℕ), n < B^K → ∑ i ∈ Finset.range K, (n / B^i % B : ℤ) * B^i = n := by
    intro n B K hnK; induction' K with K ih generalizing n <;> simp_all +decide [ Finset.sum_range_succ', pow_succ' ] ;
    have := ih ( n / B ) ( Nat.div_lt_of_lt_mul <| by linarith ) ; simp_all +decide [ Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm ] ;
    convert congr_arg ( fun x : ℤ => x * B + ( n % B ) ) this using 1 <;> norm_cast <;> norm_num [ Nat.div_div_eq_div_mul, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ] ; ring;
    rw [ Nat.div_add_mod ];
  convert h_eval_poly z _ _ hz using 1 ; norm_num [ eval_vec_as_poly, toomcook_split ] ; ring!;
  rw [ Finset.sum_range ]

/-
Lemma: `interpolate` correctly finds a polynomial that passes through the given points, provided the points are distinct.
-/
lemma interpolate_correct
  (KA KB : ℕ)
  (POINTS_Q : Fin (KA+KB-1) → ℚ)
  (evaluated_pq_pts : Fin (KA+KB - 1) → ℚ)
  (h_distinct : Function.Injective POINTS_Q) :
  let poly := interpolate KA KB POINTS_Q evaluated_pq_pts
  ∀ i : Fin (KA+KB-1), eval_vec_as_poly_Q poly (POINTS_Q i) = evaluated_pq_pts i := by
    unfold eval_vec_as_poly_Q interpolate;
    -- By definition of Vandermonde matrix, we know that the product of the Vandermonde matrix and its inverse is the identity matrix.
    have h_vandermonde_inv : Matrix.det (Matrix.vandermonde POINTS_Q) ≠ 0 := by
      rw [ Matrix.det_vandermonde ] ; exact Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero_of_ne <| by intro h; have := h_distinct h; aesop;
    intro poly i; have := congr_arg ( fun v : Fin ( KA + KB - 1 ) → ℚ => v i ) ( show Matrix.mulVec ( Matrix.vandermonde POINTS_Q ) ( Matrix.mulVec ( Matrix.vandermonde POINTS_Q ) ⁻¹ evaluated_pq_pts ) = evaluated_pq_pts from by simp +decide [ h_vandermonde_inv, isUnit_iff_ne_zero ] ) ; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
    convert this using 1 ; simp +decide [ mul_comm, Finset.mul_sum _ _ _, Finset.sum_mul, Vector.get ] ; ring!;
    simp +decide [ Vector.ofFn, Matrix.mulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]

/-
Defining `vec_to_poly` and proving properties about evaluation and degree.
-/
def vec_to_poly {K : ℕ} (v : Vector ℚ K) : Polynomial ℚ :=
  ∑ i : Fin K, Polynomial.monomial i (v.get i)

lemma eval_eq_eval_vec {K : ℕ} (v : Vector ℚ K) (x : ℚ) :
  (vec_to_poly v).eval x = eval_vec_as_poly_Q v x := by
    unfold vec_to_poly eval_vec_as_poly_Q; simp +decide [ Polynomial.eval_finset_sum, Polynomial.eval_smul, Finset.mul_sum _ _ _ ] ;

lemma degree_vec_to_poly_le {K : ℕ} (v : Vector ℚ K) :
  (vec_to_poly v).degree ≤ ↑(K - 1) := by
    exact le_trans ( Polynomial.degree_sum_le _ _ ) ( Finset.sup_le fun i _ => Polynomial.degree_monomial_le _ _ |> le_trans <| WithBot.coe_le_coe.mpr <| Nat.le_sub_one_of_lt <| Fin.is_lt i )

/-
Helper lemma: If we interpolate the point-wise products of two polynomials, the result evaluated at `B` is the product of the polynomials evaluated at `B`.
-/
lemma toomcook_interpolation_correct
  (KA KB : ℕ)
  (pcoeffs : Vector ℚ KA)
  (qcoeffs : Vector ℚ KB)
  (POINTS : Vector ℚ (KA + KB - 1))
  (h_distinct : Function.Injective POINTS.get)
  (B : ℚ)
  (hKA : 1 < KA) (hKB : 1 < KB) :
  let evaluated_pq := fun i => (eval_vec_as_poly_Q pcoeffs (POINTS.get i)) * (eval_vec_as_poly_Q qcoeffs (POINTS.get i))
  let r_vec := interpolate KA KB POINTS.get evaluated_pq
  eval_vec_as_poly_Q r_vec B = (eval_vec_as_poly_Q pcoeffs B) * (eval_vec_as_poly_Q qcoeffs B) := by
    -- By definition of `interpolate`, the polynomial `r_vec` is such that when evaluated at `POINTS.get i`, it gives `eval_vec_as_poly_Q pcoeffs (POINTS.get i) * eval_vec_as_poly_Q qcoeffs (POINTS.get i)`.
    have h_interpolate : ∀ i : Fin (KA + KB - 1), eval_vec_as_poly_Q (interpolate KA KB POINTS.get (fun i => eval_vec_as_poly_Q pcoeffs (POINTS.get i) * eval_vec_as_poly_Q qcoeffs (POINTS.get i))) (POINTS.get i) = eval_vec_as_poly_Q pcoeffs (POINTS.get i) * eval_vec_as_poly_Q qcoeffs (POINTS.get i) := by
      apply_rules [ interpolate_correct ];
    -- Since `r_vec` is a polynomial of degree at most `KA + KB - 2` that agrees with `p(x) * q(x)` at `KA + KB - 1` distinct points, it must be equal to `p(x) * q(x)`.
    have h_poly_eq : vec_to_poly (interpolate KA KB POINTS.get (fun i => eval_vec_as_poly_Q pcoeffs (POINTS.get i) * eval_vec_as_poly_Q qcoeffs (POINTS.get i))) = vec_to_poly pcoeffs * vec_to_poly qcoeffs := by
      refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
      exact Finset.image POINTS.get Finset.univ;
      · refine' lt_of_le_of_lt ( Polynomial.degree_sub_le _ _ ) _;
        refine' lt_of_le_of_lt ( max_le _ _ ) _;
        exact ↑ ( KA + KB - 2 );
        · convert degree_vec_to_poly_le _ using 1;
        · refine' le_trans ( Polynomial.degree_mul_le _ _ ) _;
          refine' le_trans ( add_le_add ( degree_vec_to_poly_le _ ) ( degree_vec_to_poly_le _ ) ) _ ; norm_cast ; omega;
        · rw [ Finset.card_image_of_injective _ h_distinct ] ; norm_num ; omega;
      · simp_all +decide [ eval_eq_eval_vec ];
    convert congr_arg ( Polynomial.eval B ) h_poly_eq using 1 <;> simp +decide [ eval_eq_eval_vec ]

/-
Lemma: If the number of digits of `n` in base `B` is at most `K`, then `n < B^K`.
-/
-- Body is GPT-written (ARistotle came up with the header but its version failed locally)
lemma nat_lt_pow_of_digits_le (B n K : ℕ) (hB : 1 < B) (h : digits B n ≤ K) :
  n < B ^ K := by
  have hn : n < B ^ (B.digits n).length := by
    simpa [digits] using
      (Nat.lt_base_pow_length_digits (b := B) (m := n) hB)
  have hB0 : 0 < B := lt_trans Nat.zero_lt_one hB
  have hpow : B ^ (B.digits n).length ≤ B ^ K := by
    exact Nat.pow_le_pow_right hB0 (by simpa [digits] using h)
  exact lt_of_lt_of_le hn hpow

/-
Lemma: `eval_vec_as_poly` evaluated at an integer `x` and cast to rational is equal to `eval_vec_as_poly_Q` evaluated at `x` cast to rational.
-/
lemma eval_int_eq_eval_rat {K : ℕ} (v : Vector ℕ K) (x : ℤ) :
  ((eval_vec_as_poly v x) : ℚ) = eval_vec_as_poly_Q (v.map (fun (n : ℕ) => (n : ℚ))) (x : ℚ) := by
  unfold eval_vec_as_poly eval_vec_as_poly_Q
  simp only [Vector.get_map]
  push_cast
  rfl

/-
Proving that if the number of digits of `n` in base `B` is at most `K`, then `n < B^K`.
-/
lemma nat_lt_pow_of_digits_le' (B n K : ℕ) (hB : 1 < B) (h : digits B n ≤ K) :
  n < B ^ K := by
  unfold digits at h
  simp only [Int.natAbs_natCast] at h
  by_cases hn : n = 0
  · subst hn
    apply pow_pos (zero_lt_one.trans hB)
  · have h_len : (Nat.digits B n).length = Nat.log B n + 1 := Nat.length_digits B n hB hn
    rw [h_len] at h
    have h_log : Nat.log B n < K := Nat.lt_of_succ_le h
    apply Nat.lt_pow_of_log_lt hB h_log

/-
Checking the signature of the induction principle for `toomcook`.
-/
#check toomcook.induct

/-
Helper lemma: The sign logic in `toomcook` correctly reconstructs the product `a * b` from the magnitude `|a| * |b|`.
-/
lemma sign_logic (a b : ℤ) (absprod : ℚ) (h_absprod : absprod = (|a| * |b| : ℤ)) :
  (if Xor' (a < 0) (b < 0) then -absprod else absprod) = (a * b : ℚ) := by
    by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> simp +decide [ ha, hb, h_absprod ];
    · norm_cast ; rw [ abs_of_neg ha, abs_of_neg hb ] ; ring;
    · norm_cast ; simp +decide [ abs_of_neg ha, abs_of_nonneg ( le_of_not_gt hb ) ];
    · rw [ abs_of_nonneg, abs_of_nonpos ] <;> norm_cast <;> linarith;
    · rw [ abs_of_nonneg ( by norm_cast; linarith ), abs_of_nonneg ( by norm_cast; linarith ) ]

/-
Lemma: If `evaluated_pq` correctly represents the product of the evaluations of the split polynomials, then the Toom-Cook logic correctly computes `a * b`.
-/
lemma toomcook_logic_correct
  (BASE KA KB : ℕ) (h_base : 1 < BASE) (h_k : 1 < KA ∧ 1 < KB)
  (a b : ℤ) (POINTS : Vector ℤ (KA + KB - 1)) (h_inj : Function.Injective POINTS.get)
  (evaluated_pq : Fin (KA + KB - 1) → ℚ)
  (h_evaluated_pq : ∀ i, evaluated_pq i =
    (eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i) : ℚ) *
    (eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i) : ℚ)) :
  let a_abs := a.natAbs
  let b_abs := b.natAbs
  let B := toomcook_B KA KB BASE a_abs b_abs
  let POINTS_Q := fun i => (POINTS.get i : ℚ)
  let r := interpolate KA KB POINTS_Q evaluated_pq
  let absprod := eval_vec_as_poly_Q r B
  (if Xor' (a < 0) (b < 0) then -absprod else absprod) = (a * b : ℚ) := by
    convert sign_logic _ _ _ _ using 1;
    convert toomcook_interpolation_correct KA KB ( Vector.map ( fun n : ℕ => ( n : ℚ ) ) ( toomcook_split KA KB KA BASE ( Int.natAbs a ) ( Int.natAbs b ) ( Int.natAbs a ) ) ) ( Vector.map ( fun n : ℕ => ( n : ℚ ) ) ( toomcook_split KA KB KB BASE ( Int.natAbs a ) ( Int.natAbs b ) ( Int.natAbs b ) ) ) ( Vector.map ( fun n : ℤ => ( n : ℚ ) ) POINTS ) ?_ ( toomcook_B KA KB BASE ( Int.natAbs a ) ( Int.natAbs b ) ) h_k.left h_k.right using 1;
    · congr! 3;
      · simp +decide [ Vector.get ];
      · convert h_evaluated_pq _ using 1;
        unfold eval_vec_as_poly_Q eval_vec_as_poly; aesop;
    · have h_eval_eq : eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (toomcook_B KA KB BASE a.natAbs b.natAbs) = a.natAbs ∧ eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (toomcook_B KA KB BASE a.natAbs b.natAbs) = b.natAbs := by
        apply And.intro;
        · convert eval_toomcook_split_correct KA KB KA BASE a.natAbs b.natAbs a.natAbs h_base _;
          convert nat_lt_pow_of_digits_le' BASE _ _ _ _ using 1;
          rotate_left;
          exact toomcook_i KA KB BASE a.natAbs b.natAbs * KA;
          · linarith;
          · unfold toomcook_i;
            cases max_cases ( ( digits BASE a.natAbs + KA - 1 ) / KA ) ( ( digits BASE b.natAbs + KB - 1 ) / KB ) <;> nlinarith [ Nat.div_add_mod ( digits BASE a.natAbs + KA - 1 ) KA, Nat.mod_lt ( digits BASE a.natAbs + KA - 1 ) h_k.1.le, Nat.sub_add_cancel ( show 1 ≤ digits BASE a.natAbs + KA from by linarith ) ];
          · rw [ pow_mul, toomcook_B ];
        · convert eval_toomcook_split_correct KA KB KB BASE a.natAbs b.natAbs b.natAbs h_base _ using 1;
          convert nat_lt_pow_of_digits_le' BASE _ _ _ _ using 1;
          rotate_left;
          exact ( toomcook_i KA KB BASE a.natAbs b.natAbs ) * KB;
          · linarith;
          · unfold toomcook_i;
            cases max_cases ( ( digits BASE a.natAbs + KA - 1 ) / KA ) ( ( digits BASE b.natAbs + KB - 1 ) / KB ) <;> nlinarith [ Nat.div_add_mod ( digits BASE b.natAbs + KB - 1 ) KB, Nat.mod_lt ( digits BASE b.natAbs + KB - 1 ) ( by linarith : 0 < KB ), Nat.sub_add_cancel ( by linarith : 1 ≤ digits BASE b.natAbs + KB ) ];
          · rw [ pow_mul, toomcook_B ];
      convert congr_arg₂ ( · * · ) ( eval_int_eq_eval_rat ( toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs ) ( toomcook_B KA KB BASE a.natAbs b.natAbs ) ) ( eval_int_eq_eval_rat ( toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs ) ( toomcook_B KA KB BASE a.natAbs b.natAbs ) ) using 1 ; aesop;
    · intro i j; aesop;

/-
Theorem: `toomcook` correctly computes the product `a * b` as a rational number.
-/
theorem toomcook_correctness
(BASE KA KB : ℕ)
(h_base : 1 < BASE)
(h_k : 1 < KA ∧ 1 < KB)
(a b : ℤ)
(POINTS : Vector ℤ (KA + KB - 1))
(h_inj : Function.Injective POINTS.get)
: (toomcook BASE KA KB h_base h_k a b POINTS h_inj) = (a * b : ℚ)
:= by
  apply Classical.byContradiction
  intro h_neq;
  -- Apply the induction hypothesis to the recursively called toomcook.
  have h_ind : ∀ a b : ℤ, toomcook BASE KA KB h_base h_k a b POINTS h_inj = (a * b : ℚ) := by
    intro a b; induction' n : ( toomcook_P BASE a b ) using Nat.strong_induction_on with n ih generalizing a b;
    unfold toomcook; simp +decide [ n ] ;
    intro h_lt
    have h_eval : ∀ i : Fin (KA + KB - 1), toomcook BASE KA KB h_base h_k (|eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i)|) (|eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i)|) POINTS h_inj =
      (|eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i)| * |eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i)| : ℚ) := by
        intro i
        have h_eval : toomcook_P BASE (|eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i)|) (|eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i)|) < toomcook_P BASE a b := by
          apply decrease_property KA KB BASE h_base h_k a b POINTS i (by
          aesop);
        exact ih _ ( by linarith ) _ _ rfl;
    convert toomcook_logic_correct BASE KA KB h_base h_k a b POINTS h_inj _ _ using 1;
    rotate_left;
    use fun i => if Xor' (eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i) < 0) (eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i) < 0) then -(|eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i)| * |eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i)| : ℚ) else (|eval_vec_as_poly (toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs) (POINTS.get i)| * |eval_vec_as_poly (toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs) (POINTS.get i)| : ℚ);
    · intro i; split_ifs <;> simp_all +decide [ Xor' ] ;
      · cases ‹_› <;> simp_all +decide [ abs_of_neg, abs_of_nonneg ];
      · cases' lt_or_ge ( eval_vec_as_poly ( toomcook_split KA KB KA BASE a.natAbs b.natAbs a.natAbs ) ( POINTS.get i ) ) 0 with h h <;> cases' lt_or_ge ( eval_vec_as_poly ( toomcook_split KA KB KB BASE a.natAbs b.natAbs b.natAbs ) ( POINTS.get i ) ) 0 with h' h' <;> simp_all +decide [ abs_of_neg, abs_of_nonneg ];
    · simp +decide [ h_eval ];
  exact h_neq <| h_ind a b


/-
The result of `toomcook` is equal to the product `a * b` cast to `ℚ`.
-/
theorem toomcook_correctness_int_cast
(BASE KA KB : ℕ)
(h_base : 1 < BASE)
(h_k : 1 < KA ∧ 1 < KB)
(a b : ℤ)
(POINTS : Vector ℤ (KA + KB - 1))
(h_inj : Function.Injective POINTS.get) :
toomcook BASE KA KB h_base h_k a b POINTS h_inj = ((a * b : ℤ) : ℚ) := by
  simp [toomcook_correctness]
