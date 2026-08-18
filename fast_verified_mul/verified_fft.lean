-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> and Claude Opus 4.7

import Mathlib
import Cslib.Algorithms.Lean.TimeM

set_option linter.style.whitespace false
set_option linter.style.emptyLine false

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open Finset BigOperators
/-
General lemma: a for loop that sets each index independently produces Vector.ofFn
-/
lemma vector_set_forIn_range {α : Type*} (K : ℕ) (a₀ : α) (f : Fin K → α) :
    (Id.run do
      let mut result := Vector.replicate K a₀
      for h : i in [0:K] do
        have hi : i < K := h.2.1
        result := result.set i (f ⟨i, hi⟩) hi
      return result) =
    Vector.ofFn f := by
  refine' Eq.symm ( _ : _ = _ );
  induction' K with K ih;
  · grind +qlia;
  · simp +decide [ List.range'_concat, ih ];
    refine' Vector.ext fun i => _;
    intro hi;
    by_cases hi' : i < K <;> simp_all +decide [ Vector.getElem_set ];
    · rw [ if_neg ( ne_of_gt hi' ) ];
      convert congr_arg ( fun v : Vector α K => v[i] ) ( ih ( fun j => f ⟨ j, Nat.lt_succ_of_lt j.2 ⟩ ) ) using 1;
      · simp +decide [ Vector.ofFn ];
      · induction' ( List.range' 0 K ).attach using List.reverseRecOn with x xs ih <;> simp_all +decide [ List.foldl ];
        grind;
    · grind

private def t_table {F : Type*} [Field F] (K : ℕ) (OMEGA : F) : TimeM ℕ (Vector F K) := do
  tick K
  let mut T := Vector.replicate K 1

  tick 1
  let mut a := (1 : F)
  for h : j in [0:K] do
    tick 1
    T := T.set j a
    a := a * OMEGA
  return T

lemma t_table_get {F : Type*} [Field F] (n : ℕ) (OMEGA : F) (j : Fin n) :
    (t_table n OMEGA).ret[j] = OMEGA ^ j.val := by
  revert OMEGA;
  unfold t_table; simp +decide ;
  intro OMEGA;
  -- By definition of `t_table`, we know that after processing the first `j` elements, the vector `T` has the property that `T[i] = OMEGA^i` for all `i < j`.
  have h_ind : ∀ j : Fin (n + 1), (List.foldl (fun (b : Vector F n × F) (x : {x : ℕ // x ∈ List.range' 0 n}) => ⟨b.1.set x.val b.2 (by
  grind +splitImp), b.2 * OMEGA⟩) ⟨Vector.replicate n 1, 1⟩ (List.take j.val (List.attach (List.range' 0 n)))).1 = Vector.ofFn (fun i : Fin n => if i.val < j.val then OMEGA ^ i.val else 1) := by
    intro j
    induction' j using Fin.induction with j ih;
    · aesop;
    · simp_all +decide [ List.take_add_one ];
      ext i; simp +decide [ Vector.getElem_set, ih ] ; split_ifs <;> simp_all +decide [ Fin.ext_iff, Nat.lt_succ_iff ] ;
      · have h_ind : ∀ k : ℕ, k ≤ n → (List.foldl (fun (b : Vector F n × F) (x : {x : ℕ // x ∈ List.range' 0 n}) => ⟨b.1.set x.val b.2 (by
        grind), b.2 * OMEGA⟩) ⟨Vector.replicate n 1, 1⟩ (List.take k (List.attach (List.range' 0 n)))).2 = OMEGA ^ k := by
          intro k hk; induction' k with k ih <;> simp_all +decide [ pow_succ, List.take_add_one ] ;
          grind +splitIndPred
        generalize_proofs at *;
        exact h_ind i ( by linarith );
      · exact absurd ‹_› ( by simp +decide [ ← ‹ ( j : ℕ ) = i › ] );
      · exact False.elim <| lt_asymm ‹_› ‹_›;
      · exact False.elim ( ‹¬ ( j : ℕ ) = i› ( le_antisymm ‹_› ‹_› ) )
  generalize_proofs at *;
  convert congr_arg ( fun v : Vector F n => v[j] ) ( h_ind ⟨ n, Nat.lt_succ_self n ⟩ ) using 1;
  · simp +decide [ Id.run ];
    rw [ List.take_of_length_le ( by simp +decide ) ];
    congr! 2;
    induction' ( List.range' 0 n ).attach using List.reverseRecOn with x xs ih <;> simp +decide [ * ];
    congr! 2;
    clear ih;
    induction x using List.reverseRecOn <;> aesop;
  · simp +decide [ Vector.ofFn ]

lemma dft_split_sum {F : Type*} [Field F] {k_pred : ℕ}
    (x : Vector F (2^(k_pred+1))) (OMEGA : F) (i : Fin (2^k_pred)) :
    ∑ j : Fin (2^(k_pred+1)), x[j] * OMEGA ^ (j.val * i.val) =
    (∑ j : Fin (2^k_pred), x[2 * j.val] * (OMEGA^2) ^ (j.val * i.val)) +
    OMEGA ^ i.val * (∑ j : Fin (2^k_pred), x[2 * j.val + 1] * (OMEGA^2) ^ (j.val * i.val)) := by
  rw [ Finset.mul_sum, ← Finset.sum_add_distrib ];
  rw [ show ( Finset.univ : Finset ( Fin ( 2 ^ ( k_pred + 1 ) ) ) ) = Finset.image ( fun j : Fin ( 2 ^ k_pred ) => ⟨ 2 * j, by linarith [ Fin.is_lt j, pow_succ' 2 k_pred ] ⟩ ) Finset.univ ∪ Finset.image ( fun j : Fin ( 2 ^ k_pred ) => ⟨ 2 * j + 1, by linarith [ Fin.is_lt j, pow_succ' 2 k_pred ] ⟩ ) Finset.univ from ?_, Finset.sum_union ];
  · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num [ Fin.ext_iff ];
    · rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; ring;
    · exact fun a b h => by simpa [ Fin.ext_iff ] using congr_arg Fin.val h;
    · exact fun a b h => by simpa [ Fin.ext_iff ] using h;
  · norm_num [ Finset.disjoint_left ];
    grind;
  · ext j;
    rcases Nat.even_or_odd' j with ⟨ c, d | d ⟩ <;> simp +decide [ Fin.ext_iff, d ];
    · exact Or.inl ⟨ ⟨ c, by linarith [ Fin.is_lt j, pow_succ' 2 k_pred ] ⟩, rfl ⟩;
    · exact Or.inr ⟨ ⟨ c, by linarith [ Fin.is_lt j, pow_succ' 2 k_pred ] ⟩, rfl ⟩

lemma prim_root_half_eq_neg_one {F : Type*} [Field F] {k_pred : ℕ} {OMEGA : F}
    (h_OMEGA : IsPrimitiveRoot OMEGA (2^(k_pred+1))) : OMEGA ^ (2^k_pred) = -1 := by
  have h_one_minus_sq : (OMEGA ^ 2 ^ k_pred) ^ 2 = 1 := by
    rw [ ← pow_mul, ← pow_succ, h_OMEGA.pow_eq_one ];
  exact Or.resolve_left ( sq_eq_one_iff.mp h_one_minus_sq ) ( h_OMEGA.pow_ne_one_of_pos_of_lt ( by positivity ) ( by ring_nf; norm_num ) )

lemma dft_split_sum_high {F : Type*} [Field F] {k_pred : ℕ}
    (x : Vector F (2^(k_pred+1))) (OMEGA : F) (h_OMEGA : IsPrimitiveRoot OMEGA (2^(k_pred+1)))
    (i : Fin (2^(k_pred+1))) (hi : ¬ i.val < 2^k_pred) :
    let i' := i.val % (2^k_pred)
    ∑ j : Fin (2^(k_pred+1)), x[j] * OMEGA ^ (j.val * i.val) =
    (∑ j : Fin (2^k_pred), x[2 * j.val] * (OMEGA^2) ^ (j.val * i')) -
    OMEGA ^ i' * (∑ j : Fin (2^k_pred), x[2 * j.val + 1] * (OMEGA^2) ^ (j.val * i')) := by
  have h_split : ∑ j : Fin (2^(k_pred+1)), x[j] * OMEGA ^ (j.val * i.val) =
                 ∑ j : Fin (2^k_pred), x[2 * j.val] * OMEGA ^ (2 * j.val * i.val) +
                 ∑ j : Fin (2^k_pred), x[2 * j.val + 1] * OMEGA ^ ((2 * j.val + 1) * i.val) := by
                   have h_split : Finset.range (2^(k_pred+1)) = Finset.image (fun j => 2 * j) (Finset.range (2^k_pred)) ∪ Finset.image (fun j => 2 * j + 1) (Finset.range (2^k_pred)) := by
                     ext j
                     simp [Finset.mem_range, Finset.mem_image];
                     exact ⟨ fun hj => by rcases Nat.even_or_odd' j with ⟨ c, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ c, by rw [ pow_succ' ] at hj; linarith, rfl ⟩, fun hj => by rcases hj with ( ⟨ c, hc, rfl ⟩ | ⟨ c, hc, rfl ⟩ ) <;> rw [ pow_succ' ] <;> linarith ⟩;
                   rw [ Finset.sum_fin_eq_sum_range ];
                   rw [ h_split, Finset.sum_union ];
                   · norm_num [ Finset.sum_range, pow_succ' ];
                     grind +splitImp;
                   · norm_num [ Finset.disjoint_right ];
                     intros; omega;
  obtain ⟨i', hi'⟩ : ∃ i' : Fin (2^k_pred), i.val = 2^k_pred + i'.val := by
    exact ⟨ ⟨ i - 2 ^ k_pred, by rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt i, pow_succ' 2 k_pred ] ⟩, by simp +decide [ Nat.add_sub_of_le ( le_of_not_gt hi ) ] ⟩;
  have h_exp_simp : ∀ j : Fin (2^k_pred), OMEGA ^ (2 * j.val * i.val) = (OMEGA ^ 2) ^ (j.val * i'.val) ∧ OMEGA ^ ((2 * j.val + 1) * i.val) = -OMEGA ^ i'.val * (OMEGA ^ 2) ^ (j.val * i'.val) := by
    have h_exp_simp : OMEGA ^ (2 ^ k_pred) = -1 := by
      exact prim_root_half_eq_neg_one h_OMEGA;
    intro j; rw [ hi' ] ; ring_nf; simp_all +decide [ pow_mul', mul_assoc, mul_comm, mul_left_comm ] ;
  simp_all +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_add_distrib ];
  rw [ Nat.mod_eq_of_lt i'.2 ] ; ring;

-- the Discrete Fourier Transform over a field
private def dft
    {F : Type*} [Field F]
    {k : ℕ}
    (x : Vector F (2^k))
    (OMEGA : F) (_h_OMEGA : IsPrimitiveRoot OMEGA (2^k))
    : Vector F (2^k) :=
  Vector.ofFn fun i => ∑ j : Fin (2^k), x[j] * OMEGA ^ (j.val * i.val)

private lemma prim_root_mul_self
    {F : Type*} [Field F]
    {k_pred : ℕ} {OMEGA : F}
    (h_OMEGA : IsPrimitiveRoot OMEGA (2^(k_pred+1)))
    : IsPrimitiveRoot (OMEGA ^ 2) (2^k_pred) := by
  convert h_OMEGA.pow_of_dvd _ _ using 1
  · norm_num [pow_succ']
  · norm_num
  · exact dvd_pow_self _ (Nat.succ_ne_zero _)

-- the Fast Fourier Transform over a field
def fft
    {F : Type*} [Field F]
    {k : ℕ}
    (x : Vector F (2^k))
    (OMEGA : F)
    (h_OMEGA : IsPrimitiveRoot OMEGA (2^k))
    : TimeM ℕ (Vector F (2^k)) :=
  match k with
  | 0      => do
    return x
  | k_pred + 1 => do
    tick 1
    let K_pred : ℕ := 2 ^ k_pred
    let K  : ℕ := 2 ^ (k_pred + 1)
    let OMEGA_sq := OMEGA^2

    tick K
    let E : Vector F K_pred := Vector.ofFn fun j : Fin K_pred => x[2 * j.val]
    let O : Vector F K_pred := Vector.ofFn fun j : Fin K_pred => x[2 * j.val + 1]

    tick 1
    let h_OMEGA' : IsPrimitiveRoot OMEGA_sq K_pred := prim_root_mul_self h_OMEGA
    let X ← (fft E OMEGA_sq h_OMEGA')
    let Y ← (fft O OMEGA_sq h_OMEGA')
    let T ← (t_table K_pred OMEGA)

    tick K
    let mut result := Vector.replicate K (0 : F)

    for h : i in [0:K_pred] do
      tick 1
      have h_i    : i < K_pred := h.2.1
      have h_Low  : i < K := by omega
      have h_High : i + K_pred < K := by omega
      let p : F := X[i]
      let q : F := T[i] * Y[i]
      result := result.set i (p + q) h_Low
      result := result.set (i + K_pred) (p - q) h_High
    return result

-- claude
private lemma ret_foldlM_TimeM {α β : Type*}
    (body : α → β → TimeM ℕ α) (init : α) (xs : List β) :
    (List.foldlM body init xs).ret =
      List.foldl (fun b x => (body b x).ret) init xs := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    show (body init x >>= fun b' => List.foldlM body b' xs).ret = _
    rw [ret_bind]
    exact ih _

-- Pure functional version of the combination step
private def fft_pure
    {F : Type} [Field F]
    {k : ℕ}
    (x : Vector F (2^k))
    (OMEGA : F)
    (h_OMEGA : IsPrimitiveRoot OMEGA (2^k))
    : Vector F (2^k) :=
  match k with
  | 0      => x
  | k_pred + 1 =>
    let K_pred : ℕ := 2 ^ k_pred
    let E : Vector F K_pred := Vector.ofFn fun j : Fin K_pred => x[2 * j.val]
    let O : Vector F K_pred := Vector.ofFn fun j : Fin K_pred => x[2 * j.val + 1]
    let h_OMEGA' : IsPrimitiveRoot (OMEGA^2) K_pred := prim_root_mul_self h_OMEGA
    let E' := fft_pure E (OMEGA^2) h_OMEGA'
    let O' := fft_pure O (OMEGA^2) h_OMEGA'
    Id.run do
      let mut result : Vector F (2 ^ (k_pred + 1)) := Vector.replicate _ 0
      for h : i in [0:K_pred] do
        have hi : i < K_pred := h.2.1
        have hLow  : i < 2 ^ (k_pred + 1) := by omega
        have hHigh : i + K_pred < 2 ^ (k_pred + 1) := by omega
        let p : F := E'[i]
        let q : F := OMEGA ^ i * O'[i]
        result := result.set i           (p + q) hLow
        result := result.set (i + K_pred) (p - q) hHigh
      return result
/-- The vector returned by `t_table n OMEGA` has `i`-th entry `OMEGA^i`. -/
private lemma t_table_ret_eq {F : Type} [Field F] (n : ℕ) (OMEGA : F) :
    (t_table n OMEGA).ret = Vector.ofFn (fun j : Fin n => OMEGA ^ j.val) := by
  refine Vector.ext fun i hi => ?_
  simp
  exact t_table_get n OMEGA ⟨i, hi⟩

/-
The butterfly combination loop produces a specific vector.
-/
private lemma butterfly_loop_eq_ofFn {F : Type} [Field F] {K_pred : ℕ}
    (E' O' : Vector F K_pred) (OMEGA : F) :
    (Id.run do
      let mut result : Vector F (2 ^ 1 * K_pred) := Vector.replicate _ 0
      for h : i in [0:K_pred] do
        have hi : i < K_pred := h.2.1
        have hLow  : i < 2 * K_pred := by omega
        have hHigh : i + K_pred < 2 * K_pred := by omega
        let p : F := E'[i]
        let q : F := OMEGA ^ i * O'[i]
        result := result.set i           (p + q) hLow
        result := result.set (i + K_pred) (p - q) hHigh
      return result) =
    Vector.ofFn (fun j : Fin (2 * K_pred) =>
      if h : j.val < K_pred then
        E'[j.val] + OMEGA ^ j.val * O'[j.val]
      else
        E'[j.val - K_pred] - OMEGA ^ (j.val - K_pred) * O'[j.val - K_pred]) := by
  refine' Vector.ext fun j => _;
  intro hj;
  by_cases hj' : j < K_pred;
  · simp +decide [ vector_set_forIn_range, hj' ];
    have h_foldl : ∀ (l : List (Fin K_pred)), j ∈ List.map (fun x => x.val) l → (List.foldl (fun (b : Vector F (2 * K_pred)) (x : Fin K_pred) => (b.set x.val (E'[x.val] + OMEGA ^ x.val * O'[x.val]) (by
    linarith [ Fin.is_lt x ])).set (x.val + K_pred) (E'[x.val] - OMEGA ^ x.val * O'[x.val]) (by
    linarith [ Fin.is_lt x ])) (Vector.replicate (2 * K_pred) 0) l)[j] = E'[j] + OMEGA ^ j * O'[j] := by
      all_goals generalize_proofs at *;
      intro l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ] ;
      grind
    generalize_proofs at *;
    convert h_foldl _ _;
    rotate_left;
    exact List.attach ( List.range' 0 K_pred ) |> List.map fun x => ⟨ x.val, by
      grind +ring ⟩
    all_goals generalize_proofs at *;
    · simp +decide [ List.mem_map, List.mem_range' ];
      linarith;
    · induction ( List.range' 0 K_pred ).attach using List.reverseRecOn <;> aesop;
  · -- Since $j \geq K_pred$, we can write $j = K_pred + m$ for some $m$.
    obtain ⟨m, rfl⟩ : ∃ m, j = K_pred + m := by
      exact Nat.exists_eq_add_of_le ( le_of_not_gt hj' );
    simp +decide [ Vector.getElem_set, List.foldl ];
    have h_foldl : ∀ (l : List (Fin K_pred)), (∀ x ∈ l, x.val < K_pred) → (List.foldl (fun (b : Vector F (2 * K_pred)) (x : Fin K_pred) => (b.set x.val (E'[x.val] + OMEGA ^ x.val * O'[x.val]) (by
    linarith [ Fin.is_lt x ])).set (x.val + K_pred) (E'[x.val] - OMEGA ^ x.val * O'[x.val]) (by
    linarith [ Fin.is_lt x ])) (Vector.replicate (2 * K_pred) 0) l)[K_pred + m] = if m ∈ List.map (fun x => x.val) l then E'[m] - OMEGA ^ m * O'[m] else 0 := by
      intro l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ] ;
      grind;
    convert h_foldl _ _ using 1;
    rotate_left;
    rotate_left;
    exact List.attach ( List.range' 0 K_pred ) |> List.map fun x => ⟨ x.val, by
      grind ⟩
    all_goals generalize_proofs at *;
    · simp +decide [ List.mem_map, List.mem_range' ];
    · congr! 2;
      induction' ( List.range' 0 K_pred ).attach using List.reverseRecOn with x xs ih <;> simp +decide [ * ];
    · simp +decide [ List.mem_map, List.mem_range' ];
      exact fun h => False.elim <| by linarith;

/-
`fft.ret = fft_pure`
-/
private lemma fft_ret_eq_fft_pure
    {F : Type} [Field F]
    {k : ℕ}
    (x : Vector F (2^k))
    (OMEGA : F)
    (h_OMEGA : IsPrimitiveRoot OMEGA (2^k))
    : (fft x OMEGA h_OMEGA).ret = fft_pure x OMEGA h_OMEGA := by
  induction' k with k ih generalizing OMEGA;
  · rfl;
  · unfold fft fft_pure;
    simp +decide [ ← ih, t_table_ret_eq ];
    convert ret_foldlM_TimeM _ _ _ using 1

/-
`fft_pure = dft`
-/
private lemma fft_pure_eq_dft
    {F : Type} [Field F]
    {k : ℕ}
    (x : Vector F (2^k))
    (OMEGA : F)
    (h_OMEGA : IsPrimitiveRoot OMEGA (2^k))
    : fft_pure x OMEGA h_OMEGA = dft x OMEGA h_OMEGA := by
  revert x OMEGA h_OMEGA;
  induction' k with k ih;
  · -- In the base case where $k = 0$, the vector $x$ has length $1$, so the FFT and DFT are both equal to $x$.
    intro x OMEGA h_OMEGA
    simp [fft_pure, dft];
    grind;
  · intro x OMEGA h_OMEGA
    simp [fft_pure, dft];
    convert butterfly_loop_eq_ofFn _ _ _ using 1;
    rotate_left;
    exact F;
    exact inferInstance;
    exact 2 ^ k;
    exact Vector.ofFn fun j => ∑ i : Fin ( 2 ^ k ), x[2 * i.val] * ( OMEGA ^ 2 ) ^ ( i.val * j.val );
    exact Vector.ofFn fun j => ∑ i : Fin ( 2 ^ k ), x[2 * i.val + 1] * ( OMEGA ^ 2 ) ^ ( i.val * j.val );
    exact OMEGA;
    simp +decide [ ← pow_succ', ih ];
    congr! 2;
    · ring;
    · congr! 3;
      · ring;
      · congr! 2;
        · unfold dft; aesop;
        · unfold dft; aesop;
      · aesop;
      · unfold dft; aesop;
    · rw [ pow_succ' ];
    · ring;
    · congr! 1;
      · rw [ pow_succ' ];
      · rename_i i j hij;
        split_ifs;
        · convert dft_split_sum x OMEGA ⟨ j, by linarith ⟩ using 1;
          congr! 2;
          grind;
        · convert dft_split_sum_high x OMEGA h_OMEGA i _ using 1;
          · rw [ show ( i : ℕ ) % 2 ^ k = ( j : ℕ ) - 2 ^ k from ?_ ];
            rw [ Nat.mod_eq_sub_mod ];
            · rw [ Nat.mod_eq_of_lt ];
              · grind;
              · grind;
            · grind;
          · grind

-- FFT CORRECTNESS THEOREM
theorem fft_eq_dft
    {F : Type} [Field F]
    {k : ℕ}
    (x : Vector F (2^k))
    (OMEGA : F)
    (h_OMEGA : IsPrimitiveRoot OMEGA (2^k))
    : (fft x OMEGA h_OMEGA).ret = dft x OMEGA h_OMEGA := by
  rw [fft_ret_eq_fft_pure, fft_pure_eq_dft]


private def convert_vector_to_zmod
    {N : ℕ}
    [NeZero N]
    (v : Vector ℂ N)
    : ZMod N → ℂ :=
  fun j => v[j.val]'(ZMod.val_lt j)

private noncomputable def ZETA (k : ℕ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) / (2^k : ℂ))

private lemma ZETA_prim (k : ℕ) :
    IsPrimitiveRoot (ZETA k) (2^k) := by
  unfold ZETA;
  convert IsPrimitiveRoot.inv _ using 1;
  rotate_left;
  exact ℂ;
  exact inferInstance;
  exact Complex.exp ( 2 * Real.pi * Complex.I / 2 ^ k );
  · convert Complex.isPrimitiveRoot_exp _ _ using 2 ; norm_num;
    norm_num;
  · rw [ ← Complex.exp_neg ] ; ring

-- PROVING CONGRUENCE TO MATHLIB DFT OVER ℂ
theorem complex_fft_eq_mathlib_dft (k : ℕ) (x : Vector ℂ (2^k)) :
    haveI : NeZero (2^k) := Nat.instNeZeroHPow
    convert_vector_to_zmod (fft (F := ℂ) x (ZETA k) (ZETA_prim k)).ret
    = ZMod.dft (convert_vector_to_zmod x) := by
  -- Prove that the FFT of a vector is equal to the DFT of the same vector.
  have h_fft_dft : (fft x (ZETA k) (ZETA_prim k)).ret = (dft x (ZETA k) (ZETA_prim k)) := by
    exact?;
  ext m;
  rw [ h_fft_dft, ZMod.dft_apply ];
  simp +decide [ convert_vector_to_zmod, dft ];
  -- By definition of exponentiation in the complex numbers, we can rewrite the right-hand side of the equation.
  have h_exp : ∀ j : ZMod (2 ^ k), (ZETA k) ^ (j.val * m.val) = ZMod.stdAddChar (-(j * m)) := by
    intro j
    have h_exp : (ZETA k) ^ (j.val * m.val) = Complex.exp (-(2 * Real.pi * Complex.I) * (j.val * m.val) / (2 ^ k : ℂ)) := by
      rw [ ZETA ];
      rw [ ← Complex.exp_nat_mul ] ; push_cast ; ring;
    have h_exp : ZMod.stdAddChar (-(j * m)) = Complex.exp (2 * Real.pi * Complex.I * (-(j * m)).val / (2 ^ k : ℂ)) := by
      convert ZMod.stdAddChar_apply ( - ( j * m ) ) using 1;
      rw [ ZMod.toCircle_apply ];
      norm_cast;
    -- Since $-(j * m).val \equiv -(j.val * m.val) \pmod{2^k}$, we can conclude that the exponents are equal.
    have h_exp_eq : (-(j * m)).val ≡ -(j.val * m.val) [ZMOD 2 ^ k] := by
      erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
    rw [ h_exp, ‹ZETA k ^ ( j.val * m.val ) = Complex.exp _› ];
    rw [ Complex.exp_eq_exp_iff_exists_int ];
    obtain ⟨ n, hn ⟩ := h_exp_eq.symm.dvd;
    use -n;
    field_simp;
    norm_cast at *;
    grind;
  refine' Finset.sum_bij ( fun j _ => j ) _ _ _ _ <;> simp +decide [ h_exp ];
  · simp +decide [ Fin.ext_iff, ZMod.natCast_eq_natCast_iff' ];
    exact fun a₁ a₂ h => Nat.mod_eq_of_lt a₁.2 ▸ Nat.mod_eq_of_lt a₂.2 ▸ h;
  · intro b; use ⟨ b.val, by
      convert b.val_lt ⟩ ; simp +decide [ ZMod.natCast_zmod_val ] ;
  · intro a; specialize h_exp a; simp_all +decide [ mul_comm, Nat.mod_eq_of_lt ] ;
    ring


-- joint aristotle + claude from this point forwards
-- (initial aristotle-generated attempt with claude revisions)

/-
Time of t_table
-/
private lemma t_table_time_eq {F : Type*} [Field F] (n : ℕ) (OMEGA : F) :
    (t_table n OMEGA).time = 2 * n + 1 := by
  by_contra h_contra;
  unfold t_table at h_contra;
  contrapose! h_contra;
  induction' n with n ih <;> simp_all +decide [ Nat.pow_succ', Nat.mul_succ, List.range'_concat ];
  convert congr_arg ( · + 2 ) ih using 1 ; ring!;
  induction' ( List.range' 0 n ).attach using List.reverseRecOn with x xs ih <;> simp_all +decide [ List.foldlM ]
-- Exact time recurrence for fft

def fft_time_formula : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * fft_time_formula k + 7 * 2 ^ k + 3

private lemma fft_time_eq {F : Type*} [Field F] {k : ℕ}
    (x : Vector F (2 ^ k)) (OMEGA : F) (h_OMEGA : IsPrimitiveRoot OMEGA (2 ^ k)) :
    (fft x OMEGA h_OMEGA).time = fft_time_formula k := by
  revert x;
  induction' k with k ih generalizing OMEGA;
  · aesop;
  · intro x
    simp [fft, tick];
    rw [ show ( List.range' 0 ( 2 ^ k ) ).attach = List.map ( fun i : Fin ( 2 ^ k ) => ⟨ i, by simp +decide ⟩ ) ( List.finRange ( 2 ^ k ) ) from ?_ ];
    · rw [ show ( t_table ( 2 ^ k ) OMEGA ).time = 2 * 2 ^ k + 1 from t_table_time_eq _ _ ] ; simp +arith +decide [ *, Nat.pow_succ' ];
      rw [ show ( List.foldlM _ _ _ : TimeM ℕ _ ).time = List.sum ( List.map ( fun _ => 1 ) ( List.finRange ( 2 ^ k ) ) ) from ?_ ] ; simp +arith +decide [ *, Nat.pow_succ' ];
      · rfl;
      · induction' ( List.finRange ( 2 ^ k ) ) using List.reverseRecOn with l ih <;> simp +decide [ * ];
    · refine' List.ext_get _ _ <;> aesop
/-
Lower bound: fft_time_formula k ≥ k * 2^k for k ≥ 1
-/
private lemma fft_time_lower (k : ℕ) (hk : k ≥ 1) :
    k * 2 ^ k ≤ fft_time_formula k := by
  induction' hk with k hk ih <;> simp +arith +decide [ *, pow_succ' ];
  grind +locals
/-
Upper bound: fft_time_formula k ≤ 10 * k * 2^k for k ≥ 1
-/
private lemma fft_time_upper (k : ℕ) (hk : k ≥ 1) :
    fft_time_formula k ≤ 10 * k * 2 ^ k := by
  induction' k with k ih <;> norm_num [ Nat.pow_succ', mul_assoc ] at *;
  by_cases hk : 1 ≤ k <;> simp_all +decide [ Nat.pow_succ', mul_assoc ];
  rw [ show fft_time_formula ( k + 1 ) = 2 * fft_time_formula k + 7 * 2 ^ k + 3 by rfl ] ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) k ]

open Nat (clog)

theorem fft_big_Theta {F : Type*} [Field F] {k : ℕ}
    (x : Vector F (2 ^ k)) (OMEGA : F) (h_OMEGA : IsPrimitiveRoot OMEGA (2 ^ k)) :
    let K := 2 ^ k
    (Nat.clog 2 K) * K ≤ (fft x OMEGA h_OMEGA).time ∧
    (fft x OMEGA h_OMEGA).time ≤ 10 * (Nat.clog 2 K) * K := by
  intro K
  rw [fft_time_eq x OMEGA h_OMEGA]
  show Nat.clog 2 (2 ^ k) * 2 ^ k ≤ fft_time_formula k ∧
       fft_time_formula k ≤ 10 * Nat.clog 2 (2 ^ k) * 2 ^ k
  rw [Nat.clog_pow 2 k (by omega)]
  constructor
  · rcases k with _ | k
    · rfl
    · exact fft_time_lower _ (by omega)
  · rcases k with _ | k
    · rfl
    · exact fft_time_upper _ (by omega)

end Cslib.Algorithms.Lean.TimeM
