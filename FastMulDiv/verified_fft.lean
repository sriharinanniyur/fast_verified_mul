-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> and Claude Opus 4.7
-- Most lemmas in this file are Aristotle-written. A few are written by Claude.
-- Assume by default that a given lemma is Aristotle. We have tried to label
-- Claude's work wherever it appears.

import Mathlib
import Cslib.Algorithms.Lean.TimeM

set_option linter.style.whitespace false
set_option linter.style.emptyLine false

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM.FFT

open Finset BigOperators Cslib.Algorithms.Lean.TimeM
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
      have hi : i < K_pred := h.2.1
      let p : F := X[i]
      let q : F := T[i] * Y[i]
      result := result.set i (p + q) (by omega)
      result := result.set (i + K_pred) (p - q) (by omega)
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

/-
Helper: characterize the butterfly loop
-/
-- aristotle + claude
private lemma fft_butterfly_loop {F : Type*} [Field F] {k' : ℕ}
    (x : Vector F (2^(k'+1))) (ω : F) (hω : IsPrimitiveRoot ω (2^(k'+1))) :
    (fft x ω hω).ret =
    let X := (fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val])
                  (ω^2) (prim_root_mul_self hω)).ret
    let Y := (fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1])
                  (ω^2) (prim_root_mul_self hω)).ret
    let T := (t_table (2^k') ω).ret
    Vector.ofFn (fun i : Fin (2^(k'+1)) =>
      if h : i.val < 2^k' then
        X[i.val]'h + T[i.val]'h * Y[i.val]'h
      else
        have hh : i.val - 2^k' < 2^k' := by
          have := i.2; grind
        X[i.val - 2^k']'hh - T[i.val - 2^k']'hh * Y[i.val - 2^k']'hh) := by
  simp +decide [fft, ret_bind, ret_pure, ret_foldlM_TimeM]
  set X : Vector F (2^k') :=
    (fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]) (ω^2)
      (prim_root_mul_self hω)).ret with hX
  set Y : Vector F (2^k') :=
    (fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]) (ω^2)
      (prim_root_mul_self hω)).ret with hY
  set T : Vector F (2^k') := (t_table (2^k') ω).ret with hT
  ext i hi
  simp [Vector.getElem_ofFn]
  by_cases hi' : i < 2 ^ k'
  · rw [dif_pos hi']
    have h_foldl : ∀ l : List {x // x ∈ List.range' 0 (2^k')},
        i ∈ List.map Subtype.val l →
        (List.foldl (fun (b : Vector F (2^(k'+1))) (x_1 : {x // x ∈ List.range' 0 (2^k')}) =>
          have hx1 : x_1.val < 2^k' := by
            have := x_1.2; simp [List.mem_range'] at this; omega
          (b.set x_1.val
              (X[x_1.val] + T[x_1.val] * Y[x_1.val])
              (by omega)).set
            (x_1.val + 2^k')
            (X[x_1.val] - T[x_1.val] * Y[x_1.val])
            (by omega))
          (Vector.replicate (2^(k'+1)) 0) l)[i] = X[i] + T[i] * Y[i] := by
      intro l hl
      induction l using List.reverseRecOn with
      | nil => simp at hl
      | append_singleton xs y ih =>
        simp_all [List.foldl_append, Vector.getElem_set]
        split_ifs <;> grind
    apply h_foldl; simp [List.mem_range']; omega
  · rw [dif_neg hi']
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2^k' := ⟨i - 2^k', by omega⟩
    have hj : j < 2^k' := by have := hi; rw [pow_succ] at this; omega
    have h_foldl : ∀ l : List {x // x ∈ List.range' 0 (2^k')},
        j ∈ List.map Subtype.val l →
        (List.foldl (fun (b : Vector F (2^(k'+1))) (x_1 : {x // x ∈ List.range' 0 (2^k')}) =>
          have hx1 : x_1.val < 2^k' := by
            have := x_1.2; simp [List.mem_range'] at this; omega
          (b.set x_1.val
              (X[x_1.val] + T[x_1.val] * Y[x_1.val])
              (by omega)).set
            (x_1.val + 2^k')
            (X[x_1.val] - T[x_1.val] * Y[x_1.val])
            (by omega))
          (Vector.replicate (2^(k'+1)) 0) l)[j + 2^k'] = X[j] - T[j] * Y[j] := by
      intro l hl
      induction l using List.reverseRecOn with
      | nil => simp at hl
      | append_singleton xs y ih =>
        have hy : y.val < 2^k' := by
          have := y.2; simp [List.mem_range'] at this; omega
        simp_all [List.foldl_append, Vector.getElem_set]
        split_ifs <;> grind
    convert h_foldl _ ?_ using 2
    all_goals first | omega | (simp [List.mem_range'])
    grind
/-
Base case
-/
private lemma fft_eq_dft_base {F : Type*} [Field F]
    (x : Vector F (2^0)) (ω : F) (hω : IsPrimitiveRoot ω (2^0)) :
    (fft x ω hω).ret = dft x ω hω := by
  -- Since $k = 0$, the FFT and DFT are both the identity function, so they are equal.
  simp [fft, dft];
  grind
/-
Inductive step: low half
-/
private lemma fft_eq_dft_low {F : Type*} [Field F] {k' : ℕ}
    (x : Vector F (2^(k'+1))) (ω : F) (hω : IsPrimitiveRoot ω (2^(k'+1)))
    (i : Fin (2^k'))
    (E_dft : Vector F (2^k'))
    (O_dft : Vector F (2^k'))
    (hE : ∀ j : Fin (2^k'), E_dft[j] = ∑ m : Fin (2^k'), x[2 * m.val] * (ω^2) ^ (m.val * j.val))
    (hO : ∀ j : Fin (2^k'), O_dft[j] = ∑ m : Fin (2^k'), x[2 * m.val + 1] * (ω^2) ^ (m.val * j.val)) :
    E_dft[i.val] + ω ^ i.val * O_dft[i.val] =
    ∑ j : Fin (2^(k'+1)), x[j] * ω ^ (j.val * i.val) := by
  convert ( dft_split_sum x ω i ) |> Eq.symm using 1;
  aesop
/-
Inductive step: high half
-/
private lemma fft_eq_dft_high {F : Type*} [Field F] {k' : ℕ}
    (x : Vector F (2^(k'+1))) (ω : F) (hω : IsPrimitiveRoot ω (2^(k'+1)))
    (i : Fin (2^(k'+1))) (hi : ¬ i.val < 2^k')
    (E_dft : Vector F (2^k'))
    (O_dft : Vector F (2^k'))
    (hE : ∀ j : Fin (2^k'), E_dft[j] = ∑ m : Fin (2^k'), x[2 * m.val] * (ω^2) ^ (m.val * j.val))
    (hO : ∀ j : Fin (2^k'), O_dft[j] = ∑ m : Fin (2^k'), x[2 * m.val + 1] * (ω^2) ^ (m.val * j.val)) :
    E_dft[i.val - 2^k'] - ω ^ (i.val - 2^k') * O_dft[i.val - 2^k'] =
    ∑ j : Fin (2^(k'+1)), x[j] * ω ^ (j.val * i.val) := by
  rw [ eq_comm ];
  convert dft_split_sum_high x ω hω i hi using 1;
  rw [ Nat.mod_eq_sub_mod ];
  · rw [ Nat.mod_eq_of_lt ];
    · convert congr_arg₂ _ ( hE ⟨ i - 2 ^ k', _ ⟩ ) ( congr_arg _ ( hO ⟨ i - 2 ^ k', _ ⟩ ) ) using 1;
      · bv_omega;
      · rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt i, pow_succ' 2 k' ];
    · rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt i, pow_succ' 2 k' ];
  · exact le_of_not_gt hi
/-
FFT CORRECTNESS THEOREM
-/
theorem fft_eq_dft
    {F : Type*} [Field F]
    {k : ℕ}
    (x : Vector F (2^k))
    (ω : F)
    (hω : IsPrimitiveRoot ω (2^k))
    : (fft x ω hω).ret = dft x ω hω := by
  revert x ω hω;
  induction' k with k ih;
  · exact?;
  · intro x ω hω
    rw [ fft_butterfly_loop ];
    refine' Vector.ext fun i => _;
    intro hi;
    by_cases hi' : i < 2 ^ k <;> simp_all +decide [ Vector.getElem_ofFn ];
    · convert fft_eq_dft_low x ω hω ⟨ i, hi' ⟩ _ _ _ _ using 1;
      congr! 1;
      congr! 1;
      · exact t_table_get _ _ ⟨ i, hi' ⟩;
      · unfold dft; aesop;
      · unfold dft; aesop;
      · simp +decide [ dft ];
    · split_ifs <;> simp_all +decide [ dft ];
      · linarith;
      · convert fft_eq_dft_high x ω hω ⟨ i, hi ⟩ ( by aesop ) ( Vector.ofFn fun j : Fin ( 2 ^ k ) => ∑ m : Fin ( 2 ^ k ), x[2 * m.val] * ( ω ^ 2 ) ^ ( m.val * j.val ) ) ( Vector.ofFn fun j : Fin ( 2 ^ k ) => ∑ m : Fin ( 2 ^ k ), x[2 * m.val + 1] * ( ω ^ 2 ) ^ ( m.val * j.val ) ) _ _ using 1 <;> simp +decide [ t_table_get ];
        exact Or.inl ( t_table_get _ _ ⟨ i - 2 ^ k, by rw [ pow_succ' ] at hi; omega ⟩ )



/-- The vector returned by `t_table n OMEGA` has `i`-th entry `OMEGA^i`. -/
private lemma t_table_ret_eq {F : Type*} [Field F] (n : ℕ) (OMEGA : F) :
    (t_table n OMEGA).ret = Vector.ofFn (fun j : Fin n => OMEGA ^ j.val) := by
  refine Vector.ext fun i hi => ?_
  simp
  exact t_table_get n OMEGA ⟨i, hi⟩


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
    ∃ (c1 c2 : ℕ),
      c1 ≥ 1
      ∧ c1 * (clog 2 K) * K ≤ (fft x OMEGA h_OMEGA).time
      ∧ c2 ≥ 1
      ∧ (fft x OMEGA h_OMEGA).time ≤ c2 * (clog 2 K) * K
      := by
  have ht := fft_time_eq x OMEGA h_OMEGA
  refine ⟨1, 10, by omega, ?_, by omega, ?_⟩
  all_goals rw [ht, Nat.clog_pow 2 k (by omega)]
  all_goals rcases k with _ | k
  · rfl
  · rw [one_mul]; exact fft_time_lower _ (by omega)
  · rfl
  · exact fft_time_upper _ (by omega)

end Cslib.Algorithms.Lean.TimeM.FFT
