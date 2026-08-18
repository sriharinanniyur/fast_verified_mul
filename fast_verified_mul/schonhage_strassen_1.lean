-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-- with some snippets written by Opus 4.8
import Mathlib

set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option maxHeartbeats 3200000

section SSADefs

/-!
# Definitions for the SSA multiplication algorithm

This file contains all the type definitions, helper functions, and
proved algebraic lemmas used by the SSA algorithm.
-/

structure FPComplex (P : ℕ) where
  re : ℤ
  im : ℤ

namespace FPComplex

variable {P : ℕ}

def shr_round (v : ℤ) (P : ℕ) : ℤ :=
  if P = 0 then v else (v + 2^(P-1)) >>> P

def cmul (a b : FPComplex P) : FPComplex P :=
  ⟨shr_round (a.re * b.re - a.im * b.im) P,
   shr_round (a.re * b.im + a.im * b.re) P⟩

def cadd (a b : FPComplex P) : FPComplex P := ⟨a.re + b.re, a.im + b.im⟩
def csub (a b : FPComplex P) : FPComplex P := ⟨a.re - b.re, a.im - b.im⟩

noncomputable def twiddle (j K : ℕ) (inv : Bool) (P : ℕ) : FPComplex P :=
  let ang : ℝ := (if inv then -1 else 1) * 2 * Real.pi * j / K
  ⟨round (Real.cos ang * (2 : ℝ)^P),
   round (Real.sin ang * (2 : ℝ)^P)⟩

noncomputable def t_table (K_pred : ℕ) (inv : Bool) (P : ℕ) :
    Vector (FPComplex P) K_pred :=
  Vector.ofFn fun j : Fin K_pred => twiddle j.val (2 * K_pred) inv P

/-- Complex multiplication with a parameterized integer multiplication function.
    When `mul_fn = (· * ·)`, this equals `cmul`. -/
def cmul_via (mul_fn : ℤ → ℤ → ℤ) (a b : FPComplex P) : FPComplex P :=
  ⟨shr_round (mul_fn a.re b.re - mul_fn a.im b.im) P,
   shr_round (mul_fn a.re b.im + mul_fn a.im b.re) P⟩

/-- FFT with a parameterized integer multiplication function.
    Uses `cmul_via mul_fn` for all butterfly twiddle multiplications.
    When `mul_fn = (· * ·)`, this equals `fft`. -/
noncomputable def FFT
    (mul_fn : ℤ → ℤ → ℤ)
    {k : ℕ}
    (x : Vector (FPComplex P) (2^k))
    (inv : Bool)
    : Vector (FPComplex P) (2^k) :=
  match k with
  | 0      => x
  | k' + 1 => Id.run do
    let K_pred := 2 ^ k'
    let K := 2 ^ (k' + 1)
    let E : Vector (FPComplex P) K_pred :=
      Vector.ofFn fun j : Fin K_pred => x[2 * j.val]'(by omega)
    let O : Vector (FPComplex P) K_pred :=
      Vector.ofFn fun j : Fin K_pred => x[2 * j.val + 1]'(by omega)
    let E' := FFT mul_fn E inv
    let O' := FFT mul_fn O inv
    let T := t_table K_pred inv P

    let mut result := Vector.replicate K {re := 0, im := 0}
    for h : j in [0:K_pred] do
      have hj : j < K_pred := h.2.1
      let p := E'[j]
      let q:= cmul_via mul_fn T[j] O'[j]
      result := result.set j           (cadd p q) (by omega)
      result := result.set (j + K_pred)    (csub p q) (by omega)
    return result

-- pure functional version (proof aid)
noncomputable def fft {k : ℕ} (x : Vector (FPComplex P) (2^k)) (inv : Bool) :
    Vector (FPComplex P) (2^k) :=
  match k with
  | 0 => x
  | k' + 1 =>
    let K_pred := 2 ^ k'
    let E : Vector (FPComplex P) K_pred :=
      Vector.ofFn fun j : Fin K_pred => x[2 * j.val]'(by omega)
    let O : Vector (FPComplex P) K_pred :=
      Vector.ofFn fun j : Fin K_pred => x[2 * j.val + 1]'(by omega)
    let E' := fft E inv
    let O' := fft O inv
    let T := t_table K_pred inv P
    Vector.ofFn fun i : Fin (2^(k'+1)) =>
      if h : i.val < K_pred then
        cadd (E'.get ⟨i.val, h⟩) (cmul (T.get ⟨i.val, h⟩) (O'.get ⟨i.val, h⟩))
      else
        csub (E'.get ⟨i.val - K_pred, by omega⟩)
             (cmul (T.get ⟨i.val - K_pred, by omega⟩) (O'.get ⟨i.val - K_pred, by omega⟩))


@[simp] lemma cmul_via_mul (a b : FPComplex P) : cmul_via (· * ·) a b = cmul a b := rfl

/-- A `Vector`-valued `for` loop over `[0:n]` that writes index `j` and index `j + n`
    on each iteration produces exactly the `Vector.ofFn` of the two write functions. -/
theorem loop_eq {β : Type*} (n N : ℕ) (lo hi : (j : ℕ) → j < n → β)
    (hlo : ∀ j (hj : j < n), j < N) (hhi : ∀ j (hj : j < n), j + n < N) (init : β) :
    (Id.run do
      let mut result := Vector.replicate N init
      for h : j in [0:n] do
        have hj : j < n := h.2.1
        result := result.set j (lo j hj) (hlo j hj)
        result := result.set (j + n) (hi j hj) (hhi j hj)
      return result)
    = Vector.ofFn (fun i : Fin N =>
        if h : i.val < n then lo i.val h
        else if h2 : i.val - n < n ∧ n ≤ i.val then hi (i.val - n) h2.1
        else init) := by
  classical
  set gtot : ℕ → β := fun a => if h : a < n then lo a h else init with hgtot
  set htot : ℕ → β := fun a => if h : a < n then hi a h else init with hhtot
  simp only [Id.run, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind, bind_pure,
    List.forIn'_pure_yield_eq_foldl]
  set g0 : Vector β N → ℕ → Vector β N := fun b a =>
    if h : a < n then (b.set a (gtot a) (hlo a h)).set (a + n) (htot a) (hhi a h) else b with hg0
  rw [List.foldl_subtype (g := g0), List.unattach_attach]
  show List.foldl g0 (Vector.replicate N init) (List.range' 0 n) =
      Vector.ofFn (fun i : Fin N =>
        if h : i.val < n then lo i.val h
        else if h2 : i.val - n < n ∧ n ≤ i.val then hi (i.val - n) h2.1
        else init)
  · have key : ∀ (l : List ℕ), (∀ a ∈ l, a < n) → ∀ (acc : Vector β N) (i : ℕ) (hi' : i < N),
        (List.foldl g0 acc l)[i]'hi' =
          if i ∈ l then gtot i
          else if (i - n) ∈ l ∧ n ≤ i then htot (i - n) else acc[i]'hi' := by
      intro l
      induction l with
      | nil => intro _ acc i hi'; simp
      | cons a t ih =>
        intro hlt acc i hi'
        have ha : a < n := hlt a (List.mem_cons_self ..)
        simp only [List.foldl_cons]
        rw [ih (fun x hx => hlt x (List.mem_cons_of_mem _ hx))]
        simp only [hg0, ha, dif_pos]
        rw [Vector.getElem_set, Vector.getElem_set]
        simp only [List.mem_cons]
        grind
    apply Vector.ext
    intro i hi'
    rw [Vector.getElem_ofFn, key _ (by intro a ha; simpa [List.mem_range'] using ha)]
    have c1 : (i ∈ List.range' 0 n) ↔ i < n := by simp
    have c2 : (i - n ∈ List.range' 0 n) ↔ i - n < n := by simp
    simp only [c1, c2, Vector.getElem_replicate, hgtot, hhtot]
    grind
  · intro b x hx
    have hxn : x < n := by simpa [List.mem_range'] using hx
    simp only [hg0, hgtot, hhtot, dif_pos hxn]

/-
Characterization of the do-notation `FFT` at the successor step: the imperative
    loop produces exactly the `Vector.ofFn` butterfly form.
-/
lemma FFT_succ (mul_fn : ℤ → ℤ → ℤ) {k' : ℕ}
    (x : Vector (FPComplex P) (2^(k'+1))) (inv : Bool) :
    FFT mul_fn x inv =
      (Vector.ofFn fun i : Fin (2^(k'+1)) =>
        if h : i.val < 2 ^ k' then
          cadd ((FFT mul_fn (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get ⟨i.val, h⟩)
               (cmul_via mul_fn ((t_table (2^k') inv P).get ⟨i.val, h⟩)
                                ((FFT mul_fn (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get ⟨i.val, h⟩))
        else
          csub ((FFT mul_fn (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get ⟨i.val - 2^k', by omega⟩)
               (cmul_via mul_fn ((t_table (2^k') inv P).get ⟨i.val - 2^k', by omega⟩)
                                ((FFT mul_fn (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get ⟨i.val - 2^k', by omega⟩))) := by
  rw [ FFT ];
  convert loop_eq ( 2 ^ k' ) ( 2 ^ ( k' + 1 ) ) _ _ ( fun j hj => by omega ) ( fun j hj => by omega ) _ using 1;
  rotate_left;
  rotate_left;
  exact fun j hj => ( FFT mul_fn ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val] ) inv ).get ⟨ j, hj ⟩ |> fun p => p.cadd ( cmul_via mul_fn ( t_table ( 2 ^ k' ) inv P |> Vector.get <| ⟨ j, hj ⟩ ) ( FFT mul_fn ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val + 1] ) inv |> Vector.get <| ⟨ j, hj ⟩ ) );
  exact fun j hj => ( FFT mul_fn ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val] ) inv ).get ⟨ j, hj ⟩ |> fun p => p.csub ( cmul_via mul_fn ( t_table ( 2 ^ k' ) inv P |> Vector.get <| ⟨ j, hj ⟩ ) ( FFT mul_fn ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val + 1] ) inv |> Vector.get <| ⟨ j, hj ⟩ ) );
  exact ⟨ 0, 0 ⟩;
  · simp +decide [ Vector.get ];
  · grind

lemma FFT_mul_eq_fft {k : ℕ} (x : Vector (FPComplex P) (2^k)) (inv : Bool) :
    FFT (· * ·) x inv = fft x inv := by
  induction' k with k ih generalizing inv
  · rfl
  · rw [FFT_succ, fft]
    simp only [← ih, cmul_via_mul]

def ofInt (n : ℤ) : FPComplex P := ⟨n * 2^P, 0⟩

def round_re (a : FPComplex P) : ℤ :=
  if P = 0 then a.re else (a.re + 2^(P-1)) >>> P

end FPComplex

def bits (x : ℤ) : ℕ := Nat.log 2 x.natAbs + 1

/-- The concrete choice of FFT parameters `l` and `n` used by `ssa`.

    `l = clog 2 N` is the per-digit bit width and
    `n = clog 2 (⌈2N / l⌉)` gives the transform size `K = 2 ^ n`.

    This replaces the earlier existential `exist_n_l`: because `n` and `l` are now
    chosen concretely, the relevant facts are packaged here. The crucial
    no-aliasing bound `l * 2 ^ n ≥ 2 * N` is what makes the FFT convolution
    compute the *linear* (not merely circular) convolution, hence the product.

    Note: the divisor uses **ceiling** division `(2 * N + l - 1) / l` rather than
    floor `(2 * N) / l`.  With floor division the bound `l * 2 ^ n ≥ 2 * N` fails
    for infinitely many `N` (the smallest being `N = 113`), which would make the
    algorithm incorrect; ceiling division restores it for every `N > 64`. -/
lemma ssa_params (N : ℕ) (hN : 64 < N) :
    let l := Nat.clog 2 N
    let n := Nat.clog 2 ((2 * N + l - 1) / l)
    n ≥ 1 ∧ l ≥ 1 ∧ l * 2 ^ n ≥ 2 * N ∧ l ≤ N := by
  intro l n
  have hlN : l ≤ N := by
    have h : N ≤ 2^N := Nat.le_of_lt Nat.lt_two_pow_self
    exact (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).2 h
  have hl1 : l ≥ 1 := by
    show 0 < Nat.clog 2 N
    exact Nat.clog_pos (by norm_num) (by omega)
  have hldvd : l * ((2*N + l - 1)/l) ≥ 2*N := by
    have h := Nat.div_add_mod (2*N + l - 1) l
    have hmod : (2*N + l - 1) % l < l := Nat.mod_lt _ (by omega)
    omega
  have hm2 : 2 ≤ (2*N + l - 1)/l := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < l)]; omega
  have hn1 : n ≥ 1 := by
    show 0 < Nat.clog 2 ((2*N + l - 1)/l)
    exact Nat.clog_pos (by norm_num) (by omega)
  have hpow : ((2*N + l - 1)/l) ≤ 2 ^ n := Nat.le_pow_clog (by norm_num) _
  refine ⟨hn1, hl1, ?_, hlN⟩
  calc 2 * N ≤ l * ((2*N + l - 1)/l) := hldvd
    _ ≤ l * 2^n := Nat.mul_le_mul_left l hpow

/-
For all `N > 64` the transform size exponent `n = clog 2 (⌈2N/l⌉)` is at least 5.
    This holds because `l = clog 2 N ≤ N/8` for `N > 64`, so `(2N+l-1)/l ≥ 17` and
    hence its base-2 ceiling logarithm is at least 5.
-/
lemma ssa_params_n5 (N : ℕ) (hN : 64 < N) :
    Nat.clog 2 ((2 * N + Nat.clog 2 N - 1) / Nat.clog 2 N) ≥ 5 := by
  by_contra h_contra;
  -- By definition of $l$, we know that $l \geq 7$.
  have hl_ge_7 : 7 ≤ Nat.clog 2 N := by
    exact Nat.le_trans ( by native_decide ) ( Nat.clog_mono_right 2 hN );
  -- By definition of $l$, we know that $8 * l \leq 2^{l-1}$.
  have hl_le_2_pow : 8 * Nat.clog 2 N ≤ 2 ^ (Nat.clog 2 N - 1) := by
    exact Nat.le_induction ( by native_decide ) ( fun k hk ih ↦ by rcases k with ( _ | _ | _ | _ | _ | _ | _ | k ) <;> norm_num [ Nat.pow_succ' ] at * ; linarith ) _ hl_ge_7;
  -- By definition of $l$, we know that $2^{l-1} < N$.
  have hl_lt_N : 2 ^ (Nat.clog 2 N - 1) < N := by
    rw [ ← Nat.lt_clog_iff_pow_lt ] <;> norm_num;
    grind +revert;
  exact h_contra <| Nat.le_trans ( by native_decide ) ( Nat.clog_mono_right 2 <| show ( 2 * N + Nat.clog 2 N - 1 ) / Nat.clog 2 N ≥ 17 by exact Nat.le_div_iff_mul_le ( by linarith ) |>.2 <| by omega )

/-- Fixed-point precision used by `ssa`. -/
def knuth_bound (n l : ℕ) : ℕ := 4 * n + 2 * l

def decompose_digit (x : ℕ) (l K j : ℕ) : ℤ :=
  let shift := l * (if j < K - 1 then j else K - 1)
  if j < K - 1 then ((x >>> shift) &&& ((1 <<< l) - 1) : ℕ)
  else (x >>> shift : ℕ)

def recompose {K : ℕ} (l : ℕ) (c : Fin K → ℤ) : ℤ :=
  ∑ j : Fin K, c j * 2^(l * j.val)

def base_threshold : ℕ := 64

/-! ## Algebraic helper lemmas (all proved) -/

/-- Sign × absolute values = product -/
lemma sign_mul_natAbs (a b : ℤ) :
    a.sign * b.sign * (↑a.natAbs * ↑b.natAbs : ℤ) = a * b := by
  simp only [Int.natCast_natAbs]
  have h1 : a.sign * b.sign * (|a| * |b|) = (a.sign * |a|) * (b.sign * |b|) := by ring
  rw [h1, Int.sign_mul_abs, Int.sign_mul_abs]

/-- Recomposing the digit decomposition recovers the original number -/
lemma decompose_recompose (x : ℕ) (l : ℕ) (K : ℕ) (hl : l ≥ 1) (hK : K ≥ 1) :
    recompose l (fun j : Fin K => decompose_digit x l K j.val) = ↑x := by
  induction' hK with K hK ih generalizing x <;>
    simp_all +decide [Nat.shiftRight_add, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq_mul_pow]
  · unfold recompose decompose_digit; aesop
  · unfold recompose decompose_digit
    simp +decide [Fin.sum_univ_succ, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    convert congr_arg (fun y : ℤ => (x % 2 ^ l + 2 ^ l * y)) (ih (x / 2 ^ l)) using 1
    · unfold recompose decompose_digit
      simp +decide [Fin.sum_univ_succ, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
      rw [Finset.mul_sum _ _ _]
      rcases K with (_ | K) <;>
        simp_all +decide [Nat.succ_eq_add_one, pow_add, pow_mul, Nat.div_div_eq_div_mul]
      norm_cast
      simp +decide [Nat.div_div_eq_div_mul, mul_assoc, mul_comm, mul_left_comm]
    · exact_mod_cast Eq.symm (Nat.mod_add_div _ _)

/-- Distributing the product of two polynomial evaluations -/
lemma recompose_mul_expand {K : ℕ} (l : ℕ) (A B : Fin K → ℤ) :
    recompose l A * recompose l B =
    ∑ j : Fin K, ∑ k : Fin K, A j * B k * (2 : ℤ)^(l * (j.val + k.val)) := by
  simp +decide [recompose, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm,
    pow_add, pow_mul]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

/-- When digit sequences have support in [0, K/2), circular convolution
    equals linear convolution (no aliasing). -/
lemma circular_eq_linear_convolution {K : ℕ} (l : ℕ)
    (A B : Fin K → ℤ)
    (hA_support : ∀ j : Fin K, K / 2 ≤ j.val → A j = 0)
    (hB_support : ∀ j : Fin K, K / 2 ≤ j.val → B j = 0) :
    recompose l A * recompose l B =
    recompose l (fun m : Fin K => ∑ j : Fin K, ∑ k : Fin K,
      if (j.val + k.val) % K = m.val then A j * B k else 0) := by
  convert recompose_mul_expand l A B using 1
  have h_no_wrap : ∀ j k : Fin K, j.val < K / 2 → k.val < K / 2 →
      (j.val + k.val) % K = j.val + k.val := by
    exact fun j k hj hk => Nat.mod_eq_of_lt (by linarith [Nat.div_mul_le_self K 2])
  simp +decide only [recompose]
  simp +decide only [Finset.sum_mul _ _ _]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_comm, Finset.sum_congr rfl]
  intro k hk
  by_cases hjk : j.val < K / 2 <;> by_cases hjk' : k.val < K / 2 <;>
    simp_all +decide [Finset.sum_ite]
  rw [Finset.sum_eq_single ⟨j + k, by linarith [Nat.div_mul_le_self K 2]⟩] <;> aesop

/-- Right-shifting a number beyond its bit width gives zero. -/
lemma shift_large_zero (x : ℕ) (N s : ℕ) (hx : x < 2^N) (hs : N ≤ s) :
    x >>> s = 0 := by
  exact Nat.shiftRight_eq_div_pow x s ▸
    Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hs))

/-- The digit decomposition has support in [0, K/2) -/
lemma decompose_digit_support (x : ℕ) (l K : ℕ) (N : ℕ)
    (hx : x < 2^N) (hlK : l * K ≥ 2 * N) (_hl : l ≥ 1) (hK : K ≥ 2)
    (heven : 2 ∣ K) :
    ∀ j : Fin K, K / 2 ≤ j.val → decompose_digit x l K j.val = 0 := by
  have h_shift : ∀ j : Fin K, K / 2 ≤ j.val → l * j.val ≥ N := by
    exact fun j hj => by nlinarith [Nat.div_mul_cancel heven]
  intros j hj
  have h_shift_j : l * j.val ≥ N := h_shift j hj
  have h_shift_zero : x >>> (l * j.val) = 0 := by
    exact shift_large_zero x N (l * j.val) hx h_shift_j
  unfold decompose_digit
  grind


end SSADefs


/- ========================================================================
   Section: DFTTheory
   ======================================================================== -/

section DFTTheory

/-!
# Discrete Fourier Transform theory

This file develops the algebraic theory of the DFT and proves the
circular convolution theorem, which is the mathematical foundation
for the SSA multiplication algorithm.
-/

open Complex Finset

noncomputable section

/-- The K-th primitive root of unity -/
def omega (K : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / K)

/-- The DFT of a sequence x[0..K-1] -/
def dft (K : ℕ) (x : Fin K → ℂ) (m : Fin K) : ℂ :=
  ∑ j : Fin K, x j * (omega K) ^ (m.val * j.val)

/-- The inverse DFT -/
def idft (K : ℕ) (X : Fin K → ℂ) (j : Fin K) : ℂ :=
  (1 / K) * ∑ m : Fin K, X m * (omega K)⁻¹ ^ (m.val * j.val)

/-- The circular convolution of two sequences -/
def circular_conv (K : ℕ) (a b : Fin K → ℂ) (m : Fin K) : ℂ :=
  ∑ j : Fin K, ∑ k : Fin K,
    if (j.val + k.val) % K = m.val then a j * b k else 0

/-
omega(K) has unit norm
-/
lemma omega_norm (K : ℕ) (hK : K ≥ 1) : ‖omega K‖ = 1 := by
  norm_num [ omega, Complex.norm_exp ]

/-
Sum of roots of unity is zero (for K ≥ 2, non-multiple of K)
-/
lemma sum_roots_of_unity_eq_zero (K : ℕ) (hK : K ≥ 2) (m : ℕ) (hm : ¬ K ∣ m) :
    ∑ j : Fin K, (omega K) ^ (m * j.val) = 0 := by
  -- The sum of the roots of unity is zero when K ≥ 2 and K does not divide m.
  have h_sum_unity : ∑ j ∈ Finset.range K, (Complex.exp (2 * Real.pi * Complex.I * m / K)) ^ j = 0 := by
    rw [ geom_sum_eq ];
    · norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀, show K ≠ 0 by positivity ];
      exact Or.inl ( sub_eq_zero_of_eq <| Complex.exp_eq_one_iff.mpr ⟨ m, by push_cast; ring ⟩ );
    · rw [ Ne.eq_def, Complex.exp_eq_one_iff ];
      simp_all +decide [ Complex.ext_iff, div_eq_iff, Real.pi_ne_zero, show K ≠ 0 by linarith ];
      exact fun x hx => hm <| Int.natCast_dvd_natCast.mp ⟨ x, by rw [ ← @Int.cast_inj ℝ ] ; push_cast; nlinarith [ Real.pi_pos ] ⟩;
  convert h_sum_unity using 1 ; norm_num [ omega, ← Complex.exp_nat_mul, mul_div_assoc, mul_comm ];
  rw [ Finset.sum_range ] ; congr ; ext ; ring;

/-
Orthogonality of roots: ∑_j ω^{mj} · ω^{-nj} = K if m ≡ n (mod K), else 0
-/
lemma roots_orthogonality (K : ℕ) (hK : K ≥ 2) (m n : Fin K) :
    ∑ j : Fin K, (omega K) ^ (m.val * j.val) * ((omega K)⁻¹ ^ (n.val * j.val)) =
    if m = n then (K : ℂ) else 0 := by
  split_ifs with h;
  · simp_all +decide [ ← mul_pow ];
    exact Eq.trans ( Finset.sum_congr rfl fun _ _ => mul_inv_cancel₀ <| pow_ne_zero _ <| Complex.exp_ne_zero _ ) ( by norm_num );
  · -- Since $m \neq n$, we have $m - n \not\equiv 0 \pmod{K}$, so the sum is zero by the properties of roots of unity.
    have h_sum_zero : ∑ j : Fin K, (omega K) ^ ((m.val - n.val : ℤ) * j.val) = 0 := by
      have h_sum_zero : ∑ j : Fin K, (omega K) ^ ((m.val - n.val : ℤ) * j.val) = ∑ j : Fin K, (omega K) ^ ((m.val - n.val : ℤ) % K * j.val) := by
        rw [ ← Int.emod_add_mul_ediv ( m - n ) K ] ; norm_num [ zpow_add₀ ( show omega K ≠ 0 from Complex.exp_ne_zero _ ), zpow_mul ] ;
        norm_num [ omega, ← Complex.exp_nat_mul, mul_div_cancel₀, show K ≠ 0 by linarith ];
      convert sum_roots_of_unity_eq_zero K hK ( Int.natAbs ( ( m - n : ℤ ) % K ) ) _ using 1;
      · convert h_sum_zero using 2;
        rw [ ← Int.natAbs_of_nonneg ( Int.emod_nonneg _ ( by positivity ) ) ] ; norm_cast;
      · rw [ ← Int.natCast_dvd ];
        rw [ Int.dvd_iff_emod_eq_zero ] ; simp_all +decide [ Fin.ext_iff, Int.emod_eq_of_lt ];
        exact fun ⟨ a, ha ⟩ => h <| by nlinarith [ show a = 0 by nlinarith [ Fin.is_lt m, Fin.is_lt n ] ] ;
    convert h_sum_zero using 2 ; norm_num [ zpow_sub₀, zpow_mul, omega ] ; ring

/-
The inverse DFT recovers the original sequence
-/
lemma idft_dft (K : ℕ) (hK : K ≥ 2) (x : Fin K → ℂ) (j : Fin K) :
    idft K (dft K x) j = x j := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ m : Fin K, (∑ r : Fin K, x r * (omega K) ^ (m.val * r.val)) * ((omega K)⁻¹ ^ (m.val * j.val)) = ∑ r : Fin K, x r * (∑ m : Fin K, (omega K) ^ (m.val * r.val) * ((omega K)⁻¹ ^ (m.val * j.val))) := by
    simpa only [ Finset.mul_sum _ _ _, mul_assoc, Finset.sum_mul ] using Finset.sum_comm;
  -- By orthogonality of roots, $\sum_{m=0}^{K-1} \omega^{mr} \omega^{-mj} = K$ if $r = j$ and $0$ otherwise.
  have h_orthog : ∀ r : Fin K, (∑ m : Fin K, (omega K) ^ (m.val * r.val) * ((omega K)⁻¹ ^ (m.val * j.val))) = if r = j then (K : ℂ) else 0 := by
    intro r; convert roots_orthogonality K hK r j using 1;
    ac_rfl;
  simp_all +decide [ Finset.sum_ite, idft, dft ];
  rw [ inv_mul_eq_div, mul_div_cancel_right₀ _ ( Nat.cast_ne_zero.mpr <| ne_bot_of_gt hK ) ]

/-
**Circular convolution theorem**: the DFT of the circular convolution equals
    the pointwise product of the DFTs.
-/
theorem dft_convolution_theorem (K : ℕ) (hK : K ≥ 2)
    (a b : Fin K → ℂ) (m : Fin K) :
    dft K (circular_conv K a b) m = dft K a m * dft K b m := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ r : Fin K, (∑ j : Fin K, ∑ k : Fin K, if (j.val + k.val) % K = r.val then a j * b k else 0) * (omega K) ^ (m.val * r.val) = ∑ j : Fin K, ∑ k : Fin K, (a j * b k) * (omega K) ^ (m.val * (j.val + k.val)) := by
    have h_fubini : ∑ r : Fin K, (∑ j : Fin K, ∑ k : Fin K, if (j.val + k.val) % K = r.val then a j * b k else 0) * (omega K) ^ (m.val * r.val) = ∑ j : Fin K, ∑ k : Fin K, (a j * b k) * ∑ r : Fin K, (if (j.val + k.val) % K = r.val then (omega K) ^ (m.val * r.val) else 0) := by
      simp +decide only [sum_mul];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by aesop ) );
    -- Since $\omega^K = 1$, we have $\omega^{m((j+k)\%K)} = \omega^{m(j+k)}$.
    have h_omega_mod : ∀ j k : Fin K, (omega K) ^ (m.val * ((j.val + k.val) % K)) = (omega K) ^ (m.val * (j.val + k.val)) := by
      norm_num [ omega, ← Complex.exp_nat_mul, mul_div_cancel₀, show K ≠ 0 by linarith ];
      intro j k; rw [ Complex.exp_eq_exp_iff_exists_int ] ; use - ( m.val * ( ( j + k ) / K ) ) ; push_cast [ Nat.mod_def ] ; ring;
      rw [ Nat.cast_sub ( Nat.mul_div_le _ _ ) ] ; push_cast ; ring;
      norm_cast ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_two.trans_le hK ) ];
    rw [ h_fubini ];
    refine' Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => _;
    rw [ Finset.sum_eq_single ⟨ ( j + k ) % K, Nat.mod_lt _ ( by linarith ) ⟩ ] <;> simp +decide [ h_omega_mod j k ];
    exact fun x hx₁ hx₂ => False.elim <| hx₁ <| Fin.ext hx₂.symm;
  convert h_fubini using 1;
  unfold dft; ring;
  simp +decide only [mul_comm, sum_mul, mul_assoc, mul_left_comm];
  simp +decide only [Finset.mul_sum _ _ _, mul_left_comm]

end

end DFTTheory


/- ========================================================================
   Section: SSAHelpers
   ======================================================================== -/

section SSAHelpers

/-!
# Helper lemmas for FFT bounds in SSA multiplication

This file contains helper lemmas for bounding FFT operations,
building toward `fft_output_natAbs_bound` and `fft_convolution_correct`.
-/

namespace FPComplex

/-! ## Bounds on fixed-point operations -/

/-- Integer shift right is floor division -/
lemma int_shr_eq_div (v : ℤ) (n : ℕ) : v >>> n = v / 2^n := by
  exact Int.shiftRight_eq_div_pow v n

/-- shr_round for P > 0 -/
lemma shr_round_pos (v : ℤ) (P : ℕ) (hP : P ≥ 1) :
    shr_round v P = (v + 2^(P-1)) / 2^P := by
  simp [shr_round, show P ≠ 0 by omega]
  rw [int_shr_eq_div]

/-- natAbs bound for addition -/
lemma natAbs_add_le (a b : ℤ) : (a + b).natAbs ≤ a.natAbs + b.natAbs := by
  exact Int.natAbs_add_le a b

/-- natAbs bound for subtraction -/
lemma natAbs_sub_le (a b : ℤ) : (a - b).natAbs ≤ a.natAbs + b.natAbs := by
  exact Int.natAbs_sub_le a b

end FPComplex

/-! ## Bounds on decompose_digit -/

/-
decompose_digit always returns nonneg values
-/
lemma decompose_digit_nonneg (x l K j : ℕ) : 0 ≤ decompose_digit x l K j := by
  unfold decompose_digit;
  grind

/-
The twiddle factor components are bounded by 2^P + 1
-/
lemma twiddle_re_bound (j K : ℕ) (inv : Bool) (P : ℕ) :
    |(FPComplex.twiddle j K inv P : FPComplex P).re| ≤ 2^P + 1 := by
  norm_num [ FPComplex.twiddle ];
  rw [ abs_le ];
  constructor <;> rw [ round_eq ] <;> norm_num [ Int.floor_le, Int.le_floor ];
  · exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.neg_one_le_cos ( ( if inv = true then - ( 2 * Real.pi * j ) else 2 * Real.pi * j ) / K ), Real.cos_le_one ( ( if inv = true then - ( 2 * Real.pi * j ) else 2 * Real.pi * j ) / K ), Int.lt_floor_add_one ( Real.cos ( ( if inv = true then - ( 2 * Real.pi * j ) else 2 * Real.pi * j ) / K ) * 2 ^ P + 1 / 2 ), pow_pos ( zero_lt_two' ℝ ) P ] );
  · exact Int.le_of_lt_add_one ( Int.floor_lt.mpr ( by norm_num; nlinarith [ Real.cos_le_one ( ( if inv = true then - ( 2 * Real.pi * j ) else 2 * Real.pi * j ) / K ), show ( 2 : ℝ ) ^ P > 0 by positivity ] ) )

lemma twiddle_im_bound (j K : ℕ) (inv : Bool) (P : ℕ) :
    |(FPComplex.twiddle j K inv P : FPComplex P).im| ≤ 2^P + 1 := by
  unfold FPComplex.twiddle;
  norm_num [ abs_le, round_eq ];
  constructor <;> exact Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast ; nlinarith [ Real.neg_one_le_sin ( ( if inv = true then - ( 2 * Real.pi * j ) else 2 * Real.pi * j ) / K ), Real.sin_le_one ( ( if inv = true then - ( 2 * Real.pi * j ) else 2 * Real.pi * j ) / K ), Int.floor_le ( Real.sin ( ( if inv = true then - ( 2 * Real.pi * j ) else 2 * Real.pi * j ) / K ) * 2 ^ P + 1 / 2 ), Int.lt_floor_add_one ( Real.sin ( ( if inv = true then - ( 2 * Real.pi * j ) else 2 * Real.pi * j ) / K ) * 2 ^ P + 1 / 2 ), pow_pos ( zero_lt_two' ℝ ) P ] ;

end SSAHelpers


/- ========================================================================
   Section: SSABounds
   ======================================================================== -/

section SSABounds

/-!
# FFT output bounds for SSA multiplication

This file develops bounds on FFT output magnitudes, building toward
`fft_output_natAbs_bound`.
-/

namespace FPComplex

variable {P : ℕ}

/-- Bound on cadd components -/
lemma cadd_natAbs_re_le (a b : FPComplex P) :
    (cadd a b).re.natAbs ≤ a.re.natAbs + b.re.natAbs := by
  simp [cadd]; exact Int.natAbs_add_le _ _

lemma cadd_natAbs_im_le (a b : FPComplex P) :
    (cadd a b).im.natAbs ≤ a.im.natAbs + b.im.natAbs := by
  simp [cadd]; exact Int.natAbs_add_le _ _

/-- Bound on csub components -/
lemma csub_natAbs_re_le (a b : FPComplex P) :
    (csub a b).re.natAbs ≤ a.re.natAbs + b.re.natAbs := by
  simp [csub]; exact Int.natAbs_sub_le _ _

lemma csub_natAbs_im_le (a b : FPComplex P) :
    (csub a b).im.natAbs ≤ a.im.natAbs + b.im.natAbs := by
  simp [csub]; exact Int.natAbs_sub_le _ _

end FPComplex

/-! ## Input bounds -/

/-
Lower bound on natAbs from bits
-/
lemma natAbs_ge_of_bits_ge (a : ℤ) (N : ℕ) (hN : N ≥ 2) (h : bits a ≥ N) :
    a.natAbs ≥ 2^(N-1) := by
  unfold bits at h;
  grind +suggestions

/-
decompose_digit values are bounded by 2^l (all indices)
-/
lemma decompose_digit_bound_all (x l K : ℕ) (N : ℕ) (hl : l ≥ 1) (hK : K ≥ 2)
    (hx : x < 2^N) (hlK : l * (K - 1) ≥ N) :
    ∀ j, j < K → decompose_digit x l K j < 2^l := by
  intro j hj;
  by_cases hj' : j < K - 1 <;> simp_all +decide [ decompose_digit ];
  · refine' lt_of_le_of_lt ( Nat.cast_le.mpr <| Nat.and_le_right ) _ ; norm_num [ Nat.shiftLeft_eq, Nat.pow_succ' ];
  · rw [ if_neg ( by omega ) ] ; norm_cast ; simp +decide [ Nat.shiftRight_eq_div_pow ] ; (
    exact lt_of_le_of_lt ( Nat.div_le_div_right hx.le ) ( by rw [ Nat.div_lt_iff_lt_mul <| by positivity ] ; rw [ ← pow_add ] ; exact pow_lt_pow_right₀ ( by decide ) <| by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ K ) ] ) ;);

/-! ## FFT characterization lemmas -/

namespace FPComplex

/-- Characterization of fft output at index i < K_pred (first half) -/
lemma fft_first_half {k' : ℕ} (x : Vector (FPComplex P) (2^(k'+1))) (inv : Bool)
    (i : Fin (2^(k'+1))) (hi : i.val < 2^k') :
    (fft x inv).get i =
      let E := Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)
      let O := Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)
      let E' := fft E inv
      let O' := fft O inv
      let T := t_table (2^k') inv P
      cadd (E'.get ⟨i.val, hi⟩) (cmul (T.get ⟨i.val, hi⟩) (O'.get ⟨i.val, hi⟩)) := by
  rw [FPComplex.fft]
  simp +decide [ Vector.get, hi ]

/-- Characterization of fft output at index i ≥ K_pred (second half) -/
lemma fft_second_half {k' : ℕ} (x : Vector (FPComplex P) (2^(k'+1))) (inv : Bool)
    (i : Fin (2^(k'+1))) (hi : ¬ i.val < 2^k') :
    (fft x inv).get i =
      let E := Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)
      let O := Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)
      let E' := fft E inv
      let O' := fft O inv
      let T := t_table (2^k') inv P
      csub (E'.get ⟨i.val - 2^k', by omega⟩)
           (cmul (T.get ⟨i.val - 2^k', by omega⟩) (O'.get ⟨i.val - 2^k', by omega⟩)) := by
  rw [ fft ]
  simp +decide [ Vector.get_ofFn, hi ]

end FPComplex


end SSABounds


/- ========================================================================
   Section: FFTError
   ======================================================================== -/

section FFTError

/-!
# FFT Error Analysis

This file develops the error analysis for the fixed-point FFT pipeline.
The key result is that the FFT pipeline with precision P = 4n + 2l + 4
computes the circular convolution with error < K * 2^(P-1).
-/

open Complex Finset

noncomputable section

/-! ## Part 1: Generalized DFT -/

/-- The generalized DFT, handling both forward (inv=false) and inverse (inv=true). -/
def gen_dft (K : ℕ) (x : Fin K → ℂ) (inv : Bool) (m : Fin K) : ℂ :=
  let w := if inv then (omega K)⁻¹ else omega K
  ∑ j : Fin K, x j * w ^ (m.val * j.val)

/-! ## Part 2: Exact FFT (defined as gen_dft) -/

/-- The exact FFT, defined directly as the generalized DFT.
    This avoids dependent type issues with the butterfly decomposition. -/
def exact_fft (k : ℕ) (x : Fin (2^k) → ℂ) (inv : Bool) : Fin (2^k) → ℂ :=
  gen_dft (2^k) x inv

/-! ## Part 3: Cooley-Tukey theorem (exact_fft = gen_dft) -/

/-
omega(2K)^(2j) = omega(K)^j
-/
lemma omega_sq_step (K : ℕ) (hK : K ≥ 1) (j : ℕ) :
    omega (2 * K) ^ (2 * j) = omega K ^ j := by
  simp +decide [ omega, ← Complex.exp_nat_mul ] ; ring

/-
omega(2K)^K = -1
-/
lemma omega_half_period (K : ℕ) (hK : K ≥ 1) :
    omega (2 * K) ^ K = -1 := by
  -- By definition of omega, we have omega (2 * K) = exp (2 * π * Complex.I / (2 * K)).
  have h_omega_def : omega (2 * K) = Complex.exp (2 * Real.pi * Complex.I / (2 * K)) := by
    unfold omega; aesop;
  convert Complex.exp_pi_mul_I using 1 ; rw [ h_omega_def ] ; rw [ ← Complex.exp_nat_mul ] ; ring_nf ; norm_num [ show K ≠ 0 by linarith ];
  norm_num [ mul_assoc, mul_comm, mul_left_comm, show K ≠ 0 by linarith ];
  norm_num [ mul_comm Complex.I ]

/-
omega inverse version: omega(2K)^(-2j) = omega(K)^(-j)
-/
lemma omega_inv_sq_step (K : ℕ) (hK : K ≥ 1) (j : ℕ) :
    (omega (2 * K))⁻¹ ^ (2 * j) = (omega K)⁻¹ ^ j := by
  rw [ inv_pow ];
  convert congr_arg ( fun x : ℂ => x⁻¹ ) ( omega_sq_step K hK j ) using 1 ; norm_num [ pow_mul ]

/-
omega inverse half period
-/
lemma omega_inv_half_period (K : ℕ) (hK : K ≥ 1) :
    (omega (2 * K))⁻¹ ^ K = -1 := by
  convert congr_arg ( ·⁻¹ ) ( omega_half_period K hK ) using 1 ; norm_num [ pow_mul', omega ] ; ring

/-
Cooley-Tukey: gen_dft of size 2K splits into sub-DFTs of size K (first half).
-/
lemma gen_dft_cooley_tukey_lo (K : ℕ) (hK : K ≥ 1) (x : Fin (2*K) → ℂ) (inv : Bool)
    (m : Fin (2*K)) (hm : m.val < K) :
    gen_dft (2*K) x inv m =
      gen_dft K (fun j : Fin K => x ⟨2 * j.val, by omega⟩) inv ⟨m.val, by omega⟩ +
      (if inv then (omega (2*K))⁻¹ else omega (2*K)) ^ m.val *
        gen_dft K (fun j : Fin K => x ⟨2 * j.val + 1, by omega⟩) inv ⟨m.val, by omega⟩ := by
  -- Apply the split_sum lemma to split the sum into two parts.
  have h_split : ∑ j : Fin (2 * K), x j * (if inv then (omega (2 * K))⁻¹ else omega (2 * K)) ^ (m.val * j.val) = ∑ j : Fin K, x ⟨2 * j, by omega⟩ * (if inv then (omega (2 * K))⁻¹ else omega (2 * K)) ^ (m.val * (2 * j)) + ∑ j : Fin K, x ⟨2 * j + 1, by omega⟩ * (if inv then (omega (2 * K))⁻¹ else omega (2 * K)) ^ (m.val * (2 * j + 1)) := by
    rw [ show ( Finset.univ : Finset ( Fin ( 2 * K ) ) ) = Finset.image ( fun i : Fin K => ⟨ 2 * i, by linarith [ Fin.is_lt i ] ⟩ ) Finset.univ ∪ Finset.image ( fun i : Fin K => ⟨ 2 * i + 1, by linarith [ Fin.is_lt i ] ⟩ ) Finset.univ from ?_, Finset.sum_union ];
    · rw [ Finset.sum_image, Finset.sum_image ] <;> simp +decide [ Fin.ext_iff ]; all_goals exact fun i j h => by simpa [ Fin.ext_iff ] using h;
    · norm_num [ Finset.disjoint_right ];
      exact fun a b => ne_of_apply_ne ( fun x => x % 2 ) ( by norm_num [ Nat.add_mod, Nat.mul_mod ] );
    · ext ⟨ i, hi ⟩ ; simp +decide [ Fin.ext_iff ] ; (
      rcases Nat.even_or_odd' i with ⟨ k, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ ⟨ k, by linarith ⟩, rfl ⟩ ;);
  convert h_split using 1;
  simp +decide [ gen_dft, pow_add, pow_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
  simp +decide [ ← mul_assoc, ← pow_mul', mul_comm, omega_sq_step K hK, omega_inv_sq_step K hK ];
  simp +decide [ ← omega_sq_step K hK, ← omega_inv_sq_step K hK, mul_comm, mul_assoc, mul_left_comm, pow_mul' ];
  split_ifs <;> ring

/-
Cooley-Tukey: gen_dft of size 2K splits into sub-DFTs of size K (second half).
-/
lemma gen_dft_cooley_tukey_hi (K : ℕ) (hK : K ≥ 1) (x : Fin (2*K) → ℂ) (inv : Bool)
    (m : Fin (2*K)) (hm : ¬m.val < K) :
    gen_dft (2*K) x inv m =
      gen_dft K (fun j : Fin K => x ⟨2 * j.val, by omega⟩) inv ⟨m.val - K, by omega⟩ -
      (if inv then (omega (2*K))⁻¹ else omega (2*K)) ^ (m.val - K) *
        gen_dft K (fun j : Fin K => x ⟨2 * j.val + 1, by omega⟩) inv ⟨m.val - K, by omega⟩ := by
  generalize_proofs at *;
  have h_split : ∑ j : Fin (2 * K), x j * (if inv then (omega (2 * K))⁻¹ else omega (2 * K)) ^ (m.val * j.val) = ∑ j : Fin K, x ⟨2 * j.val, by omega⟩ * (if inv then (omega (2 * K))⁻¹ else omega (2 * K)) ^ (m.val * (2 * j.val)) + ∑ j : Fin K, x ⟨2 * j.val + 1, by omega⟩ * (if inv then (omega (2 * K))⁻¹ else omega (2 * K)) ^ (m.val * (2 * j.val + 1)) := by
    have h_split : Finset.range (2 * K) = Finset.image (fun j => 2 * j) (Finset.range K) ∪ Finset.image (fun j => 2 * j + 1) (Finset.range K) := by
      ext j
      simp [Finset.mem_range, Finset.mem_image];
      exact ⟨ fun hj => by rcases Nat.even_or_odd' j with ⟨ k, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ k, by linarith, rfl ⟩, fun hj => by rcases hj with ( ⟨ k, hk, rfl ⟩ | ⟨ k, hk, rfl ⟩ ) <;> linarith ⟩;
    rw [ Finset.sum_fin_eq_sum_range ];
    rw [ h_split, Finset.sum_union ];
    · norm_num [ Finset.sum_image, Finset.sum_range ];
      split_ifs <;> simp +decide [ *, Finset.sum_ite ];
    · norm_num [ Finset.disjoint_right ];
      intros; omega;
  have h_even_odd : (if inv then (omega (2 * K))⁻¹ else omega (2 * K)) ^ (m.val) = - (if inv then (omega (2 * K))⁻¹ else omega (2 * K)) ^ (m.val - K) := by
    have h_even_odd : (if inv then (omega (2 * K))⁻¹ else omega (2 * K)) ^ K = -1 := by
      split_ifs <;> simp_all +decide [ omega_half_period, omega_inv_half_period ];
    rw [ ← Nat.sub_add_cancel ( show K ≤ ( m : ℕ ) from le_of_not_gt hm ), pow_add, h_even_odd ] ; ring;
    rw [ Nat.add_sub_cancel_left ];
  convert h_split using 1;
  simp +decide [ gen_dft, h_even_odd, mul_add, add_mul, pow_add, pow_mul', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
  split_ifs <;> simp_all +decide [ ← mul_assoc, ← pow_mul, mul_comm ];
  · rw [ ← Finset.sum_sub_distrib ] ; rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; ring;
    rw [ show ( m : ℕ ) = K + ( m - K ) by rw [ Nat.add_sub_cancel' hm ] ] ; ring;
    norm_num [ pow_mul', omega ];
    norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀, show K ≠ 0 by linarith ];
    norm_num [ Complex.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, show K ≠ 0 by linarith ];
    norm_num [ show Complex.exp ( Complex.I * ( Real.pi * ( ↑‹Fin K› * 2 ) ) ) = 1 by rw [ Complex.exp_eq_one_iff ] ; use ↑‹Fin K›; push_cast; ring ];
  · rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_sub_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; ring;
    rw [ show ( omega K : ℂ ) = omega ( K * 2 ) ^ 2 by
          unfold omega; rw [ ← Complex.exp_nat_mul ] ; ring;
          push_cast; ring; ] ; ring;
    rw [ show ( m : ℕ ) = K + ( m - K ) by rw [ Nat.add_sub_of_le hm ] ] ; ring;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, pow_mul', omega ];
    norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀, show K ≠ 0 by linarith ];
    norm_num [ ← mul_assoc, ← Complex.exp_add, mul_div_cancel₀, show K ≠ 0 by linarith ];
    norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, mul_div_cancel₀, show K ≠ 0 by linarith ];
    norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hK ) ] ; ring;
    norm_num [ mul_assoc, mul_comm Real.pi ];
    constructor <;> ring

/-! ## Part 4: Exact pipeline gives K * circular convolution -/

/-! ## Part 5: FFT error bounds

The key error recurrence: after k levels of FFT, the component error
is bounded. Here ε is the initial error and M bounds the exact values.

For real inputs (forward FFT): error ≤ (M + 1)(3^k - 2^k) where M_level = 2^k * M.
For complex inputs (inverse FFT): error ≤ (ε_0 + 2M + 1) * 3^k.

We state a unified bound that works for both cases. -/

/-! ## Part 6: cmul error bound -/

/-
Error bound for the pointwise cmul step.
    If inputs approximate exact values α, β with errors ε_a, ε_b,
    and exact components are bounded by M_a, M_b, then the cmul output
    error is bounded.
-/
lemma cmul_error_bound (P : ℕ) (hP : P ≥ 1)
    (a b : FPComplex P) (α β : ℂ)
    (ε_a ε_b : ℝ) (M_a M_b : ℝ)
    (hεa : ε_a ≥ 0) (hεb : ε_b ≥ 0) (hMa : M_a ≥ 0) (hMb : M_b ≥ 0)
    (ha_re : |(↑a.re : ℝ) - α.re * 2^P| ≤ ε_a)
    (ha_im : |(↑a.im : ℝ) - α.im * 2^P| ≤ ε_a)
    (hb_re : |(↑b.re : ℝ) - β.re * 2^P| ≤ ε_b)
    (hb_im : |(↑b.im : ℝ) - β.im * 2^P| ≤ ε_b)
    (hMa_re : |α.re| ≤ M_a) (hMa_im : |α.im| ≤ M_a)
    (hMb_re : |β.re| ≤ M_b) (hMb_im : |β.im| ≤ M_b) :
    |(↑(FPComplex.cmul a b).re : ℝ) - (α * β).re * 2^P| ≤
      2 * (M_a * ε_b + ε_a * M_b) + 2 * ε_a * ε_b / 2^P + 1/2 ∧
    |(↑(FPComplex.cmul a b).im : ℝ) - (α * β).im * 2^P| ≤
      2 * (M_a * ε_b + ε_a * M_b) + 2 * ε_a * ε_b / 2^P + 1/2 := by
  constructor <;> rw [ abs_le ] <;> constructor <;> norm_num [ div_eq_mul_inv ] at *;
  · have h_cmul_re : |(FPComplex.cmul a b).re - ((a.re * b.re - a.im * b.im) / 2^P : ℝ)| ≤ 1 / 2 := by
      have h_cmul_re : ∀ (v : ℤ), |(FPComplex.shr_round v P : ℝ) - (v / 2^P : ℝ)| ≤ 1 / 2 := by
        unfold FPComplex.shr_round;
        intro v; split_ifs <;> norm_num [ abs_le ] ;
        · linarith;
        · rw [ Int.shiftRight_eq_div_pow ];
          field_simp;
          norm_cast;
          rcases P with ( _ | P ) <;> simp_all +decide [ pow_succ' ];
          constructor <;> nlinarith [ Int.mul_ediv_add_emod ( v + 2 ^ P ) ( 2 * 2 ^ P ), Int.emod_nonneg ( v + 2 ^ P ) ( by positivity : ( 2 * 2 ^ P : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( v + 2 ^ P ) ( by positivity : ( 2 * 2 ^ P : ℤ ) > 0 ), pow_pos ( by positivity : 0 < ( 2 : ℤ ) ) P ];
      convert h_cmul_re ( a.re * b.re - a.im * b.im ) using 1 ; norm_cast;
    have h_cmul_re_bound : |(a.re * b.re - a.im * b.im : ℝ) - (α.re * β.re - α.im * β.im) * 2^(2*P)| ≤ 2 * (M_a * ε_b + ε_a * M_b) * 2^P + 2 * ε_a * ε_b := by
      have h_cmul_re_bound : |(a.re * b.re - a.im * b.im : ℝ) - (α.re * β.re - α.im * β.im) * 2^(2*P)| ≤ |(a.re - α.re * 2^P) * b.re| + |α.re * 2^P * (b.re - β.re * 2^P)| + |(a.im - α.im * 2^P) * b.im| + |α.im * 2^P * (b.im - β.im * 2^P)| := by
        rw [ abs_le ];
        constructor <;> cases abs_cases ( ( a.re - α.re * 2 ^ P ) * b.re ) <;> cases abs_cases ( α.re * 2 ^ P * ( b.re - β.re * 2 ^ P ) ) <;> cases abs_cases ( ( a.im - α.im * 2 ^ P ) * b.im ) <;> cases abs_cases ( α.im * 2 ^ P * ( b.im - β.im * 2 ^ P ) ) <;> push_cast [ pow_mul' ] at * <;> linarith;
      have h_cmul_re_bound : |(a.re - α.re * 2^P) * b.re| ≤ ε_a * (M_b * 2^P + ε_b) ∧ |α.re * 2^P * (b.re - β.re * 2^P)| ≤ M_a * 2^P * ε_b ∧ |(a.im - α.im * 2^P) * b.im| ≤ ε_a * (M_b * 2^P + ε_b) ∧ |α.im * 2^P * (b.im - β.im * 2^P)| ≤ M_a * 2^P * ε_b := by
        norm_num [ abs_mul, abs_of_nonneg, hεa, hεb, hMa, hMb ];
        refine' ⟨ mul_le_mul ha_re _ _ _, mul_le_mul ( mul_le_mul hMa_re ( le_refl _ ) _ _ ) hb_re _ _, mul_le_mul ha_im _ _ _, mul_le_mul ( mul_le_mul hMa_im ( le_refl _ ) _ _ ) hb_im _ _ ⟩ <;> try positivity;
        · exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp hMb_re, abs_le.mp hb_re, show ( 2 : ℝ ) ^ P ≥ 1 by exact one_le_pow₀ ( by norm_num ) ], by nlinarith [ abs_le.mp hMb_re, abs_le.mp hb_re, show ( 2 : ℝ ) ^ P ≥ 1 by exact one_le_pow₀ ( by norm_num ) ] ⟩;
        · exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp hMb_im, abs_le.mp hb_im, show ( 2 : ℝ ) ^ P ≥ 1 by exact one_le_pow₀ ( by norm_num ) ], by nlinarith [ abs_le.mp hMb_im, abs_le.mp hb_im, show ( 2 : ℝ ) ^ P ≥ 1 by exact one_le_pow₀ ( by norm_num ) ] ⟩;
      linarith;
    norm_num [ abs_le ] at *;
    field_simp at *;
    norm_num [ pow_mul' ] at * ; nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hP ];
  · -- By definition of `cmul`, we have:
    have h_cmul_def : (a.cmul b).re = round ((a.re * b.re - a.im * b.im : ℝ) / 2^P) := by
      convert Int.cast_inj.mpr ( FPComplex.shr_round_pos ( a.re * b.re - a.im * b.im ) P hP ) using 1;
      · rcases P with ( _ | P ) <;> simp_all +decide [ pow_succ, div_mul_eq_div_div ];
        norm_num [ round_eq, Int.floor_eq_iff ];
        rw [ div_div, div_add_div, le_div_iff₀, div_lt_iff₀ ] <;> norm_cast <;> norm_num [ pow_succ, mul_assoc ];
        constructor <;> nlinarith [ Int.mul_ediv_add_emod ( a.re * b.re - a.im * b.im + 2 ^ P ) ( 2 ^ P * 2 ), Int.emod_nonneg ( a.re * b.re - a.im * b.im + 2 ^ P ) ( by positivity : ( 2 ^ P * 2 : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( a.re * b.re - a.im * b.im + 2 ^ P ) ( by positivity : ( 2 ^ P * 2 : ℤ ) > 0 ), pow_pos ( by positivity : 0 < ( 2 : ℤ ) ) P ];
      · infer_instance;
    rw [ h_cmul_def, round_eq ];
    refine' le_trans ( Int.floor_le _ ) _;
    field_simp;
    norm_num [ abs_le ] at *;
    nlinarith [ show ( 2 : ℝ ) ^ P > 0 by positivity, mul_le_mul_of_nonneg_left hMa_re.1 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMa_re.2 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMa_im.1 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMa_im.2 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_re.1 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_re.2 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_im.1 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_im.2 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ) ];
  · have h_cmul_im : |(a.cmul b).im - (α.re * β.im + α.im * β.re) * 2 ^ P| ≤ |(a.re * b.im + a.im * b.re) - (α.re * β.im + α.im * β.re) * 2 ^ (2 * P)| / 2 ^ P + 1 / 2 := by
      have h_cmul_im : |(a.cmul b).im - (a.re * b.im + a.im * b.re : ℝ) / 2 ^ P| ≤ 1 / 2 := by
        convert abs_sub_round ( ( a.re * b.im + a.im * b.re : ℝ ) / 2 ^ P ) using 1;
        rw [ abs_sub_comm ];
        rw [ show ( a.cmul b ).im = round ( ( a.re * b.im + a.im * b.re : ℝ ) / 2 ^ P ) from ?_ ];
        unfold FPComplex.cmul;
        unfold FPComplex.shr_round;
        rcases P <;> simp_all +decide [ Int.shiftRight_eq_div_pow ];
        rw [ round_eq ];
        rw [ eq_comm, Int.floor_eq_iff ];
        rw [ div_add_div, le_div_iff₀, div_lt_iff₀ ] <;> norm_cast <;> norm_num [ pow_succ' ];
        constructor <;> nlinarith [ Int.mul_ediv_add_emod ( a.re * b.im + a.im * b.re + 2 ^ ‹_› ) ( 2 * 2 ^ ‹_› ), Int.emod_nonneg ( a.re * b.im + a.im * b.re + 2 ^ ‹_› ) ( by positivity : ( 2 * 2 ^ ‹_› : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( a.re * b.im + a.im * b.re + 2 ^ ‹_› ) ( by positivity : ( 2 * 2 ^ ‹_› : ℤ ) > 0 ), pow_pos ( zero_lt_two' ℤ ) ‹_› ];
      rw [ abs_le ] at *;
      field_simp at *;
      constructor <;> cases abs_cases ( ( a.re : ℝ ) * b.im + a.im * b.re - ( α.re * β.im + α.im * β.re ) * 2 ^ ( 2 * P ) ) <;> push_cast [ pow_mul' ] at * <;> nlinarith [ pow_pos ( zero_lt_two' ℝ ) P ];
    have h_cmul_im_bound : |(a.re * b.im + a.im * b.re) - (α.re * β.im + α.im * β.re) * 2 ^ (2 * P)| ≤ 2 * (M_a * ε_b + ε_a * M_b) * 2 ^ P + 2 * ε_a * ε_b := by
      rw [ abs_le ] at *;
      norm_num [ pow_mul' ] at *;
      constructor <;> nlinarith [ pow_pos ( zero_lt_two' ℝ ) P, mul_le_mul_of_nonneg_left hMa_re.1 ( show 0 ≤ ( 2 : ℝ ) ^ P by positivity ), mul_le_mul_of_nonneg_left hMa_re.2 ( show 0 ≤ ( 2 : ℝ ) ^ P by positivity ), mul_le_mul_of_nonneg_left hMa_im.1 ( show 0 ≤ ( 2 : ℝ ) ^ P by positivity ), mul_le_mul_of_nonneg_left hMa_im.2 ( show 0 ≤ ( 2 : ℝ ) ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_re.1 ( show 0 ≤ ( 2 : ℝ ) ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_re.2 ( show 0 ≤ ( 2 : ℝ ) ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_im.1 ( show 0 ≤ ( 2 : ℝ ) ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_im.2 ( show 0 ≤ ( 2 : ℝ ) ^ P by positivity ) ];
    rw [ abs_le ] at h_cmul_im;
    field_simp at *;
    nlinarith [ pow_pos ( zero_lt_two' ℝ ) P ];
  · -- By definition of `shr_round`, we know that
    have h_shr_round : ∀ v : ℤ, (FPComplex.shr_round v P : ℝ) ≤ (v : ℝ) / 2^P + 1 / 2 := by
      intro v; rw [ div_add_div, le_div_iff₀ ] <;> norm_cast <;> norm_num [ FPComplex.shr_round ] ;
      rcases P with ( _ | P ) <;> simp_all +decide [ pow_succ, Int.shiftRight_eq_div_pow ];
      nlinarith [ Int.mul_ediv_add_emod ( v + 2 ^ P ) ( 2 ^ P * 2 ), Int.emod_nonneg ( v + 2 ^ P ) ( by positivity : ( 2 ^ P * 2 : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( v + 2 ^ P ) ( by positivity : ( 2 ^ P * 2 : ℤ ) > 0 ), pow_pos ( zero_lt_two' ℤ ) P ];
    refine le_trans ( h_shr_round _ ) ?_;
    norm_num [ abs_le ] at *;
    field_simp;
    nlinarith [ show ( 2 : ℝ ) ^ P > 0 by positivity, mul_le_mul_of_nonneg_left hMa_re.1 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMa_re.2 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMa_im.1 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMa_im.2 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_re.1 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_re.2 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_im.1 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ), mul_le_mul_of_nonneg_left hMb_im.2 ( show ( 0 : ℝ ) ≤ 2 ^ P by positivity ) ]

/-! ## Part 7: Numerical bounds -/

/-
Component bound for gen_dft with real inputs (im = 0)
-/
lemma gen_dft_real_component_bound (K : ℕ) (hK : K ≥ 1) (x : Fin K → ℂ)
    (M : ℝ) (hM : M ≥ 0)
    (hx_re : ∀ j : Fin K, |(x j).re| ≤ M)
    (hx_im : ∀ j : Fin K, (x j).im = 0)
    (inv : Bool) (m : Fin K) :
    |(gen_dft K x inv m).re| ≤ K * M ∧ |(gen_dft K x inv m).im| ≤ K * M := by
  -- By definition of $gen_dft$, we know that its real and imaginary parts are bounded by $K * M$.
  have h_gen_dft_bound : ∀ m : Fin K, ‖(gen_dft K x inv m)‖ ≤ K * M := by
    intro m
    have h_sum_bound : ∀ j : Fin K, ‖(x j) * (if inv then (omega K)⁻¹ else omega K) ^ (m.val * j.val)‖ ≤ M := by
      intro j; split_ifs <;> simp_all +decide [ Complex.norm_def, Complex.normSq ] ;
      · unfold omega; norm_num [ Complex.exp_re, Complex.exp_im ] ; ring_nf; norm_num [ hM, hx_re j, hx_im j ] ;
        rw [ Real.sqrt_sq_eq_abs ] ; exact hx_re j;
      · unfold omega; norm_num [ Complex.exp_re, Complex.exp_im ] ; ring_nf;
        norm_num [ Real.sqrt_sq_eq_abs ] ; exact le_trans ( by simpa [ hx_im ] using hx_re j ) ( by norm_num ) ;
    exact le_trans ( norm_sum_le _ _ ) ( le_trans ( Finset.sum_le_sum fun _ _ => h_sum_bound _ ) ( by norm_num ) );
  exact ⟨ le_trans ( Complex.abs_re_le_norm _ ) ( h_gen_dft_bound m ), le_trans ( Complex.abs_im_le_norm _ ) ( h_gen_dft_bound m ) ⟩

/-
Component bound for gen_dft with complex inputs
-/
lemma gen_dft_complex_component_bound (K : ℕ) (hK : K ≥ 1) (x : Fin K → ℂ)
    (M : ℝ) (hM : M ≥ 0)
    (hx : ∀ j : Fin K, ‖x j‖ ≤ M)
    (inv : Bool) (m : Fin K) :
    |(gen_dft K x inv m).re| ≤ K * M ∧ |(gen_dft K x inv m).im| ≤ K * M := by
  have h_sum_bound : ‖gen_dft K x inv m‖ ≤ K * M := by
    refine' le_trans ( norm_sum_le _ _ ) _;
    unfold omega; split_ifs <;> simp_all +decide [ Complex.norm_exp ] ;
    · exact le_trans ( Finset.sum_le_sum fun _ _ => hx _ ) ( by norm_num );
    · exact le_trans ( Finset.sum_le_sum fun _ _ => hx _ ) ( by norm_num );
  exact ⟨ le_trans ( Complex.abs_re_le_norm _ ) h_sum_bound, le_trans ( Complex.abs_im_le_norm _ ) h_sum_bound ⟩

/-
Inverse gen_dft equals K * idft
-/
lemma gen_dft_true_eq_K_idft (K : ℕ) (hK : K ≥ 2) (x : Fin K → ℂ) (m : Fin K) :
    gen_dft K x true m = (K : ℂ) * idft K x m := by
  unfold gen_dft idft; simp +decide [ mul_comm, mul_assoc, mul_left_comm, Finset.mul_sum ] ; ring;
  exact Finset.sum_congr rfl fun _ _ => by rw [ mul_inv_cancel_right₀ ( by norm_cast; linarith ) ] ; ring;

/-
The gen_dft pipeline gives K * circular convolution (no exact_fft needed).
-/
lemma gen_dft_pipeline_eq_conv (K : ℕ) (hK : K ≥ 2)
    (A_digits B_digits : Fin K → ℤ) :
    let A : Fin K → ℂ := fun j => (↑(A_digits j) : ℂ)
    let B : Fin K → ℂ := fun j => (↑(B_digits j) : ℂ)
    ∀ m : Fin K,
      gen_dft K (fun i => gen_dft K A false i * gen_dft K B false i) true m =
      (↑K : ℂ) * ↑(∑ j : Fin K, ∑ k : Fin K,
        if (j.val + k.val) % K = m.val then A_digits j * B_digits k else 0) := by
  have h_shift : ∀ m : Fin K, gen_dft K (fun i => gen_dft K (fun j => (A_digits j : ℂ)) false i * gen_dft K (fun j => (B_digits j : ℂ)) false i) true m = K * idft K (fun i => gen_dft K (fun j => (A_digits j : ℂ)) false i * gen_dft K (fun j => (B_digits j : ℂ)) false i) m := by
    exact fun m => gen_dft_true_eq_K_idft K hK _ m;
  have h_idft : ∀ m : Fin K, idft K (fun i => gen_dft K (fun j => (A_digits j : ℂ)) false i * gen_dft K (fun j => (B_digits j : ℂ)) false i) m = circular_conv K (fun j => (A_digits j : ℂ)) (fun j => (B_digits j : ℂ)) m := by
    intro m
    have h_idft : idft K (fun i => gen_dft K (fun j => (A_digits j : ℂ)) false i * gen_dft K (fun j => (B_digits j : ℂ)) false i) m = idft K (fun i => gen_dft K (circular_conv K (fun j => (A_digits j : ℂ)) (fun j => (B_digits j : ℂ))) false i) m := by
      congr! 2;
      convert dft_convolution_theorem K hK ( fun j => ( A_digits j : ℂ ) ) ( fun j => ( B_digits j : ℂ ) ) _ |> Eq.symm using 1;
    have := idft_dft K hK ( fun j => circular_conv K ( fun j => ( A_digits j : ℂ ) ) ( fun j => ( B_digits j : ℂ ) ) j ) m; aesop;
  simp_all +decide [ circular_conv ]

end

end FFTError


/- ========================================================================
   Section: FFTErrorInduction
   ======================================================================== -/

section FFTErrorInduction

/-!
# FFT Error Bound - Inductive proof

This file contains the inductive proof of `fft_error_bound`, which shows that
the fixed-point FFT approximates the generalized DFT with error ≤ (ε₀ + 2M + 1) * 3^k.

The proof proceeds by strong induction on the number of butterfly levels k.
-/

open Complex Finset

noncomputable section

/-! ## Part 1: Twiddle factor properties -/

/-- |round(x) - x| ≤ 1/2 for any real x -/
lemma abs_round_sub_le (x : ℝ) : |(round x : ℝ) - x| ≤ 1/2 := by
  rw [abs_sub_comm]; exact abs_sub_round x

/-- The twiddle factor approximates the exact complex exponential with error ≤ 1/2. -/
lemma twiddle_approx_re (j K : ℕ) (inv : Bool) (P : ℕ) :
    let θ := (if inv then (-1 : ℝ) else 1) * 2 * Real.pi * j / K
    |(↑(FPComplex.twiddle j K inv P).re : ℝ) - Real.cos θ * 2^P| ≤ 1/2 := by
  simp only [FPComplex.twiddle]
  exact abs_round_sub_le _

lemma twiddle_approx_im (j K : ℕ) (inv : Bool) (P : ℕ) :
    let θ := (if inv then (-1 : ℝ) else 1) * 2 * Real.pi * j / K
    |(↑(FPComplex.twiddle j K inv P).im : ℝ) - Real.sin θ * 2^P| ≤ 1/2 := by
  simp only [FPComplex.twiddle]
  exact abs_round_sub_le _

/-! ## Part 2: FPComplex.fft unfolding for butterfly step -/

lemma fft_succ_lo (k : ℕ) (P : ℕ) (x : Vector (FPComplex P) (2^(k+1)))
    (inv : Bool) (i : Fin (2^(k+1))) (hi : i.val < 2^k) :
    (FPComplex.fft x inv).get i =
      FPComplex.cadd
        ((FPComplex.fft (Vector.ofFn fun j : Fin (2^k) => x[2 * j.val]'(by omega)) inv).get ⟨i.val, hi⟩)
        (FPComplex.cmul
          ((FPComplex.t_table (2^k) inv P).get ⟨i.val, hi⟩)
          ((FPComplex.fft (Vector.ofFn fun j : Fin (2^k) => x[2 * j.val + 1]'(by omega)) inv).get ⟨i.val, hi⟩)) := by
  convert Vector.get_ofFn _ _ using 1;
  aesop

lemma fft_succ_hi (k : ℕ) (P : ℕ) (x : Vector (FPComplex P) (2^(k+1)))
    (inv : Bool) (i : Fin (2^(k+1))) (hi : ¬i.val < 2^k) :
    (FPComplex.fft x inv).get i =
      FPComplex.csub
        ((FPComplex.fft (Vector.ofFn fun j : Fin (2^k) => x[2 * j.val]'(by omega)) inv).get ⟨i.val - 2^k, by omega⟩)
        (FPComplex.cmul
          ((FPComplex.t_table (2^k) inv P).get ⟨i.val - 2^k, by omega⟩)
          ((FPComplex.fft (Vector.ofFn fun j : Fin (2^k) => x[2 * j.val + 1]'(by omega)) inv).get ⟨i.val - 2^k, by omega⟩)) := by
  rw [FPComplex.fft];
  simp +decide [ Vector.get, hi ]

/-! ## Part 3: Twiddle = omega connection -/

lemma t_table_exact_value (K j : ℕ) (hK : K ≥ 1) (hj : j < K) (inv : Bool) (P : ℕ) :
    let T := (FPComplex.t_table K inv P).get ⟨j, hj⟩
    let w := if inv then (omega (2 * K))⁻¹ else omega (2 * K)
    |(↑T.re : ℝ) - (w ^ j).re * 2^P| ≤ 1/2 ∧
    |(↑T.im : ℝ) - (w ^ j).im * 2^P| ≤ 1/2 := by
  have h_t_table_approx : |(FPComplex.twiddle j (2 * K) inv P).re - (Complex.exp ((if inv then -1 else 1) * 2 * Real.pi * j / (2 * K) * Complex.I)).re * 2 ^ P| ≤ 1 / 2 ∧ |(FPComplex.twiddle j (2 * K) inv P).im - (Complex.exp ((if inv then -1 else 1) * 2 * Real.pi * j / (2 * K) * Complex.I)).im * 2 ^ P| ≤ 1 / 2 := by
    convert And.intro ( twiddle_approx_re j ( 2 * K ) inv P ) ( twiddle_approx_im j ( 2 * K ) inv P ) using 3 <;> norm_num [ Complex.exp_re, Complex.exp_im ];
    · split_ifs <;> norm_num [ div_eq_mul_inv ];
      · simp +decide [ show K ≠ 0 by linarith ];
      · simp +decide [ ← mul_assoc, ne_of_gt ( zero_lt_one.trans_le hK ) ];
    · split_ifs <;> norm_num [ div_eq_mul_inv ]; all_goals simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hK ) ];
  convert h_t_table_approx using 3 <;> norm_num [ Complex.exp_re, Complex.exp_im, omega ] ; ring;
  · unfold FPComplex.t_table; norm_num [ Complex.exp_re, Complex.exp_im, ← Complex.exp_nat_mul ] ; ring;
    split_ifs <;> simp +decide [ Complex.exp_re, Complex.exp_im, div_eq_mul_inv ];
    norm_num [ Complex.normSq_eq_norm_sq, Complex.norm_exp ];
  · split_ifs <;> simp +decide [ *, ← Complex.exp_nat_mul, ← Complex.exp_neg ] <;> ring;
    · norm_num [ Complex.exp_re, Complex.exp_im, FPComplex.t_table ] ; ring;
    · norm_num [ Complex.exp_re, Complex.exp_im, FPComplex.t_table ] ; ring

/-! ## Part 4: Magnitude bounds for even/odd sub-DFTs -/

lemma gen_dft_sub_component_bound (K : ℕ) (hK : K ≥ 1)
    (x_exact : Fin K → ℂ) (M : ℝ) (hM : M ≥ 0)
    (hx : ∀ j : Fin K, |(x_exact j).re| ≤ M ∧ |(x_exact j).im| ≤ M)
    (inv : Bool) (m : Fin K) :
    |(gen_dft K x_exact inv m).re| ≤ 2 * K * M ∧
    |(gen_dft K x_exact inv m).im| ≤ 2 * K * M := by
  convert gen_dft_complex_component_bound K hK x_exact ( 2 * M ) ( by positivity ) ( fun j => ?_ ) inv m using 1 <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
  · grind
  · ring;
  · exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ abs_le.mp ( hx j |>.1 ), abs_le.mp ( hx j |>.2 ) ] ⟩

/-! ## Part 5: Butterfly error for one step -/

lemma butterfly_error_lo (K : ℕ) (P : ℕ) (hK : K ≥ 1) (hP : P ≥ 1)
    (E' O' : FPComplex P) (T : FPComplex P)
    (E_exact O_exact : ℂ)
    (w_j : ℂ)
    (ε : ℝ) (M : ℝ) (hε : ε ≥ 0) (hM : M ≥ 0)
    (hE_re : |(↑E'.re : ℝ) - E_exact.re * 2^P| ≤ ε)
    (hE_im : |(↑E'.im : ℝ) - E_exact.im * 2^P| ≤ ε)
    (hO_re : |(↑O'.re : ℝ) - O_exact.re * 2^P| ≤ ε)
    (hO_im : |(↑O'.im : ℝ) - O_exact.im * 2^P| ≤ ε)
    (hT_re : |(↑T.re : ℝ) - w_j.re * 2^P| ≤ 1/2)
    (hT_im : |(↑T.im : ℝ) - w_j.im * 2^P| ≤ 1/2)
    (hw_re : |w_j.re| ≤ 1) (hw_im : |w_j.im| ≤ 1)
    (hO_mag_re : |O_exact.re| ≤ 2 * K * M) (hO_mag_im : |O_exact.im| ≤ 2 * K * M)
    (h_prec : ε ≤ 2^(P - 1 : ℕ)) :
    |(↑(FPComplex.cadd E' (FPComplex.cmul T O')).re : ℝ) -
      (E_exact + w_j * O_exact).re * 2^P| ≤ 3 * ε + 2 * K * M + 1 ∧
    |(↑(FPComplex.cadd E' (FPComplex.cmul T O')).im : ℝ) -
      (E_exact + w_j * O_exact).im * 2^P| ≤ 3 * ε + 2 * K * M + 1 := by
  convert cmul_error_bound P hP T O' w_j O_exact ( 1 / 2 ) ε 1 ( 2 * K * M ) _ _ _ _ _ using 1;
  all_goals norm_num [ hε, hM, hT_re, hT_im, hw_re, hw_im, hO_mag_re, hO_mag_im, h_prec ];
  · constructor <;> intro h;
    · convert cmul_error_bound P hP T O' w_j O_exact ( 1 / 2 ) ε 1 ( 2 * K * M ) _ _ _ _ _ using 1;
      all_goals norm_num [ hε, hM, hT_re, hT_im, hw_re, hw_im, hO_mag_re, hO_mag_im, h_prec ];
      · exact hO_re;
      · exact Or.inl hO_re;
      · positivity;
    · have h_prec : ε / 2^P ≤ 1 / 2 := by
        rw [ div_le_iff₀ ] <;> first | positivity | cases P <;> norm_num [ pow_succ' ] at * ; linarith;
      norm_num [ FPComplex.cadd ] at *;
      exact ⟨ abs_le.mpr ⟨ by linarith [ abs_le.mp hE_re, abs_le.mp ( h hO_re hO_im |>.1 ) ], by linarith [ abs_le.mp hE_re, abs_le.mp ( h hO_re hO_im |>.1 ) ] ⟩, abs_le.mpr ⟨ by linarith [ abs_le.mp hE_im, abs_le.mp ( h hO_re hO_im |>.2 ) ], by linarith [ abs_le.mp hE_im, abs_le.mp ( h hO_re hO_im |>.2 ) ] ⟩ ⟩;
  · positivity

lemma butterfly_error_hi (K : ℕ) (P : ℕ) (hK : K ≥ 1) (hP : P ≥ 1)
    (E' O' : FPComplex P) (T : FPComplex P)
    (E_exact O_exact : ℂ)
    (w_j : ℂ)
    (ε : ℝ) (M : ℝ) (hε : ε ≥ 0) (hM : M ≥ 0)
    (hE_re : |(↑E'.re : ℝ) - E_exact.re * 2^P| ≤ ε)
    (hE_im : |(↑E'.im : ℝ) - E_exact.im * 2^P| ≤ ε)
    (hO_re : |(↑O'.re : ℝ) - O_exact.re * 2^P| ≤ ε)
    (hO_im : |(↑O'.im : ℝ) - O_exact.im * 2^P| ≤ ε)
    (hT_re : |(↑T.re : ℝ) - w_j.re * 2^P| ≤ 1/2)
    (hT_im : |(↑T.im : ℝ) - w_j.im * 2^P| ≤ 1/2)
    (hw_re : |w_j.re| ≤ 1) (hw_im : |w_j.im| ≤ 1)
    (hO_mag_re : |O_exact.re| ≤ 2 * K * M) (hO_mag_im : |O_exact.im| ≤ 2 * K * M)
    (h_prec : ε ≤ 2^(P - 1 : ℕ)) :
    |(↑(FPComplex.csub E' (FPComplex.cmul T O')).re : ℝ) -
      (E_exact - w_j * O_exact).re * 2^P| ≤ 3 * ε + 2 * K * M + 1 ∧
    |(↑(FPComplex.csub E' (FPComplex.cmul T O')).im : ℝ) -
      (E_exact - w_j * O_exact).im * 2^P| ≤ 3 * ε + 2 * K * M + 1 := by
  convert @butterfly_error_lo K P hK hP E' O' T E_exact O_exact w_j ε M hε hM ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ using 1;
  any_goals assumption;
  constructor <;> intro h <;> simp_all +decide [ FPComplex.cadd, FPComplex.csub ];
  · convert @butterfly_error_lo K P hK hP E' O' T E_exact O_exact w_j ε M hε hM ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ using 1;
    all_goals norm_cast at *;
    · simp_all +decide [ FPComplex.cadd, FPComplex.cmul, Complex.ext_iff ];
    · exact hT_re.trans ( by norm_num );
    · exact hT_im.trans ( by norm_num );
  · have := cmul_error_bound P hP T O' w_j O_exact ( 1 / 2 ) ε 1 ( 2 * K * M ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num at *;
    all_goals norm_cast at *;
    · norm_num [ abs_le ] at *;
      constructor <;> constructor <;> linarith [ this hw_im.1 hw_im.2 hO_mag_re.1 hO_mag_re.2 hO_mag_im.1 hO_mag_im.2, show ( ε : ℝ ) / 2 ^ P ≤ 1 / 2 by rw [ div_le_iff₀ ( by positivity ) ] ; linarith [ show ( 2 : ℝ ) ^ P ≥ 2 ^ ( P - 1 ) * 2 by rw [ ← pow_succ, Nat.sub_add_cancel hP ] ] ];
    · positivity

/-! ## Part 6: Error recurrence closes -/

/-- Omega power components are bounded by 1 (on the unit circle). -/
lemma omega_pow_component_bound (K j : ℕ) (hK : K ≥ 1) (inv : Bool) :
    let w := if inv then (omega (2*K))⁻¹ else omega (2*K)
    |(w ^ j).re| ≤ 1 ∧ |(w ^ j).im| ≤ 1 := by
  split_ifs with h
  · have h1 : ‖(omega (2*K))⁻¹ ^ j‖ = 1 := by
      rw [norm_pow, norm_inv, omega_norm (2*K) (by omega)]; simp
    exact ⟨le_trans (Complex.abs_re_le_norm _) (by rw [h1]),
           le_trans (Complex.abs_im_le_norm _) (by rw [h1])⟩
  · have h1 : ‖omega (2*K) ^ j‖ = 1 := by
      rw [norm_pow, omega_norm (2*K) (by omega)]; simp
    exact ⟨le_trans (Complex.abs_re_le_norm _) (by rw [h1]),
           le_trans (Complex.abs_im_le_norm _) (by rw [h1])⟩

/-! ## Part 7: Cooley-Tukey in 2^(k'+1) form -/

/-- Cooley-Tukey decomposition for first half, using 2^(k'+1) types directly. -/
lemma gen_dft_cooley_tukey_lo' (k' : ℕ) (x_exact : Fin (2^(k'+1)) → ℂ) (inv : Bool)
    (i : Fin (2^(k'+1))) (hi : i.val < 2^k') :
    gen_dft (2^(k'+1)) x_exact inv i =
      gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2 * j.val, by omega⟩) inv ⟨i.val, hi⟩ +
      (if inv then (omega (2^(k'+1)))⁻¹ else omega (2^(k'+1))) ^ i.val *
        gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2 * j.val + 1, by omega⟩) inv ⟨i.val, hi⟩ := by
  set K := 2^k'
  have h_size : 2^(k'+1) = 2 * K := by omega
  have h_omega : omega (2 * K) = omega (2^(k'+1)) := by congr 1; omega
  have h := gen_dft_cooley_tukey_lo K (Nat.one_le_pow _ _ (by omega))
    (fun j : Fin (2 * K) => x_exact ⟨j.val, by omega⟩) inv ⟨i.val, by omega⟩ hi
  rw [h_omega] at h
  have h_lhs : gen_dft (2^(k'+1)) x_exact inv i =
    gen_dft (2 * K) (fun j : Fin (2 * K) => x_exact ⟨j.val, by omega⟩) inv ⟨i.val, by omega⟩ := by
    unfold gen_dft
    refine Finset.sum_equiv (Fin.castOrderIso h_size).toEquiv ?_ ?_
    · intro; constructor <;> intro <;> exact Finset.mem_univ _
    · intro a _; rw [h_omega.symm]; split_ifs <;> simp_all
  rw [h_lhs, h]

/-- Cooley-Tukey decomposition for second half, using 2^(k'+1) types directly. -/
lemma gen_dft_cooley_tukey_hi' (k' : ℕ) (x_exact : Fin (2^(k'+1)) → ℂ) (inv : Bool)
    (i : Fin (2^(k'+1))) (hi : ¬i.val < 2^k') :
    gen_dft (2^(k'+1)) x_exact inv i =
      gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2 * j.val, by omega⟩) inv ⟨i.val - 2^k', by omega⟩ -
      (if inv then (omega (2^(k'+1)))⁻¹ else omega (2^(k'+1))) ^ (i.val - 2^k') *
        gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2 * j.val + 1, by omega⟩) inv ⟨i.val - 2^k', by omega⟩ := by
  set K := 2^k'
  have h_size : 2^(k'+1) = 2 * K := by omega
  have h_omega : omega (2 * K) = omega (2^(k'+1)) := by congr 1; omega
  have h := gen_dft_cooley_tukey_hi K (Nat.one_le_pow _ _ (by omega))
    (fun j : Fin (2 * K) => x_exact ⟨j.val, by omega⟩) inv ⟨i.val, by omega⟩ hi
  rw [h_omega] at h
  have h_lhs : gen_dft (2^(k'+1)) x_exact inv i =
    gen_dft (2 * K) (fun j : Fin (2 * K) => x_exact ⟨j.val, by omega⟩) inv ⟨i.val, by omega⟩ := by
    unfold gen_dft
    refine Finset.sum_equiv (Fin.castOrderIso h_size).toEquiv ?_ ?_
    · intro; constructor <;> intro <;> exact Finset.mem_univ _
    · intro a _; rw [h_omega.symm]; split_ifs <;> simp_all
  rw [h_lhs, h]

/-! ## Part 8: The tight bound G(k) and the main theorem -/

/-- The tight bound: G(k) = (ε₀ + 2M + 1/2) * 3^k - 2M * 2^k - 1/2. -/
def G_bound (ε₀ M : ℝ) (k : ℕ) : ℝ :=
  (ε₀ + 2 * M + 1/2) * 3^k - 2 * M * 2^k - 1/2

lemma G_bound_zero (ε₀ M : ℝ) : G_bound ε₀ M 0 = ε₀ := by
  simp [G_bound]; ring

lemma G_bound_le (ε₀ M : ℝ) (hM : M ≥ 0) (k : ℕ) :
    G_bound ε₀ M k ≤ (ε₀ + 2 * M + 1) * 3^k := by
  exact sub_le_iff_le_add'.mpr ( by nlinarith [ pow_pos ( zero_lt_three' ℝ ) k, pow_pos ( zero_lt_two' ℝ ) k ] )

lemma G_bound_nonneg (ε₀ M : ℝ) (hε : ε₀ ≥ 0) (hM : M ≥ 0) (k : ℕ) :
    G_bound ε₀ M k ≥ 0 := by
  unfold G_bound;
  induction' k with k ih <;> norm_num [ pow_succ' ] at *;
  · linarith;
  · nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 2 ) k, pow_le_pow_left₀ ( by norm_num ) ( by norm_num : ( 2 : ℝ ) ≤ 3 ) k ]

/-! ## Part 9: Inductive step helpers -/

/-
Inductive step helper for the first half (i < K).
-/
lemma fft_error_step_lo (k' : ℕ) (P : ℕ) (hP : P ≥ 1)
    (x : Vector (FPComplex P) (2^(k'+1))) (inv : Bool)
    (x_exact : Fin (2^(k'+1)) → ℂ)
    (ε₀ M : ℝ) (hε : ε₀ ≥ 0) (hM : M ≥ 0)
    (h_mag : ∀ i : Fin (2^(k'+1)), |(x_exact i).re| ≤ M ∧ |(x_exact i).im| ≤ M)
    (h_prec : (ε₀ + 2 * M + 1) * (3 : ℝ)^(k'+1) ≤ 2^(P - 1))
    (i : Fin (2^(k'+1))) (hi : i.val < 2^k')
    (IH_E : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get j).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv j).re * 2^P| ≤ G_bound ε₀ M k')
    (IH_E_im : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get j).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv j).im * 2^P| ≤ G_bound ε₀ M k')
    (IH_O : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get j).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv j).re * 2^P| ≤ G_bound ε₀ M k')
    (IH_O_im : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get j).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv j).im * 2^P| ≤ G_bound ε₀ M k') :
    |(↑((FPComplex.fft x inv).get i).re : ℝ) - (gen_dft (2^(k'+1)) x_exact inv i).re * 2^P| ≤ G_bound ε₀ M (k'+1) ∧
    |(↑((FPComplex.fft x inv).get i).im : ℝ) - (gen_dft (2^(k'+1)) x_exact inv i).im * 2^P| ≤ G_bound ε₀ M (k'+1) := by
  convert butterfly_error_lo ( 2 ^ k' ) P ( Nat.one_le_pow _ _ ( by decide ) ) hP ( FPComplex.fft ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val]'(by omega) ) inv |> Vector.get <| ⟨ i.val, hi ⟩ ) ( FPComplex.fft ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val + 1]'(by omega) ) inv |> Vector.get <| ⟨ i.val, hi ⟩ ) ( FPComplex.t_table ( 2 ^ k' ) inv P |> Vector.get <| ⟨ i.val, hi ⟩ ) ( gen_dft ( 2^k' ) ( fun j => x_exact ⟨ 2 * j.val, by omega ⟩ ) inv ⟨ i.val, hi ⟩ ) ( gen_dft ( 2^k' ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) inv ⟨ i.val, hi ⟩ ) _ using 6;
  rotate_left;
  exact if inv then ( omega ( 2 ^ ( k' + 1 ) ) ) ⁻¹ ^ i.val else omega ( 2 ^ ( k' + 1 ) ) ^ i.val;
  apply Iff.intro;
  · intro h ε M hε hM hE_re hE_im hO_re hO_im hT_re hT_im hw_re hw_im hO_mag_re hO_mag_im h_prec;
    convert butterfly_error_lo ( 2 ^ k' ) P ( Nat.one_le_pow _ _ ( by decide ) ) hP _ _ _ _ _ _ ε M hε hM _ _ _ _ _ _ _ _ _ _ _ using 1;
    all_goals assumption;
  · intro h;
    convert h ( G_bound ε₀ M k' ) M ( by
      exact G_bound_nonneg ε₀ M hε hM k' ) hM ( IH_E ⟨ i.val, hi ⟩ ) ( IH_E_im ⟨ i.val, hi ⟩ ) ( IH_O ⟨ i.val, hi ⟩ ) ( IH_O_im ⟨ i.val, hi ⟩ ) ( by
      convert t_table_exact_value ( 2 ^ k' ) i.val ( Nat.one_le_pow _ _ ( by decide ) ) hi inv P |>.1 using 1;
      rw [ ← pow_succ' ];
      split_ifs <;> norm_num ) ( by
      convert t_table_exact_value ( 2 ^ k' ) i.val ( Nat.one_le_pow _ _ ( by decide ) ) hi inv P |>.2 using 1;
      norm_num [ pow_succ' ] ) ( by
      convert omega_pow_component_bound ( 2 ^ k' ) i.val ( Nat.one_le_pow _ _ ( by decide ) ) inv |>.1 using 1;
      grind +splitImp ) ( by
      convert omega_pow_component_bound ( 2 ^ k' ) i.val ( Nat.one_le_pow _ _ ( by decide ) ) inv |>.2 using 1;
      grind ) ( by
      have := gen_dft_sub_component_bound ( 2 ^ k' ) ( Nat.one_le_pow _ _ ( by decide ) ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) M hM ( fun j => h_mag _ ) inv ⟨ i.val, hi ⟩ ; norm_num at * ; linarith ) ( by
      convert gen_dft_sub_component_bound ( 2 ^ k' ) ( Nat.one_le_pow _ _ ( by decide ) ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) M hM ( fun j => h_mag _ ) inv ⟨ i.val, hi ⟩ |>.2 using 1 ) ( by
      exact le_trans ( G_bound_le ε₀ M hM k' ) ( by nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 3 ) k', pow_pos ( by norm_num : ( 0 : ℝ ) < 2 ) k', pow_succ' ( 3 : ℝ ) k', pow_succ' ( 2 : ℝ ) k' ] ) ) using 1;
    · rw [ fft_succ_lo k' P x inv i hi, gen_dft_cooley_tukey_lo' k' x_exact inv i hi ];
      split_ifs <;> norm_num [ pow_succ' ]; all_goals unfold G_bound; ring;
    · rw [ fft_succ_lo k' P x inv i hi, gen_dft_cooley_tukey_lo' k' x_exact inv i hi ];
      simp +decide [ G_bound ];
      ring

/-
Inductive step helper for the second half (i ≥ K).
-/
lemma fft_error_step_hi (k' : ℕ) (P : ℕ) (hP : P ≥ 1)
    (x : Vector (FPComplex P) (2^(k'+1))) (inv : Bool)
    (x_exact : Fin (2^(k'+1)) → ℂ)
    (ε₀ M : ℝ) (hε : ε₀ ≥ 0) (hM : M ≥ 0)
    (h_mag : ∀ i : Fin (2^(k'+1)), |(x_exact i).re| ≤ M ∧ |(x_exact i).im| ≤ M)
    (h_prec : (ε₀ + 2 * M + 1) * (3 : ℝ)^(k'+1) ≤ 2^(P - 1))
    (i : Fin (2^(k'+1))) (hi : ¬i.val < 2^k')
    (IH_E : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get j).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv j).re * 2^P| ≤ G_bound ε₀ M k')
    (IH_E_im : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get j).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv j).im * 2^P| ≤ G_bound ε₀ M k')
    (IH_O : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get j).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv j).re * 2^P| ≤ G_bound ε₀ M k')
    (IH_O_im : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get j).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv j).im * 2^P| ≤ G_bound ε₀ M k') :
    |(↑((FPComplex.fft x inv).get i).re : ℝ) - (gen_dft (2^(k'+1)) x_exact inv i).re * 2^P| ≤ G_bound ε₀ M (k'+1) ∧
    |(↑((FPComplex.fft x inv).get i).im : ℝ) - (gen_dft (2^(k'+1)) x_exact inv i).im * 2^P| ≤ G_bound ε₀ M (k'+1) := by
  rw [ fft_succ_hi k' P x inv i hi, gen_dft_cooley_tukey_hi' k' x_exact inv i hi ];
  convert butterfly_error_hi ( 2 ^ k' ) P ( Nat.one_le_pow _ _ ( by decide ) ) hP ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) ( _ ) using 1;
  rotate_left;
  exact ( FPComplex.fft ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val]'(by omega) ) inv ).get ⟨ i.val - 2 ^ k', by omega ⟩;
  exact ( FPComplex.fft ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val + 1]'(by omega) ) inv ).get ⟨ i.val - 2 ^ k', by omega ⟩;
  exact ( FPComplex.t_table ( 2 ^ k' ) inv P ).get ⟨ i.val - 2 ^ k', by omega ⟩;
  exact gen_dft ( 2 ^ k' ) ( fun j => x_exact ⟨ 2 * j.val, by omega ⟩ ) inv ⟨ i.val - 2 ^ k', by omega ⟩;
  exact gen_dft ( 2 ^ k' ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) inv ⟨ i.val - 2 ^ k', by omega ⟩;
  exact ( if inv then ( omega ( 2 ^ ( k' + 1 ) ) ) ⁻¹ else omega ( 2 ^ ( k' + 1 ) ) ) ^ ( i.val - 2 ^ k' );
  exact G_bound ε₀ M k';
  bv_omega;
  exact G_bound_nonneg ε₀ M hε hM k';
  finiteness;
  exact IH_E ⟨ i - 2 ^ k', by omega ⟩;
  exact IH_E_im ⟨ i - 2 ^ k', by omega ⟩;
  exact IH_O ⟨ i - 2 ^ k', by omega ⟩;
  exact IH_O_im ⟨ i - 2 ^ k', by omega ⟩;
  convert t_table_exact_value ( 2 ^ k' ) ( i - 2 ^ k' ) ( Nat.one_le_pow _ _ ( by decide ) ) ( by omega ) inv P |>.1 using 1;
  grind +splitImp;
  convert t_table_exact_value ( 2 ^ k' ) ( i - 2 ^ k' ) ( Nat.one_le_pow _ _ ( by decide ) ) ( by omega ) inv P |>.2 using 1;
  grind +extAll;
  · convert omega_pow_component_bound ( 2 ^ k' ) ( i - 2 ^ k' ) ( Nat.one_le_pow _ _ ( by decide ) ) inv |>.1 using 1;
    rw [ ← pow_succ' ];
  · convert omega_pow_component_bound ( 2 ^ k' ) ( i - 2 ^ k' ) ( Nat.one_le_pow _ _ ( by decide ) ) inv |>.2 using 1;
    rw [ ← pow_succ' ];
  · convert gen_dft_sub_component_bound ( 2 ^ k' ) ( Nat.one_le_pow _ _ ( by decide ) ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) M hM ( fun j => h_mag _ ) inv _ |>.1 using 1;
  · convert gen_dft_sub_component_bound ( 2 ^ k' ) ( Nat.one_le_pow _ _ ( by decide ) ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) M hM ( fun j => h_mag _ ) inv ⟨ i - 2 ^ k', by omega ⟩ |>.2 using 1;
  · rw [ show G_bound ε₀ M ( k' + 1 ) = 3 * G_bound ε₀ M k' + 2 * ( 2 ^ k' : ℝ ) * M + 1 by
          unfold G_bound; ring; ];
    norm_num [ G_bound ] at *;
    exact Or.inl ( by nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 3 ) k', pow_pos ( by norm_num : ( 0 : ℝ ) < 2 ) k', pow_succ' ( 3 : ℝ ) k', pow_succ' ( 2 : ℝ ) k' ] )

/-! ## Part 10: Main induction -/

/-- The FFT error bound with the tight bound G(k). -/
lemma fft_error_bound_tight (k : ℕ) (P : ℕ) (hP : P ≥ 1)
    (x : Vector (FPComplex P) (2^k)) (inv : Bool)
    (x_exact : Fin (2^k) → ℂ)
    (ε₀ : ℝ) (M : ℝ) (hε : ε₀ ≥ 0) (hM : M ≥ 0)
    (h_approx : ∀ i : Fin (2^k),
      |(↑(x.get i).re : ℝ) - (x_exact i).re * 2^P| ≤ ε₀ ∧
      |(↑(x.get i).im : ℝ) - (x_exact i).im * 2^P| ≤ ε₀)
    (h_mag : ∀ i : Fin (2^k), |(x_exact i).re| ≤ M ∧ |(x_exact i).im| ≤ M)
    (h_prec : (ε₀ + 2 * M + 1) * (3 : ℝ)^k ≤ 2^(P - 1)) :
    ∀ i : Fin (2^k),
      |(↑((FPComplex.fft x inv).get i).re : ℝ) - (gen_dft (2^k) x_exact inv i).re * 2^P| ≤ G_bound ε₀ M k ∧
      |(↑((FPComplex.fft x inv).get i).im : ℝ) - (gen_dft (2^k) x_exact inv i).im * 2^P| ≤ G_bound ε₀ M k := by
  induction k with
  | zero =>
    intro i; rw [G_bound_zero]
    have : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst this
    simp [FPComplex.fft, gen_dft]
    exact h_approx ⟨0, by omega⟩
  | succ k' ih =>
    intro i
    have h_prec' : (ε₀ + 2 * M + 1) * (3 : ℝ)^k' ≤ 2^(P - 1) :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_succ _)) (by positivity)) h_prec
    have h_even_approx : ∀ j : Fin (2^k'),
        |(↑((Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)).get j).re : ℝ) -
          (x_exact ⟨2*j.val, by omega⟩).re * 2^P| ≤ ε₀ ∧
        |(↑((Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)).get j).im : ℝ) -
          (x_exact ⟨2*j.val, by omega⟩).im * 2^P| ≤ ε₀ := by
      intro j; simp only [Vector.get_ofFn]; exact h_approx ⟨2*j.val, by omega⟩
    have h_even_mag : ∀ j : Fin (2^k'),
        |(x_exact ⟨2*j.val, by omega⟩).re| ≤ M ∧
        |(x_exact ⟨2*j.val, by omega⟩).im| ≤ M := by
      intro j; exact h_mag ⟨2*j.val, by omega⟩
    have IH_E : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get j).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv j).re * 2^P| ≤ G_bound ε₀ M k' ∧
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get j).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv j).im * 2^P| ≤ G_bound ε₀ M k' := by
      exact ih (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega))
        (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩)
        h_even_approx h_even_mag h_prec'
    have h_odd_approx : ∀ j : Fin (2^k'),
        |(↑((Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)).get j).re : ℝ) -
          (x_exact ⟨2*j.val+1, by omega⟩).re * 2^P| ≤ ε₀ ∧
        |(↑((Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)).get j).im : ℝ) -
          (x_exact ⟨2*j.val+1, by omega⟩).im * 2^P| ≤ ε₀ := by
      intro j; simp only [Vector.get_ofFn]; exact h_approx ⟨2*j.val+1, by omega⟩
    have h_odd_mag : ∀ j : Fin (2^k'),
        |(x_exact ⟨2*j.val+1, by omega⟩).re| ≤ M ∧
        |(x_exact ⟨2*j.val+1, by omega⟩).im| ≤ M := by
      intro j; exact h_mag ⟨2*j.val+1, by omega⟩
    have IH_O : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get j).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv j).re * 2^P| ≤ G_bound ε₀ M k' ∧
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get j).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv j).im * 2^P| ≤ G_bound ε₀ M k' := by
      exact ih (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega))
        (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩)
        h_odd_approx h_odd_mag h_prec'
    by_cases hi : i.val < 2^k'
    · exact fft_error_step_lo k' P hP x inv x_exact ε₀ M hε hM h_mag h_prec i hi
        (fun j => (IH_E j).1) (fun j => (IH_E j).2)
        (fun j => (IH_O j).1) (fun j => (IH_O j).2)
    · exact fft_error_step_hi k' P hP x inv x_exact ε₀ M hε hM h_mag h_prec i hi
        (fun j => (IH_E j).1) (fun j => (IH_E j).2)
        (fun j => (IH_O j).1) (fun j => (IH_O j).2)

/-- fft_error_bound follows from fft_error_bound_tight via G_bound_le. -/
lemma fft_error_bound' (k : ℕ) (P : ℕ) (hP : P ≥ 1)
    (x : Vector (FPComplex P) (2^k)) (inv : Bool)
    (x_exact : Fin (2^k) → ℂ)
    (ε₀ : ℝ) (M : ℝ) (hε : ε₀ ≥ 0) (hM : M ≥ 0)
    (h_approx : ∀ i : Fin (2^k),
      |(↑(x.get i).re : ℝ) - (x_exact i).re * 2^P| ≤ ε₀ ∧
      |(↑(x.get i).im : ℝ) - (x_exact i).im * 2^P| ≤ ε₀)
    (h_mag : ∀ i : Fin (2^k), |(x_exact i).re| ≤ M ∧ |(x_exact i).im| ≤ M)
    (h_prec : (ε₀ + 2 * M + 1) * (3 : ℝ)^k ≤ 2^(P - 1)) :
    ∀ i : Fin (2^k),
      |(↑((FPComplex.fft x inv).get i).re : ℝ) - (gen_dft (2^k) x_exact inv i).re * 2^P| ≤ (ε₀ + 2 * M + 1) * 3^k ∧
      |(↑((FPComplex.fft x inv).get i).im : ℝ) - (gen_dft (2^k) x_exact inv i).im * 2^P| ≤ (ε₀ + 2 * M + 1) * 3^k := by
  intro i
  have h := fft_error_bound_tight k P hP x inv x_exact ε₀ M hε hM h_approx h_mag h_prec i
  exact ⟨le_trans h.1 (G_bound_le ε₀ M hM k), le_trans h.2 (G_bound_le ε₀ M hM k)⟩

end

end FFTErrorInduction


/- ========================================================================
   Section: FFTErrorNPC
   ======================================================================== -/

section FFTErrorNPC

/-!
# FFT Error Bound Without Precision Condition

This file provides a version of the FFT error bound that does not require the
precision condition `(ε₀ + 2*M + 1)*3^k ≤ 2^(P-1)`.

The bound is `(ε₀ + 2*M + 1) * (3 + 1/2^P)^k`.
-/

open Complex Finset

noncomputable section

/-! ## NPC bound function -/

/-- The inductive invariant for the NPC error analysis. -/
def G_npc (ε₀ M : ℝ) (P : ℕ) (k : ℕ) : ℝ :=
  (ε₀ + 2*M + 1)*(3+1/(2:ℝ)^P)^k - (2*M+1/2)*2^k

lemma G_npc_le (ε₀ M : ℝ) (P : ℕ) (hM : M ≥ 0) (k : ℕ) :
    G_npc ε₀ M P k ≤ (ε₀ + 2*M + 1) * (3 + 1/(2:ℝ)^P)^k := by
  unfold G_npc; linarith [mul_nonneg (by linarith : 2*M+1/2 ≥ 0) (pow_nonneg (by norm_num : (2:ℝ) ≥ 0) k)]

lemma G_npc_nonneg (ε₀ M : ℝ) (P : ℕ) (hε : ε₀ ≥ 0) (hM : M ≥ 0) (k : ℕ) :
    G_npc ε₀ M P k ≥ 0 := by
  refine' sub_nonneg_of_le _;
  exact mul_le_mul ( by linarith ) ( pow_le_pow_left₀ ( by positivity ) ( by linarith [ show ( 1 : ℝ ) / 2 ^ P ≥ 0 by positivity ] ) _ ) ( by positivity ) ( by positivity )

/-! ## Butterfly error without precision condition -/

lemma butterfly_error_lo_npc (K : ℕ) (P : ℕ) (hK : K ≥ 1) (hP : P ≥ 1)
    (E' O' : FPComplex P) (T : FPComplex P)
    (E_exact O_exact : ℂ) (w_j : ℂ)
    (ε : ℝ) (M : ℝ) (hε : ε ≥ 0) (hM : M ≥ 0)
    (hE_re : |(↑E'.re : ℝ) - E_exact.re * 2^P| ≤ ε)
    (hE_im : |(↑E'.im : ℝ) - E_exact.im * 2^P| ≤ ε)
    (hO_re : |(↑O'.re : ℝ) - O_exact.re * 2^P| ≤ ε)
    (hO_im : |(↑O'.im : ℝ) - O_exact.im * 2^P| ≤ ε)
    (hT_re : |(↑T.re : ℝ) - w_j.re * 2^P| ≤ 1/2)
    (hT_im : |(↑T.im : ℝ) - w_j.im * 2^P| ≤ 1/2)
    (hw_re : |w_j.re| ≤ 1) (hw_im : |w_j.im| ≤ 1)
    (hO_mag_re : |O_exact.re| ≤ 2 * K * M) (hO_mag_im : |O_exact.im| ≤ 2 * K * M) :
    |(↑(FPComplex.cadd E' (FPComplex.cmul T O')).re : ℝ) -
      (E_exact + w_j * O_exact).re * 2^P| ≤ (3 + 1/(2:ℝ)^P) * ε + 2 * K * M + 1/2 ∧
    |(↑(FPComplex.cadd E' (FPComplex.cmul T O')).im : ℝ) -
      (E_exact + w_j * O_exact).im * 2^P| ≤ (3 + 1/(2:ℝ)^P) * ε + 2 * K * M + 1/2 := by
  have h_cmul_error : |(FPComplex.cmul T O').re - (w_j * O_exact).re * 2 ^ P| ≤ 2 * (1 * ε + (1 / 2) * (2 * K * M)) + 2 * (1 / 2) * ε / 2 ^ P + 1 / 2 ∧ |(FPComplex.cmul T O').im - (w_j * O_exact).im * 2 ^ P| ≤ 2 * (1 * ε + (1 / 2) * (2 * K * M)) + 2 * (1 / 2) * ε / 2 ^ P + 1 / 2 := by
    apply_rules [ cmul_error_bound ]
    · norm_num
    · norm_num
    · positivity
  norm_num [ Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, FPComplex.cadd ] at *
  exact ⟨ abs_le.mpr ⟨ by ring_nf at *; linarith [ abs_le.mp hE_re, abs_le.mp h_cmul_error.1 ], by ring_nf at *; linarith [ abs_le.mp hE_re, abs_le.mp h_cmul_error.1 ] ⟩, abs_le.mpr ⟨ by ring_nf at *; linarith [ abs_le.mp hE_im, abs_le.mp h_cmul_error.2 ], by ring_nf at *; linarith [ abs_le.mp hE_im, abs_le.mp h_cmul_error.2 ] ⟩ ⟩

lemma butterfly_error_hi_npc (K : ℕ) (P : ℕ) (hK : K ≥ 1) (hP : P ≥ 1)
    (E' O' : FPComplex P) (T : FPComplex P)
    (E_exact O_exact : ℂ) (w_j : ℂ)
    (ε : ℝ) (M : ℝ) (hε : ε ≥ 0) (hM : M ≥ 0)
    (hE_re : |(↑E'.re : ℝ) - E_exact.re * 2^P| ≤ ε)
    (hE_im : |(↑E'.im : ℝ) - E_exact.im * 2^P| ≤ ε)
    (hO_re : |(↑O'.re : ℝ) - O_exact.re * 2^P| ≤ ε)
    (hO_im : |(↑O'.im : ℝ) - O_exact.im * 2^P| ≤ ε)
    (hT_re : |(↑T.re : ℝ) - w_j.re * 2^P| ≤ 1/2)
    (hT_im : |(↑T.im : ℝ) - w_j.im * 2^P| ≤ 1/2)
    (hw_re : |w_j.re| ≤ 1) (hw_im : |w_j.im| ≤ 1)
    (hO_mag_re : |O_exact.re| ≤ 2 * K * M) (hO_mag_im : |O_exact.im| ≤ 2 * K * M) :
    |(↑(FPComplex.csub E' (FPComplex.cmul T O')).re : ℝ) -
      (E_exact - w_j * O_exact).re * 2^P| ≤ (3 + 1/(2:ℝ)^P) * ε + 2 * K * M + 1/2 ∧
    |(↑(FPComplex.csub E' (FPComplex.cmul T O')).im : ℝ) -
      (E_exact - w_j * O_exact).im * 2^P| ≤ (3 + 1/(2:ℝ)^P) * ε + 2 * K * M + 1/2 := by
  have := @cmul_error_bound P hP
  specialize this T O' w_j O_exact ( 1 / 2 ) ε 1 ( 2 * K * M ) ; norm_num at *
  unfold FPComplex.csub at *; norm_num [ abs_le ] at *
  grind +splitImp

/-! ## Recurrence bound -/

lemma npc_recurrence_bound (ε₀ M : ℝ) (P : ℕ) (hP : P ≥ 1) (hε : ε₀ ≥ 0) (hM : M ≥ 0) :
    ∀ k : ℕ, ∀ G : ℝ, G ≤ G_npc ε₀ M P k →
    (3+1/(2:ℝ)^P)*G + 2*2^k*M + 1/2 ≤ G_npc ε₀ M P (k+1) := by
  intro k G hG
  refine le_trans ( add_le_add_three ( mul_le_mul_of_nonneg_left hG ( by positivity ) ) le_rfl le_rfl ) ?_;
  unfold G_npc;
  ring_nf;
  nlinarith [ show ( 2 : ℝ ) ^ k ≥ 1 by exact one_le_pow₀ ( by norm_num ), show ( 2⁻¹ : ℝ ) ^ P ≥ 0 by positivity, show ( 2⁻¹ : ℝ ) ^ P * 2 ^ k ≥ 0 by positivity, show ( 2⁻¹ : ℝ ) ^ P ≤ 1 by exact pow_le_one₀ ( by norm_num ) ( by norm_num ) ]

/-! ## FFT error step lemmas (NPC versions) -/

/-
Lo-half NPC step: for i < 2^k'.
-/
lemma fft_error_step_lo_npc (k' : ℕ) (P : ℕ) (hP : P ≥ 1)
    (x : Vector (FPComplex P) (2^(k'+1))) (inv : Bool)
    (x_exact : Fin (2^(k'+1)) → ℂ)
    (ε₀ M : ℝ) (hε : ε₀ ≥ 0) (hM : M ≥ 0)
    (h_mag : ∀ i : Fin (2^(k'+1)), |(x_exact i).re| ≤ M ∧ |(x_exact i).im| ≤ M)
    (i : Fin (2^(k'+1))) (hi : i.val < 2^k')
    (IH_E_re : |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get ⟨i.val, hi⟩).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv ⟨i.val, hi⟩).re * 2^P| ≤ G_npc ε₀ M P k')
    (IH_E_im : |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get ⟨i.val, hi⟩).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv ⟨i.val, hi⟩).im * 2^P| ≤ G_npc ε₀ M P k')
    (IH_O_re : |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get ⟨i.val, hi⟩).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv ⟨i.val, hi⟩).re * 2^P| ≤ G_npc ε₀ M P k')
    (IH_O_im : |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get ⟨i.val, hi⟩).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv ⟨i.val, hi⟩).im * 2^P| ≤ G_npc ε₀ M P k') :
    |(↑((FPComplex.fft x inv).get i).re : ℝ) - (gen_dft (2^(k'+1)) x_exact inv i).re * 2^P| ≤ G_npc ε₀ M P (k'+1) ∧
    |(↑((FPComplex.fft x inv).get i).im : ℝ) - (gen_dft (2^(k'+1)) x_exact inv i).im * 2^P| ≤ G_npc ε₀ M P (k'+1) := by
  rw [ fft_succ_lo k' P x inv i hi, gen_dft_cooley_tukey_lo' k' x_exact inv i hi ];
  have := butterfly_error_lo_npc ( 2 ^ k' ) P ( Nat.one_le_pow _ _ zero_lt_two ) hP;
  specialize this (FPComplex.fft (Vector.ofFn fun j => x[2 * j.val]) inv |>.get ⟨i.val, hi⟩) (FPComplex.fft (Vector.ofFn fun j => x[2 * j.val + 1]) inv |>.get ⟨i.val, hi⟩) (FPComplex.t_table (2^k') inv P |>.get ⟨i.val, hi⟩) (gen_dft (2^k') (fun j => x_exact ⟨2 * j.val, by omega⟩) inv ⟨i.val, hi⟩) (gen_dft (2^k') (fun j => x_exact ⟨2 * j.val + 1, by omega⟩) inv ⟨i.val, hi⟩) ((if inv then (omega (2^(k'+1)))⁻¹ else omega (2^(k'+1))) ^ i.val) (G_npc ε₀ M P k') M (by
  exact G_npc_nonneg ε₀ M P hε hM k') (by
  exact hM) (by
  exact IH_E_re) (by
  exact IH_E_im) (by
  exact IH_O_re) (by
  exact IH_O_im) (by
  convert t_table_exact_value ( 2 ^ k' ) i.val ( Nat.one_le_pow _ _ zero_lt_two ) hi inv P |>.1 using 1;
  grind +splitImp) (by
  convert t_table_exact_value ( 2 ^ k' ) i.val ( Nat.one_le_pow _ _ zero_lt_two ) hi inv P |>.2 using 1;
  rw [ ← pow_succ' ]) (by
  convert omega_pow_component_bound ( 2 ^ k' ) i.val ( Nat.one_le_pow _ _ zero_lt_two ) inv |>.1 using 1;
  rw [ ← pow_succ' ]) (by
  convert omega_pow_component_bound ( 2 ^ k' ) i.val ( Nat.one_le_pow _ _ zero_lt_two ) inv |>.2 using 1;
  rw [ ← pow_succ' ]);
  refine' this _ _ |> fun h => ⟨ h.1.trans _, h.2.trans _ ⟩;
  · have := gen_dft_sub_component_bound ( 2 ^ k' ) ( Nat.one_le_pow _ _ zero_lt_two ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) M hM ( fun j => h_mag _ ) inv ⟨ i.val, hi ⟩ ; norm_num at * ; linarith;
  · have := gen_dft_sub_component_bound ( 2 ^ k' ) ( Nat.one_le_pow _ _ zero_lt_two ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) M hM ( fun j => h_mag ⟨ 2 * j.val + 1, by omega ⟩ ) inv ⟨ i.val, hi ⟩ ; norm_num at * ; linarith;
  · convert npc_recurrence_bound ε₀ M P hP hε hM k' ( G_npc ε₀ M P k' ) le_rfl using 1;
    norm_num;
  · convert npc_recurrence_bound ε₀ M P hP hε hM k' ( G_npc ε₀ M P k' ) le_rfl using 1;
    norm_num

/-
Hi-half NPC step: for i ≥ 2^k'.
-/
lemma fft_error_step_hi_npc (k' : ℕ) (P : ℕ) (hP : P ≥ 1)
    (x : Vector (FPComplex P) (2^(k'+1))) (inv : Bool)
    (x_exact : Fin (2^(k'+1)) → ℂ)
    (ε₀ M : ℝ) (hε : ε₀ ≥ 0) (hM : M ≥ 0)
    (h_mag : ∀ i : Fin (2^(k'+1)), |(x_exact i).re| ≤ M ∧ |(x_exact i).im| ≤ M)
    (i : Fin (2^(k'+1))) (hi : ¬i.val < 2^k')
    (IH_E_re : |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get ⟨i.val - 2^k', by omega⟩).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv ⟨i.val - 2^k', by omega⟩).re * 2^P| ≤ G_npc ε₀ M P k')
    (IH_E_im : |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get ⟨i.val - 2^k', by omega⟩).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv ⟨i.val - 2^k', by omega⟩).im * 2^P| ≤ G_npc ε₀ M P k')
    (IH_O_re : |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get ⟨i.val - 2^k', by omega⟩).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv ⟨i.val - 2^k', by omega⟩).re * 2^P| ≤ G_npc ε₀ M P k')
    (IH_O_im : |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get ⟨i.val - 2^k', by omega⟩).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv ⟨i.val - 2^k', by omega⟩).im * 2^P| ≤ G_npc ε₀ M P k') :
    |(↑((FPComplex.fft x inv).get i).re : ℝ) - (gen_dft (2^(k'+1)) x_exact inv i).re * 2^P| ≤ G_npc ε₀ M P (k'+1) ∧
    |(↑((FPComplex.fft x inv).get i).im : ℝ) - (gen_dft (2^(k'+1)) x_exact inv i).im * 2^P| ≤ G_npc ε₀ M P (k'+1) := by
  convert butterfly_error_hi_npc ( 2 ^ k' ) P ( Nat.one_le_pow _ _ zero_lt_two ) hP _ _ _ _ _ _ _ _ _ _ _ _ using 1;
  any_goals exact IH_E_re;
  any_goals assumption;
  rotate_left;
  exact ( FPComplex.fft ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val + 1]'( by omega ) ) inv ).get ⟨ i.val - 2 ^ k', by omega ⟩;
  exact ( FPComplex.t_table ( 2 ^ k' ) inv P ).get ⟨ i.val - 2 ^ k', by omega ⟩;
  exact gen_dft ( 2 ^ k' ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) inv ⟨ i.val - 2 ^ k', by omega ⟩;
  exact ( if inv then ( omega ( 2 ^ ( k' + 1 ) ) ) ⁻¹ else omega ( 2 ^ ( k' + 1 ) ) ) ^ ( i.val - 2 ^ k' );
  · exact G_npc_nonneg ε₀ M P hε hM k';
  · constructor;
    · intro h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉;
      convert butterfly_error_hi_npc ( 2 ^ k' ) P ( Nat.one_le_pow _ _ zero_lt_two ) hP _ _ _ _ _ _ _ _ _ _ _ _ using 1;
      rotate_left;
      exact ( FPComplex.fft ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val] ) inv ).get ⟨ i.val - 2 ^ k', by omega ⟩;
      exact ( FPComplex.fft ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val + 1] ) inv ).get ⟨ i.val - 2 ^ k', by omega ⟩;
      exact ( FPComplex.t_table ( 2 ^ k' ) inv P ).get ⟨ i.val - 2 ^ k', by omega ⟩;
      exact gen_dft ( 2 ^ k' ) ( fun j => x_exact ⟨ 2 * j.val, by omega ⟩ ) inv ⟨ i.val - 2 ^ k', by omega ⟩;
      exact gen_dft ( 2 ^ k' ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) inv ⟨ i.val - 2 ^ k', by omega ⟩;
      exact ( if inv then ( omega ( 2 ^ ( k' + 1 ) ) ) ⁻¹ else omega ( 2 ^ ( k' + 1 ) ) ) ^ ( i.val - 2 ^ k' );
      exact G_npc ε₀ M P k';
      exact M;
      · exact G_npc_nonneg ε₀ M P hε hM k';
      · exact hM;
      · exact IH_E_re;
      · exact IH_E_im;
      · grind +splitImp;
    · intro h;
      contrapose! h;
      refine' ⟨ IH_O_re, IH_O_im, _, _, _, _, _ ⟩;
      · convert t_table_exact_value ( 2 ^ k' ) ( i.val - 2 ^ k' ) ( Nat.one_le_pow _ _ zero_lt_two ) ( by omega ) inv P |>.1 using 1;
        rw [ ← pow_succ' ];
      · convert t_table_exact_value ( 2 ^ k' ) ( i.val - 2 ^ k' ) ( Nat.one_le_pow _ _ zero_lt_two ) ( by omega ) inv P |>.2 using 1;
        rw [ ← pow_succ' ];
      · convert omega_pow_component_bound ( 2 ^ k' ) ( i.val - 2 ^ k' ) ( Nat.one_le_pow _ _ zero_lt_two ) inv |>.1 using 1;
        rw [ ← pow_succ' ];
      · split_ifs <;> norm_num [ Complex.normSq, Complex.norm_def, omega ];
        · norm_num [ ← sq, Complex.exp_re, Complex.exp_im, ← Complex.exp_nat_mul ];
          norm_num [ Complex.normSq, Complex.div_re, Complex.div_im, Complex.exp_re, Complex.exp_im, pow_succ' ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ];
          norm_cast ; norm_num [ Real.sin_sq, Real.cos_sq ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ];
          exact Real.abs_sin_le_one _;
        · norm_num [ ← Complex.exp_nat_mul, Complex.exp_im ];
          norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_succ' ];
          norm_cast ; norm_num;
          exact Real.abs_sin_le_one _;
      · refine' ⟨ _, _, _ ⟩;
        · have := gen_dft_sub_component_bound ( 2 ^ k' ) ( Nat.one_le_pow _ _ zero_lt_two ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) M hM ( fun j => h_mag ⟨ 2 * j.val + 1, by omega ⟩ ) inv ⟨ i.val - 2 ^ k', by omega ⟩ ; norm_num at * ; linarith;
        · have := gen_dft_sub_component_bound ( 2 ^ k' ) ( Nat.one_le_pow _ _ zero_lt_two ) ( fun j => x_exact ⟨ 2 * j.val + 1, by omega ⟩ ) M hM ( fun j => h_mag ⟨ 2 * j.val + 1, by omega ⟩ ) inv ⟨ i.val - 2 ^ k', by omega ⟩ ; norm_num at * ; linarith;
        · intro h;
          rename_i h';
          contrapose! h';
          rw [ fft_succ_hi k' P x inv i hi, gen_dft_cooley_tukey_hi' k' x_exact inv i hi ];
          exact ⟨ h.trans ( by simpa using npc_recurrence_bound ε₀ M P hP hε hM k' ( G_npc ε₀ M P k' ) le_rfl ), h'.trans ( by simpa using npc_recurrence_bound ε₀ M P hP hε hM k' ( G_npc ε₀ M P k' ) le_rfl ) ⟩

/-- NPC step lemma: combines butterfly_error_npc with the NPC recurrence. -/
lemma fft_error_step_npc (k' : ℕ) (P : ℕ) (hP : P ≥ 1)
    (x : Vector (FPComplex P) (2^(k'+1))) (inv : Bool)
    (x_exact : Fin (2^(k'+1)) → ℂ)
    (ε₀ M : ℝ) (hε : ε₀ ≥ 0) (hM : M ≥ 0)
    (h_mag : ∀ i : Fin (2^(k'+1)), |(x_exact i).re| ≤ M ∧ |(x_exact i).im| ≤ M)
    (IH_E : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get j).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv j).re * 2^P| ≤ G_npc ε₀ M P k' ∧
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val]'(by omega)) inv).get j).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val, by omega⟩) inv j).im * 2^P| ≤ G_npc ε₀ M P k')
    (IH_O : ∀ j : Fin (2^k'),
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get j).re : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv j).re * 2^P| ≤ G_npc ε₀ M P k' ∧
      |(↑((FPComplex.fft (Vector.ofFn fun j : Fin (2^k') => x[2 * j.val + 1]'(by omega)) inv).get j).im : ℝ) -
        (gen_dft (2^k') (fun j : Fin (2^k') => x_exact ⟨2*j.val+1, by omega⟩) inv j).im * 2^P| ≤ G_npc ε₀ M P k') :
    ∀ i : Fin (2^(k'+1)),
    |(↑((FPComplex.fft x inv).get i).re : ℝ) - (gen_dft (2^(k'+1)) x_exact inv i).re * 2^P| ≤ G_npc ε₀ M P (k'+1) ∧
    |(↑((FPComplex.fft x inv).get i).im : ℝ) - (gen_dft (2^(k'+1)) x_exact inv i).im * 2^P| ≤ G_npc ε₀ M P (k'+1) := by
  intro i
  by_cases hi : i.val < 2^k'
  · exact fft_error_step_lo_npc k' P hP x inv x_exact ε₀ M hε hM h_mag i hi
      (IH_E ⟨i.val, hi⟩).1 (IH_E ⟨i.val, hi⟩).2 (IH_O ⟨i.val, hi⟩).1 (IH_O ⟨i.val, hi⟩).2
  · exact fft_error_step_hi_npc k' P hP x inv x_exact ε₀ M hε hM h_mag i hi
      (IH_E ⟨i.val - 2^k', by omega⟩).1 (IH_E ⟨i.val - 2^k', by omega⟩).2
      (IH_O ⟨i.val - 2^k', by omega⟩).1 (IH_O ⟨i.val - 2^k', by omega⟩).2

/-! ## Main FFT error bound (NPC) -/

lemma fft_error_bound_npc (k : ℕ) (P : ℕ) (hP : P ≥ 1)
    (x : Vector (FPComplex P) (2^k)) (inv : Bool)
    (x_exact : Fin (2^k) → ℂ)
    (ε₀ : ℝ) (M : ℝ) (hε : ε₀ ≥ 0) (hM : M ≥ 0)
    (h_approx : ∀ i : Fin (2^k),
      |(↑(x.get i).re : ℝ) - (x_exact i).re * 2^P| ≤ ε₀ ∧
      |(↑(x.get i).im : ℝ) - (x_exact i).im * 2^P| ≤ ε₀)
    (h_mag : ∀ i : Fin (2^k), |(x_exact i).re| ≤ M ∧ |(x_exact i).im| ≤ M) :
    ∀ i : Fin (2^k),
      |(↑((FPComplex.fft x inv).get i).re : ℝ) - (gen_dft (2^k) x_exact inv i).re * 2^P| ≤ (ε₀ + 2 * M + 1) * (3 + 1/(2:ℝ)^P)^k ∧
      |(↑((FPComplex.fft x inv).get i).im : ℝ) - (gen_dft (2^k) x_exact inv i).im * 2^P| ≤ (ε₀ + 2 * M + 1) * (3 + 1/(2:ℝ)^P)^k := by
  -- Apply the induction hypothesis to the even and odd sub-vectors.
  have h_ind : ∀ i : Fin (2 ^ k), |(↑((FPComplex.fft x inv).get i).re : ℝ) - (gen_dft (2 ^ k) x_exact inv i).re * 2 ^ P| ≤ G_npc ε₀ M P k ∧ |(↑((FPComplex.fft x inv).get i).im : ℝ) - (gen_dft (2 ^ k) x_exact inv i).im * 2 ^ P| ≤ G_npc ε₀ M P k := by
    -- We proceed by induction on $k$.
    induction' k with k ih;
    · simp_all +decide [ Fin.eq_zero, G_npc ] ;
      unfold gen_dft; norm_num [ FPComplex.fft ] ; constructor <;> linarith!;
    · convert fft_error_step_npc k P hP x inv x_exact ε₀ M hε hM h_mag _ _ using 1;
      · convert ih _ _ _ _ using 1;
        · intro i; specialize h_approx ⟨ 2 * i, by linarith [ Fin.is_lt i, pow_succ' 2 k ] ⟩ ; aesop;
        · exact fun i => h_mag _;
      · convert ih _ _ _ _ using 1;
        · grind +suggestions;
        · exact fun i => h_mag _;
  exact fun i => ⟨ le_trans ( h_ind i |>.1 ) ( G_npc_le ε₀ M P hM k ), le_trans ( h_ind i |>.2 ) ( G_npc_le ε₀ M P hM k ) ⟩

/-! ## Pipeline bound -/

/-- The core numerical inequality (clean, division-free, fixed amplification base),
    proved by induction on `n` from 5 with `l ≥ 7` fixed. The amplification factor
    `6 * (3 + 1/128) = 18.046875 < 32 = 2^5` drives the induction step. -/
lemma core2 (n l : ℕ) (hn5 : n ≥ 5) (hl7 : l ≥ 7) :
    (4 * ((2:ℝ)^n * 2^l) * ((2 * 2^l + 1) * 3^n)
      + 5/2 + 2 * ((2:ℝ)^n * 2^l) * ((2:ℝ)^n * 2^l))
      * (3 + 1/(128:ℝ))^n
    < (2:ℝ)^n * 2^(4*n+2*l-1) := by
  induction' hn5 with k hk <;> norm_num [ Nat.mul_succ, pow_succ' ] at *;
  · norm_num [ pow_add, pow_mul' ];
    nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hl7 ];
  · rw [ show 4 * k + 3 + 2 * l = 4 * k + 2 * l - 1 + 4 by omega ] ; ring_nf at * ; norm_num at *;
    nlinarith [ show 0 < ( 2 : ℝ ) ^ k * 2 ^ l * 3 ^ k * ( 385 / 128 ) ^ k by positivity, show 0 < ( 2 : ℝ ) ^ k * 2 ^ ( l * 2 ) * 3 ^ k * ( 385 / 128 ) ^ k by positivity, show 0 < ( 2 : ℝ ) ^ ( k * 2 ) * 2 ^ ( l * 2 ) * ( 385 / 128 ) ^ k by positivity, show 0 < ( 385 / 128 : ℝ ) ^ k by positivity ]

/-- `B ≤ 1`: the complex-multiply cross-error term is bounded by 1 for `n ≥ 5`, `l ≥ 7`. -/
lemma B_le_one (n l : ℕ) (hn5 : n ≥ 5) (hl7 : l ≥ 7) :
    2 * (((2 * (2:ℝ)^l + 1) * 3^n) * ((2 * (2:ℝ)^l + 1) * 3^n)) / 2^(4*n+2*l) ≤ 1 := by
  have h_simp : 2 * (257 / 128 : ℝ) ^ 2 * (9 : ℝ) ^ n ≤ (16 : ℝ) ^ n := by
    exact Nat.le_induction ( by norm_num ) ( fun k hk ih ↦ by norm_num [ pow_succ' ] at * ; linarith [ pow_pos ( by norm_num : 0 < ( 9 : ℝ ) ) k, pow_le_pow_left₀ ( by norm_num ) ( by norm_num : ( 16 : ℝ ) ≥ 9 ) k ] ) n hn5;
  rw [ div_le_iff₀ ( by positivity ) ];
  have h_final : 2 * ((2 * 2 ^ l + 1) * 3 ^ n * ((2 * 2 ^ l + 1) * 3 ^ n)) ≤ 2 * ((257 / 128 : ℝ) * 2 ^ l * 3 ^ n * ((257 / 128 : ℝ) * 2 ^ l * 3 ^ n)) := by
    gcongr; all_goals linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hl7 ];
  convert h_final.trans _ using 1 ; ring_nf at * ; norm_num [ pow_mul' ] at *;
  convert mul_le_mul_of_nonneg_left h_simp ( by positivity : ( 0 : ℝ ) ≤ 4 ^ l ) using 1 ; ring

lemma pipeline_numerical_bound_npc (n l : ℕ) (hn5 : n ≥ 5) (hl7 : l ≥ 7) :
    let P := knuth_bound n l
    let K := 2^n
    let ε_fwd := (2 * (2 : ℝ)^l + 1) * 3^n
    let M_dft := (K : ℝ) * 2^l
    let ε_cmul := 2 * (M_dft * ε_fwd + ε_fwd * M_dft) + 2 * ε_fwd * ε_fwd / 2^P + 1/2
    let M_prod := M_dft * M_dft
    let ε_inv := (ε_cmul + 2 * M_prod + 1) * (3 + 1/(2:ℝ)^P)^n
    ε_inv < (K : ℝ) * 2^(P - 1) := by
  refine lt_of_le_of_lt ?_ ( core2 n l hn5 hl7 );
  refine' mul_le_mul _ _ _ _;
  · have := B_le_one n l hn5 hl7;
    unfold knuth_bound; ring_nf at *; linarith;
  · gcongr;
    exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) ( show 4 * n + 2 * l ≥ 7 by linarith ) );
  · positivity;
  · positivity

end

end FFTErrorNPC


/- ========================================================================
   Section: FFTConv
   ======================================================================== -/

section FFTConv

open Complex Finset

noncomputable section

/-! ## Section 1: Rounding correctness -/

lemma shr_round_of_close (k ε : ℤ) (P : ℕ) (hP : P ≥ 1)
    (h_lo : -(2 : ℤ)^(P-1 : ℕ) ≤ ε) (h_hi : ε < 2^(P-1 : ℕ)) :
    FPComplex.shr_round (k * 2^P + ε) P = k := by
  rcases P with ( _ | P ) <;> simp_all +decide [ pow_succ, mul_assoc ]
  unfold FPComplex.shr_round; norm_num [ Int.shiftRight_eq_div_pow ] ; ring
  exact Int.le_antisymm ( Int.le_of_lt_add_one <| Int.ediv_lt_of_lt_mul ( by positivity ) <| by linarith ) ( Int.le_ediv_of_mul_le ( by positivity ) <| by linarith )

lemma round_re_eq_shr (v w : ℤ) (P : ℕ) (hP : P ≥ 1) :
    FPComplex.round_re (P := P) ⟨v, w⟩ = FPComplex.shr_round v P := by
  simp [FPComplex.round_re, FPComplex.shr_round, show P ≠ 0 by omega]

/-! ## Section 2: Floor division properties -/

lemma int_ediv_add_of_dvd (a b : ℤ) (K : ℤ) (hK : K > 0) (h : K ∣ a) :
    (a + b) / K = a / K + b / K := by
  obtain ⟨c, rfl⟩ := h
  rw [show K * c + b = b + K * c by ring, Int.add_mul_ediv_left _ _ hK.ne']
  rw [Int.mul_ediv_cancel_left c hK.ne']; ring

lemma int_ediv_bound (b : ℤ) (K M : ℤ) (hK : K > 0) (_hM : M > 0)
    (h : |b| < K * M) :
    -M ≤ b / K ∧ b / K ≤ M - 1 := by
  constructor <;> nlinarith [ Int.mul_ediv_add_emod b K, Int.emod_nonneg b hK.ne', Int.emod_lt_of_pos b hK, abs_lt.mp h ]

/-! ## Section 3: Rounding pipeline -/

lemma rounding_pipeline_correct (C_re : ℤ) (conv_m : ℤ)
    (K : ℕ) (P : ℕ) (hK : K ≥ 2) (hP : P ≥ 1)
    (h_error : |C_re - (K : ℤ) * conv_m * 2^P| < (K : ℤ) * 2^(P - 1 : ℕ)) :
    FPComplex.round_re (P := P) ⟨C_re / (K : ℤ), 0⟩ = conv_m := by
  rw [round_re_eq_shr _ _ _ hP]
  set err := C_re - (K : ℤ) * conv_m * 2^P
  have hC_re : C_re = (K : ℤ) * conv_m * 2^P + err := by omega
  rw [hC_re]
  have hK_dvd : (K : ℤ) ∣ ((K : ℤ) * conv_m * 2^P) := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hK_pos : (K : ℤ) > 0 := by positivity
  rw [int_ediv_add_of_dvd _ _ _ hK_pos hK_dvd]
  rw [show (K : ℤ) * conv_m * 2^P / (K : ℤ) = conv_m * 2^P from by
    rw [mul_assoc, Int.mul_ediv_cancel_left _ (by omega : (K : ℤ) ≠ 0)]]
  exact shr_round_of_close conv_m (err / K) P hP
    (int_ediv_bound err K (2^(P-1 : ℕ)) hK_pos (by positivity) h_error).1
    (by linarith [(int_ediv_bound err K (2^(P-1 : ℕ)) hK_pos (by positivity) h_error).2])

/-! ## Section 4: Pipeline error bound helpers -/

lemma fwd_fft_prec (n l P : ℕ) (hn : n ≥ 1) (_hl : l ≥ 1) (hP : P = knuth_bound n l) :
    (0 + 2 * (2 : ℝ)^l + 1) * 3^n ≤ 2^(P - 1) := by
  subst hP
  unfold knuth_bound
  have e : 4 * n + 2 * l - 1 = (2*n + l + 2) + (2*n + l - 3) := by omega
  rw [e, pow_add]
  have h3 : (3:ℝ)^n ≤ 2^(2*n) := by
    rw [pow_mul]; gcongr; norm_num
  have hl1 : (0 + 2 * (2:ℝ)^l + 1) ≤ 2^(l+2) := by
    have he : (2:ℝ)^(l+2) = 4 * 2^l := by rw [pow_add]; ring
    rw [he]
    nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) l, one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := l)]
  have key : (0 + 2 * (2:ℝ)^l + 1) * 3^n ≤ 2^(l+2) * 2^(2*n) := by
    apply mul_le_mul hl1 h3 (by positivity) (by positivity)
  calc (0 + 2 * (2:ℝ)^l + 1) * 3^n ≤ 2^(l+2) * 2^(2*n) := key
    _ = 2^(2*n+l+2) := by rw [← pow_add]; ring_nf
    _ ≤ 2^(2*n+l+2) * 2^(2*n+l-3) := by
        nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := 2*n+l-3), pow_pos (show (0:ℝ)<2 by norm_num) (2*n+l+2)]

/-! ## Section 5: Forward FFT error for digit inputs -/

/-
The forward FFT on integer digit inputs approximates the gen_dft with error (2*2^l+1)*3^n.
-/
lemma fwd_fft_digit_error (n l P : ℕ) (hn : n ≥ 1) (hl : l ≥ 1) (hP : P = knuth_bound n l)
    (D : Fin (2^n) → ℤ) (hD : ∀ j, |D j| < 2^l)
    (X : Vector (FPComplex P) (2^n))
    (hX : X = Vector.ofFn fun i => FPComplex.ofInt (D i)) :
    let X_hat := FPComplex.fft (k := n) X false
    let D_exact : Fin (2^n) → ℂ := fun i => (↑(D i) : ℂ)
    ∀ i : Fin (2^n),
      |(↑(X_hat.get i).re : ℝ) - (gen_dft (2^n) D_exact false i).re * 2^P| ≤ (2 * (2:ℝ)^l + 1) * 3^n ∧
      |(↑(X_hat.get i).im : ℝ) - (gen_dft (2^n) D_exact false i).im * 2^P| ≤ (2 * (2:ℝ)^l + 1) * 3^n := by
  convert fft_error_bound' n P ( by linarith [ show knuth_bound n l ≥ 1 by exact Nat.succ_le_of_lt ( by unfold knuth_bound; linarith ) ] ) X false ( fun i => ( D i : ℂ ) ) 0 ( 2 ^ l ) ( by linarith ) ( by linarith [ pow_pos ( by linarith : 0 < ( 2 : ℝ ) ) l ] ) _ _ ( fwd_fft_prec n l P hn hl hP ) using 1;
  · norm_num;
  · simp [hX, FPComplex.ofInt];
  · norm_num [ abs_le ];
    exact fun i => ⟨ neg_le_of_abs_le ( mod_cast le_of_lt ( hD i ) ), le_of_abs_le ( mod_cast le_of_lt ( hD i ) ) ⟩

/-! ## Section 6: DFT norm bound and product component bound -/

/-
The norm of gen_dft output is bounded by K * M for real inputs with components bounded by M.
-/
lemma gen_dft_norm_bound_real (K : ℕ) (hK : K ≥ 1) (x : Fin K → ℂ)
    (M : ℝ) (hM : M ≥ 0)
    (hx_re : ∀ j : Fin K, |(x j).re| ≤ M)
    (hx_im : ∀ j : Fin K, (x j).im = 0)
    (inv : Bool) (m : Fin K) :
    ‖gen_dft K x inv m‖ ≤ K * M := by
  refine' le_trans ( norm_sum_le _ _ ) _;
  convert Finset.sum_le_card_nsmul _ _ _ _ <;> norm_num;
  · ext; norm_num;
  · infer_instance;
  · intro j; split_ifs <;> simp_all +decide [ Complex.norm_def, Complex.normSq ] ;
    · simp_all +decide [ omega, Complex.exp_re, Complex.exp_im ];
      norm_num [ ← sq ];
      rw [ Real.sqrt_sq_eq_abs ] ; exact hx_re j;
    · simp_all +decide [ omega, Complex.exp_re, Complex.exp_im ];
      norm_num [ ← sq, Real.sqrt_sq_eq_abs ];
      exact hx_re j

/-
Component bound on a product of two complex numbers using norm bounds.
-/
lemma product_component_bound_via_norm (α β : ℂ) (Ma Mb : ℝ)
    (hMa : Ma ≥ 0) (hMb : Mb ≥ 0)
    (ha : ‖α‖ ≤ Ma) (hb : ‖β‖ ≤ Mb) :
    |(α * β).re| ≤ Ma * Mb ∧ |(α * β).im| ≤ Ma * Mb := by
  exact ⟨ le_trans ( Complex.abs_re_le_norm _ ) ( by simpa using mul_le_mul ha hb ( by positivity ) ( by positivity ) ), le_trans ( Complex.abs_im_le_norm _ ) ( by simpa using mul_le_mul ha hb ( by positivity ) ( by positivity ) ) ⟩

/- NOTE: The original `inv_fft_prec` lemma (precision condition for inverse FFT) was
   DISPROVED - it fails for n=l=1. The precision condition `(ε_cmul + 2*M_prod + 1)*3^n ≤ 2^(P-1)`
   is too strong for the inverse FFT. Instead, we use `fft_error_bound_npc` from FFTErrorNPC.lean
   which provides an FFT error bound WITHOUT requiring a precision condition, using the bound
   `(ε₀ + 2*M + 1) * (3 + 1/2^P)^k` instead of `(ε₀ + 2*M + 1) * 3^k`. -/

/-! ## Section 7: Pipeline error bound helpers -/

/-
Pointwise cmul error: C_hat[i] approximates the exact product.
-/
lemma cmul_pointwise_error (n l P : ℕ) (hn : n ≥ 1) (hl : l ≥ 1) (hP : P = knuth_bound n l)
    (A_digits B_digits : Fin (2^n) → ℤ)
    (hA_bound : ∀ j, |A_digits j| < 2^l)
    (hB_bound : ∀ j, |B_digits j| < 2^l)
    (A_hat B_hat : Vector (FPComplex P) (2^n))
    (hA_err : ∀ i : Fin (2^n),
      |(↑(A_hat.get i).re : ℝ) - (gen_dft (2^n) (fun j => (↑(A_digits j) : ℂ)) false i).re * 2^P| ≤ (2*(2:ℝ)^l+1)*3^n ∧
      |(↑(A_hat.get i).im : ℝ) - (gen_dft (2^n) (fun j => (↑(A_digits j) : ℂ)) false i).im * 2^P| ≤ (2*(2:ℝ)^l+1)*3^n)
    (hB_err : ∀ i : Fin (2^n),
      |(↑(B_hat.get i).re : ℝ) - (gen_dft (2^n) (fun j => (↑(B_digits j) : ℂ)) false i).re * 2^P| ≤ (2*(2:ℝ)^l+1)*3^n ∧
      |(↑(B_hat.get i).im : ℝ) - (gen_dft (2^n) (fun j => (↑(B_digits j) : ℂ)) false i).im * 2^P| ≤ (2*(2:ℝ)^l+1)*3^n) :
    let ε_fwd := (2*(2:ℝ)^l+1)*3^n
    let M_dft := (2^n : ℝ)*2^l
    let ε_cmul := 2*(M_dft*ε_fwd + ε_fwd*M_dft) + 2*ε_fwd*ε_fwd/2^P + 1/2
    let C_hat_exact := fun i : Fin (2^n) =>
      gen_dft (2^n) (fun j => (↑(A_digits j) : ℂ)) false i *
      gen_dft (2^n) (fun j => (↑(B_digits j) : ℂ)) false i
    ∀ i : Fin (2^n),
      |(↑(FPComplex.cmul (A_hat.get i) (B_hat.get i)).re : ℝ) - (C_hat_exact i).re * 2^P| ≤ ε_cmul ∧
      |(↑(FPComplex.cmul (A_hat.get i) (B_hat.get i)).im : ℝ) - (C_hat_exact i).im * 2^P| ≤ ε_cmul := by
  intros ε_fwd M_dft ε_cmul C_hat_exact i
  have hA : |(A_hat.get i).re - (gen_dft (2^n) (fun j => (A_digits j : ℂ)) false i).re * 2^P| ≤ ε_fwd ∧ |(A_hat.get i).im - (gen_dft (2^n) (fun j => (A_digits j : ℂ)) false i).im * 2^P| ≤ ε_fwd := by
    exact hA_err i
  have hB : |(B_hat.get i).re - (gen_dft (2^n) (fun j => (B_digits j : ℂ)) false i).re * 2^P| ≤ ε_fwd ∧ |(B_hat.get i).im - (gen_dft (2^n) (fun j => (B_digits j : ℂ)) false i).im * 2^P| ≤ ε_fwd := by
    exact hB_err i;
  have := cmul_error_bound P ( by
    exact hP.symm ▸ by unfold knuth_bound; linarith; ) ( A_hat.get i ) ( B_hat.get i ) ( gen_dft ( 2^n ) ( fun j => ( A_digits j : ℂ ) ) false i ) ( gen_dft ( 2^n ) ( fun j => ( B_digits j : ℂ ) ) false i ) ε_fwd ε_fwd ( 2^n * 2^l ) ( 2^n * 2^l ) ( by positivity ) ( by positivity ) ( by positivity ) ( by positivity ) hA.1 hA.2 hB.1 hB.2 ( by
    convert gen_dft_real_component_bound ( 2 ^ n ) ( by linarith [ Nat.pow_le_pow_right two_pos hn ] ) ( fun j => ( A_digits j : ℂ ) ) ( 2 ^ l ) ( by positivity ) ( fun j => ?_ ) ( fun j => ?_ ) false i |>.1 using 1 <;> norm_num [ abs_mul, abs_of_nonneg ];
    exact_mod_cast le_of_lt ( hA_bound j ) ) ( by
    convert gen_dft_real_component_bound ( 2 ^ n ) ( by linarith [ Nat.pow_le_pow_right two_pos hn ] ) ( fun j => ( A_digits j : ℂ ) ) ( 2 ^ l ) ( by positivity ) ( fun j => ?_ ) ( fun j => ?_ ) false i |>.2 using 1 <;> norm_num [ abs_mul, abs_of_nonneg ];
    exact_mod_cast le_of_lt ( hA_bound j ) ) ( by
    convert gen_dft_real_component_bound ( 2 ^ n ) ( by linarith [ Nat.pow_le_pow_right two_pos hn ] ) ( fun j => ( B_digits j : ℂ ) ) ( 2 ^ l ) ( by positivity ) ( fun j => ?_ ) ( fun j => ?_ ) false i |> And.left using 1 <;> norm_num;
    exact_mod_cast le_of_lt ( hB_bound j ) ) ( by
    convert gen_dft_real_component_bound ( 2 ^ n ) ( by linarith [ Nat.pow_le_pow_right two_pos hn ] ) ( fun j => ( B_digits j : ℂ ) ) ( 2 ^ l ) ( by positivity ) ( fun j => ?_ ) ( fun j => ?_ ) false i |>.2 using 1 <;> norm_num [ abs_le ];
    exact ⟨ neg_le_of_abs_le <| mod_cast le_of_lt <| hB_bound j, le_of_abs_le <| mod_cast le_of_lt <| hB_bound j ⟩ );
  convert this using 2

/-
Magnitude bound on exact products via norm.
-/
lemma exact_product_mag_bound (n l : ℕ) (hn : n ≥ 1) (hl : l ≥ 1)
    (A_digits B_digits : Fin (2^n) → ℤ)
    (hA_bound : ∀ j, |A_digits j| < 2^l)
    (hB_bound : ∀ j, |B_digits j| < 2^l) :
    let M_dft := (2^n : ℝ)*2^l
    let C_hat_exact := fun i : Fin (2^n) =>
      gen_dft (2^n) (fun j => (↑(A_digits j) : ℂ)) false i *
      gen_dft (2^n) (fun j => (↑(B_digits j) : ℂ)) false i
    ∀ i : Fin (2^n),
      |(C_hat_exact i).re| ≤ M_dft * M_dft ∧ |(C_hat_exact i).im| ≤ M_dft * M_dft := by
  intros M_dft C_hat_exact i;
  convert product_component_bound_via_norm _ _ _ _ _ _ _ _ using 1;
  · positivity;
  · positivity;
  · convert gen_dft_norm_bound_real ( 2 ^ n ) ( Nat.one_le_pow _ _ zero_lt_two ) ( fun j => ( A_digits j : ℂ ) ) ( 2 ^ l ) ( by positivity ) _ _ _ _ using 1 <;> norm_num;
    · rfl;
    · exact fun j => mod_cast le_of_lt ( hA_bound j );
  · convert gen_dft_norm_bound_real ( 2 ^ n ) ( by linarith [ Nat.one_le_pow n 2 zero_lt_two ] ) ( fun j => ( B_digits j : ℂ ) ) ( 2 ^ l ) ( by positivity ) _ _ _ _ using 1 <;> norm_num;
    · rfl;
    · exact fun j => mod_cast le_of_lt ( hB_bound j )

/-
The full pipeline ℝ-valued error bound.
-/
lemma fft_pipeline_real_error
    (n l P : ℕ) (hn : n ≥ 1) (hn5 : n ≥ 5) (hl : l ≥ 1) (hl7 : l ≥ 7) (hP : P = knuth_bound n l)
    (A_digits B_digits : Fin (2^n) → ℤ)
    (hA_bound : ∀ j, |A_digits j| < 2^l)
    (hB_bound : ∀ j, |B_digits j| < 2^l)
    (A B : Vector (FPComplex P) (2^n))
    (hA : A = Vector.ofFn fun i => FPComplex.ofInt (A_digits i))
    (hB : B = Vector.ofFn fun i => FPComplex.ofInt (B_digits i))
    (A_hat : Vector (FPComplex P) (2^n))
    (hA_hat : A_hat = FPComplex.fft (k := n) A false)
    (B_hat : Vector (FPComplex P) (2^n))
    (hB_hat : B_hat = FPComplex.fft (k := n) B false)
    (C_hat : Vector (FPComplex P) (2^n))
    (hC_hat : C_hat = Vector.ofFn fun i : Fin (2^n) =>
      FPComplex.cmul (A_hat.get i) (B_hat.get i))
    (C : Vector (FPComplex P) (2^n))
    (hC : C = FPComplex.fft (k := n) C_hat true) :
    let conv_m := fun m : Fin (2^n) =>
      ∑ j : Fin (2^n), ∑ k : Fin (2^n),
        if (j.val + k.val) % (2^n) = m.val then A_digits j * B_digits k else 0
    ∀ m : Fin (2^n),
      |(↑(C.get m).re : ℝ) - (2^n : ℝ) * ↑(conv_m m) * 2^P| <
        (2^n : ℝ) * 2^(P - 1 : ℕ) := by
  intro conv_m m
  set ε_fwd := (2 * (2 : ℝ)^l + 1) * 3^n
  set M_dft := (2^n : ℝ) * 2^l
  set ε_cmul := 2 * (M_dft * ε_fwd + ε_fwd * M_dft) + 2 * ε_fwd * ε_fwd / 2^P + 1/2
  set M_prod := M_dft * M_dft
  set C_hat_exact := fun i : Fin (2^n) =>
    gen_dft (2^n) (fun j => (↑(A_digits j) : ℂ)) false i *
    gen_dft (2^n) (fun j => (↑(B_digits j) : ℂ)) false i
  set ε_inv := (ε_cmul + 2 * M_prod + 1) * (3 + 1/(2:ℝ)^P)^n
  have h_conv : gen_dft (2^n) C_hat_exact true m = (2^n : ℂ) * ↑(conv_m m) := by
    convert gen_dft_pipeline_eq_conv ( 2 ^ n ) ( by linarith [ Nat.pow_le_pow_right two_pos hn ] ) A_digits B_digits m using 1;
    norm_cast;
  have h_error : |(↑(C.get m).re : ℝ) - (gen_dft (2^n) C_hat_exact true m).re * 2^P| ≤ ε_inv := by
    have := fft_error_bound_npc n P (by
    exact hP.symm ▸ by exact le_add_of_le_of_nonneg ( by linarith ) ( by positivity ) ;) C_hat true C_hat_exact ε_cmul M_prod (by
    positivity) (by
    positivity) (by
    convert cmul_pointwise_error n l P hn hl hP A_digits B_digits hA_bound hB_bound A_hat B_hat _ _ using 1
    all_goals generalize_proofs at *;
    · simp +decide [ hC_hat ];
      simp +zetaDelta at *;
    · convert fwd_fft_digit_error n l P hn hl hP A_digits hA_bound A _ using 1;
      · rw [ hA_hat ];
      · exact hA;
    · convert fwd_fft_digit_error n l P hn hl hP B_digits hB_bound B _ using 1
      generalize_proofs at *;
      · rw [ hB_hat ];
      · exact hB) (by
    -- Apply the lemma exact_product_mag_bound to conclude the proof.
    apply exact_product_mag_bound n l hn hl A_digits B_digits hA_bound hB_bound) m
    generalize_proofs at *;
    simpa only [ hC ] using this.1;
  have h_pipeline : ε_inv < (2^n : ℝ) * 2^(P - 1) := by
    convert pipeline_numerical_bound_npc n l hn5 hl7 using 1;
    · grind;
    · rw [ hP ];
  convert lt_of_le_of_lt h_error h_pipeline using 1 ; norm_num [ h_conv ];
  norm_cast

/-! ## Section 8: Pipeline error bound (ℤ version) -/

/-
The core error bound: the FFT pipeline output is within K * 2^(P-1) of K * conv * 2^P.
-/
lemma fft_pipeline_error_bound
    (n l : ℕ) (P : ℕ) (hn : n ≥ 1) (hn5 : n ≥ 5) (hl : l ≥ 1) (hl7 : l ≥ 7) (hP : P = knuth_bound n l)
    (A_digits B_digits : Fin (2^n) → ℤ)
    (hA_bound : ∀ j, |A_digits j| < 2^l)
    (hB_bound : ∀ j, |B_digits j| < 2^l)
    (A : Vector (FPComplex P) (2^n))
    (hA : A = Vector.ofFn fun i => FPComplex.ofInt (A_digits i))
    (B : Vector (FPComplex P) (2^n))
    (hB : B = Vector.ofFn fun i => FPComplex.ofInt (B_digits i))
    (A_hat : Vector (FPComplex P) (2^n))
    (hA_hat : A_hat = FPComplex.fft (k := n) A false)
    (B_hat : Vector (FPComplex P) (2^n))
    (hB_hat : B_hat = FPComplex.fft (k := n) B false)
    (C_hat : Vector (FPComplex P) (2^n))
    (hC_hat : C_hat = Vector.ofFn fun i : Fin (2^n) =>
      FPComplex.cmul (A_hat.get i) (B_hat.get i))
    (C : Vector (FPComplex P) (2^n))
    (hC : C = FPComplex.fft (k := n) C_hat true) :
    ∀ m : Fin (2^n),
      |(C.get m).re - (2^n : ℤ) *
        (∑ j : Fin (2^n), ∑ k : Fin (2^n),
          if (j.val + k.val) % (2^n) = m.val then A_digits j * B_digits k else 0) *
        (2 : ℤ)^P| < (2^n : ℤ) * 2^(P - 1 : ℕ) := by
  have := @fft_pipeline_real_error;
  convert this n l P hn hn5 hl hl7 hP A_digits B_digits hA_bound hB_bound A B hA hB A_hat hA_hat B_hat hB_hat C_hat hC_hat C hC using 1;
  norm_cast

end

end FFTConv


/- ========================================================================
   Section: SSATermination
   ======================================================================== -/

section SSATermination

/-!
# Termination proof for SSA multiplication

This file proves that the FFT output components are strictly smaller
than the inputs, which ensures termination of the SSA algorithm.

## Strategy

1. Prove tight shr_round bound: |shr_round v P| ≤ |v| / 2^P + 1
2. Prove cmul with twiddle factor gives ≤ 3B + 1
3. Prove FFT component bound by induction: output ≤ 4^k * (M+1) - 1
4. Instantiate to show FFT outputs < 2^(6n+3l+5) < a.natAbs
-/

namespace FPComplex

variable {P : ℕ}

/-! ## Tight shr_round bound -/

/-
Tight bound on shr_round: divides by 2^P (not 2^(P-1) as in the looser bound).
-/
lemma shr_round_natAbs_tight (v : ℤ) (P : ℕ) (hP : P ≥ 1) :
    (shr_round v P).natAbs ≤ v.natAbs / 2^P + 1 := by
  unfold shr_round;
  rcases P with ( _ | P ) <;> simp_all +decide [ Int.shiftRight_eq_div_pow ];
  rw [ ← Int.ofNat_le ] ; norm_num;
  rw [ abs_le ];
  constructor <;> cases abs_cases v <;> nlinarith [ pow_pos ( zero_lt_two' ℤ ) P, pow_succ' ( 2 : ℤ ) P, Int.mul_ediv_add_emod ( v + 2 ^ P ) ( 2 ^ ( P + 1 ) ), Int.emod_nonneg ( v + 2 ^ P ) ( by positivity : ( 2 ^ ( P + 1 ) : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( v + 2 ^ P ) ( by positivity : ( 2 ^ ( P + 1 ) : ℤ ) > 0 ), Int.mul_ediv_add_emod ( |v| ) ( 2 ^ ( P + 1 ) ), Int.emod_nonneg ( |v| ) ( by positivity : ( 2 ^ ( P + 1 ) : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( |v| ) ( by positivity : ( 2 ^ ( P + 1 ) : ℤ ) > 0 ) ]

/-! ## Tight cmul bound for twiddle multiplication -/

/-
When multiplying by a twiddle factor (components ≤ 2^P + 1),
    the result has components ≤ 3B + 1 where B is the input component bound.
-/
lemma cmul_twiddle_bound (tw x : FPComplex P) (B : ℕ) (hP : P ≥ 1)
    (htw_re : tw.re.natAbs ≤ 2^P + 1) (htw_im : tw.im.natAbs ≤ 2^P + 1)
    (hx_re : x.re.natAbs ≤ B) (hx_im : x.im.natAbs ≤ B) :
    (cmul tw x).re.natAbs ≤ 3 * B + 1 ∧ (cmul tw x).im.natAbs ≤ 3 * B + 1 := by
  constructor <;> refine' le_trans ( shr_round_natAbs_tight _ _ hP ) _;
  · refine' Nat.succ_le_succ ( Nat.div_le_div_right _ ) |> le_trans <| _;
    exact 2 * ( 2 ^ P + 1 ) * B;
    · exact le_trans ( Int.natAbs_sub_le _ _ ) ( by nlinarith [ abs_mul ( tw.re ) ( x.re ), abs_mul ( tw.im ) ( x.im ), abs_nonneg ( tw.re ), abs_nonneg ( tw.im ), abs_nonneg ( x.re ), abs_nonneg ( x.im ) ] );
    · exact Nat.succ_le_succ ( Nat.div_le_of_le_mul <| by nlinarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hP ] );
  · refine' Nat.succ_le_succ ( Nat.div_le_of_le_mul _ );
    rw [ ← Int.ofNat_le ] at * ; norm_num at *;
    exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp htw_re, abs_le.mp htw_im, abs_le.mp hx_re, abs_le.mp hx_im, pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hP ], by nlinarith [ abs_le.mp htw_re, abs_le.mp htw_im, abs_le.mp hx_re, abs_le.mp hx_im, pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hP ] ⟩

/-! ## Twiddle table bound -/

/-
Each entry of the twiddle table has components bounded by 2^P + 1.
-/
lemma t_table_bound (K_pred : ℕ) (inv : Bool) (P : ℕ) (j : Fin K_pred) :
    ((t_table K_pred inv P).get j).re.natAbs ≤ 2^P + 1 ∧
    ((t_table K_pred inv P).get j).im.natAbs ≤ 2^P + 1 := by
  -- By definition of `t_table`, we know that each entry is a `twiddle` function.
  simp [t_table];
  exact ⟨ by simpa [ ← Int.ofNat_le ] using twiddle_re_bound j ( 2 * K_pred ) inv P, by simpa [ ← Int.ofNat_le ] using twiddle_im_bound j ( 2 * K_pred ) inv P ⟩

/-! ## FFT component bound -/

/-
The main FFT component bound: after k butterfly stages starting from
    inputs with components ≤ M, each output component has natAbs ≤ 4^k * (M+1) - 1.

    This captures the growth through the butterfly network:
    - Base case (k=0): output = input, bound = M ≤ 4^0 * (M+1) - 1 = M. ✓
    - Inductive step: butterfly gives ≤ 4*B + 1 where B = 4^k*(M+1)-1.
      4*B + 1 = 4^(k+1)*(M+1) - 3 ≤ 4^(k+1)*(M+1) - 1. ✓
-/
lemma fft_component_bound (k : ℕ) (P : ℕ) (hP : P ≥ 1)
    (x : Vector (FPComplex P) (2^k)) (inv : Bool) (M : ℕ)
    (hM : ∀ i : Fin (2^k), (x.get i).re.natAbs ≤ M ∧ (x.get i).im.natAbs ≤ M) :
    ∀ i : Fin (2^k), ((fft x inv).get i).re.natAbs ≤ 4^k * (M + 1) - 1 ∧
                      ((fft x inv).get i).im.natAbs ≤ 4^k * (M + 1) - 1 := by
  -- Apply the induction hypothesis to the recursive calls.
  have h_ind : ∀ (k : ℕ) (x : Vector (FPComplex P) (2^k)) (inv : Bool) (M : ℕ) (hM : ∀ i : Fin (2^k), (x.get i).re.natAbs ≤ M ∧ (x.get i).im.natAbs ≤ M), ∀ i : Fin (2^k), ((FPComplex.fft x inv).get i).re.natAbs ≤ 4^k * (M + 1) - 1 ∧ ((FPComplex.fft x inv).get i).im.natAbs ≤ 4^k * (M + 1) - 1 := by
    intro k
    induction' k with k ih;
    · simp +zetaDelta at *;
      intro x; exact ⟨ fun M hM₁ hM₂ => ⟨ hM₁, hM₂ ⟩, fun M hM₁ hM₂ => ⟨ hM₁, hM₂ ⟩ ⟩ ;
    · intro x inv M hM i;
      by_cases hi : i.val < 2^k;
      · have h_bound : ((FPComplex.fft x inv).get i).re.natAbs ≤ (4^k * (M + 1) - 1) + (3 * (4^k * (M + 1) - 1) + 1) ∧ ((FPComplex.fft x inv).get i).im.natAbs ≤ (4^k * (M + 1) - 1) + (3 * (4^k * (M + 1) - 1) + 1) := by
          rw [ fft_first_half ];
          refine' ⟨ _, _ ⟩;
          refine' le_trans ( cadd_natAbs_re_le _ _ ) ( add_le_add _ _ );
          any_goals assumption;
          · refine' ih _ _ _ _ _ |>.1;
            simp +decide [ Vector.get ];
            exact fun j => hM ⟨ 2 * j, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
          · refine' le_trans ( cmul_twiddle_bound _ _ _ hP _ _ _ _ |>.1 ) _;
            exact 4 ^ k * ( M + 1 ) - 1;
            · exact t_table_bound _ _ _ _ |>.1;
            · exact t_table_bound _ _ _ _ |>.2;
            · refine' ih _ _ _ _ _ |>.1;
              simp +decide [ Vector.get ];
              exact fun j => hM ⟨ 2 * j + 1, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
            · convert ih _ _ _ _ ⟨ i, hi ⟩ |>.2 using 1;
              simp +decide [ Vector.get ];
              exact fun j => hM ⟨ 2 * j + 1, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
            · norm_num;
          · refine' le_trans ( cadd_natAbs_im_le _ _ ) _;
            refine' add_le_add _ _;
            · convert ih _ _ _ _ _ |>.2 using 1;
              simp +decide [ Vector.get ];
              exact fun j => hM ⟨ 2 * j, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
            · refine' cmul_twiddle_bound _ _ _ hP _ _ _ _ |>.2;
              · exact t_table_bound _ _ _ _ |>.1;
              · exact t_table_bound _ _ _ _ |>.2;
              · refine' ih _ _ _ _ _ |>.1;
                simp +decide [ Vector.get ];
                exact fun j => hM ⟨ 2 * j + 1, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
              · convert ih _ _ _ _ _ |>.2 using 1;
                simp +decide [ Vector.get ];
                exact fun j => hM ⟨ 2 * j + 1, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
        exact ⟨ le_trans h_bound.1 ( Nat.le_sub_one_of_lt ( by zify ; norm_num [ pow_succ' ] ; nlinarith [ pow_pos ( show 0 < 4 by decide ) k, Nat.sub_add_cancel ( show 1 ≤ 4 ^ k * ( M + 1 ) from Nat.mul_pos ( pow_pos ( show 0 < 4 by decide ) k ) ( Nat.succ_pos _ ) ) ] ) ), le_trans h_bound.2 ( Nat.le_sub_one_of_lt ( by zify ; norm_num [ pow_succ' ] ; nlinarith [ pow_pos ( show 0 < 4 by decide ) k, Nat.sub_add_cancel ( show 1 ≤ 4 ^ k * ( M + 1 ) from Nat.mul_pos ( pow_pos ( show 0 < 4 by decide ) k ) ( Nat.succ_pos _ ) ) ] ) ) ⟩;
      · rw [ fft_second_half ];
        swap;
        lia;
        refine' ⟨ _, _ ⟩;
        · refine' le_trans ( csub_natAbs_re_le _ _ ) _;
          refine' le_trans ( add_le_add ( ih _ _ _ _ _ |>.1 ) ( cmul_twiddle_bound _ _ _ hP _ _ _ _ |>.1 ) ) _;
          exact M;
          rotate_left;
          exact 4 ^ k * ( M + 1 ) - 1;
          exact t_table_bound _ _ _ _ |>.1;
          · exact t_table_bound _ _ _ _ |>.2;
          · refine' ih _ _ _ _ _ |>.1;
            simp +decide [ Vector.get ];
            exact fun j => hM ⟨ 2 * j + 1, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
          · convert ih _ _ _ _ _ |>.2 using 1;
            simp +decide [ Vector.get ];
            exact fun j => hM ⟨ 2 * j + 1, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
          · rw [ pow_succ' ] ; zify ; norm_num ; ring_nf ; norm_num;
          · simp +decide [ Vector.get ];
            exact fun j => hM ⟨ 2 * j, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
        · refine' le_trans ( csub_natAbs_im_le _ _ ) _;
          refine' le_trans ( add_le_add ( ih _ _ _ _ _ |>.2 ) ( cmul_twiddle_bound _ _ _ hP _ _ _ _ |>.2 ) ) _;
          exact M;
          rotate_left;
          exact 4 ^ k * ( M + 1 ) - 1;
          exact t_table_bound _ _ _ _ |>.1;
          · exact t_table_bound _ _ _ _ |>.2;
          · refine' ih _ _ _ _ _ |>.1;
            simp +decide [ Vector.get ];
            exact fun j => hM ⟨ 2 * j + 1, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
          · convert ih _ _ _ _ _ |>.2 using 1;
            simp +decide [ Vector.get ];
            exact fun j => hM ⟨ 2 * j + 1, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
          · rw [ pow_succ' ] ; zify ; norm_num ; ring_nf ; norm_num;
          · simp +decide [ Vector.get ];
            exact fun j => hM ⟨ 2 * j, by linarith [ Fin.is_lt j, pow_succ' 2 k ] ⟩;
  exact h_ind k x inv M hM

end FPComplex

/-! ## Auxiliary arithmetic lemmas -/

/-
The FFT output of digit decomposition has bounded components.
-/
lemma fft_digit_output_bound (n l P : ℕ) (hn : n ≥ 1) (hl : l ≥ 1) (hP : P = knuth_bound n l)
    (x : ℕ) (N : ℕ) (hx : x < 2^N) (hlK : l * 2^n ≥ 2 * N)
    (inv : Bool) :
    let K := 2^n
    let A : Vector (FPComplex P) K :=
      Vector.ofFn fun i : Fin K => FPComplex.ofInt (decompose_digit x l K i.val)
    ∀ i : Fin K, ((FPComplex.fft (k := n) A inv).get i).re.natAbs < 2^(6*n + 3*l + 5) ∧
                  ((FPComplex.fft (k := n) A inv).get i).im.natAbs < 2^(6*n + 3*l + 5) := by
  intro K A;
  -- By definition of $A$, we know that each component is bounded by $(2^l - 1) * 2^P$.
  have hA_bound : ∀ i : Fin K, (A.get i).re.natAbs ≤ (2^l - 1) * 2^P ∧ (A.get i).im.natAbs ≤ (2^l - 1) * 2^P := by
    intro i
    have h_decomp_bound : decompose_digit x l K i.val < 2^l := by
      apply decompose_digit_bound_all x l K N hl (by
      exact le_trans ( by decide ) ( Nat.pow_le_pow_right ( by decide ) hn )) hx (by
      nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow n 2 zero_lt_two ), Nat.pow_le_pow_right two_pos hn ]) i.val (by
      exact i.2);
    simp +zetaDelta at *;
    unfold FPComplex.ofInt; norm_num [ Int.natAbs_mul ] ;
    exact Nat.le_sub_one_of_lt ( by linarith [ abs_of_nonneg ( show 0 ≤ decompose_digit x l ( 2 ^ n ) i from decompose_digit_nonneg x l ( 2 ^ n ) i ) ] );
  have := @FPComplex.fft_component_bound n P ?_ A inv ( ( 2 ^ l - 1 ) * 2 ^ P ) hA_bound;
  · refine fun i => ⟨ lt_of_le_of_lt ( this i |>.1 ) ?_, lt_of_le_of_lt ( this i |>.2 ) ?_ ⟩ <;> norm_num [ hP, knuth_bound ] <;> ring_nf;
    · rw [ show ( 4 : ℕ ) ^ n = 2 ^ ( n * 2 ) by norm_num [ pow_mul' ] ] ; ring_nf;
      zify ; norm_num ; ring_nf ; (
      nlinarith [ pow_pos ( by decide : 0 < 2 ) ( l * 2 ), pow_pos ( by decide : 0 < 2 ) ( n * 6 ), pow_pos ( by decide : 0 < 2 ) ( l * 3 ), pow_pos ( by decide : 0 < 2 ) ( n * 2 ), pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( by linarith : l * 2 ≤ l * 3 ), pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( by linarith : n * 2 ≤ n * 6 ) ]);
    · rw [ show ( 4 : ℕ ) ^ n = 2 ^ ( n * 2 ) by norm_num [ pow_mul' ] ] ; ring_nf;
      zify ; norm_num ; ring_nf ; (
      nlinarith [ pow_pos ( by decide : 0 < 2 ) ( l * 2 ), pow_pos ( by decide : 0 < 2 ) ( n * 6 ), pow_pos ( by decide : 0 < 2 ) ( l * 3 ), pow_pos ( by decide : 0 < 2 ) ( n * 2 ), pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( by linarith : l * 2 ≤ l * 3 ), pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( by linarith : n * 2 ≤ n * 6 ) ]);
  · exact hP.symm ▸ Nat.succ_le_of_lt ( by unfold knuth_bound; positivity )

end SSATermination


/- ========================================================================
   Section: SSAMain
   ======================================================================== -/

section SSAMain

/-! ## The SSA multiplication algorithm -/

noncomputable def ssa : ℤ → ℤ → ℤ
  | a, b =>
    let N := max (bits a) (bits b)
    if hN : N > base_threshold then
      let sgn : ℤ := a.sign * b.sign
      let x := a.natAbs
      let y := b.natAbs

      let l := Nat.clog 2 N
      let n := Nat.clog 2 ((2 * N + l - 1) / l)

      let K := 2 ^ n
      let P := knuth_bound n l
      let A : Vector (FPComplex P) K :=
        Vector.ofFn fun i : Fin K => FPComplex.ofInt (decompose_digit x l K i.val)
      let B : Vector (FPComplex P) K :=
        Vector.ofFn fun i : Fin K => FPComplex.ofInt (decompose_digit y l K i.val)

      -- All integer multiplications go through this function
      let mul_fn : ℤ → ℤ → ℤ := fun u v =>
        -- note from srihari:
        -- this guard is always vacuously true and never violated,
        -- but we need it anyway because the termination checker can't see inside FFT.
        -- so afaik it is not possible to make the checker understand that the
        -- twiddle muls inside FFT are always on operands of smaller size.
        if u.natAbs + v.natAbs < a.natAbs + b.natAbs then ssa u v else u * v

      let A_hat := FPComplex.FFT mul_fn (k := n) A false
      let B_hat := FPComplex.FFT mul_fn (k := n) B false
      let C_hat : Vector (FPComplex P) K := Vector.ofFn fun i : Fin K =>
        FPComplex.cmul_via mul_fn (A_hat.get i) (B_hat.get i)
      let C := FPComplex.FFT mul_fn (k := n) C_hat true
      let coeff : Fin K → ℤ := fun j =>
        FPComplex.round_re (⟨(C.get j).re / (↑K : ℤ),
          (C.get j).im / (↑K : ℤ)⟩ : FPComplex P)
      sgn * recompose l coeff
    else a * b
termination_by a b => a.natAbs + b.natAbs
decreasing_by all_goals assumption

/-! ## FFT convolution correctness -/

/-- Core numerical analysis lemma: the fixed-point FFT-based convolution procedure
    correctly computes the circular convolution of the input digit sequences,
    given sufficient precision P = 4n + 2l + 4.

    Proved by combining `fft_pipeline_error_bound` (from FFTConv.lean) with
    `rounding_pipeline_correct` (also from FFTConv.lean). -/
lemma fft_convolution_correct
    {P : ℕ} (n l : ℕ)
    (hn : n ≥ 1) (hn5 : n ≥ 5) (hl : l ≥ 1) (hl7 : l ≥ 7) (hP : P = knuth_bound n l)
    (A_digits B_digits : Fin (2^n) → ℤ)
    (hA_bound : ∀ j, |A_digits j| < 2^l)
    (hB_bound : ∀ j, |B_digits j| < 2^l)
    (A : Vector (FPComplex P) (2^n))
    (hA : A = Vector.ofFn fun i => FPComplex.ofInt (A_digits i))
    (B : Vector (FPComplex P) (2^n))
    (hB : B = Vector.ofFn fun i => FPComplex.ofInt (B_digits i))
    (A_hat : Vector (FPComplex P) (2^n))
    (hA_hat : A_hat = FPComplex.fft (k := n) A false)
    (B_hat : Vector (FPComplex P) (2^n))
    (hB_hat : B_hat = FPComplex.fft (k := n) B false)
    (C_hat : Vector (FPComplex P) (2^n))
    (hC_hat : C_hat = Vector.ofFn fun i : Fin (2^n) =>
      FPComplex.cmul (A_hat.get i) (B_hat.get i))
    (C : Vector (FPComplex P) (2^n))
    (hC : C = FPComplex.fft (k := n) C_hat true)
    (coeff : Fin (2^n) → ℤ)
    (hcoeff : coeff = fun j =>
      FPComplex.round_re (P := P) ⟨(C.get j).re / (2^n : ℤ), (C.get j).im / (2^n : ℤ)⟩) :
    ∀ m : Fin (2^n),
      coeff m = ∑ j : Fin (2^n), ∑ k : Fin (2^n),
        if (j.val + k.val) % (2^n) = m.val then A_digits j * B_digits k else 0 := by
  intro m
  have h_err := fft_pipeline_error_bound n l P hn hn5 hl hl7 hP
    A_digits B_digits hA_bound hB_bound A hA B hB A_hat hA_hat B_hat hB_hat C_hat hC_hat C hC m
  set conv_m := ∑ j : Fin (2^n), ∑ k : Fin (2^n),
    if (j.val + k.val) % (2^n) = m.val then A_digits j * B_digits k else 0 with hconv_m_def
  rw [hcoeff]; show FPComplex.round_re ⟨(C.get m).re / (2^n : ℤ), (C.get m).im / (2^n : ℤ)⟩ = conv_m
  have h_re : FPComplex.round_re (P := P) ⟨(C.get m).re / (2^n : ℤ), (C.get m).im / (2^n : ℤ)⟩ =
    FPComplex.round_re (P := P) ⟨(C.get m).re / (2^n : ℤ), 0⟩ := by
    simp [FPComplex.round_re]
  rw [h_re]
  have hP_ge : P ≥ 1 := by unfold knuth_bound at hP; omega
  exact rounding_pipeline_correct _ conv_m (2^n) P
    (show 2^n ≥ 2 from le_trans (by norm_num : 2 ≤ 2^1) (Nat.pow_le_pow_right (by omega) hn)) hP_ge h_err

/-! ## Helper lemmas for correctness -/

/--
The algebraic chain: given circular convolution equals coeff,
    the final result equals a * b.
-/
lemma ssa_algebraic_chain (a b : ℤ) (n l : ℕ) (K : ℕ) (hK : K = 2 ^ n)
    (hn : n ≥ 1) (hl : l ≥ 1) (hlK : l * K ≥ 2 * max (bits a) (bits b))
    (coeff : Fin K → ℤ)
    (hcoeff : ∀ m : Fin K,
      coeff m = ∑ j : Fin K, ∑ k : Fin K,
        if (j.val + k.val) % K = m.val then
          decompose_digit a.natAbs l K j.val * decompose_digit b.natAbs l K k.val else 0) :
    a.sign * b.sign * recompose l coeff = a * b := by
  convert congr_arg ( fun x : ℤ => a.sign * b.sign * x ) ( circular_eq_linear_convolution l ( fun j : Fin K => decompose_digit a.natAbs l K j.val ) ( fun j : Fin K => decompose_digit b.natAbs l K j.val ) _ _ ) using 1 <;> norm_num [ hcoeff ];
  · convert Or.inl ( circular_eq_linear_convolution l _ _ _ _ ) using 1;
    rw [ eq_comm ];
    convert Iff.rfl;
    · exact hcoeff _ ▸ rfl;
    · convert decompose_digit_support a.natAbs l K ( max ( bits a ) ( bits b ) ) _ _ _ _ _ using 1;
      · have h_abs : a.natAbs < 2 ^ (bits a) := by
          exact Nat.lt_pow_succ_log_self ( by decide ) _;
        exact h_abs.trans_le ( Nat.pow_le_pow_right ( by decide ) ( Nat.le_max_left _ _ ) );
      · linarith;
      · grind;
      · exact hK.symm ▸ Nat.le_self_pow ( by linarith ) _;
      · exact hK.symm ▸ dvd_pow_self _ ( by linarith );
    · convert decompose_digit_support b.natAbs l K ( max ( bits a ) ( bits b ) ) _ _ _ _ _ using 1;
      · unfold bits;
        exact Nat.lt_pow_of_log_lt ( by norm_num ) ( by omega );
      · grind;
      · linarith;
      · grind +qlia;
      · exact hK.symm ▸ dvd_pow_self _ ( by linarith );
  · convert congr_arg ( fun x : ℤ => a.sign * b.sign * x ) ( circular_eq_linear_convolution l ( fun j : Fin K => decompose_digit a.natAbs l K j.val ) ( fun j : Fin K => decompose_digit b.natAbs l K j.val ) _ _ ) using 1 <;> norm_num [ hcoeff ];
    · rw [ decompose_recompose, decompose_recompose ];
      · convert sign_mul_natAbs a b |> Eq.symm using 1;
      · grind;
      · exact hK.symm ▸ Nat.one_le_pow _ _ ( by decide );
      · grind;
      · exact hK.symm ▸ Nat.one_le_pow _ _ ( by decide );
    · convert decompose_digit_support a.natAbs l K ( max ( bits a ) ( bits b ) ) _ _ _ _ _ using 1;
      · have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) a.natAbs; simp_all +decide [ bits ] ;
        exact this.trans_le ( Nat.pow_le_pow_right ( by decide ) ( Nat.succ_le_succ ( Nat.le_max_left _ _ ) ) );
      · grind;
      · grind +extAll;
      · grind;
      · exact hK.symm ▸ dvd_pow_self _ ( by linarith );
    · apply decompose_digit_support;
      any_goals exact max ( bits a ) ( bits b );
      · have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) ( Int.natAbs b );
        exact this.trans_le ( pow_le_pow_right₀ ( by decide ) ( by unfold bits; omega ) );
      · linarith;
      · grind;
      · grind;
      · grind;
  · convert decompose_digit_support a.natAbs l K ( max ( bits a ) ( bits b ) ) _ hlK hl ( by rw [ hK ] ; exact Nat.le_self_pow ( by linarith ) _ ) ( by rw [ hK ] ; exact dvd_pow_self _ ( by linarith ) ) using 1;
    exact lt_of_lt_of_le ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.le_max_left _ _ ) );
  · convert decompose_digit_support b.natAbs l K ( max ( bits a ) ( bits b ) ) _ hlK hl ( by rw [ hK ] ; exact Nat.le_self_pow ( by linarith ) _ ) ( by rw [ hK ] ; exact dvd_pow_self _ ( by linarith ) ) using 1;
    unfold bits at *;
    exact Nat.lt_pow_of_log_lt ( by norm_num ) ( by omega )

/-! ## Pipeline correctness -/

/--
The standard FFT pipeline (forward FFT → pointwise cmul → inverse FFT → rounding)
    correctly computes `a * b`.

    This is the core of the SSA correctness proof, factored out for reuse.
-/
lemma pipeline_correct (a b : ℤ) (hN : max (bits a) (bits b) > base_threshold) :
    let N := max (bits a) (bits b)
    let sgn : ℤ := a.sign * b.sign
    let l := Nat.clog 2 N
    let n := Nat.clog 2 ((2 * N + l - 1) / l)
    let K := 2 ^ n
    let P := knuth_bound n l
    let A : Vector (FPComplex P) K :=
      Vector.ofFn fun i : Fin K => FPComplex.ofInt (decompose_digit a.natAbs l K i.val)
    let B : Vector (FPComplex P) K :=
      Vector.ofFn fun i : Fin K => FPComplex.ofInt (decompose_digit b.natAbs l K i.val)
    let A_hat := FPComplex.fft (k := n) A false
    let B_hat := FPComplex.fft (k := n) B false
    let C_hat : Vector (FPComplex P) K := Vector.ofFn fun i : Fin K =>
      FPComplex.cmul (A_hat.get i) (B_hat.get i)
    let C := FPComplex.fft (k := n) C_hat true
    let coeff : Fin K → ℤ := fun j =>
      FPComplex.round_re (⟨(C.get j).re / (↑K : ℤ),
        (C.get j).im / (↑K : ℤ)⟩ : FPComplex P)
    sgn * recompose l coeff = a * b := by
  intro N sgn l n K P A B A_hat B_hat C_hat C coeff
  have hN' : 64 < N := hN
  obtain ⟨hn, hl, hlK0, hlN⟩ := ssa_params N hN'
  -- restate with the local `let` names `l`, `n` so `omega` sees matching atoms
  have hlK : l * 2 ^ n ≥ 2 * N := hlK0
  have hn5 : n ≥ 5 := ssa_params_n5 N hN'
  have hl7 : l ≥ 7 := Nat.le_trans (by native_decide) (Nat.clog_mono_right 2 (by omega : (65:ℕ) ≤ N))
  -- hn : n ≥ 1, hl : l ≥ 1, hlK : l * 2 ^ n ≥ 2 * N, hlN : l ≤ N
  have ha_lt : a.natAbs < 2 ^ N := lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by decide) _)
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hb_lt : b.natAbs < 2 ^ N := lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by decide) _)
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  have hK2 : K ≥ 2 := by
    show 2 ^ n ≥ 2
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  -- l * (K - 1) ≥ N, needed for the digit bound
  have hlK1 : l * (K - 1) ≥ N := by
    show l * (2 ^ n - 1) ≥ N
    have : l * (2 ^ n - 1) = l * 2 ^ n - l := by rw [Nat.mul_sub, mul_one]
    rw [this]; omega
  have hAbound : ∀ j : Fin K, |decompose_digit a.natAbs l K j.val| < 2 ^ l := by
    intro j
    rw [abs_of_nonneg (decompose_digit_nonneg _ _ _ _)]
    exact_mod_cast decompose_digit_bound_all a.natAbs l K N hl hK2 ha_lt hlK1 j.val j.2
  have hBbound : ∀ j : Fin K, |decompose_digit b.natAbs l K j.val| < 2 ^ l := by
    intro j
    rw [abs_of_nonneg (decompose_digit_nonneg _ _ _ _)]
    exact_mod_cast decompose_digit_bound_all b.natAbs l K N hl hK2 hb_lt hlK1 j.val j.2
  apply ssa_algebraic_chain a b n l K rfl hn hl (by show l * 2 ^ n ≥ 2 * N; exact hlK) coeff
  refine fft_convolution_correct n l hn hn5 hl hl7 rfl
    (fun i => decompose_digit a.natAbs l K i.val)
    (fun i => decompose_digit b.natAbs l K i.val)
    hAbound hBbound A rfl B rfl A_hat rfl B_hat rfl C_hat rfl C rfl coeff ?_
  funext j
  show FPComplex.round_re (P := P) ⟨(C.get j).re / (↑K : ℤ), (C.get j).im / (↑K : ℤ)⟩
     = FPComplex.round_re (P := P) ⟨(C.get j).re / ((2 : ℤ) ^ n), (C.get j).im / ((2 : ℤ) ^ n)⟩
  rw [show (↑K : ℤ) = (2 : ℤ) ^ n from by rw [show K = 2 ^ n from rfl]; push_cast; ring]

/-! ## Main correctness theorem -/

/-- **Correctness of the SSA multiplication algorithm.**
    The algorithm correctly computes the product of two integers.
    All integer multiplications — including FFT butterfly products —
    are performed via recursive `ssa` calls. -/
theorem ssa_correct (a b : ℤ) : ssa a b = a * b := by
  suffices h : ∀ n : ℕ, ∀ a b : ℤ, a.natAbs + b.natAbs = n → ssa a b = a * b from
    h _ a b rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b hab
    rw [ssa.eq_1]
    split
    · -- Inductive step: N > base_threshold
      rename_i hN
      -- By IH, ssa = * on all smaller inputs
      have ih' : ∀ x y : ℤ, x.natAbs + y.natAbs < n → ssa x y = x * y :=
        fun x y h => ih (x.natAbs + y.natAbs) h x y rfl
      -- The guarded mul_fn equals plain multiplication on ALL inputs:
      -- - In the then-branch: ssa u v = u * v by IH
      -- - In the else-branch: u * v = u * v by definition
      have h_mul_fn : (fun u v : ℤ =>
          if u.natAbs + v.natAbs < a.natAbs + b.natAbs then ssa u v else u * v) =
          fun u v => u * v := by
        ext u v; split_ifs with h
        · exact ih' u v (hab ▸ h)
        · rfl
      -- Therefore FFT mul_fn = fft and cmul_via mul_fn = cmul
      simp only [h_mul_fn, FPComplex.FFT_mul_eq_fft, FPComplex.cmul_via_mul]
      -- Now the pipeline is the standard one; apply pipeline_correct
      exact pipeline_correct a b hN
    · -- Base case: N ≤ base_threshold, ssa returns a * b directly
      rfl


end SSAMain
