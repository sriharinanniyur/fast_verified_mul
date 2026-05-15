import Mathlib

set_option linter.style.whitespace false
set_option linter.style.emptyLine false

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option grind.warning false

def poly_eval_commring {R : Type*} [CommRing R] {K : ℕ} (p : Fin K → ℤ) (x : R) : R :=
  ∑ i : Fin K, (p i) * x ^ (i.1)

def field_poly_eval_field {F : Type*} [Field F] {K : ℕ} (p : Fin K → F) (x : F) : F :=
  ∑ i : Fin K, (p i) * x ^ (i.1)

def poly_eval_field {K : ℕ} {F : Type*} [Field F] (p : Fin K → ℤ) (x : F) : F :=
  ∑ i : Fin K, (p i) * x ^ (i.1)

def poly_product {M : ℕ} {N : ℕ} (p : Fin M → ℤ) (q : Fin N → ℤ) :
    Fin (M + N).pred → ℤ := -- .pred over ℕ is floored at 0, so safer than M + N - 1
  fun k => ∑ i : Fin M, ∑ j : Fin N,
    if i.val + j.val = k.val then p i * q j else 0

def pointwise_eval_commring
{R : Type*} [CommRing R] {K : ℕ} {NPTS : ℕ} (p : Fin K → ℤ) (pts : Fin NPTS ↪ R)
: Fin NPTS → R :=
  fun i => poly_eval_commring p (pts i)

def pointwise_eval_field
{F : Type*} [Field F] {K : ℕ} {NPTS : ℕ} (p : Fin K → ℤ) (pts : Fin NPTS ↪ F)
: Fin NPTS → F :=
  fun i => poly_eval_field p (pts i)

def pointwise_mul_ring
{M N NPTS : ℕ} {R : Type*} [CommRing R]
(p : Fin M → ℤ) (q : Fin N → ℤ)
(pts : Fin NPTS ↪ R)
: Fin NPTS → R :=
  let p_eval := pointwise_eval_commring p pts
  let q_eval := pointwise_eval_commring q pts
  fun i => (p_eval i) * (q_eval i)

def pointwise_mul_field
{M N NPTS : ℕ} {F : Type*} [Field F]
(p : Fin M → ℤ) (q : Fin N → ℤ)
(pts : Fin NPTS ↪ F)
: Fin NPTS → F :=
  let p_eval := pointwise_eval_field p pts
  let q_eval := pointwise_eval_field q pts
  fun i => (p_eval i) * (q_eval i)

-- Vandermonde interpolation
noncomputable def vandermonde_interpolate
{M N : ℕ} {F : Type*} [Field F]
(p : Fin M → ℤ) (q : Fin N → ℤ)
(pts : Fin (M + N).pred ↪ F)
: Fin (M + N).pred → F :=
  let V := Matrix.vandermonde (R := F) pts
  V⁻¹.mulVec (pointwise_mul_field p q pts)


-- BEGIN ARISTOTLE
/-
Helper: Vandermonde determinant is a unit for injective points
-/
lemma vandermonde_det_isUnit {n : ℕ} {F : Type*} [Field F]
  (pts : Fin n ↪ F) : IsUnit (Matrix.vandermonde (R := F) pts).det := by
  rw [ Matrix.det_vandermonde ];
  exact isUnit_iff_ne_zero.mpr ( Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr <| pts.injective.ne <| by aesop )
-- Helper: poly_eval_field equals poly_eval_commring (they're definitionally equal modulo universe)
lemma poly_eval_field_eq_commring {K : ℕ} {F : Type*} [Field F] (p : Fin K → ℤ) (x : F) :
    poly_eval_field p x = poly_eval_commring p x := by
  simp [poly_eval_field, poly_eval_commring]
-- Helper: pointwise_mul_field equals pointwise_mul_ring
lemma pointwise_mul_field_eq {M N NPTS : ℕ} {F : Type*} [Field F]
    (p : Fin M → ℤ) (q : Fin N → ℤ) (pts : Fin NPTS ↪ F) :
    pointwise_mul_field p q pts = fun k =>
      poly_eval_field p (pts k) * poly_eval_field q (pts k) := by
  simp [pointwise_mul_field, pointwise_eval_field]
/-
Core: evaluation of poly_product at a point = product of evaluations
This says: ∑ k, (poly_product p q) k * x^k = (∑ i, p i * x^i) * (∑ j, q j * x^j)
-/
lemma eval_poly_product_eq_mul_eval {M N : ℕ} {F : Type*} [Field F]
    (p : Fin M → ℤ) (q : Fin N → ℤ) (x : F) :
    (∑ k : Fin (M + N).pred, ((poly_product p q k : ℤ) : F) * x ^ k.val) =
    (∑ i : Fin M, (p i : F) * x ^ i.val) * (∑ j : Fin N, (q j : F) * x ^ j.val) := by
  simp +decide only [poly_product, Int.cast_sum, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  rotate_right;
  use fun i => ∑ j : Fin N, ( p i * q j : F ) * x ^ ( i.val + j.val );
  · exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  · intro i hi;
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro j hj
    by_cases h : i.val + j.val < (M + N).pred;
    · rw [ Finset.sum_eq_single ⟨ i + j, h ⟩ ] <;> aesop;
    · rcases M with ( _ | M ) <;> rcases N with ( _ | N ) <;> simp_all +decide;
      linarith [ Fin.is_lt i, Fin.is_lt j ]

-- END ARISTOTLE


-- We now define the machinery needed for FFT convolution.

-- clean mathematical definition of DFT

def Kth_roots_of_unity
{K : ℕ} [NeZero K]
{F : Type*} [Field F]
(ω : F)
: Fin K → F :=
  fun i => (ω ^ i.val)

def DFT_field
{K : ℕ} [NeZero K]
{F : Type*} [Field F]
(x : Fin K → F)
(ω : F)
: Fin K → F :=
  fun i => ∑ j : Fin K, x j * ω ^ (j.val * i.val)

def DFT_field_inv
{K : ℕ} [NeZero K]
{F : Type*} [Field F]
(x : Fin K → F)
(ω : F)
: Fin K → F :=
  fun i => (K : F)⁻¹ * (DFT_field x ω⁻¹ i)

-- perform the cyclic convolution of two signals over a field using DFTs
def cyclic_convolution_DFT
{K : ℕ} [NeZero K]
{F : Type*} [Field F]
(ω : F)
(A B : Fin K → F)
: Fin K → F :=
  let A_hat := DFT_field A ω
  let B_hat := DFT_field B ω
  let pointwise : Fin K → F := fun i => (A_hat i) * (B_hat i)
  DFT_field_inv pointwise ω

-- benchmark for what a cyclic convolution *should* compute
def cyclic_convolution_benchmark
{K : ℕ} [NeZero K]
{R : Type*} [CommRing R]
(A B : Fin K → R) : Fin K → R :=
  fun i => ∑ j : Fin K, (A j) * (B ⟨(i.val + K - j.val) % K, Nat.mod_lt _ (NeZero.pos K)⟩)


-- BEGIN ARISTOTLE
/-
Orthogonality of roots of unity:
∑ k : Fin K, ω^(k * m) = K if K ∣ m, else 0
-/
lemma roots_of_unity_orthogonality
    {K : ℕ} [NeZero K] {R : Type*} [Field R]
    {ω : R} (hω : IsPrimitiveRoot ω K) (hK : (K : R) ≠ 0)
    (m : ℕ) :
    ∑ k : Fin K, ω ^ (k.val * m) = if K ∣ m then (K : R) else 0 := by
  split_ifs with h
  · obtain ⟨d, rfl⟩ := h
    have : ∀ k : Fin K, ω ^ (k.val * (K * d)) = 1 := by
      intro k
      rw [show k.val * (K * d) = K * (k.val * d) from by ring]
      rw [pow_mul, hω.pow_eq_one, one_pow]
    simp [this]
  · have hne : ω ^ m ≠ 1 := fun h' => h ((hω.pow_eq_one_iff_dvd m).mp h')
    rw [show (∑ k : Fin K, ω ^ (k.val * m)) = ∑ k : Fin K, (ω ^ m) ^ k.val from by
      congr 1; ext k; rw [← pow_mul, mul_comm]]
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hne,
        ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]
/-
The core identity: expanding cyclic_convolution_signals at index i gives
the correct cyclic convolution formula.
-/
theorem cyclic_convolution_theorem
    {R : Type*} [Field R]
    {K : ℕ} [NeZero K] (hK : (K : R) ≠ 0)
    {ω : R} (hω : IsPrimitiveRoot ω K)
    (A B : Fin K → R) :
    cyclic_convolution_DFT ω A B = cyclic_convolution_benchmark A B := by
  -- By definition of DFT, we can rewrite the left-hand side of the equation.
  funext i
  simp [cyclic_convolution_DFT, cyclic_convolution_benchmark, DFT_field, DFT_field_inv];
  -- Let's simplify the expression using the fact that multiplication by a constant out of the sum can be taken outside.
  have h_simp : ∑ x : Fin K, (∑ j : Fin K, A j * ω ^ (j.val * x.val)) * (∑ l : Fin K, B l * ω ^ (l.val * x.val)) * (ω ^ (x.val * i.val))⁻¹ = ∑ j : Fin K, ∑ l : Fin K, A j * B l * ∑ x : Fin K, ω ^ (x.val * (j.val + l.val - i.val : ℤ)) := by
    simp +decide only [Finset.sum_mul _ _ _, Finset.mul_sum];
    refine' Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _ ) ) ; ring;
    by_cases h : ω = 0 <;> simp_all +decide [ zpow_add₀, zpow_sub₀ ] ; ring;
    · exact absurd ( hω.eq_orderOf ) ( by aesop );
    · norm_cast ; ring;
  -- Apply the orthogonality relation to simplify the inner sum.
  have h_inner : ∀ j l : Fin K, ∑ x : Fin K, ω ^ (x.val * (j.val + l.val - i.val : ℤ)) = if (j.val + l.val - i.val : ℤ) % K = 0 then (K : R) else 0 := by
    intro j l; split_ifs with h; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff', IsPrimitiveRoot.iff_def ] ;
    · obtain ⟨ k, hk ⟩ := h; simp +decide [ hk, zpow_mul' ] ;
      rw [ ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω.1, one_zpow ] ; simp +decide [ hK ];
    · -- Since $ω$ is a primitive $K$-th root of unity, we have $ω^{j.val + l.val - i.val} ≠ 1$.
      have h_ne_one : ω ^ (j.val + l.val - i.val : ℤ) ≠ 1 := by
        exact fun h' => h ( Int.emod_eq_zero_of_dvd <| hω.zpow_eq_one_iff_dvd _ |>.1 h' );
      have h_geom_sum : ∑ x ∈ Finset.range K, (ω ^ (j.val + l.val - i.val : ℤ)) ^ x = 0 := by
        rw [ geom_sum_eq ] <;> simp_all +decide [ IsPrimitiveRoot.iff_def ];
        exact Or.inl ( by rw [ ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω.1, one_zpow, sub_self ] );
      simp_all +decide [ Finset.sum_range, zpow_mul' ];
  simp_all +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ];
  refine' Finset.sum_congr rfl fun j hj => _;
  rw [ Finset.sum_eq_single ⟨ ( i + K - j ) % K, Nat.mod_lt _ ( NeZero.pos K ) ⟩ ] <;> simp +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
  · rw [ Nat.cast_sub ( by linarith [ Fin.is_lt j, Fin.is_lt i ] ) ] ; simp +decide [ add_assoc, Nat.mod_eq_of_lt ];
  · intro b hb h; contrapose! hb; simp_all +decide [ Fin.ext_iff, Nat.mod_eq_of_lt ] ;
    rw [ Nat.ModEq.symm ];
    exact Eq.symm ( Nat.mod_eq_of_lt b.2 );
    simp +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_sub ( show ( j : ℕ ) ≤ i + K from by linarith [ Fin.is_lt j, Fin.is_lt i ] ) ];
    linear_combination' h

-- END ARISTOTLE



-- the Fast Fourier Transform, and a proof of its equivalence to the plain DFT,
-- specified with Claude's help.
-- To extract even and odd indices, we use the fact that if our (even) transform length
-- is 2^(k), then there are (2^(k-1)) even indices and 2^(k-1) odd indices.
def FFT_field
{k : Nat}
{F : Type*} [Field F]
(x : Fin (2^k) → F)
(ω : F)
: Fin (2^k) → F :=
  match k with
  | 0     => x
  | k'+1  =>
    let evens : Fin (2^k') → F :=
      fun j => x ⟨2 * j.val, by grind⟩
    let odds : Fin (2^k') → F :=
      fun j => x ⟨2 * j.val + 1, by grind⟩
    let E := FFT_field evens (ω^2)
    let O := FFT_field odds  (ω^2)
    fun i =>
      let j : Fin (2^k') := ⟨i.val % 2^k', Nat.mod_lt _ (by positivity)⟩
      E j + (if i.val < 2^k' then 1 else -1) * ω^j.val * O j

-- BEGIN ARISTOTLE
/-
Helper lemma 1: ω^2 is a primitive 2^k'-th root when ω is a primitive 2^(k'+1)-th root
-/
lemma prim_root_sq {F : Type*} [Field F] {k' : ℕ} {ω : F}
    (hω : IsPrimitiveRoot ω (2^(k'+1))) :
    IsPrimitiveRoot (ω^2) (2^k') := by
  convert hω.pow_of_dvd _ _ using 1;
  · norm_num [ pow_succ' ];
  · norm_num;
  · exact dvd_pow_self _ ( Nat.succ_ne_zero _ )
/-
Helper lemma 2: ω^(2^k') = -1 when ω is a primitive 2^(k'+1)-th root
-/
lemma prim_root_half_neg_one {F : Type*} [Field F] {k' : ℕ} {ω : F}
    (hω : IsPrimitiveRoot ω (2^(k'+1))) :
    ω ^ (2^k') = -1 := by
  have h_sq : ω ^ (2 ^ k') ≠ 1 := by
    exact fun h => absurd ( hω.2 _ h ) ( Nat.not_dvd_of_pos_of_lt ( pow_pos ( by decide ) _ ) ( pow_lt_pow_right₀ ( by decide ) k'.lt_succ_self ) );
  exact mul_left_cancel₀ ( sub_ne_zero_of_ne h_sq ) ( by linear_combination' hω.pow_eq_one )
/-
Helper lemma 3: DFT even-odd decomposition.
For K = 2^(k'+1) with ω a primitive K-th root, and i < 2^k':
  DFT A ω i = (∑ m, A(2m) * (ω^2)^(m*i)) + ω^i * (∑ m, A(2m+1) * (ω^2)^(m*i))
-/
lemma DFT_split_even_odd {F : Type*} [Field F] {k' : ℕ}
    (A : Fin (2^(k'+1)) → F) (ω : F)
    (i : Fin (2^(k'+1))) :
    @DFT_field (2^(k'+1)) ⟨by positivity⟩ F _ A ω i =
    (∑ m : Fin (2^k'), A ⟨2 * m.val, by omega⟩ * (ω^2) ^ (m.val * i.val)) +
    ω ^ i.val * (∑ m : Fin (2^k'), A ⟨2 * m.val + 1, by omega⟩ * (ω^2) ^ (m.val * i.val)) := by
  simp +decide only [DFT_field, Finset.mul_sum _ _ _, pow_mul', mul_left_comm];
  have h_split : Finset.range (2 ^ (k' + 1)) = Finset.image (fun m => 2 * m) (Finset.range (2 ^ k')) ∪ Finset.image (fun m => 2 * m + 1) (Finset.range (2 ^ k')) := by
    ext m
    simp [Finset.mem_range, Finset.mem_image];
    exact ⟨ fun h => by rcases Nat.even_or_odd' m with ⟨ c, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ c, by rw [ pow_succ' ] at h; linarith, rfl ⟩, fun h => by rcases h with ( ⟨ c, hc, rfl ⟩ | ⟨ c, hc, rfl ⟩ ) <;> rw [ pow_succ' ] <;> linarith ⟩;
  rw [ Finset.sum_fin_eq_sum_range ];
  rw [ h_split, Finset.sum_union ];
  · simp +decide [ pow_succ', pow_mul', mul_assoc, mul_comm, mul_left_comm, Finset.sum_image ];
    simp +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm, Finset.sum_range, Nat.mul_comm ];
    grind;
  · norm_num [ Finset.disjoint_right ];
    intros; omega;
/-
Main theorem: FFT computes the DFT
-/
theorem FFT_eq_DFT
{F : Type*} [Field F]
{k : ℕ}
(ω : F) (hω : IsPrimitiveRoot ω (2^k))
(A : Fin (2^k) → F)
: FFT_field A ω = DFT_field A ω
:= by
  revert A;
  induction' k with k ih generalizing ω;
  · simp +decide [ funext_iff, Fin.forall_fin_succ, DFT_field, FFT_field ];
  · intro A
    funext i
    rw [DFT_split_even_odd];
    by_cases hi : i.val < 2 ^ k;
    · rw [ FFT_field ];
      simp +decide [ hi, Nat.mod_eq_of_lt hi, ih _ ( prim_root_sq hω ) ];
      rfl;
    · -- Since $i.val \geq 2^k$, we can write $i.val = 2^k + j$ for some $j$.
      obtain ⟨j, hj⟩ : ∃ j : Fin (2 ^ k), i.val = 2 ^ k + j.val := by
        exact ⟨ ⟨ i - 2 ^ k, by rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt i, pow_succ' 2 k ] ⟩, by simp +decide [ Nat.add_sub_of_le ( le_of_not_gt hi ) ] ⟩;
      -- By the properties of the FFT, we can split the sum into two parts: one for the even indices and one for the odd indices.
      have h_split : FFT_field A ω i = FFT_field (fun m => A ⟨2 * m.val, by
        rw [ pow_succ' ] ; linarith [ Fin.is_lt m ]⟩) (ω ^ 2) j - ω ^ j.val * FFT_field (fun m => A ⟨2 * m.val + 1, by
        rw [ pow_succ' ] ; linarith [ Fin.is_lt m ]⟩) (ω ^ 2) j := by
        rw [ show i = ⟨ 2 ^ k + j.val, by
              lia ⟩ from Fin.ext hj ]
        generalize_proofs at *;
        rw [ FFT_field ];
        simp +decide [ Nat.mod_eq_of_lt, hi ];
        ring
      generalize_proofs at *;
      rw [ h_split, ih, ih ];
      any_goals exact prim_root_sq hω;
      simp +decide [ hj, pow_add, pow_mul', mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
      simp +decide [ DFT_field, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
      have := prim_root_half_neg_one hω; simp_all +decide [ pow_succ, pow_mul ] ;
      simp +decide [ mul_pow, this ];
      ring
-- END ARISTOTLE




-- STRASSEN I
def bits (x : ℤ) : ℕ :=
  Nat.log 2 (x.natAbs) + 1
def N_of (x y : ℤ) : ℕ := max (bits x) (bits y)
/-
For `N > 64`, suitable transform parameters `(n, l)` exist with
    `l · 2^n ≥ 2N` and the termination bound `2*(3n+3l+5) ≤ N`.
-/
lemma exist_n_l (N : ℕ) (hN : 64 < N) :
    ∃ n l : ℕ, l * 2 ^ n ≥ 2 * N ∧ n ≥ 1 ∧ l ≥ 1 ∧ 2 * (3 * n + 3 * l + 5) ≤ N := by
  set n := Nat.log 2 (2*N) + 1
  refine ⟨n, 1, ?_, ?_, ?_, ?_⟩
  · simp; exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)
  · exact Nat.succ_pos _
  · exact le_refl _
  · simp only [n]
    set k := Nat.log 2 (2 * N) with hk_def
    have hk7 : k ≥ 7 := by
      have : 2 ^ 7 ≤ 2 * N := by omega
      exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr this
    have hN_lb : N ≥ 2 ^ (k - 1) := by
      have h1 : 2 ^ k ≤ 2 * N := Nat.pow_log_le_self 2 (by omega)
      have hk_pos : 1 ≤ k := by omega
      calc N = (2 * N) / 2 := by omega
        _ ≥ 2 ^ k / 2 := Nat.div_le_div_right h1
        _ = 2 ^ (k - 1) := by rw [Nat.pow_div hk_pos (by norm_num)]
    suffices h : 6 * k + 22 ≤ 2 ^ (k - 1) by omega
    have key : ∀ m : ℕ, 6 * (m + 7) + 22 ≤ 2 ^ (m + 6) := by
      intro m
      induction m with
      | zero => norm_num
      | succ n ih =>
        have : 2 ^ (n + 1 + 6) = 2 * 2 ^ (n + 6) := by
          rw [show n + 1 + 6 = (n + 6) + 1 from by omega, pow_succ]; ring
        omega
    have ⟨m, hm⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
    calc 6 * k + 22 = 6 * (m + 7) + 22 := by omega
      _ ≤ 2 ^ (m + 6) := key m
      _ = 2 ^ (k - 1) := by congr 1; omega

/-! ## Digit decomposition and recomposition -/
def decompose (β K a : ℕ) : Fin K → ℕ :=
  fun j =>
    if j.val < K - 1 then (a / β ^ j.val) % β
    else a / β ^ (K - 1)

def recompose_int {K : ℕ} (β : ℕ) (A : Fin K → ℤ) : ℤ :=
  ∑ j : Fin K, A j * (β : ℤ) ^ j.val

/-! ## Fixed-point complex numbers -/
structure FPComplex (P : ℕ) where
  re : ℤ
  im : ℤ
deriving Repr, DecidableEq

namespace FPComplex

variable {P : ℕ}
noncomputable def toℂ (z : FPComplex P) : ℂ :=
  (z.re : ℂ) / (2 : ℂ) ^ P + ((z.im : ℂ) / (2 : ℂ) ^ P) * Complex.I

instance : Zero (FPComplex P) := ⟨⟨0, 0⟩⟩
instance : One (FPComplex P) := ⟨⟨2 ^ P, 0⟩⟩

def mul (a b : FPComplex P) : FPComplex P :=
  ⟨(a.re * b.re - a.im * b.im) >>> P,
   (a.re * b.im + a.im * b.re) >>> P⟩

instance : Mul (FPComplex P) := ⟨mul⟩
def mul_via (intMul : ℤ → ℤ → ℤ) (a b : FPComplex P) : FPComplex P :=
  ⟨(intMul a.re b.re - intMul a.im b.im) >>> P,
   (intMul a.re b.im + intMul a.im b.re) >>> P⟩

def ofInt (n : ℤ) : FPComplex P := ⟨n * 2 ^ P, 0⟩

def round_re (a : FPComplex P) : ℤ :=
  if P = 0 then a.re
  else (a.re + 2^(P-1)) >>> P

end FPComplex

/-! ## Fixed-point DFT -/
namespace FPComplex
noncomputable def DFT_canonical
    {k : ℕ} {P : ℕ}
    (x : Fin (2^k) → FPComplex P) : Fin (2^k) → FPComplex P :=
  let x_ℂ : Fin (2^k) → ℂ := fun j => (x j).toℂ
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2^k) : ℂ))
  let result_ℂ := FFT_field x_ℂ ω
  fun i => ⟨round ((result_ℂ i).re * (2 : ℝ) ^ P),
            round ((result_ℂ i).im * (2 : ℝ) ^ P)⟩
/- Original definition had a bug: used `(k : ℂ)` instead of `((2^k : ℕ) : ℂ)` for the root of unity.
   For k=1 (K=2), this gives ω = exp(2πi/1) = 1 instead of exp(2πi/2) = -1,
   making the inverse DFT incorrect (it loses information). -/
-- noncomputable def DFT_inv_canonical_BUGGY
--     {k : ℕ} {P : ℕ}
--     (x : Fin (2^k) → FPComplex P) : Fin (2^k) → FPComplex P :=
--   let x_ℂ : Fin (2^k) → ℂ := fun j => (x j).toℂ
--   let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (k : ℂ))  -- BUG: should be 2^k
--   let result_ℂ_pred := FFT_field x_ℂ ω⁻¹
--   let result_ℂ := fun i => (2^k)⁻¹ * (result_ℂ_pred i)
--   fun i => ⟨round ((result_ℂ i).re * (2 : ℝ) ^ P),
--             round ((result_ℂ i).im * (2 : ℝ) ^ P)⟩
/-- Corrected inverse DFT: uses `((2^k : ℕ) : ℂ)` for the root of unity. -/
noncomputable def DFT_inv_canonical
    {k : ℕ} {P : ℕ}
    (x : Fin (2^k) → FPComplex P) : Fin (2^k) → FPComplex P :=
  let x_ℂ : Fin (2^k) → ℂ := fun j => (x j).toℂ
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2^k : ℕ) : ℂ))
  let result_ℂ_pred := FFT_field x_ℂ ω⁻¹
  let result_ℂ := fun i => (2^k)⁻¹ * (result_ℂ_pred i)
  fun i => ⟨round ((result_ℂ i).re * (2 : ℝ) ^ P),
            round ((result_ℂ i).im * (2 : ℝ) ^ P)⟩
end FPComplex
def ssa1_required_precision (n l : ℕ) : ℕ := 2 * n + 2 * l + 4
/-! ## Helper lemmas -/

lemma bits_pos (x : ℤ) : 1 ≤ bits x := by
  exact Nat.succ_pos _

lemma bits_sum_gt_max (a b : ℤ) :
    max (bits a) (bits b) < bits a + bits b := by
  exact max_lt ( lt_add_of_pos_right _ ( bits_pos _ ) ) ( lt_add_of_pos_left _ ( bits_pos _ ) )

lemma bits_le_of_natAbs_lt {x : ℤ} {k : ℕ} (hk : k ≥ 1) (hx : x.natAbs < 2^k) :
    bits x ≤ k := by
  by_cases h : x.natAbs = 0;
  · aesop;
  · exact Nat.log_lt_of_lt_pow ( by positivity ) hx

lemma dft_field_norm_bound {K : ℕ} [NeZero K]
    (x : Fin K → ℂ) (ω : ℂ) (hω : ‖ω‖ = 1) (M : ℝ) (hM : ∀ j, ‖x j‖ ≤ M)
    (i : Fin K) :
    ‖DFT_field x ω i‖ ≤ K * M := by
  refine' le_trans ( norm_sum_le _ _ ) ( le_trans ( Finset.sum_le_sum fun j _ => _ ) _ );
  exacts [ fun j => M, by simpa [ hω ] using hM j, by simpa ]

lemma abs_round_le (x : ℝ) : (round x : ℤ).natAbs ≤ ⌊|x|⌋₊ + 1 := by
  have h_round_bound : |round x - x| ≤ 1 / 2 := by
    convert abs_sub_round x using 1 ; ring;
    rw [ neg_add_eq_sub, abs_sub_comm ];
  exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; norm_num; cases abs_cases x <;> cases abs_cases ( round x : ℝ ) <;> linarith [ abs_le.mp h_round_bound, Nat.lt_floor_add_one |x| ] ;

lemma decompose_recompose (β : ℕ) (K : ℕ) (a : ℕ) (hβ : 0 < β) (hK : 0 < K) :
    recompose_int β (fun j => (decompose β K a j : ℤ)) = (a : ℤ) := by
  rcases K with ( _ | K ) <;> simp_all +decide [ Nat.pow_succ', mul_assoc, mul_comm, mul_left_comm ];
  unfold recompose_int;
  have h_decomp : ∑ j ∈ Finset.range K, ((a / β ^ j) % β) * β ^ j + (a / β ^ K) * β ^ K = a := by
    induction' K with K ih;
    · norm_num;
    · rw [ Finset.sum_range_succ, pow_succ' ];
      rw [ show a / ( β * β ^ K ) = a / β ^ K / β by rw [ Nat.div_div_eq_div_mul ] ; ring ];
      nlinarith [ Nat.mod_add_div ( a / β ^ K ) β, pow_pos hβ K ];
  unfold decompose; simp +decide [ Fin.sum_univ_castSucc, Finset.sum_range ] at *; linarith;

lemma sign_natAbs_mul (a b : ℤ) : a.sign * b.sign * (a.natAbs * b.natAbs : ℤ) = a * b := by
  grind

lemma FPComplex.mul_via_eq_mul' {P : ℕ} (a b : FPComplex P) :
    FPComplex.mul_via (· * ·) a b = FPComplex.mul a b := by
  rfl

lemma decompose_digit_bound (β K a : ℕ) (hβ : 0 < β) (j : Fin K) (hj : j.val < K - 1) :
    decompose β K a j < β := by
  unfold decompose;
  exact if_pos hj ▸ Nat.mod_lt _ hβ

lemma decompose_all_bounded (β K a : ℕ) (hβ : 0 < β) (ha : a < β ^ K) (j : Fin K) :
    decompose β K a j < β := by
  unfold decompose;
  split_ifs;
  · exact Nat.mod_lt _ hβ;
  · exact Nat.div_lt_of_lt_mul <| by cases K <;> simp_all +decide [ pow_succ' ] ; linarith;

lemma poly_product_recompose (β : ℕ) {M N : ℕ} (A : Fin M → ℤ) (B : Fin N → ℤ) :
    recompose_int (↑β) (poly_product A B) = recompose_int (↑β) A * recompose_int (↑β) B := by
  convert eval_poly_product_eq_mul_eval A B ( β : ℚ ) using 1;
  unfold recompose_int; norm_cast;

lemma dft_canonical_component_bound
    {n l : ℕ} (hn : n ≥ 1) (hl : l ≥ 1)
    (x' : ℕ) (hx : x' < (2^l)^(2^n))
    (i : Fin (2^n)) :
    (@FPComplex.DFT_canonical n (ssa1_required_precision n l)
      (fun j => FPComplex.ofInt (↑(decompose (2^l) (2^n) x' j))) i).re.natAbs
      < 2 ^ (3 * n + 3 * l + 5) ∧
    (@FPComplex.DFT_canonical n (ssa1_required_precision n l)
      (fun j => FPComplex.ofInt (↑(decompose (2^l) (2^n) x' j))) i).im.natAbs
      < 2 ^ (3 * n + 3 * l + 5) := by
  -- By definition of $DFT_canonical$, we know that the norm of the DFT result is bounded by $2^n * 2^l = 2^{n+l}$.
  have h_norm_bound : ∀ i : Fin (2 ^ n), ‖(FFT_field (fun j => (decompose (2 ^ l) (2 ^ n) x' j : ℂ)) (Complex.exp (2 * Real.pi * Complex.I / (2 ^ n : ℂ))) i)‖ ≤ 2 ^ (n + l) := by
    have h_norm_bound : ∀ i : Fin (2 ^ n), ‖(DFT_field (fun j => (decompose (2 ^ l) (2 ^ n) x' j : ℂ)) (Complex.exp (2 * Real.pi * Complex.I / (2 ^ n : ℂ))) i)‖ ≤ 2 ^ n * 2 ^ l := by
      intro i;
      convert dft_field_norm_bound _ _ _ _ _ _ using 1;
      norm_cast;
      rw [ Nat.cast_mul ];
      · norm_num [ Complex.norm_exp ];
        norm_num [ div_eq_mul_inv ];
        norm_cast;
      · intro j; exact_mod_cast Nat.le_of_lt ( decompose_all_bounded _ _ _ ( by positivity ) ( by
          exact hx ) j ) ;
    intro i; convert h_norm_bound i using 1; rw [ FFT_eq_DFT ] ; ring;
    · convert Complex.isPrimitiveRoot_exp _ _ using 2 ; ring;
      · norm_num [ ← inv_pow ];
      · positivity;
    · ring;
  constructor <;> refine' lt_of_le_of_lt ( abs_round_le _ ) _;
  · refine' Nat.lt_of_le_of_lt ( Nat.succ_le_of_lt ( Nat.floor_lt ( by positivity ) |>.2 _ ) ) _;
    exact 2 ^ ( n + l ) * 2 ^ ( 2 * n + 2 * l + 4 ) + 1;
    · refine' lt_of_le_of_lt ( _ : _ ≤ _ ) ( Nat.cast_lt.mpr ( Nat.lt_succ_self _ ) );
      convert mul_le_mul_of_nonneg_right ( Complex.abs_re_le_norm _ |> le_trans <| h_norm_bound i ) ( by positivity : ( 0 : ℝ ) ≤ 2 ^ ( 2 * n + 2 * l + 4 ) ) using 1 ; norm_num [ ssa1_required_precision ] ; ring;
      · unfold FPComplex.ofInt; norm_num [ FPComplex.toℂ ] ;
      · norm_cast;
    · ring_nf;
      nlinarith [ pow_pos ( by decide : 0 < 2 ) ( n * 3 ), pow_pos ( by decide : 0 < 2 ) ( l * 3 ) ];
  · refine' lt_of_le_of_lt ( Nat.succ_le_of_lt ( Nat.floor_lt' _ |>.2 _ ) ) _;
    exact 2 ^ ( n + l + ssa1_required_precision n l ) + 1;
    · positivity;
    · refine' lt_of_le_of_lt ( _ : _ ≤ _ ) ( Nat.cast_lt.mpr ( Nat.lt_succ_self _ ) );
      norm_num [ pow_add ] at *;
      convert Complex.abs_im_le_norm _ |> le_trans <| h_norm_bound i using 1;
      unfold FPComplex.toℂ;
      unfold FPComplex.ofInt; norm_num [ pow_add, pow_mul ] ;
    · unfold ssa1_required_precision; ring_nf;
      nlinarith [ pow_pos ( by decide : 0 < 2 ) ( n * 3 ), pow_pos ( by decide : 0 < 2 ) ( l * 3 ) ]

/-! ## Recursive SSA I -/
lemma natAbs_lt_pow_bits (a : ℤ) : a.natAbs < 2 ^ (bits a) :=
  Nat.lt_pow_succ_log_self (by norm_num) a.natAbs
lemma natAbs_lt_of_bits_le_of_le {a : ℤ} {N M : ℕ} (haN : bits a ≤ N) (hNM : N ≤ M) :
    a.natAbs < 2 ^ M :=
  lt_of_lt_of_le (natAbs_lt_pow_bits a) (Nat.pow_le_pow_right (by norm_num) (le_trans haN hNM))
def ssa1_base_threshold : ℕ := 64
lemma FPComplex.ofInt_toC {P : ℕ} (z : ℤ) :
    (FPComplex.ofInt z : FPComplex P).toℂ = (z : ℂ) := by
  simp [FPComplex.ofInt, FPComplex.toℂ]
lemma round_div_approx (x : ℝ) (P : ℕ) :
    |((round (x * (2 : ℝ)^P) : ℤ) : ℝ) / (2 : ℝ)^P - x| ≤ 1 / (2 * (2 : ℝ)^P) := by
  rw [ div_sub' ] <;> norm_num;
  rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 ^ P ) ];
  rw [ inv_mul_eq_div, div_le_div_iff_of_pos_right ] <;> norm_num;
  convert abs_sub_round ( x * 2 ^ P ) using 1 ; ring;
  rw [ neg_add_eq_sub, abs_sub_comm ]
lemma Complex.norm_le_abs_re_add_abs_im' (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| :=
  Complex.norm_le_abs_re_add_abs_im z
lemma fpcomplex_mul_toC_approx {P : ℕ} (a b : FPComplex P) :
    ‖(FPComplex.mul a b).toℂ - a.toℂ * b.toℂ‖ ≤ 2 / (2 : ℝ)^P := by
  unfold FPComplex.mul FPComplex.toℂ;
  norm_num [ Complex.normSq, Complex.norm_def ];
  norm_cast ; norm_num [ div_eq_mul_inv ];
  rw [ Real.sqrt_le_left ] <;> norm_num [ Rat.divInt_eq_div ];
  field_simp;
  have h_bound : ∀ x : ℤ, |(x >>> P : ℤ) * (2 : ℝ) ^ P - x| ≤ 2 ^ P := by
    intro x; norm_cast; simp +decide [ Int.shiftRight_eq_div_pow ] ;
    exact abs_le.mpr ⟨ by linarith [ Int.mul_ediv_add_emod x ( 2 ^ P ), Int.emod_nonneg x ( by positivity : ( 2 ^ P : ℤ ) ≠ 0 ), Int.emod_lt_of_pos x ( by positivity : ( 2 ^ P : ℤ ) > 0 ) ], by linarith [ Int.mul_ediv_add_emod x ( 2 ^ P ), Int.emod_nonneg x ( by positivity : ( 2 ^ P : ℤ ) ≠ 0 ), Int.emod_lt_of_pos x ( by positivity : ( 2 ^ P : ℤ ) > 0 ) ] ⟩;
  have := h_bound ( a.re * b.re - a.im * b.im ) ; have := h_bound ( a.re * b.im + a.im * b.re ) ; norm_num [ abs_le ] at *;
  nlinarith [ pow_pos ( zero_lt_two' ℝ ) P ]
lemma mul_approx_norm (a b α β : ℂ) (εα εβ : ℝ) (hεα : 0 ≤ εα) (hεβ : 0 ≤ εβ)
    (hα : ‖α - a‖ ≤ εα) (hβ : ‖β - b‖ ≤ εβ) (Ma Mb : ℝ)
    (ha : ‖a‖ ≤ Ma) (hb : ‖b‖ ≤ Mb) :
    ‖α * β - a * b‖ ≤ Ma * εβ + εα * Mb + εα * εβ := by
  have h_triangle : ‖α * β - a * b‖ ≤ ‖a‖ * ‖β - b‖ + ‖α - a‖ * ‖b‖ + ‖α - a‖ * ‖β - b‖ := by
    rw [ show α * β - a * b = a * ( β - b ) + ( α - a ) * b + ( α - a ) * ( β - b ) by ring ] ; exact le_trans ( norm_add₃_le .. ) ( by norm_num ) ;
  exact h_triangle.trans ( add_le_add_three ( mul_le_mul ha hβ ( by positivity ) ( by linarith [ norm_nonneg a ] ) ) ( mul_le_mul hα hb ( by positivity ) ( by linarith [ norm_nonneg b ] ) ) ( mul_le_mul hα hβ ( by positivity ) ( by linarith [ norm_nonneg α ] ) ) )
lemma norm_exp_2pi_div (K : ℕ) [NeZero K] :
    ‖Complex.exp (2 * Real.pi * Complex.I / (K : ℂ))‖ = 1 := by
  norm_num [ Complex.norm_exp, Complex.norm_exp ]
lemma idft_error_bound' {K : ℕ} [NeZero K]
    (f g : Fin K → ℂ) (ε : ℝ) (hε : ∀ i, ‖f i - g i‖ ≤ ε)
    (ω : ℂ) (hω : ‖ω‖ = 1) (k : Fin K) :
    |(DFT_field_inv f ω k - DFT_field_inv g ω k).re| ≤ ε := by
  have h_idft : DFT_field_inv f ω k - DFT_field_inv g ω k = (1 / K : ℂ) * ∑ i, (f i - g i) * (ω⁻¹) ^ (i.val * k.val) := by
    unfold DFT_field_inv DFT_field; simp +decide [ sub_mul, mul_sub, Finset.mul_sum _ _ _ ] ;
  have h_triangle : ‖∑ i, (f i - g i) * (ω⁻¹) ^ (i.val * k.val)‖ ≤ K * ε := by
    exact le_trans ( norm_sum_le _ _ ) ( le_trans ( Finset.sum_le_sum fun i _ => by simpa [ hω ] using hε i ) ( by norm_num ) );
  simp_all +decide [ Complex.normSq, Complex.norm_def ];
  rw [ inv_mul_le_iff₀ ( Nat.cast_pos.mpr <| NeZero.pos K ) ];
  exact le_trans ( Real.abs_le_sqrt <| by nlinarith ) h_triangle
lemma int_norm_le_of_natAbs_lt {l : ℕ} (z : ℤ) (hz : z.natAbs < 2^l) : ‖(z : ℂ)‖ ≤ (2^l : ℝ) := by
  simp only [Complex.norm_intCast]
  calc |(z : ℝ)| = ↑(|z| : ℤ) := by push_cast; rfl
    _ = ↑((z.natAbs : ℤ)) := by rw [Int.abs_eq_natAbs]
    _ ≤ _ := by exact_mod_cast le_of_lt hz
/-- Key lemma for termination: from the dft bound and exist_n_l, recursive call arguments
    have strictly smaller `max bits`. -/
lemma bits_of_dft_component_lt {n l N : ℕ}
    (hn : n ≥ 1) (hl : l ≥ 1) (hbound : 2 * (3 * n + 3 * l + 5) ≤ N)
    (z : ℤ) (hz : z.natAbs < 2 ^ (3 * n + 3 * l + 5)) :
    bits z < N := by
  have hbits : bits z ≤ 3 * n + 3 * l + 5 := by
    exact bits_le_of_natAbs_lt (by omega) hz
  omega

noncomputable def ssa1_multiply : ℤ → ℤ → ℤ
  | a, b =>
    let N := max (bits a) (bits b)
    if hN : ssa1_base_threshold < N then
      let sgn : ℤ := a.sign * b.sign
      let x' : ℕ := a.natAbs
      let y' : ℕ := b.natAbs

      -- Choose transform parameters
      let n := Classical.choose (exist_n_l N hN)
      let hl := Classical.choose_spec (exist_n_l N hN)
      let l := Classical.choose hl
      let β : ℕ := 2 ^ l
      let K : ℕ := 2 ^ n
      haveI : NeZero K := ⟨by positivity⟩

      -- Pick precision according to the bound
      let P : ℕ := ssa1_required_precision n l

      -- Decompose operands into digits and embed into FPComplex P (exactly)
      let A : Fin (2 ^ n) → FPComplex P :=
        fun i => FPComplex.ofInt (decompose β K x' i : ℤ)
      let B : Fin (2 ^ n) → FPComplex P :=
        fun i => FPComplex.ofInt (decompose β K y' i : ℤ)

      -- Forward DFTs
      let A_hat := FPComplex.DFT_canonical A
      let B_hat := FPComplex.DFT_canonical B

      -- Prove bounds on DFT components (for termination of recursive calls)
      have hx_bound : x' < (2 ^ l) ^ (2 ^ n) := by
        have h := natAbs_lt_of_bits_le_of_le (le_max_left (bits a) (bits b))
          (le_trans (le_mul_of_one_le_left (Nat.zero_le N) (by norm_num)) (Classical.choose_spec hl).1)
        rwa [pow_mul] at h
      have hy_bound : y' < (2 ^ l) ^ (2 ^ n) := by
        have h := natAbs_lt_of_bits_le_of_le (le_max_right (bits a) (bits b))
          (le_trans (le_mul_of_one_le_left (Nat.zero_le N) (by norm_num)) (Classical.choose_spec hl).1)
        rwa [pow_mul] at h

      -- Pointwise multiplication: inline mul_via so termination checker sees arguments
      let C_hat : Fin K → FPComplex P :=
        fun i =>
          have hAi := dft_canonical_component_bound (Classical.choose_spec hl).2.1 (Classical.choose_spec hl).2.2.1 x' hx_bound i
          have hBi := dft_canonical_component_bound (Classical.choose_spec hl).2.1 (Classical.choose_spec hl).2.2.1 y' hy_bound i
          ⟨(ssa1_multiply (A_hat i).re (B_hat i).re -
            ssa1_multiply (A_hat i).im (B_hat i).im) >>> P,
           (ssa1_multiply (A_hat i).re (B_hat i).im +
            ssa1_multiply (A_hat i).im (B_hat i).re) >>> P⟩

      -- Inverse DFT (already includes 1/K normalization)
      let C := FPComplex.DFT_inv_canonical C_hat

      -- Round each coefficient to ℤ, recompose at base β
      let C_int : Fin K → ℤ := fun j => FPComplex.round_re (C j)

      sgn * recompose_int β C_int
    else
      a * b
termination_by x y => bits x + bits y
decreasing_by
  all_goals {
    show _ < bits a + bits b
    calc bits _ + bits _
        ≤ (3*n+3*l+5) + (3*n+3*l+5) := by
          apply Nat.add_le_add <;>
            exact bits_le_of_natAbs_lt (k := 3*n+3*l+5) (by
              have := (Classical.choose_spec hl).2.1
              have := (Classical.choose_spec hl).2.2.1
              omega) (by
              first
              | exact hAi.1
              | exact hAi.2
              | exact hBi.1
              | exact hBi.2)
      _ = 2 * (3*n+3*l+5) := by ring
      _ ≤ N := (Classical.choose_spec hl).2.2.2
      _ < bits a + bits b := bits_sum_gt_max a b
  }


/- The key helper lemma `dft_pipeline_gives_product` (now called `dft_pipeline_gives_product'`)
   is proved in RequestProject/SSAPipeline.lean, which imports this file.
   It combines the numerical error analysis with the algebraic correctness
   of cyclic convolution for zero-padded digit sequences. -/

/-! ### Sub-lemma: digits are zero in upper half when x < β^(K/2) -/

lemma decompose_zero_upper_half (β K : ℕ) (a : ℕ) (hβ : 0 < β) (hK : 0 < K)
    (ha : a < β ^ (K / 2)) (j : Fin K) (hj : K / 2 ≤ j.val) :
    decompose β K a j = 0 := by
  unfold decompose;
  split_ifs <;> norm_num [ Nat.div_eq_of_lt ha, hj ];
  · rw [ Nat.div_eq_of_lt ( lt_of_lt_of_le ha ( Nat.pow_le_pow_right hβ ( by omega ) ) ), Nat.zero_mod ];
  · exact Or.inr ( ha.trans_le ( Nat.pow_le_pow_right hβ ( Nat.le_sub_one_of_lt ( by omega ) ) ) )

/-! ### Sub-lemma: recomposition of cyclic convolution of zero-padded sequences equals product -/

lemma cyclic_conv_zero_padded_recompose (β : ℕ) (K : ℕ) [NeZero K] (hβ : 0 < β)
    (A B : Fin K → ℤ)
    (hA : ∀ j : Fin K, K / 2 ≤ j.val → A j = 0)
    (hB : ∀ j : Fin K, K / 2 ≤ j.val → B j = 0) :
    recompose_int (↑β) (cyclic_convolution_benchmark A B) =
    recompose_int (↑β) A * recompose_int (↑β) B := by
  unfold recompose_int cyclic_convolution_benchmark;
  -- By definition of convolution, we can rewrite the left-hand side as a double sum.
  have h_conv : ∑ j : Fin K, (∑ j_1 : Fin K, A j_1 * B ⟨(j.val + K - j_1.val) % K, Nat.mod_lt _ (NeZero.pos K)⟩) * (β : ℤ) ^ j.val = ∑ j_1 : Fin K, ∑ j : Fin K, A j_1 * B j * (β : ℤ) ^ ((j_1.val + j.val) % K) := by
    simp +decide only [Finset.sum_mul _ _ _];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun i hi => _;
    refine' Finset.sum_bij ( fun j hj => ⟨ ( j + K - i ) % K, Nat.mod_lt _ ( NeZero.pos K ) ⟩ ) _ _ _ _ <;> simp +decide [ Fin.ext_iff ];
    · intro a₁ a₂ h; have := Nat.modEq_iff_dvd.mp h.symm; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
      obtain ⟨ k, hk ⟩ := this; rw [ Nat.cast_sub ( by linarith [ Fin.is_lt a₁, Fin.is_lt i ] ), Nat.cast_sub ( by linarith [ Fin.is_lt a₂, Fin.is_lt i ] ) ] at hk; norm_num at hk; nlinarith [ show k = 0 by nlinarith [ Fin.is_lt a₁, Fin.is_lt a₂, Fin.is_lt i ] ] ;
    · intro b; use ⟨ ( b + i ) % K, Nat.mod_lt _ ( NeZero.pos K ) ⟩ ; simp +decide [ Nat.mod_eq_of_lt ] ;
      simp +decide [ add_assoc, Nat.add_sub_assoc, Nat.mod_eq_of_lt ];
    · intro a; rw [ add_tsub_cancel_of_le ( by linarith [ Fin.is_lt i, Fin.is_lt a ] ) ] ; norm_num;
      exact Or.inl ( by rw [ Nat.mod_eq_of_lt ( Fin.is_lt a ) ] );
  -- By definition of convolution, we can rewrite the left-hand side as a double sum and then factor out the common terms.
  have h_conv_factor : ∑ j_1 : Fin K, ∑ j : Fin K, A j_1 * B j * (β : ℤ) ^ ((j_1.val + j.val) % K) = ∑ j_1 : Fin K, ∑ j : Fin K, A j_1 * B j * (β : ℤ) ^ (j_1.val + j.val) := by
    refine' Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => _;
    by_cases hi' : K / 2 ≤ i.val <;> by_cases hj' : K / 2 ≤ j.val <;> simp_all +decide;
    exact Or.inl ( by rw [ Nat.mod_eq_of_lt ( by linarith [ Nat.div_mul_le_self K 2 ] ) ] );
  simp_all +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option grind.warning false

/-!
# Pipeline correctness: DFT → pointwise multiply → IDFT → round gives exact cyclic convolution
-/

/-! ## Forward DFT approximation error -/

/-
DFT_canonical output.toℂ has norm error ≤ 1/2^P from the exact FFT value.
-/
lemma dft_canonical_norm_error {k P : ℕ}
    (x : Fin (2^k) → FPComplex P) (i : Fin (2^k)) :
    let ω := Complex.exp (2 * Real.pi * Complex.I / (2^k : ℂ))
    ‖(FPComplex.DFT_canonical x i).toℂ - FFT_field (fun j => (x j).toℂ) ω i‖
    ≤ 1 / (2^P : ℝ) := by
  refine' Complex.norm_le_abs_re_add_abs_im _ |> le_trans <| _;
  unfold FPComplex.toℂ FPComplex.DFT_canonical;
  norm_cast ; norm_num [ mul_div_mul_comm ];
  norm_num [ Rat.divInt_eq_div ];
  convert add_le_add ( round_div_approx _ _ ) ( round_div_approx _ _ ) using 1 ; ring

/-! ## round_re correctness when close to integer -/

/-
If an FPComplex P value has .re close enough to n * 2^P, round_re returns n.
-/
lemma round_re_eq_of_close {P : ℕ} (hP : P ≥ 1)
    (z : FPComplex P) (n : ℤ)
    (h : |z.re - n * (2 : ℤ)^P| < 2^(P-1)) :
    z.round_re = n := by
  -- Apply the definition of `round_re` to `(z.re + 2^(P-1)) >>> P`.
  have h_round : (z.re + 2^(P-1)) / 2^P = n := by
    rcases P with ( _ | P ) <;> simp_all +decide [ pow_succ' ];
    exact Int.le_antisymm ( Int.le_of_lt_add_one <| Int.ediv_lt_of_lt_mul ( by positivity ) <| by linarith [ abs_lt.mp h ] ) ( Int.le_ediv_of_mul_le ( by positivity ) <| by linarith [ abs_lt.mp h ] );
  unfold FPComplex.round_re;
  cases P <;> simp_all +decide [ pow_succ', Int.shiftRight_eq_div_pow ]

/-! ## Main helper: pointwise error bound on C_hat -/

/-
The DFT magnitude of digit sequences is bounded by 2^(n+l).
-/
lemma dft_digit_norm_bound {n l : ℕ}
    (x' : ℕ) (hx : x' < (2^l)^(2^n)) (i : Fin (2^n)) :
    let ω := Complex.exp (2 * Real.pi * Complex.I / (2^n : ℂ))
    ‖DFT_field (fun j : Fin (2^n) => (↑(decompose (2^l) (2^n) x' j) : ℂ)) ω i‖ ≤ (2^n : ℝ) * (2^l : ℝ) := by
  refine' le_trans ( dft_field_norm_bound _ _ _ _ _ _ ) _;
  rotate_left;
  exact 2 ^ l;
  · intro j;
    convert int_norm_le_of_natAbs_lt _ _;
    convert decompose_all_bounded ( 2 ^ l ) ( 2 ^ n ) x' ( by positivity ) hx j using 1;
  · norm_num;
  · norm_num [ Complex.norm_exp ];
    norm_num [ div_eq_mul_inv ];
    norm_cast

/-
The numerical bound: for P = 2n+2l+4 and M = 2^(n+l):
    2/2^P + 2M/2^P + 1/2^(2P) ≤ 1/4
-/
lemma numerical_bound_le_quarter (n l : ℕ) (hn : n ≥ 1) (hl : l ≥ 1) :
    (2 : ℝ) / 2^(ssa1_required_precision n l) +
    2 * ((2^n : ℝ) * (2^l : ℝ)) / 2^(ssa1_required_precision n l) +
    1 / (2^(ssa1_required_precision n l) * 2^(ssa1_required_precision n l)) ≤ 1/4 := by
  unfold ssa1_required_precision;
  rcases n with ( _ | _ | n ) <;> norm_num at *;
  · ring_nf;
    norm_num [ pow_mul', ← mul_pow ];
    exact le_trans ( add_le_add_three ( mul_le_mul_of_nonneg_right ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) hl ) ( by norm_num ) ) ( mul_le_mul_of_nonneg_right ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) hl ) ( by norm_num ) ) ( mul_le_mul_of_nonneg_right ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) hl ) ( by norm_num ) ) ) ( by norm_num );
  · field_simp;
    ring_nf;
    norm_cast ; norm_num [ pow_mul', ← mul_pow ];
    nlinarith [ pow_pos ( by decide : 0 < 4 ) n, pow_pos ( by decide : 0 < 4 ) l, pow_le_pow_left' ( by decide : 4 ≤ 8 ) n, pow_le_pow_left' ( by decide : 4 ≤ 8 ) l, pow_le_pow_left' ( by decide : 8 ≤ 16 ) n, pow_le_pow_left' ( by decide : 8 ≤ 16 ) l ]

lemma pointwise_error_bound
    {n l : ℕ} (hn : n ≥ 1) (hl : l ≥ 1)
    (x' y' : ℕ) (hx : x' < (2^l)^(2^n)) (hy : y' < (2^l)^(2^n))
    (i : Fin (2^n)) :
    let ω := Complex.exp (2 * Real.pi * Complex.I / (2^n : ℂ))
    ‖(FPComplex.mul
        (FPComplex.DFT_canonical (fun j => FPComplex.ofInt (P := ssa1_required_precision n l) (↑(decompose (2^l) (2^n) x' j))) i)
        (FPComplex.DFT_canonical (fun j => FPComplex.ofInt (P := ssa1_required_precision n l) (↑(decompose (2^l) (2^n) y' j))) i)).toℂ -
      DFT_field (fun j : Fin (2^n) => (↑(decompose (2^l) (2^n) x' j) : ℂ)) ω i *
      DFT_field (fun j : Fin (2^n) => (↑(decompose (2^l) (2^n) y' j) : ℂ)) ω i‖ ≤ 1/4 := by
  have := @dft_canonical_norm_error;
  specialize @this n ( ssa1_required_precision n l ) ( fun j => FPComplex.ofInt ( decompose ( 2 ^ l ) ( 2 ^ n ) x' j ) ) i ; norm_num at this;
  have := @dft_canonical_norm_error n ( ssa1_required_precision n l ) ( fun j => FPComplex.ofInt ( decompose ( 2 ^ l ) ( 2 ^ n ) y' j ) ) i ; norm_num at this;
  have := @fpcomplex_mul_toC_approx ( ssa1_required_precision n l ) ( FPComplex.DFT_canonical ( fun j => FPComplex.ofInt ( decompose ( 2 ^ l ) ( 2 ^ n ) x' j ) ) i ) ( FPComplex.DFT_canonical ( fun j => FPComplex.ofInt ( decompose ( 2 ^ l ) ( 2 ^ n ) y' j ) ) i ) ; norm_num at this;
  have := @dft_digit_norm_bound n l x' hx i; have := @dft_digit_norm_bound n l y' hy i; norm_num at *;
  have := @FFT_eq_DFT ( Complex ) _ n ( Complex.exp ( 2 * Real.pi * Complex.I / 2 ^ n ) ) ?_ ( fun j => ( decompose ( 2 ^ l ) ( 2 ^ n ) x' j : ℂ ) ) <;> norm_num at *;
  · have := @FFT_eq_DFT ( Complex ) _ n ( Complex.exp ( 2 * Real.pi * Complex.I / 2 ^ n ) ) ?_ ( fun j => ( decompose ( 2 ^ l ) ( 2 ^ n ) y' j : ℂ ) ) <;> norm_num at *;
    · simp_all +decide [ FPComplex.ofInt_toC ];
      rename_i h₁ h₂ h₃ h₄ h₅ h₆;
      have := @numerical_bound_le_quarter n l hn hl;
      have := @mul_approx_norm;
      specialize this ( DFT_field ( fun j => ( decompose ( 2 ^ l ) ( 2 ^ n ) x' j : ℂ ) ) ( Complex.exp ( 2 * Real.pi * Complex.I / 2 ^ n ) ) i ) ( DFT_field ( fun j => ( decompose ( 2 ^ l ) ( 2 ^ n ) y' j : ℂ ) ) ( Complex.exp ( 2 * Real.pi * Complex.I / 2 ^ n ) ) i ) ( ( FPComplex.DFT_canonical ( fun j => FPComplex.ofInt ( decompose ( 2 ^ l ) ( 2 ^ n ) x' j ) ) i ).toℂ ) ( ( FPComplex.DFT_canonical ( fun j => FPComplex.ofInt ( decompose ( 2 ^ l ) ( 2 ^ n ) y' j ) ) i ).toℂ ) ( ( 2 ^ ssa1_required_precision n l ) ⁻¹ ) ( ( 2 ^ ssa1_required_precision n l ) ⁻¹ ) ( by positivity ) ( by positivity ) h₁ h₂ ( 2 ^ n * 2 ^ l ) ( 2 ^ n * 2 ^ l ) h₄ h₅ ; norm_num at *;
      refine le_trans ?_ this;
      convert le_trans ( norm_add_le _ _ ) ( add_le_add h₃ ‹_› ) using 1 ; ring;
      ring;
    · convert Complex.isPrimitiveRoot_exp _ _ using 2 ; norm_num [ Nat.cast_pow ];
      positivity;
  · convert Complex.isPrimitiveRoot_exp _ _ using 2 ; norm_num [ Nat.cast_pow ];
    positivity

/-! ## Each pipeline coefficient equals the cyclic convolution coefficient -/

lemma pipeline_coeff_correct
    {n l : ℕ} (hn : n ≥ 1) (hl : l ≥ 1)
    (x' y' : ℕ) (hx : x' < (2^l)^(2^n)) (hy : y' < (2^l)^(2^n))
    (j : Fin (2^n)) :
    let P := ssa1_required_precision n l
    let K := 2^n
    let β := 2^l
    haveI : NeZero K := ⟨by positivity⟩
    let A := fun j => FPComplex.ofInt (P := P) (↑(decompose β K x' j))
    let B := fun j => FPComplex.ofInt (P := P) (↑(decompose β K y' j))
    let A_hat := FPComplex.DFT_canonical A
    let B_hat := FPComplex.DFT_canonical B
    let C_hat : Fin K → FPComplex P := fun i => FPComplex.mul (A_hat i) (B_hat i)
    let C := FPComplex.DFT_inv_canonical C_hat
    (C j).round_re = cyclic_convolution_benchmark
      (fun j => (↑(decompose β K x' j) : ℤ))
      (fun j => (↑(decompose β K y' j) : ℤ)) j := by
  intro j
  set P := ssa1_required_precision n l
  set K := 2 ^ n
  set β := 2 ^ l
  set A : Fin K → FPComplex P := fun j => FPComplex.ofInt (decompose β K x' j : ℤ)
  set B : Fin K → FPComplex P := fun j => FPComplex.ofInt (decompose β K y' j : ℤ)
  set A_hat := FPComplex.DFT_canonical A
  set B_hat := FPComplex.DFT_canonical B
  set C_hat : Fin K → FPComplex P := fun i => FPComplex.mul (A_hat i) (B_hat i)
  set C := FPComplex.DFT_inv_canonical C_hat
  set C_int : Fin K → ℤ := fun j => (C j).round_re;
  -- By definition of $C_int$, we know that $C_int j = \text{round}((C j).re)$.
  have hC_int : ∀ j, |(C j).re - (cyclic_convolution_benchmark (fun j => (decompose β K x' j : ℤ)) (fun j => (decompose β K y' j : ℤ)) j : ℝ) * 2^P| ≤ 1/2 + (1/4 : ℝ) * 2^P := by
    intro j
    have h_error_bound : |(C j).re - (cyclic_convolution_benchmark (fun j => (decompose β K x' j : ℤ)) (fun j => (decompose β K y' j : ℤ)) j : ℝ) * 2^P| ≤ 1/2 + (1/4 : ℝ) * 2^P := by
      have h_idft_error : |(DFT_field_inv (fun i => (C_hat i).toℂ) (Complex.exp (2 * Real.pi * Complex.I / (K : ℂ))) j).re - (cyclic_convolution_benchmark (fun j => (decompose β K x' j : ℤ)) (fun j => (decompose β K y' j : ℤ)) j : ℝ)| ≤ 1/4 := by
        have h_idft_error : |(DFT_field_inv (fun i => (C_hat i).toℂ) (Complex.exp (2 * Real.pi * Complex.I / (K : ℂ))) j).re - (DFT_field_inv (fun i => (DFT_field (fun j => (decompose β K x' j : ℂ)) (Complex.exp (2 * Real.pi * Complex.I / (K : ℂ))) i) * (DFT_field (fun j => (decompose β K y' j : ℂ)) (Complex.exp (2 * Real.pi * Complex.I / (K : ℂ))) i)) (Complex.exp (2 * Real.pi * Complex.I / (K : ℂ))) j).re| ≤ 1/4 := by
          apply idft_error_bound';
          · convert pointwise_error_bound hn hl x' y' hx hy using 1;
            grind +locals;
          · norm_num [ Complex.norm_exp ];
        convert h_idft_error using 3;
        have := cyclic_convolution_theorem ( show ( K : ℂ ) ≠ 0 from by norm_cast; positivity ) ( show IsPrimitiveRoot ( Complex.exp ( 2 * Real.pi * Complex.I / ( K : ℂ ) ) ) K from ?_ ) ( fun j => ( decompose β K x' j : ℂ ) ) ( fun j => ( decompose β K y' j : ℂ ) );
        · convert congr_arg ( fun f => f j |> Complex.re ) this.symm using 1;
          norm_num [ cyclic_convolution_benchmark ];
        · convert Complex.isPrimitiveRoot_exp _ _ using 2 ; norm_num [ K ]
      have h_round_error : |(C j).re - (DFT_field_inv (fun i => (C_hat i).toℂ) (Complex.exp (2 * Real.pi * Complex.I / (K : ℂ))) j).re * 2^P| ≤ 1/2 := by
        have h_round_error : ∀ z : ℂ, |(round (z.re * 2^P) : ℝ) - z.re * 2^P| ≤ 1/2 := by
          exact fun z => abs_sub_le_iff.mpr ⟨ by linarith [ abs_le.mp ( abs_sub_round ( z.re * 2 ^ P ) ) ], by linarith [ abs_le.mp ( abs_sub_round ( z.re * 2 ^ P ) ) ] ⟩;
        convert h_round_error _ using 1;
        swap;
        exact ( DFT_field_inv ( fun i => ( C_hat i |> FPComplex.toℂ ) ) ( Complex.exp ( 2 * Real.pi * Complex.I / K ) ) j );
        simp +zetaDelta at *;
        unfold FPComplex.DFT_inv_canonical; norm_num [ DFT_field_inv ] ;
        rw [ FFT_eq_DFT ];
        rw [ IsPrimitiveRoot.inv_iff ];
        convert Complex.isPrimitiveRoot_exp _ _ using 2 ; norm_num [ Nat.cast_pow ];
        positivity;
      exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp h_idft_error, abs_le.mp h_round_error, pow_pos ( zero_lt_two' ℝ ) P ], by nlinarith [ abs_le.mp h_idft_error, abs_le.mp h_round_error, pow_pos ( zero_lt_two' ℝ ) P ] ⟩;
    convert h_error_bound using 1;
  have h_round_re : ∀ j, |(C j).re - (cyclic_convolution_benchmark (fun j => (decompose β K x' j : ℤ)) (fun j => (decompose β K y' j : ℤ)) j : ℤ) * 2^P| < 2^(P-1) := by
    intro j
    specialize hC_int j
    have hP_ge_8 : 8 ≤ P := by
      exact le_trans ( by decide ) ( Nat.add_le_add ( Nat.add_le_add ( Nat.mul_le_mul_left 2 hn ) ( Nat.mul_le_mul_left 2 hl ) ) le_rfl )
    have h_bound : 1 / 2 + (1 / 4 : ℝ) * 2^P < 2^(P-1) := by
      rcases P with ( _ | _ | P ) <;> norm_num [ pow_succ' ] at *;
      linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show P ≥ 6 by linarith ) ]
    exact (by
    rw [ ← @Int.cast_lt ℝ ] ; norm_num;
    convert lt_of_le_of_lt hC_int h_bound using 1;
    norm_num [ cyclic_convolution_benchmark ]);
  convert round_re_eq_of_close _ _ _ _ using 1;
  · exact Nat.succ_le_of_lt ( by exact Nat.succ_pos _ );
  · exact h_round_re _

/-! ## Algebraic part: recomposition = product -/

lemma dft_pipeline_gives_product'
    {n l : ℕ} (hn : n ≥ 1) (hl : l ≥ 1)
    (x' y' : ℕ)
    (hx : x' < (2^l)^(2^(n-1)))
    (hy : y' < (2^l)^(2^(n-1))) :
    let P := ssa1_required_precision n l
    let β := 2^l
    let K := 2^n
    haveI : NeZero K := ⟨by positivity⟩
    let A : Fin K → FPComplex P := fun j => FPComplex.ofInt (↑(decompose β K x' j))
    let B : Fin K → FPComplex P := fun j => FPComplex.ofInt (↑(decompose β K y' j))
    let A_hat := FPComplex.DFT_canonical A
    let B_hat := FPComplex.DFT_canonical B
    let C_hat : Fin K → FPComplex P := fun i => FPComplex.mul (A_hat i) (B_hat i)
    let C := FPComplex.DFT_inv_canonical C_hat
    let C_int : Fin K → ℤ := fun j => (C j).round_re
    recompose_int (↑β) C_int = ↑x' * ↑y' := by
  have hx_full : x' < (2^l)^(2^n) :=
    lt_of_lt_of_le hx (Nat.pow_le_pow_right (by positivity) (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)))
  have hy_full : y' < (2^l)^(2^n) :=
    lt_of_lt_of_le hy (Nat.pow_le_pow_right (by positivity) (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)))
  have h_coeff : ∀ j, (FPComplex.DFT_inv_canonical (fun i =>
      FPComplex.mul (FPComplex.DFT_canonical (fun j => FPComplex.ofInt (P := ssa1_required_precision n l) (↑(decompose (2^l) (2^n) x' j))) i)
                     (FPComplex.DFT_canonical (fun j => FPComplex.ofInt (P := ssa1_required_precision n l) (↑(decompose (2^l) (2^n) y' j))) i)) j).round_re =
      cyclic_convolution_benchmark
        (fun j => (↑(decompose (2^l) (2^n) x' j) : ℤ))
        (fun j => (↑(decompose (2^l) (2^n) y' j) : ℤ)) j := by
    intro j
    exact pipeline_coeff_correct hn hl x' y' hx_full hy_full j
  have hK_half : 2^n / 2 = 2^(n-1) := Nat.pow_div hn (by norm_num)
  have hx_half : x' < (2^l) ^ (2^n / 2) := hK_half ▸ hx
  have hy_half : y' < (2^l) ^ (2^n / 2) := hK_half ▸ hy
  simp only [show ∀ j, (FPComplex.DFT_inv_canonical (fun i =>
      FPComplex.mul (FPComplex.DFT_canonical (fun j => FPComplex.ofInt (P := ssa1_required_precision n l) (↑(decompose (2^l) (2^n) x' j))) i)
                     (FPComplex.DFT_canonical (fun j => FPComplex.ofInt (P := ssa1_required_precision n l) (↑(decompose (2^l) (2^n) y' j))) i)) j).round_re =
      cyclic_convolution_benchmark
        (fun j => (↑(decompose (2^l) (2^n) x' j) : ℤ))
        (fun j => (↑(decompose (2^l) (2^n) y' j) : ℤ)) j from h_coeff]
  rw [show (fun j : Fin (2 ^ n) => cyclic_convolution_benchmark
        (fun j => (↑(decompose (2^l) (2^n) x' j) : ℤ))
        (fun j => (↑(decompose (2^l) (2^n) y' j) : ℤ)) j) =
    cyclic_convolution_benchmark
        (fun j => (↑(decompose (2^l) (2^n) x' j) : ℤ))
        (fun j => (↑(decompose (2^l) (2^n) y' j) : ℤ)) from rfl]
  rw [cyclic_conv_zero_padded_recompose (2^l) (2^n) (by positivity)
    (fun j => (↑(decompose (2^l) (2^n) x' j) : ℤ))
    (fun j => (↑(decompose (2^l) (2^n) y' j) : ℤ))
    (fun j hj => by simp [decompose_zero_upper_half (2^l) (2^n) x' (by positivity) (by positivity) hx_half j hj])
    (fun j hj => by simp [decompose_zero_upper_half (2^l) (2^n) y' (by positivity) (by positivity) hy_half j hj])]
  rw [decompose_recompose (2^l) (2^n) x' (by positivity) (by positivity),
      decompose_recompose (2^l) (2^n) y' (by positivity) (by positivity)]

theorem ssa1_multiply_correct (x y : ℤ) : ssa1_multiply x y = x * y := by
  induction x, y using ssa1_multiply.induct
  -- Recursive case
  next A_fp B_fp B_hat_ctx hxb_ctx hyb_ctx A_hat_ctx ih_rr ih_ii ih_ri ih_ir =>
    rename_i a b N hThresh x' y' n hl_ex l β K P
    rw [ssa1_multiply.eq_1]
    have hN_pos : ssa1_base_threshold < max (bits a) (bits b) := hThresh
    rw [dif_pos hN_pos]
    -- Unfold let/have bindings using zeta reduction, then rewrite IH
    simp +zetaDelta only [ih_rr, ih_ii, ih_ri, ih_ir]
    have h_contra : x' < (2 ^ l) ^ (2 ^ (n - 1)) := by
      have hbx'_lt : bits a ≤ l * 2 ^ (n - 1) := by
        have := Classical.choose_spec ( Classical.choose_spec ( exist_n_l ( max ( bits a ) ( bits b ) ) hN_pos ) );
        rcases n : Classical.choose ( exist_n_l ( max ( bits a ) ( bits b ) ) hN_pos ) with ( _ | n ) <;> simp_all +decide [ pow_succ' ];
        norm_num +zetaDelta at *;
        cases this.2.2 <;> simp_all +decide [ Nat.pow_succ' ];
        · grind;
        · grind +splitImp;
      exact lt_of_lt_of_le ( natAbs_lt_pow_bits a ) ( by rw [ ← pow_mul ] ; exact pow_le_pow_right₀ ( by decide ) hbx'_lt )
    have h_contra' : y' < (2 ^ l) ^ (2 ^ (n - 1)) := by
      have h_bits_y : bits b ≤ l * 2 ^ (n - 1) := by
        have := Classical.choose_spec hl_ex;
        rcases k : Classical.choose ( show ∃ n : ℕ, ∃ l : ℕ, l * 2 ^ n ≥ 2 * N ∧ n ≥ 1 ∧ l ≥ 1 ∧ 2 * ( 3 * n + 3 * l + 5 ) ≤ N from ⟨ _, _, hl_ex.choose_spec ⟩ ) with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
        norm_num [ n, l, ‹Classical.choose _ = _› ] at *;
        grind;
      have h_bits_y : b.natAbs < 2 ^ (l * 2 ^ (n - 1)) := by
        exact lt_of_lt_of_le ( natAbs_lt_pow_bits b ) ( Nat.pow_le_pow_right ( by decide ) h_bits_y );
      simpa only [ pow_mul ] using h_bits_y;
    have := Classical.choose_spec hl_ex;
    have := dft_pipeline_gives_product' ( show 1 ≤ n from this.2.1 ) ( show 1 ≤ l from this.2.2.1 ) x' y' h_contra h_contra';
    convert congr_arg ( fun x : ℤ => a.sign * b.sign * x ) this using 1;
    exact Eq.symm (sign_natAbs_mul a b)
  -- Base case
  next a b hN =>
    rw [ssa1_multiply.eq_1, dif_neg hN]
