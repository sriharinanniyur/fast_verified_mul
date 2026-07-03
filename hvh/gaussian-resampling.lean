-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-- with some contribution from Fable 5

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

noncomputable section

open Complex Real

namespace GaussianResampling

variable (s t : ℕ) (α : ℝ)

def S (u : ZMod s → ℂ) : ZMod t → ℂ := fun k =>
  (α⁻¹ : ℂ) * ∑' j : ℤ,
    (Real.exp (-π * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((k.val : ℝ) / t - (j : ℝ) / s) ^ 2) : ℂ)
      * u (j : ZMod s)

def T (u : ZMod s → ℂ) : ZMod t → ℂ := fun k =>
  ∑' j : ℤ,
    (Real.exp (-π * α ^ 2 * (t : ℝ) ^ 2 * ((k.val : ℝ) / t - (j : ℝ) / s) ^ 2) : ℂ)
      * u (j : ZMod s)

def Ps (u : ZMod s → ℂ) : ZMod s → ℂ := fun j => u ((t : ZMod s) * j)

def Pt (v : ZMod t → ℂ) : ZMod t → ℂ := fun k => v (-((s : ZMod t) * k))

def ZETA (N : ℕ) : ℂ := Complex.exp (2 * π * I / N)

def F (N : ℕ) [NeZero N] (u : ZMod N → ℂ) : ZMod N → ℂ := fun k =>
  (N : ℂ)⁻¹ * ∑ j : ZMod N, u j * ZETA N ^ (-(j.val * k.val : ℤ))

/-
A `zpow` of `ZETA N` is an exponential of a linear phase.
-/
lemma ZETA_zpow (N : ℕ) (m : ℤ) :
    ZETA N ^ m = Complex.exp (2 * (π : ℂ) * I * (m : ℂ) / (N : ℂ)) := by
  unfold GaussianResampling.ZETA; rw [ ← Complex.exp_int_mul ] ; ring;

/-
Two integer phases `exp (2πi X / N)` agree when `X ≡ Y (mod N)`.
-/
lemma exp_int_congr (N : ℕ) [NeZero N] (X Y : ℤ) (h : (X : ZMod N) = (Y : ZMod N)) :
    Complex.exp (2 * (π : ℂ) * I * (X : ℂ) / (N : ℂ))
      = Complex.exp (2 * (π : ℂ) * I * (Y : ℂ) / (N : ℂ)) := by
  convert Complex.exp_periodic.int_mul ( ( X - Y ) / N ) _ using 2;
  rw [ Int.cast_div ] <;> norm_num [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, h ] ; ring;
  exact NeZero.ne N

/-- The common intermediate expression `G` to which both sides of the resampling
identity reduce.  Here `k.val` is the canonical integer representative of `k`. -/
def Gterm (s t : ℕ) [NeZero s] (α : ℝ) (u : ZMod s → ℂ) (k : ZMod t) : ℂ :=
  (s : ℂ)⁻¹ * ∑ r : ZMod s, u r *
    ∑' j : ℤ,
      (Real.exp (-π * α ^ 2 * (t : ℝ) ^ 2 * ((k.val : ℝ) / t - (j : ℝ) / s) ^ 2) : ℂ)
        * Complex.exp (-2 * (π : ℂ) * I * (r.val : ℂ) * (t : ℂ) * (j : ℂ) / (s : ℂ))

/-! ### General analytic helper lemmas -/

/-
Gaussian Poisson summation (shifted form), derived from
`Complex.tsum_exp_neg_quadratic`.
-/
lemma poisson_gauss (A : ℝ) (hA : 0 < A) (c : ℝ) :
    ∑' p : ℤ, (Real.exp (-π * A * (c - (p : ℝ)) ^ 2) : ℂ)
      = (1 / Real.sqrt A : ℂ) * ∑' n : ℤ,
          (Real.exp (-π * (n : ℝ) ^ 2 / A) : ℂ)
            * Complex.exp (-2 * (π : ℂ) * I * (c : ℂ) * (n : ℂ)) := by
  have h_shift : (∑' p : ℤ, (Real.exp (-Real.pi * A * (c - p) ^ 2) : ℂ)) = (Complex.exp (-Real.pi * A * c ^ 2)) * (∑' p : ℤ, (Complex.exp (-Real.pi * A * p ^ 2 + 2 * Real.pi * A * c * p) : ℂ)) := by
    rw [ ← tsum_mul_left ] ; congr ; ext p ; norm_cast ; ring;
    rw [ ← Real.exp_add ] ; push_cast ; ring;
  convert congr_arg ( fun x : ℂ => ( Complex.exp ( -Real.pi * A * c ^ 2 ) : ℂ ) * x ) ( Complex.tsum_exp_neg_quadratic ( show 0 < ( A : ℂ ).re by simpa ) ( A * c ) ) using 1;
  · simpa only [ mul_assoc ] using h_shift;
  · norm_num [ ← Complex.exp_add, Complex.ofReal_exp, Real.sqrt_eq_rpow, Complex.ofReal_cpow hA.le ] ; ring;
    norm_num [ sq, mul_assoc, hA.ne' ] ; ring;
    rw [ ← tsum_mul_left ] ; congr ; ext n ; rw [ ← Complex.exp_add ] ; ring;

/-
Summability of a shifted Gaussian times a fixed exponential phase, over `ℤ`.
-/
lemma summable_gauss_phase (B c : ℝ) (hB : 0 < B) (w : ℂ) :
    Summable (fun n : ℤ =>
      (Real.exp (-π * B * ((n : ℝ) - c) ^ 2) : ℂ) * Complex.exp (w * (n : ℂ))) := by
  -- Choose τ := I*B (then τ.im = B > 0) and z := (2*π*B*c + w)/(2*π*I).
  set τ := Complex.I * B
  have hτ : τ.im > 0 := by
    aesop
  set z := (2 * Real.pi * B * c + w) / (2 * Real.pi * Complex.I)
  have hz : ∀ n : ℤ, Complex.exp (-Real.pi * B * (n - c) ^ 2) * Complex.exp (w * n) = Complex.exp (-Real.pi * B * c ^ 2) * jacobiTheta₂_term n z τ := by
    intro n; unfold jacobiTheta₂_term; rw [ ← Complex.exp_add ] ; ring;
    rw [ ← Complex.exp_add ] ; rw [ show z = ( 2 * Real.pi * B * c + w ) / ( 2 * Real.pi * Complex.I ) by rfl ] ; rw [ show τ = Complex.I * B by rfl ] ; ring_nf ; norm_num [ Complex.ext_iff, Real.pi_ne_zero ] ; ring;
    norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero ] ; ring_nf ; norm_num [ Complex.exp_re, Complex.exp_im ] ;
    norm_cast; norm_num [ sq, mul_assoc, mul_comm Real.pi _, Real.pi_ne_zero ] ;
  simp_all +decide [ Complex.exp_ne_zero ];
  exact Summable.mul_left _ <| summable_jacobiTheta₂_term_iff _ _ |>.mpr hτ

/-
A shifted Gaussian times a uniformly bounded sequence is summable over `ℤ`.
-/
lemma summable_gauss_bounded (B c : ℝ) (hB : 0 < B) (f : ℤ → ℂ) (M : ℝ)
    (hf : ∀ j : ℤ, ‖f j‖ ≤ M) :
    Summable (fun j : ℤ =>
      (Real.exp (-π * B * ((j : ℝ) - c) ^ 2) : ℂ) * f j) := by
  refine' .of_norm _;
  refine' .of_nonneg_of_le ( fun j => norm_nonneg _ ) ( fun j => _ ) ( Summable.mul_right M <| summable_gauss_phase B c hB 0 |> Summable.norm );
  norm_num [ hf ]

/-
Summability of the Poisson-side kernel appearing in `S_unfold`: a centered
Gaussian in `n` times a linear exponential phase.
-/
lemma summable_S_kernel (s : ℕ) [NeZero s] (α : ℝ) (hα : 0 < α) (w : ℂ) :
    Summable (fun n : ℤ =>
      (Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) * Complex.exp (w * (n : ℂ))) := by
  convert summable_gauss_phase ( α ^ 2 / s ^ 2 ) 0 ?_ w using 3 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_two ];
  exact mul_pos hα ( mul_pos hα ( mul_pos ( inv_pos.mpr ( Nat.cast_pos.mpr ( NeZero.pos s ) ) ) ( inv_pos.mpr ( Nat.cast_pos.mpr ( NeZero.pos s ) ) ) ) )

/-
Summability of the `T`-side summand: the Gaussian `exp(-πα²t²(k/t - j/s)²)` in
`j` times a linear exponential phase.
-/
lemma summable_T_summand (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) (hα : 0 < α)
    (k : ZMod t) (w : ℂ) :
    Summable (fun j : ℤ =>
      (Real.exp (-π * α ^ 2 * (t : ℝ) ^ 2 * ((k.val : ℝ) / t - (j : ℝ) / s) ^ 2) : ℂ)
        * Complex.exp (w * (j : ℂ))) := by
  convert summable_gauss_phase ( α ^ 2 * t ^ 2 / s ^ 2 ) ( ( s : ℝ ) * k.val / t ) ( by exact div_pos (
      by exact mul_pos ( sq_pos_of_pos hα ) ( sq_pos_of_pos ( Nat.cast_pos.mpr <| NeZero.pos t ) ) ) ( sq_pos_of_pos ( Nat.cast_pos.mpr <| NeZero.pos s ) ) ) w using 3 ; norm_num ; ring_nf;
  simp +decide [ sq, mul_assoc, NeZero.ne ]

/-
Splitting a `tsum` over `ℤ` according to residues mod `s`.
-/
lemma tsum_int_split (s : ℕ) [NeZero s] (F : ℤ → ℂ) (hF : Summable F) :
    ∑' j : ℤ, F j = ∑ r : ZMod s, ∑' p : ℤ, F ((s : ℤ) * p + (r.val : ℤ)) := by
  have h_equiv : Function.Bijective (fun p : ZMod s × ℤ => s * p.2 + p.1.val : ZMod s × ℤ → ℤ) := by
    constructor <;> intro p <;> simp_all +decide [ Function.Injective, Function.Surjective ];
    · intro a b h;
      have h_eq : p.1 = a := by
        replace h := congr_arg ( fun x : ℤ => x : ℤ → ZMod s ) h ; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
      aesop;
    · use p;
      use (p - (p : ZMod s).cast) / s;
      rw [ Int.mul_ediv_cancel' ] <;> norm_num [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
  have h_sum_eq : ∑' j : ℤ, F j = ∑' p : ZMod s × ℤ, F (s * p.2 + p.1.val) := by
    rw [ ← Equiv.tsum_eq ( Equiv.ofBijective _ h_equiv ) ] ; aesop;
  erw [ h_sum_eq, Summable.tsum_prod ];
  · exact tsum_fintype fun (b : ZMod s) => ∑' (c : ℤ), F ((↑s : ℤ) * (b, c).2 + (↑(b, c).1.val : ℤ))
  · exact hF.comp_injective h_equiv.injective

/-
Orthogonality of roots of unity, collapsing a `tsum` over `ℤ` against a full
DFT sum: only the arithmetic progression `n = t*m - d` survives.
-/
lemma orthog_tsum (t : ℕ) [NeZero t] (d : ℤ) (g : ℤ → ℂ)
    (hg : Summable g) :
    (∑' n : ℤ, g n * (t : ℂ)⁻¹ * ∑ a : ZMod t,
        Complex.exp (-2 * (π : ℂ) * I * (a.val : ℂ) * ((n : ℂ) + (d : ℂ)) / (t : ℂ)))
      = ∑' m : ℤ, g ((t : ℤ) * m - d) := by
  -- Let's simplify the inner sum.
  have h_inner : ∀ n : ℤ, (∑ a : ZMod t, Complex.exp (-2 * Real.pi * Complex.I * (a.val : ℂ) * ((n : ℂ) + d) / (t : ℂ))) = if (t : ℤ) ∣ (n + d) then (t : ℂ) else 0 := by
    intro n
    by_cases h_div : (t : ℤ) ∣ (n + d);
    · obtain ⟨ k, hk ⟩ := h_div; norm_cast; simp_all +decide [ ← mul_assoc, ← mul_add ] ;
      convert Finset.sum_const ( 1 : ℂ ) ; norm_num [ NeZero.ne, mul_assoc, mul_div_assoc ];
      · rw [ Complex.exp_eq_one_iff ] ; use -k * ‹ZMod t›.val ; ring_nf ; norm_num [ NeZero.ne ] ; ring;
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, NeZero.ne ];
      · norm_num [ Finset.card_univ ];
    · -- If $t$ does not divide $n + d$, then $\exp(-2 \pi i (n + d) / t)$ is a primitive $t$-th root of unity.
      have h_primitive : ∑ a ∈ Finset.range t, (Complex.exp (-2 * Real.pi * Complex.I * (n + d) / t)) ^ a = 0 := by
        rw [ geom_sum_eq ];
        · rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff.mpr ⟨ - ( n + d ), by push_cast; ring_nf; norm_num [ NeZero.ne ] ⟩ ] ; norm_num;
        · rw [ Ne.eq_def, Complex.exp_eq_one_iff ];
          contrapose! h_div;
          obtain ⟨ k, hk ⟩ := h_div; rw [ div_eq_iff ( NeZero.ne _ ) ] at hk; norm_num [ Complex.ext_iff ] at hk;
          exact ⟨ -k, by rw [ ← @Int.cast_inj ℝ ] ; push_cast; nlinarith [ Real.pi_pos ] ⟩;
      convert h_primitive using 1;
      · -- ∑ over `ZMod t` = geometric sum over `range t`, reindexing by `ZMod.val`
        refine Finset.sum_bij (fun (a : ZMod t) _ => a.val)
          (fun a _ => Finset.mem_range.mpr (ZMod.val_lt a))
          (fun a _ b _ hab => ZMod.val_injective t hab)
          (fun j hj => ⟨(j : ZMod t), Finset.mem_univ _,
            ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)⟩)
          (fun a _ => ?_)
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      · aesop;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, tsum_mul_left, tsum_mul_right ];
  rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
  use fun x => ( x.val + d ) / t;
  · intro x y; aesop;
  · intro x hx; use ⟨ x * t - d, by aesop ⟩ ; simp +decide [ NeZero.ne ] ;
  · simp +contextual [ Int.ediv_mul_cancel ]

/-! ### Unfolding lemmas -/

/-
Poisson-summation rewriting of `S u` at an index `a : ZMod t`.
-/
lemma S_unfold [NeZero s] [NeZero t] (α : ℝ) (hα : 0 < α) (u : ZMod s → ℂ) (a : ZMod t) :
    (S s t α u) a
      = (s : ℂ)⁻¹ * ∑ r : ZMod s, u r *
          ∑' n : ℤ, (Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ)
            * Complex.exp (-2 * (π : ℂ) * I * (n : ℂ) * (a.val : ℂ) / (t : ℂ))
            * Complex.exp (2 * (π : ℂ) * I * (n : ℂ) * (r.val : ℂ) / (s : ℂ)) := by
  -- Apply the lemma `tsum_int_split` to the function $G(j) = \exp(-\pi \alpha^{-2} s^2 (a.val / t - j / s)^2) u (j : ZMod s)$.
  have h_split : ∑' j : ℤ, (Real.exp (-Real.pi * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((a.val : ℝ) / t - (j : ℝ) / s) ^ 2) : ℂ) * u (j : ZMod s) =
    ∑ r : ZMod s, ∑' p : ℤ, (Real.exp (-Real.pi * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((a.val / t - (p * s + r.val) / s) ^ 2) : ℝ)) * u r := by
      have h_split : Summable (fun j : ℤ => (Real.exp (-Real.pi * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((a.val : ℝ) / t - (j : ℝ) / s) ^ 2) : ℂ) * u (j : ZMod s)) := by
        have h_summable : Summable (fun j : ℤ => (Real.exp (-Real.pi * α⁻¹ ^ 2 * ((s * a.val / t : ℝ) - (j : ℝ)) ^ 2) : ℂ) * u (j : ZMod s)) := by
          convert summable_gauss_bounded ( α⁻¹ ^ 2 ) ( s * a.val / t ) ( by positivity ) ( fun j => u ( j : ZMod s ) ) ( ∑ r : ZMod s, ‖u r‖ ) _ using 1;
          · exact funext fun x => by rw [ ← neg_sub, neg_sq ] ;
          · exact fun j => Finset.single_le_sum ( fun r _ => norm_nonneg ( u r ) ) ( Finset.mem_univ _ );
        convert h_summable using 3 ; ring;
        simp +decide [ sq, mul_assoc, mul_comm, mul_left_comm, NeZero.ne ];
      convert tsum_int_split s _ h_split using 1;
      simp +decide [ mul_comm, ZMod.natCast_self ];
  -- Apply the Poisson summation formula to the inner sum.
  have h_poisson : ∀ r : ZMod s, ∑' p : ℤ, (Real.exp (-Real.pi * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((a.val / t - (p * s + r.val) / s) ^ 2) : ℝ)) =
    (Real.sqrt ((α⁻¹ * s) ^ 2) : ℂ)⁻¹ * ∑' n : ℤ, (Real.exp (-Real.pi * (n : ℝ) ^ 2 / (α⁻¹ * s) ^ 2) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * (a.val / t - r.val / s) * n) := by
      intro r
      have := poisson_gauss (α⁻¹ ^ 2 * s ^ 2) (by
      exact mul_pos ( sq_pos_of_pos ( inv_pos.mpr hα ) ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( NeZero.pos s ) ) )) (a.val / t - r.val / s)
      simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm ];
      convert this using 1;
      · convert Complex.ofReal_tsum _ using 3 ; norm_num ; ring;
        grind;
      · norm_num [ ZMod.cast, ZMod.val ];
        cases t <;> cases s <;> norm_num at *;
  -- Combine the results from h_split and h_poisson.
  have h_combined : ∑' j : ℤ, (Real.exp (-Real.pi * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((a.val : ℝ) / t - (j : ℝ) / s) ^ 2) : ℂ) * u (j : ZMod s) =
    (Real.sqrt ((α⁻¹ * s) ^ 2) : ℂ)⁻¹ * ∑ r : ZMod s, u r * ∑' n : ℤ, (Real.exp (-Real.pi * (n : ℝ) ^ 2 / (α⁻¹ * s) ^ 2) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * (a.val / t - r.val / s) * n) := by
      rw [ h_split, Finset.mul_sum _ _ _ ];
      refine' Finset.sum_congr rfl fun r hr => _;
      convert congr_arg ( · * u r ) ( h_poisson r ) using 1;
      · rw [ Complex.ofReal_tsum ] ; norm_num [ tsum_mul_right ];
      · ring;
  convert congr_arg ( fun x : ℂ => α⁻¹ * x ) h_combined using 1;
  · unfold GaussianResampling.S; norm_num;
  · rw [ Real.sqrt_sq ( by positivity ) ] ; norm_num [ hα.ne', mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, tsum_mul_left, tsum_mul_right ] ;
    norm_num [ ← mul_assoc, ← Complex.exp_add ] ; ring_nf ; norm_num;
    exact Or.inl <| Finset.sum_congr rfl fun _ _ => by congr; ext; ring;

/-
Unfolding the DFT/permutation on the left-hand side.
-/
lemma lhs_unfold [NeZero s] [NeZero t] (α : ℝ) (u : ZMod s → ℂ) (k : ZMod t) :
    (Pt s t (F t (S s t α u))) k
      = (t : ℂ)⁻¹ * ∑ a : ZMod t, (S s t α u) a *
          Complex.exp (2 * (π : ℂ) * I * (a.val : ℂ) * (s : ℂ) * (k.val : ℂ) / (t : ℂ)) := by
  -- Let's simplify the expression by factoring out common terms and using the properties of exponents.
  simp [GaussianResampling.Pt, GaussianResampling.F, GaussianResampling.ZETA];
  left;
  refine' Finset.sum_congr rfl fun x _ => congr_arg _ _;
  rw [ ← Complex.exp_int_mul, ← Complex.exp_neg ] ; ring;
  rw [ Complex.exp_eq_exp_iff_exists_int ];
  use -((x.cast * (-((s : ZMod t) * k)).cast + x.cast * s * k.cast) / t : ℤ);
  rw [ Int.cast_neg, Int.cast_div ] <;> norm_num ; ring;
  · simp +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, mul_assoc ];
  · exact NeZero.ne t

/-
Unfolding the DFT/permutation `Pₛ Fₛ` on the right-hand side, evaluated at an
integer index.
-/
lemma psfs_unfold [NeZero s] (u : ZMod s → ℂ) (j : ℤ) :
    (Ps s t (F s u)) (j : ZMod s)
      = (s : ℂ)⁻¹ * ∑ r : ZMod s, u r *
          Complex.exp (-2 * (π : ℂ) * I * (r.val : ℂ) * (t : ℂ) * (j : ℂ) / (s : ℂ)) := by
  unfold GaussianResampling.Ps GaussianResampling.F;
  simp +decide only [ZETA_zpow, neg_mul];
  refine' congrArg _ ( Finset.sum_congr rfl fun x hx => _ );
  refine' congrArg _ ( Complex.exp_eq_exp_iff_exists_int.mpr _ );
  use (x.val * (t * j - ((t : ZMod s) * (j : ZMod s)).val)) / s;
  rw [ Int.cast_div ] <;> norm_num ; ring;
  · simp +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
  · exact NeZero.ne s

/-! ### The two sides reduce to `Gterm` -/

lemma lhs_eq_G [NeZero s] [NeZero t] (α : ℝ) (hα : 0 < α) (u : ZMod s → ℂ) (k : ZMod t) :
    (Pt s t (F t (S s t α u))) k = Gterm s t α u k := by
  -- Apply the lemma `lhs_unfold` to rewrite the left-hand side.
  rw [lhs_unfold];
  -- Apply the lemma `S_unfold` to rewrite the sum.
  have h_sum : ∑ a : ZMod t, (S s t α u) a * Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) * (s : ℂ) * (k.val : ℂ) / (t : ℂ)) =
    (s : ℂ)⁻¹ * ∑ r : ZMod s, u r *
      ∑' n : ℤ, (Real.exp (-Real.pi * α ^ 2 * (n : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (r.val : ℂ) / (s : ℂ))
        * ∑ a : ZMod t, Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) * (s : ℂ) * (k.val : ℂ) / (t : ℂ) - 2 * Real.pi * Complex.I * (n : ℂ) * (a.val : ℂ) / (t : ℂ)) := by
          have h_sum : ∀ a : ZMod t, (S s t α u) a * Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) * (s : ℂ) * (k.val : ℂ) / (t : ℂ)) =
            (s : ℂ)⁻¹ * ∑ r : ZMod s, u r *
              ∑' n : ℤ, (Real.exp (-Real.pi * α ^ 2 * (n : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ)
                * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (r.val : ℂ) / (s : ℂ))
                * Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) * (s : ℂ) * (k.val : ℂ) / (t : ℂ) - 2 * Real.pi * Complex.I * (n : ℂ) * (a.val : ℂ) / (t : ℂ)) := by
                  intro a
                  rw [S_unfold s t α hα u a];
                  simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ← tsum_mul_left, ← Complex.exp_add ];
                  exact Or.inl ( by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ ← tsum_mul_left ] ; exact tsum_congr fun _ => by rw [ mul_left_comm, ← Complex.exp_add ] ; ring );
          simp +decide only [h_sum, Finset.mul_sum _ _ _];
          rw [ Finset.sum_comm ];
          refine' Finset.sum_congr rfl fun _ _ => _;
          rw [ ← Finset.mul_sum _ _ _, ← Finset.mul_sum _ _ _ ];
          congr! 2;
          have h_summable : ∀ i : ZMod t, Summable (fun n : ℤ => (Real.exp (-Real.pi * α ^ 2 * (n : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (↑‹ZMod s›.val : ℂ) / (s : ℂ))
              * Complex.exp (2 * Real.pi * Complex.I * (i.val : ℂ) * (s : ℂ) * (k.val : ℂ) / (t : ℂ) - 2 * Real.pi * Complex.I * (n : ℂ) * (i.val : ℂ) / (t : ℂ))) := by
            intro i;
            have := summable_S_kernel s α hα ( 2 * Real.pi * Complex.I * ( ↑‹ZMod s›.val : ℂ ) / ( s : ℂ ) - 2 * Real.pi * Complex.I * ( i.val : ℂ ) / ( t : ℂ ) );
            convert this.mul_right ( Complex.exp ( 2 * Real.pi * Complex.I * ( i.val : ℂ ) * ( s : ℂ ) * ( k.val : ℂ ) / ( t : ℂ ) ) ) using 2 ; ring;
            simpa only [ sub_eq_add_neg, Complex.exp_add ] using by ring;
          exact Eq.symm (Summable.tsum_finsetSum fun (i : ZMod t) (_ : i ∈ Finset.univ) => h_summable i)
  -- Apply the orthogonality result to simplify the inner sum.
  have h_inner : ∀ r : ZMod s, ∑' n : ℤ, (Real.exp (-Real.pi * α ^ 2 * (n : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ)
      * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (r.val : ℂ) / (s : ℂ))
      * ∑ a : ZMod t, Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) * (s : ℂ) * (k.val : ℂ) / (t : ℂ) - 2 * Real.pi * Complex.I * (n : ℂ) * (a.val : ℂ) / (t : ℂ)) =
    t * ∑' m : ℤ, (Real.exp (-Real.pi * α ^ 2 * ((t : ℝ) * m + (s : ℝ) * k.val) ^ 2 / (s : ℝ) ^ 2) : ℂ)
      * Complex.exp (2 * Real.pi * Complex.I * ((t : ℂ) * m + (s : ℂ) * k.val) * (r.val : ℂ) / (s : ℂ)) := by
        intro r
        have h_inner : ∑' n : ℤ, (Real.exp (-Real.pi * α ^ 2 * (n : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ)
            * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (r.val : ℂ) / (s : ℂ))
            * (t : ℂ)⁻¹ * ∑ a : ZMod t, Complex.exp (-2 * Real.pi * Complex.I * (a.val : ℂ) * ((n : ℂ) + (-(s : ℤ) * (k.val : ℤ))) / (t : ℂ)) =
          ∑' m : ℤ, (Real.exp (-Real.pi * α ^ 2 * ((t : ℝ) * m + (s : ℝ) * k.val) ^ 2 / (s : ℝ) ^ 2) : ℂ)
            * Complex.exp (2 * Real.pi * Complex.I * ((t : ℂ) * m + (s : ℂ) * k.val) * (r.val : ℂ) / (s : ℂ)) := by
              convert orthog_tsum t ( - ( s * k.val ) ) ( fun n : ℤ => ( Real.exp ( -Real.pi * α ^ 2 * ( n : ℝ ) ^ 2 / ( s : ℝ ) ^ 2 ) : ℂ ) * Complex.exp ( 2 * Real.pi * Complex.I * ( n : ℂ ) * ( r.val : ℂ ) / ( s : ℂ ) ) ) _ using 1;
              · grind +locals;
              · norm_num;
              · convert summable_S_kernel s α hα ( 2 * Real.pi * Complex.I * ( r.val : ℂ ) / ( s : ℂ ) ) using 2 ; ring;
        convert congr_arg ( fun x : ℂ => t * x ) h_inner using 1;
        rw [ ← tsum_mul_left ] ; congr ; ext n ; ring;
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, NeZero.ne ];
  simp_all +decide [ GaussianResampling.Gterm ];
  simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left, NeZero.ne ];
  rw [ inv_mul_eq_div, Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; ring;
  rw [ mul_right_comm ] ; norm_num [ NeZero.ne ] ; ring;
  left; rw [ ← Equiv.tsum_eq ( Equiv.neg ( ℤ ) ) ] ; norm_num ; congr ; ext ; ring;
  norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, NeZero.ne ] ; ring;
  convert Complex.exp_periodic.int_mul ( x.val * k.val ) _ using 2 ; push_cast ; ring;
  cases s <;> cases t <;> aesop

lemma rhs_eq_G [NeZero s] [NeZero t] (α : ℝ) (hα : 0 < α) (u : ZMod s → ℂ) (k : ZMod t) :
    (T s t α (Ps s t (F s u))) k = Gterm s t α u k := by
  unfold GaussianResampling.T GaussianResampling.Gterm;
  rw [ tsum_congr fun j => ?_ ];
  rotate_left;
  use fun j => ( s : ℂ ) ⁻¹ * ∑ r : ZMod s, u r * Complex.exp ( -2 * Real.pi * Complex.I * r.val * t * j / s ) * Real.exp ( -Real.pi * α ^ 2 * t ^ 2 * ( k.val / t - j / s ) ^ 2 );
  · rw [ psfs_unfold ];
    simp +decide only [mul_assoc, mul_comm, Finset.mul_sum _ _ _];
  · simp +decide only [mul_comm, ← tsum_mul_left];
    simp +decide only [mul_assoc];
    have h_summable : ∀ r : ZMod s, Summable (fun j : ℤ => u r * (Complex.exp ((j : ℂ) * ((t : ℂ) * (Complex.I * ((Real.pi : ℂ) * (-2 * (r.val : ℂ))))) / (s : ℂ)) * (Real.exp (-Real.pi * (α ^ 2 * ((t : ℝ) ^ 2 * ((k.val : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ)) ^ 2))))) ) := by
      intro r
      have h_summable : Summable (fun j : ℤ => (Real.exp (-Real.pi * (α ^ 2 * ((t : ℝ) ^ 2 * ((k.val : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ)) ^ 2)))) * Complex.exp ((j : ℂ) * ((t : ℂ) * (Complex.I * ((Real.pi : ℂ) * (-2 * (r.val : ℂ))))) / (s : ℂ))) := by
        convert summable_T_summand s t α hα k ( ( t : ℂ ) * ( Complex.I * ( Real.pi * ( -2 * r.val ) ) ) / s ) using 2 ; ring;
      convert h_summable.mul_left ( u r ) using 2 ; ring;
    have h_summable : Summable (fun j : ℤ => ∑ r : ZMod s, u r * (Complex.exp ((j : ℂ) * ((t : ℂ) * (Complex.I * ((Real.pi : ℂ) * (-2 * (r.val : ℂ))))) / (s : ℂ)) * (Real.exp (-Real.pi * (α ^ 2 * ((t : ℝ) ^ 2 * ((k.val : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ)) ^ 2))))) ) := by
      exact summable_sum fun r _ => h_summable r;
    convert ( Summable.tsum_mul_left _ h_summable ) using 1;
    refine congrArg _ (Eq.symm ?_)
    expose_names
    exact Summable.tsum_finsetSum fun (i : ZMod s) (_ : i ∈ Finset.univ) => h_summable_1 i

theorem resampling_identity [NeZero s] [NeZero t]
    (h_alpha : 0 < α)
    (hcop : Nat.Coprime s t)
    (hst : s < t)
    (u : ZMod s → ℂ) (k : ZMod t) :
    (Pt s t (F t (S s t α u))) k = (T s t α (Ps s t (F s u))) k := by
  rw [lhs_eq_G s t α h_alpha u k, rhs_eq_G s t α h_alpha u k]

end GaussianResampling
