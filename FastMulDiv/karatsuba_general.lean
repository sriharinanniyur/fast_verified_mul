import Mathlib
set_option maxHeartbeats 800000
/-! # Karatsuba multiplication algorithm
We define the Karatsuba multiplication algorithm and prove it correct.
-/
/-
b^(n/2) ≤ M when M has n ≥ 2 digits in base b
-/
lemma pow_half_digits_le (b : ℕ) (hb : 1 < b) (M : ℕ)
    (hn : ¬ (Nat.digits b M).length ≤ 1) :
    b ^ ((Nat.digits b M).length / 2) ≤ M := by
  have := @Nat.digits_len b M;
  by_cases hM : M = 0;
  · aesop;
  · exact Nat.pow_le_of_le_log ( by positivity ) ( by omega )
/-
Component bound for mod: (a % (m : ℤ)).natAbs < M when m ≤ M and m > 0
-/
lemma emod_natAbs_lt_of_le (a : ℤ) (m M : ℕ) (hm : 0 < m) (hle : m ≤ M) :
    (a % (m : ℤ)).natAbs < M := by
  cases abs_cases ( a % m ) <;> linarith [ Int.emod_lt_of_pos a ( by positivity : ( m : ℤ ) > 0 ), Int.emod_nonneg a ( by positivity : ( m : ℤ ) ≠ 0 ) ]
/-
Component bound for div: (a / (m : ℤ)).natAbs < M when m ≥ 2 and a.natAbs ≤ M and m ≤ M
-/
lemma ediv_natAbs_lt_of_le (a : ℤ) (m M : ℕ) (hm : 2 ≤ m) (hle : m ≤ M)
    (ha : a.natAbs ≤ M) : (a / (m : ℤ)).natAbs < M := by
  cases abs_cases ( a / m ) <;> cases abs_cases a <;> nlinarith [ Int.mul_ediv_add_emod a m, Int.emod_nonneg a ( by positivity : ( m : ℤ ) ≠ 0 ), Int.emod_lt_of_pos a ( by positivity : ( m : ℤ ) > 0 ) ]
/-
Component bound for div + mod
-/
lemma ediv_add_emod_natAbs_lt_of_le (a : ℤ) (m M : ℕ) (hm : 2 ≤ m) (hle : m ≤ M)
    (ha : a.natAbs ≤ M) : (a / (m : ℤ) + a % (m : ℤ)).natAbs < M := by
  cases abs_cases a <;> cases abs_cases ( a / m + a % m ) <;> nlinarith [ Int.emod_add_mul_ediv a m, Int.emod_nonneg a ( by linarith : ( m : ℤ ) ≠ 0 ), Int.emod_lt_of_pos a ( by linarith : ( m : ℤ ) > 0 ) ]
/-
Helper: b^k ≥ 2 when b ≥ 2 and k ≥ 1
-/
lemma pow_ge_two (b k : ℕ) (hb : 1 < b) (hk : 1 ≤ k) : 2 ≤ b ^ k := by
  exact le_trans hb ( Nat.le_self_pow ( by positivity ) _ )
-- Termination helper combining all bounds for the mod case
lemma karatsuba_term_mod' (b : ℕ) (hb : 1 < b) (x y : ℤ) (M : ℕ)
    (_hM : M = max x.natAbs y.natAbs)
    (hn : ¬ (Nat.digits b M).length ≤ 1) :
    (x % ↑(b ^ ((Nat.digits b M).length / 2))).natAbs < M ∧
    (y % ↑(b ^ ((Nat.digits b M).length / 2))).natAbs < M := by
  have hpow := pow_half_digits_le b hb M hn
  exact ⟨emod_natAbs_lt_of_le x _ M (by positivity) hpow,
         emod_natAbs_lt_of_le y _ M (by positivity) hpow⟩
lemma karatsuba_term_div' (b : ℕ) (hb : 1 < b) (x y : ℤ) (M : ℕ)
    (hM : M = max x.natAbs y.natAbs)
    (hn : ¬ (Nat.digits b M).length ≤ 1) :
    (x / ↑(b ^ ((Nat.digits b M).length / 2))).natAbs < M ∧
    (y / ↑(b ^ ((Nat.digits b M).length / 2))).natAbs < M := by
  have hpow := pow_half_digits_le b hb M hn
  have hm2 := pow_ge_two b _ hb (show 1 ≤ (Nat.digits b M).length / 2 by omega)
  exact ⟨ediv_natAbs_lt_of_le x _ M hm2 hpow (hM ▸ le_max_left ..),
         ediv_natAbs_lt_of_le y _ M hm2 hpow (hM ▸ le_max_right ..)⟩
lemma karatsuba_term_add' (b : ℕ) (hb : 1 < b) (x y : ℤ) (M : ℕ)
    (hM : M = max x.natAbs y.natAbs)
    (hn : ¬ (Nat.digits b M).length ≤ 1) :
    (x / ↑(b ^ ((Nat.digits b M).length / 2)) +
     x % ↑(b ^ ((Nat.digits b M).length / 2))).natAbs < M ∧
    (y / ↑(b ^ ((Nat.digits b M).length / 2)) +
     y % ↑(b ^ ((Nat.digits b M).length / 2))).natAbs < M := by
  have hpow := pow_half_digits_le b hb M hn
  have hm2 := pow_ge_two b _ hb (show 1 ≤ (Nat.digits b M).length / 2 by omega)
  exact ⟨ediv_add_emod_natAbs_lt_of_le x _ M hm2 hpow (hM ▸ le_max_left ..),
         ediv_add_emod_natAbs_lt_of_le y _ M hm2 hpow (hM ▸ le_max_right ..)⟩

def karatsuba (b : ℕ) (hb : 1 < b) (x y : ℤ) : ℤ :=
  let n := (b.digits (max x.natAbs y.natAbs)).length
  if n ≤ 1 then x * y
  else
    let k := n / 2
    let b' := b ^ k
    let x1 := x / b'
    let x0 := x % b'
    let y1 := y / b'
    let y0 := y % b'
    let z1 := karatsuba b hb x1 y1
    let z0 := karatsuba b hb x0 y0
    let z2 := karatsuba b hb (x0 + x1) (y0 + y1)
    z1 * (b' ^ 2) + (z2 - z1 - z0) * b' + z0
termination_by (max x.natAbs y.natAbs)
decreasing_by
  all_goals simp_wf
  all_goals rename_i hn
  all_goals simp only [← Nat.cast_pow]
  · obtain ⟨h1, h2⟩ := karatsuba_term_div' b hb x y _ rfl hn; omega
  · obtain ⟨h1, h2⟩ := karatsuba_term_mod' b hb x y _ rfl hn; omega
  · obtain ⟨h1, h2⟩ := karatsuba_term_add' b hb x y _ rfl hn; omega


theorem karatsuba_correct (b : ℕ) (hb : 1 < b) (x y : ℤ)
    : karatsuba b hb x y = x * y := by
  induction' n : max x.natAbs y.natAbs using Nat.strong_induction_on with n ih generalizing x y;
  have h_ind : ∀ (x y : ℤ), max x.natAbs y.natAbs < ‹ℕ› → karatsuba b hb x y = x * y := by
    exact fun x y h => ih _ h _ _ rfl;
  unfold karatsuba;
  have := karatsuba_term_div' b hb x y ( max x.natAbs y.natAbs ) rfl; have := karatsuba_term_mod' b hb x y ( max x.natAbs y.natAbs ) rfl; have := karatsuba_term_add' b hb x y ( max x.natAbs y.natAbs ) rfl; simp_all +decide [ Int.emod_def ] ;
  grind
