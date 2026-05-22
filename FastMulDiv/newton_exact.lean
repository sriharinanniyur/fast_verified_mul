-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

import Mathlib

set_option maxHeartbeats 800000

def nr_div_exact (A B : ℕ) (n : ℕ) : ℕ := Id.run do
  let twoN : ℤ := 1 <<< n
  let mut C : ℕ := 1
  for i in [1:Nat.clog 2 n].toList.reverse do
    let twoK : ℤ := 1 <<< ((n + (1 <<< i) - 1) >>> i)
    C := (((C : ℤ) + C * (1 - B * C)) % twoK).toNat
  let mut Q : ℕ := A * C % (1 <<< ((n + 1) >>> 1))
  Q := (((Q : ℤ) + C * ((A : ℤ) - B * Q)) % twoN).toNat
  return Q


/-! ## Pure functional equivalent -/
def invStep (B n i C : ℕ) : ℕ :=
  (((C : ℤ) + C * (1 - ↑B * ↑C)) % ((1 : ℤ) <<< ((n + (1 <<< i) - 1) >>> i))).toNat

def invResult (B n : ℕ) : ℕ :=
  ([1:Nat.clog 2 n].toList.reverse).foldl (fun C i => invStep B n i C) 1

theorem forIn_to_foldl (B n : ℕ) (l : List ℕ) (init : ℕ) :
    (forIn (m := Id) l init fun i r =>
      (Bind.bind (Pure.pure PUnit.unit : Id PUnit) (fun _ =>
        (Pure.pure (ForInStep.yield (invStep B n i r)) : Id (ForInStep ℕ))))) =
    l.foldl (fun r i => invStep B n i r) init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    show forIn' (m := Id) (hd :: tl) init _ = _
    rw [List.forIn'_cons]
    exact ih (invStep B n hd init)
/-
Unfold nr_div_exact to pure form
-/
theorem nr_div_exact_unfold (A B n : ℕ) :
    nr_div_exact A B n =
    let C := invResult B n
    let Q := A * C % (1 <<< ((n + 1) >>> 1))
    (((Q : ℤ) + ↑C * (↑A - ↑B * ↑Q)) % ((1 : ℤ) <<< n)).toNat := by
  unfold nr_div_exact; simp +decide ;
  unfold invResult; simp +decide ;
  congr
/-! ## Precision function -/
def precAt (n i : ℕ) : ℕ := (n + (1 <<< i) - 1) >>> i
theorem precAt_eq (n i : ℕ) : precAt n i = (n + 2 ^ i - 1) / 2 ^ i := by
  simp [precAt, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
/-! ## Core mathematical lemmas -/
/-
Newton step: B*C ≡ 1 mod 2^k → B*(C+C*(1-B*C)) ≡ 1 mod 2^(2k)
-/
theorem newton_inv_step (B C : ℤ) (k : ℕ) (h : B * C ≡ 1 [ZMOD (2 ^ k)]) :
    B * (C + C * (1 - B * C)) ≡ 1 [ZMOD (2 ^ (2 * k))] := by
  -- By definition of $C_k$, we have $B * C_k ≡ 1 \pmod{2^k}$.
  obtain ⟨e, he⟩ : ∃ e : ℤ, B * C = 1 + e * 2^k := by
    exact h.symm.dvd.imp fun e he => by linarith;
  rw [ he ] ; ring_nf;
  rw [ he ] ; ring_nf; norm_num [ Int.ModEq ] ;
/-
toNat of (x % 2^m) cast back to ℤ is congruent to x mod 2^m
-/
theorem toNat_emod_congr (x : ℤ) (m : ℕ) :
    ((x % (2 ^ m : ℤ)).toNat : ℤ) ≡ x [ZMOD (2 ^ m)] := by
  rw [ Int.toNat_of_nonneg ( Int.emod_nonneg _ ( by positivity ) ), Int.ModEq, Int.emod_emod ]
/-
Combined: if B*C ≡ 1 mod 2^p and p' ≤ 2p, then
B * toNat((C + C*(1-B*C)) % 2^p') ≡ 1 mod 2^p'
-/
theorem newton_step_combined (B C : ℕ) (p p' : ℕ)
    (hp' : 0 < p') (hpp : p' ≤ 2 * p)
    (hBC : (↑B : ℤ) * ↑C ≡ 1 [ZMOD (2 ^ p)]) :
    (↑B : ℤ) * ↑((((C : ℤ) + ↑C * (1 - ↑B * ↑C)) % (2 ^ p' : ℤ)).toNat)
      ≡ 1 [ZMOD (2 ^ p')] := by
  -- By newton_inv_step, B*(C + C*(1-B*C)) ≡ 1 mod 2^(2p).
  have h_mod : B * (C + C * (1 - B * C)) ≡ 1 [ZMOD 2 ^ (2 * p)] := by
    exact newton_inv_step (↑B) (↑C) p hBC;
  rw [ Int.toNat_of_nonneg ( Int.emod_nonneg _ ( by positivity ) ) ];
  simpa [ Int.ModEq, Int.mul_emod ] using h_mod.of_dvd <| pow_dvd_pow _ hpp
/-! ## Precision sequence properties -/
theorem precAt_doubling (n i : ℕ) : precAt n i ≤ 2 * precAt n (i + 1) := by
  unfold precAt;
  simp +decide [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ] at *;
  rcases n with ( _ | n ) <;> simp +arith +decide [ Nat.pow_succ', Nat.mul_succ ];
  · rw [ Nat.div_eq_of_lt ] <;> norm_num;
  · exact Nat.le_of_lt_succ ( by nlinarith [ Nat.div_mul_le_self n ( 2 ^ i ), Nat.div_add_mod n ( 2 * 2 ^ i ), Nat.mod_lt n ( by positivity : 0 < ( 2 * 2 ^ i ) ), pow_pos ( by decide : 0 < 2 ) i, pow_succ' 2 i ] )
theorem precAt_one (n : ℕ) : precAt n 1 = (n + 1) / 2 := by
  rfl
theorem nat_shiftLeft_one (k : ℕ) : (1 : ℕ) <<< k = 2 ^ k := by
  simp [Nat.shiftLeft_eq]
theorem nat_shr_one (n : ℕ) : (n + 1) >>> 1 = (n + 1) / 2 := by
  simp [Nat.shiftRight_eq_div_pow]
theorem n_le_two_ceil_half (n : ℕ) : n ≤ 2 * ((n + 1) / 2) := by
  omega
theorem precAt_first_le_two (n : ℕ) (hn : 2 ≤ Nat.clog 2 n) :
    precAt n (Nat.clog 2 n - 1) ≤ 2 := by
  have h_ceil : n ≤ 2 ^ (Nat.clog 2 n) := by
    exact Nat.le_pow_clog ( by decide ) _;
  unfold precAt; rcases k : Nat.clog 2 n with ( _ | _ | k ) <;> simp_all +decide [ Nat.pow_succ', Nat.shiftRight_eq_div_pow ] ;
  norm_num [ Nat.shiftLeft_eq ] at *;
  exact Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by rw [ tsub_lt_iff_left ] <;> ring_nf at * <;> linarith [ Nat.one_le_pow ‹_› 2 zero_lt_two ] )
theorem precAt_pos (n i : ℕ) (hn : 0 < n) : 0 < precAt n i := by
  unfold precAt;
  simp_all +decide [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ];
  omega
/-! ## Loop correctness -/
def invFoldDown (B n : ℕ) : ℕ → ℕ → ℕ
  | 0, C => C
  | k + 1, C => invFoldDown B n k (invStep B n (k + 1) C)
theorem invResult_eq (B n : ℕ) :
    invResult B n = invFoldDown B n (Nat.clog 2 n - 1) 1 := by
  have h_fold : ∀ {k : ℕ} {l : List ℕ} {C : ℕ}, l = List.reverse (List.range' 1 k) → List.foldl (fun C i => invStep B n i C) C l = invFoldDown B n k C := by
    intros k l C hl; subst hl; induction' k with k ih generalizing C <;> simp_all +decide [ List.range'_concat ] ;
    · rfl;
    · grind +locals;
  convert h_fold _;
  grind
/-
Main loop invariant
-/
theorem invFoldDown_correct (B n : ℕ) (hB : B % 2 = 1) (hn : 0 < n) :
    ∀ (k C p : ℕ),
    0 < p →
    (↑B : ℤ) * ↑C ≡ 1 [ZMOD (2 ^ p)] →
    (k = 0 → p ≥ precAt n 1) →
    (0 < k → precAt n k ≤ 2 * p) →
    (↑B : ℤ) * ↑(invFoldDown B n k C) ≡ 1 [ZMOD (2 ^ precAt n 1)] := by
  intro k C p hp hBC hk hk';
  induction' k with k ih generalizing C p <;> simp_all +decide [ invFoldDown ];
  · exact hBC.of_dvd <| pow_dvd_pow _ hk;
  · apply ih;
    exact precAt_pos n ( k + 1 ) hn;
    · convert newton_step_combined B C p ( precAt n ( k + 1 ) ) ( precAt_pos n ( k + 1 ) hn ) hk' hBC using 1;
      unfold invStep; norm_cast;
      unfold precAt; norm_num [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ] ;
    · aesop;
    · exact fun _ => precAt_doubling n k
theorem invResult_correct (B n : ℕ) (hB : B % 2 = 1) (hn : 0 < n) :
    (↑B : ℤ) * ↑(invResult B n) ≡ 1 [ZMOD (2 ^ precAt n 1)] := by
  convert invFoldDown_correct B n hB hn ( Nat.clog 2 n - 1 ) 1 1 ( by norm_num ) _ _ _ using 1;
  · rw [ invResult_eq ];
  · norm_num [ Int.ModEq, Int.mul_emod, show ( B : ℤ ) % 2 = 1 from mod_cast hB ];
  · rcases n with ( _ | _ | _ | _ | _ | _ | _ | n ) <;> simp +arith +decide [ Nat.clog_of_two_le ] at *;
    exact fun h => absurd h ( Nat.ne_of_gt ( Nat.clog_pos ( by norm_num ) ( by omega ) ) );
  · exact fun h => precAt_first_le_two n ( Nat.le_of_not_lt fun h' => by omega )
/-! ## Final step -/
theorem final_step (A B C n : ℕ) (hn : 0 < n)
    (hBC : (↑B : ℤ) * ↑C ≡ 1 [ZMOD (2 ^ ((n + 1) / 2))]) :
    let k := (n + 1) / 2
    let Q := A * C % 2 ^ k
    (↑B : ℤ) * ↑(((↑Q + ↑C * (↑A - ↑B * ↑Q)) % (2 ^ n : ℤ)).toNat) ≡
      ↑A [ZMOD (2 ^ n)] := by
  -- Let $k = (n+1)/2$ and $Q = A*C \mod 2^k$.
  set k := (n + 1) / 2
  set Q := A * C % 2 ^ k;
  -- From step 2, $B*Q \equiv A \pmod{2^k}$, so $A - B*Q \equiv 0 \pmod{2^k}$.
  have h_diff : (A - B * Q : ℤ) ≡ 0 [ZMOD 2 ^ k] := by
    simp_all +decide [ Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero ];
    rw [ show ( Q : ℤ ) = A * C % 2 ^ k from rfl ] ; rw [ Int.emod_def ] ; ring_nf at *;
    convert dvd_add ( dvd_neg.mpr ( hBC.mul_left A ) ) ( dvd_mul_left ( 2 ^ k : ℤ ) ( B * ( A * C / 2 ^ k ) ) ) using 1 ; ring;
  -- Since $e = B*C - 1$ and $A - B*Q$ are both divisible by $2^k$, their product $e*(A - B*Q)$ is divisible by $2^{2k}$. Given $n \leq 2k$, $2^n$ divides $e*(A - B*Q)$.
  have h_prod_div : (B * C - 1 : ℤ) * (A - B * Q) ≡ 0 [ZMOD 2 ^ n] := by
    have h_prod_div : (B * C - 1 : ℤ) * (A - B * Q) ≡ 0 [ZMOD 2 ^ (2 * k)] := by
      rw [ Int.modEq_zero_iff_dvd ] at *;
      simpa only [ two_mul, pow_add ] using mul_dvd_mul ( hBC.symm.dvd ) h_diff;
    exact h_prod_div.of_dvd <| pow_dvd_pow _ <| by omega;
  simp_all +decide [ Int.ModEq ];
  rw [ max_eq_left ( Int.emod_nonneg _ <| by positivity ) ];
  simp +decide [ ← ZMod.intCast_eq_intCast_iff', Int.add_emod, Int.sub_emod, Int.mul_emod ];
  simp_all +decide [ ← Int.mul_emod, ← Int.sub_emod ];
  rw [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] ; ring_nf at * ; aesop
/-! ## Main theorem -/


theorem nr_div_exact_spec (A B : ℕ) (n : ℕ) (hB : B % 2 = 1) (hn : 0 < n) :
    (B * nr_div_exact A B n) % 2 ^ n = A % 2 ^ n := by
  -- Step 1: Unfold to pure form
  -- nr_div_exact A B n = let C := invResult B n; let Q := A*C % 2^k; ((Q + C*(A - B*Q)) % 2^n).toNat
  -- where k = (n+1)/2
  -- Step 2: invResult gives B^(-1) mod 2^k
  -- Step 3: Final Newton step gives B * result ≡ A mod 2^n
  convert Int.ModEq.of_dvd ( dvd_refl ( 2 ^ n : ℤ ) ) ( final_step A B ( invResult B n ) n hn ( invResult_correct B n hB hn |> fun h => by simpa [ precAt_one ] using h ) ) using 1;
  rw [ ← Int.natCast_inj ] ; simp +decide [ Int.ModEq, Int.toNat_of_nonneg ] ;
  rw [ nr_div_exact_unfold ];
  norm_num [ Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow ];
  norm_num [ Int.shiftLeft_eq ]
