import Mathlib
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
open scoped ZMod


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

def NTT
    {R : Type*} [CommRing R]
    {K : ℕ} [NeZero K]
    (x : Fin K → R)
    (OMEGA : R)
    : Fin K → R :=
  fun i => ∑ j : Fin K, x j * OMEGA ^ (j.val * i.val)

private def t_table {R : Type*} [CommRing R] (n : ℕ) (ω : R) : Vector R n := Id.run do
  let mut T := Vector.replicate n 1
  let mut acc := (1 : R)
  for h : j in [0:n] do
    T := T.set j acc
    acc := acc * ω
  T

def FFT_zmod
    {k : ℕ}
    {m : ℕ} [NeZero m]
    (x : Vector (ZMod m) (2^k))
    (OMEGA : ZMod m)
    : Vector (ZMod m) (2^k) :=
  match k with
  | 0      => x
  | k' + 1 => Id.run do
    let K_pred : ℕ := 2 ^ k'
    let K  : ℕ := 2 ^ (k' + 1)
    let OMEGA_sq := OMEGA^2
    let E : Vector (ZMod m) K_pred := Vector.ofFn fun j : Fin K_pred => x[2 * j.val]
    let O : Vector (ZMod m) K_pred := Vector.ofFn fun j : Fin K_pred => x[2 * j.val + 1]

    let E' := FFT_zmod E OMEGA_sq
    let O' := FFT_zmod O OMEGA_sq
    let T  : Vector (ZMod m) K_pred := t_table K_pred OMEGA

    let mut result := Vector.replicate K (0 : (ZMod m))
    for h : j in [0:K_pred] do
      have hj : j < K_pred := h.2.1
      let p := E'[j]
      let q:= T[j] * O'[j]
      result := result.set j           (p + q) (by omega)
      result := result.set (j + K_pred)    (p - q) (by omega)
    return result

def decompose
    {m : ℕ} [NeZero m]
    (A : ZMod m) (BETA K : ℕ) : Fin K → ℕ :=
  fun j =>
    if j.val < (K - 1) then
      (A.val / BETA ^ j.val) % BETA
    else
      A.val / BETA ^ (K - 1)

def recover_sign
    {m : ℕ} [NeZero m]
    (elem : ZMod m)
    (threshold : Int)
    : Int :=
  if elem.val ≥ threshold then
    elem.val - m
  else elem.val

def good_n (n : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ 2 ^ k ∣ n

lemma exists_suitable_n' (n : ℕ) (hn : good_n n) (h_large : ¬(n < 16)) :
    let k := Nat.min (Classical.choose hn) (Nat.log 2 n - 1)
    let K := 2 ^ k
    let M := n / K
    ∃ n' : Nat, (n' ≥ 2*M + k) ∧ (n' < n) ∧ (good_n n') ∧ (2^k ∣ n') := by
  refine' ⟨ n - 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ), _, _, _, _ ⟩ <;> norm_num at *;
  · refine' le_tsub_of_add_le_left _;
    have h_exp : 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1) + 1) ≤ n := by
      have h_exp : Nat.min (Classical.choose hn) (Nat.log 2 n - 1) + 1 ≤ Nat.log 2 n := by
        exact Nat.succ_le_of_lt ( lt_of_le_of_lt ( Nat.min_le_right _ _ ) ( Nat.pred_lt ( ne_bot_of_gt ( Nat.log_pos one_lt_two ( by linarith ) ) ) ) );
      exact Nat.pow_le_of_le_log ( by linarith ) h_exp;
    rcases k : Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
    · exact absurd ( k.resolve_left ( by linarith [ Classical.choose_spec hn ] ) ) ( Nat.ne_of_gt ( Nat.sub_pos_of_lt ( Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ) ) );
    · cases min_choice ( Classical.choose hn ) ( Nat.log 2 n - 1 ) <;> simp_all +decide [ Nat.log_eq_iff ];
      · have := Classical.choose_spec hn; aesop;
      · interval_cases n;
    · rename_i k';
      nlinarith [ Nat.div_mul_le_self n ( 2 * ( 2 * 2 ^ k' ) ), show k' < 2 ^ k' from Nat.recOn k' ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.one_le_pow n 2 zero_lt_two ] ];
  · linarith;
  · refine' ⟨ Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ), _, _ ⟩ <;> norm_num at *;
    · exact ⟨ Classical.choose_spec hn |>.1, Nat.le_sub_one_of_lt ( Nat.le_log_of_pow_le ( by decide ) ( by linarith ) ) ⟩;
    · exact Or.inl ( dvd_trans ( pow_dvd_pow _ ( Nat.min_le_left _ _ ) ) ( Classical.choose_spec hn |>.2 ) );
  · exact Or.inl ( dvd_trans ( pow_dvd_pow _ ( Nat.min_le_left _ _ ) ) ( Classical.choose_spec hn |>.2 ) )

noncomputable def ssa2_multiply
    (n : ℕ)
    (hn : good_n n)
    (a b : ZMod (2^n + 1))
    : ZMod (2^n + 1) :=
  if _hn : n < 16 then
    a * b
  else
    let k := Nat.min (Classical.choose hn) ((Nat.log 2 n) - 1)
    let K := 2 ^ k
    let M := n / K
    let BETA := 2 ^ M

    have h_exists_n' : ∃ n' : ℕ,
        (n' ≥ 2*M + k) ∧ (n' < n) ∧ (good_n n') ∧ (2^k ∣ n') :=
      exists_suitable_n' n hn _hn

    let n' := Classical.choose h_exists_n'
    have h_good_n' : good_n n' := by grind

    let THETA : ZMod (2^n' + 1) := 2 ^ (n' / K)
    let OMEGA : ZMod (2^n' + 1) := THETA ^ 2
    let THETA_inv : ZMod (2^n' + 1) := THETA.inv
    let OMEGA_inv : ZMod (2^n' + 1) := OMEGA.inv
    let K_inv : ZMod (2^n' + 1) := (K : ZMod (2^n' + 1)).inv

    let A := decompose a BETA K
    let B := decompose b BETA K

    let A' := Vector.ofFn (fun j => (((A j) * (THETA ^ j.val))
                        : ZMod (2^n' + 1)))
    let B' := Vector.ofFn (fun j => (((B j) * (THETA ^ j.val))
                        : ZMod (2^n' + 1)))

    let A'_hat := FFT_zmod A' OMEGA
    let B'_hat := FFT_zmod B' OMEGA

    let C'_hat := Vector.ofFn (fun j => (ssa2_multiply
                            n' h_good_n'
                            (A'_hat[j]) (B'_hat[j])))

    let C' := FFT_zmod C'_hat OMEGA_inv
    let C_unsigned := fun j =>
      (C'[j]) * K_inv * THETA_inv ^ j.val

    let C : Fin K → ℤ := fun j =>
      recover_sign (C_unsigned j) ((j.val + 1) * (BETA ^ 2))

    ∑ j, ((C j) * (BETA ^ j.val))
termination_by n
decreasing_by
  exact (Classical.choose_spec h_exists_n').2.1


-- END SPECIFICATION
-- BEGIN CORRECTNESS PROOF

lemma sum_fin_pow_succ_split {R : Type*} [AddCommMonoid R] {k : ℕ}
    (f : Fin (2 ^ (k + 1)) → R) :
    ∑ i : Fin (2 ^ (k + 1)), f i =
    (∑ j : Fin (2 ^ k), f ⟨2 * j.val, by grind⟩) +
    (∑ j : Fin (2 ^ k), f ⟨2 * j.val + 1, by grind⟩) := by
  have h_split : Finset.range (2 ^ (k + 1)) = Finset.image (fun j => 2 * j) (Finset.range (2 ^ k)) ∪ Finset.image (fun j => 2 * j + 1) (Finset.range (2 ^ k)) := by
    ext j
    simp [Finset.mem_range, Finset.mem_image];
    exact ⟨ fun hj => by rcases Nat.even_or_odd' j with ⟨ c, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ c, by rw [ pow_succ' ] at hj; linarith, rfl ⟩, fun hj => by rcases hj with ( ⟨ c, hc, rfl ⟩ | ⟨ c, hc, rfl ⟩ ) <;> rw [ pow_succ' ] <;> linarith ⟩;
  rw [ Finset.sum_fin_eq_sum_range ];
  rw [ h_split, Finset.sum_union ];
  · simp +decide [ Finset.sum_image, Finset.sum_range, Nat.pow_succ' ];
    grind;
  · norm_num [ Finset.disjoint_right ];
    intros; omega;
/-
Key periodicity: when a^n = 1, a^(x * y) = a^(x * (y % n)).
-/
lemma pow_mul_mod_of_pow_eq_one {R : Type*} [Monoid R] {a : R} {n : ℕ}
    (ha : a ^ n = 1) (x y : ℕ) :
    a ^ (x * y) = a ^ (x * (y % n)) := by
  rw [ ← Nat.mod_add_div y n ];
  simp +decide [ pow_add, pow_mul', ha ];
  rw [ ← pow_mul, mul_comm, pow_mul, ha, one_pow, mul_one ]
/-
When OMEGA^H = -1, OMEGA^i = (if i < H then 1 else -1) * OMEGA^(i % H) for i < 2*H.
-/
lemma pow_factor_neg_one {R : Type*} [Ring R] {OMEGA : R} {H : ℕ}
    (hOMEGA : OMEGA ^ H = -1) {i : ℕ} (hi : i < 2 * H) :
    OMEGA ^ i = (if i < H then (1 : R) else (-1 : R)) * OMEGA ^ (i % H) := by
  rw [ ← Nat.div_add_mod i H ];
  rcases n : i / H with ( _ | _ | k ) <;> simp_all +decide [ pow_add, pow_mul ];
  · cases n <;> simp_all +decide [ Nat.mod_eq_of_lt ];
  · nlinarith [ Nat.div_mul_le_self i H ]
/-
The NTT butterfly identity: the NTT can be expressed via even/odd sub-sums
    when OMEGA^(2^k') = -1. This is the core of the Cooley-Tukey FFT correctness.
-/
lemma NTT_butterfly {k' : ℕ} {R : Type*} [CommRing R]
    (x : Fin (2 ^ (k' + 1)) → R) (OMEGA : R)
    (hOMEGA : OMEGA ^ (2 ^ k') = -1) (i : Fin (2 ^ (k' + 1))) :
    (∑ s : Fin (2 ^ (k' + 1)), x s * OMEGA ^ (s.val * i.val)) =
    let H := 2 ^ k'
    let j := i.val % H
    (∑ t : Fin H, x ⟨2 * t.val, by grind⟩ * (OMEGA ^ 2) ^ (t.val * j)) +
    (if i.val < H then (1 : R) else (-1 : R)) * OMEGA ^ j *
    (∑ t : Fin H, x ⟨2 * t.val + 1, by grind⟩ * (OMEGA ^ 2) ^ (t.val * j)) := by
  convert sum_fin_pow_succ_split _ using 2;
  · refine' Finset.sum_congr rfl fun j _ => _;
    rw [ ← Nat.mod_add_div i ( 2 ^ k' ) ] ; ring;
    simp +decide [ pow_add, pow_mul', hOMEGA ];
    simp +decide [ show ( OMEGA ^ 2 ) ^ 2 ^ k' = 1 by linear_combination' hOMEGA * hOMEGA ];
  · rw [ Finset.mul_sum _ _ _ ];
    refine' Finset.sum_congr rfl fun j _ => _;
    rw [ ← pow_factor_neg_one hOMEGA ];
    · rw [ ← pow_mul_mod_of_pow_eq_one ];
      · ring;
      · rw [ ← pow_mul, mul_comm, pow_mul, hOMEGA, neg_one_sq ];
    · exact lt_of_lt_of_le i.2 ( by rw [ pow_succ' ] )
set_option maxHeartbeats 1600000 in
lemma butterfly_loop_eq {α : Type*} (K : ℕ) (a₀ : α) (f g : Fin K → α) :
    (Id.run do
      let mut result := Vector.replicate (2 * K) a₀
      for h : j in [0:K] do
        have hj : j < K := h.2.1
        result := result.set j (f ⟨j, hj⟩) (by omega)
        result := result.set (j + K) (g ⟨j, hj⟩) (by omega)
      return result) =
    Vector.ofFn (fun i : Fin (2 * K) =>
      if h : i.val < K then f ⟨i.val, h⟩ else g ⟨i.val - K, by omega⟩) := by
  refine' Vector.ext _;
  intro i hi; rcases lt_or_ge i K with hi' | hi' <;> simp_all +decide [ List.range', two_mul ] ;
  · -- By induction on the list, we can show that the element at position i in the resulting vector is f ⟨i, hi'⟩.
    have h_ind : ∀ (l : List (Fin K)), (∀ i ∈ l, i.val < K) → (List.foldl (fun b x => (b.set (↑x) (f ⟨↑x, by
      exact x.2⟩) (by
    linarith [ Fin.is_lt x ])).set (↑x + K) (g ⟨↑x, by
      exact x.2⟩) (by
    lia)) (Vector.replicate (2 * K) a₀) l)[i] = if i ∈ l.map (fun x => x.val) then f ⟨i, hi'⟩ else a₀ := by
      intro l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl_append ] ;
      grind
    generalize_proofs at *;
    convert h_ind _ _ using 1
    generalize_proofs at *;
    rotate_left;
    rotate_left;
    exact List.map ( fun x : { x // x ∈ List.range' 0 K } => ⟨ x.val, by
      grind ⟩ ) ( List.range' 0 K |> List.attach )
    all_goals generalize_proofs at *;
    · grind;
    · congr! 2
      generalize_proofs at *;
      induction' ( List.range' 0 K ).attach using List.reverseRecOn with x xs ih <;> simp +decide [ * ];
    · simp +decide [ List.mem_map, List.mem_range' ];
      lia;
  · -- Since $i \geq K$, we can write $i = K + j$ for some $j$.
    obtain ⟨j, hj⟩ : ∃ j, i = K + j := by
      exact Nat.exists_eq_add_of_le hi';
    simp +decide [ hj, two_mul, List.range' ];
    -- By definition of `List.foldl`, we can rewrite the goal in terms of the list of indices.
    have h_foldl : ∀ (l : List (Fin K)), (∀ j ∈ l, j.val < K) → (List.foldl (fun (b : Vector α (2 * K)) (x : Fin K) => (b.set x.val (f x) (by
    linarith [ Fin.is_lt x ])).set (x.val + K) (g x) (by
    linarith [ Fin.is_lt x ])) (Vector.replicate (2 * K) a₀) l)[K + j] = if ⟨j, by
      grind⟩ ∈ l then g ⟨j, by
      grind⟩ else a₀ := by
      intro l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ] ;
      grind
    generalize_proofs at *;
    convert h_foldl _ _ using 1;
    rotate_left;
    rotate_left;
    exact List.map ( fun x : { x // x ∈ List.range' 0 K } => ⟨ x.val, by
      grind ⟩ ) ( List.range' 0 K |> List.attach )
    all_goals generalize_proofs at *;
    · simp +decide [ List.mem_map ];
    · rw [ List.foldl_map ];
    · simp +decide [ List.mem_map, List.mem_range' ];
      exact fun h => False.elim <| by linarith;
set_option maxHeartbeats 1600000 in
lemma t_table_eq {R : Type*} [CommRing R] (n : ℕ) (ω : R) :
    t_table n ω = Vector.ofFn (fun j : Fin n => ω ^ j.val) := by
  unfold t_table;
  convert vector_set_forIn_range n 1 fun j => ω ^ j.val using 1;
  induction' n with n ih;
  · aesop;
  · simp_all +decide [ List.range'_concat ];
    simp_all +decide [ Id.run, List.foldl_map ];
    congr! 1;
    · convert congr_arg ( fun x : Vector R n => x.push 1 ) ih using 1;
      · induction' ( List.range' 0 n ).attach using List.reverseRecOn with x xs ih <;> simp +decide [ * ];
        · grind;
        · ext i; simp +decide [ Vector.getElem_push ] ;
          split_ifs <;> simp_all +decide [ Vector.getElem_set, Vector.getElem_push ];
          · split_ifs <;> simp_all +decide [ Vector.getElem_set ];
            rename_i k hk₁ hk₂;
            clear hk₁ hk₂ ih;
            induction' x using List.reverseRecOn with x xs ih <;> simp +decide [ * ];
          · grind;
      · induction' ( List.range' 0 n ).attach using List.reverseRecOn with x xs ih <;> simp_all +decide [ List.foldl ];
        · grind +qlia;
        · grind;
    · have h_foldl : ∀ (l : List (Fin n)), (List.foldl (fun (x : Vector R (n + 1) × R) (y : Fin n) => ⟨x.1.set y.val x.2 (by
      exact Nat.lt_succ_of_lt y.2), x.2 * ω⟩) ⟨Vector.replicate (n + 1) 1, 1⟩ l).2 = ω ^ l.length := by
        intro l; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ pow_succ' ] ;
        ring
      generalize_proofs at *;
      convert h_foldl _;
      rotate_right;
      exact List.map ( fun x : { x // x ∈ List.range' 0 n } => ⟨ x.val, by
        grind ⟩ ) ( List.range' 0 n |> List.attach )
      all_goals generalize_proofs at *;
      · induction' ( List.range' 0 n ).attach using List.reverseRecOn with l ih <;> simp +decide [ * ];
      · simp +decide
/-
FFT_zmod computes the NTT when OMEGA is a primitive 2^k-th root of unity,
    i.e., when OMEGA^(2^(k-1)) = -1 (for k ≥ 1).
-/
set_option maxHeartbeats 800000 in
lemma FFT_zmod_base {m : ℕ} [NeZero m]
    (x : Vector (ZMod m) (2^0)) (OMEGA : ZMod m) :
    FFT_zmod x OMEGA = Vector.ofFn (NTT x.get OMEGA) := by
  unfold FFT_zmod NTT;
  ext i;
  interval_cases i ; aesop
/-
Helper: NTT_butterfly expressed in the form we need
-/
set_option maxHeartbeats 800000 in
lemma NTT_butterfly_get {k' : ℕ} {m : ℕ} [NeZero m]
    (x : Vector (ZMod m) (2^(k'+1))) (OMEGA : ZMod m)
    (hOMEGA : OMEGA ^ (2 ^ k') = -1) (i : Fin (2 ^ (k' + 1))) :
    NTT x.get OMEGA i =
    let H := 2 ^ k'
    let j := i.val % H
    NTT (fun t : Fin H => x[2 * t.val]) (OMEGA ^ 2) ⟨j, Nat.mod_lt _ (by positivity)⟩ +
    (if i.val < H then (1 : ZMod m) else (-1 : ZMod m)) * OMEGA ^ j *
    NTT (fun t : Fin H => x[2 * t.val + 1]) (OMEGA ^ 2) ⟨j, Nat.mod_lt _ (by positivity)⟩ := by
  convert NTT_butterfly x.get OMEGA hOMEGA i using 1
set_option maxHeartbeats 3200000 in
lemma FFT_zmod_step {k' : ℕ} {m : ℕ} [NeZero m]
    (x : Vector (ZMod m) (2^(k'+1))) (OMEGA : ZMod m)
    (hOMEGA : OMEGA ^ (2 ^ k') = -1)
    (ih_even : FFT_zmod (Vector.ofFn fun j : Fin (2 ^ k') => x[2 * j.val]) (OMEGA ^ 2) =
               Vector.ofFn (NTT (Vector.ofFn fun j : Fin (2 ^ k') => x[2 * j.val]).get (OMEGA ^ 2)))
    (ih_odd  : FFT_zmod (Vector.ofFn fun j : Fin (2 ^ k') => x[2 * j.val + 1]) (OMEGA ^ 2) =
               Vector.ofFn (NTT (Vector.ofFn fun j : Fin (2 ^ k') => x[2 * j.val + 1]).get (OMEGA ^ 2)))
    : FFT_zmod x OMEGA = Vector.ofFn (NTT x.get OMEGA) := by
  unfold FFT_zmod;
  apply Vector.ext;
  intro i hi; simp +decide [ *, NTT_butterfly_get ] ;
  convert congr_arg ( fun v : Vector ( ZMod m ) ( 2 * 2 ^ k' ) => v[i] ) ( butterfly_loop_eq ( 2 ^ k' ) 0 ( fun j => NTT ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val] ).get ( OMEGA ^ 2 ) j + ( t_table ( 2 ^ k' ) OMEGA)[j] * NTT ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val + 1] ).get ( OMEGA ^ 2 ) j ) ( fun j => NTT ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val] ).get ( OMEGA ^ 2 ) j - ( t_table ( 2 ^ k' ) OMEGA)[j] * NTT ( Vector.ofFn fun j : Fin ( 2 ^ k' ) => x[2 * j.val + 1] ).get ( OMEGA ^ 2 ) j ) ) using 1;
  · congr! 2;
    · ring;
    · rw [ pow_succ' ];
    · ring;
    · simp +decide [ pow_succ', List.range' ];
      congr! 2;
      · congr! 1;
        grind;
      · ring;
  · simp +decide [ Vector.get_ofFn, t_table_eq ];
    split_ifs <;> simp_all +decide [ Nat.mod_eq_of_lt, pow_add, pow_mul, NTT ];
    rw [ show i - 2 ^ k' = i % 2 ^ k' from ?_ ];
    · ring;
    · rw [ Nat.mod_eq_sub_mod ( by linarith ) ];
      rw [ Nat.mod_eq_of_lt ( by rw [ tsub_lt_iff_left ] <;> linarith [ pow_succ' 2 k' ] ) ]
set_option maxHeartbeats 1600000 in
theorem FFT_zmod_eq_NTT
    {k : ℕ} {m : ℕ} [NeZero m]
    (x : Vector (ZMod m) (2^k)) (OMEGA : ZMod m)
    (hOMEGA : k ≥ 1 → OMEGA ^ (2 ^ (k - 1)) = -1)
    : FFT_zmod x OMEGA = Vector.ofFn (NTT x.get OMEGA) := by
  induction k generalizing OMEGA with
  | zero => exact FFT_zmod_base x OMEGA
  | succ k' ih =>
    have hO := hOMEGA (by omega)
    simp only [Nat.succ_sub_one] at hO
    have ih_hyp : k' ≥ 1 → (OMEGA ^ 2) ^ (2 ^ (k' - 1)) = -1 := by
      intro hk'
      rw [← pow_mul, show 2 * 2 ^ (k' - 1) = 2 ^ k' from by
        cases k' with | zero => omega | succ n => simp [pow_succ]; ring]
      exact hO
    exact FFT_zmod_step x OMEGA hO
      (ih (Vector.ofFn fun j : Fin (2 ^ k') => x[2 * j.val]) (OMEGA ^ 2) ih_hyp)
      (ih (Vector.ofFn fun j : Fin (2 ^ k') => x[2 * j.val + 1]) (OMEGA ^ 2) ih_hyp)
set_option maxHeartbeats 4000000 in
set_option grind.warning false in
/-! ## Helper definitions and lemmas for the correctness proof -/
/-- Negacyclic convolution -/
def negacyclic_conv_ssa {R : Type*} [CommRing R] {K : ℕ} [NeZero K]
    (A B : Fin K → R) : Fin K → R :=
  fun l => ∑ j : Fin K, ∑ k : Fin K,
    if (j.val + k.val) % K = l.val then
      (if j.val + k.val < K then A j * B k else -(A j * B k))
    else 0
lemma beta_pow_K_eq_ssa (n K : ℕ) (hK : K ∣ n) : (2 ^ (n / K)) ^ K = 2 ^ n := by
  rw [← pow_mul, Nat.div_mul_cancel hK]
lemma ZMod_two_pow_eq_neg_one_ssa (n : ℕ) (hn : n ≥ 1) :
    (2 ^ n : ZMod (2 ^ n + 1)) = -1 := by
  exact eq_neg_of_add_eq_zero_left (mod_cast by simp +decide)
lemma decompose_sum_eq_val_ssa {m : ℕ} [NeZero m] (a : ZMod m) (BETA K : ℕ)
    (hBETA : BETA ≥ 1) (hK : K ≥ 1) :
    ∑ j : Fin K, decompose a BETA K j * BETA ^ j.val = a.val := by
  have h_decomp : ∀ (k : ℕ), ∑ j ∈ Finset.range k, (a.val / BETA ^ j) % BETA * BETA ^ j + (a.val / BETA ^ k) * BETA ^ k = a.val := by
    intro k; induction' k with k ih <;> simp_all +decide [ Finset.sum_range_succ, pow_succ, ← mul_assoc ] ;
    rw [ ← Nat.mod_add_div ( a.val / BETA ^ k ) BETA ] at *; simp_all +decide [ Nat.div_div_eq_div_mul, mul_assoc ] ;
    convert ih using 1 ; ring;
  rcases K with ( _ | K ) <;> simp_all +decide [ Finset.sum_range, decompose ];
  rw [ Fin.sum_univ_castSucc ] ; aesop
lemma negacyclic_conv_eval_ssa {R : Type*} [CommRing R] {K : ℕ} [NeZero K]
    (A B : Fin K → R) (β : R) (hβ : β ^ K = -1) :
    ∑ l : Fin K, negacyclic_conv_ssa A B l * β ^ l.val =
    (∑ j : Fin K, A j * β ^ j.val) * (∑ k : Fin K, B k * β ^ k.val) := by
  unfold negacyclic_conv_ssa;
  simp +decide only [Finset.sum_mul _ _ _];
  have h_sum : ∀ (j k : Fin K), β ^ (j.val + k.val) = if j.val + k.val < K then β ^ ((j.val + k.val) % K) else -β ^ ((j.val + k.val) % K) := by
    intro j k
    have h_exp : β ^ (j.val + k.val) = β ^ ((j.val + k.val) % K) * (β ^ K) ^ ((j.val + k.val) / K) := by
      rw [ ← pow_mul, ← pow_add, Nat.mod_add_div ];
    split_ifs <;> simp_all +decide [ Nat.div_eq_of_lt ];
    rw [ show ( j + k : ℕ ) / K = 1 by nlinarith [ Fin.is_lt j, Fin.is_lt k, Nat.div_mul_le_self ( j + k ) K, Nat.div_add_mod ( j + k ) K, Nat.mod_lt ( j + k ) ( NeZero.pos K ) ] ] ; norm_num;
  simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro j hj; rw [ Finset.sum_comm ] ; simp +decide [ ← pow_add, h_sum ] ;
  rw [ Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_eq_single ⟨ ( j + ‹Fin K› ) % K, Nat.mod_lt _ ( NeZero.pos K ) ⟩ ] <;> aesop
lemma root_of_unity_sum_zero_ssa {R : Type*} [CommRing R] {k : ℕ} (hk : k ≥ 1)
    (ω : R) (hω : ω ^ (2 ^ (k - 1)) = -1) (d : ℕ) (hd : 0 < d) (hd' : d < 2 ^ k) :
    ∑ i : Fin (2 ^ k), ω ^ (i.val * d) = 0 := by
  induction' k with k ih generalizing ω d;
  · grind;
  · -- Split the sum into even and odd indices.
    have h_split : ∑ i : Fin (2 ^ (k + 1)), ω ^ (i.val * d) = (∑ j : Fin (2 ^ k), ω ^ (2 * j.val * d)) + (∑ j : Fin (2 ^ k), ω ^ ((2 * j.val + 1) * d)) := by
      convert sum_fin_pow_succ_split _ using 1;
    by_cases hk : k ≥ 1 <;> simp_all +decide [ pow_succ', pow_mul ];
    · by_cases h : 2 ^ k ∣ d;
      · obtain ⟨ m, rfl ⟩ := h;
        rcases m with ( _ | _ | m ) <;> simp_all +decide [ pow_succ', pow_mul ];
        · simp_all +decide [ mul_pow, ← pow_mul ];
        · nlinarith [ pow_pos ( zero_lt_two' ℕ ) k ];
      · have h_ind : ∑ x : Fin (2 ^ k), (ω ^ 2) ^ (x.val * d) = 0 := by
          convert ih ( ω ^ 2 ) _ ( d % 2 ^ k ) _ _ using 1;
          · refine' Finset.sum_congr rfl fun x hx => _;
            rw [ ← Nat.mod_add_div d ( 2 ^ k ) ] ; simp +decide [ pow_add, pow_mul ] ;
            simp_all +decide [ pow_right_comm, ← pow_mul ];
            simp_all +decide [ pow_mul', pow_add ];
          · cases k <;> simp_all +decide [ pow_succ', pow_mul ];
          · exact Nat.pos_of_ne_zero fun con => h <| Nat.dvd_of_mod_eq_zero con;
          · exact Nat.mod_lt _ ( by positivity );
        simp_all +decide [ mul_pow, pow_mul' ];
        simp_all +decide [ ← pow_mul', ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
        simp_all +decide [ ← pow_add, mul_comm ];
        simp_all +decide [ ← two_mul, pow_mul' ];
        simp_all +decide [ pow_right_comm ];
    · interval_cases d ; norm_num
lemma ntt_double_apply_ssa {R : Type*} [CommRing R] {k : ℕ} (hk : k ≥ 1)
    (ω ω_inv : R) (hω_inv : ω * ω_inv = 1)
    (hω : ω ^ (2 ^ (k - 1)) = -1)
    (f : Fin (2 ^ k) → R) (l : Fin (2 ^ k)) :
    NTT (NTT f ω) ω_inv l = (2 ^ k : ℕ) * f l := by
  -- By definition of $ω_inv$, we know that $ω_inv = ω^{2^k - 1}$.
  have h_ω_inv : ω_inv = ω ^ (2 ^ k - 1) := by
    have h_ω_inv : ω ^ (2 ^ k) = 1 := by
      cases k <;> simp_all +decide [ pow_succ, pow_mul ];
    rcases n : 2 ^ k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ', mul_assoc ];
    grind;
  -- Let's simplify the expression using the properties of roots of unity.
  have h_simplify : ∑ i : Fin (2 ^ k), ω ^ (i.val * (2 ^ k - 1) * l.val) * (∑ j : Fin (2 ^ k), f j * ω ^ (j.val * i.val)) = ∑ j : Fin (2 ^ k), f j * ∑ i : Fin (2 ^ k), ω ^ (i.val * ((j.val + (2 ^ k - 1) * l.val) % (2 ^ k))) := by
    have h_simplify : ∀ i j : Fin (2 ^ k), ω ^ (i.val * (2 ^ k - 1) * l.val) * ω ^ (j.val * i.val) = ω ^ (i.val * ((j.val + (2 ^ k - 1) * l.val) % (2 ^ k))) := by
      intro i j
      have h_exp : ω ^ (i.val * (2 ^ k - 1) * l.val + j.val * i.val) = ω ^ (i.val * ((j.val + (2 ^ k - 1) * l.val) % (2 ^ k))) := by
        have h_exp : ω ^ (2 ^ k) = 1 := by
          cases k <;> simp_all +decide [ pow_succ, pow_mul ];
        rw [ ← Nat.mod_add_div ( i.val * ( ( j.val + ( 2 ^ k - 1 ) * l.val ) % 2 ^ k ) ) ( 2 ^ k ) ] ; simp_all +decide [ pow_add, pow_mul ] ; ring;
        rw [ ← pow_add, ← Nat.mod_add_div ( ( i : ℕ ) * ( 2 ^ k - 1 ) * l + i * j ) ( 2 ^ k ), pow_add, pow_mul ] ; aesop;
      rw [ ← h_exp, pow_add ];
    simp +decide only [Finset.mul_sum _ _ _, mul_left_comm];
    rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ h_simplify ] ;
  -- Let's simplify the inner sum using the properties of roots of unity.
  have h_inner_sum : ∀ j : Fin (2 ^ k), j ≠ l → ∑ i : Fin (2 ^ k), ω ^ (i.val * ((j.val + (2 ^ k - 1) * l.val) % (2 ^ k))) = 0 := by
    intro j hj_ne_l
    have h_inner_sum_zero : ∑ i : Fin (2 ^ k), ω ^ (i.val * ((j.val + (2 ^ k - 1) * l.val) % (2 ^ k))) = 0 := by
      have h_order : 0 < ((j.val + (2 ^ k - 1) * l.val) % (2 ^ k)) ∧ ((j.val + (2 ^ k - 1) * l.val) % (2 ^ k)) < 2 ^ k := by
        refine' ⟨ Nat.pos_of_ne_zero _, Nat.mod_lt _ ( by positivity ) ⟩;
        intro h; have := Nat.dvd_of_mod_eq_zero h; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Fin.ext_iff ] ;
        simp_all +decide [ add_eq_zero_iff_eq_neg ];
        simp_all +decide [ Fin.ext_iff, ZMod.natCast_eq_natCast_iff' ];
        exact hj_ne_l ( Nat.mod_eq_of_lt j.2 ▸ Nat.mod_eq_of_lt l.2 ▸ this )
      convert root_of_unity_sum_zero_ssa hk ω hω _ h_order.1 h_order.2 using 1;
    exact h_inner_sum_zero;
  convert h_simplify using 1;
  · unfold NTT; simp +decide [ h_ω_inv, pow_mul ] ;
    exact Finset.sum_congr rfl fun _ _ => by ring;
  · rw [ Finset.sum_eq_single l ] <;> simp_all +decide [ mul_comm ];
    rw [ show ( l + l * ( 2 ^ k - 1 ) : ℕ ) % 2 ^ k = 0 from Nat.mod_eq_zero_of_dvd ⟨ l, by nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow k 2 zero_lt_two ) ] ⟩ ] ; simp +decide [ Finset.sum_const, nsmul_eq_mul ]
/-- Cyclic convolution -/
def cyclic_conv_ssa {R : Type*} [CommRing R] {K : ℕ} [NeZero K]
    (f g : Fin K → R) : Fin K → R :=
  fun l => ∑ j : Fin K, ∑ k : Fin K,
    if (j.val + k.val) % K = l.val then f j * g k else 0
lemma ntt_pointwise_eq_ntt_conv_ssa {R : Type*} [CommRing R] {K : ℕ} [NeZero K]
    (ω : R) (hω : ω ^ K = 1)
    (f g : Fin K → R) (i : Fin K) :
    NTT f ω i * NTT g ω i = NTT (cyclic_conv_ssa f g) ω i := by
  unfold cyclic_conv_ssa NTT;
  simp +decide [ Finset.sum_mul, pow_mul' ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro x hx; rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.sum_comm ] ;
  refine' Finset.sum_congr rfl fun y hy => _;
  rw [ Finset.sum_eq_single ⟨ ( x + y ) % K, Nat.mod_lt _ ( NeZero.pos K ) ⟩ ] <;> simp +decide [ *, mul_assoc, mul_comm, mul_left_comm ];
  · rw [ ← pow_add, ← Nat.mod_add_div ( x + y ) K ] ; simp +decide [ pow_add, pow_mul, hω ] ;
    simp +decide [ pow_right_comm, hω ];
  · exact fun b hb₁ hb₂ => False.elim <| hb₁ <| Fin.ext hb₂.symm
lemma weighted_cyclic_eq_negacyclic_ssa {R : Type*} [CommRing R] {K : ℕ} [NeZero K]
    (A B : Fin K → R) (θ θ_inv : R) (hθ : θ ^ K = -1) (hθ_inv : θ * θ_inv = 1)
    (l : Fin K) :
    cyclic_conv_ssa (fun j => A j * θ ^ j.val) (fun j => B j * θ ^ j.val) l * θ_inv ^ l.val =
    negacyclic_conv_ssa A B l := by
  unfold cyclic_conv_ssa negacyclic_conv_ssa;
  simp +decide only [mul_left_comm, mul_comm, Finset.mul_sum _ _ _];
  refine' Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => _ ; split_ifs <;> simp_all +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm ];
  · simp_all +decide [ ← mul_assoc, ← pow_add, Nat.mod_eq_of_lt ];
    simp +decide [ mul_assoc, ← mul_pow, hθ_inv ];
  · have h_exp : θ ^ (i.val + j.val) = θ ^ l.val * (-1) := by
      rw [ ← ‹ ( i + j : ℕ ) % K = l ›, ← Nat.mod_add_div ( i + j ) K ] ; simp +decide [ pow_add, pow_mul, hθ ] ;
      rcases Nat.even_or_odd' ( ( i + j ) / K ) with ⟨ k, hk | hk ⟩ <;> simp +decide [ hk, pow_add, pow_mul, hθ ];
      have := Nat.mod_add_div ( i + j ) K; simp_all +decide [ pow_add, pow_mul ] ;
      nlinarith [ Fin.is_lt i, Fin.is_lt j, Fin.is_lt l, show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Fin.is_lt i, Fin.is_lt j, Fin.is_lt l ] ) ];
    simp_all +decide [ ← mul_assoc, ← pow_add ];
    rw [ mul_assoc, ← mul_pow, hθ_inv, one_pow, mul_one ]
lemma val_natCast_eq (m : ℕ) [NeZero m] (x : ZMod m) : (x.val : ZMod m) = x := by
  rw [ZMod.natCast_val, ZMod.cast_id']; rfl
lemma recover_sign_cast {m : ℕ} [NeZero m] (elem : ZMod m) (threshold : Int) :
    (recover_sign elem threshold : ZMod m) = elem := by
  unfold recover_sign
  split_ifs with h
  · simp only [Int.cast_sub, Int.cast_natCast]
    have : (m : ZMod m) = 0 := by simp
    rw [this, sub_zero]
    exact val_natCast_eq m elem
  · simp only [Int.cast_natCast]
    exact val_natCast_eq m elem
/-! ### Key helper lemma for ssa2_multiply_correct
We need to show that THETA is a primitive 2K-th root of unity in Z/(2^n'+1)Z,
i.e., THETA^K = -1. This follows from THETA = 2^(n'/K) and
2^n' ≡ -1 (mod 2^n'+1).
-/
lemma theta_pow_K_eq_neg_one {n' K : ℕ} (hK : K ∣ n') (hn' : n' ≥ 1) :
    (2 ^ (n' / K) : ZMod (2 ^ n' + 1)) ^ K = -1 := by
  rw [← pow_mul, Nat.div_mul_cancel hK]
  exact ZMod_two_pow_eq_neg_one_ssa n' hn'
lemma omega_pow_K_eq_one {n' K : ℕ} (hK : K ∣ n') (hn' : n' ≥ 1) :
    ((2 ^ (n' / K) : ZMod (2 ^ n' + 1)) ^ 2) ^ K = 1 := by
  convert congr_arg ( · ^ 2 ) ( theta_pow_K_eq_neg_one hK hn' ) using 1 <;> ring



open scoped ZMod
/-! ## Helper lemmas for ssa2_multiply_correct recursive case -/
/-- The integer version of negacyclic convolution, defined over ℤ -/
def negacyclic_conv_int {K : ℕ} [NeZero K] (A B : Fin K → ℕ) : Fin K → ℤ :=
  fun l => ∑ j : Fin K, ∑ k : Fin K,
    if (j.val + k.val) % K = l.val then
      (if j.val + k.val < K then (A j : ℤ) * (B k : ℤ) else -((A j : ℤ) * (B k : ℤ)))
    else 0
/-
negacyclic_conv_int cast to any CommRing equals negacyclic_conv_ssa with cast inputs
-/
lemma negacyclic_conv_int_cast {K : ℕ} [NeZero K] {R : Type*} [CommRing R]
    (A B : Fin K → ℕ) (l : Fin K) :
    (negacyclic_conv_int A B l : R) =
    negacyclic_conv_ssa (fun j => (A j : R)) (fun j => (B j : R)) l := by
  unfold negacyclic_conv_int negacyclic_conv_ssa; simp +decide ;
/-
Each digit of decompose is at most BETA
-/
lemma decompose_le_BETA {m : ℕ} [NeZero m] (a : ZMod m) (BETA K : ℕ)
    (hBETA : BETA ≥ 1) (hK : K ≥ 1) (hm : m ≤ BETA ^ K + 1)
    (j : Fin K) :
    decompose a BETA K j ≤ BETA := by
  rcases K with ( _ | _ | K ) <;> simp_all +decide [ decompose ];
  · exact Nat.le_of_lt_succ ( lt_of_lt_of_le ( ZMod.val_lt a ) hm );
  · split_ifs;
    · exact Nat.le_of_lt ( Nat.mod_lt _ hBETA );
    · refine' Nat.div_le_of_le_mul _;
      grind
/-
Non-last digits of decompose are strictly less than BETA
-/
lemma decompose_lt_BETA {m : ℕ} [NeZero m] (a : ZMod m) (BETA K : ℕ)
    (hBETA : BETA ≥ 1) (j : Fin K) (hj : j.val < K - 1) :
    decompose a BETA K j < BETA := by
  unfold decompose;
  split_ifs ; exact Nat.mod_lt _ hBETA
/-
Negacyclic convolution positive bound:
    the integer coefficient is strictly less than (l+1) * BETA^2
    when both sequences have appropriate digit bounds
-/
lemma negacyclic_conv_int_upper {K BETA : ℕ} [NeZero K]
    (A B : Fin K → ℕ)
    (hK : K ≥ 2) (hBETA : BETA ≥ 1)
    (hA : ∀ j, A j ≤ BETA) (hB : ∀ j, B j ≤ BETA)
    (hA' : ∀ j : Fin K, j.val < K - 1 → A j < BETA)
    (hB' : ∀ j : Fin K, j.val < K - 1 → B j < BETA)
    (l : Fin K) :
    negacyclic_conv_int A B l < ((l.val + 1) * BETA ^ 2 : ℤ) := by
  refine' lt_of_lt_of_le ( Finset.sum_lt_sum _ _ ) _;
  use fun i => ∑ k : Fin K, if ( i.val + k.val ) % K = l.val then if i.val + k.val < K then ( BETA : ℤ ) * ( BETA : ℤ ) else 0 else 0;
  · intro i hi; apply Finset.sum_le_sum; intro k hk; split_ifs <;> norm_cast ;
    · exact Nat.mul_le_mul ( hA i ) ( hB k );
    · exact neg_nonpos_of_nonneg ( Nat.cast_nonneg _ );
  · refine' ⟨ ⟨ 0, by linarith ⟩, _, _ ⟩ <;> norm_num;
    refine' Finset.sum_lt_sum _ _;
    · exact fun i _ => by split_ifs <;> nlinarith [ hA 0, hB i ] ;
    · refine' ⟨ ⟨ l, by linarith [ Fin.is_lt l ] ⟩, Finset.mem_univ _, _ ⟩ ; norm_num;
      rw [ if_pos ( Nat.mod_eq_of_lt l.2 ), if_pos ( Nat.mod_eq_of_lt l.2 ) ] ; nlinarith [ hA 0, hB l, hA' 0 ( Nat.sub_pos_of_lt hK ) ];
  · -- The sum is over pairs (i, k) where i + k ≡ l (mod K) and i + k < K. For each such pair, the term is BETA^2.
    have h_pairs : Finset.filter (fun p : Fin K × Fin K => (p.1.val + p.2.val) % K = l.val ∧ p.1.val + p.2.val < K) (Finset.univ : Finset (Fin K × Fin K)) ⊆ Finset.image (fun i : Fin (l.val + 1) => (⟨i.val, by linarith [Fin.is_lt i, Fin.is_lt l]⟩, ⟨l.val - i.val, by omega⟩)) (Finset.univ : Finset (Fin (l.val + 1))) := by
      intros p hp
      simp at hp
      generalize_proofs at *;
      simp +zetaDelta at *;
      use ⟨p.1.val, by
        linarith [ Nat.mod_eq_of_lt hp.2 ]⟩
      generalize_proofs at *;
      exact Prod.ext ( Fin.ext <| by linarith [ Nat.mod_eq_of_lt hp.2 ] ) ( Fin.ext <| by norm_num; linarith [ Nat.mod_eq_of_lt hp.2, Nat.sub_add_cancel <| show ( p.1 : ℕ ) ≤ l from by linarith ] );
    have h_sum_pairs : ∑ p ∈ Finset.filter (fun p : Fin K × Fin K => (p.1.val + p.2.val) % K = l.val ∧ p.1.val + p.2.val < K) (Finset.univ : Finset (Fin K × Fin K)), (BETA : ℤ) * (BETA : ℤ) ≤ (l.val + 1) * (BETA : ℤ) * (BETA : ℤ) := by
      refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_pairs fun _ _ _ => by positivity ) _;
      rw [ Finset.sum_image ] <;> norm_num [ mul_assoc ];
      exact fun i j h => by simpa [ Fin.ext_iff ] using congr_arg Prod.fst h;
    convert h_sum_pairs using 1;
    · rw [ Finset.sum_filter ];
      rw [ ← Finset.sum_product' ] ; congr ; ext ; aesop;
    · ring
/-
Negacyclic convolution negative bound
-/
lemma negacyclic_conv_int_lower {K BETA : ℕ} [NeZero K]
    (A B : Fin K → ℕ)
    (hA : ∀ j, A j ≤ BETA) (hB : ∀ j, B j ≤ BETA)
    (l : Fin K) :
    -((K - 1 - l.val : ℤ) * (BETA : ℤ) ^ 2) ≤ negacyclic_conv_int A B l := by
  -- The negative terms come from the case j+k ≥ K. Each such term is -A_j * B_k where A_j ≤ BETA, B_k ≤ BETA. The negative contribution is at most K*(BETA^2) in absolute value.
  have h_neg : ∑ j : Fin K, ∑ k : Fin K, (if (j.val + k.val) % K = l.val ∧ j.val + k.val ≥ K then -(A j * B k : ℤ) else 0) ≥ -((K - 1 - l.val) * BETA ^ 2 : ℤ) := by
    -- The number of pairs (j,k) with j+k ≥ K and j+k ≡ l (mod K) is at most K-1-l.
    have h_count : (∑ j : Fin K, ∑ k : Fin K, if (j.val + k.val) % K = l.val ∧ j.val + k.val ≥ K then 1 else 0) ≤ K - 1 - l.val := by
      -- For each $j$, there is at most one $k$ such that $(j.val + k.val) % K = l.val$ and $j.val + k.val ≥ K$.
      have h_unique_k : ∀ j : Fin K, Finset.card (Finset.filter (fun k : Fin K => (j.val + k.val) % K = l.val ∧ j.val + k.val ≥ K) Finset.univ) ≤ if j.val ≥ l.val + 1 then 1 else 0 := by
        intro j; split_ifs <;> simp_all +decide [ Finset.card_le_one ] ;
        · intro a ha₁ ha₂ b hb₁ hb₂; rw [ Fin.ext_iff ] ; have := Nat.modEq_iff_dvd.mp ( ha₁.trans hb₁.symm ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
          obtain ⟨ k, hk ⟩ := this; nlinarith [ show k = 0 by nlinarith [ Fin.is_lt a, Fin.is_lt b ] ] ;
        · intro x hx; have := Nat.mod_add_div ( j + x ) K; simp_all +decide [ Nat.mod_eq_of_lt ] ;
          nlinarith [ show ( j : ℕ ) ≤ l from by assumption, show ( l : ℕ ) < K from by exact l.2, show ( x : ℕ ) < K from by exact x.2, show ( ( j + x ) / K : ℕ ) = 0 from by nlinarith [ show ( j : ℕ ) ≤ l from by assumption, show ( l : ℕ ) < K from by exact l.2, show ( x : ℕ ) < K from by exact x.2 ] ];
      refine' le_trans ( Finset.sum_le_sum fun j _ => by simpa using h_unique_k j ) _;
      simp +decide [ Finset.sum_ite, Finset.filter_lt_eq_Ioi ];
    have h_neg_contribution : ∑ j : Fin K, ∑ k : Fin K, (if (j.val + k.val) % K = l.val ∧ j.val + k.val ≥ K then -(A j * B k : ℤ) else 0) ≥ -((∑ j : Fin K, ∑ k : Fin K, if (j.val + k.val) % K = l.val ∧ j.val + k.val ≥ K then 1 else 0) * BETA ^ 2 : ℤ) := by
      push_cast [ Finset.sum_mul _ _ _ ];
      rw [ ← Finset.sum_neg_distrib ];
      exact Finset.sum_le_sum fun i hi => by rw [ ← Finset.sum_neg_distrib ] ; exact Finset.sum_le_sum fun j hj => by split_ifs <;> nlinarith [ hA i, hB j ] ;
    refine le_trans ?_ h_neg_contribution;
    gcongr;
    norm_cast;
    grind;
  refine le_trans h_neg ?_;
  refine' Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => _;
  grind
/-
The sum of integer negacyclic convolution coefficients
    times BETA^l equals a*b in ZMod(2^n+1)
-/
lemma negacyclic_int_sum_eq_mul {n : ℕ} (hn : n ≥ 1)
    (a b : ZMod (2^n + 1)) (BETA K : ℕ)
    (hBETA : BETA = 2 ^ (n / K)) (hK : K ≥ 1) [NeZero K]
    (hKdvd : K ∣ n) :
    (∑ l : Fin K,
      (negacyclic_conv_int (decompose a BETA K) (decompose b BETA K) l : ZMod (2^n+1)) *
      (↑BETA : ZMod (2^n+1)) ^ l.val) = a * b := by
  convert negacyclic_conv_eval_ssa _ _ _ _ using 1;
  congr! 1;
  convert congr_arg ( fun x : ZMod ( 2 ^ n + 1 ) => x * ( BETA : ZMod ( 2 ^ n + 1 ) ) ^ ( ↑‹Fin K› : ℕ ) ) ( negacyclic_conv_int_cast _ _ _ ) using 1;
  · have h_sum : ∑ j : Fin K, (decompose a BETA K j : ℕ) * BETA ^ j.val = a.val ∧ ∑ k : Fin K, (decompose b BETA K k : ℕ) * BETA ^ k.val = b.val := by
      exact ⟨ decompose_sum_eq_val_ssa a BETA K ( by rw [ hBETA ] ; exact Nat.one_le_pow _ _ ( by decide ) ) hK, decompose_sum_eq_val_ssa b BETA K ( by rw [ hBETA ] ; exact Nat.one_le_pow _ _ ( by decide ) ) hK ⟩;
    norm_cast ; aesop;
  · haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; simp_all +decide [ ← ZMod.natCast_eq_zero_iff ] ;
    rw [ ← pow_mul, Nat.div_mul_cancel ( show K ∣ n from by rw [ ZMod.natCast_eq_zero_iff ] at hKdvd; exact hKdvd ), ZMod_two_pow_eq_neg_one_ssa ] ; aesop
/-
recover_sign correctly recovers the integer negacyclic coefficient
    when the modulus is large enough
-/
lemma recover_sign_eq_negacyclic_int {K m BETA : ℕ} [NeZero K] [NeZero m]
    (A B : Fin K → ℕ) (l : Fin K)
    (hm : m ≥ K * BETA ^ 2 + 1)
    (hK : K ≥ 2) (hBETA : BETA ≥ 1)
    (hA : ∀ j, A j ≤ BETA) (hB : ∀ j, B j ≤ BETA)
    (hA' : ∀ j : Fin K, j.val < K - 1 → A j < BETA)
    (hB' : ∀ j : Fin K, j.val < K - 1 → B j < BETA) :
    recover_sign
      (negacyclic_conv_ssa (fun j => (A j : ZMod m)) (fun j => (B j : ZMod m)) l)
      ((↑l.val + 1) * ↑BETA ^ 2)
    = negacyclic_conv_int A B l := by
  -- Let $c$ be the integer value of the negacyclic convolution.
  set c : ℤ := negacyclic_conv_int A B l;
  -- By definition of recover_sign, we need to show that the integer value of the negacyclic convolution is within the range of the modulus.
  have h_range : -((K - 1 - l.val : ℤ) * (BETA : ℤ) ^ 2) ≤ c ∧ c < ((l.val + 1) * BETA ^ 2 : ℤ) := by
    exact ⟨ by simpa using negacyclic_conv_int_lower A B hA hB l, by simpa using negacyclic_conv_int_upper A B hK hBETA hA hB hA' hB' l ⟩;
  have h_mod : (negacyclic_conv_ssa (fun j => (A j : ZMod m)) (fun j => (B j : ZMod m)) l).val = if c < 0 then m + c else c := by
    have h_mod : (negacyclic_conv_ssa (fun j => (A j : ZMod m)) (fun j => (B j : ZMod m)) l).val = c % m := by
      have h_mod : (negacyclic_conv_ssa (fun j => (A j : ZMod m)) (fun j => (B j : ZMod m)) l) = c := by
        convert negacyclic_conv_int_cast A B l |> Eq.symm using 1;
      rw [ h_mod, ZMod.val_intCast ];
    split_ifs <;> simp_all +decide [ Int.emod_eq_of_lt ];
    · rw [ Int.emod_eq_add_self_emod ];
      rw [ Int.emod_eq_of_lt ] <;> nlinarith [ Fin.is_lt l ];
    · rw [ Int.emod_eq_of_lt ] <;> nlinarith [ Fin.is_lt l ];
  unfold recover_sign;
  grind



/-! ## Pipeline correctness and main theorem -/
/-
The FFT-based pipeline computes the negacyclic convolution.
    Given θ with θ^K = -1 and the FFT pipeline using ω = θ²,
    the output C_unsigned l = negacyclic_conv_ssa A B l.
-/
lemma pipeline_eq_negacyclic
    {k : ℕ} {m : ℕ} [NeZero m]
    (hk : k ≥ 2)
    (A B : Fin (2^k) → ZMod m)
    (THETA : ZMod m)
    (hθ_K : THETA ^ (2^k) = -1)
    (hθ_inv : THETA * (ZMod.inv m THETA) = 1)
    (hω_inv : THETA^2 * (ZMod.inv m (THETA^2)) = 1)
    (hK_inv : (↑(2^k) : ZMod m) * (ZMod.inv m (↑(2^k))) = 1)
    (l : Fin (2^k)) :
    let OMEGA := THETA^2
    let OMEGA_inv := ZMod.inv m OMEGA
    let THETA_inv := ZMod.inv m THETA
    let K_inv := ZMod.inv m (↑(2^k))
    let A' := Vector.ofFn (fun j : Fin (2^k) => A j * THETA ^ j.val)
    let B' := Vector.ofFn (fun j : Fin (2^k) => B j * THETA ^ j.val)
    let A'_hat := FFT_zmod A' OMEGA
    let B'_hat := FFT_zmod B' OMEGA
    let C'_hat := Vector.ofFn (fun j => A'_hat[j] * B'_hat[j])
    let C' := FFT_zmod C'_hat OMEGA_inv
    C'[l] * K_inv * THETA_inv ^ l.val =
    negacyclic_conv_ssa A B l := by
  have h_apply_double : NTT (NTT (fun j => A j * THETA ^ j.val) (THETA ^ 2) * NTT (fun j => B j * THETA ^ j.val) (THETA ^ 2)) (ZMod.inv m (THETA ^ 2)) l = (2 ^ k : ℕ) * cyclic_conv_ssa (fun j => A j * THETA ^ j.val) (fun j => B j * THETA ^ j.val) l := by
    convert ntt_double_apply_ssa ( show k ≥ 1 by linarith ) ( THETA ^ 2 ) ( ZMod.inv m ( THETA ^ 2 ) ) _ _ _ l using 1;
    · congr! 2;
      ext i; exact ntt_pointwise_eq_ntt_conv_ssa _ ( show ( THETA ^ 2 ) ^ 2 ^ k = 1 from by linear_combination' hθ_K * hθ_K ) _ _ _;
    · exact hω_inv;
    · cases k <;> simp_all +decide [ pow_succ', pow_mul ];
  convert congr_arg ( fun x : ZMod m => x * ZMod.inv m ( 2 ^ k ) * ZMod.inv m THETA ^ ( l : ℕ ) ) h_apply_double using 1;
  · congr! 2;
    convert congr_arg ( fun x : Vector ( ZMod m ) ( 2 ^ k ) => x[l] ) ( FFT_zmod_eq_NTT _ _ _ ) using 1;
    · have := FFT_zmod_eq_NTT ( Vector.ofFn fun j : Fin ( 2 ^ k ) => A j * THETA ^ ( j : ℕ ) ) ( THETA ^ 2 ) ?_ <;> simp_all +decide [ NTT ];
      · have := FFT_zmod_eq_NTT ( Vector.ofFn fun j : Fin ( 2 ^ k ) => B j * THETA ^ ( j : ℕ ) ) ( THETA ^ 2 ) ?_ <;> simp_all +decide [ NTT ];
        rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ', pow_mul ];
      · cases k <;> simp_all +decide [ pow_succ', pow_mul ];
    · have h_inv_pow : (THETA ^ 2) ^ (2 ^ (k - 1)) * (ZMod.inv m (THETA ^ 2)) ^ (2 ^ (k - 1)) = 1 := by
        rw [ ← mul_pow, hω_inv, one_pow ];
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ', pow_mul ];
      exact neg_eq_iff_eq_neg.mp h_inv_pow;
  · have := weighted_cyclic_eq_negacyclic_ssa A B THETA ( ZMod.inv m THETA ) ?_ ?_ l <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    grind +splitIndPred
/-
Coprimality of powers of 2 with 2^n'+1
-/
lemma two_pow_coprime_two_pow_succ (a b : ℕ) (hb : b ≥ 1) :
    Nat.Coprime (2^a) (2^b + 1) := by
  rcases a with ( _ | a ) <;> rcases b with ( _ | b ) <;> simp_all +arith +decide [ Nat.Coprime ]



set_option maxHeartbeats 800000 in
/-- Main correctness theorem for ssa2_multiply -/
theorem ssa2_multiply_correct
    (n : ℕ)
    (hn : good_n n)
    (a b : ZMod (2^n + 1)) :
    ssa2_multiply n hn a b = a * b := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [ssa2_multiply.eq_def]
    split_ifs with h_small
    · rfl
    · -- Recursive case
      have := Classical.choose_spec ( exists_suitable_n' n hn h_small );
      have hk_ge_2 : 2 ≤ Nat.min (Classical.choose hn) (Nat.log 2 n - 1) := by
        exact le_min ( Classical.choose_spec hn |>.1 ) ( Nat.le_sub_one_of_lt ( Nat.le_log_of_pow_le ( by decide ) ( by linarith ) ) );
      have hθ_K : (2 ^ (Classical.choose (exists_suitable_n' n hn h_small) / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) : ZMod (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1)) ^ (2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) = -1 := by
        convert theta_pow_K_eq_neg_one this.2.2.2 _ using 1;
        omega;
      have hθ_inv : (2 ^ (Classical.choose (exists_suitable_n' n hn h_small) / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) : ZMod (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1)) * (ZMod.inv (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1) (2 ^ (Classical.choose (exists_suitable_n' n hn h_small) / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))))) = 1 := by
        convert ZMod.coe_mul_inv_eq_one _;
        rotate_left;
        exact 2 ^ Classical.choose ( exists_suitable_n' n hn h_small ) + 1;
        exact 2 ^ ( Classical.choose ( exists_suitable_n' n hn h_small ) / 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ) );
        have h_coprime : Nat.Coprime (2 ^ (Classical.choose (exists_suitable_n' n hn h_small) / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1)))) (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1) := by
          apply two_pow_coprime_two_pow_succ;
          omega;
        simp +decide [ ZMod.inv ];
        exact Iff.symm (imp_iff_right h_coprime);
      have hω_inv : (2 ^ (Classical.choose (exists_suitable_n' n hn h_small) / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) : ZMod (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1)) ^ 2 * (ZMod.inv (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1) ((2 ^ (Classical.choose (exists_suitable_n' n hn h_small) / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) : ZMod (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1)) ^ 2)) = 1 := by
        convert ZMod.coe_mul_inv_eq_one _ using 1;
        rotate_left;
        exact 2 ^ Classical.choose ( exists_suitable_n' n hn h_small ) + 1;
        exact ( 2 ^ ( Classical.choose ( exists_suitable_n' n hn h_small ) / 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ) ) ) ^ 2;
        simp +decide [ ZMod.coe_mul_inv_eq_one ];
        constructor <;> intro h;
        · finiteness;
        · convert h _ using 1;
          convert two_pow_coprime_two_pow_succ _ _ _ using 1;
          omega;
      have hK_inv : (2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1)) : ZMod (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1)) * (ZMod.inv (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1) (2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1)))) = 1 := by
        convert ZMod.coe_mul_inv_eq_one _ _ using 1;
        rotate_left;
        exact 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) );
        · apply two_pow_coprime_two_pow_succ;
          omega;
        · push_cast; rfl;
      have h_pipeline : ∀ l : Fin (2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))), (let k := Nat.min (Classical.choose hn) (Nat.log 2 n - 1); let K := 2 ^ k; let M := n / K; let n' := Classical.choose (exists_suitable_n' n hn h_small); let THETA := 2 ^ (n' / K); let OMEGA := THETA ^ 2; let THETA_inv := ZMod.inv (2 ^ n' + 1) THETA; let OMEGA_inv := ZMod.inv (2 ^ n' + 1) OMEGA; let K_inv := ZMod.inv (2 ^ n' + 1) K; let A := decompose a (2 ^ M) K; let B := decompose b (2 ^ M) K; let A' := Vector.ofFn (fun j : Fin K => (A j : ZMod (2 ^ n' + 1)) * THETA ^ j.val); let B' := Vector.ofFn (fun j : Fin K => (B j : ZMod (2 ^ n' + 1)) * THETA ^ j.val); let A'_hat := FFT_zmod A' OMEGA; let B'_hat := FFT_zmod B' OMEGA; let C'_hat := Vector.ofFn (fun j => ssa2_multiply n' (Classical.choose_spec (exists_suitable_n' n hn h_small)).2.2.1 A'_hat[j] B'_hat[j]); let C' := FFT_zmod C'_hat OMEGA_inv; C'[l] * K_inv * THETA_inv ^ l.val = negacyclic_conv_ssa (fun j => (A j : ZMod (2 ^ n' + 1))) (fun j => (B j : ZMod (2 ^ n' + 1))) l) := by
        convert pipeline_eq_negacyclic hk_ge_2 _ _ _ _ _ _ _ using 1;
        rotate_left;
        exact 2 ^ Classical.choose ( exists_suitable_n' n hn h_small ) + 1;
        exact ⟨ by positivity ⟩;
        exact fun j => ( decompose a ( 2 ^ ( n / 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ) ) ) ( 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ) ) j : ZMod ( 2 ^ Classical.choose ( exists_suitable_n' n hn h_small ) + 1 ) );
        exact fun j => ( decompose b ( 2 ^ ( n / 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ) ) ) ( 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ) ) j : ZMod ( 2 ^ Classical.choose ( exists_suitable_n' n hn h_small ) + 1 ) );
        exact 2 ^ ( Classical.choose ( exists_suitable_n' n hn h_small ) / 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ) );
        · convert hθ_K using 1;
        · convert hθ_inv using 1;
        · convert hω_inv using 1;
        · convert hK_inv using 1;
        · simp +decide [ ih _ this.2.1 ];
      have h_recover_sign : ∀ l : Fin (2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))), recover_sign (negacyclic_conv_ssa (fun j => (decompose a (2 ^ (n / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) ) (2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) j : ZMod (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1))) (fun j => (decompose b (2 ^ (n / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) ) (2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) j : ZMod (2 ^ Classical.choose (exists_suitable_n' n hn h_small) + 1))) l) ((l.val + 1) * (2 ^ (n / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1)))) ^ 2) = negacyclic_conv_int (decompose a (2 ^ (n / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) ) (2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) ) (decompose b (2 ^ (n / 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) ) (2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1))) ) l := by
        apply_rules [ recover_sign_eq_negacyclic_int ];
        ext l;
        apply_rules [ recover_sign_eq_negacyclic_int ];
        any_goals intro j hj; exact decompose_lt_BETA _ _ _ ( Nat.one_le_pow _ _ ( by decide ) ) _ hj;
        · rw [ ← pow_mul ];
          rw [ ← pow_add ];
          exact Nat.succ_le_succ ( pow_le_pow_right₀ ( by decide ) ( by linarith ) );
        · exact le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) hk_ge_2 );
        · exact Nat.one_le_pow _ _ ( by decide );
        · apply_rules [ decompose_le_BETA ];
          · exact Nat.one_le_pow _ _ ( by decide );
          · exact Nat.one_le_pow _ _ ( by decide );
          · rw [ ← pow_mul, Nat.mul_comm, pow_mul ];
            rw [ ← pow_mul, Nat.mul_div_cancel' ];
            exact dvd_trans ( pow_dvd_pow _ ( Nat.min_le_left _ _ ) ) ( Classical.choose_spec hn |>.2 );
        · apply_rules [ decompose_le_BETA ];
          · exact Nat.one_le_pow _ _ ( by decide );
          · exact Nat.one_le_pow _ _ ( by decide );
          · rw [ ← pow_mul, Nat.mul_comm, pow_mul ];
            rw [ ← pow_mul, Nat.mul_div_cancel' ];
            exact dvd_trans ( pow_dvd_pow _ ( Nat.min_le_left _ _ ) ) ( Classical.choose_spec hn |>.2 );
      convert negacyclic_int_sum_eq_mul ( show n ≥ 1 from by linarith ) a b ( 2 ^ ( n / 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ) ) ) ( 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ) ) _ _ _ using 1;
      · refine' Finset.sum_congr rfl fun l hl => _;
        simp +zetaDelta at *;
        rw [ ← h_recover_sign l, ← h_pipeline l ];
      · rfl;
      · exact Nat.one_le_pow _ _ ( by decide );
      · exact dvd_trans ( pow_dvd_pow _ ( Nat.min_le_left _ _ ) ) ( Classical.choose_spec hn |>.2 )
