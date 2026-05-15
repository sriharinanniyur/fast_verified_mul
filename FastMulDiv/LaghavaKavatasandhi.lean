import Mathlib
open Finset
set_option maxHeartbeats 400000


-- GENERIC FOR-LOOP LEMMAS
lemma range_forIn_invariant {α : Type} (n : Nat) (init : α)
    (body : Nat → α → α)
    (P : Nat → α → Prop)
    (h0 : P 0 init)
    (hstep : ∀ i, i < n → ∀ s, P i s → P (i + 1) (body i s)) :
    P n (Id.run do
      let mut s := init
      for i in [0:n] do
        s := body i s
      return s) := by
  induction' n with n ih generalizing init <;> simp_all +decide [ List.range'_concat ];
  exact hstep _ le_rfl _ ( ih _ h0 fun i hi => hstep _ ( Nat.le_of_lt hi ) )
/-- Version that returns the actual value: the for loop equals iterated application -/
def iterateBody (body : Nat → α → α) : Nat → Nat → α → α
  | _, 0, s => s
  | start, k + 1, s => iterateBody body (start + 1) k (body start s)


lemma range_forIn_eq_iterate {α : Type} (n : Nat) (init : α)
    (body : Nat → α → α) :
    (Id.run do
      let mut s := init
      for i in [0:n] do
        s := body i s
      return s) = iterateBody body 0 n init := by
  convert range_forIn_invariant n init body _ _ _ using 1;
  rotate_left;
  rotate_left;
  exact fun i s => s = ( List.foldl ( fun x y => body y x ) init ( List.range i ) );
  · rfl;
  · simp +decide [ List.range_succ ];
  · rw [ List.range_eq_range' ] ; aesop;
  · induction' n with n ih generalizing init <;> simp_all +decide [ List.range'_concat ];
    · rfl;
    · -- By definition of `iterateBody`, we have `iterateBody body 0 (n + 1) init = body n (iterateBody body 0 n init)`.
      have h_iter : ∀ (start : ℕ) (k : ℕ) (s : α), iterateBody body start (k + 1) s = body (start + k) (iterateBody body start k s) := by
        intros start k s
        induction' k with k ih generalizing start s;
        · rfl;
        · rw [ show iterateBody body start ( k + 2 ) s = iterateBody body ( start + 1 ) ( k + 1 ) ( body start s ) by rfl, ih ];
          rw [ show iterateBody body start ( k + 1 ) s = iterateBody body ( start + 1 ) k ( body start s ) by rfl ] ; ring;
      grind



lemma iterateBody_eq_foldl {α : Type} (body : Nat → α → α) (start n : Nat) (init : α) :
    iterateBody body start n init =
    List.foldl (fun s i => body i s) init (List.range' start n) := by
  induction' n with n ih generalizing start init;
  · rfl;
  · convert ih ( start + 1 ) ( body start init ) using 1



lemma range_forIn_invariant2 {α β : Type} (n : Nat) (init_a : α) (init_b : β)
    (body : Nat → α → β → α × β)
    (P : Nat → α → β → Prop)
    (h0 : P 0 init_a init_b)
    (hstep : ∀ i, i < n → ∀ a b, P i a b → P (i + 1) (body i a b).1 (body i a b).2) :
    P n
      (Id.run do
        let mut a := init_a
        let mut b := init_b
        for i in [0:n] do
          let r := body i a b
          a := r.1
          b := r.2
        return (a, b)).1
      (Id.run do
        let mut a := init_a
        let mut b := init_b
        for i in [0:n] do
          let r := body i a b
          a := r.1
          b := r.2
        return (a, b)).2 := by
  induction' n with n ih generalizing init_a init_b;
  · aesop;
  · convert hstep _ n.lt_succ_self _ _ ( ih _ _ h0 fun i hi a b h => hstep _ ( Nat.lt_succ_of_lt hi ) _ _ h ) using 1;
    · simp +decide [ List.range'_concat ];
    · simp +decide [ List.range'_concat ]

-- BEGIN LAGHAVA KAVATASANDHI SPEC AND PROOF --
-------------------------------------------------------------


def multAndAdd (a b c base : Nat) : Nat × Nat :=
  let fullres := a * b + c
  let res := fullres % base
  let carry := fullres / base
  (res, carry)

def zeroPrefix (W : Array Nat) (m : Nat) : Array Nat :=
  Id.run do
    let mut W' := W
    let lim := min m W'.size
    for i in [0:lim] do
      W' := W'.set! i 0
    return W'

def lsdToNat (digits : Array Nat) (base : Nat) : Nat :=
  Id.run do
    let mut pow := 1
    let mut acc := 0
    for i in [0:digits.size] do
      acc := acc + digits[i]! * pow
      pow := pow * base
    return acc

def ValidDigits (base : Nat) (A : Array Nat) : Prop :=
  ∀ i, i < A.size → A[i]! < base

def multiplyDigits
(W : Array Nat)
(m base : Nat)
(hbase : base ≥ 2)
(hsplit : 0 < m ∧ m < W.size)
: Array Nat :=
  Id.run do
    let l := W.size
    let n := l - m
    let X := W.extract 0 m
    let mut W' := zeroPrefix W m
    for i in [0:n] do
      let mut c := 0
      for j in [0:m] do
        let k := i + j
        let (res, c') := multAndAdd (X[j]!) (W'[m + i]!) (W'[k]! + c) base
        W' := W'.set! k res
        c := c'
      W' := W'.set! (i + m) c
    return W'

def laghavaKavatasandhi
(W : Array Nat)
(m base : Nat)
(hbase : base ≥ 2)
(hsplit : 0 < m ∧ m < W.size - 1)
: Array Nat :=
  multiplyDigits W m base hbase (by omega)

def leftDigits (W : Array Nat) (m : Nat) : Array Nat :=
  W.extract 0 m
def rightDigits (W : Array Nat) (m : Nat) : Array Nat :=
  W.extract m W.size
def leftVal (W : Array Nat) (m base : Nat) : Nat :=
  lsdToNat (leftDigits W m) base
def rightVal (W : Array Nat) (m base : Nat) : Nat :=
  lsdToNat (rightDigits W m) base
def outVal (W : Array Nat) (m base : Nat) (hbase : base ≥ 2)
(hsplit : 0 < m ∧ m < W.size) : Nat :=
  lsdToNat (multiplyDigits W m base hbase hsplit) base

def outVal' (W : Array Nat) (m base : Nat) (hbase : base ≥ 2)
(hsplit : 0 < m ∧ m < W.size - 1) : Nat :=
  lsdToNat (laghavaKavatasandhi W m base hbase hsplit) base


-- ============================================================
-- To prove the correctness of the iterative algorithm given above,
-- we have to create recursive equivalents to the loops, prove that
-- the iterative algorithm's behavior is equivalent to theirs,
-- and then show that the invariants hold in the recursive loops
-- (which allows us to show that the iterative version satisfies the
-- invariants as well).
-- ============================================================
/-- Inner loop of multiplyDigits -/
def innerLoop (X W : Array Nat) (yi : Nat) (i m base : Nat) (j c : Nat) : Array Nat × Nat :=
  if h : j < m then
    let k := i + j
    let (res, c') := multAndAdd (X[j]!) yi (W[k]! + c) base
    innerLoop X (W.set! k res) yi i m base (j + 1) c'
  else
    (W, c)
termination_by m - j
/-- Outer loop of multiplyDigits -/
def outerLoop (X W : Array Nat) (m n base : Nat) (i : Nat) : Array Nat :=
  if h : i < n then
    let yi := W[m + i]!
    let (W', c) := innerLoop X W yi i m base 0 0
    outerLoop X (W'.set! (i + m) c) m n base (i + 1)
  else
    W
termination_by n - i
-- ============================================================
-- Helper lemmas
-- ============================================================
lemma multAndAdd_spec (a b c base : Nat) (hbase : 0 < base) :
    let p := multAndAdd a b c base
    p.1 + p.2 * base = a * b + c := by
  exact Nat.mod_add_div' _ _



lemma lsdToNat_eq_sum (A : Array Nat) (base : Nat) :
    lsdToNat A base = ∑ i ∈ range A.size, A[i]! * base ^ i := by
  unfold lsdToNat;
  induction A.size <;> simp_all +decide [ List.range_succ ];
  simp_all +decide [ List.range'_concat, Finset.sum_range_succ ];
  rename_i k hk; exact Or.inl ( Nat.recOn k ( by norm_num ) fun n ihn => by rw [ List.range'_concat ] ; simp +decide [ ihn, pow_succ ] ) ;


-- gpt rewrote
lemma lsdToNat_set (A : Array Nat) (k v base : Nat) (hk : k < A.size) :
    lsdToNat (A.set! k v) base + A[k]! * base ^ k =
    lsdToNat A base + v * base ^ k := by
  rw [lsdToNat_eq_sum, lsdToNat_eq_sum]
  have hsize : (A.set! k v).size = A.size := by
    simp [Array.set!, Array.setIfInBounds, hk]
  rw [hsize]
  have hk' : k ∈ Finset.range A.size := Finset.mem_range.mpr hk
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem
        (s := Finset.range A.size)
        (i := k)
        (f := fun i => (A.set! k v)[i]! * base ^ i)
        hk']
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem
        (s := Finset.range A.size)
        (i := k)
        (f := fun i => A[i]! * base ^ i)
        hk']
  have hrest :
      ∑ i ∈ Finset.range A.size \ {k}, (A.set! k v)[i]! * base ^ i =
      ∑ i ∈ Finset.range A.size \ {k}, A[i]! * base ^ i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_range : i ∈ Finset.range A.size := (Finset.mem_sdiff.mp hi).1
    have hi_lt : i < A.size := Finset.mem_range.mp hi_range
    have hi_ne : i ≠ k := by
      intro hEq
      exact (Finset.mem_sdiff.mp hi).2 (by simp [hEq])
    have hget : (A.set! k v)[i]! = A[i]! := by
      simp [Array.set!, Array.setIfInBounds]
      grind +ring;
    rw [hget]
  have hself : (A.set! k v)[k]! = v := by
    simp [Array.set!, Array.setIfInBounds, hk]
  rw [hrest, hself]
  ac_rfl

lemma size_set_bang (A : Array Nat) (k v : Nat) (hk : k < A.size) :
    (A.set! k v).size = A.size := by aesop


lemma zeroPrefix_size (W : Array Nat) (m : Nat) :
    (zeroPrefix W m).size = W.size := by
  -- The zeroPrefix function preserves the size of the array because it only modifies existing elements and does not add or remove any elements.
  simp [zeroPrefix];
  induction' ( List.range' 0 ( Min.min m W.size ) ) using List.reverseRecOn with _ _ ih <;> aesop


lemma zeroPrefix_get (W : Array Nat) (m : Nat) (i : Nat) (hi : i < W.size) :
    (zeroPrefix W m)[i]! = if i < m then 0 else W[i]! := by
  unfold zeroPrefix;
  have h_foldl : ∀ (l : List ℕ) (W : Array ℕ) (i : ℕ), i < W.size → (List.foldl (fun r i => r.setIfInBounds i 0) W l)[i]! = if i ∈ l then 0 else W[i]! := by
    intros l W i hi; induction' l using List.reverseRecOn with l ih generalizing W i; aesop;
    by_cases hi' : i = ih <;> simp_all +decide [ List.foldl_append ];
    · rw [ Array.setIfInBounds ] ; aesop;
    · grind;
  simp_all +decide [ List.range' ]


lemma lsdToNat_zeroPrefix_eq (W : Array Nat) (m base : Nat) (hm : m ≤ W.size) :
    lsdToNat (zeroPrefix W m) base = base ^ m * rightVal W m base := by
  have h_split : lsdToNat (zeroPrefix W m) base = ∑ i ∈ Finset.range W.size, (zeroPrefix W m)[i]! * base ^ i := by
    rw [ lsdToNat_eq_sum, zeroPrefix_size ];
  have h_split : ∑ i ∈ Finset.range W.size, (zeroPrefix W m)[i]! * base ^ i = ∑ i ∈ Finset.Ico m W.size, W[i]! * base ^ i := by
    have h_split : ∀ i ∈ Finset.range W.size, (zeroPrefix W m)[i]! = if i < m then 0 else W[i]! := by
      exact fun i hi => zeroPrefix_get W m i ( Finset.mem_range.mp hi );
    rw [ Finset.sum_congr rfl fun i hi => by rw [ h_split i hi ] ] ; simp +decide [ Finset.sum_ite ] ;
    rcongr i ; aesop;
  have h_split : ∑ i ∈ Finset.Ico m W.size, W[i]! * base ^ i = base ^ m * ∑ i ∈ Finset.range (W.size - m), W[m + i]! * base ^ i := by
    rw [ Finset.mul_sum _ _ _, Finset.sum_Ico_eq_sum_range ];
    exact Finset.sum_congr rfl fun _ _ => by ring;
  have h_split : ∑ i ∈ Finset.range (W.size - m), W[m + i]! * base ^ i = lsdToNat (W.extract m W.size) base := by
    rw [ lsdToNat_eq_sum ];
    grind;
  aesop
/-
PROVIDED SOLUTION
By induction on m - j. Each step does set! which preserves size.
-/
lemma innerLoop_size (X W : Array Nat) (yi i m base j c : Nat)
    (him : i + m ≤ W.size) :
    (innerLoop X W yi i m base j c).1.size = W.size := by
  induction' k : m - j with k ih generalizing j c W;
  · unfold innerLoop;
    grind;
  · unfold innerLoop;
    grind +ring



lemma innerLoop_spec (X W : Array Nat) (yi i m base : Nat)
    (hXsize : X.size = m)
    (hWsize : i + m ≤ W.size)
    (hbase : 0 < base) :
    let (W', c) := innerLoop X W yi i m base 0 0
    lsdToNat W' base + c * base ^ (i + m) =
    lsdToNat W base + yi * (∑ j ∈ range m, X[j]! * base ^ j) * base ^ i := by
  have h_innerLoop_spec : ∀ (j : Nat) (c : Nat), j ≤ m → i + m ≤ W.size → let (W', c') := innerLoop X W yi i m base j c; lsdToNat W' base + c' * base ^ (i + m) = lsdToNat W base + c * base ^ (i + j) + yi * (∑ k ∈ Finset.range (m - j), X[j + k]! * base ^ k) * base ^ (i + j) := by
    intro j c hj hWsize
    induction' h : m - j with k ih generalizing j c W;
    · unfold innerLoop; simp_all +decide [ Nat.sub_eq_iff_eq_add hj ] ;
    · unfold innerLoop;
      split_ifs <;> simp_all +decide [ Nat.sub_succ, Finset.sum_range_succ' ];
      have := lsdToNat_set W ( i + j ) ( multAndAdd X[j] yi ( W[i + j]! + c ) base |>.1 ) base ( by linarith ) ; simp_all +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring;
      have := multAndAdd_spec X[j] yi ( W[i + j]! + c ) base hbase; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring;
      grind;
  simpa using h_innerLoop_spec 0 0 bot_le hWsize



lemma innerLoop_get_ge (X W : Array Nat) (yi i m base j c : Nat)
    (him : i + m ≤ W.size) (p : Nat) (hp : p ≥ i + m) :
    (innerLoop X W yi i m base j c).1[p]! = W[p]! := by
  -- By induction on $m - j$, we can show that the inner loop does not modify positions $\geq i + m$.
  induction' h : m - j with k ih generalizing j c W p;
  · unfold innerLoop;
    grind +ring;
  · unfold innerLoop;
    grind +ring



lemma inner_forIn_eq_innerLoop (X W : Array Nat) (i m base : Nat)
    (him : i + m ≤ W.size) (hm : 0 < m) :
    (Id.run do
      let mut s := (W, 0)
      for j in [0:m] do
        let k := i + j
        let (res, c') := multAndAdd (X[j]!) (s.1[m + i]!) (s.1[k]! + s.2) base
        s := (s.1.set! k res, c')
      return s)
    = innerLoop X W (W[m + i]!) i m base 0 0 := by
  convert range_forIn_eq_iterate m ( W, 0 ) _ using 1;
  -- By definition of `iterateBody`, we can show that it is equivalent to the recursive definition of `innerLoop`.
  have h_iterateBody_eq_innerLoop : ∀ (j : ℕ) (sj : Array ℕ × ℕ), j ≤ m → iterateBody (fun j r => (r.1.set! (i + j) (multAndAdd X[j]! r.1[m + i]! (r.1[i + j]! + r.2) base).1, (multAndAdd X[j]! r.1[m + i]! (r.1[i + j]! + r.2) base).2)) j (m - j) sj = innerLoop X sj.1 (sj.1[m + i]!) i m base j sj.2 := by
    intros j sj hj;
    induction' k : m - j with k ih generalizing j sj <;> simp_all +decide [ Nat.sub_succ ];
    · unfold innerLoop; simp +decide [ Nat.sub_eq_iff_eq_add hj ] ;
      rw [ Nat.sub_eq_iff_eq_add ] at k <;> aesop;
    · convert ih ( j + 1 ) _ _ ( by omega ) ( by omega ) using 1;
      rw [ innerLoop ];
      split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add hj ];
      grind +ring;
  exact Eq.symm ( h_iterateBody_eq_innerLoop 0 ( W, 0 ) ( Nat.zero_le _ ) )


lemma outerLoop_eq_foldl (X : Array Nat) (init : Array Nat) (m n base i : Nat) :
    outerLoop X init m n base i =
    List.foldl (fun W' j =>
      let yi := W'[m + j]!
      let (W'', c) := innerLoop X W' yi j m base 0 0
      W''.set! (j + m) c
    ) init (List.range' i (n - i)) := by
  induction' h : n - i with k ih generalizing i init;
  · unfold outerLoop;
    grind;
  · rw [ outerLoop, List.range' ];
    grind



/-- Helper: forIn invariant for monadic bodies in the Id monad -/
lemma forIn_id_invariant {α : Type} (n : Nat) (init : α)
    (body : Nat → α → Id (ForInStep α))
    (body' : Nat → α → α)
    (hbody : ∀ i s, body i s = ForInStep.yield (body' i s))
    (P : Nat → α → Prop)
    (h0 : P 0 init)
    (hstep : ∀ i, i < n → ∀ s, P i s → P (i + 1) (body' i s)) :
    P n (forIn (m := Id) [0:n] init body) := by
  have h : body = fun i s => ForInStep.yield (body' i s) := by
    funext i s; exact hbody i s
  rw [h]
  exact range_forIn_invariant n init body' P h0 hstep

/-- The outer loop body as a pure function -/
def outerBody (X : Array Nat) (m base : Nat) (i : Nat) (W' : Array Nat) : Array Nat :=
  Id.run do
    let mut W'' := W'
    let mut c := 0
    for j in [0:m] do
      let k := i + j
      let (res, c') := multAndAdd (X[j]!) (W''[m + i]!) (W''[k]! + c) base
      W'' := W''.set! k res
      c := c'
    return W''.set! (i + m) c

/-- Helper: extract the for loop part of outerBody as returning a pair -/
def outerBodyPair (X : Array Nat) (m base : Nat) (i : Nat) (W' : Array Nat) : Array Nat × Nat :=
  Id.run do
    let mut W'' := W'
    let mut c := 0
    for j in [0:m] do
      let k := i + j
      let (res, c') := multAndAdd (X[j]!) (W''[m + i]!) (W''[k]! + c) base
      W'' := W''.set! k res
      c := c'
    return (W'', c)

/-- outerBody uses the pair result -/
lemma outerBody_eq_pair (X : Array Nat) (m base i : Nat) (W' : Array Nat) :
    outerBody X m base i W' = (outerBodyPair X m base i W').1.set! (i + m) (outerBodyPair X m base i W').2 := by
  unfold outerBody outerBodyPair multAndAdd
  rfl



lemma outerBodyPair_eq_innerLoop (X W' : Array Nat) (m base i : Nat)
    (him : i + m ≤ W'.size) (hm : 0 < m) :
    outerBodyPair X m base i W' = innerLoop X W' (W'[m + i]!) i m base 0 0 := by
  have h_innerLoop : ∀ j c, innerLoop X W' (W'[m + i]!) i m base j c = innerLoop X (Id.run do
    let mut W'' := W'
    let mut c := c
    for j in [j:m] do
      let k := i + j
      let (res, c') := multAndAdd (X[j]!) (W''[m + i]!) (W''[k]! + c) base
      W'' := W''.set! k res
      c := c'
    return (W'', c)).1 (W'[m + i]!) i m base (m) (Id.run do
    let mut W'' := W'
    let mut c := c
    for j in [j:m] do
      let k := i + j
      let (res, c') := multAndAdd (X[j]!) (W''[m + i]!) (W''[k]! + c) base
      W'' := W''.set! k res
      c := c'
    return (W'', c)).2 := by
      intros j c
      induction' h : m - j with k hk generalizing j c W';
      · unfold innerLoop;
        split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ];
        omega;
      · rw [ innerLoop ];
        split_ifs <;> simp_all +decide [ List.range' ];
        grind;
  rw [ h_innerLoop ];
  unfold outerBodyPair; simp +decide [ hm ] ;
  unfold innerLoop; simp +decide [ hm ] ;

lemma outerBody_eq_step (X W' : Array Nat) (m base i : Nat)
    (him : i + m ≤ W'.size) (hm : 0 < m) :
    outerBody X m base i W' =
    (let (W'', c) := innerLoop X W' (W'[m + i]!) i m base 0 0
     W''.set! (i + m) c) := by
  rw [outerBody_eq_pair, outerBodyPair_eq_innerLoop X W' m base i him hm]


lemma multiplyDigits_eq_outerLoop (W : Array Nat) (m base : Nat)
    (hbase : base ≥ 2) (hsplit : 0 < m ∧ m < W.size) :
    multiplyDigits W m base hbase hsplit =
    outerLoop (W.extract 0 m) (zeroPrefix W m) m (W.size - m) base 0 := by
  -- Step 1: Show multiplyDigits = Id.run do for ... outerBody ...
  have step1 : multiplyDigits W m base hbase hsplit =
      (Id.run do
        let mut W' := zeroPrefix W m
        for i in [0:W.size - m] do
          W' := outerBody (W.extract 0 m) m base i W'
        return W') := by
    unfold multiplyDigits outerBody multAndAdd
    rfl
  -- Step 2: Convert to List.foldl using range_forIn_eq_iterate + iterateBody_eq_foldl
  rw [step1, range_forIn_eq_iterate, iterateBody_eq_foldl]
  -- Step 3: Show List.foldl outerBody = outerLoop, by showing outerLoop also equals
  -- the same List.foldl (via outerLoop_eq_foldl) with matching body functions
  rw [outerLoop_eq_foldl, show W.size - m - 0 = W.size - m by omega]
  -- Now both sides are List.foldl with the same init and range, but different bodies.
  -- LHS body: fun s i => outerBody (W.extract 0 m) m base i s
  -- RHS body: fun W' j => let yi := W'[m+j]!; let (W'',c) := innerLoop ...; W''.set!(j+m) c
  -- These agree pointwise by outerBody_eq_step (when size conditions hold).
  -- Prove by induction on the range list, maintaining size invariant.
  -- By induction on the list, we can show that the two foldl operations are equal.
  have h_foldl_eq_induction : ∀ (l : List ℕ), (∀ i ∈ l, i < W.size - m) → List.foldl (fun s i => outerBody (W.extract 0 m) m base i s) (zeroPrefix W m) l = List.foldl (fun W' j => let yi := W'[m + j]!; let (W'', c) := innerLoop (W.extract 0 m) W' yi j m base 0 0; W''.set! (j + m) c) (zeroPrefix W m) l := by
    intro l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide ;
    apply_rules [ outerBody_eq_step ];
    · -- By induction on the list `l`, we can show that the size of the array remains `W.size` after each step.
      have h_size_induction : ∀ (l : List ℕ), (∀ i ∈ l, i < W.size - m) → (List.foldl (fun W' j => (innerLoop (W.extract 0 m) W' W'[m + j]! j m base 0 0).1.setIfInBounds (j + m) (innerLoop (W.extract 0 m) W' W'[m + j]! j m base 0 0).2) (zeroPrefix W m) l).size = W.size := by
        intro l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ zeroPrefix_size ] ;
        rw [ innerLoop_size ] ; aesop;
        linarith [ hl ih ( Or.inr rfl ), Nat.sub_add_cancel hsplit.2.le ];
      linarith [ h_size_induction l fun i hi => hl i ( Or.inl hi ), Nat.sub_add_cancel hsplit.2.le, hl ih ( Or.inr rfl ) ];
    · linarith;
  grind


lemma outer_body_lsdToNat (X W' origW : Array Nat) (m base i : Nat)
    (hm : 0 < m) (hbase : 0 < base)
    (hXsize : X.size = m)
    (him : i + m + 1 ≤ W'.size)
    (hWsize : W'.size = origW.size)
    (hyi : W'[m + i]! = origW[m + i]!) :
    let inner_result := innerLoop X W' (W'[m + i]!) i m base 0 0
    let W'' := inner_result.1.set! (i + m) inner_result.2
    lsdToNat W'' base + origW[m + i]! * base ^ (m + i) =
    lsdToNat W' base + origW[m + i]! * (∑ j ∈ range m, X[j]! * base ^ j) * base ^ i := by
  -- Apply the lemma for the inner loop
  have h_inner : (innerLoop X W' (W'[m + i]!) i m base 0 0).1.size = W'.size := by
    apply innerLoop_size; linarith;
  have := innerLoop_spec X W' ( W'[m + i]! ) i m base hXsize ( by linarith ) hbase; simp_all +decide [ add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm, pow_add ] ;
  have := lsdToNat_set ( innerLoop X W' origW[m + i]! i m base 0 0 |>.1 ) ( m + i ) ( innerLoop X W' origW[m + i]! i m base 0 0 |>.2 ) base ( by
    linarith ) ; simp_all +decide [ add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm, pow_add ] ;
  have := innerLoop_get_ge X W' ( origW[m + i]! ) i m base 0 0 ( by linarith ) ( m + i ) ( by linarith ) ; simp_all +decide [ add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm, pow_add ] ;



lemma outerLoop_correct (X W₀ : Array Nat) (m n base : Nat)
    (hXsize : X.size = m) (hW₀size : W₀.size = m + n)
    (hbase : 0 < base) (hm : 0 < m) :
    lsdToNat (outerLoop X W₀ m n base 0) base =
    lsdToNat W₀ base + (∑ j ∈ range m, X[j]! * base ^ j) *
      (∑ j ∈ range n, W₀[m + j]! * base ^ j) -
    ∑ j ∈ range n, W₀[m + j]! * base ^ (m + j) := by
  -- By induction on $n - i$, we can show that the outerLoop's result satisfies the additive formula.
  have h_ind : ∀ i ≤ n, lsdToNat (outerLoop X W₀ m n base i) base + ∑ j ∈ Finset.Ico i n, W₀[m + j]! * base^(m + j) = lsdToNat W₀ base + (∑ j ∈ Finset.range m, X[j]! * base^j) * (∑ j ∈ Finset.Ico i n, W₀[m + j]! * base^j) := by
    intro i hi
    induction' h : n - i with k ih generalizing i W₀;
    · unfold outerLoop; simp_all +decide [ Nat.sub_eq_iff_eq_add' hi ] ;
    · -- By definition of `outerLoop`, we can write
      have h_outerLoop_def : outerLoop X W₀ m n base i = outerLoop X (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.1.set! (i + m) (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.2)) m n base (i + 1) := by
        rw [ outerLoop ];
        grind +ring;
      have h_innerLoop_spec : lsdToNat (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.1.set! (i + m) (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.2)) base + (W₀[m + i]!) * base ^ (m + i) = lsdToNat W₀ base + (W₀[m + i]!) * (∑ j ∈ Finset.range m, X[j]! * base ^ j) * base ^ i := by
        have h_innerLoop_spec : lsdToNat (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.1) base + (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.2) * base ^ (i + m) = lsdToNat W₀ base + (W₀[m + i]!) * (∑ j ∈ Finset.range m, X[j]! * base ^ j) * base ^ i := by
          convert innerLoop_spec X W₀ ( W₀[m + i]! ) i m base hXsize ( by linarith ) hbase using 1;
        have h_innerLoop_spec : lsdToNat ((innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.1).set! (i + m) (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.2)) base + (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.1)[i + m]! * base ^ (i + m) = lsdToNat (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.1) base + (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.2) * base ^ (i + m) := by
          have h_innerLoop_spec : ∀ (A : Array ℕ) (k v : ℕ) (hk : k < A.size), lsdToNat (A.set! k v) base + A[k]! * base ^ k = lsdToNat A base + v * base ^ k := by
            exact?;
          apply h_innerLoop_spec;
          rw [ innerLoop_size ] ; linarith [ Nat.sub_add_cancel hi ];
          linarith [ Nat.sub_add_cancel hi ];
        have h_innerLoop_spec : (innerLoop X W₀ (W₀[m + i]!) i m base 0 0 |>.1)[i + m]! = W₀[m + i]! := by
          convert innerLoop_get_ge X W₀ ( W₀[m + i]! ) i m base 0 0 _ _ _ using 1;
          · rw [ add_comm ];
          · linarith [ Nat.sub_add_cancel hi ];
          · grind;
        grind +ring;
      have := ih ( ( innerLoop X W₀ W₀[m + i]! i m base 0 0 |>.1.set! ( i + m ) ( innerLoop X W₀ W₀[m + i]! i m base 0 0 |>.2 ) ) ) ?_ ( i + 1 ) ?_ ?_ <;> simp_all +decide [ Nat.sub_succ, Finset.sum_Ico_eq_sum_range ];
      · have h_innerLoop_get_ge : ∀ x ∈ Finset.range k, ((innerLoop X W₀ W₀[m + i]! i m base 0 0).1.setIfInBounds (i + m) (innerLoop X W₀ W₀[m + i]! i m base 0 0).2)[m + (i + 1 + x)]! = W₀[m + (i + 1 + x)]! := by
          intros x hx
          have h_pos : m + (i + 1 + x) ≥ i + m := by
            grind
          have h_innerLoop_get_ge : ((innerLoop X W₀ W₀[m + i]! i m base 0 0).1)[m + (i + 1 + x)]! = W₀[m + (i + 1 + x)]! := by
            apply innerLoop_get_ge; linarith; linarith;
          have h_setIfInBounds : ((innerLoop X W₀ W₀[m + i]! i m base 0 0).1.setIfInBounds (i + m) (innerLoop X W₀ W₀[m + i]! i m base 0 0).2)[m + (i + 1 + x)]! = ((innerLoop X W₀ W₀[m + i]! i m base 0 0).1)[m + (i + 1 + x)]! := by
            grind +ring
          rw [h_setIfInBounds, h_innerLoop_get_ge];
        simp_all +decide [ Finset.sum_range_succ', pow_add ];
        grind;
      · convert innerLoop_size X W₀ W₀[m + i]! i m base 0 0 ( by linarith ) using 1 ; aesop;
      · omega;
  exact eq_tsub_of_add_eq <| by simpa using h_ind 0 bot_le;



theorem multiplyDigits_correct
(W : Array Nat) (m base : Nat)
(hbase : 2 ≤ base)
(hsplit : 0 < m ∧ m < W.size)
(hdigits : ValidDigits base W)
: outVal W m base hbase hsplit = leftVal W m base * rightVal W m base := by
  have h_meera : multiplyDigits W m base hbase hsplit = outerLoop (W.extract 0 m) (zeroPrefix W m) m (W.size - m) base 0 := by
    exact?;
  -- Let's express the lsdToNat of the outerLoop using the definitions provided.
  have h_lsdToNat_outerLoop : lsdToNat (outerLoop (W.extract 0 m) (zeroPrefix W m) m (W.size - m) base 0) base =
    base^m * rightVal W m base + (∑ j ∈ range m, W[j]! * base^j) * (∑ j ∈ range (W.size - m), W[m + j]! * base^j) - (∑ j ∈ range (W.size - m), W[m + j]! * base^(m + j)) := by
      convert outerLoop_correct (W.extract 0 m) (zeroPrefix W m) m (W.size - m) base _ _ _ _ using 1 <;> norm_num [ hsplit ];
      · congr! 2;
        · exact Eq.symm ( lsdToNat_zeroPrefix_eq W m base hsplit.2.le );
        · congr! 2;
          · grind +ring;
          · rw [ zeroPrefix_get ] ; aesop;
            grind;
        · rw [ zeroPrefix_get ] ; aesop;
          grind;
      · linarith;
      · rw [ zeroPrefix_size, add_tsub_cancel_of_le hsplit.2.le ];
      · linarith;
  -- Let's simplify the expression using the definitions of `leftVal` and `rightVal`.
  have h_simplify : base^m * rightVal W m base + (∑ j ∈ range m, W[j]! * base^j) * (∑ j ∈ range (W.size - m), W[m + j]! * base^j) =
    base^m * rightVal W m base + leftVal W m base * rightVal W m base := by
      congr! 2;
      · convert lsdToNat_eq_sum ( W.extract 0 m ) base |> Eq.symm using 1;
        simp +decide [ Array.size_extract ];
        rw [ min_eq_left hsplit.2.le ];
        refine' Finset.sum_congr rfl fun i hi => _;
        cases W ; aesop;
      · convert lsdToNat_eq_sum ( W.extract m W.size ) base using 1;
        · rw [ lsdToNat_eq_sum ];
          grind;
        · convert lsdToNat_eq_sum ( W.extract m W.size ) base using 1;
  -- Let's simplify the expression using the definition of `rightVal`.
  have h_rightVal : ∑ j ∈ range (W.size - m), W[m + j]! * base^(m + j) = base^m * rightVal W m base := by
    unfold rightVal;
    rw [ lsdToNat_eq_sum ];
    simp +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, rightDigits ];
    grind;
  unfold outVal; aesop;

theorem laghavaKavatasandhiCorrect
(W : Array Nat) (m base : Nat)
(hbase : 2 ≤ base)
(hsplit : 0 < m ∧ m < W.size - 1)
(hdigits : ValidDigits base W)
: outVal' W m base hbase hsplit = leftVal W m base * rightVal W m base := by
  simp [outVal', laghavaKavatasandhi]
  have h' : 0 < m ∧ m < W.size := by
    exact ⟨hsplit.1, Nat.lt_of_lt_of_le hsplit.2 (Nat.sub_le _ _)⟩
  exact multiplyDigits_correct W m base hbase h' hdigits
