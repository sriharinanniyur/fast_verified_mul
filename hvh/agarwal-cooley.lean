-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-- with some contribution from Opus 4.8
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

set_option grind.warning false

def ac_labels {d : ℕ} (s : List.Vector ℕ d) :
    List.Vector (List.Vector ℕ d) (∏ i, s.get i) := Id.run do
  let N : ℕ := ∏ i, s.get i
  let mut acc : List.Vector (List.Vector ℕ d) N :=
    List.Vector.replicate N (List.Vector.replicate d 0)
  for j in List.finRange N do
    if h : 0 < (j : ℕ) then
      let prev : List.Vector ℕ d := acc.get ⟨(j : ℕ) - 1, by omega⟩
      let next : List.Vector ℕ d := List.Vector.ofFn fun k =>
        if prev.get k + 1 < s.get k then prev.get k + 1 else 0
      acc := acc.set j next
  return acc

noncomputable def ac_forward
    {d : ℕ}
    (s : List.Vector ℕ d)
    [forall i, NeZero (s.get i)]
    (A : List.Vector ℂ ( ∏ i, s.get i)) :
    List.Vector (List.Vector ℕ d × ℂ) (∏ i, s.get i) :=
  let labels := ac_labels s
  let tape : List (List.Vector ℕ d × ℂ) :=
    (List.finRange ( ∏ i, s.get i)).map fun l => (labels.get l, A.get l)
  let by_label := fun p q => decide (toLex p.1.get ≤ toLex q.1.get)
  ⟨tape.mergeSort by_label, by
    simp only [tape, List.length_mergeSort, List.length_map, List.length_finRange]⟩

noncomputable def ac_backward
    {d : ℕ}
    (s : List.Vector ℕ d)
    [forall i, NeZero (s.get i)]
    (T : List.Vector (List.Vector ℕ d × ℂ) (∏ i, s.get i)) :
    List.Vector ℂ (∏ i, s.get i) :=
  let N : ℕ := ∏ i, s.get i
  let recover_l : List.Vector ℕ d → ZMod N :=
    fun L => ∑ k,
      let t_k : ℕ := N / s.get k
      (L.get k * t_k * (t_k : ZMod (s.get k))⁻¹.val : ZMod N)
  let tagged : List (ℕ × ℂ) :=
    T.toList.map fun p => ((recover_l p.1).val, p.2)
  let sorted : List (ℕ × ℂ) :=
    tagged.mergeSort fun x y => decide (x.1 ≤ y.1)
  ⟨sorted.map Prod.snd, by
    simp only [sorted, tagged, List.length_map, List.length_mergeSort, T.toList_length]⟩

-- BEGIN PROOFS


-- proof aid; characterization
noncomputable def acRecover {d : ℕ} (s : List.Vector ℕ d) (L : List.Vector ℕ d) :
    ZMod (∏ i, s.get i) :=
  ∑ k,
    let t_k : ℕ := (∏ i, s.get i) / s.get k
    (L.get k * t_k * (t_k : ZMod (s.get k))⁻¹.val : ZMod (∏ i, s.get i))

/-
Characterisation of the imperative label generator: the `j`-th label is the mixed–radix
    (CRT) digit vector `k ↦ j % s_k`.
-/
theorem ac_labels_get
    {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (j : Fin (∏ i, s.get i)) :
    (ac_labels s).get j = List.Vector.ofFn (fun k => (j : ℕ) % s.get k) := by
  revert j;
  -- Unfold `ac_labels` to the `Id.run`/`forIn` monadic loop, then rewrite `List.idRun_forIn_yield_eq_foldl` (or `List.forIn_pure_yield_eq_foldl` if `yield` is entirely eliminated) to convert it to a `List.foldl` over `List.finRange N` with the given `step` function.
  unfold ac_labels at *;
  simp [Id.run] at *;
  have h_step : ∀ (m : ℕ) (hm : m ≤ ∏ i, s.get i) (j : Fin (∏ i, s.get i)), j.val < m → (List.foldl (fun (acc : List.Vector (List.Vector ℕ d) (∏ i, s.get i)) (j : Fin (∏ i, s.get i)) => if h : 0 < j.val then acc.set j (List.Vector.ofFn fun k => if (acc.get ⟨j.val - 1, by omega⟩).get k + 1 < s.get k then (acc.get ⟨j.val - 1, by omega⟩).get k + 1 else 0) else acc) (List.Vector.replicate (∏ i, s.get i) (List.Vector.replicate d 0)) (List.take m (List.finRange (∏ i, s.get i)))).get j = List.Vector.ofFn (fun k => j.val % s.get k) := by
    intro m hm j hj
    induction' m with m ih generalizing j;
    · grind;
    · by_cases hj' : j.val < m;
      · rw [ List.take_add_one ];
        grind +suggestions;
      · simp_all +decide [ show j = ⟨ m, by linarith ⟩ from Fin.ext ( by linarith ) ];
        rw [ List.take_add_one ];
        simp +decide [ hm ];
        split_ifs <;> simp_all +decide [ List.Vector.get_set_same ];
        · ext k; simp +decide [ ih ( Nat.le_of_succ_le hm ) ⟨ m - 1, by omega ⟩ ( Nat.sub_lt ( by linarith ) zero_lt_one ) ] ;
          split_ifs <;> simp_all +decide;
          · rcases m with ( _ | m ) <;> simp_all +decide;
            rw [ Nat.add_mod ];
            rcases n : s.get k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ];
          · rw [ Nat.mod_eq_zero_of_dvd ];
            exact ⟨ ( m - 1 ) / s.get k + 1, by linarith [ Nat.mod_add_div ( m - 1 ) ( s.get k ), Nat.sub_add_cancel ( by linarith : 1 ≤ m ), Nat.mod_lt ( m - 1 ) ( NeZero.pos ( s.get k ) ) ] ⟩;
        · aesop;
  convert h_step ( ∏ i, s.get i ) le_rfl using 1;
  rw [ List.take_of_length_le ( by simp +decide ) ];
  rw [ forIn_eq_forIn' ];
  rw [ forIn'_eq_forIn ];
  rotate_left;
  use fun j acc => pure ( ForInStep.yield ( if h : 0 < j.val then acc.set j ( List.Vector.ofFn fun k => if ( acc.get ⟨ j.val - 1, by omega ⟩ ).get k + 1 < s.get k then ( acc.get ⟨ j.val - 1, by omega ⟩ ).get k + 1 else 0 ) else acc ) );
  · aesop;
  · simp +decide [ Fin.is_lt ];
    rfl

/-
`N / s_k = ∏_{i ≠ k} s_i`.
-/
theorem prod_div_get
    {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)] (k : Fin d) :
    (∏ i, s.get i) / s.get k = ∏ i ∈ Finset.univ.erase k, s.get i := by
  exact Nat.div_eq_of_eq_mul_left ( NeZero.pos _ ) ( by rw [ ← Finset.prod_erase_mul _ _ ( Finset.mem_univ k ) ] )

/-
Reducing `acRecover s L` modulo `s_m` recovers the `m`-th digit.
-/
theorem acRecover_castHom
    {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (h : Pairwise (Function.onFun Nat.Coprime s.get))
    (L : List.Vector ℕ d) (m : Fin d) :
    (ZMod.castHom (Finset.dvd_prod_of_mem s.get (Finset.mem_univ m)) (ZMod (s.get m)))
        (acRecover s L) = (L.get m : ZMod (s.get m)) := by
  generalize_proofs at *;
  unfold acRecover; simp +decide [ * ] ;
  rw [ Finset.sum_eq_single m ];
  · have h_inv : Nat.Coprime ((∏ i, s.get i) / s.get m) (s.get m) := by
      rw [ prod_div_get ];
      exact Nat.Coprime.prod_left fun i hi => h <| by aesop;
    have h_inv : (↑((∏ i, s.get i) / s.get m) : ZMod (s.get m)) * (↑((∏ i, s.get i) / s.get m) : ZMod (s.get m))⁻¹ = 1 := by
      exact ZMod.coe_mul_inv_eq_one ((∏ i, s.get i) / s.get m) h_inv
    grind +suggestions;
  · intro i hi him; simp +decide [ Finset.prod_eq_prod_diff_singleton_mul hi, Nat.mul_div_cancel _ ( NeZero.pos ( s.get i ) ) ] ;
    rw [ Finset.prod_eq_zero ( Finset.mem_sdiff.mpr ⟨ Finset.mem_univ m, by aesop ⟩ ) ] <;> aesop;
  · aesop

/-
Two residues mod `N = ∏ s_i` (pairwise coprime) that agree modulo every `s_m` are equal.
-/
theorem zmod_prod_ext
    {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (h : Pairwise (Function.onFun Nat.Coprime s.get))
    (x y : ZMod (∏ i, s.get i))
    (hxy : ∀ m : Fin d,
      (ZMod.castHom (Finset.dvd_prod_of_mem s.get (Finset.mem_univ m)) (ZMod (s.get m))) x
        = (ZMod.castHom (Finset.dvd_prod_of_mem s.get (Finset.mem_univ m)) (ZMod (s.get m))) y) :
    x = y := by
  -- By definition of $N$, we know that $x - y$ is divisible by $N$.
  have h_div : (∏ i, s.get i) ∣ (x - y).val := by
    have h_div : ∀ m : Fin d, s.get m ∣ (x - y).val := by
      intro m; specialize hxy m; simp_all +decide;
      rw [ ← ZMod.natCast_eq_zero_iff ];
      convert sub_eq_zero.mpr hxy using 1;
      convert ZMod.natCast_val ( x - y ) using 1;
      · convert rfl;
        convert RingHom.map_sub ( ZMod.castHom ( Finset.dvd_prod_of_mem s.get ( Finset.mem_univ m ) ) ( ZMod ( s.get m ) ) ) x y using 1;
      · exact ⟨ Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne _ ⟩;
    convert Finset.lcm_dvd fun i _ => h_div i using 1;
    have h_lcm : ∀ {S : Finset (Fin d)}, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (s.get i) (s.get j)) → Finset.lcm S s.get = ∏ i ∈ S, s.get i := by
      intros S hS; induction' S using Finset.induction with i S hi ih; aesop;
      rw [ Finset.lcm_insert, Finset.prod_insert hi, ih fun i hi j hj hij => hS i ( Finset.mem_insert_of_mem hi ) j ( Finset.mem_insert_of_mem hj ) hij ];
      exact Nat.Coprime.lcm_eq_mul <| Nat.Coprime.prod_right fun j hj => hS i ( Finset.mem_insert_self _ _ ) j ( Finset.mem_insert_of_mem hj ) <| by aesop;
    exact Eq.symm ( h_lcm fun i hi j hj hij => h hij );
  have h_eq : (x - y).val = 0 := by
    convert Nat.eq_zero_of_dvd_of_lt h_div _;
    convert ZMod.val_lt ( x - y );
    exact ⟨ Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne _ ⟩;
  simp_all +decide [ sub_eq_iff_eq_add ]

/-
The CRT reconstruction of the digit vector `k ↦ a % s_k` is `a (mod N)`.
-/
theorem acRecover_ofFn_mod
    {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (h : Pairwise (Function.onFun Nat.Coprime s.get)) (a : ℕ) :
    acRecover s (List.Vector.ofFn (fun k => a % s.get k))
      = (a : ZMod (∏ i, s.get i)) := by
  apply zmod_prod_ext s h;
  intro m; rw [ acRecover_castHom s h ] ; simp +decide [ ZMod.natCast_mod ] ;

/-
The two directions are mutually inverse (correctness of the reduction), under pairwise
    coprimality of the moduli. Length is enforced by the `Vector` types, so no length
    hypotheses appear.
-/
theorem ac_forward_backward
    {d : ℕ}
    (s : List.Vector ℕ d)
    [forall i, NeZero (s.get i)]
    (h : Pairwise (Function.onFun Nat.Coprime s.get))
    (A : List.Vector ℂ (∏ i, s.get i)) :
    ac_backward s (ac_forward s A) = A := by
      -- After unfolding, the goal is:
      -- `(((tape.mergeSort by_label).map g).mergeSort keyle).map Prod.snd = A.toList`.
      -- Use `List.eq_of_perm_of_sorted` (a.k.a. `List.Perm.eq_of_pairwise`) for the mergesort equality.
      have h_perm : List.Perm (((List.finRange (∏ i, s.get i)).map (fun l => ((ac_labels s).get l, A.get l))).mergeSort (fun p q => decide (toLex p.1.get ≤ toLex q.1.get)) |>.map (fun p => ((acRecover s p.1).val, p.2))) (List.map (fun l : Fin (∏ i, s.get i) => ((l.val : ℕ), A.get l)) (List.finRange (∏ i, s.get i))) := by
        convert List.Perm.map _ ( List.mergeSort_perm _ _ ) using 1;
        simp +decide [ ac_labels_get, acRecover_ofFn_mod s h ];
        exact fun a => by rw [ Nat.mod_eq_of_lt a.2 ] ;
      have h_sorted : List.Pairwise (fun x y => x.1 ≤ y.1) (List.map (fun l : Fin (∏ i, s.get i) => ((l.val : ℕ), A.get l)) (List.finRange (∏ i, s.get i))) := by
        rw [ List.pairwise_iff_get ];
        intro i j hij
        simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
        exact Nat.le_of_lt hij
      have h_eq : List.mergeSort (List.map (fun p => ((acRecover s p.1).val, p.2)) (List.mergeSort (List.map (fun l => ((ac_labels s).get l, A.get l)) (List.finRange (∏ i, s.get i))) (fun p q => decide (toLex p.1.get ≤ toLex q.1.get)))) (fun x y => decide (x.1 ≤ y.1)) = List.map (fun l : Fin (∏ i, s.get i) => ((l.val : ℕ), A.get l)) (List.finRange (∏ i, s.get i)) := by
        apply_rules [ List.Perm.eq_of_pairwise ];
        · intro a b ha hb hab hba
          have hperm : List.Perm (List.mergeSort (List.map (fun p => ((acRecover s p.1).val, p.2)) (List.mergeSort (List.map (fun l => ((ac_labels s).get l, A.get l)) (List.finRange (∏ i, s.get i))) (fun p q => decide (toLex p.1.get ≤ toLex q.1.get)))) (fun x y => decide (x.1 ≤ y.1))) (List.map (fun l : Fin (∏ i, s.get i) => ((l.val : ℕ), A.get l)) (List.finRange (∏ i, s.get i))) :=
            List.Perm.trans ( List.mergeSort_perm _ _ ) h_perm
          have ha' := hperm.mem_iff.mp ha
          simp only [List.mem_map, List.mem_finRange, true_and] at ha' hb
          obtain ⟨la, rfl⟩ := ha'
          obtain ⟨lb, rfl⟩ := hb
          have : la = lb := by
            apply Fin.ext
            omega
          rw [this]
        · convert List.pairwise_mergeSort _ _ _ using 1; all_goals grind;
        · exact List.Perm.trans ( List.mergeSort_perm _ _ ) h_perm;
      refine' List.Vector.toList_injective _;
      convert congr_arg ( fun l => l.map Prod.snd ) h_eq using 1;
      refine' List.ext_get _ _ <;> aesop

open scoped BigOperators

/-- The tape-address assigned to source index `l`: the row-major linear address of the grid
    cell `(l mod s₁,…,l mod s_d)`, namely `∑ₙ (l mod sₙ) · ∏_{p>n} sₚ`. -/
def tape_addr {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (l : Fin (∏ i, s.get i)) : ℕ :=
  ∑ n : Fin d, ((l : ℕ) % s.get n) * ∏ p ∈ Finset.univ.filter (n < ·), s.get p

/-
Telescoping identity: the maximal mixed-radix number is `N - 1`.
-/
theorem tape_tele_full {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)] :
    (∑ n : Fin d, (s.get n - 1) * ∏ p ∈ Finset.univ.filter (n < ·), s.get p) + 1
      = ∏ i, s.get i := by
  induction d with
  | zero => simp
  | succ d hd =>
    -- The `NeZero` instances transfer to the tail.
    haveI htail : ∀ i : Fin d, NeZero (s.tail.get i) := fun i => by
      rw [List.Vector.get_tail_succ]; infer_instance
    -- Abbreviation for the product over the tail entries.
    set P : ℕ := ∏ i : Fin d, s.get i.succ with hP
    -- Every filtered product splits off its (trivial) `p = 0` factor.
    have hsplit : ∀ (m : Fin (d + 1)),
        (∏ p ∈ Finset.univ.filter (m < ·), s.get p)
          = ∏ q : Fin d, if m < q.succ then s.get q.succ else 1 := by
      intro m
      rw [Finset.prod_filter, Fin.prod_univ_succ]
      simp
    -- Split the sum into its head term (`n = 0`) and the tail.
    rw [Fin.sum_univ_succ]
    -- The head product equals `P`.
    have hhead : (∏ p ∈ Finset.univ.filter ((0 : Fin (d + 1)) < ·), s.get p) = P := by
      rw [hsplit]
      exact Finset.prod_congr rfl (fun q _ => by simp [Fin.succ_pos])
    -- The tail sum matches the inductive hypothesis applied to `s.tail`.
    have htailsum :
        (∑ n : Fin d, (s.get n.succ - 1) *
            ∏ p ∈ Finset.univ.filter (n.succ < ·), s.get p)
          = ∑ n : Fin d, (s.tail.get n - 1) *
              ∏ p ∈ Finset.univ.filter (n < ·), s.tail.get p := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [List.Vector.get_tail_succ, hsplit, Finset.prod_filter]
      refine congrArg _ (Finset.prod_congr rfl (fun q _ => ?_))
      rw [List.Vector.get_tail_succ]
      simp [Fin.succ_lt_succ_iff]
    rw [hhead, htailsum]
    -- The inductive hypothesis for `s.tail`, with its product rewritten in terms of `P`.
    have hih := @hd s.tail htail
    have hPtail : (∏ i : Fin d, s.tail.get i) = P :=
      Finset.prod_congr rfl (fun i _ => by rw [List.Vector.get_tail_succ])
    -- Combine the inductive hypothesis with the product rewriting, avoiding a fragile `rw`.
    have key : (∑ n : Fin d, (s.tail.get n - 1) *
              ∏ p ∈ Finset.univ.filter (n < ·), s.tail.get p) + 1 = P := hih.trans hPtail
    have hpos : 1 ≤ s.get 0 := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    rw [Fin.prod_univ_succ]
    calc (s.get 0 - 1) * P +
            (∑ n : Fin d, (s.tail.get n - 1) *
              ∏ p ∈ Finset.univ.filter (n < ·), s.tail.get p) + 1
        = (s.get 0 - 1) * P +
            ((∑ n : Fin d, (s.tail.get n - 1) *
              ∏ p ∈ Finset.univ.filter (n < ·), s.tail.get p) + 1) := by ring
      _ = (s.get 0 - 1) * P + P := by rw [key]
      _ = s.get 0 * P := by
          rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left P hpos)]

/-
Telescoping identity for a strict suffix: `∑_{n>m} (sₙ-1)·∏_{p>n} sₚ + 1 = ∏_{p>m} sₚ`.
-/
theorem tape_tele_suffix {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (m : Fin d) :
    (∑ n ∈ Finset.univ.filter (m < ·),
        (s.get n - 1) * ∏ p ∈ Finset.univ.filter (n < ·), s.get p) + 1
      = ∏ p ∈ Finset.univ.filter (m < ·), s.get p := by
        -- By definition of Finset.Ioi, we can rewrite the sum as a sum over the complement of {m}.
        have h_compl : (∑ n ∈ Finset.Ioi m, (s.get n - 1) * ∏ p ∈ Finset.Ioi n, s.get p) + 1 = ∏ p ∈ Finset.Ioi m, s.get p := by
          induction' m with m ih;
          induction' h : d - m using Nat.strong_induction_on with k ih generalizing m;
          by_cases hm : m + 1 < d;
          · rw [ show ( Finset.Ioi ⟨ m, ih ⟩ : Finset ( Fin d ) ) = Finset.Ioi ⟨ m + 1, hm ⟩ ∪ { ⟨ m + 1, hm ⟩ } from ?_, Finset.sum_union ] <;> norm_num;
            · rename_i h';
              rw [ show ( Finset.Ici ⟨ m + 1, hm ⟩ : Finset ( Fin d ) ) = Finset.Ioi ⟨ m + 1, hm ⟩ ∪ { ⟨ m + 1, hm ⟩ } from ?_, Finset.prod_union ] <;> norm_num;
              specialize h' ( d - ( m + 1 ) ) ( by omega ) ( m + 1 ) hm rfl;
              nlinarith [ Nat.sub_add_cancel ( show 1 ≤ s.get ⟨ m + 1, hm ⟩ from Nat.pos_of_ne_zero ( NeZero.ne _ ) ), show ∏ p ∈ Finset.Ioi ⟨ m + 1, hm ⟩, s.get p > 0 from Finset.prod_pos fun p hp => Nat.pos_of_ne_zero ( NeZero.ne _ ) ];
            · ext ⟨ n, hn ⟩ ; simp +decide;
          · simp +decide [ show m = d - 1 by omega ];
            rcases d with ( _ | _ | d ) <;> simp_all +decide [ Fin.ext_iff ];
            contradiction;
        convert h_compl using 1;
        · rcongr n ; aesop;
          simp +decide [ Finset.mem_Ioi ];
        · rcongr p ; aesop

/-
`tape_addr` lands in `{0,…,N-1}`, so it indexes the length-`N` tape.
-/
theorem tape_addr_lt {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (l : Fin (∏ i, s.get i)) : tape_addr s l < ∏ i, s.get i := by
      have := tape_tele_full s;
      exact lt_of_le_of_lt ( Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ ( Nat.le_sub_one_of_lt ( Nat.mod_lt _ ( NeZero.pos _ ) ) ) ) ( by omega )

/-
CRT injectivity at the residue level: two indices with the same residues everywhere are
    equal.
-/
theorem index_eq_of_res_eq {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (h : Pairwise (Function.onFun Nat.Coprime s.get))
    (l l' : Fin (∏ i, s.get i))
    (hres : ∀ k, (l : ℕ) % s.get k = (l' : ℕ) % s.get k) : l = l' := by
      refine' Fin.ext _;
      have h_eq : (l : ZMod (∏ i, s.get i)) = (l' : ZMod (∏ i, s.get i)) := by
        apply zmod_prod_ext s h;
        simp_all +decide [ ZMod.natCast_eq_natCast_iff' ];
      convert congr_arg ( fun x : ZMod ( ∏ i, s.get i ) => x.val ) h_eq using 1;
      · exact Eq.symm ( ZMod.val_cast_of_lt l.2 );
      · erw [ ZMod.val_cast_of_lt ] ; simp +decide [ Fin.is_lt ]

/-
Order preservation: strict lexicographic order of residue cells implies strict order of
    tape addresses.
-/
theorem tape_addr_lt_of_lex {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (l l' : Fin (∏ i, s.get i))
    (hlex : toLex (fun k => (l : ℕ) % s.get k) < toLex (fun k => (l' : ℕ) % s.get k)) :
    tape_addr s l < tape_addr s l' := by
      -- By definition of `toLex`, there exists some `i` such that `l % s.get i < l' % s.get i` and for all `j < i`, `l % s.get j = l' % s.get j`.
      obtain ⟨i, hi⟩ : ∃ i : Fin d, (l.val % s.get i) < (l'.val % s.get i) ∧ ∀ j : Fin d, j < i → (l.val % s.get j) = (l'.val % s.get j) := by
        by_contra hcontr;
        exact hlex.elim fun i hi => hcontr ⟨ i, hi.2, fun j hj => by have := hi.1 j hj; aesop ⟩;
      -- Let $W_n = \prod_{p \in \text{Ioi } n} s_p$.
      set W : Fin d → ℕ := fun n => ∏ p ∈ Finset.univ.filter (n < ·), s.get p;
      -- Split the sum into three parts: before `i`, at `i`, and after `i`.
      have h_split : ∑ n : Fin d, (l.val % s.get n) * W n = (∑ n ∈ Finset.Iio i, (l.val % s.get n) * W n) + (l.val % s.get i) * W i + (∑ n ∈ Finset.Ioi i, (l.val % s.get n) * W n) ∧ ∑ n : Fin d, (l'.val % s.get n) * W n = (∑ n ∈ Finset.Iio i, (l'.val % s.get n) * W n) + (l'.val % s.get i) * W i + (∑ n ∈ Finset.Ioi i, (l'.val % s.get n) * W n) := by
        constructor <;> rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ i ), add_comm ];
        · rw [ show ( Finset.univ.erase i : Finset ( Fin d ) ) = Finset.Iio i ∪ Finset.Ioi i from ?_, Finset.sum_union ] <;> norm_num [ add_comm, add_left_comm, add_assoc ];
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => lt_asymm ( Finset.mem_Iio.mp hx₁ ) ( Finset.mem_Ioi.mp hx₂ );
          · ext j; simp [Finset.mem_erase, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi];
        · rw [ show ( Finset.univ.erase i : Finset ( Fin d ) ) = Finset.Iio i ∪ Finset.Ioi i from ?_, Finset.sum_union ] <;> norm_num [ add_comm, add_left_comm, add_assoc ];
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => lt_asymm ( Finset.mem_Iio.mp hx₁ ) ( Finset.mem_Ioi.mp hx₂ );
          · ext j; simp [Finset.mem_erase, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi];
      -- Bound the `l`-side tail. Since `r n ≤ s.get n - 1` (as `r n = (l:ℕ) % s.get n < s.get n`), `∑ n ∈ Finset.Ioi i, r n * W n ≤ ∑ n ∈ Finset.Ioi i, (s.get n - 1) * W n = W i - 1` by `tape_tele_suffix s i` (note `Finset.univ.filter (i < ·) = Finset.Ioi i` and `W i = ∏ p ∈ Finset.Ioi i, s.get p`). Hence `∑ n ∈ Finset.Ioi i, r n * W n < W i`.
      have h_tail_bound : ∑ n ∈ Finset.Ioi i, (l.val % s.get n) * W n < W i := by
        have h_tail_bound : ∑ n ∈ Finset.Ioi i, (s.get n - 1) * W n + 1 = W i := by
          convert tape_tele_suffix s i using 1;
          rcongr n ; aesop;
        exact lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => Nat.mul_le_mul_right _ ( Nat.le_sub_one_of_lt ( Nat.mod_lt _ ( NeZero.pos _ ) ) ) ) ( by linarith );
      -- Combine the inequalities to conclude the proof.
      have h_final : (∑ n ∈ Finset.Iio i, (l.val % s.get n) * W n) + (l.val % s.get i) * W i + (∑ n ∈ Finset.Ioi i, (l.val % s.get n) * W n) < (∑ n ∈ Finset.Iio i, (l'.val % s.get n) * W n) + (l'.val % s.get i) * W i := by
        rw [ Finset.sum_congr rfl fun j hj => by rw [ hi.2 j ( Finset.mem_Iio.mp hj ) ] ];
        nlinarith [ Nat.zero_le ( ∑ n ∈ Finset.Ioi i, ( l : ℕ ) % s.get n * W n ), Nat.zero_le ( ∑ n ∈ Finset.Ioi i, ( l' : ℕ ) % s.get n * W n ), show 0 < W i from Finset.prod_pos fun j hj => Nat.pos_of_ne_zero ( NeZero.ne _ ) ];
      grind +locals

/-
`tape_addr` is injective.
-/
theorem tape_addr_inj {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (h : Pairwise (Function.onFun Nat.Coprime s.get))
    (l l' : Fin (∏ i, s.get i)) (heq : tape_addr s l = tape_addr s l') : l = l' := by
      contrapose! heq;
      -- By the contrapositive of `index_eq_of_res_eq s h`, there is some `k` with `(l:ℕ) % s.get k ≠ (l':ℕ) % s.get k`.
      obtain ⟨k, hk⟩ : ∃ k : Fin d, (l : ℕ) % s.get k ≠ (l' : ℕ) % s.get k := by
        exact not_forall.mp fun h' => heq <| index_eq_of_res_eq s h l l' h';
      -- Since `toLex` is injective, we have `toLex (fun k => (l:ℕ) % s.get k) ≠ toLex (fun k => (l':ℕ) % s.get k)`.
      have h_toLex_ne : toLex (fun k => (l : ℕ) % s.get k) ≠ toLex (fun k => (l' : ℕ) % s.get k) := by
        exact fun h => hk <| by simpa using congr_arg ( fun f => f k ) h;
      cases lt_or_gt_of_ne h_toLex_ne <;> [ exact ne_of_lt ( tape_addr_lt_of_lex s l l' ‹_› ) ; exact ne_of_gt ( tape_addr_lt_of_lex s l' l ‹_› ) ]

/-
Order preservation (non-strict): `tape_addr l ≤ tape_addr l'` implies lex order of the
    residue cells.
-/
theorem lex_le_of_tape_addr_le {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (l l' : Fin (∏ i, s.get i)) (hle : tape_addr s l ≤ tape_addr s l') :
    toLex (fun k => (l : ℕ) % s.get k) ≤ toLex (fun k => (l' : ℕ) % s.get k) := by
      -- By contradiction, assume that `toLex (fun k => (l:ℕ) % s.get k) > toLex (fun k => (l':ℕ) % s.get k)`.
      by_contra h_contra;
      exact hle.not_gt <| tape_addr_lt_of_lex s l' l <| lt_of_not_ge h_contra

/-
`tape_addr` is surjective onto `{0,…,N-1}`.
-/
theorem tape_addr_surj {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (h : Pairwise (Function.onFun Nat.Coprime s.get))
    (q : Fin (∏ i, s.get i)) : ∃ l : Fin (∏ i, s.get i), tape_addr s l = (q : ℕ) := by
      -- Consider the endofunction `F : Fin (∏ i, s.get i) → Fin (∏ i, s.get i)`, `F l = ⟨tape_addr s l, tape_addr_lt s l⟩`.
      set F : Fin (∏ i, s.get i) → Fin (∏ i, s.get i) := fun l => ⟨tape_addr s l, tape_addr_lt s l⟩;
      -- Since `F` is injective, it is surjective.
      have h_surjective : Function.Surjective F := by
        have h_injective : Function.Injective F := by
          exact fun a b hab => tape_addr_inj s h a b <| by injection hab;
        exact Finite.injective_iff_surjective.mp h_injective;
      exact Exists.elim ( h_surjective q ) fun l hl => ⟨ l, by aesop ⟩

/-
The sorted forward tape at position `tape_addr s l` is exactly `(residue cell of l, A l)`.
-/
theorem ac_forward_get {d : ℕ} (s : List.Vector ℕ d) [forall i, NeZero (s.get i)]
    (h : Pairwise (Function.onFun Nat.Coprime s.get))
    (A : List.Vector ℂ (∏ i, s.get i)) (l : Fin (∏ i, s.get i)) :
    (ac_forward s A).get ⟨tape_addr s l, tape_addr_lt s l⟩
      = (List.Vector.ofFn (fun k => (l : ℕ) % s.get k), A.get l) := by
        -- Define the function F that maps each index l to the pair (residue cell of l, A l).
        set F : Fin (∏ i, s.get i) → (List.Vector ℕ d) × ℂ := fun l => (List.Vector.ofFn (fun k => (l : ℕ) % s.get k), A.get l);
        set sorted := (ac_forward s A).toList with hsorted_def
        set L_exp := (List.finRange (∏ i, s.get i)).map (fun q => F (Classical.choose (tape_addr_surj s h q))) with hL_exp_def;
        have h_sorted_eq_L_exp : sorted = L_exp := by
          apply List.Perm.eq_of_pairwise;
          case le => exact fun p q => toLex p.1.get ≤ toLex q.1.get;
          · intros a b ha hb hab hba
            obtain ⟨la, rfl⟩ : ∃ la : Fin (∏ i, s.get i), a = F la := by
              simp +zetaDelta at *;
              unfold ac_forward at ha; simp_all +decide [ List.mem_map, List.mem_finRange ] ;
              obtain ⟨ la, rfl ⟩ := ha; use la; simp +decide [ ac_labels_get ] ;
            obtain ⟨lb, rfl⟩ : ∃ lb : Fin (∏ i, s.get i), b = F lb := by
              grind
            have h_eq : toLex (fun k => (la : ℕ) % s.get k) = toLex (fun k => (lb : ℕ) % s.get k) := by
              convert le_antisymm hab hba using 1; all_goals exact congr_arg _ ( funext fun k => by simp +decide [ F, List.Vector.get_ofFn ] )
            have h_eq' : la = lb := by
              exact index_eq_of_res_eq s h la lb fun k => by simpa using congr_arg ( fun f => f k ) h_eq;
            aesop;
          · convert List.pairwise_mergeSort _ _ _ using 1; all_goals grind;
          · rw [ List.pairwise_iff_get ];
            intro i j hij;
            have h_tape_addr_le : tape_addr s (Classical.choose (tape_addr_surj s h ⟨i, by
              exact i.2.trans_le ( by simp +decide [ L_exp ] )⟩)) ≤ tape_addr s (Classical.choose (tape_addr_surj s h ⟨j, by
              exact j.2.trans_le ( by simp +decide [ L_exp ] )⟩)) := by
              grind
            generalize_proofs at *;
            convert lex_le_of_tape_addr_le s _ _ h_tape_addr_le using 1; all_goals aesop;
          · have h_perm : List.Perm sorted (List.map F (List.finRange (∏ i, s.get i))) := by
              convert List.mergeSort_perm _ _ using 1;
              exact List.map_congr_left fun x hx => by rw [ ac_labels_get ] ;
            refine' h_perm.trans _;
            have h_perm : List.Perm (List.finRange (∏ i, s.get i)) (List.map (fun q => Classical.choose (tape_addr_surj s h q)) (List.finRange (∏ i, s.get i))) := by
              have h_perm : Function.Bijective (fun q : Fin (∏ i, s.get i) => Classical.choose (tape_addr_surj s h q)) := by
                have h_inj : Function.Injective (fun q : Fin (∏ i, s.get i) => Classical.choose (tape_addr_surj s h q)) := by
                  intro q q' h_eq;
                  grind +revert;
                exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩;
              rw [ List.perm_iff_count ];
              intro a; rw [ List.count_eq_one_of_mem, List.count_eq_one_of_mem ] <;> norm_num [ h_perm.injective.eq_iff ] ;
              · exact List.Nodup.map ( fun x y hxy => by simpa [ Fin.ext_iff ] using h_perm.injective hxy ) ( List.nodup_finRange _ );
              · exact h_perm.surjective a;
              · exact List.nodup_finRange _;
            convert h_perm.map F using 1;
            aesop;
        have hlist : (ac_forward s A).toList = L_exp := h_sorted_eq_L_exp
        have hchoose : Classical.choose (tape_addr_surj s h ⟨tape_addr s l, tape_addr_lt s l⟩) = l := by
          apply tape_addr_inj s h
          simpa using Classical.choose_spec (tape_addr_surj s h ⟨tape_addr s l, tape_addr_lt s l⟩)
        rw [List.Vector.get_eq_get_toList, List.get_eq_getElem, List.getElem_of_eq hlist]
        simp only [hL_exp_def, List.getElem_map, List.getElem_finRange, Fin.val_cast]
        rw [hchoose]


theorem ac_index_mapping
    {d : ℕ}
    (s : List.Vector ℕ d)
    [forall i, NeZero (s.get i)]
    (h : Pairwise (Function.onFun Nat.Coprime s.get))
    (A : List.Vector ℂ ( ∏ i, s.get i)) :
    let N := ∏ i, s.get i
    -- claim 1: correct coefficient at position M(l)
    (forall l : Fin N,
        ((ac_forward s A).get ⟨tape_addr s l, tape_addr_lt s l ⟩).2 = A.get l)
    ∧
    -- claim 2: correct label at position M(l)
    (forall (l : Fin N) (k : Fin d),
        (((ac_forward s A).get ⟨tape_addr s l, tape_addr_lt s l ⟩).1).get k
          = (l : ℕ) % s.get k)
    ∧
    -- claim 3: injectivity of index mapping
    (forall l l' : Fin N, tape_addr s l = tape_addr s l' → l = l')
    ∧
    -- claim 4: surjectivity of index mapping
    (forall q : Fin N, ∃ l : Fin N, tape_addr s l = (q : ℕ)) := by
  refine' ⟨ _, _, _, _ ⟩;
  · intro l
    have := ac_forward_get s h A l
    generalize_proofs at *;
    exact this.symm ▸ rfl;
  · intro l k; rw [ ac_forward_get s h A l ] ; simp +decide [ List.Vector.get_ofFn ] ;
  · exact tape_addr_inj s h
  · convert tape_addr_surj s h using 1
