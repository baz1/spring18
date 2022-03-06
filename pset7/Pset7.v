(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 7 *)

Require Import Frap Pset7Sig.

Ltac elimc var := elim var; clear var.
Ltac pinvert expr := pose (pinvert_tmp := expr); invert pinvert_tmp.

Lemma strong_induction0 {P: nat -> Prop} :
    P O ->
    (forall n:nat, n <> 0 -> (forall p:nat, p < n -> P p) -> P n) ->
    forall n:nat, (forall p:nat, p < n -> P p).
Proof.
  intros P0 rec n; elimc n.
  (* O *)
    intros p absurd; discriminate (le_n_0_eq _ absurd).
  (* S p *)
    intros n H p Hp; induct Hp.
      induct n; try exact P0. refine (rec (S n) _ H). discriminate.
      exact (H p Hp).
Qed.
Theorem strong_induction {P: nat -> Prop} :
    P O -> (forall n, n <> 0 -> (forall p, p < n -> P p) -> P n) ->
    forall n, P n.
Proof fun P0 rec n => strong_induction0 P0 rec (S n) n (le_n _).





(* ========================= Map library extension ========================= *)


Lemma includes_refl : forall {A B} (m:fmap A B), m $<= m.
Proof.
  intros A B m; refine (includes_intro _).
  exact (fun _ _ H => H).
Qed.

Lemma includes_trans : forall {A B} (m1 m2 m3: fmap A B),
    m1 $<= m2 -> m2 $<= m3 -> m1 $<= m3.
Proof.
  intros A B m1 m2 m3 H1 H2; refine (includes_intro _); intros k v H3.
  exact (includes_lookup (includes_lookup H3 H1) H2).
Qed.

Lemma includes_nonexistent {A B} {m m' : fmap A B} {k} :
    m $<= m' -> m' $? k = None -> m $? k = None.
Proof.
  intros H1 H2; cases (m $? k); try reflexivity.
  rewrite (includes_lookup Heq H1) in H2; discriminate H2.
Qed.

Lemma includes_add_nonexistent {A B} {m m' : fmap A B} {k v} :
    (forall (x y:A), sumbool (x=y) (x<>y)) ->
    m $<= m' -> m $? k = None -> m $<= m' $+ (k, v).
Proof.
  intros A_dec m_le mk_none; refine (includes_intro _).
  intros k0 v0 mk0.
  cases (A_dec k0 k).
    invert e; rewrite mk_none in mk0; discriminate mk0.
    rewrite (lookup_add_ne _ _ n).
    exact (includes_lookup mk0 m_le).
Qed.

(* Map Equality *)

Definition map_eq {A B} (m m': fmap A B) : Prop :=
    forall (x:A), m $? x = m' $? x.
Infix "$==" := map_eq (at level 90).

Lemma map_eq_refl : forall {A B} (m: fmap A B), m $== m.
Proof fun A B m x => eq_refl (m $? x).
Lemma map_eq_sym : forall {A B} {m m': fmap A B}, m $== m' -> m' $== m.
Proof fun A B m m' H x => eq_sym (H x).
Lemma map_eq_trans : forall {A B} {m1 m2 m3: fmap A B},
    m1 $== m2 -> m2 $== m3 -> m1 $== m3.
Proof fun A B m1 m2 m3 H1 H2 x => eq_trans (H1 x) (H2 x).

Ltac map_rewritel Heq := refine (map_eq_trans Heq _).
Ltac map_rewriter Heq := refine (map_eq_trans _ (map_eq_sym Heq)).

(* Other properties *)

Lemma plus_minus : forall {A B} (m: fmap A B) k v,
    (forall x y:A, sumbool (x=y) (x<>y)) ->
    m $+ (k, v) $- k $== m $- k.
Proof.
  intros A B m k1 v A_dec k2; cases (A_dec k2 k1).
  (* k2 = k1 *)
    repeat rewrite (lookup_remove_eq _ (eq_sym e)); reflexivity.
  (* k2 <> k1 *)
    repeat rewrite (lookup_remove_ne _ n).
    rewrite (lookup_add_ne _ _ n); reflexivity.
Qed.

Lemma map_eq_leq {A B} (m m': fmap A B):
    m $== m' <-> (m $<= m') /\ (m' $<= m).
Proof.
  split.
  (* -> *)
    intro H; split; refine (includes_intro _); intros k v H2;
       [ pose (Heq := map_eq_sym H) | pose (Heq := H) ];
       rewrite (Heq k); exact H2.
  (* <- *)
    intros [H1 H2] x; cases (m $? x).
    (* Some b *)
      exact (eq_sym (includes_lookup Heq H1)).
    (* None *)
      cases (m' $? x); try reflexivity.
      rewrite (includes_lookup Heq0 H2) in Heq; discriminate Heq.
Qed.

Lemma map_eq_through_minus: forall {A B} {m m': fmap A B} k,
    (forall x y:A, sumbool (x=y) (x<>y)) ->
    m $== m' -> m $- k $== m' $- k.
Proof.
  intros A B m m' k1 A_dec H k2; cases (A_dec k2 k1).
    repeat rewrite (lookup_remove_eq _ (eq_sym e)); reflexivity.
    repeat rewrite (lookup_remove_ne _ n); exact (H k2).
Qed.

(* Map difference *)

Definition map_diff {A B} (m m': fmap A B) : fmap A B :=
    restrict (fun k => (m' $? k = None)) m.
Infix "$--" := map_diff (at level 50, left associativity).

Lemma diff_includes : forall {A B} (m m': fmap A B) k v,
    (m $-- m') $? k = Some v -> m $? k = Some v.
Proof.
  intros A B m m' k v H.
  rewrite <- (lookup_restrict_true _ m k (lookup_restrict_true_fwd H)).
  exact H.
Qed.

Lemma option_none_dec : forall {B} (res: option B),
    sumbool (res=None) (res<>None).
Proof.
  intros B res; cases res.
    right; intro absurd; discriminate absurd.
    left; reflexivity.
Qed.
Lemma diff_minus_assoc : forall {A B} (m1 m2: fmap A B) k,
    (forall x y:A, sumbool (x=y) (x<>y)) ->
    (m1 $-- m2) $- k $== (m1 $- k) $-- m2.
Proof.
  intros A B m1 m2 k1 A_dec k2; cases (A_dec k2 k1).
  (* k1 = k2 *)
    rewrite (lookup_remove_eq _ (eq_sym e)).
    cases (option_none_dec (m2 $? k2)); unfold map_diff.
    (* m2 $? k2 = None *)
      rewrite (lookup_restrict_true _ _ k2 e0).
      rewrite (lookup_remove_eq _ (eq_sym e)); reflexivity.
    (* m2 $? k2 <> None *)
      rewrite (lookup_restrict_false _ _ k2 n); reflexivity.
  (* k1 <> k2 *)
    rewrite (lookup_remove_ne _ n).
    cases (option_none_dec (m2 $? k2)); unfold map_diff.
    (* m2 $? k2 = None *)
      repeat rewrite (lookup_restrict_true _ _ k2 e).
      rewrite (lookup_remove_ne _ n); reflexivity.
    (* m2 $? k2 <> None *)
      repeat rewrite (lookup_restrict_false _ _ k2 n0); reflexivity.
Qed.

Lemma split_diff : forall {A B} (m1 m2: fmap A B) k v,
    (forall x y:A, sumbool (x=y) (x<>y)) ->
    m1 $-- (m2 $+ (k, v)) $== (m1 $-- m2) $- k.
Proof.
  intros A B m1 m2 k1 v A_dec k2; cases (A_dec k2 k1).
  (* k1 <> k2 *)
    rewrite (lookup_remove_eq _ (eq_sym e)).
    cases (option_none_dec ((m2 $+ (k1, v)) $? k2)); unfold map_diff.
    (* m1 $? k2 = None *)
      rewrite (lookup_add_eq m2 v (eq_sym e)) in e0; discriminate e0.
    (* m1 $? k2 <> None *)
      rewrite (lookup_restrict_false _ _ k2 n); reflexivity.
  (* k1 = k2 *)
    rewrite (lookup_remove_ne _ n).
    cases (option_none_dec ((m2 $+ (k1, v)) $? k2)); unfold map_diff.
    (* (m2 $+ (k1, v)) $? k2 = None *)
      rewrite (lookup_restrict_true _ _ k2 e).
      rewrite (lookup_add_ne m2 v n) in e.
      rewrite (lookup_restrict_true _ _ k2 e); reflexivity.
    (* (m2 $+ (k1, v)) $? k2 <> None *)
      rewrite (lookup_restrict_false _ _ k2 n0).
      rewrite (lookup_add_ne m2 v n) in n0.
      rewrite (lookup_restrict_false _ _ k2 n0); reflexivity.
Qed.

Lemma map_eq_through_diff : forall {A B} {m1 m2 m1' m2': fmap A B},
    m1 $== m1' -> m2 $== m2' -> m1 $-- m2 $== m1' $-- m2'.
Proof.
  intros A B m1 m2 m1' m2' H1 H2 k.
  cases (option_none_dec (m2 $? k)); unfold map_diff.
  (* m2 $? k = None *)
    rewrite (lookup_restrict_true _ m1 k e).
    rewrite (H2 k) in e.
    rewrite (lookup_restrict_true _ m1' k e).
    rewrite (H1 k); reflexivity.
  (* m2 $? k <> None *)
    rewrite (lookup_restrict_false _ m1 k n).
    rewrite (H2 k) in n.
    rewrite (lookup_restrict_false _ m1' k n); reflexivity.
Qed.

Lemma diff_discard : forall {A B} (m1: fmap A B) {m2 k} v,
    (forall x y:A, sumbool (x=y) (x<>y)) ->
    m2 $? k <> None -> m1 $+ (k, v) $-- m2 $== m1 $-- m2.
Proof.
  intros A B m1 m2 k1 v A_dec H k2; cases (A_dec k2 k1); unfold map_diff.
  (* k2 = k1 *)
    rewrite <- e in H.
    repeat rewrite (lookup_restrict_false _ _ k2 H); reflexivity.
  (* k2 <> k1 *)
    cases (option_none_dec (m2 $? k2)).
      repeat rewrite (lookup_restrict_true _ _ k2 e);
          rewrite (lookup_add_ne m1 v n); reflexivity.
      repeat rewrite (lookup_restrict_false _ _ k2 n0); reflexivity.
Qed.

Lemma bigger_diff_eq {A B} {m1 m2 r1 r2: fmap A B} :
    m1 $-- r1 $== m2 $-- r1 -> r1 $<= r2 -> m1 $-- r2 $== m2 $-- r2.
Proof.
  intros H1 H2 x.
  cases (option_none_dec (r2 $? x)).
  (* None *)
    unfold map_diff; repeat rewrite
        (lookup_restrict_true (fun k => (lookup r2 k = None)) _ _ e).
    pose (H1x := H1 x).
    unfold map_diff in H1x; repeat rewrite
        (lookup_restrict_true (fun k => (lookup r1 k = None)) _ _
          (includes_nonexistent H2 e)) in H1x.
    exact H1x.
  (* Some b *)
    unfold map_diff; repeat rewrite
        (lookup_restrict_false (fun k => (lookup r2 k = None)) _ _ n).
    reflexivity.
Qed.

Lemma add_under_diff {A B} {m1 m2 r: fmap A B} k v :
    (forall x y:A, sumbool (x=y) (x<>y)) ->
    m1 $-- r $== m2 $-- r -> m1 $+ (k,v) $-- r $== m2 $+ (k,v) $-- r.
Proof.
  intros A_dec H x.
  pose (Hx := H x); unfold map_diff; unfold map_diff in Hx.
  cases (option_none_dec (r $? x)).
  (* r $? x = None *)
    repeat rewrite (lookup_restrict_true (fun k => (r $? k = None)) _ _ e).
    repeat rewrite (lookup_restrict_true (fun k => (r $? k = None)) _ _ e)
        in Hx.
    cases (A_dec x k).
      repeat rewrite (lookup_add_eq _ _ (eq_sym e0)); reflexivity.
      repeat rewrite (lookup_add_ne _ _ n); exact Hx.
  (* r $? x <> None *)
    repeat rewrite (lookup_restrict_false (fun k => (r $? k = None)) _ _ n).
    reflexivity.
Qed.





(* ============= Additional properties on Pset7Sig definitions ============== *)


Lemma validator_on_same_cmds: forall {sc md1 md2},
    validator' sc sc md1 = Some md2 -> md1 = md2.
Proof.
  intro sc; elimc sc; invert 1; try reflexivity.
  (* Assign *)
    cases (md1 $? x); cases (arithNotReading e md1);
        cases (cmd_eq_dec (x <- e) (x <- e)); cases e; try discriminate H1;
        invert H1; reflexivity.
  (* Sequence *)
    cases (validator' c1 c1 md1); cases (validator' c2 c2 md1);
        try discriminate H3.
      exact (eq_trans (H _ _ Heq) (H0 _ _ H3)).
      rewrite (H _ _ Heq) in Heq0; rewrite H3 in Heq0; discriminate Heq0.
  (* If *)
    cases (validator' then_ then_ md1); cases (validator' else_ else_ md1);
        cases (cmd_eq_dec (when e then then_ else else_ done)
            (when e then then_ else else_ done));
        cases (arithNotReading e md1 && cmdNotReading then_ md1 &&
            cmdNotReading else_ md1); try discriminate H3.
    invert H3; reflexivity.
  (* While *)
    cases (validator' body body md1); cases (arithNotReading e md1);
        cases (cmd_eq_dec (while e loop body done) (while e loop body done));
        try discriminate H2.
    invert H2; reflexivity.
  (* Output *)
    cases (arith_eq_dec e e); cases (arithNotReading e md1);
        try discriminate H1.
    invert H1; reflexivity.
Qed.

Theorem validator_incr : forall {c1 c2 m1 m2},
    validator' c1 c2 m1 = Some m2 -> m1 $<= m2.
Proof.
  intro c1; elim c1; clear c1.
  (* Skip *)
    intros c2 m1 m2 H; invert H; cases c2; try discriminate H1.
    invert H1; exact (includes_refl m2).
  (* Nop *)
    intros c2 m1 m2 H; invert H; cases c2; try discriminate H1.
    (* Nop Nop *)
      invert H1; exact (includes_refl _).
    (* Nop Assign *)
      cases e; try discriminate H1.
      cases (m1 $? x); try discriminate H1.
      invert H1.
      exact (includes_add_nonexistent string_dec (includes_refl m1) Heq).
  (* Assign *)
    intros v e c2 m1 m2 H; invert H; cases c2; try (cases e; discriminate H1).
    (* Assign Nop *)
      cases e; try discriminate H1.
      cases (m1 $? v); try discriminate H1.
      cases (n ==n n0); try discriminate H1.
      invert H1; exact (includes_refl _).
    (* Assign Assign *)
      cases (cmd_eq_dec (v <- e) (x <- e0));
          cases (arithNotReading e m1);
          cases (m1 $? x);
          try (cases e; discriminate H1).
      cases e; invert H1; exact (includes_refl _).
  (* Seq *)
    intros ca reca cb recb c2 m1 m2 H; invert H; cases c2; try discriminate H1.
    cases (validator' ca c2_1 m1); try discriminate H1.
    exact (includes_trans m1 m m2 (reca _ _ _ Heq) (recb _ _ _ H1)).
  (* If *)
    intros e ca reca cb recb c2 m1 m2 H; invert H;
        cases c2; try discriminate H1.
    cases (validator' ca c2_1 m1); try discriminate H1.
    cases (validator' cb c2_2 m1); try discriminate H1.
    cases (cmd_eq_dec (when e then ca else cb done)
                      (when e0 then c2_1 else c2_2 done)); try discriminate H1.
    invert e1.
    cases (arithNotReading e0 m1 && cmdNotReading c2_1 m1 &&
           cmdNotReading c2_2 m1); try discriminate H1.
    invert H1; exact (includes_refl _).
  (* While *)
    intros e c1 rec c2 m1 m2 H; invert H; cases c2; try discriminate H1.
    cases (validator' c1 c2 m1); try discriminate H1.
    cases (cmd_eq_dec (while e loop c1 done) (while e0 loop c2 done));
        try discriminate H1.
    cases (arithNotReading e m1); try discriminate H1.
    invert H1; exact (includes_refl _).
  (* Output *)
    intros e c2 m1 m2 H; invert H; cases c2; try discriminate H1.
    cases (arith_eq_dec e e0); try discriminate H1.
    cases (arithNotReading e m1); try discriminate H1.
    invert H1; exact (includes_refl _).
Qed.

Theorem arith_sub {e md v1 v2} :
    arithNotReading e md = true -> v1 $-- md $== v2 $-- md ->
    interp e v1 = interp e v2.
Proof.
  elimc e; try (* Const *) reflexivity; try ((* Plus, Minus, Times *)
      intros e1 rec1 e2 rec2 H1 H2; simpl;
      pinvert (proj1 (andb_true_iff _ _) H1);
      rewrite (rec1 H H2); rewrite (rec2 H0 H2); reflexivity).
  (* Var *)
  intros x H1 H2. simpl. simpl in H1.
  cases (md $? x); try discriminate H1.
  pose (solution := H2 x).
  unfold map_diff in solution.
  repeat rewrite (lookup_restrict_true (fun k => (lookup md k = None)) _ x Heq)
      in solution.
  rewrite solution; reflexivity.
Qed.





(* =============================== Generation =============================== *)


Inductive my_generate :
    valuation * cmd -> list (option (option nat)) -> valuation -> Prop :=
  | MyGenDone : forall v c,
      my_generate (v, c) [] v
  | MyGenSkip : forall v,
      my_generate (v, Skip) [None] v
  | MyGenStep : forall vc l vc' ns vf,
      cstep vc l vc' ->
      my_generate vc' ns vf ->
      my_generate vc (Some l :: ns) vf.

Lemma gen_unicity_n : forall {n vc l1 l2 vf1 vf2},
    my_generate vc l1 vf1 -> my_generate vc l2 vf2 ->
    length l1 = n -> length l2 = n -> l1 = l2 /\ vf1 = vf2.
Proof.
  intro n; elimc n.
  (* O *)
    intros vc l1 l2 vf1 vf2 H1 H2 l1len l2len.
    pose (l1empty := proj1 (length_zero_iff_nil l1) l1len); invert l1empty.
    pose (l2empty := proj1 (length_zero_iff_nil l2) l2len); invert l2empty.
    induct H1; induct H2; exact (conj (eq_refl _) (eq_refl _)).
  (* S n *)
    intros n rec (v,c) l1 l2 vf1 vf2 H1 H2 l1slen l2slen.
    induct l1; try discriminate l1slen; clear IHl1.
    induct l2; try discriminate l2slen; clear IHl2.
    assert (length l1 = n) as l1len; try exact (f_equal pred l1slen).
    assert (length l2 = n) as l2len; try exact (f_equal pred l2slen).
    induct H1.
    (* MyGenSkip *)
      invert l1slen; clear H0.
      pose (l2empty := proj1 (length_zero_iff_nil l2) l2len); invert l2empty.
      invert H2.
        exact (conj (eq_refl _) (eq_refl _)).
        invert H3; invert H1; invert H2.
    (* MyGenStep *)
      clear IHmy_generate.
      induct H2; try (invert H; invert H3; invert H4); clear IHmy_generate.
      pose (equalities := deterministic H0 H); destruct equalities, H3, H4.
      pose (solution := rec _ _ _ _ _ H1 H2 l1len l2len); invert solution.
      exact (conj (eq_refl _) (eq_refl _)).
Qed.
Theorem gen_unicity {vc l1 l2 vf1 vf2} :
    my_generate vc l1 vf1 -> my_generate vc l2 vf2 -> length l1 = length l2 ->
    l1 = l2 /\ vf1 = vf2.
Proof fun H1 H2 leneq => gen_unicity_n H1 H2 leneq (eq_refl _).

Theorem gen_prefix : forall {l1 vc l2 vf1 vf2},
    my_generate vc l1 vf1 -> my_generate vc l2 vf2 ->
    length l1 <= length l2 -> exists lq, l1 ++ lq = l2.
Proof.
  intro l1; elimc l1; try (
      intros vc l2 vf1 vf2 _ _ _; exists l2; reflexivity).
  intros a l1 rec vc l2 vf1 vf2 gen1 gen2 lencmp; invert gen1.
  (* MyGenSkip *)
    invert gen2; [invert lencmp | | invert H; invert H3; invert H4].
    exists nil; reflexivity.
  (* MyGenStep *)
    invert gen2; [ invert lencmp | invert H2; invert H1; invert H3 |].
    pinvert (deterministic H H2).
    elim (rec vc' ns vf1 vf2 H4 H0 (le_S_n _ _ lencmp)).
    intros lq Hrec; exists lq.
    rewrite <- (app_comm_cons _ _ _); rewrite Hrec; reflexivity.
Qed.

Lemma split_gen : forall {vc l vc' l' ns vf},
    cstep vc l vc' -> my_generate vc (Some l' :: ns) vf ->
    l = l' /\ my_generate vc' ns vf.
Proof.
  intros vc l vc' l' ns vf step H; induct H.
  pose (eqs := deterministic step H); invert eqs.
  exact (conj (eq_refl _) H0).
Qed.

Lemma split_seq0: forall {n vi1 s1 s2 outs vf1},
    my_generate (vi1, Sequence s1 s2) outs vf1 -> length outs = n
    ->
      my_generate (vi1, s1) outs vf1 /\ ~ In None outs
      \/
      exists outs1 outs2 vfmid1,
        my_generate (vi1, s1) (outs1 ++ [None]) vfmid1
        /\
        my_generate (vfmid1, s2) (outs2) vf1
        /\
        outs = outs1 ++ [Some None] ++ outs2.
Proof.
  intro n; elimc n.
  (* O *)
    intros vi1 s1 s2 outs vf1 H no_outs.
    pinvert (proj1 (length_zero_iff_nil _) no_outs); left.
    invert H.
    exact (conj (MyGenDone vf1 s1) (fun H => in_nil H)).
  (* S n *)
    intros n rec vi1 s1 s2 outs vf1 Hseq outs_len.
    cases outs; try discriminate outs_len.
    invert Hseq; invert H2; invert H1.
    (* s1 stops *)
      right; exists [], outs, vi1.
      invert H3; invert H7.
      exact (conj (MyGenSkip v') (conj H4 (eq_refl _))).
    (* s1 continues *)
      invert H7.
      cases (rec v' c'0 s2 outs vf1 H4 (f_equal pred outs_len)).
      (* s1 only *)
        clear Heq; left; split.
          exact (MyGenStep _ _ _ _ _ (CStep H5 H3 H6) (proj1 a)).
          intro absurd; cases absurd; try discriminate; cases (proj2 a H).
      (* s1 eventually stops *)
        clear Heq; elimc e; intros outs1 tmp; elimc tmp; intros outs2 tmp.
        elimc tmp; intros vfmid1 [midgen [finalgen outssum]].
        right; exists (Some l::outs1), outs2, vfmid1.
        repeat rewrite <- (app_comm_cons _ _ _); rewrite outssum.
        exact (conj (MyGenStep _ _ _ _ _ (CStep H5 H3 H6) midgen)
            (conj finalgen (eq_refl _))).
Qed.
Theorem split_seq {vi1 s1 s2 outs vf1} :
    my_generate (vi1, Sequence s1 s2) outs vf1
    ->
      my_generate (vi1, s1) outs vf1 /\ ~ In None outs
      \/
      exists outs1 outs2 vfmid1,
        my_generate (vi1, s1) (outs1 ++ [None]) vfmid1
        /\
        my_generate (vfmid1, s2) (outs2) vf1
        /\
        outs = outs1 ++ [Some None] ++ outs2.
Proof fun H => split_seq0 H (eq_refl _).

Lemma plug_step {vi c1 l vf c2} :
    cstep (vi, c1) l (vf, c2) -> forall c3, cstep (vi, c1;; c3) l (vf, c2;; c3).
Proof.
  intros H c3; invert H.
  exact (CStep (PlugSeq c3 H5) H6 (PlugSeq c3 H7)).
Qed.
Theorem plug_gen1 : forall {outs vi t1 vf},
    my_generate (vi, t1) outs vf -> ~ In None outs ->
    forall t2, my_generate (vi, t1;; t2) outs vf.
Proof.
  intro outs; elimc outs.
  (* nil *)
    intros vi t1 vf H _ t2; invert H.
    exact (MyGenDone vf _).
  (* a::outs *)
    intros a outs rec vi t1 vf gen no_none t2; induct gen.
    (* MyGenSkip *)
      cases (no_none (or_introl (eq_refl None))).
    (* MyGenStep *)
      clear IHgen; induct vc'.
      pose (no_none2 := fun H => no_none (in_cons (Some l) None outs H)).
      exact (MyGenStep _ _ _ _ _ (plug_step H t2) (rec a b vf gen no_none2 t2)).
Qed.

Theorem plug_gen2 : forall {outs1 outs2 vi t1 t2 vm vf},
    my_generate (vi, t1) (outs1 ++ [None]) vm ->
    my_generate (vm, t2) outs2 vf ->
    my_generate (vi, t1;; t2) (outs1 ++ [Some None] ++ outs2) vf.
Proof.
  intro outs1; elimc outs1.
  (* nil *)
    intros outs2 vi t1 t2 vm vf H1 H2; invert H1.
    exact (MyGenStep _ _ _ _ _
        (CStep (PlugHole _) (Step0Seq vm t2) (PlugHole _)) H2).
  (* a::outs1 *)
    intros a outs1 rec outs2 vi t1 t2 vm vf H1 H2; invert H1;
        try cases (app_cons_not_nil _ _ _ H5).
    induct vc'.
    refine (MyGenStep _ _ _ _ _ _ (rec outs2 a b t2 vm vf H6 H2)).
    exact (plug_step H4 t2).
Qed.





(* =============== Conclusion using simulation on valid_state =============== *)


Definition valid_state (vc1 vc2: valuation * cmd) : Prop :=
    forall ns vf1, my_generate vc1 ns vf1 ->
    exists vf2, my_generate vc2 ns vf2.

Theorem valid_state_refl : forall {vc1 vc2},
    valid_state vc1 vc2 -> valid_state vc2 vc1.
Proof.
  assert (forall ns vc1 vc2 vf2, valid_state vc1 vc2 ->
      my_generate vc2 ns vf2 ->
      exists vf1, my_generate vc1 ns vf1) as reordered.
    intro ns; elimc ns.
    (* nil *)
      exact (fun '(v,c) _ _ _ _ => ex_intro _ _ (MyGenDone v c)).
    (* a::q *)
      intros a q rec (v,c) vc2 vf2 H1 H2.
      induct H2.
      (* MyGenSkip *)
        cases (skip_or_step v c).
        (* Skip *)
          clear Heq; invert e; exact (ex_intro _ _ (MyGenSkip v)).
        (* CStep *)
          clear Heq; elimc e; intros v' tmp; elimc tmp; intros l tmp; elimc tmp.
          intros c' v0step.
          elim (H1 [Some l] v' (MyGenStep _ _ _ _ _ v0step (MyGenDone _ _))).
          intros vf2 vf2_gen.
          discriminate (proj1 (gen_unicity vf2_gen (MyGenSkip v0) (eq_refl 1))).
      (* MyGenStep *)
        clear IHmy_generate.
        cases (skip_or_step v c).
        (* Skip *)
          clear Heq; invert e; destruct vc.
          pose (tmp := (H1 [None] v (MyGenSkip v))).
          invert tmp; invert H0; invert H; invert H4; invert H5.
        (* CStep *)
          clear Heq; elimc e; intros v' tmp; elimc tmp.
          intros l' tmp; elimc tmp; intros c' H'.
          assert (valid_state (v', c') vc') as valid_followup.
            intros ns vf1 Ha.
            elim (H1 _ _ (MyGenStep _ _ _ _ _ H' Ha)); intros vf2 vf2_gen.
            exact (ex_intro _ _ (proj2 (split_gen H vf2_gen))).
          elim (H1 [Some l'] _ (MyGenStep _ _ _ _ _ H' (MyGenDone _ _))).
          intros vf2 vf2_gen; induct vc'.
          pose (l_eq_l' := proj1 (gen_unicity vf2_gen
              (MyGenStep _ _ _ _ _ H (MyGenDone _ _)) (eq_refl 1))).
          invert l_eq_l'.
          elim (rec (v', c') (a, b) vf valid_followup H2).
          intros vff vff_gen.
          exact (ex_intro _ _ (MyGenStep _ _ _ _ _ H' vff_gen)).
  exact (fun vc1 vc2 H ns vf2 => reordered ns vc1 vc2 vf2 H).
Qed.

Theorem validator_valid0 : forall s n t md1 md2,
    validator' s t md1 = Some md2 ->
    forall vi1 vi2,
    (vi1 $-- md1) $== (vi2 $-- md1) ->
    forall vf1 outs, my_generate (vi1, s) outs vf1 -> length outs = n ->
    exists vf2,
        my_generate (vi2, t) outs vf2
        /\ ((vf1 $-- md2) $== (vf2 $-- md2)).
Proof.
  intro s; elimc s.
  intros n t; cases t; try discriminate.
  (* Skip Skip *)
    intros md1 md2 valid vi1 vi2 vi12 vf1 outs gen1 outslen.
    invert valid; invert gen1.
      exact (ex_intro _ vi2 (conj (MyGenDone _ _) vi12)).
      exact (ex_intro _ vi2 (conj (MyGenSkip _) vi12)).
      invert H; invert H3; invert H4.
  intros n t; cases t; try discriminate.
  (* Nop Nop *)
    intros md1 md2 valid vi1 vi2 vi12 vf1 outs gen1 outslen.
    invert valid; invert gen1;
        try exact (ex_intro _ vi2 (conj (MyGenDone _ _) vi12)).
    invert H; invert H3; invert H4; invert H7.
    pose (first_step := CStep (PlugHole _) (Step0Nop vi2) (PlugHole _)).
    invert H0.
      exact (ex_intro _ vi2
          (conj (MyGenStep _ _ _ _ _ first_step (MyGenDone _ _)) vi12)).
      exact (ex_intro _ vi2
          (conj (MyGenStep _ _ _ _ _ first_step (MyGenSkip _)) vi12)).
      invert H; invert H3; invert H4.
  (* Nop, Assign x (Const n) *)
    intros md1 md2 valid vi1 vi2 vi12 vf1 outs gen1 outslen.
    simpl in valid.
    cases e; cases (md1 $? x); try discriminate valid; invert valid.
    pose (vi12x := (bigger_diff_eq vi12
        (includes_add_nonexistent (v:=n0) string_dec (includes_refl _) Heq))).
    invert gen1; try exact (ex_intro _ vi2 (conj (MyGenDone _ _) vi12x)).
    invert H; invert H3; invert H4; invert H7.
    pose (first_step := CStep (PlugHole _) (Step0Assign vi2 x n0) (PlugHole _)).
    exists (vi2 $+ (x, interp n0 vi2)).
    assert ((md1 $+ (x, n0)) $? x <> None) as x_discarded.
      rewrite (lookup_add_eq _ _ (eq_refl _)); discriminate.
    pose (vi12xx := map_eq_trans vi12x (map_eq_sym
        (diff_discard _ (interp n0 vi2) string_dec x_discarded))).
    invert H0.
      exact (conj (MyGenStep _ _ _ _ _ first_step (MyGenDone _ _)) vi12xx).
      exact (conj (MyGenStep _ _ _ _ _ first_step (MyGenSkip _)) vi12xx).
      invert H; invert H3; invert H4.
  intros x e n t; cases t; try (cases e; discriminate).
  (* Assign x (Const n), Nop *)
    intros md1 md2 valid vi1 vi2 vi12 vf1 outs gen1 outslen.
    simpl in valid.
    cases e; cases (md1 $? x); try discriminate valid.
    cases (n0 ==n n1); try discriminate valid; invert valid.
    invert gen1; try exact (ex_intro _ vi2 (conj (MyGenDone _ _) vi12)).
    invert H; invert H3; invert H4; invert H7.
    pose (first_step := CStep (PlugHole _) (Step0Nop vi2) (PlugHole _)).
    assert (md2 $? x <> None) as md2_has_x; try (rewrite Heq; discriminate).
    pose (vi12x := map_eq_trans (diff_discard _ n1 string_dec md2_has_x) vi12).
    invert H0.
      exact (ex_intro _ vi2
          (conj (MyGenStep _ _ _ _ _ first_step (MyGenDone _ _)) vi12x)).
      exact (ex_intro _ vi2
          (conj (MyGenStep _ _ _ _ _ first_step (MyGenSkip _)) vi12x)).
      invert H; invert H3; invert H4.
  (* Assign sx se, Assign tx te *)
    intros md1 md2 valid vi1 vi2 vi12 vf1 outs gen1 outslen.
    simpl in valid.
    cases (md1 $? x0); cases (cmd_eq_dec (x <- e) (x0 <- e0));
        cases (arithNotReading e md1); try (cases e; discriminate valid).
    assert (md1 = md2) as md12; try (cases e; invert valid; reflexivity).
    invert md12; clear valid; invert e1.
    invert gen1; try exact (ex_intro _ vi2 (conj (MyGenDone _ _) vi12)).
    invert H; invert H3; invert H4; invert H7.
    rewrite (arith_sub Heq0 vi12) in H0.
    pose (vi12x0 := add_under_diff x0 (interp e0 vi2) string_dec vi12).
    pose (first_step :=
        CStep (PlugHole _) (Step0Assign vi2 x0 e0) (PlugHole _)).
    exists (vi2 $+ (x0, interp e0 vi2)).
    invert H0.
      exact (conj (MyGenStep _ _ _ _ _ first_step (MyGenDone _ _)) vi12x0).
      exact (conj (MyGenStep _ _ _ _ _ first_step (MyGenSkip _)) vi12x0).
      invert H; invert H3; invert H4.
  intros c1 rec1 c2 rec2 n t; cases t; try discriminate.
  (* Sequence c1 c2, Sequence t1 t2 *)
    intros md1 md2 valid vi1 vi2 vi12 vf1 outs gen1 outslen.
    invert valid.
    cases (validator' c1 t1 md1); try discriminate H0.
    elim (split_seq gen1).
    (* Case 1 *)
      intros [gen11 no_none].
      elim (rec1 _ _ _ _ Heq _ _ vi12 _ _ gen11 (eq_refl _)).
      intros vf2 [gen21 vf12]; exists vf2.
      exact (conj (plug_gen1 gen21 no_none t2)
          (bigger_diff_eq vf12 (validator_incr H0))).
    (* Case 2 *)
      intro tmp; elimc tmp; intros outs1 tmp; elimc tmp; intros outs2 tmp;
          elimc tmp; intros vfmid1 [gen3 [gen4 outsrel]].
      elim (rec1 _ _ _ _ Heq _ _ vi12 _ _ gen3 (eq_refl _));
          intros vfmid2 [gen6 eq6].
      elim (rec2 _ _ _ _ H0 _ _ eq6 _ _ gen4 (eq_refl));
          intros vf2 [gen7 eq7].
      exists vf2; refine (conj _ eq7).
      rewrite outsrel; exact (plug_gen2 gen6 gen7).
  intros e c1 rec1 c2 rec2 n t; cases t; try discriminate.
  (* If ..., If ... *)
    intros md1 md2 valid vi1 vi2 vi12 vf1 outs gen1 outslen.
    invert valid.
    cases (validator' c1 t1 md1); cases (validator' c2 t2 md1);
        cases (cmd_eq_dec (when e then c1 else c2 done)
            (when e0 then t1 else t2 done));
        cases (arithNotReading e md1 && cmdNotReading c1 md1 &&
            cmdNotReading c2 md1);
        try discriminate H0.
    invert H0; invert e1.
    pinvert (validator_on_same_cmds Heq).
    pinvert (validator_on_same_cmds Heq0).
    cases outs; invert gen1.
    (* [] *)
      exact (ex_intro _ vi2 (conj (MyGenDone vi2 _) vi12)).
    (* Some l::outs *)
      induct vc'.
      pose (arith_e0 := proj1 (proj1 (andb_true_iff _ _)
          (proj1 (proj1 (andb_true_iff _ _) Heq1)))).
      invert H2; invert H6; invert H7; invert H8.
      (* True *)
        elim (rec1 _ _ _ _ Heq _ _ vi12 _ _ H4 (eq_refl _)).
        intros vf2 [gen2 vf12]; exists vf2.
        rewrite (arith_sub arith_e0 vi12) in H5.
        pose (false_step :=
            (CStep (PlugHole _) (Step0IfTrue vi2 e0 b t2 H5) (PlugHole _))).
        exact (conj (MyGenStep _ _ _ _ _ false_step gen2) vf12).
      (* False *)
        elim (rec2 _ _ _ _ Heq0 _ _ vi12 _ _ H4 (eq_refl _)).
        intros vf2 [gen2 vf12]; exists vf2.
        rewrite (arith_sub arith_e0 vi12) in H5.
        pose (false_step :=
            (CStep (PlugHole _) (Step0IfFalse vi2 e0 t1 b H5) (PlugHole _))).
        exact (conj (MyGenStep _ _ _ _ _ false_step gen2) vf12).
  (* While ..., While ... *)
    intros e c rec; refine (strong_induction _ _).
    (* outs = [] *)
      intro t; cases t; try discriminate.
      intros md1 md2 valid vi1 vi2 vi12 vf1 outs gen1 outslen.
      invert valid.
      cases (validator' c t md1); cases (arithNotReading e md1);
          cases (cmd_eq_dec (while e loop c done) (while e0 loop t done));
          try discriminate H0.
      invert H0; invert e1.
      pinvert (validator_on_same_cmds Heq).
      cases outs; try discriminate outslen.
      induct gen1; exists vi2.
      exact (conj (MyGenDone _ _) vi12).
    (* Strong induction *)
      intros n n_nonzero srec t; cases t; try discriminate.
      intros md1 md2 valid vi1 vi2 vi12 vf1 outs gen1 outslen.
      invert valid.
      cases (validator' c t md1); cases (arithNotReading e md1);
          cases (cmd_eq_dec (while e loop c done) (while e0 loop t done));
          try discriminate H0.
      invert H0; invert e1.
      pinvert (validator_on_same_cmds Heq).
      cases outs; try cases (n_nonzero (eq_refl O)); clear n_nonzero.
      invert gen1; invert H2; invert H1; invert H7.
      pinvert H3.
      (* True *)
        rewrite (arith_sub Heq0 vi12) in H5.
        elim (split_seq H4).
        (* t not completed *)
          intros [gen1 no_none].
          elim (rec _ _ _ _ Heq _ _ vi12 _ _ gen1 (eq_refl _)).
          intros vf2 [gen2 vf12]; exists vf2.
          exact (conj (MyGenStep _ _ _ _ _
              (CStep (PlugHole _) (Step0WhileTrue vi2 e0 t H5) (PlugHole _))
              (plug_gen1 gen2 no_none _)) vf12).
        (* t completed *)
          intro tmp; elimc tmp; intros outs1 tmp; elimc tmp; intros outs2 tmp;
              elimc tmp; intros vfmid1 [gen3 [gen4 outsrel]].
          elim (rec _ _ _ _ Heq _ _ vi12 _ _ gen3 (eq_refl _)).
          intros vfmid2 [gen5 vfmid12].
          assert (length outs2 < length (Some None :: outs)) as outs2sub.
            simpl; rewrite outsrel; repeat rewrite (app_length _ _).
            refine (le_n_S _ _ _); rewrite (plus_assoc _ _ _).
            exact (le_plus_r _ _).
          assert (validator' (while e0 loop t done) (while e0 loop t done) m
              = Some m) as wvalid.
            simpl; rewrite Heq; rewrite Heq0.
            cases (cmd_eq_dec (while e0 loop t done) (while e0 loop t done));
                [ reflexivity | cases (n (eq_refl _)) ].
          elim (srec _ outs2sub _ _ _ wvalid _ _ vfmid12 _ _ gen4 (eq_refl _)).
          intros vf2 [gen6 vf12]; exists vf2.
          refine (conj (MyGenStep _ _ _ _ _
              (CStep (PlugHole _) (Step0WhileTrue vi2 e0 t H5) (PlugHole _)) _)
              vf12).
          rewrite outsrel; exact (plug_gen2 gen5 gen6).
      (* False *)
        rewrite (arith_sub Heq0 vi12) in H5.
        exists vi2; invert H4.
        (* MyGenDone *)
          exact (conj (MyGenStep _ _ _ _ _
              (CStep (PlugHole _) (Step0WhileFalse vi2 e0 t H5) (PlugHole _))
              (MyGenDone _ _)) vi12).
        (* MyGenSkip *)
          refine (conj (MyGenStep _ _ _ _ _
              (CStep (PlugHole _) (Step0WhileFalse vi2 e0 t H5) (PlugHole _))
              (MyGenSkip _)) vi12).
        invert H; invert H4; invert H6.
  intros e n t; cases t; try discriminate.
  (* Output e, Output e0 *)
    intros md1 md2 valid vi1 vi2 vi12 vf1 outs gen1 outslen; exists vi2.
    simpl in valid; cases (arithNotReading e md1); cases (arith_eq_dec e e0);
        try discriminate valid; invert valid.
    invert gen1; try exact (conj (MyGenDone _ _) vi12).
    invert H; invert H3; invert H4; invert H7.
    rewrite (arith_sub Heq vi12).
    pose (first_step := CStep (PlugHole _) (Step0Output vi2 e0) (PlugHole _)).
    invert H0.
      exact (conj (MyGenStep _ _ _ _ _ first_step (MyGenDone _ _)) vi12).
      exact (conj (MyGenStep _ _ _ _ _ first_step (MyGenSkip _)) vi12).
      invert H; invert H3; invert H4.
Qed.

Theorem validator_valid : forall s t v,
    validator s t = true -> valid_state (v, s) (v, t).
Proof.
  intros s t v valid ns vf1 H; unfold validator in valid.
  cases (validator' s t $0); try discriminate valid; clear valid.
  elim (validator_valid0
      s _ t $0 m Heq v v (map_eq_refl _) vf1 ns H (eq_refl _)).
  intros vf2 [solution _]; exact (ex_intro _ vf2 solution).
Qed.

Lemma one_step_proof :
    forall vc1 vc2,
      valid_state vc1 vc2 -> forall vc1' l,
        cstep vc1 l vc1' ->
        exists vc2', cstep vc2 l vc2' /\ valid_state vc1' vc2'.
Proof.
  intros vc1 vc2 H1 vc1' l H2; destruct vc2.
  cases (skip_or_step v c); induct vc1'.
  (* Skip *)
    clear Heq; invert e.
    elim (valid_state_refl H1 [None] v (MyGenSkip v)); intros vf vc1_gen_none.
    discriminate (proj1 (gen_unicity vc1_gen_none
        (MyGenStep _ _ _ _ _ H2 (MyGenDone _ _)) (eq_refl 1))).
  (* Step *)
    clear Heq; elimc e; intros v' tmp; elimc tmp; intros l' tmp; elimc tmp.
    intros c' vstep.
    assert (l = l') as l_eq_l'.
      elim (H1 [Some l] _ (MyGenStep _ _ _ _ _ H2 (MyGenDone _ _))).
      intros vf vf_gen.
      pose (l_eq_l' := proj1 (gen_unicity vf_gen
          (MyGenStep _ _ _ _ _ vstep (MyGenDone _ _)) (eq_refl 1))).
      invert l_eq_l'; reflexivity.
    invert l_eq_l'; exists (v', c'); refine (conj vstep _).
    intros ns vf Hns.
    elim (H1 _ _ (MyGenStep _ _ _ _ _ H2 Hns)); intros vf2 vf2_gen.
    exact (ex_intro _ _ (proj2 (split_gen vstep vf2_gen))).
Qed.

Lemma agree_on_termination_proof :
    forall v1 v2 c2, valid_state (v1, Skip) (v2, c2) -> c2 = Skip.
Proof.
  intros v1 v2 c2 H; elim (H _ _ (MyGenSkip v1)).
  intros vf gen2; invert gen2; reflexivity.
Qed.

Theorem validator_ok:
  forall v s t, validator s t = true -> (v, s) =| (v, t).
Proof fun v s t H => simulation
    valid_state one_step_proof agree_on_termination_proof (v,s) (v,t)
    (validator_valid s t v H).
