(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 9 *)

Require Import Frap Pset9Sig.

Set Implicit Arguments.

Ltac elimc var := elim var; clear var.
Ltac pinvert expr := pose (pinvert_tmp := expr); invert pinvert_tmp.

Definition map_eq {A B} (m m': fmap A B) : Prop :=
    forall (x:A), m $? x = m' $? x.

(* Not sure why they redefine maps/sets/etc instead using the constructive
   versions from the standard lib. Using workarounds like $== like in Pset7 is
   annoying; let's just add this new axiom which is "obviously" fine. *)
Axiom map_eq_struct : forall {A B} {m m': fmap A B}, map_eq m m' -> m = m'.

Lemma map_remove_add {A B} : forall (m: fmap A B) k v,
    (forall (x y:A), sumbool (x=y) (x<>y)) ->
    m $+ (k, v) = m $- k $+ (k, v).
Proof.
  intros m k v A_dec; refine (map_eq_struct _); intro x.
  cases (A_dec x k).
    repeat rewrite (lookup_add_eq _ _ (eq_sym e)); reflexivity.
    repeat rewrite (lookup_add_ne _ _ n); rewrite (lookup_remove_ne _ n);
        reflexivity.
Qed.

Lemma map_add_remove {A B} : forall (m: fmap A B) k v,
    (forall (x y:A), sumbool (x=y) (x<>y)) ->
    m $+ (k, v) $- k = m $- k.
Proof.
  intros m k v A_dec; refine (map_eq_struct _); intro x.
  cases (A_dec x k).
    repeat rewrite (lookup_remove_eq _ (eq_sym e)); reflexivity.
    repeat rewrite (lookup_remove_ne _ n); rewrite (lookup_add_ne _ _ n);
        reflexivity.
Qed.

Lemma map_add_comm {A B} : forall (m: fmap A B) k1 v1 k2 v2,
    (forall (x y:A), sumbool (x=y) (x<>y)) -> k1 <> k2 ->
    m $+ (k1, v1) $+ (k2, v2) = m $+ (k2, v2) $+ (k1, v1).
Proof.
  intros m k1 v1 k2 v2 A_dec kneq; refine (map_eq_struct _); intro x.
  cases (A_dec x k1); cases (A_dec x k2).
    invert e; cases (kneq (eq_refl _)).
    rewrite (lookup_add_ne _ _ n);
        invert e; repeat rewrite (lookup_add_eq _ _ (eq_refl _)); reflexivity.
    rewrite (lookup_add_ne _ _ n);
        invert e; repeat rewrite (lookup_add_eq _ _ (eq_refl _)); reflexivity.
    repeat (rewrite (lookup_add_ne _ _ n); rewrite (lookup_add_ne _ _ n0));
        reflexivity.
Qed.

Lemma map_remove_comm {A B} : forall (m: fmap A B) k1 k2,
    (forall (x y:A), sumbool (x=y) (x<>y)) ->
    m $- k1 $- k2 = m $- k2 $- k1.
Proof.
  intros m k1 k2 A_dec; refine (map_eq_struct _); intro x.
  cases (A_dec x k1); cases (A_dec x k2).
    invert e; repeat rewrite (lookup_remove_eq _ (eq_refl _)); reflexivity.
    rewrite (lookup_remove_ne _ n); invert e;
        repeat rewrite (lookup_remove_eq _ (eq_refl _)); reflexivity.
    rewrite (lookup_remove_ne _ n); invert e;
        repeat rewrite (lookup_remove_eq _ (eq_refl _)); reflexivity.
    repeat (rewrite (lookup_remove_ne _ n); rewrite (lookup_remove_ne _ n0));
        reflexivity.
Qed.

Lemma map_add_remove_comm {A B} : forall (m: fmap A B) {k1 k2} v2,
    (forall (x y:A), sumbool (x=y) (x<>y)) -> k1 <> k2 ->
    m $- k1 $+ (k2, v2) = m $+ (k2, v2) $- k1.
Proof.
  intros m k1 k2 v2 A_dec kneq; refine (map_eq_struct _); intro x.
  cases (A_dec x k1).
    invert e; rewrite (lookup_add_ne _ _ kneq);
        repeat rewrite (lookup_remove_eq _ (eq_refl _)); reflexivity.
    rewrite (lookup_remove_ne _ n); cases (A_dec x k2).
      invert e; repeat rewrite (lookup_add_eq _ _ (eq_refl _)); reflexivity.
      repeat rewrite (lookup_add_ne _ _ n0); rewrite (lookup_remove_ne _ n);
          reflexivity.
Qed.

Lemma map_add_idempotent {A B} : forall (m: fmap A B) k v1 v2,
    (forall (x y:A), sumbool (x=y) (x<>y)) ->
    m $+ (k, v1) $+ (k, v2) = m $+ (k, v2).
Proof.
  intros m k v1 v2 A_dec; refine (map_eq_struct _); intro x.
  cases (A_dec x k).
    invert e; repeat rewrite (lookup_add_eq _ _ (eq_refl _)); reflexivity.
    repeat rewrite (lookup_add_ne _ _ n); reflexivity.
Qed.

Lemma map_remove_idempotent {A B} : forall (m: fmap A B) k,
    (forall (x y:A), sumbool (x=y) (x<>y)) ->
    m $- k $- k = m $- k.
Proof.
  intros m k A_dec; refine (map_eq_struct _); intro x.
  cases (A_dec x k).
    invert e; repeat rewrite (lookup_remove_eq _ (eq_refl _)); reflexivity.
    repeat rewrite (lookup_remove_ne _ n); reflexivity.
Qed.

Lemma add_new_item : forall {A B} (m: fmap A B) k2 v2,
    (forall (x y:A), sumbool (x=y) (x<>y)) ->
    (forall k1 v1, (m $- k2) $? k1 = Some v1 ->
     (m $- k2 $+ (k2, v2)) $? k1 = Some v1).
Proof.
  intros A B m k2 v2 A_dec k1 v1 H.
  cases (A_dec k1 k2).
  - invert e; rewrite (lookup_remove_eq _ (eq_refl _)) in H; discriminate H.
  - rewrite (lookup_add_ne _ _ n), (lookup_remove_ne _ n).
    rewrite (lookup_remove_ne _ n) in H; exact H.
Qed.

Lemma g_rel_reduce {abst1 abst2 value_rel_abs G g1 g2} : forall x0,
    g_rel abst1 abst2 value_rel_abs G g1 g2
    -> g_rel abst1 abst2 value_rel_abs (G $- x0) (g1 $- x0) (g2 $- x0).
Proof.
  intros x0 H x; split.
  (* x is mapped *)
    intros t Hx.
    cases (string_dec x x0);
        [ rewrite (lookup_remove_eq _ (eq_sym e)) in Hx; discriminate Hx |].
    rewrite (lookup_remove_ne _ n) in Hx.
    elim (proj1 (H x) t Hx); intros v1 tmp; elimc tmp; intros v2 solution.
    exists v1, v2; repeat rewrite (lookup_remove_ne _ n).
    exact solution.
  (* x is not mapped *)
    cases (string_dec x x0);
        [ repeat rewrite (lookup_remove_eq _ (eq_sym e));
            exact (fun _ => (conj (eq_refl _) (eq_refl _))) |].
    repeat rewrite (lookup_remove_ne _ n).
    exact (proj2 (H x)).
Qed.

Lemma instantiation_type : forall {e1 G M g1 g2 value_rel_abs x t1 t2 abst1 abst2},
    hasty None ((adds M G) $+ (x, t1)) e1 t2 ->
    g_rel abst1 abst2 value_rel_abs G g1 g2 ->
    t1 <> AbsT ->
    hasty (Some abst1) (M $+ (x, t1)) (substs (g1 $- x) e1) t2
    /\
    hasty (Some abst2) (M $+ (x, t1)) (substs (g2 $- x) e1) t2.
Proof.
  intro e1; elimc e1; simplify.
  (* Var *)
    cases (string_dec x x0).
    (* x = x0 *)
      invert e; repeat rewrite (lookup_remove_eq _ (eq_refl _)).
      invert H; rewrite (lookup_add_eq _ _ (eq_refl _)) in H5.
      invert H5; split; exact (HtVar _ (lookup_add_eq _ _ (eq_refl _))).
    (* x <> x0 *)
      repeat rewrite (lookup_remove_ne _ n); invert H.
      rewrite (lookup_add_ne _ _ n) in  H5.
      cases (G $? x).
      (* G $? x = Some t *)
        unfold adds in H5; rewrite (lookup_merge _ _ _ _) in H5.
        repeat rewrite Heq in H5; invert H5.
        elim (proj1 (H0 x) _ Heq); intros v1 tmp; elimc tmp.
        intros v2 [g1v [g2v vrel]]; rewrite g1v, g2v.
        exact (conj
            (hasty_weakening_empty (proj1 (value_rel_hasty _ _ _ _ _ _ vrel)) _)
            (hasty_weakening_empty (proj2 (value_rel_hasty _ _ _ _ _ _ vrel)) _)
        ).
      (* G $? x = None *)
        unfold adds in H5; rewrite (lookup_merge _ _ _ _) in H5.
        rewrite Heq in H5.
        elim (proj2 (H0 x) Heq); intros g1x g2x.
        rewrite g1x, g2x; clear g1x g2x.
        split; refine (HtVar _ _); rewrite (lookup_add_ne _ _ n); exact H5.
  (* Abs *)
    invert H0; cases (string_dec x0 x).
    (* x0 = x *)
      invert e; repeat rewrite (map_remove_idempotent _ _ string_dec).
      rewrite (map_add_idempotent _ _ _ _ string_dec) in H7.
      assert (adds M G $+ (x, t0) = adds (M $- x) G $+ (x, t0)) as H8.
        refine (map_eq_struct _); intro x'; cases (string_dec x' x).
          invert e; repeat rewrite (lookup_add_eq _ _ (eq_refl _)); reflexivity.
          repeat rewrite (lookup_add_ne _ _ n).
          unfold adds; repeat rewrite (lookup_merge _ _ _ _).
          cases (G $? x'); try reflexivity.
          rewrite (lookup_remove_ne _ n); reflexivity.
      rewrite H8 in H7.
      repeat rewrite (map_remove_add M x t1 string_dec).
      exact (conj
          (hasty_weakening (HtAbs (proj1 (H _ _ _ _ _ _ _ _ _ _ H7 H1 H9)) H9)
              (add_new_item t1 string_dec))
          (hasty_weakening (HtAbs (proj2 (H _ _ _ _ _ _ _ _ _ _ H7 H1 H9)) H9)
              (add_new_item t1 string_dec))).
    (* x0 <> x *)
      refine ((fun rec_conj =>
          conj (HtAbs (proj1 rec_conj) H9) (HtAbs (proj2 rec_conj) H9)) _).
      rewrite (adds_add _ _ _ _) in H7; rewrite <- (adds_remove _ _ _ _) in H7.
      exact (H _ _ _ _ _ _ _ _ _ _ H7 (g_rel_reduce x0 H1) H9).
  (* App *)
    invert H1.
    pose (myfn := H _ _ _ _ _ _ _ _ _ _ H8 H2 H3).
    pose (myarg := H0 _ _ _ _ _ _ _ _ _ _ H10 H2 H3).
    exact (conj (HtApp (proj1 myfn) (proj1 myarg))
        (HtApp (proj2 myfn) (proj2 myarg))).
  (* Const *)
    invert H.
    exact (conj (HtConst _ _ _) (HtConst _ _ _)).
  (* Add *)
    invert H1.
    pose (myfst := H _ _ _ _ _ _ _ _ _ _ H8 H2 H3).
    pose (mysnd := H0 _ _ _ _ _ _ _ _ _ _ H10 H2 H3).
    exact (conj (HtAdd (proj1 myfst) (proj1 mysnd))
        (HtAdd (proj2 myfst) (proj2 mysnd))).
  (* Pair *)
    invert H1.
    pose (myfst := H _ _ _ _ _ _ _ _ _ _ H8 H2 H3).
    pose (mysnd := H0 _ _ _ _ _ _ _ _ _ _ H10 H2 H3).
    exact (conj (HtPair (proj1 myfst) (proj1 mysnd))
        (HtPair (proj2 myfst) (proj2 mysnd))).
  (* Fst *)
    invert H0.
    pose (myprod := H _ _ _ _ _ _ _ _ _ _ H6 H1 H2).
    exact (conj (HtFst (proj1 myprod)) (HtFst (proj2 myprod))).
  (* Snd *)
    invert H0.
    pose (myprod := H _ _ _ _ _ _ _ _ _ _ H6 H1 H2).
    exact (conj (HtSnd (proj1 myprod)) (HtSnd (proj2 myprod))).
Qed.

Lemma g_rel_add {abst1 abst2 value_rel_abs G g1 g2 t1 v1 v2} :
    g_rel abst1 abst2 value_rel_abs G g1 g2 ->
    value_rel abst1 abst2 value_rel_abs t1 v1 v2 ->
    forall x, g_rel abst1 abst2 value_rel_abs
        (G $+ (x, t1)) (g1 $+ (x, v1)) (g2 $+ (x, v2)).
Proof.
  simplify.
  intro x1; cases (string_dec x1 x).
  (* x1 = x *)
    invert e; repeat rewrite (lookup_add_eq _ _ (eq_refl _)).
    split; try discriminate.
    intros t tt1; invert tt1; exists v1, v2.
    exact (conj (eq_refl _) (conj (eq_refl _) H0)).
  (* x1 <> x *)
    repeat rewrite (lookup_add_ne _ _ n); exact (H x1).
Qed.

Theorem subst_cons {abst1 abst2 value_rel_abs} :
    forall {e M G g1 g2 x tx v1 v2 t},
    hasty None (adds M G $+ (x, tx)) e t ->
    g_rel abst1 abst2 value_rel_abs G g1 g2 ->
    value_rel abst1 abst2 value_rel_abs tx v1 v2 ->
    subst v1 x (substs (g1 $- x) e) = substs (g1 $+ (x, v1)) e
    /\
    subst v2 x (substs (g2 $- x) e) = substs (g2 $+ (x, v2)) e.
Proof.
  intro e; elimc e.
  (* Var *)
    simplify; cases (string_dec x x0).
    (* x = x0 *)
      invert e; repeat rewrite (lookup_add_eq _ _ (eq_refl _));
          repeat rewrite (lookup_remove_eq _ (eq_refl _)).
      simpl; cases (x0 ==v x0); [ | pinvert (n (eq_refl _)) ].
      exact (conj (eq_refl _) (eq_refl _)).
    (* x <> x0 *)
      repeat rewrite (lookup_add_ne _ _ n).
      repeat rewrite (lookup_remove_ne _ n).
      cases (G $? x).
      (* x in g1 *)
        invert H.
        rewrite (lookup_add_ne _ _ n) in H5.
        unfold adds in H5; rewrite (lookup_merge _ _ _ _) in H5.
        repeat rewrite Heq in H5; invert H5.
        elim (proj1 (H0 x) _ Heq); intros v3 [v4 [eval3 [eval4 vrel]]].
        repeat rewrite eval3; repeat rewrite eval4.
        pose (v34t := value_rel_hasty _ _ _ _ _ _ vrel).
        exact (conj (value_hasty_closed (proj1 v34t) _ _)
            (value_hasty_closed (proj2 v34t) _ _)).
      (* x not in g1 *)
        repeat rewrite (proj1 (proj2 (H0 x) Heq)).
        repeat rewrite (proj2 (proj2 (H0 x) Heq)).
        simpl; cases (x ==v x0); [ pinvert (n e) | ].
        exact (conj (eq_refl _) (eq_refl _)).
  (* Abs *)
    simplify; cases (string_dec x x0).
    (* x = x0 *)
      invert e; cases (x0 ==v x0); try pinvert (n (eq_refl _)); clear e.
      repeat rewrite (map_remove_idempotent _ _ string_dec).
      repeat rewrite (map_add_remove _ _ _ string_dec).
      exact (conj (eq_refl _) (eq_refl _)).
    (* x <> x0 *)
      cases (x ==v x0); try pinvert (n e); pinvert H0.
      repeat rewrite (map_remove_comm _ _ x string_dec).
      repeat rewrite <- (map_add_remove_comm _ _ string_dec n).
      rewrite <- (map_add_comm _ _ _ string_dec n) in H7.
      rewrite (adds_add _ _ _ _) in H7; rewrite <- (adds_remove _ _ _ _) in H7.
      rewrite (proj1 (H _ _ _ _ x0 _ _ _ _ H7 (g_rel_reduce x H1) H2)).
      rewrite (proj2 (H _ _ _ _ x0 _ _ _ _ H7 (g_rel_reduce x H1) H2)).
      exact (conj (eq_refl _) (eq_refl _)).
  (* App *)
    simplify.
    invert H1.
    rewrite (proj1 (H _ _ _ _ _ _ _ _ _ H8 H2 H3)).
    rewrite (proj2 (H _ _ _ _ _ _ _ _ _ H8 H2 H3)).
    rewrite (proj1 (H0 _ _ _ _ _ _ _ _ _ H10 H2 H3)).
    rewrite (proj2 (H0 _ _ _ _ _ _ _ _ _ H10 H2 H3)).
    exact (conj (eq_refl _) (eq_refl _)).
  (* Const *)
    simplify.
    exact (conj (eq_refl _) (eq_refl _)).
  (* Add *)
    simplify.
    invert H1.
    rewrite (proj1 (H _ _ _ _ _ _ _ _ _ H8 H2 H3)).
    rewrite (proj2 (H _ _ _ _ _ _ _ _ _ H8 H2 H3)).
    rewrite (proj1 (H0 _ _ _ _ _ _ _ _ _ H10 H2 H3)).
    rewrite (proj2 (H0 _ _ _ _ _ _ _ _ _ H10 H2 H3)).
    exact (conj (eq_refl _) (eq_refl _)).
  (* Pair *)
    simplify.
    invert H1.
    rewrite (proj1 (H _ _ _ _ _ _ _ _ _ H8 H2 H3)).
    rewrite (proj2 (H _ _ _ _ _ _ _ _ _ H8 H2 H3)).
    rewrite (proj1 (H0 _ _ _ _ _ _ _ _ _ H10 H2 H3)).
    rewrite (proj2 (H0 _ _ _ _ _ _ _ _ _ H10 H2 H3)).
    exact (conj (eq_refl _) (eq_refl _)).
  (* Fst *)
    simplify.
    invert H0.
    rewrite (proj1 (H _ _ _ _ _ _ _ _ _ H6 H1 H2)).
    rewrite (proj2 (H _ _ _ _ _ _ _ _ _ H6 H1 H2)).
    exact (conj (eq_refl _) (eq_refl _)).
  (* Snd *)
    simplify.
    invert H0.
    rewrite (proj1 (H _ _ _ _ _ _ _ _ _ H6 H1 H2)).
    rewrite (proj2 (H _ _ _ _ _ _ _ _ _ H6 H1 H2)).
    exact (conj (eq_refl _) (eq_refl _)).
Qed.

Theorem logical_rel_fundamental_aux:
  forall abst1 abst2 (value_rel_abs: exp -> exp -> Prop),
    (forall v1 v2, value_rel_abs v1 v2 -> value v1 /\ value v2) ->
    abst1 <> AbsT ->
    abst2 <> AbsT ->
    forall e G t,
      hasty None G e t ->
      forall g1 g2,
      g_rel abst1 abst2 value_rel_abs G g1 g2 ->
      exp_rel abst1 abst2 value_rel_abs t (substs g1 e) (substs g2 e).
Proof.
  intros abst1 abst2 value_rel_abs H abst1NA abst2NA e; elimc e.
  (* Var *)
    simplify.
    invert H0.
    elim (proj1 (H1 x) t H5); intros x1 T; elimc T; intros x2 [g1x [g2x vrel]].
    rewrite g1x, g2x. clear g1x g2x.
    pose (types := value_rel_hasty abst1 abst2 value_rel_abs _ _ _ vrel).
    refine (conj (proj1 types) (conj (proj2 types) _)); clear types.
    exists x1, x2.
    exact (conj (value_eval (proj1 (value_rel_value _ _ _ H _ _ _ vrel)))
       (conj (value_eval (proj2 (value_rel_value _ _ _ H _ _ _ vrel))) vrel)).
  (* Abs *)
    simplify.
    unfold exp_rel, exp_rel'.
    invert H1.
    pose (H7bis := H7); rewrite <- (adds_empty1 G) in H7bis.
    pose (part1 := instantiation_type H7bis H2 H9).
    refine (conj (HtAbs (proj1 part1) H9) (conj (HtAbs (proj2 part1) H9) _)).
    exists (\ x, substs (g1 $- x) e1), (\ x, substs (g2 $- x) e1).
    refine (conj (BigAbs _ _) (conj (BigAbs _ _) _)).
    simplify.
    refine (conj (HtAbs (proj1 part1) H9) (conj (HtAbs (proj2 part1) H9) _)).
    intros v1 v2 tv1 tv2 vrel.
    rewrite (proj1 (subst_cons H7bis H2 vrel)).
    rewrite (proj2 (subst_cons H7bis H2 vrel)).
    exact (H0 _ _ H7 _ _ (g_rel_add H2 vrel x)).
  (* App *)
    simplify.
    unfold exp_rel, exp_rel'.
    invert H2.
    pose (rec1 := H0 _ _ H8 _ _ H3).
    pose (rec2 := H1 _ _ H10 _ _ H3).
    refine (conj (HtApp (proj1 rec1) (proj1 rec2)) _).
    refine (conj (HtApp (proj1 (proj2 rec1)) (proj1 (proj2 rec2))) _).
    elim (proj2 (proj2 rec1)); intros fn1 tmp; elimc tmp;
        intros fn2 [fn1v [fn2v vrelfn]].
    elim (proj2 (proj2 rec2)); intros v1 tmp; elimc tmp;
        intros v2 [v1v [v2v vrel]].
    pose (fn12t := value_rel_hasty _ _ _ _ _ _ vrelfn).
    elim (hasty_Fun_value (proj1 fn12t) (eval_value fn1v)).
    intros x1 tmp; elimc tmp; intros x1t tmp; elimc tmp; intros x1e [fn1eq x1h].
    elim (hasty_Fun_value (proj2 fn12t) (eval_value fn2v)).
    intros x2 tmp; elimc tmp; intros x2t tmp; elimc tmp; intros x2e [fn2eq x2h].
    invert fn1eq.
    pose (v12h := value_rel_hasty _ _ _ _ _ _ vrel).
    elim (proj2 (proj2 (proj2 (proj2 vrelfn) _ _
        (proj1 v12h) (proj2 v12h) vrel))).
    intros vf1 [vf2 [evalf1 [evalf2 vrelf]]]; exists vf1, vf2.
    exact (conj (BigApp fn1v v1v evalf1) (conj (BigApp fn2v v2v evalf2) vrelf)).
  (* Const *)
    simplify.
    unfold exp_rel, exp_rel'.
    invert H0.
    refine (conj (HtConst _ _ _) (conj (HtConst _ _ _) _)).
    exists n, n.
    exact (conj (BigConst n) (conj (BigConst n) (eq_refl _))).
  (* Add *)
    simplify.
    invert H2.
    pose (rec1 := H0 _ _ H8 _ _ H3).
    pose (rec2 := H1 _ _ H10 _ _ H3).
    unfold exp_rel, exp_rel'.
    refine (conj (HtAdd (proj1 rec1) (proj1 rec2)) _).
    refine (conj (HtAdd (proj1 (proj2 rec1)) (proj1 (proj2 rec2))) _).
    elim (proj2 (proj2 rec1)); intros v1a [v2a [eval1a [eval2a vrela]]].
    elim (proj2 (proj2 rec2)); intros v1b [v2b [eval1b [eval2b vrelb]]].
    cases v1a; cases v2a; try invert vrela.
    cases v1b; cases v2b; try invert vrelb.
    exists (Const (n0 + n1)), (Const (n0 + n1)).
    refine (conj (BigAdd eval1a eval1b) _).
    refine (conj (BigAdd eval2a eval2b) _).
    reflexivity.
  (* Pair *)
    simplify.
    invert H2.
    pose (rec1 := H0 _ _ H8 _ _ H3).
    pose (rec2 := H1 _ _ H10 _ _ H3).
    unfold exp_rel, exp_rel'.
    refine (conj (HtPair (proj1 rec1) (proj1 rec2)) _).
    refine (conj (HtPair (proj1 (proj2 rec1)) (proj1 (proj2 rec2))) _).
    elim (proj2 (proj2 rec1)); intros v1a [v2a [eval1a [eval2a vrela]]].
    elim (proj2 (proj2 rec2)); intros v1b [v2b [eval1b [eval2b vrelb]]].
    exists (Pair v1a v1b), (Pair v2a v2b).
    refine (conj (BigPair eval1a eval1b) _).
    refine (conj (BigPair eval2a eval2b) _).
    exact (conj vrela vrelb).
  (* Fst *)
    simplify.
    invert H1.
    pose (rec := H0 _ _ H6 _ _ H2).
    refine (conj (HtFst (proj1 rec)) (conj (HtFst (proj1 (proj2 rec))) _)).
    elim (proj2 (proj2 rec)); intros v1 [v2 [eval1 [eval2 vrel]]].
    cases v1; cases v2; try invert vrel.
    exists v1_1, v2_1.
    exact (conj (BigFst eval1) (conj (BigFst eval2) H1)).
  (* Snd *)
    simplify.
    invert H1.
    pose (rec := H0 _ _ H6 _ _ H2).
    refine (conj (HtSnd (proj1 rec)) (conj (HtSnd (proj1 (proj2 rec))) _)).
    elim (proj2 (proj2 rec)); intros v1 [v2 [eval1 [eval2 vrel]]].
    cases v1; cases v2; try invert vrel.
    exists v1_2, v2_2.
    exact (conj (BigSnd eval1) (conj (BigSnd eval2) H3)).
Qed.

Theorem logical_rel_fundamental:
  forall abst1 abst2 (value_rel_abs: exp -> exp -> Prop),
    (forall v1 v2, value_rel_abs v1 v2 -> value v1 /\ value v2) ->
    abst1 <> AbsT ->
    abst2 <> AbsT ->
    forall e G t,
      hasty None G e t ->
      logical_rel abst1 abst2 value_rel_abs G e e t.
Proof.
  simplify.
  refine (conj (hasty_weakening_abst H2 abst1)
      (conj (hasty_weakening_abst H2 abst2) _)).
  simplify; unfold exp_rel, exp_rel'.
  exact (logical_rel_fundamental_aux H H0 H1 H2 H3).
Qed.

Theorem counter_impls_equiv:
  forall x e,
    hasty None ($0 $+ (x, counter_type)) e Nat ->
    exists n : nat,
      eval (subst counter_impl1 x e) n /\ eval (subst counter_impl2 x e) n.
Proof.
  assert (forall v1 v2 : exp, value_rel_counters v1 v2 -> value v1 /\ value v2)
      as H1.
    intros v1 v2 H; invert H.
    exact (conj (VConst _) (VPair (VConst _) (VConst _))).
  assert (Nat <> AbsT) as H2; try discriminate.
  assert (Nat ^*^ Nat <> AbsT) as H3; try discriminate.
  intros x e H4.
  assert (g_rel Nat (Nat ^*^ Nat) value_rel_counters ($0 $+ (x, counter_type))
      ($0 $+ (x, counter_impl1)) ($0 $+ (x, counter_impl2))) as H5.
    intros x1; cases (string_dec x1 x).
    (* x1 = x *)
      invert e0; repeat rewrite (lookup_add_eq _ _ (eq_refl _)).
      split; try discriminate.
      intros t ct; invert ct; exists counter_impl1, counter_impl2.
      exact (conj (eq_refl _) (conj (eq_refl _) counter_impls_related)).
    (* x1 <> x *)
      repeat rewrite (lookup_add_ne _ _ n); repeat rewrite (lookup_empty _ x1).
      split; try discriminate.
      exact (fun _ => conj (eq_refl _) (eq_refl _)).
  pose (log_rel := (logical_rel_fundamental value_rel_counters H1 H2 H3 H4)).
  elim (proj2 (proj2 (proj2 (proj2 log_rel) _ _ H5))).
  intros v1 [v2 [eval1 [eval2 vrel]]].
  cases v1; cases v2; try invert vrel.
  rewrite (substs_single _ _ _) in eval1.
  rewrite (substs_single _ _ _) in eval2.
  exists n0; exact (conj eval1 eval2).
Qed.
