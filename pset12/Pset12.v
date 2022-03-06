Require Import Frap Pset12Sig.

Require Import Classical_Prop.
Require Import ClassicalFacts.

Ltac elimc var := elim var; clear var.
Ltac pinvert expr := pose (pinvert_tmp := expr); invert pinvert_tmp.

Theorem has_min_or_empty (s: set nat) :
    s = {} \/ (exists n, n \in s /\ forall m, m<n -> ~m \in s).
Proof.
  cases (classic (exists r, r \in s)); clear Heq.
  (* s is not empty *)
    elimc e; intros r H; right.
    elim (excluded_middle_entails_unrestricted_minimization classic
        (fun x => x \in s) _ H); intros n [lH rH]; exists n.
    refine (conj lH _); clear lH.
    intros m H2 absurd; pinvert (le_not_lt _ _ (rH m absurd) H2).
  (* s is empty *)
    left; refine (sets_equal _ _ _); intro x; split; intro H.
      pinvert (n (ex_intro _ x H)).
      invert H.
Qed.

Theorem empty_union {A} {s1 s2: set A} :
    s1 \cup s2 = {} -> s1 = {}.
Proof.
  intro H; refine (sets_equal _ _ _); intro x; split.
    rewrite <- H; exact (fun H => or_introl H).
    intro absurd; invert absurd.
Qed.

Lemma cmd_return_check (c: cmd) :
  (exists v, c = Return v) \/ ~(exists v, c = Return v).
Proof.
  cases c; try (right; intros [v1 absurd]; discriminate absurd).
  exact (or_introl (ex_intro _ r (eq_refl _))).
Qed.

Lemma cmd_lock_check (c: cmd) :
  (exists a, c = Lock a) \/ ~(exists a, c = Lock a).
Proof.
  cases c; try (right; intros [a1 absurd]; discriminate absurd).
  exact (or_introl (ex_intro _ a (eq_refl _))).
Qed.

Lemma extract_prog : forall {m p},
    m \in locksOf p ->
    exists cs1 cs2 l c, p = cs1 ++ ((l, c)::cs2) /\ m \in l.
Proof.
  intros m p; elimc p; try (intro absurd; invert absurd).
  simplify.
  cases a; cases H0.
  (* First has m *)
    exists nil, l, s, c.
    exact (conj (eq_refl _) H0).
  (* Tail has m *)
    elim (H H0); intros cs1 [cs2 [l0 [c0 [Hlists Hhas]]]].
    exists ((s, c)::cs1), cs2, l0, c0.
    rewrite Hlists; clear Hlists.
    rewrite (app_comm_cons _ _ _).
    exact (conj (eq_refl _) Hhas).
Qed.

Lemma deadlock_freedom_nolocks : forall {c} h,
    ~ (exists v : nat, c = Return v) ->
    (exists l3, goodCitizen {} c l3) ->
    exists h2 l2 c2, step0 (h, {}, c) (h2, l2, c2).
Proof.
  intro c; elimc c; simplify.
  (* Return *)
    pinvert (H (ex_intro _ _ (eq_refl _))).
  (* Bind *)
    cases (cmd_return_check c1); clear Heq.
    (* c1 is Return *)
      elimc e; intros v c1eq; invert c1eq.
      exists h, {}, (c2 v); exact (StepBindProceed _ _ _ _).
    (* c1 is not Return *)
      elimc H2; intros l3 H2; invert H2.
      elim (H h n (ex_intro _ _ H6)); intros h4 [l4 [c4 H4]].
      exists h4, l4, (Bind c4 c2); exact (StepBindRecur _ H4).
  (* Read *)
    exact (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (StepRead _ _ _)))).
  (* Write *)
    exact (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (StepWrite _ _ _ _)))).
  (* Lock *)
    refine (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (StepLock _ _ _ _)))).
    intro absurd; invert absurd.
  (* Unlock *)
    refine (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (StepUnlock _ _ _ _)))).
    elimc H0; intros l3 absurd; invert absurd.
    invert H2.
Qed.

Lemma deadlock_freedom_goodcitz : forall {c l l1 m} h,
    ~ (exists v : nat, c = Return v) ->
    m \in l ->
    (exists l3, goodCitizen l c l3) ->
    (forall a : nat, a < m -> ~ a \in l1) ->
    l \subseteq l1 ->
    exists h2 l2 c2, step0 (h, l1, c) (h2, l2, c2).
Proof.
  intro c; elimc c; simplify.
  (* Return *)
    pinvert (H (ex_intro _ _ (eq_refl _))).
  (* Bind *)
    cases (cmd_return_check c1); clear Heq.
    (* c1 is Return *)
      elimc e; intros v c1eq; invert c1eq.
      exists h, l1, (c2 v); exact (StepBindProceed _ _ _ _).
    (* c1 is not Return *)
      elimc H3; intros l3 H3; invert H3.
      elim (H _ _ _ h n H2 (ex_intro _ _ H9) H4 H5); intros h4 [l4 [c4 Hstep0]].
      exists h4, l4, (Bind c4 c2); exact (StepBindRecur _ Hstep0).
  (* Read *)
    exact (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (StepRead _ _ _)))).
  (* Write *)
    exact (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (StepWrite _ _ _ _)))).
  (* Lock *)
    refine (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (StepLock _ _ _ _)))).
    elimc H1; intros l3 H1; invert H1.
    exact (H2 _ (H6 _ H0)).
  (* Unlock *)
    refine (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (StepUnlock _ _ _ _)))).
    elimc H1; intros l3 H1; invert H1.
    exact (H3 _ H6).
Qed.

Lemma deadlock_freedom_rec:
  forall (n: nat) (h : heap) (p : prog'), length p = n ->
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  Forall finished (progOf p) \/ (exists h_l_p' : heap * locks * prog,
                                    step (h, locksOf p, progOf p) h_l_p').
Proof.
  intro n; elimc n.
  (* No threads *)
    simplify; left.
    rewrite (proj1 (length_zero_iff_nil p) H).
    exact (Forall_nil _).
  (* Thread induction *)
    simplify.
    cases (has_min_or_empty (locksOf p)); clear Heq.
    (* No locks locked *)
      cases p; try discriminate H0; invert H1.
      cases (H h _ (eq_add_S _ _ H0) H5); clear Heq.
      (* Tail has finished *)
        cases p; cases (cmd_return_check c); clear Heq.
        (* First thread too *)
          elimc e0; intros v veq; invert veq.
          exact (or_introl (Forall_cons _ (Finished v) f)).
        (* First thread can continue *)
          pinvert e; rewrite e; right.
          rewrite (empty_union H2) in H4.
          elim (deadlock_freedom_nolocks h n0 (ex_intro _ _ H4)).
          intros h2 [l2 [c2 Hcont]].
          exists (h2, l2, c2::(progOf p0)).
          exact (StepThread nil (progOf p0) Hcont).
      (* Tail has continuation *)
        elimc e0; intros h_l_p' Hstep; cases h_l_p'; cases p1; cases p; right.
        pinvert e; rewrite e.
        rewrite (union_comm _ _) in H2.
        rewrite (empty_union H2) in Hstep; invert Hstep.
        unfold progOf; fold progOf; rewrite <- H7.
        rewrite (app_comm_cons _ _ _).
        exact (ex_intro _ _ (StepThread (c::cs1) cs2 H3)).
    (* Some locks locked *)
      elimc e; intros m [mlocked mmin]; right.
      elim (extract_prog mlocked); intros cs1 [cs2 [l [c [peq minl]]]].
      rewrite (f_equal progOf peq); rewrite (progOf_app _ _).
      assert (goodCitizen l c {}) as c_citz.
        rewrite peq in H1; pinvert (proj2 (Forall_app_fwd _ _ H1)); exact H4.
      assert (~(exists v : nat, c = Return v)) as c_not_return.
        intros [v ceq]; invert ceq; invert c_citz; invert minl.
      assert (l \subseteq locksOf p) as l_sub_lp.
        intros x Hlx; rewrite peq; rewrite (locksOf_app _ _).
        right; left; exact Hlx.
      elim (deadlock_freedom_goodcitz h c_not_return minl (ex_intro _ _ c_citz)
          mmin l_sub_lp); intros h2 [l2 [c2 solution]].
      exact (ex_intro _ _ (StepThread (progOf cs1) (progOf cs2) solution)).
Qed.

(* Since we use the [a_useful_invariant] theorem, proving [deadlock_freedom]
 * reduces to proving this lemma. *)
Lemma deadlock_freedom' :
  forall (h : heap) (p : prog'),
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  Forall finished (progOf p) \/ (exists h_l_p' : heap * locks * prog,
                                    step (h, locksOf p, progOf p) h_l_p').
Proof fun h p => deadlock_freedom_rec _ h p (eq_refl _).

Theorem deadlock_freedom :
  forall h p,
    Forall (fun c => goodCitizen {} c {}) p ->
    invariantFor (trsys_of h {} p) (fun h_l_p =>
                                      let '(_, _, p') := h_l_p in
                                      Forall finished p'
                                      \/ exists h_l_p', step h_l_p h_l_p').
Proof.
  (* To begin with, we strengthen the invariant to the one proved in Pset12Sig. *)
  simplify.
  eapply invariant_weaken.
  eauto using a_useful_invariant.

  (* What's left is to prove that that invariant implies deadlock-freedom. *)
  first_order.
  destruct s as [[h' ls] p'].
  invert H0.

  (* We don't actually need to use the [disjointLocks] property.  It was only
   * important in strengthening the induction to prove that other invariant. *)
  clear H6.

  (* At this point, we apply the lemma that we expect you to prove! *)
  apply deadlock_freedom'. assumption.
Qed.
