Require Import Frap Pset13Sig.

Set Implicit Arguments.

Ltac elimc var := elim var; clear var.
Ltac pinvert expr := pose (pinvert_tmp := expr); invert pinvert_tmp.

Definition my_rel (init: nat) : hrel :=
  fun h h' : heap => h' $! 0 >= init /\ (h $! 0 > init -> h' $! 0 > init).

Lemma ht_prog1_read (init: nat) :
    hoare_triple
      (fun h : heap => h $! 0 >= init)
      (fun h h' : heap => my_rel init h h' \/ my_rel init h h')
      (Atomic (Read 0))
      (my_rel init)
      (fun (n: nat) (h : heap) => n >= init).
Proof.
  refine (HtAtomic _ _ _ _).
  - intros v h h' H1 H2; invert H2; existT_subst.
    exact (conj H1 (fun H => H)).
  - intros v h h' H1 H2; invert H2; existT_subst; exact H1.
  - split.
      intros h h' H1 H2; cases H2; exact (proj1 H).
      intros v h h' H1 H2; exact H1.
Qed.

Lemma ht_prog1_write (init: nat) (tmp: nat) :
    hoare_triple
      (fun h : heap => tmp >= init)
      (fun h h' : heap => my_rel init h h' \/ my_rel init h h')
      (Atomic (Write 0 (tmp + 1)))
      (my_rel init)
      (fun (_ : unit) (h : heap) => h $! 0 > init).
Proof.
  refine (HtAtomic _ _ _ _).
  - intros v h h' H1 H2; invert H2; existT_subst.
    split; rewrite (lookup_add_eq _ _ (eq_refl _)).
      exact (le_trans _ _ _ H1 (le_plus_l tmp 1)).
      refine (fun _ => le_lt_trans _ _ _ H1 _); rewrite (plus_comm _ _);
          exact (le_n _).
  - intros v h h' H1 H2; invert H2; existT_subst.
    rewrite (lookup_add_eq _ _ (eq_refl _)).
    refine (le_lt_trans _ _ _ H1 _).
    rewrite (plus_comm _ _); exact (le_n _).
  - split.
      intros h h' H1 H2; exact H1.
      intros v h h' H1 H2; cases H2; exact (proj2 H H1).
Qed.

Lemma ht_prog1_th (init: nat) :
    hoare_triple
      (fun h : heap => h $! 0 >= init)
      (fun h h' : heap => my_rel init h h' \/ my_rel init h h')
      (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
      (my_rel init)
      (fun (_ : unit) (h : heap) => h $! 0 > init).
Proof HtBind _ (ht_prog1_read init) (ht_prog1_write init).

Theorem ht_prog1 : forall init, hoare_triple
                                (fun h => h $! 0 = init)
                                (fun _ _ => False)
                                prog1
                                (fun _ _ => True)
                                (fun _ h => h $! 0 > init).
Proof.
  intro init.
  refine  (HtConsequence _ _ (HtPar (ht_prog1_th init) (ht_prog1_th init) _
      (fun _ H => H) (fun _ H => H)) _ _ _ _ _).
  - intros h h' H1 H2; exact (proj1 H2).
  - intros h H; rewrite H; exact (le_n _).
  - exact (fun _ _ H => proj1 H).
  - invert 1.
  - exact (fun _ _ _ => I).
  - intros h h' H1 H2; invert H2.
Qed.


Lemma hoare_return_cl : forall {t:Set} {v:t} {P R G Q},
    hoare_triple P R (Return v) G Q -> forall h:heap, P h -> Q v h.
Proof.
  induct 1.
    exact (fun _ H => conj H (eq_refl _)).
    exact (fun _ H => H1 _ _ (IHhoare_triple _ (H0 _ H))).
Qed.

Lemma or_subst {A B C: Prop} : (B -> C) -> A \/ B -> A \/ C.
Proof. tauto. Qed.
Lemma or_incr3 {A B C: Prop} : A \/ B -> A \/ B \/ C.
Proof. tauto. Qed.
Lemma or_incr2 {A B C: Prop} : A \/ C -> A \/ B \/ C.
Proof. tauto. Qed.

Theorem hoare_triple_step :
  forall {t : Set} {c : cmd t} {P: hprop} {R G Q h h' c'},
    P h -> hoare_triple P R c G Q ->
    step (h, c) (h', c') ->
    (h = h' \/ G h h') /\ exists P',
      P' h' /\ hoare_triple P' R c' G Q.
Proof.
  intros t c; elimc c; induct 2; simplify.
  (* Return *)
    invert H1.
    invert H6.
  (* Bind *)
    (* HtBind *)
      clear H4; clear IHhoare_triple; invert H5; existT_subst.
      (* StepBindRecur *)
        pose (Hrec := H _ _ _ _ _ _ _ H1 H2 H7).
        elim (proj2 Hrec); intros P' [P'H Htriple1].
        refine (conj (proj1 Hrec) _); exists P'; refine (conj P'H _).
        exact (HtBind _ Htriple1 H3).
      (* StepBindProceed *)
        exact (conj (or_introl (eq_refl _)) (ex_intro _ _
            (conj (hoare_return_cl H2 _ H1) (H3 v0)))).
    (* HtConsequence *)
      pose (Hrec := IHhoare_triple _ (H6 _ H1) _ _ H _ H0 (eq_refl _) H8).
      elim (proj2 Hrec); intros P'0 [P'0H Htriple].
      refine (conj (or_subst (H3 _ _) (proj1 Hrec)) _); exists P'0.
      refine (conj P'0H (HtConsequence _ _ Htriple (fun _ H => H) H7 H5 H3 _)).
      exact (stableP_weakenR (always_stableP Htriple) _ H5).
  (* Fail *)
    invert H0.
    invert H6.
  (* Par *)
    (* HtPar *)
      clear IHhoare_triple1; clear IHhoare_triple2.
      invert H5; existT_subst.
      (* c1 run *)
        pose (Hrec := H _ _ _ _ _ _ _ (H3 _ H1) H2_ H8).
        elim (proj2 Hrec); intros P1' [P1'H Htriple1].
        refine (conj (or_incr3 (proj1 Hrec)) _).
        exists (fun h:heap => P1' h /\ P2 h).
        assert (P2 h') as P2'H.
          cases (proj1 Hrec).
            pinvert e; exact (H2 _ H1).
            exact (always_stableP H2_0 h h' (H2 _ H1) (or_intror g)).
        refine (conj (conj P1'H P2'H) (HtPar Htriple1 H2_0 _
            (fun _ H => proj1 H) (fun _ H => proj2 H))).
        intros h1 h2 [hyp1 hyp2] Hrel.
        exact (conj
            (always_stableP Htriple1 h1 h2 hyp1 (or_introl Hrel))
            (always_stableP H2_0 h1 h2 hyp2 (or_introl Hrel))).
      (* c2 run (same thing, symmetrically) *)
        pose (Hrec := H0 _ _ _ _ _ _ _ (H2 _ H1) H2_0 H8).
        elim (proj2 Hrec); intros P2' [P2'H Htriple2].
        refine (conj (or_incr2 (proj1 Hrec)) _).
        exists (fun h:heap => P1 h /\ P2' h).
        assert (P1 h') as P1'H.
          cases (proj1 Hrec).
            pinvert e; exact (H3 _ H1).
            exact (always_stableP H2_ h h' (H3 _ H1) (or_intror g)).
        refine (conj (conj P1'H P2'H) (HtPar H2_ Htriple2 _
            (fun _ H => proj1 H) (fun _ H => proj2 H))).
        intros h1 h2 [hyp1 hyp2] Hrel.
        exact (conj
            (always_stableP H2_ h1 h2 hyp1 (or_introl Hrel))
            (always_stableP Htriple2 h1 h2 hyp2 (or_introl Hrel))).
    (* HtConsequence *)
      pose (Hrec := IHhoare_triple (H7 _ H1) _ _ H0 _ H (eq_refl _)
          (JMeq.JMeq_refl _) (JMeq.JMeq_refl _) H8).
      elim (proj2 Hrec); intros P'0 [P'0H Htriple].
      refine (conj (or_subst (H3 _ _) (proj1 Hrec)) _); exists P'0.
      refine (conj P'0H (HtConsequence _ _ Htriple (fun _ H => H) H6 H5 H3 _)).
      exact (stableP_weakenR (always_stableP Htriple) _ H5).
  (* Atomic *)
    (* HtAtomic *)
      invert H3; existT_subst; invert H6; existT_subst.
      (* Read *)
        pose (myP := (fun h:heap => P h /\ Q (h' $! a0) h)).
        refine (conj (or_introl (eq_refl _)) _); exists myP.
        refine (conj (conj H (H0 _ _ _ H (StepRead _ _))) _).
        assert (stableP myP R) as Hstable.
          intros h1 h2 [Ph1 Qh1] Hrel.
          exact (conj (proj1 H1 h1 h2 Ph1 Hrel)
              (proj2 H1 (h' $! a0) h1 h2 Qh1 Hrel)).
        refine (HtWeaken _ (HtReturn G (h' $! a0) Hstable) _).
        intros v h [Ph veq]; invert veq.
        exact (proj2 Ph).
      (* Write *)
        refine (conj (or_intror (H2 _ _ _ H (StepWrite _ _ _))) _).
        exists (Q tt); refine (conj (H0 _ _ _ H (StepWrite _ _ _)) _).
        refine (HtWeaken _ (HtReturn G _ (proj2 H1 tt)) _).
        intros v h' [HQ veq]; invert veq; exact HQ.
    (* HtConsequence *)
      pose (Hrec := IHhoare_triple _ _ (H5 _ H) (eq_refl _) H6).
      elim (proj2 Hrec); intros P'0 [P'0H Htriple].
      refine (conj (or_subst (H3 _ _) (proj1 Hrec)) _); exists P'0.
      refine (conj P'0H (HtConsequence _ _ Htriple (fun _ H => H) H1 H2 H3 _)).
      exact (stableP_weakenR (always_stableP Htriple) _ H2).
  (* Loop *)
    (* HtLoop *)
      clear H2; invert H4; existT_subst.
      refine (conj (or_introl (eq_refl _)) _); exists (I (Again init)).
      refine (conj H0 (HtBind _ (H3 init) _)).
      intro r; cases r.
      (* Done *)
        refine (HtWeaken _  (HtReturn _ _ (H1 a)) _).
        intros v h [HI veq]; invert veq; exact HI.
      (* Again *)
        exact (HtLoop _ _ H3 H1 ).
    (* HtConsequence *)
      pose (Hrec := IHhoare_triple _ (H6 _ H0) _ H _ (eq_refl _) H7).
      elim (proj2 Hrec); intros P'0 [P'0H Htriple].
      refine (conj (or_subst (H3 _ _) (proj1 Hrec)) _); exists P'0.
      refine (conj P'0H (HtConsequence _ _ Htriple (fun _ H => H) H5 H2 H3 _)).
      exact (stableP_weakenR (always_stableP Htriple) _ H2).
Qed.

Theorem hoare_triple_invariant {t: Set} {c: cmd t} {P Q h}:
    hoare_triple P (fun _ _ => False) c (fun _ _ => True) Q ->
    P h ->
    invariantFor (trsys_of h c) (fun st =>
      exists P',
        P' (fst st)
        /\
        hoare_triple P' (fun _ _ => False) (snd st) (fun _ _ => True) Q).
Proof.
  intros Htriple0 Ph; refine (invariant_induction _ _ _ _).
  (* Base case *)
    intros s Hi; invert Hi; try invert H.
    exists P; exact (conj Ph Htriple0).
  (* Induction *)
    intros [h1 c1] [P' [HP' Htriple]] [h2 c2] Hstep.
    exact (proj2 (hoare_triple_step HP' Htriple Hstep)).
Qed.

Lemma triple_not_failing {t: Set} {c: cmd t} : forall {h P R G Q},
    hoare_triple P R c G Q ->
    P h ->
    notAboutToFail c.
Proof.
  elimc c; induct 1.
  (* Return *)
    exact (fun _ => NatfReturn _).
    exact (fun _ => NatfReturn _).
  (* Bind *)
    exact (fun HP1 => NatfBind _ (H _ _ _ _ _ H1 HP1)).
    exact (fun Hhyp => IHhoare_triple _ _ H _ H0 (eq_refl _) (H5 _ Hhyp)).
  (* Fail *)
    intro absurd; invert absurd.
    exact (fun Hhyp => IHhoare_triple (H0 _ Hhyp)).
  (* Par *)
    exact (fun HP => NatfPar (H _ _ _ _ _ H1_ (H2 _ HP))
        (H0 _ _ _ _ _ H1_0 (H1 _ HP))).
    exact (fun HP => IHhoare_triple _ _ H0 _ H (eq_refl _)
        (JMeq.JMeq_refl _) (JMeq.JMeq_refl _) (H6 _ HP)).
  (* Atomic *)
    exact (fun _ => NatfAtomic _).
    exact (fun _ => NatfAtomic _).
  (* Loop *)
    exact (fun _ => NatfLoop _ _).
    exact (fun _ => NatfLoop _ _).
Qed.

Theorem hoare_triple_sound :
  forall (t : Set) P (c : cmd t) Q,
    hoare_triple P (fun _ _ => False) c (fun _ _ => True) Q ->
    forall h,
      P h ->
      invariantFor (trsys_of h c) (fun st => notAboutToFail (snd st)).
Proof.
  intros t P c Q H h Ph.
  refine (invariant_weaken _ (hoare_triple_invariant H Ph) _).
  clear Ph; clear h; clear H; clear c; clear P.
  intros [h c] [P [HP Htriple]]; exact (triple_not_failing Htriple HP).
Qed.
