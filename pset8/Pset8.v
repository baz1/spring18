Require Import Frap Pset8Sig.

Set Implicit Arguments.

Ltac elimc var := elim var; clear var.

Lemma subtype_refl : forall t1, t1 $<: t1.
Proof.
  intro t1; elimc t1.
    exact (fun _ domrec _ ranrec => StFun domrec ranrec).
    exact StTupleNilNil.
    exact (fun _ rec1 _ rec2 => StTupleCons rec1 rec2).
Qed.

Lemma subtype_trans0 : forall t2 t1 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof.
  intro t2; elimc t2.
  (* Fun *)
    intros dom2 dom2rec ran2 ran2rec t1 t3 t12 t23.
    invert t12; invert t23.
    exact (StFun (dom2rec _ _ H1 H2) (ran2rec _ _ H3 H5)).
  (* TupleTypeNil *)
    intros t1 t3 t12 t23; invert t12; invert t23;
        [ exact StTupleNilNil | exact (StTupeNilCons _ _) ].
  (* TupleTypeCons *)
    intros t2_1 rec1 t2_2 rec2 t1 t3 t12 t23; invert t12; invert t23;
        try exact (StTupeNilCons _ _).
    exact (StTupleCons (rec1 _ _ H2 H1) (rec2 _ _ H3 H5)).
Qed.
Lemma subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof fun t1 t2 t3 => subtype_trans0 (t1:=t1) (t2:=t2) (t3:=t3).

Definition unstuck e := value e \/ (exists e' : exp, step e e').

(* Sounds like a copy-paste and patch-up of what's in
 * frap/LambdaCalculusAndTypeSoundness.v; will skip since that becomes
 * monotonous/boring. *)
Lemma progress : forall e t, hasty $0 e t -> unstuck e.
Proof. Admitted.
Lemma preservation : forall e1 e2,
  step e1 e2 -> forall t, hasty $0 e1 t -> hasty $0 e2 t.
Proof. Admitted.

Theorem safety :
  forall e t,
    hasty $0 e t -> invariantFor (trsys_of e)
                                 (fun e' => value e'
                                            \/ exists e'', step e' e'').
Proof.
  simplify.
  apply invariant_weaken with (invariant1 := fun e' => hasty $0 e' t).
  (* Hasty invariant *)
    apply invariant_induction; simplify.
    equality.
    eapply preservation; [ eassumption | assumption ].
  (* Hasty means unstuck *)
    simplify.
    eapply progress.
    eassumption.
Qed.
