(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 10 *)

Require Import Frap.

(* Authors: 
 * Joonwon Choi (joonwonc@csail.mit.edu)
 * Adam Chlipala (adamc@csail.mit.edu) 
 *)

Set Implicit Arguments.

Ltac elimc var := elim var; clear var.
Ltac pinvert expr := pose (pinvert_tmp := expr); invert pinvert_tmp.

(** * Hoare Logic with Input/Output Traces *)

(* Hoare logic as covered in lecture is only the beginning, so far as
 * programming features that can be supported. In this problem set, we
 * will implement one of variant, a Hoare logic that deals with
 * input/output traces.
 *
 * As we learned in compiler verification, behaviors of a program can be
 * defined as sequences of communications with the outside world. Hoare logic
 * certainly can be used for proving properties about program behaviors.
 * Besides valuation and heap, we will need to keep track of traces of a program
 * to ensure the properties we want, sometimes by proving invariants in the
 * middle of the program.
 *
 * The problem set consists of 4 tasks; basically we ask you to formally prove 
 * the correctness of some programs using Hoare logic:
 * 1) To design a big-step operational semantics of the given language.
 * 2) To define a Hoare logic for the language, and to prove the consistency
 *    between the semantics and the logic.
 * 3) To verify three example programs we provide, using Hoare logic.
 * 4) To design your own interesting program and to verify it.
 *)

(** * Language syntax *)

(* There is nothing special with the definitions of [exp] and [bexp]; they are
 * exactly same as we've seen in the lecture.
 *)
Inductive exp :=
| Const (n : nat)
| Var (x : string)
| Read (e1 : exp)
| Plus (e1 e2 : exp)
| Minus (e1 e2 : exp)
| Mult (e1 e2 : exp).

Inductive bexp :=
| Equal (e1 e2 : exp)
| Less (e1 e2 : exp).

(* [heap] and [valuation] are also as usual. *)
Definition heap := fmap nat nat.
Definition valuation := fmap var nat.

(* Besides [heap] and [valuation], we have one more component to verify using 
 * Hoare logic, called [io]. We keep track of inputs and outputs of a certain
 * program, regarding them as meaningful communication with the outside world.
 * When a program is executed, it generates [trace], which is a list of [io]s,
 * meaning inputs and outputs that occurred during the execution. Traces are
 * also called behaviors of a program.
 *)
Inductive io := In (v : nat) | Out (v : nat).
Definition trace := list io.

(* We now have two types of assertions: [iassertion] is used only for asserting 
 * properties of internal states. [assertion] can be used for asserting 
 * properties of [trace]s as well as internal states.
 *)
Definition iassertion := heap -> valuation -> Prop.
Definition assertion := trace -> heap -> valuation -> Prop.

(* [cmd] has more constructors than what we've seen.  The new ones are called
 * [Input] and [Output]. As expected, semantically they generates [io]s,
 * eventually forming a [trace] of a program.
 *)
Inductive cmd :=
| Skip
| Assign (x : var) (e : exp)
| Write (e1 e2 : exp)
| Seq (c1 c2 : cmd)
| If_ (be : bexp) (then_ else_ : cmd)
| While_ (inv : assertion) (be : bexp) (body : cmd)

| Assert (a : iassertion) (* Note that we are using [iassertion], not 
                           * [assertion], for [Assert]. While [valuation] and
                           * [heap] are internal states directly manipulated by
                           * a program, [trace] is rather an abstract notion for
                           * defining a behavior of a program.
                           *)

(* The new constructors are below! *)
| Input (x : var) (* [Input] takes an input from the external world and assigns
                   * the value to the local variable [x].
                   *)
| Output (e : exp). (* [Output] prints the value of [e]. *)

(** We here provide fancy notations for our language. *)

Coercion Const : nat >-> exp.
Coercion Var : string >-> exp.
Notation "*[ e ]" := (Read e) : cmd_scope.
Infix "+" := Plus : cmd_scope.
Infix "-" := Minus : cmd_scope.
Infix "*" := Mult : cmd_scope.
Infix "=" := Equal : cmd_scope.
Infix "<" := Less : cmd_scope.
Definition set (dst src : exp) : cmd :=
  match dst with
  | Read dst' => Write dst' src
  | Var dst' => Assign dst' src
  | _ => Assign "Bad LHS" 0
  end.
Infix "<-" := set (no associativity, at level 70) : cmd_scope.
Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'when' b 'then' then_ 'else' else_ 'done'" :=
  (If_ b then_ else_) (at level 75, b at level 0) : cmd_scope.
Notation "{{ I }} 'while' b 'loop' body 'done'" := (While_ I b body) (at level 75) : cmd_scope.
Notation "'assert' {{ I }}" := (Assert I) (at level 75) : cmd_scope.
Notation "x '<--' 'input'" := (Input x) (at level 75) : cmd_scope.
Notation "'output' e" := (Output e) (at level 75) : cmd_scope.
Delimit Scope cmd_scope with cmd.

Infix "+" := plus : reset_scope.
Infix "-" := Init.Nat.sub : reset_scope.
Infix "*" := mult : reset_scope.
Infix "=" := eq : reset_scope.
Infix "<" := lt : reset_scope.
Delimit Scope reset_scope with reset.
Open Scope reset_scope.


(** * Task 1: A big-step operational semantics for commands *)

(* Your first task is to define a big-step operational semantics for commands.
 * While it should be very similar to what we've seen in class, it should
 * also represent something about [io]s (or [trace]). Make sure the semantics
 * captures the effects of [Input]/[Output] on [trace]s. The most
 * recent event should appear at the *front* of the list in the trace.
 *
 * We provide the signature of the big-step semantics below. Replace the
 * [Axiom] below with your own definition of the semantics.
 * The first three arguments are the trace, heap, and valuation before execution,
 * and the final three arguments are the trace, heap, and valuation after execution.
 *)

(** * Define your semantics here! *)

Fixpoint interp (e : exp) (h: heap) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Read e1 =>
    match h $? (interp e1 h v) with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 h v + interp e2 h v
  | Minus e1 e2 => interp e1 h v - interp e2 h v
  | Mult e1 e2 => interp e1 h v * interp e2 h v
  end.

Definition interpb (be: bexp) (h: heap) (v : valuation) : bool :=
  match be with
  | Equal e1 e2 => if interp e1 h v ==n interp e2 h v then true else false
  | Less e1 e2 => if lt_dec (interp e1 h v) (interp e2 h v) then true else false
  end.

Inductive exec : trace -> heap -> valuation -> cmd ->
                 trace -> heap -> valuation -> Prop :=
  | ExecSkip : forall t h v, exec t h v Skip t h v
  | ExecAssign : forall t h v x e,
    exec t h v (Assign x e) t h (v $+ (x, interp e h v))
  | ExecWrite : forall t h v e1 e2,
    exec t h v (Write e1 e2) t (h $+ (interp e1 h v, interp e2 h v)) v
  | ExecSeq : forall t1 h1 v1 c1 t2 h2 v2 c2 t3 h3 v3,
    exec t1 h1 v1 c1 t2 h2 v2 ->
    exec t2 h2 v2 c2 t3 h3 v3 ->
    exec t1 h1 v1 (Seq c1 c2) t3 h3 v3
  | ExecIfTrue : forall t1 h1 v1 be then_ else_ t2 h2 v2,
    interpb be h1 v1 = true ->
    exec t1 h1 v1 then_ t2 h2 v2 ->
    exec t1 h1 v1 (If_ be then_ else_) t2 h2 v2
  | ExecIfFalse : forall t1 h1 v1 be then_ else_ t2 h2 v2,
    interpb be h1 v1 = false ->
    exec t1 h1 v1 else_ t2 h2 v2 ->
    exec t1 h1 v1 (If_ be then_ else_) t2 h2 v2
  | ExecWhileTrue : forall t1 h1 v1 (inv: assertion) be body t2 h2 v2 t3 h3 v3,
    inv t1 h1 v1 ->
    interpb be h1 v1 = true ->
    exec t1 h1 v1 body t2 h2 v2 ->
    exec t2 h2 v2 (While_ inv be body) t3 h3 v3 ->
    exec t1 h1 v1 (While_ inv be body) t3 h3 v3
  | ExecWhileFalse : forall t h v (inv: assertion) be body,
    inv t h v ->
    interpb be h v = false ->
    exec t h v (While_ inv be body) t h v
  | ExecAssert : forall t h v (a: iassertion),
    a h v ->
    exec t h v (Assert a) t h v
  | ExecInput : forall t h v x n,
    exec t h v (Input x) ((In n)::t) h (v $+ (x, n))
  | ExecOutput : forall t h v e,
    exec t h v (Output e) ((Out (interp e h v))::t) h v.

(** * Task 2 : Hoare logic *)

(* We also ask you to define a Hoare logic for our language. The logic should
 * derive triples of the form {{ P }} c {{ Q }}, where "P" and "Q" have type
 * [assertion] and "c" has type [cmd]. It should be also very similar to the
 * Hoare logic we've defined in class.
 *)

(* The logic should be consistent with the semantics you defined, so we
 * also ask you to prove a soundness relation between your Hoare logic and your
 * semantics.  You will need this consistency to prove the correctness of
 * example programs we will provide soon. 
 *)

(** Task 2-1: Define your Hoare logic here! *)

Notation "[[ tr , h , v ]] ~> e" := (fun tr h v => e%reset) (at level 90).

Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
  | HoareSkip : forall P, hoare_triple P Skip P
  | HoareAssign : forall P x e,
    hoare_triple P (Assign x e) ([[t, h, v]] ~>
        exists v', P t h v' /\ v = v' $+ (x, interp e h v'))
  | HoareWrite : forall P e1 e2,
    hoare_triple P (Write e1 e2) ([[t, h, v]] ~>
        exists h', P t h' v /\ h = h' $+ (interp e1 h' v, interp e2 h' v))
  | HoareSeq : forall P e1 Q e2 R,
    hoare_triple P e1 Q -> hoare_triple Q e2 R ->
    hoare_triple P (Seq e1 e2) R
  | HoareIf : forall P eb then_ Q1 else_ Q2,
    hoare_triple ([[t, h, v]] ~> P t h v /\ interpb eb h v = true) then_ Q1 ->
    hoare_triple ([[t, h, v]] ~> P t h v /\ interpb eb h v = false) else_ Q2 ->
    hoare_triple P (If_ eb then_ else_) ([[t, h, v]] ~> Q1 t h v \/ Q2 t h v)
  | HoareWhile : forall (P I: assertion) be body,
    (forall t h v, P t h v -> I t h v) ->
    hoare_triple ([[t, h, v]] ~> I t h v /\ interpb be h v = true) body I ->
    hoare_triple P (While_ I be body) ([[t, h, v]] ~>
        I t h v /\ interpb be h v = false)
  | HoareAssert : forall (P: assertion) (I: iassertion),
    (forall t h v, P t h v -> I h v) ->
    hoare_triple P (Assert I) P
  | HoareInput : forall P x,
    hoare_triple P (Input x) ([[t, h, v]] ~>
        exists t' v' n, P t' h v' /\ v = v' $+ (x, n) /\ t = (In n)::t')
  | HoareOutput : forall P e,
    hoare_triple P (Output e) ([[t, h, v]] ~>
        exists t', P t' h v /\ t = (Out (interp e h v))::t')
  | HoareConseq : forall c (P P' Q Q': assertion),
    hoare_triple P c Q ->
    (forall t h v, P' t h v -> P t h v) ->
    (forall t h v, Q t h v -> Q' t h v) ->
    hoare_triple P' c Q'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c%cmd Q) (at level 90, c at next level).

(** Task 2-2: Prove the consistency theorem. *)

Lemma hoare_while : forall t1 h1 v1 inv be body t2 h2 v2,
    exec t1 h1 v1 (While_ inv be body) t2 h2 v2 ->
    inv t2 h2 v2 /\ interpb be h2 v2 = false.
Proof.
  simplify.
  induct H.
    exact IHexec2.
    exact (conj H H0).
Qed.

Theorem hoare_triple_big_step :
  forall pre c post,
    hoare_triple pre c post ->
    forall tr h v tr' h' v',
      exec tr h v c tr' h' v' ->
      pre tr h v -> post tr' h' v'.
Proof.
  intros pre c post H; elim H.
  (* HoareSkip *)
    simplify.
    invert H0; exact H1.
  (* HoareAssign *)
    simplify.
    exists v; invert H0.
    exact (conj H1 (eq_refl _)).
  (* HoareWrite *)
    simplify.
    exists h; invert H0.
    exact (conj H1 (eq_refl _)).
  (* HoareSeq *)
    simplify.
    invert H4.
    exact (H3 _ _ _ _ _ _ H15 (H1 _ _ _ _ _ _ H11 H5)).
  (* HoareIf *)
    simplify.
    invert H4.
      exact (or_introl (H1 _ _ _ _ _ _ H16 (conj H5 H15))).
      exact (or_intror (H3 _ _ _ _ _ _ H16 (conj H5 H15))).
  (* HoareWhile *)
    simplify.
    exact (hoare_while H3).
  (* HoareAssert *)
    simplify.
    invert H1; exact H2.
  (* HoareInput *)
    simplify.
    exists tr, v; invert H0.
    exists n; exact (conj H1 (conj (eq_refl _) (eq_refl _))).
  (* HoareOutput *)
    simplify.
    exists tr; invert H0.
    exact (conj H1 (eq_refl _)).
  (* HoareConseq *)
    simplify.
    exact (H3 _ _ _ (H1 _ _ _ _ _ _ H4 (H2 _ _ _ H5))).
Qed.


(** * Task 3: Verification of some example programs *)

(* Now it's time to verify programs using the Hoare logic you've just defined!
 * We provide three example programs and three corresponding correctness 
 * theorems. You are required to prove the theorems stated below using Hoare
 * logic.
 *)

(** Task 3-1: adding two inputs -- prove [add_two_inputs_ok] *)

Example add_two_inputs :=
  ("x" <-- input;;
   "y" <-- input;;
   output ("x" + "y"))%cmd.

Lemma add_two_inputs_ok_hoare_triple :
  {{ [[t,h,v]] ~> t = nil }}
  add_two_inputs
  {{ [[t,h,v]] ~> exists vx vy, t = [Out (vx + vy); In vy; In vx] }}.
Proof.
  refine (HoareConseq _ _
      (HoareSeq (HoareInput _ "x")
      (HoareSeq (HoareInput _ "y")
                (HoareOutput _ ("x" + "y")%cmd)))
      (fun _ _ _ H => H) _).
  intros t h v [t' [ [t'0 [v' [n [ [t'1 [v'0 [n0 eq3] ] ] eq2 ] ] ] ] eq1 ] ].
  invert eq3; invert eq2; invert H0.
  exists n0, n; simpl.
  assert ("x" <> "y") as xyne; try discriminate.
  rewrite (lookup_add_ne _ _ xyne).
  repeat rewrite (lookup_add_eq _ _ (eq_refl _)).
  reflexivity.
Qed.

Theorem add_two_inputs_ok:
  forall tr h v tr' h' v',
    exec tr h v add_two_inputs tr' h' v' ->
    tr = nil ->
    exists vx vy, tr' = [Out (vx + vy); In vy; In vx].
Proof.
  exact (hoare_triple_big_step add_two_inputs_ok_hoare_triple).
Qed.

(** Task 3-2: finding the maximum of three numbers -- prove [max3_ok] *)

Example max3 :=
  ("x" <-- input;;
   "y" <-- input;;
   "z" <-- input;;
   when "x" < "y" then
     when "y" < "z" then
       output "z"
     else 
       output "y"
     done
   else
     when "x" < "z" then
       output "z"
     else
       output "x"
     done
   done)%cmd.

Inductive max3_spec : trace -> Prop :=
| M3s: forall x y z mx,
    mx >= x ->
    mx >= y ->
    mx >= z ->
    (mx = x \/ mx = y \/ mx = z) ->
    max3_spec [Out mx; In z; In y; In x].

Lemma not_lt_gt : forall n m, ~ n < m -> n >= m.
Proof.
  intros n m nlt; cases (n ?= m).
    pinvert (proj1 (Nat.compare_eq_iff _ _) Heq); exact (le_n _).
    pinvert (nlt (proj1 (Nat.compare_lt_iff _ _) Heq)).
    exact (le_Sn_le _ _ (proj1 (Nat.compare_gt_iff _ _) Heq)).
Qed.

Lemma max3_hoare_triple :
  {{ [[t,h,v]] ~> t = nil }}
  max3
  {{ [[t,h,v]] ~> max3_spec t }}.
Proof.
  assert ("y" <> "z") as yzne; try discriminate.
  assert ("x" <> "z") as xzne; try discriminate.
  assert ("x" <> "y") as xyne; try discriminate.
  refine (HoareConseq _ _
      (HoareSeq (HoareInput _ "x")
      (HoareSeq (HoareInput _ "y")
      (HoareSeq (HoareInput _ "z")
        (HoareIf _ _
          (HoareIf _ _ (HoareOutput _ _) (HoareOutput _ _))
          (HoareIf _ _ (HoareOutput _ _) (HoareOutput _ _))))))
      (fun _ _ _ H => H) _).
  intros t h v H; cases H; cases H; elimc H;
      intros t'2 [ [ [ [t' [v' [n [ [t'0 [v'0 [n0 [ [t'1 [v'1 [n1 [eq10
          [eq9 eq8] ] ] ] ] [eq7 eq6] ] ] ] ] [eq5 eq4] ] ] ] ] eq3] eq2] eq1];
      invert eq10; simpl; simpl in eq2, eq3;
      try rewrite (lookup_add_ne _ _ xzne) in eq2;
      rewrite (lookup_add_ne _ _ xzne) in eq3;
      try rewrite (lookup_add_ne _ _ yzne) in eq2;
      rewrite (lookup_add_ne _ _ yzne) in eq3;
      try rewrite (lookup_add_ne _ _ xyne) in eq2;
      rewrite (lookup_add_ne _ _ xyne) in eq3;
      repeat rewrite (lookup_add_eq _ _ (eq_refl _)) in eq2;
      repeat rewrite (lookup_add_eq _ _ (eq_refl _)) in eq3;
      [ cases (lt_dec n0 n); try discriminate eq2 |
        cases (lt_dec n0 n); try discriminate eq2 |
        cases (lt_dec n1 n); try discriminate eq2 |
        cases (lt_dec n1 n); try discriminate eq2 ];
      cases (lt_dec n1 n0); try discriminate eq3;
      try rewrite (lookup_add_ne _ _ yzne);
      try rewrite (lookup_add_ne _ _ xzne);
      try rewrite (lookup_add_ne _ _ xyne);
      rewrite (lookup_add_eq _ _ (eq_refl _)).
  (* true true *)
    pose (n1n := lt_trans _ _ _ l0 l).
    exact (M3s (le_Sn_le _ _ n1n) (le_Sn_le _ _ l) (le_refl _)
        (or_intror (or_intror (eq_refl _)))).
  (* false true *)
    exact (M3s (le_Sn_le _ _ l) (le_refl _) (not_lt_gt n2)
        (or_intror (or_introl (eq_refl _)))).
  (* true false *)
    pose (n0n := le_trans _ _ _ (not_lt_gt n2) (le_Sn_le _ _ l)).
    exact (M3s (le_Sn_le _ _ l) n0n (le_refl _)
        (or_intror (or_intror (eq_refl _)))).
  (* false false *)
    exact (M3s (le_refl _) (not_lt_gt n3) (not_lt_gt n2)
        (or_introl (eq_refl _))).
Qed.

Theorem max3_ok:
  forall tr h v tr' h' v',
    exec tr h v max3 tr' h' v' ->
    tr = nil ->
    max3_spec tr'.
Proof.
  exact (hoare_triple_big_step max3_hoare_triple).
Qed.

(** Task 3-3: Fibonacci sequence -- prove [fibonacci_ok] *)

Inductive fibonacci_spec : trace -> Prop :=
| Fs0: fibonacci_spec nil
| Fs1: fibonacci_spec [Out 1]
| Fs2: fibonacci_spec [Out 1; Out 1]
| Fsn:
    forall x y tr,
      fibonacci_spec (Out y :: Out x :: tr) ->
      fibonacci_spec (Out (x + y) :: Out y :: Out x :: tr).

Definition loop_cmd : cmd := 
  ("tmp" <- "y";;
   "y" <- "x" + "y";;
   "x" <- "tmp";;
   "cnt" <- "cnt" + 1;;
   output "y")%cmd.

Definition loop_inv : assertion := fun t _ v =>
    fibonacci_spec t
    /\ (
      (t = [Out 1] /\ (v $? "x" = Some 0) /\ (v $? "y" = Some 1))
      \/
      exists x y tr,
        t = (Out y)::(Out x)::tr
        /\
        v $? "x" = Some x
        /\
        v $? "y" = Some y
    ).

Example fibonacci (n: nat) :=
  ("cnt" <- 0;;
   "x" <- 0;;
   "y" <- 1;;
   output "y";;
   {{ loop_inv }}
   while "cnt" < n loop loop_cmd done)%cmd.

Lemma loop_inv_hoare_triple : hoare_triple loop_inv loop_cmd loop_inv.
Proof.
  assert ("y" <> "cnt") as ycne; try discriminate.
  assert ("x" <> "cnt") as xcne; try discriminate.
  assert ("y" <> "x") as yxne; try discriminate.
  assert ("tmp" <> "y") as tyne; try discriminate.
  assert ("y" <> "tmp") as ytne; try discriminate.
  assert ("x" <> "tmp") as xtne; try discriminate.
  refine (HoareConseq _ _
      (HoareSeq (HoareAssign _ _ _)
      (HoareSeq (HoareAssign _ _ _)
      (HoareSeq (HoareAssign _ _ _)
      (HoareSeq (HoareAssign _ _ _)
                (HoareOutput _ _)))))
      (fun _ _ _ H => H) _).
  intros t h v
      [t' [ [v' [ [v'0 [ [v'1 [ [v'2 [H eq5] ] eq4] ] eq3] ] eq2] ] eq1] ].
  invert eq1.
  invert H.
  unfold interp.
  repeat rewrite (lookup_add_ne _ _ ycne).
  repeat rewrite (lookup_add_ne _ _ yxne).
  repeat rewrite (lookup_add_ne _ _ xtne).
  repeat rewrite (lookup_add_ne _ _ ytne).
  repeat rewrite (lookup_add_ne _ _ tyne).
  repeat rewrite (lookup_add_eq _ _ (eq_refl _)).
  cases H1.
  (* First iteration *)
    invert H; invert H2.
    repeat rewrite H.
    repeat rewrite H1.
    split.
    (* fibonacci_spec *)
      exact Fs2.
    (* valuation *)
      right; exists 1, 1, nil.
      refine (conj (eq_refl _) _).
      rewrite (lookup_add_ne _ _ xcne).
      rewrite (lookup_add_ne _ _ ycne).
      rewrite (lookup_add_ne _ _ yxne).
      repeat rewrite (lookup_add_eq _ _ (eq_refl _)).
      exact (conj (eq_refl _) (eq_refl _)).
  (* Next iterations *)
    elimc H; intros x [y [tr [teq [vxeq vyeq] ] ] ].
    repeat rewrite vxeq.
    repeat rewrite vyeq.
    invert teq.
    split.
    (* fibonacci_spec *)
      exact (Fsn H0).
    (* valuation *)
      right; exists y, (x + y), ((Out x)::tr).
      refine (conj (eq_refl _) _).
      rewrite (lookup_add_ne _ _ xcne).
      rewrite (lookup_add_ne _ _ ycne).
      rewrite (lookup_add_ne _ _ yxne).
      repeat rewrite (lookup_add_eq _ _ (eq_refl _)).
      exact (conj (eq_refl _) (eq_refl _)).
Qed.

Lemma fibonacci_hoare_triple (n: nat) :
  {{ [[t,h,v]] ~> t = nil }}
  (fibonacci n)
  {{ [[t,h,v]] ~> fibonacci_spec t }}.
Proof.
  assert ("x" <> "y") as xyne; try discriminate.
  refine (HoareConseq _ _
      (HoareSeq (HoareAssign _ _ _)
      (HoareSeq (HoareAssign _ _ _)
      (HoareSeq (HoareAssign _ _ _)
      (HoareSeq (HoareOutput _ _) _))))
      (fun _ _ _ H => H) _).
  refine (HoareWhile _ ("cnt" < n)%cmd _
      (HoareConseq _ _ loop_inv_hoare_triple _ (fun _ _ _ H => H))).
  (* Setup *)
    intros t h v [t' [ [v' [ [v'0 [ [v'1 [eq5 eq4] ] eq3] ] eq2] ] eq1] ].
    invert eq1.
    unfold interp; rewrite (lookup_add_eq _ _ (eq_refl _)).
    refine (conj Fs1 (or_introl (conj (eq_refl _) _))).
    rewrite (lookup_add_ne _ _ xyne).
    repeat rewrite (lookup_add_eq _ _ (eq_refl _)).
    exact (conj (eq_refl _) (eq_refl _)).
  (* weakening for invariant *)
    exact (fun _ _ _ H => proj1 H).
  (* weakening for conclusion *)
    exact (fun _ _ _ H => proj1 (proj1 H)).
Qed.

Theorem fibonacci_ok (n: nat):
  forall tr h v tr' h' v',
    exec tr h v (fibonacci n) tr' h' v' ->
    tr = nil ->
    fibonacci_spec tr'.
Proof.
  exact (hoare_triple_big_step (fibonacci_hoare_triple n)).
Qed.


(** * Task 4: Implement your own program to verify. *)

(* The last task is to implement your own program and to verify its correctness
 * using Hoare logic. Note that the three examples we provided above had nothing
 * to do with [heap]s. Design a program that uses the heap in a nontrivial
 * manner and prove its correctness.
 *)

(** Define your own program and prove its correctness here! *)

(* Same thing again and again, skipping that last free exercise *)
