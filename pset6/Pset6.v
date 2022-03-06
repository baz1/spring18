(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 6 *)

Require Import Frap.

(* Authors: 
 * Ben Sherman (sherman@csail.mit.edu),
 * Joonwon Choi (joonwonc@csail.mit.edu), 
 * Adam Chlipala (adamc@csail.mit.edu)
 *)

(* In this problem set, we will work with the following simple imperative language with
 * a nondeterministic choice operator. Your task is to define both big-step as well as
 * a particular kind of small-step operational semantics for this language
 * (one that is in fact deterministic), and to prove a theorem connecting the two:
 * if the small-step semantics aborts, then the big-step semantics may abort.
 *
 * This is the first problem set so far in this class that is truly open-ended.
 * We want to give you the flexibility to define the operational semantics as
 * you wish, and if you'd like you may even differ from the template shown here
 * if you find it more convenient.
 * Additionally, this is the first problem set where it is *NOT* sufficient to
 * just get the file compiling without any use of [admit] or [Admitted].
 * This will not necessarily guarantee that you have given reasonable semantics
 * for the programming language, and accordingly, will not necessarily
 * guarantee that you will earn full credit. For instance, if you define
 * your small-step semantics as the empty relation (which is incorrect), 
 * the theorem you must prove to connect your big-step and small-step 
 * semantics will be trivial.
 *)

(** * Syntax *)

(* Basic arithmetic expressions, as we've seen several times in class. *)
Inductive arith : Set :=
| Const : nat -> arith
| Var : var -> arith
| Plus : arith -> arith -> arith
| Eq : arith -> arith -> arith
(* should return 1 if the two expressions are equal, and 0 otherwise. *)
| Lt : arith -> arith -> arith
(* should return 1 if the two expressions are equal, and 0 otherwise. *)
.

(* The simple imperative language with a [Choose] syntax for 
 * nondeterminism. The intended meaning of the program 
 * [Choose c c'] is that either [c] should run or [c'] should run.
 *)
Inductive cmd :=
| Assign : var -> arith -> cmd
| Skip : cmd
| Seq : cmd -> cmd -> cmd
| Choose : cmd -> cmd -> cmd (* Here's the main novelty: nondeterministic choice *)
| If : arith -> cmd (* then *) -> cmd (* else *) -> cmd
| While : arith -> cmd -> cmd
| Abort : cmd (* This command should immediately terminate the program *)
.


(** Notations *)

Declare Scope cmd_scope.
Delimit Scope cmd_scope with cmd.

Declare Scope arith_scope.

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "==" := Eq (at level 75) : arith_scope.
Infix "<" := Lt : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75) : cmd_scope.
Infix "<|>" := Choose (at level 78) : cmd_scope.
Infix ";;" := Seq (at level 80) : cmd_scope.

Notation "'if_' c 'then' t 'else' f" := (If c%arith t f) (at level 75) : cmd_scope.
Notation "'while' c 'do' p" := (While c%arith p) (at level 75) : cmd_scope.


(** * Examples *)

(* All nondeterministic realizations of [test_prog1] terminate
 * (either normally or by aborting). [test_prog1 5] may abort,
 * but [test_prog1 6] always terminates normally.
 *)
Definition test_prog1 (k : nat) : cmd := (
  "target" <- 8 ;;
  ("x" <- 3 <|> "x" <- 4) ;;
  ("y" <- 1 <|> "y" <- k) ;;
  if_ "x" + "y" == "target"
     then Abort
     else Skip
  )%cmd.

(* No matter the value of [num_iters], [test_prog2 num_iters]
 * always may potentially fail to terminate, and always
 * may potentially abort.
 *)
Definition test_prog2 (num_iters : nat) : cmd := (
   "acc" <- 0 ;;
   "n" <- 0;;
   while ("n" < 1) do (
     (Skip <|> "n" <- 1) ;;
     "acc" <- "acc" + 1
   ) ;;
   if_ "acc" == S num_iters
     then Abort
     else Skip
  )%cmd.


(* We've seen the expression language in class a few times,
 * so here we'll just give you the interpreter for that
 * expression language.
 *)
Definition valuation := fmap var nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Eq e1 e2 => if interp e1 v ==n interp e2 v then 1 else 0
  | Lt e1 e2 => if lt_dec (interp e1 v) (interp e2 v) then 1 else 0
  end.

(** ** Part 1: Big-step operational semantics *)

(* You should define some result type (say, [result]) for values that commands
   in the language run to, and define a big-step operational semantics
   [eval : valuation -> cmd -> result -> Prop]
   that says when a program *may* run to some result in *some* nondeterministic
   realization of the program. Then you should also define a predicate
   [big_aborted : result -> Prop]
   that describes which results indicate that the program aborted.

 * Looking at the examples, we should have
   [exists res, eval $0 (test_prog1 5) res /\ big_aborted res]
   but
   [forall res, eval $0 (test_prog1 6) res -> big_aborted res -> False] 
 * . You are not required to prove these facts, but it could be a good
     sanity check!
 *)

Inductive result : Type :=
  | Terminated (v: valuation)
  | Aborted.

Inductive eval : valuation -> cmd -> result -> Prop :=
  | EvalAssign : forall v x a,
      eval v (Assign x a) (Terminated (v $+ (x, interp a v)))
  | EvalSkip : forall v,
      eval v Skip (Terminated v)
  | EvalSeqAborted : forall v0 cmd0 cmd1,
      eval v0 cmd0 Aborted -> eval v0 (Seq cmd0 cmd1) Aborted
  | EvalSeqSuccess : forall v0 cmd0 v1 cmd1 res,
      eval v0 cmd0 (Terminated v1) -> eval v1 cmd1 res -> eval v0 (Seq cmd0 cmd1) res
  | EvalChoose0 : forall v cmd0 cmd1 res,
      eval v cmd0 res -> eval v (Choose cmd0 cmd1) res
  | EvalChoose1 : forall v cmd0 cmd1 res,
      eval v cmd1 res -> eval v (Choose cmd0 cmd1) res
  | EvalIfFalse : forall v a cmd1 cmd0 res,
      interp a v = O -> eval v cmd0 res -> eval v (If a cmd1 cmd0) res
  | EvalIfTrue : forall v a cmd1 cmd0 res,
      interp a v <> O -> eval v cmd1 res -> eval v (If a cmd1 cmd0) res
  | EvalWhileFalse : forall v a cmd,
      interp a v = O -> eval v (While a cmd) (Terminated v)
  | EvalWhileTrueAborted : forall v a cmd,
      interp a v <> O -> eval v cmd Aborted -> eval v (While a cmd) Aborted
  | EvalWhileTrueSuccess : forall v0 a cmd v1 res,
      interp a v0 <> O -> eval v0 cmd (Terminated v1) -> eval v1 (While a cmd) res -> eval v0 (While a cmd) res
  | EvalAbort : forall v,
      eval v Abort Aborted.

Definition big_aborted : result -> Prop := fun r => r = Aborted.

(* As an optional sanity check, you may attempt to
 * prove that your big-step semantics behaves appropriately
 * for an example program: *)
 
Lemma extract_y : forall (a b c: nat), ($0 $+ ("target", a) $+ ("x", b) $+ ("y", c)) $? "y" = Some c.
Proof.
  intros a b c.
  exact (lookup_add_eq ($0 $+ ("target", a) $+ ("x", b)) c (eq_refl "y")).
Qed.

Lemma extract_x : forall (a b c: nat), ($0 $+ ("target", a) $+ ("x", b) $+ ("y", c)) $? "x" = Some b.
Proof.
  assert ("x" <> "y") as x_not_y.
    intros abs.
    discriminate abs.
  intros a b c.
  rewrite (lookup_add_ne ($0 $+ ("target", a) $+ ("x", b)) c x_not_y).
  exact (lookup_add_eq ($0 $+ ("target", a)) b (eq_refl "x")).
Qed.

Lemma extract_target : forall (a b c: nat), ($0 $+ ("target", a) $+ ("x", b) $+ ("y", c)) $? "target" = Some a.
Proof.
  assert ("target" <> "y") as target_not_y.
    intros abs.
    discriminate abs.
  assert ("target" <> "x") as target_not_x.
    intros abs.
    discriminate abs.
  intros a b c.
  rewrite (lookup_add_ne ($0 $+ ("target", a) $+ ("x", b)) c target_not_y).
  rewrite (lookup_add_ne ($0 $+ ("target", a)) b target_not_x).
  exact (lookup_add_eq ($0) a (eq_refl "target")).
Qed.

Example test_prog1_reachable :
  exists res, eval $0 (test_prog1 5) res /\ big_aborted res.
Proof.
  refine (ex_intro _ Aborted (conj _ (eq_refl Aborted))).
  refine (EvalSeqSuccess $0 _ _ _ Aborted _ _).
  refine (EvalSeqSuccess _ _ _ _ _ _ _).
  refine (EvalSeqSuccess _ _ _ _ _ _ _).
  refine (EvalAssign _ _ _).
  refine (EvalChoose0 _ _ _ _ (EvalAssign _ _ _)).
  refine (EvalChoose1 _ _ _ _ (EvalAssign _ _ _)).
  refine (EvalIfTrue _ _ _ _ _ _ _).
  simpl.
  rewrite (extract_x 8 3 5).
  rewrite (extract_y 8 3 5).
  rewrite (extract_target 8 3 5).
  discriminate.
  exact (EvalAbort _).
Qed.

Example test_prog1_unreachable :
  forall res, eval $0 (test_prog1 6) res -> big_aborted res -> False.
Proof.
  intros res evaluation res_value.
  invert res_value.
  invert evaluation.
  (* Show that we cannot abort before the If *)
    invert H1.
    invert H2.
    invert H1.
    invert H5.
    invert H4.
    invert H4.
    invert H5.
    invert H4.
    invert H4.
  (* Show that the If will not abort *)
    invert H2.
    invert H3.
    invert H6.
    invert H7.
    (* left left *)
      invert H5.
      invert H6.
      invert H2.
      invert H4.
      invert H6.
      simpl in H5.
      rewrite (extract_x 8 3 1) in H5.
      rewrite (extract_y 8 3 1) in H5.
      rewrite (extract_target 8 3 1) in H5.
      exact (H5 (eq_refl O)).
    (* right left *)
      invert H5.
      invert H6.
      invert H2.
      invert H4.
      invert H6.
      simpl in H5.
      rewrite (extract_x 8 4 1) in H5.
      rewrite (extract_y 8 4 1) in H5.
      rewrite (extract_target 8 4 1) in H5.
      exact (H5 (eq_refl O)).
    invert H7.
    (* left right *)
      invert H5.
      invert H6.
      invert H2.
      invert H4.
      invert H6.
      simpl in H5.
      rewrite (extract_x 8 3 6) in H5.
      rewrite (extract_y 8 3 6) in H5.
      rewrite (extract_target 8 3 6) in H5.
      exact (H5 (eq_refl O)).
    (* right right *)
      invert H5.
      invert H6.
      invert H2.
      invert H4.
      invert H6.
      simpl in H5.
      rewrite (extract_x 8 4 6) in H5.
      rewrite (extract_y 8 4 6) in H5.
      rewrite (extract_target 8 4 6) in H5.
      exact (H5 (eq_refl O)).
Qed.



  (** ** Part 2: Small-step deterministic operational semantics *)

(* Next, you should define a small-step operational semantics for this
   language that in some sense tries to run *all* possible nondeterministic
   realizations and aborts if any possible realization aborts.
   Define a type [state] that represents the underlying state that the
   small-step semantics should take steps on, and then define a small-step
   semantics
   [step : state -> state -> Prop]
   .

   Here's the twist: we ask that you define an operational semantics that 
   is *deterministic*, in the sense of the following formal statement:
   [forall s1 s2 s2', step s1 s2 -> step s1 s2' -> s2 = s2'].

   The operational model that we have in mind in this: when we encounter
   a nondeterministic choice, we execute the left branch. If the left
   branch terminates without aborting, we backtrack and try the
   other nondeterministic choice.

   Note that if any possible realization does not terminate,
   we allow the deterministic small-step semantics to diverge as well.
   (It is actually possible to define a semantics that always "finds" aborts,
   even if some branches of nondeterminism diverge!  However, the proof of that
   variant would likely be significantly more complicated, and we haven't tried
   it ourselves.)

   Define a function
   [init : valuation -> cmd -> state]
   that builds starting states for the small-step semantics,
   a predicate
   [small_aborted : state -> Prop]
   that describes which states are considered aborted, and
   a predicate
   [small_terminated : state -> Prop]
   that describes states that have run to completion without any
   nondeterministic branch aborting.

 * Looking at the examples, we should have
   [exists st, step^* (init $0 (test_prog1 5)) st /\ small_aborted st]
   but
   [forall st, step^* (init $0 (test_prog1 6)) st -> small_aborted st -> False]
   . You are not required to prove these facts, but it could be
   a good sanity check!
 *)

(* From the instructions:
   forall s1 s2 s2', step s1 s2 -> step s1 s2' -> s2 = s2'
   If we want states to contain some current valuation(s),
   we need another axiom about valuations.
   That axiom could be derived from fmap_ext if we incorporate the fact that
   valuations would always operate over the same finite set of strings.
   We'll just add a new axiom here though, to be able to actually write s2 = s2' *)
Axiom valuation_dec : forall x y : valuation, sumbool (x = y) (x <> y).

(*

   > (It is actually possible to define a semantics that always "finds" aborts,
   > even if some branches of nondeterminism diverge!  However, the proof of that
   > variant would likely be significantly more complicated, and we haven't tried
   > it ourselves.)
   Let's do it!
*)

Inductive singular_state :=
  | SRunning (v: valuation) (l: list cmd)
  | SDone (r: result).

Definition state := list singular_state.

Definition singular_step (s: singular_state) : list singular_state := match s with
  | SRunning v nil => [SDone (Terminated v)]
  | SRunning v ((Assign x a)::q) => [SRunning (v $+ (x, interp a v)) q]
  | SRunning v (Skip::q) => [SRunning v q]
  | SRunning v ((Seq c1 c2)::q) => [SRunning v (c1::c2::q)]
  | SRunning v ((Choose c1 c2)::q) => [SRunning v (c1::q); SRunning v (c2::q)]
  | SRunning v ((If a c1 c0)::q) => match interp a v with
    | O => [SRunning v (c0::q)]
    | _ => [SRunning v (c1::q)]
    end
  | SRunning v ((While a c)::q) => match interp a v with
    | O => [SRunning v q]
    | _ => [SRunning v (c::(While a c)::q)]
    end
  | SRunning v (Abort::q) => [SDone Aborted]
  | SDone (Terminated v) => [SDone (Terminated v)]
  | SDone Aborted => [SDone Aborted]
  end.

Definition full_step (s: state) : state := flat_map singular_step s.

Definition step : state -> state -> Prop :=
  fun x y => y = full_step x.

Definition init : valuation -> cmd -> state :=
    fun (v: valuation) (c: cmd) => [SRunning v [c]].

Lemma arith_dec : forall x y : arith, sumbool (x = y) (x <> y).
Proof.
  decide equality.
  exact (Nat.eq_dec n n0).
  exact (string_dec s s0).
Qed.

Lemma cmd_dec : forall x y : cmd, sumbool (x = y) (x <> y).
Proof.
  decide equality.
  exact (arith_dec a a0).
  exact (string_dec s s0).
  exact (arith_dec a a0).
  exact (arith_dec a a0).
Qed.

Lemma result_dec : forall x y : result, sumbool (x = y) (x <> y).
Proof.
  intros x y; destruct x, y; decide equality; exact (valuation_dec _ _).
Qed.

Lemma state_dec : forall x y : singular_state, sumbool (x = y) (x <> y).
Proof.
  decide equality.
  exact (list_eq_dec cmd_dec _ _).
  exact (valuation_dec _ _).
  exact (result_dec _ _).
Qed.

(*
Inductive small_aborted : state -> Prop :=
  | FirstAborted : forall q, small_aborted (SAborted::q)
  | TailAborted : forall x q, small_aborted q -> small_aborted (x::q).
Theorem small_aborted_in : forall s : state, small_aborted s <-> In SAborted s.
Proof. (* should probably have defined it with In in the first place... *)
  
Qed.
*)
Definition small_aborted (s:state) : Prop := In (SDone Aborted) s.
Fixpoint small_aborted_bool (s:state) : bool := match s with
  | nil => false
  | (SRunning _ _)::q => small_aborted_bool q
  | (SDone (Terminated _))::q => small_aborted_bool q
  | (SDone Aborted)::_ => true
  end.
Theorem small_aborted_equiv : forall st : state, small_aborted st <-> small_aborted_bool st = true.
Proof.
  intro st.
  elim st.
  (* [] *)
    split.
      intro absurd; elim absurd.
      discriminate.
  (* a::q *)
    intros a q rec.
    split.
    (* small_aborted (a :: q) -> small_aborted_bool (a :: q) = true *)
      intro H; elim H.
        intro a_aborted; rewrite a_aborted; trivial.
        elim a.
          intros v l; unfold small_aborted_bool; exact (proj1 rec).
          intro r; elim r.
            exact (fun _ => (proj1 rec)).
            reflexivity.
    (* small_aborted_bool (a :: q) = true -> small_aborted (a :: q) *)
      elim a.
        intros v l H; exact (or_intror (proj2 rec H)).
        intro r; elim r.
          exact (fun _ H => or_intror (proj2 rec H)).
          exact (fun _ => or_introl (eq_refl (SDone Aborted))).
Qed.

Fixpoint small_terminated_bool (s:state) : bool := match s with
  | nil => true
  | (SRunning _ _)::q => false
  | (SDone (Terminated _))::q => small_terminated_bool q
  | (SDone Aborted)::_ => false
  end.
Definition small_terminated (s:state) : Prop := small_terminated_bool s = true.
Theorem small_terminated_only_terminated : forall (s:state) (res:singular_state),
    small_terminated s -> In res s -> exists v:valuation, res = SDone (Terminated v).
Proof.
  intro s; elim s; clear s.
  (* [] *)
    intros res taut absurd; elim absurd.
  intro a; elim a; clear a.
  (* (SRunning v l)::q *)
    intros v l q rec res absurd; discriminate absurd.
  intro r; elim r; clear r.
  (* (SDone (Terminated v))::q *)
    intros v q rec res H1 H2; elim H2; clear H2.
      intro result; exists v; exact (eq_sym result).
      exact (rec _ H1).
  (* (SDone Aborted)::q *)
    intros l rec res absurd; discriminate absurd.
Qed.

Fixpoint iterate (A:Type) (F:A -> A) (n:nat){struct n} : A -> A := match n with
  | O => fun x => x
  | S m => fun x => iterate A F m (F x)
  end.
Definition do_steps (n:nat) : state -> state := iterate state full_step n.
Theorem do_steps_ex : forall n : nat, forall st : state, step^* st (do_steps n st).
Proof.
  intros n.
  elim n.
  (* Base case *)
    intros st.
    exact (TrcRefl step st).
  (* Recursion *)
    intros m H st.
    refine (TrcFront st (eq_refl (full_step st)) _).
    exact (H (full_step st)).
Qed.
Theorem do_steps_find : forall st1 st2 : state, step^* st1 st2 -> exists n:nat, st2 = do_steps n st1.
Proof.
  intros st1 st2 H.
  elim H.
  (* Base case *)
    intro x.
    exact (ex_intro _ O (eq_refl x)).
  (* Recursion *)
    intros x y z xy yz rec.
    invert rec.
    invert xy.
    exact (ex_intro _ (S x0) (eq_refl _)).
Qed.
Lemma do_steps_split0 : forall (n:nat) (st:state), full_step (do_steps n st) = do_steps n (full_step st).
Proof.
  intro n; elim n; clear n; [reflexivity|].
  intros n rec st.
  replace (do_steps (S n) st) with (do_steps n (full_step st)) by reflexivity.
  rewrite (rec _).
  reflexivity.
Qed.
Theorem do_steps_split : forall (n m:nat) (st:state), do_steps n (do_steps m st) = do_steps (n+m) st.
Proof.
  intro n; elim n; clear n; [reflexivity|].
  intros n rec m st.
  replace (do_steps (S n) (do_steps m st))
      with (do_steps n (full_step (do_steps m st))) by reflexivity.
  rewrite (do_steps_split0 _ _).
  rewrite (rec _ _).
  reflexivity.
Qed.

(* Two lemmas borrowed from newer versions of Coq;
   might have to comment out and remove implicit arguments further down. *)
Lemma flat_map_concat_map : forall A B, forall f:A->list B, forall l,
    flat_map f l = concat (map f l).
Proof.
  induction l as [|x l IH]; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.
Lemma flat_map_app : forall A B, forall f:A->list B, forall l1 l2,
    flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A B f l1 l2.
  now rewrite !flat_map_concat_map, map_app, concat_app.
Qed.
(* End of the borrowing :-) *)

Theorem step_split :
    forall (n:nat) (l1 l2: list singular_state),
    do_steps n (l1 ++ l2) = (do_steps n l1) ++ (do_steps n l2).
Proof.
  intro n; elim n.
  (* Base case *)
    reflexivity.
  (* Recursion *)
    clear n; intros n rec l1 l2.
    replace (do_steps (S n) (l1 ++ l2)) with (do_steps n (flat_map singular_step (l1 ++ l2))) by reflexivity.
    replace (do_steps (S n) l1) with (do_steps n (flat_map singular_step l1)) by reflexivity.
    replace (do_steps (S n) l2) with (do_steps n (flat_map singular_step l2)) by reflexivity.
    rewrite (flat_map_app _ _ singular_step l1 l2).
    exact (rec _ _).
Qed.

Theorem empty_future : forall st : state, step ^* nil st -> st = nil.
Proof.
  intros st H.
  induct H.
  (* Base case *)
    reflexivity.
  (* Recursion *)
    compute in H.
    rewrite H in IHtrc.
    exact (IHtrc (JMeq.JMeq_refl nil)).
Qed.
Lemma terminated_split : forall l1 l2 : list singular_state,
    small_terminated l1 /\ small_terminated l2 <-> small_terminated (l1 ++ l2).
Proof.
  intro l1; elim l1.
  (* Base case *)
    split.
      intros [useless H]; exact H.
      exact (fun H => conj (eq_refl true) H).
  (* Recursion *)
    intros a q rec l2; elim a.
    (* SRunning *)
      intros v c; split; [intros [absurd Hl2]|intro absurd]; discriminate absurd.
    intro r; elim r.
    (* SDone (Terminated v) *)
      intros v; exact (rec l2).
    (* SDone Abort *)
      split; [intros [absurd Hl2]|intro absurd]; discriminate absurd.
Qed.
Theorem terminated_future : forall st1 st2 : state,
    small_terminated st1 -> step ^* st1 st2 -> small_terminated st2.
Proof.
  assert (
      forall n:nat, forall st1:state,
      small_terminated st1 -> small_terminated (do_steps n st1)
  ) as recgoal.
    intro n; elim n.
    (* Base case *)
      exact (fun _ H => H).
    (* Recursion *)
      clear n; intros n rec st1; elim st1.
      (* [] *)
        rewrite (empty_future _ (do_steps_ex (S n) nil)); reflexivity.
      (* a::q *)
        intro a; elim a.
        (* SRunning *)
          intros v c q rec2 absurd; discriminate absurd.
        intro r; elim r.
        (* SDone (Terminated v) *)
          intros v q rec2 Hq.
          replace (SDone (Terminated v) :: q) with ([SDone (Terminated v)] ++ q) by reflexivity.
          rewrite (step_split _ _ _).
          refine (proj1 (terminated_split _ _) (conj (rec _ _) (rec2 Hq))); reflexivity.
        (* SDone Aborted *)
          intros q rec2 absurd; discriminate absurd.
  (* Back to the main goal *)
  intros st1 st2 base evol.
  elim (do_steps_find st1 st2 evol).
  intros n Hst2; rewrite Hst2; exact (recgoal n st1 base).
Qed.

Lemma terminated_not_aborted : forall s:state, small_terminated s -> ~ (small_aborted s).
Proof.
  intro s; elim s.
  (* [] *)
    intros useless absurd; elim absurd.
  (* a::q *)
    intro a; elim a.
    (* SRunning v c *)
      intros v c q rec absurd; discriminate absurd.
    intro r; elim r.
    (* SDone (Terminated v) *)
      intros v c rec H absurd.
      elim (in_inv absurd); [discriminate | exact (rec H)].
    (* SDone Aborted *)
      discriminate.
Qed.

(* As an optional sanity check, you may attempt to
 * prove that your small-step semantics behaves appropriately
 * for an example program: *)

Lemma test_lookup_y : forall t x y : nat, ($0 $+ ("target", t) $+ ("x", x) $+ ("y", y)) $? "y" = Some y.
Proof.
  intros t x y.
  exact (lookup_add_eq _ _ (eq_refl "y")).
Qed.
Lemma test_lookup_x : forall t x y : nat, ($0 $+ ("target", t) $+ ("x", x) $+ ("y", y)) $? "x" = Some x.
Proof.
  intros t x y.
  assert ("x" <> "y") as H.
    discriminate.
  rewrite (lookup_add_ne _ _ H).
  exact (lookup_add_eq _ _ (eq_refl "x")).
Qed.
Lemma test_lookup_target : forall t x y : nat, ($0 $+ ("target", t) $+ ("x", x) $+ ("y", y)) $? "target" = Some t.
Proof.
  intros t x y.
  assert ("target" <> "y") as Hy.
    discriminate.
  rewrite (lookup_add_ne _ _ Hy).
  assert ("target" <> "x") as Hx.
    discriminate.
  rewrite (lookup_add_ne _ _ Hx).
  exact (lookup_add_eq _ _ (eq_refl "target")).
Qed.

Example test_prog1_reachable_small :
  exists st, step^* (init $0 (test_prog1 5)) st /\ small_aborted st.
Proof.
  refine (ex_intro _ (do_steps 10 (init $0 (test_prog1 5))) _).
  split.
  (* left side *)
    exact (do_steps_ex 10 (init $0 (test_prog1 5))).
  (* right side *)
    compute.
    rewrite
      (test_lookup_x 8 3 1), (test_lookup_x 8 3 5), (test_lookup_x 8 4 1), (test_lookup_x 8 4 5),
      (test_lookup_y 8 3 1), (test_lookup_y 8 3 5), (test_lookup_y 8 4 1), (test_lookup_y 8 4 5),
      (test_lookup_target 8 3 1), (test_lookup_target 8 3 5),
      (test_lookup_target 8 4 1), (test_lookup_target 8 4 5).
    compute.
    exact (or_intror (or_introl (eq_refl (SDone Aborted)))).
Qed.

Example test_prog1_unreachable_small :
  forall st, step^* (init $0 (test_prog1 6)) st -> small_aborted st -> False.
Proof.
  intros st H absurd.
  pose (my_absurd := proj1 (small_aborted_equiv st) absurd).
  invert H.
  (* step 0 *)
    discriminate my_absurd.
  invert H0.
  invert H1.
  (* step 1 *)
    discriminate my_absurd.
  invert H.
  invert H0.
  (* step 2 *)
    discriminate my_absurd.
  invert H.
  invert H1.
  (* step 3 *)
    discriminate my_absurd.
  invert H.
  invert H0.
  (* step 4 *)
    discriminate my_absurd.
  invert H.
  invert H1.
  (* step 5 *)
    discriminate my_absurd.
  invert H.
  invert H0.
  (* step 6 *)
    discriminate my_absurd.
  invert H.
  invert H1.
  (* step 7 *)
    discriminate my_absurd.
  invert H.
  invert H0.
  (* step 8 *)
    discriminate my_absurd.
  invert H.
  replace
      (full_step (full_step (full_step (full_step
      (full_step (full_step (full_step (full_step
      (full_step (init $0 (test_prog1 6)))))))))))
    with
      [SRunning ($0 $+ ("target", 8) $+ ("x", 3) $+ ("y", 1)) [Skip];
       SRunning ($0 $+ ("target", 8) $+ ("x", 3) $+ ("y", 6)) [Skip];
       SRunning ($0 $+ ("target", 8) $+ ("x", 4) $+ ("y", 1)) [Skip];
       SRunning ($0 $+ ("target", 8) $+ ("x", 4) $+ ("y", 6)) [Skip]]
    in H1.
  (* Proving the final steps *)
    invert H1.
    (* Step 9 *)
      discriminate my_absurd.
    invert H.
    invert H0.
    (* Step 10 *)
      discriminate my_absurd.
    invert H.
    (* Remaining steps - nil state *)
    refine (
        (terminated_not_aborted _ (terminated_future _ _ _ H1))
        (proj2 (small_aborted_equiv _) my_absurd)); reflexivity.
  (* Proving the rewrite *)
    compute.
    rewrite
        (test_lookup_x 8 3 1), (test_lookup_x 8 3 6), (test_lookup_x 8 4 1), (test_lookup_x 8 4 6),
        (test_lookup_y 8 3 1), (test_lookup_y 8 3 6), (test_lookup_y 8 4 1), (test_lookup_y 8 4 6),
        (test_lookup_target 8 3 1), (test_lookup_target 8 3 6),
        (test_lookup_target 8 4 1), (test_lookup_target 8 4 6).
    reflexivity.
Qed.


(** ** Part 3: Connection between big- and small-step semantics *)

(* Prove the following theorem demonstrating the connection between the big-step
 * and small-step semantics:
 *
 * If the small-step semantics aborts, then the big-step semantics may
 * potentially abort.
 *)

Lemma eval_dec : forall m:nat, m=O \/ exists p:nat, m=S p.
Proof.
  intro m; destruct m;
      [ exact (or_introl (eq_refl O)) | exact (or_intror (ex_intro _ m (eq_refl (S m)))) ].
Qed.
Lemma abort_interrupts : forall n:nat, forall (c1 c2:list cmd) (v:valuation),
  small_aborted (do_steps n [SRunning v c1]) -> small_aborted (do_steps n [SRunning v (c1 ++ c2)]).
Proof.
  intro n; elim n.
  (* Base case *)
    intros c1 c2 v absurd; discriminate (proj1 (small_aborted_equiv _) absurd).
  (* Recursion *)
    clear n; intros n rec c1; elim c1.
    (* [] *)
      intros c2 v absurd.
      replace (do_steps (S n) [SRunning v []]) with (do_steps n [SDone (Terminated v)]) in absurd by reflexivity.
      assert (small_terminated [SDone (Terminated v)]) as taut.
        reflexivity.
      elim (terminated_not_aborted _ (terminated_future _ _ taut (do_steps_ex n [SDone (Terminated v)])) absurd).
    intro a; elim a.
    (* (Assign va a)::q *)
      exact (fun _ _ _ _ _ _ H => rec _ _ _ H).
    (* Skip::q *)
      exact (fun _ _ _ _ H => rec _ _ _ H).
    (* (Seq ca cb)::q *)
      exact (fun _ _ _ _ _ _ _ _ H => rec _ _ _ H).
    (* (Choose ca cb)::q *)
      intros ca rec2 cb rec3 q rec4 c2 v H.
      replace (do_steps (S n) [SRunning v (((ca <|> cb)%cmd :: q) ++ c2)])
          with (do_steps n ((SRunning v (ca::q ++ c2))::[SRunning v (cb::q ++ c2)])) by reflexivity.
      replace (do_steps (S n) [SRunning v ((ca <|> cb)%cmd :: q)])
          with (do_steps n ((SRunning v (ca::q))::[SRunning v (cb::q)])) in H by reflexivity.
      replace ((SRunning v (ca::q ++ c2))::[SRunning v (cb::q ++ c2)])
          with ([SRunning v (ca::q ++ c2)] ++ [SRunning v (cb::q ++ c2)]) by reflexivity.
      replace ((SRunning v (ca::q))::[SRunning v (cb::q)])
          with ([SRunning v (ca::q)] ++ [SRunning v (cb::q)]) in H by reflexivity.
      rewrite (step_split n [SRunning v (ca::q ++ c2)] [SRunning v (cb::q ++ c2)]).
      rewrite (step_split n [SRunning v (ca::q)] [SRunning v (cb::q)]) in H.
      refine (in_or_app _ _ _ _).
      elim (in_app_or _ _ _ H); intro Hcab;
          [ exact (or_introl (rec _ _ _ Hcab)) | exact (or_intror (rec _ _ _ Hcab)) ].
    (* If e ca cb *)
      intros e ca rec2 cb rec3 q rec4 c2 v.
      replace (do_steps (S n) [SRunning v (((if_ e then ca else cb)%cmd :: q) ++ c2)])
        with (do_steps n (full_step [SRunning v (((if_ e then ca else cb)%cmd :: q) ++ c2)])) by reflexivity.
      replace (do_steps (S n) [SRunning v (((if_ e then ca else cb)%cmd :: q))])
        with (do_steps n (full_step [SRunning v (((if_ e then ca else cb)%cmd :: q))])) by reflexivity.
      replace (((if_ e then ca else cb)%cmd :: q) ++ c2)
        with ([(if_ e then ca else cb)%cmd] ++ (q ++ c2)) by exact ((app_assoc _ _ _)).
      replace ([(if_ e then ca else cb)%cmd] ++ (q ++ c2))
        with (((if_ e then ca else cb)%cmd)::(q ++ c2)) by reflexivity.
      unfold full_step, singular_step, flat_map.
      replace (match interp e v with
          | 0 => [SRunning v (cb :: q ++ c2)]
          | S _ => [SRunning v (ca :: q ++ c2)]
          end ++ [])
        with (match interp e v with
          | 0 => [SRunning v (cb :: q ++ c2)]
          | S _ => [SRunning v (ca :: q ++ c2)]
          end) by exact (eq_sym (app_nil_r _)).
      replace (match interp e v with
          | 0 => [SRunning v (cb :: q)]
          | S _ => [SRunning v (ca :: q)]
          end ++ [])
        with (match interp e v with
          | 0 => [SRunning v (cb :: q)]
          | S _ => [SRunning v (ca :: q)]
          end) by exact (eq_sym (app_nil_r _)).
      elim (eval_dec (interp e v)).
      (* Then branch *)
        intros ev; rewrite ev; exact (rec _ _ _).
      (* Else branch *)
        intros evex; elim evex; intros p ev; rewrite ev; exact (rec _ _ _).
    (* While e c *)
      intros e c rec2 q rec3 c2 v.
      replace (do_steps (S n) [SRunning v (((while e do c)%cmd :: q) ++ c2)])
        with (do_steps n (full_step [SRunning v (((while e do c)%cmd :: q) ++ c2)])) by reflexivity.
      replace (do_steps (S n) [SRunning v (((while e do c)%cmd :: q))])
        with (do_steps n (full_step [SRunning v (((while e do c)%cmd :: q))])) by reflexivity.
      replace (((while e do c)%cmd :: q) ++ c2)
        with ([(while e do c)%cmd] ++ (q ++ c2)) by exact ((app_assoc _ _ _)).
      replace ([(while e do c)%cmd] ++ (q ++ c2))
        with (((while e do c)%cmd)::(q ++ c2)) by reflexivity.
      unfold full_step, singular_step, flat_map.
      replace (match interp e v with
          | 0 => [SRunning v (q ++ c2)]
          | S _ => [SRunning v (c::(while e do c)%cmd::q ++ c2)]
          end ++ [])
        with (match interp e v with
          | 0 => [SRunning v (q ++ c2)]
          | S _ => [SRunning v (c::(while e do c)%cmd::q ++ c2)]
          end) by exact (eq_sym (app_nil_r _)).
      replace (match interp e v with
          | 0 => [SRunning v q]
          | S _ => [SRunning v (c::(while e do c)%cmd::q)]
          end ++ [])
        with (match interp e v with
          | 0 => [SRunning v q]
          | S _ => [SRunning v (c::(while e do c)%cmd::q)]
          end) by exact (eq_sym (app_nil_r _)).
      elim (eval_dec (interp e v)).
      (* Do branch *)
        intros ev; rewrite ev; exact (rec _ _ _).
      (* Done branch *)
        intros evex; elim evex; intros p ev; rewrite ev; exact (rec _ _ _).
    (* Abort *)
      assert (forall m:nat, do_steps m [SDone Aborted] = [SDone Aborted]) as aborted_stays.
        intro m; elim m; [ reflexivity | exact (fun _ H => H) ].
      intros q rec2 c2 v H.
      replace (do_steps (S n) [SRunning v ((Abort :: q) ++ c2)])
          with (do_steps n ([SDone Aborted])) by reflexivity.
      rewrite (aborted_stays n).
      exact (or_introl (eq_refl _)).
Qed.

Lemma keep_pace : forall (a:cmd) (q:list cmd) (v1 v2:valuation),
    ~ In (SDone (Terminated v2)) (full_step [SRunning v1 (a::q)]).
Proof.
  intro a; elim a; clear a.
  (* Assign *)
    intros s a q v1 v2 absurd; invert absurd; [ discriminate H | elim H ].
  (* Skip *)
    intros q v1 v2 absurd; invert absurd; [ discriminate H | elim H ].
  (* Seq *)
    intros c1 rec1 c2 rec2 q v1 v2 absurd; invert absurd; [ discriminate H | elim H ].
  (* Choose *)
    intros c1 rec1 c2 rec2 q v1 v2 absurd; invert absurd; [ discriminate H | elim H ].
      discriminate.
      intro H2; elim H2.
  (* If *)
    intros a c1 rec1 c2 rec2 q v1 v2.
    replace (full_step [SRunning v1 ((if_ a then c1 else c2)%cmd :: q)])
        with (match interp a v1 with
        | O => [SRunning v1 (c2::q)]
        | S _ => [SRunning v1 (c1::q)]
        end) by exact (eq_sym (app_nil_r _)).
    elim (eval_dec (interp a v1)); [|intro Hp; elim Hp; clear Hp; intro p];
        intros H absurd; rewrite H in absurd; elim absurd; clear absurd; intro absurd;
        [ discriminate absurd | elim absurd | discriminate absurd | elim absurd ].
  (* While *)
    intros a c rec q v1 v2.
    replace (full_step [SRunning v1 ((while a do c)%cmd :: q)])
        with (match interp a v1 with
        | O => [SRunning v1 q]
        | S _ => [SRunning v1 (c::(While a c)::q)]
        end) by exact (eq_sym (app_nil_r _)).
    elim (eval_dec (interp a v1)); [|intro Hp; elim Hp; clear Hp; intro p];
        intros H absurd; rewrite H in absurd; elim absurd; clear absurd; intro absurd;
        [ discriminate absurd | elim absurd | discriminate absurd | elim absurd ].
  (* Abort *)
    intros q v1 v2 absurd; elim absurd; clear absurd; intro absurd; [ discriminate absurd | elim absurd ].
Qed.

Lemma before_termination0 : forall (st:state) (v:valuation),
    ~ In (SDone (Terminated v)) st
      -> In (SDone (Terminated v)) (full_step st)
      -> In (SRunning v []) st.
Proof.
  intro st; elim st; clear st.
  (* [] *)
    intros v taut absurd; elim (absurd).
  assert (forall (a:singular_state) (q:list singular_state) (v:valuation),
      In (SDone (Terminated v)) (full_step (a::q))
        -> In (SDone (Terminated v)) (full_step [a]) \/ In (SDone (Terminated v)) (full_step q))
      as my_rewrite.
    intros a q v.
    replace (full_step (a :: q)) with ((full_step [a]) ++ (full_step q))
        by exact (eq_sym (flat_map_app _ _ singular_step _ _)).
    exact (in_app_or _ _ _).
  intro a; elim a; clear a.
  intros v0 l0; elim l0; clear l0.
  (* (SRunning v0 nil)::q *)
    intros q rec v not_here here; elim (my_rewrite _ _ _ here).
    (* a contains the terminaison *)
      intro done_in; elim done_in; clear done_in; intro done_eq; invert done_eq.
      exact (or_introl (eq_refl _)).
    (* q contains the terminaison *)
      intro H; refine (_ (rec _ (fun P => not_here (in_cons _ _ _ P)) H)).
      exact (in_cons _ _ _).
  (* (SRunning v0 ac::qc)::q *)
    intros ac qc rec q rec2 v not_here here. elim (my_rewrite _ _ _ here).
    (* a contains the terminaison *)
      intro absurd; elim (keep_pace _ _ _ _ absurd).
    (* q contains the terminaison *)
      intro H; refine (_ (rec2 _ (fun P => not_here (in_cons _ _ _ P)) H)).
      exact (in_cons _ _ _).
  intro r; elim r; clear r.
  (* (SDone (Terminated v0))::q *)
    intros v q rec v0 v0_not_v H; elim (valuation_dec v v0).
      intro v_eq_v0; rewrite v_eq_v0 in v0_not_v; elim (v0_not_v (or_introl (eq_refl _))).
      intro v_not_v0; right; elim (my_rewrite _ _ _ H).
        intro absurd; elim absurd; clear absurd; intro absurd; invert absurd; elim (v_not_v0 (eq_refl _)).
        exact (rec _ (fun P => v0_not_v (in_cons _ _ _ P))).
  (* (SDone Abort)::q *)
    intros q rec v not_here here; elim (my_rewrite _ _ _ here).
      intro absurd; invert absurd; [ discriminate H | invert H ].
      intro term_q; right; exact (rec _ (fun P => not_here (in_cons _ _ _ P)) term_q).
Qed.
Lemma before_termination : forall (n:nat) (st:state) (v:valuation),
    ~ In (SDone (Terminated v)) st
      -> In (SDone (Terminated v)) (do_steps n st)
      -> exists m:nat, In (SRunning v nil) (do_steps m st).
Proof.
  (* Main goal: *)
  intro n; elim n.
  (* Base case *)
    intros st v not_there there; elim (not_there there).
  (* Recursion *)
    clear n; intros n rec st v H0 H1.
    elim (in_dec state_dec (SDone (Terminated v)) (full_step st)).
    (* One step *)
      intro H; exists O.
      exact (before_termination0 _ _ H0 H).
    (* More than one step *)
      intro H; elim (rec _ _ H H1); intros m Hb; exists (S m); exact Hb.
Qed.
Lemma before_termination_or : forall (s:state) (v:valuation),
    In (SDone (Terminated v)) (full_step s) -> In (SDone (Terminated v)) s \/ In (SRunning v nil) s.
Proof.
  intros s v; elim (in_dec state_dec (SDone (Terminated v)) s).
    exact (fun P _ => or_introl P).
    exact (fun H1 H2 => or_intror (before_termination0 _ _ H1 H2)).
Qed.

Lemma before_aborted (s:state) :
    In (SDone Aborted) (full_step s)
      -> In (SDone Aborted) s \/ exists v q, In (SRunning v (Abort::q)) s.
Proof.
  elim s; clear s.
  (* [] *)
    intro absurd; elim absurd.
  intro a; elim a; clear a.
  (* (SRunning v l)::q *)
    intros v l q rec.
    replace (full_step (SRunning v l :: q)) with (flat_map singular_step ([SRunning v l] ++ q)) by reflexivity.
    rewrite (flat_map_app _ _ singular_step _ _).
    intro H; elim (in_app_or _ _ _ H); clear H; intro H.
    (* Abort from (SRunning v l) *)
      destruct l; [ elim H; [ discriminate | intro absurd; elim absurd ] |].
      destruct c.
        elim H; [ discriminate | intro absurd; elim absurd ].  (* Assign *)
        elim H; [ discriminate | intro absurd; elim absurd ].  (* Skip *)
        elim H; [ discriminate | intro absurd; elim absurd ].  (* Seq *)
        elim H; [ discriminate | intro absurd; elim absurd; clear absurd;
            [ discriminate | intro absurd; elim absurd ] ].  (* Choose *)
      (* If *)
        replace (flat_map singular_step [SRunning v ((if_ a then c1 else c2)%cmd :: l)])
            with (match interp a v with | O => [SRunning v (c2::l)] | _ => [SRunning v (c1::l)] end ++ [])
            in H by reflexivity.
        elim (eval_dec (interp a v)); intro interpeval;
            [| elim interpeval; clear interpeval; intros p interpeval ];
            rewrite interpeval in H;
            elim H; [ discriminate | intro absurd; elim absurd | discriminate | intro absurd; elim absurd ].
      (* While *)
        replace (flat_map singular_step [SRunning v ((while a do c)%cmd :: l)])
            with (match interp a v with | O => [SRunning v l] | _ => [SRunning v (c::(While a c)::l)] end ++ [])
            in H by reflexivity.
        elim (eval_dec (interp a v)); intro interpeval;
            [| elim interpeval; clear interpeval; intros p interpeval ];
            rewrite interpeval in H;
            elim H; [ discriminate | intro absurd; elim absurd | discriminate | intro absurd; elim absurd ].
      (* Abort *)
        exact (or_intror (ex_intro _ v (ex_intro _ l (or_introl (eq_refl _))))).
    (* Abort from q *)
      elim (rec H); clear rec H; intro H.
        exact (or_introl (in_cons _ _ _ H)).
        elim H; clear H; intros v0 H; elim H; clear H; intros q0 H; right; exists v0, q0;
            exact (in_cons _ _ _ H).
  intro r; elim r; clear r.
  (* (SDone (Terminated v))::q *)
    intros v q rec.
    replace (full_step (SDone (Terminated v) :: q))
        with (flat_map singular_step ([SDone (Terminated v)] ++ q)) by reflexivity.
    rewrite (flat_map_app _ _ singular_step _ _).
    intro H; elim (in_app_or _ _ _ H); clear H; intro H;
        [ elim H; clear H; [ discriminate | intro H; elim H ] |].
    elim (rec H); clear rec H; intro H.
      exact (or_introl (in_cons _ _ _ H)).
      elim H; clear H; intros v0 H; elim H; clear H; intros q0 H; right; exists v0, q0;
          exact (in_cons _ _ _ H).
  (* (SDone Aborted)::q *)
    exact (fun _ _ _ => or_introl (or_introl (eq_refl _))).
Qed.

Lemma before_running : forall (s:state) (v:valuation) (lc:list cmd),
    In (SRunning v lc) (full_step s)
      -> exists v0 lc0, In (SRunning v0 lc0) s /\ In (SRunning v lc) (full_step [SRunning v0 lc0]).
Proof.
  intro s; elim s; clear s; [ intros v lc absurd; elim absurd |].
  intro a; elim a; clear a.
  (* SRunning v l :: q *)
    intros v l q rec v0 lc.
    replace (full_step (SRunning v l :: q))
        with (flat_map singular_step ([SRunning v l] ++ q)) by reflexivity.
    rewrite (flat_map_app _ _ singular_step _ _).
    intro H; elim (in_app_or _ _ _ H); clear H; intro H.
      exists v, l; exact (conj (or_introl (eq_refl _)) H).
      elim (rec _ _ H); clear rec H; intros v1 H; elim H; clear H; intros lc1 H.
        exists v1, lc1; exact (conj (in_cons _ _ _ (proj1 H)) (proj2 H)).
  (* SDone r :: q *)
    intros r q rec v lc.
    replace (full_step (SDone r :: q))
        with (flat_map singular_step ([SDone r] ++ q)) by reflexivity.
    rewrite (flat_map_app _ _ singular_step _ _).
    intro H; elim (in_app_or _ _ _ H); clear H; intro H.
      destruct r; elim H;
          [ discriminate | intro absurd; elim absurd | discriminate | intro absurd; elim absurd ].
      elim (rec _ _ H); clear rec H; intros v1 H; elim H; clear H; intros lc1 H.
        exists v1, lc1; exact (conj (in_cons _ _ _ (proj1 H)) (proj2 H)).
Qed.

Lemma abort_const : forall m:nat, do_steps m [SDone Aborted] = [SDone Aborted].
Proof.
  intro m; elim m; clear m.
    reflexivity.
    intros m H; rewrite <- H at 2; reflexivity.
Qed.
Lemma pending_commands : forall (n:nat) (lc0 lc1 q:list cmd) (v0 v1:valuation),
    In (SRunning v1 lc1) (do_steps n [SRunning v0 lc0])
    -> In (SRunning v1 (lc1 ++ q)) (do_steps n [SRunning v0 (lc0 ++ q)]).
Proof.
  intro n; elim n; clear n.
  (* Base case *)
    intros lc0 lc1 q v0 v1 H; elim H; clear H.
      intro eq; invert eq; exact (or_introl (eq_refl _)).
      intro absurd; elim absurd.
  (* Recursion *)
    intros n rec lc0; elim lc0; clear lc0.
    (* No command *)
      intros lc1 q v0 v1 absurd.
      replace (do_steps (S n) [SRunning v0 []]) with (do_steps n [SDone (Terminated v0)])
          in absurd by reflexivity.
      elim (small_terminated_only_terminated _ _
          (terminated_future [SDone (Terminated v0)] (do_steps n [SDone (Terminated v0)])
             (eq_refl _) (do_steps_ex _ _)) absurd).
      discriminate.
    intro a; elim a; clear a.
    (* Assign *)
      exact (fun _ _ _ _ _ _ _ _ => rec _ _ _ _ _).
    (* Skip *)
      exact (fun _ _ _ _ _ _ => rec _ _ _ _ _).
    (* Seq *)
      exact (fun _ _ _ _ _ _ _ _ _ _ => rec _ _ _ _ _).
    (* Choose *)
      intros c1 rec1 c2 rec2 l recl lc1 q v0 v1.
      replace (((c1 <|> c2)%cmd :: l) ++ q)
          with ((c1 <|> c2)%cmd :: (l ++ q)) by exact (eq_sym (app_comm_cons _ _ _)).
      replace (do_steps (S n) [SRunning v0 ((c1 <|> c2)%cmd :: l)])
          with (do_steps n ([SRunning v0 (c1::l)] ++ [SRunning v0 (c2::l)])) by reflexivity.
      replace (do_steps (S n) [SRunning v0 ((c1 <|> c2)%cmd :: l ++ q)])
          with (do_steps n ([SRunning v0 (c1::l++q)] ++ [SRunning v0 (c2::l++q)])) by reflexivity.
      rewrite (step_split n _ _); rewrite (step_split n _ _).
      intro H; elim (proj1 (in_app_iff _ _ _) H); clear H; intro H.
        refine (proj2 (in_app_iff _ _ _) (or_introl (rec _ _ _ _ _ H))).
        refine (proj2 (in_app_iff _ _ _) (or_intror (rec _ _ _ _ _ H))).
    (* If *)
      intros a c1 rec1 c2 rec2 l recl lc1 q v0 v1.
      replace (((if_ a then c1 else c2)%cmd :: l) ++ q)
          with ((if_ a then c1 else c2)%cmd :: (l ++ q)) by exact (eq_sym (app_comm_cons _ _ _)).
      replace (do_steps (S n) [SRunning v0 ((if_ a then c1 else c2)%cmd :: l)])
          with (do_steps n (
            match interp a v0 with
            | O => [SRunning v0 (c2::l)]
            | _ => [SRunning v0 (c1::l)]
            end ++ [])) by reflexivity; rewrite app_nil_r.
      replace (do_steps (S n) [SRunning v0 ((if_ a then c1 else c2)%cmd :: l++q)])
          with (do_steps n (
            match interp a v0 with
            | O => [SRunning v0 (c2::l++q)]
            | _ => [SRunning v0 (c1::l++q)]
            end ++ [])) by reflexivity; rewrite app_nil_r.
      elim (eval_dec (interp a v0)); [| intro eqex; elim eqex; intro p];
          intro eval; rewrite eval; exact (rec _ _ _ _ _).
    (* While *)
      intros a c recc l recl lc1 q v0 v1.
      replace (((while a do c)%cmd :: l) ++ q)
          with ((while a do c)%cmd :: (l ++ q)) by exact (eq_sym (app_comm_cons _ _ _)).
      replace (do_steps (S n) [SRunning v0 ((while a do c)%cmd :: l)])
          with (do_steps n (
            match interp a v0 with
            | O => [SRunning v0 l]
            | _ => [SRunning v0 (c::(While a c)::l)]
            end ++ [])) by reflexivity; rewrite app_nil_r.
      replace (do_steps (S n) [SRunning v0 ((while a do c)%cmd :: l ++ q)])
          with (do_steps n (
            match interp a v0 with
            | O => [SRunning v0 (l++q)]
            | _ => [SRunning v0 (c::(While a c)::l++q)]
            end ++ [])) by reflexivity; rewrite app_nil_r.
      elim (eval_dec (interp a v0)); [| intro eqex; elim eqex; intro p];
          intro eval; rewrite eval; exact (rec _ _ _ _ _).
    (* Abort *)
      intros l recl lc1 q v0 v1 absurd.
      replace (do_steps (S n) [SRunning v0 (Abort :: l)])
          with (do_steps n [SDone Aborted]) in absurd by reflexivity.
      rewrite (abort_const n) in absurd.
      elim absurd; clear absurd; [ discriminate | intro absurd; elim absurd ].
Qed.

Lemma split_computation0 : forall (lst1:state) (st1:singular_state),
    In st1 lst1 -> forall (m:nat) (st2:singular_state), In st2 (do_steps m [st1]) -> In st2 (do_steps m lst1).
Proof.
  intro lst1; elim lst1; clear lst1.
  (* [] *)
    intros st1 absurd; elim absurd.
  (* a::q *)
    intros a q rec st1 H; replace (a::q) with ([a] ++ q) by reflexivity; elim H; clear H.
    (* a = st1 *)
      intros a_eq m st2 H; rewrite a_eq.
      rewrite (step_split _ _ _).
      exact (in_or_app _ _ _ (or_introl H)).
    (* In st1 q *)
      intros st1q m st2 H.
      rewrite (step_split _ _ _).
      refine (in_or_app _ _ _ (or_intror _)).
      exact (rec st1 st1q m st2 H).
Qed.

Theorem split_computation1 (n m:nat) (lst0:list singular_state) (st1 st2:singular_state) :
    In st1 (do_steps n lst0)
    -> In st2 (do_steps m [st1])
    -> In st2 (do_steps (m+n) lst0).
Proof.
  rewrite <- (do_steps_split _ _ _).
  exact (fun H => split_computation0 _ _ H _ _).
Qed.

Theorem split_computation2 (n m:nat) (v0 v1:valuation) (lc q:list cmd) (st2:singular_state) :
    In (SRunning v1 nil) (do_steps n [SRunning v0 lc])
    -> In st2 (do_steps m [SRunning v1 q])
    -> In st2 (do_steps (m+n) [SRunning v0 (lc ++ q)]).
Proof (fun H => split_computation1 _ _ _ _ _ (pending_commands _ _ _ _ _ _ H)).

Theorem big_to_small :
    forall (v:valuation) (c:cmd) (r:result), eval v c r -> exists n:nat, In (SDone r) (do_steps n (init v c)).
Proof.
  assert (forall m:nat, m<>0 -> exists p:nat, m=S p) as intro_prec.
    intro m; elim m; clear m.
      intro absurd; elim (absurd (eq_refl O)).
      exact (fun p _ _ => ex_intro _ p (eq_refl (S p))).
  assert (forall (mv0 mv1:valuation) (mc:cmd), ~ In (SDone (Terminated mv1)) (init mv0 mc)) as cmd_takes_time.
    intros mv0 mv1 mc absurd; elim absurd; clear absurd; intro absurd; [ discriminate absurd | elim absurd ].
  intros v c r eval; elim eval.
  (* EvalAssign *)
    exact (fun _ _ _ => ex_intro _ 2 (in_eq _ nil)).
  (* EvalSkip *)
    exact (fun _ => ex_intro _ 2 (in_eq _ nil)).
  (* EvalSeqAborted *)
    intros v0 cmd0 cmd1 useless H; elim H; intro n; exists (S n).
    replace (do_steps (S n) (init v0 (cmd0;; cmd1)%cmd))
        with (do_steps n [SRunning v0 [cmd0; cmd1]]) by reflexivity.
    exact (abort_interrupts _ _ _ _ H0).
  (* EvalSeqSuccess *)
    intros v0 cmd0 v1 cmd1 res cmd0eval rec0 cmd1eval rec1.
    elim rec0; elim rec1; intros n0 rec0n n2 rec2n.
    elim (before_termination _ _ _ (cmd_takes_time _ _ _) rec2n); intros n1 rec1n.
    exists (S (n0 + n1)).
    exact (split_computation2 _ _ _ _ _ _ _ rec1n rec0n).
  (* EvalChoose0 *)
    intros v0 cmd0 cmd1 res cmd0eval rec; elim rec; clear rec; intros n rec; exists (S n).
    replace (do_steps (S n) (init v0 (cmd0 <|> cmd1)%cmd))
        with (do_steps n ([SRunning v0 [cmd0]] ++ [SRunning v0 [cmd1]])) by reflexivity.
    rewrite (step_split _ _ _).
    exact (in_or_app _ _ _ (or_introl rec)).
  (* EvalChoose1 *)
    intros v0 cmd0 cmd1 res cmd0eval rec; elim rec; clear rec; intros n rec; exists (S n).
    replace (do_steps (S n) (init v0 (cmd0 <|> cmd1)%cmd))
        with (do_steps n ([SRunning v0 [cmd0]] ++ [SRunning v0 [cmd1]])) by reflexivity.
    rewrite (step_split _ _ _).
    exact (in_or_app _ _ _ (or_intror rec)).
  (* EvalIfFalse *)
    intros v0 a cmd1 cmd0 res interpeval cmd0eval rec; elim rec; clear rec; intros n rec; exists (S n).
    replace (do_steps (S n) (init v0 (if_ a then cmd1 else cmd0)%cmd))
        with (do_steps n (
          match interp a v0 with
          | O => [SRunning v0 [cmd0]]
          | _ => [SRunning v0 [cmd1]]
          end ++ [])) by reflexivity.
    rewrite interpeval.
    exact rec.
  (* EvalIfTrue *)
    intros v0 a cmd1 cmd0 res interpeval cmd1eval rec; elim rec; clear rec; intros n rec; exists (S n).
    elim (intro_prec _ interpeval); clear interpeval; intros p interpeval.
    replace (do_steps (S n) (init v0 (if_ a then cmd1 else cmd0)%cmd))
        with (do_steps n (
          match interp a v0 with
          | O => [SRunning v0 [cmd0]]
          | _ => [SRunning v0 [cmd1]]
          end ++ [])) by reflexivity.
    rewrite interpeval.
    exact rec.
  (* EvalWhileFalse *)
    intros v0 a cmd0 interpeval; exists 2.
    replace (do_steps 2 (init v0 (while a do cmd0)%cmd))
        with (do_steps 1 (
          match interp a v0 with
          | O => [SRunning v0 nil]
          | _ => [SRunning v0 [cmd0; While a cmd0]]
          end ++ [])) by reflexivity.
    rewrite interpeval.
    exact (or_introl (eq_refl _)).
  (* EvalWhileTrueAborted *)
    intros v0 a cmd0 interpeval cmd0eval rec; elim rec; clear rec; intros n rec; exists (S n).
    elim (intro_prec _ interpeval); clear interpeval; intros p interpeval.
    replace (do_steps (S n) (init v0 (while a do cmd0)%cmd))
        with (do_steps n (
          match interp a v0 with
          | O => [SRunning v0 nil]
          | _ => [SRunning v0 [cmd0; While a cmd0]]
          end ++ [])) by reflexivity.
    rewrite interpeval.
    exact (abort_interrupts _ _ _ _ rec).
  (* EvalWhileTrueSuccess *)
    intros v0 a cmd0 v1 res interpeval cmd0eval rec0 followeval followrec.
    elim rec0; elim followrec; clear rec0 followrec; intros m followrec n rec0.
    elim (intro_prec _ interpeval); clear interpeval; intros p interpeval.
    elim (before_termination _ _ _ (cmd_takes_time _ _ _) rec0); intros n0 rec00.
    exists (S (m+n0)).
    replace (do_steps (S (m + n0)) (init v0 (while a do cmd0)%cmd))
        with (do_steps (m + n0) (
          match interp a v0 with
          | O => [SRunning v0 nil]
          | _ => [SRunning v0 [cmd0; While a cmd0]]
          end ++ [])) by reflexivity.
    rewrite interpeval.
    exact (split_computation2 _ _ _ _ _ _ _ rec00 followrec).
  (* EvalAbort *)
    exact (fun _ => ex_intro _ 1 (or_introl (eq_refl _))).
Qed.

Lemma tail_cmd_unchanged : forall a v0 v1 q lc,
    In (SRunning v1 lc) (full_step [SRunning v0 (a::q)])
    -> exists lc1,
      lc = lc1++q
      /\
      forall q', In (SRunning v1 (lc1++q')) (full_step [SRunning v0 (a::q')]).
Proof.
  intro a; elim a; clear a.
  (* Assign *)
    intros s a v0 v1 q lc H; invert H; invert H0.
    exact (ex_intro _ nil (conj (eq_sym (app_nil_l lc)) (fun _ => or_introl (eq_refl _)))).
  (* Skip *)
    intros v0 v1 q lc H; invert H; invert H0.
    exact (ex_intro _ nil (conj (eq_sym (app_nil_l lc)) (fun _ => or_introl (eq_refl _)))).
  (* Seq *)
    intros c1 rec1 c2 rec2 v0 v1 q lc H; invert H; invert H0.
    exact (ex_intro _ [c1;c2] (conj (eq_refl _) (fun _ => or_introl (eq_refl _)))).
  (* Choose *)
    intros c1 rec1 c2 rec2 v0 v1 q lc H; invert H; invert H0; [| invert H | invert H ].
    exact (ex_intro _ [c1] (conj (eq_refl _) (fun _ => or_introl (eq_refl _)))).
    exact (ex_intro _ [c2] (conj (eq_refl _) (fun _ => or_intror (or_introl (eq_refl _))))).
  (* If *)
    intros a c1 rec1 c2 rec2 v0 v1 q lc.
    replace (full_step [SRunning v0 ((if_ a then c1 else c2)%cmd :: q)]) with (
        match interp a v0 with
        | O => [SRunning v0 (c2::q)]
        | _ => [SRunning v0 (c1::q)]
        end ++ []) by reflexivity.
    elim (eval_dec (interp a v0)); intro interpeval.
    (* False *)
      rewrite interpeval; intro H; invert H; invert H0.
      refine (ex_intro _ [c2] (conj (eq_refl _) _)); intro q'.
      replace (full_step [SRunning v1 ((if_ a then c1 else c2)%cmd :: q')]) with (
          match interp a v1 with
          | O => [SRunning v1 (c2::q')]
          | _ => [SRunning v1 (c1::q')]
          end ++ []) by reflexivity.
      rewrite interpeval; exact (or_introl (eq_refl _)).
    (* True *)
      elim interpeval; clear interpeval; intros p interpeval.
      rewrite interpeval; intro H; invert H; invert H0.
      refine (ex_intro _ [c1] (conj (eq_refl _) _)); intro q'.
      replace (full_step [SRunning v1 ((if_ a then c1 else c2)%cmd :: q')]) with (
          match interp a v1 with
          | O => [SRunning v1 (c2::q')]
          | _ => [SRunning v1 (c1::q')]
          end ++ []) by reflexivity.
      rewrite interpeval; exact (or_introl (eq_refl _)).
  (* While *)
    intros a c rec v0 v1 q lc.
    replace (full_step [SRunning v0 ((while a do c)%cmd :: q)]) with (
        match interp a v0 with
        | O => [SRunning v0 q]
        | _ => [SRunning v0 (c::While a c::q)]
        end ++ []) by reflexivity.
    elim (eval_dec (interp a v0)); intro interpeval.
    (* False *)
      rewrite interpeval; intro H; invert H; invert H0.
      refine (ex_intro _ nil (conj (eq_refl _) _)); intro q'.
      replace (full_step [SRunning v1 ((while a do c)%cmd :: q')]) with (
          match interp a v1 with
          | O => [SRunning v1 q']
          | _ => [SRunning v1 (c::While a c::q')]
          end ++ []) by reflexivity.
      rewrite interpeval; exact (or_introl (eq_refl _)).
    (* True *)
      elim interpeval; clear interpeval; intros p interpeval.
      rewrite interpeval; intro H; invert H; invert H0.
      refine (ex_intro _ [c; (While a c)] (conj (eq_refl _) _)); intro q'.
      replace (full_step [SRunning v1 ((while a do c)%cmd :: q')]) with (
          match interp a v1 with
          | O => [SRunning v1 q']
          | _ => [SRunning v1 (c::(While a c)::q')]
          end ++ []) by reflexivity.
      rewrite interpeval; exact (or_introl (eq_refl _)).
  (* Abort *)
    intros v0 v1 q lc absurd; elim absurd; clear absurd; [ discriminate | intro absurd; elim absurd ].
Qed.

Theorem code_split : forall (n:nat) (st:singular_state) (lc1 lc2:list cmd) (v:valuation),
    In st (do_steps n [SRunning v (lc1 ++ lc2)]) -> 
      (
        (* c1 terminates in n steps *)
        exists (v2:valuation) (m:nat),
        m<=n
        /\ In (SDone (Terminated v2)) (do_steps n [SRunning v lc1])
        /\ In st (do_steps m [SRunning v2 lc2])
      ) \/ (
        (* c1 does not terminate in n steps *)
        exists st0:singular_state,
        (
          (st = SDone Aborted /\ st0 = st)
          \/
          (exists v0 l0, st = SRunning v0 (l0 ++ lc2) /\ st0 = SRunning v0 l0)
        )
        /\ In st0 (do_steps n [SRunning v lc1])
      ).
Proof.
  assert (forall s v, In (SDone (Terminated v)) s -> In (SDone (Terminated v)) (full_step s))
      as terminated_const.
    intro s; elim s; clear s; [ intros v H; elim H |].
    intros a q rec v H; elim H; clear H.
    (* Head *)
      intro a_eq; rewrite a_eq.
      replace (full_step (SDone (Terminated v) :: q))
          with (flat_map singular_step ([SDone (Terminated v)] ++ q)) by reflexivity.
      rewrite (flat_map_app _ _ singular_step _ _).
      exact (or_introl (eq_refl _)).
    (* Tail *)
      replace (full_step (a :: q))
          with (flat_map singular_step ([a] ++ q)) by reflexivity.
      rewrite (flat_map_app _ _ singular_step _ _).
      exact (fun P => in_or_app _ _ _ (or_intror (rec _ P))).
  intro n; elim n; clear n.
  (* Base case *)
    intros st lc1 lc2 v H; elim H; [| intro absurd; elim absurd ]; clear H.
    intro st_val; rewrite <- st_val; clear st_val; right.
    exists (SRunning v lc1); refine (conj _ (or_introl (eq_refl _))).
    right; exists v, lc1; exact (conj (eq_refl _) (eq_refl _)).
  (* Recursion *)
    intros n rec st lc1 lc2 v H.
    replace (do_steps (S n) [SRunning v (lc1 ++ lc2)])
        with (do_steps n (full_step [SRunning v (lc1 ++ lc2)])) in H by reflexivity.
    rewrite <- (do_steps_split0 n _) in H.
    destruct st.
    (* st = SRunning v0 l *)
      elim (before_running _ _ _ H); clear H; intros v4 H; elim H; clear H; intros lc4 [H1 H2].
      elim (rec _ _ _ _ H1); clear rec; intro H; elim H; clear H.
      (* Left branch *)
        intros v2 H; elim H; clear H; intros m [mcmp [nstep mstep]].
        left; exists v2, (S m); refine (conj (le_n_S _ _ mcmp) _).
        exact (conj
            (split_computation1 n 1 _ _ _ nstep (or_introl (eq_refl _)))
            (split_computation1 m 1 _ _ _ mstep H2)).
      (* Right branch *)
        intros st0 [H H3]; elim H; clear H; intro H; elim H; clear H; [ discriminate |].
        intros vf H; elim H; clear H; intros l0 [H4 H5].
        destruct l0.
        (* Finishes in c1 after n+1 steps *)
          destruct lc2; [ invert H4; elim H2; [ discriminate | intro absurd; elim absurd ] |].
          rewrite (app_nil_l _) in H4; invert H4.
          left; exists vf, 1; refine (conj (Nat.lt_0_succ n) (conj _ H2)).
          exact (split_computation1 n 1 _ _ _ H3 (or_introl (eq_refl _))).
        (* Does not finish in c1 *)
          invert H4; right.
          elim (tail_cmd_unchanged _ _ _ _ _ H2); intros hlc [l_eq H].
          exists (SRunning v0 (hlc ++ l0)).
          refine (conj (or_intror _) (split_computation1 n 1 _ _ _ H3 (H l0))).
          exists v0, (hlc ++ l0); refine (conj _ (eq_refl _)).
          rewrite l_eq, (app_assoc _ _ _); reflexivity.
    destruct r.
    (* st = SDone (Terminvated v0) *)
      elim (before_termination_or _ _ H); clear H; intro H.
      (* c1;;c2 finish after n *)
        elim (rec _ _ _ _ H); clear rec; intro Hrec; elim Hrec; clear Hrec;
            [| intros st0 [absurd H2]; invert absurd; [| invert H0; invert H1 ]; discriminate (proj1 H0) ].
        intros v2 Hrec; elim Hrec; clear Hrec; intros m [m_le_n [nstep mstep]]; left.
        exists v2, m; refine (conj (le_S m n m_le_n) (conj _ mstep)).
        exact (split_computation1 n 1 _ _ _ nstep (or_introl (eq_refl))).
      (* c1;;c2 finish at n+1 *)
        elim (rec _ _ _ _ H); clear rec; intro Hrec; elim Hrec; clear Hrec.
        (* Left branch *)
          intros v2 Hrec; elim Hrec; clear Hrec; intros m [m_le_n [nstep mstep]].
          left; exists v2, (S m); refine (conj (le_n_S _ _ m_le_n) _).
          exact (conj
              (split_computation1 n 1 _ _ _ nstep (or_introl (eq_refl)))
              (split_computation1 m 1 _ _ _ mstep (or_introl (eq_refl)))).
        (* Right branch *)
          intros st0 [H1 H2]; invert H1; [ discriminate (proj1 H0) |].
          elim H0; clear H0; intros v2 H0; elim H0; clear H0; intros m [sreq st0_eq].
          invert st0_eq. invert sreq. pose (test := app_eq_nil _ _ (eq_sym H3)). invert test.
          left; exists v2, 1; refine (conj (Nat.lt_0_succ n) (conj _ (or_introl (eq_refl _)))).
          exact (split_computation1 n 1 _ _ _ H2 (or_introl (eq_refl _))).
    (* st = SDone Aborted *)
      elim (before_aborted _ H); clear H; intro H.
      (* Aborted after n steps *)
        elim (rec _ _ _ _ H); clear rec; intro Hrec; elim Hrec; clear Hrec.
        (* Aborted in c2 after n steps *)
          intros v2 Hrec; elim Hrec; clear Hrec; intros m [m_le_n [nstep mstep]]; left.
          exists v2, m; refine (conj (le_S _ _ m_le_n) (conj _ mstep)).
          exact (split_computation1 n 1 _ _ _ nstep (or_introl (eq_refl _))).
        (* Aborted in c1 after n steps *)
          intros st0 [H1 H2]; elim H1; clear H1; [| intro H1; invert H1; invert H0; discriminate (proj1 H1) ].
          intros [useless st0_eq]; invert st0_eq; right; exists (SDone Aborted).
          refine (conj (or_introl (conj (eq_refl _) (eq_refl _))) _).
          exact (split_computation1 n 1 _ _ _ H2 (or_introl (eq_refl _))).
      (* Aborted at n+1 steps *)
        elim H; clear H; intros v0 H; elim H; clear H; intros q H.
        elim (rec _ _ _ _ H); clear rec; intro Hrec; elim Hrec; clear Hrec.
        (* c1 terminates after n steps *)
          intros v2 Hrec; elim Hrec; clear Hrec; intros m [m_le_n [nstep mstep]].
          left; exists v2, (S m); refine (conj (le_n_S _ _ m_le_n) _).
          exact (conj
              (split_computation1 n 1 _ _ _ nstep (or_introl (eq_refl)))
              (split_computation1 m 1 _ _ _ mstep (or_introl (eq_refl)))).
        (* c1 does not terminate after n steps *)
          intros st0 [H1 H2]; elim H1; clear H1; [ intro absurd; discriminate (proj1 absurd) |].
          intro H1; elim H1; clear H1; intros v1 H1; elim H1; clear H1; intros l0 [H1 st0_eq].
          invert st0_eq; induct l0.
          (* c1 terminates at n+1 steps *)
            left; exists v1, 1; refine (conj (Nat.lt_0_succ n) _).
            rewrite (app_nil_l _) in H1; rewrite <- H1.
            exact (conj
                (split_computation1 n 1 _ _ _ H2 (or_introl (eq_refl)))
                (or_introl (eq_refl _))).
          (* c1 aborts at n+1 steps *)
            right; exists (SDone Aborted); refine (conj (or_introl (conj (eq_refl _) (eq_refl _))) _).
            invert H1.
            exact (split_computation1 n 1 _ _ _ H2 (or_introl (eq_refl _))).
Qed.

Lemma small_abort_big_may_abort_n : forall n:nat, forall v c r,
    In (SDone r) (do_steps n (init v c)) -> eval v c r.
Proof.
  assert (forall (m:nat) (v:valuation),
      do_steps m [SDone (Terminated v)] = [SDone (Terminated v)]) as termination_const.
    intro m; elim m; clear m; [ reflexivity | exact (fun _ H => H) ].
  assert (forall (n:nat) (v:valuation), In (SDone (Terminated v)) (do_steps n [SDone (Terminated v)])) as term_f.
    intro n; elim n.
      exact (fun v => or_introl (eq_refl _)).
      exact (fun p rec v => split_computation1 p 1 _ _ _ (rec v) (or_introl (eq_refl))).
  intro n; elim n; clear n.
  (* Base case *)
    intros v c r absurd; elim absurd; clear absurd; [ discriminate | intro absurd; elim absurd ].
  (* Recursion *)
    intros n rec v c; elim c; clear c.
    (* Assign *)
      intros s a r.
      destruct n; [ intro absurd; elim absurd; clear absurd; intro absurd; [ discriminate | elim absurd ] |].
      replace (do_steps (S (S n)) (init v (s <- a)%cmd))
          with (do_steps n [SDone (Terminated (v $+ (s, interp a v)))]) by reflexivity.
      rewrite (termination_const n _).
      intro H; elim H; clear H; intro H; invert H.
      exact (EvalAssign _ _ _).
    (* Skip *)
      destruct n; [ intros r absurd; elim absurd; clear absurd; [ discriminate | intro absurd; elim absurd ] |].
      replace (do_steps (S (S n)) (init v Skip))
          with (do_steps n [SDone (Terminated v)]) by reflexivity.
      rewrite (termination_const n v).
      intro H; elim H; clear H.
        intros v0 H; elim H; clear H.
          intro H; invert H; exact (EvalSkip _).
          intro H; elim H.
        intro absurd; elim absurd; clear absurd; [ discriminate | intro absurd; elim absurd ].
    (* Seq *)
      intros c1 rec1 c2 rec2 r.
      replace (do_steps (S n) (init v (c1;; c2)%cmd))
          with (do_steps n [SRunning v [c1; c2]]) by reflexivity.
      elim r; clear r.
      (* Terminated v0 *)
        intros v0 H; elim (code_split n _ [c1] [c2] v H); clear H.
        (* Left branch *)
          intro H2; elim H2; clear H2; intros v2 H2; elim H2; clear H2; intros m [m_le_n [nstep mstep]].
          refine (EvalSeqSuccess v c1 v2 c2 (Terminated v0) (rec _ _ _ nstep) (rec _ _ _ _)).
          rewrite (le_plus_minus _ _ m_le_n), (plus_comm _ _).
          exact (split_computation1 m (n - m) _ _ _ mstep (term_f _ v0)).
        (* Right branch - absurd *)
          intro H2; elim H2; clear H2; intros st0 [H2 nstep]; elim H2; clear H2; intro H2;
            [ discriminate (proj1 H2) | invert H2; invert H; discriminate (proj1 H0) ].
      (* Aborted *)
        intro H; elim (code_split n _ [c1] [c2] v H); clear H.
        (* Left branch *)
          intro H2; elim H2; clear H2; intros v2 H2; elim H2; clear H2; intros m [m_le_n [nstep mstep]].
          refine (EvalSeqSuccess v c1 v2 c2 Aborted (rec _ _ _ nstep) (rec _ _ _ _)).
          rewrite (le_plus_minus _ _ m_le_n), (plus_comm _ _).
          refine (split_computation1 m (n - m) _ _ _ mstep _).
          rewrite (abort_const (n - m)); exact (or_introl (eq_refl _)).
        (* Right branch *)
          intro H2; elim H2; clear H2; intros st0 [H2 nstep]; elim H2; clear H2; intro H2;
            [| invert H2; invert H; discriminate (proj1 H0) ].
          invert H2; destruct H.
          exact (EvalSeqAborted _ _ _ (rec _ _ _ nstep)).
    (* Choose *)
      intros c1 rec1 c2 rec2 r.
      replace (do_steps (S n) (init v (c1 <|> c2)%cmd))
          with (do_steps n ([SRunning v [c1]] ++ [SRunning v [c2]])) by reflexivity.
      rewrite (step_split n _ _).
      intro H; elim (in_app_or _ _ _ H); clear H; intro H.
      (* Result from c1 *)
        exact (EvalChoose0 v c1 c2 r (rec _ _ _ H)).
      (* Result from c2 *)
        exact (EvalChoose1 v c1 c2 r (rec _ _ _ H)).
    (* If *)
      intros a c1 rec1 c2 rec2 r.
      replace (do_steps (S n) (init v (if_ a then c1 else c2)%cmd))
          with (do_steps n (
            match interp a v with
            | O => [SRunning v [c2]]
            | _ => [SRunning v [c1]]
            end ++ [])) by reflexivity.
      elim (eval_dec (interp a v)); intros interpeval H.
      (* False branch *)
        rewrite interpeval in H.
        exact (EvalIfFalse v a c1 c2 r interpeval (rec _ _ _ H)).
      (* True branch *)
        elim interpeval; clear interpeval; intros p interpeval.
        assert (interp a v <> O) as condition_true; [ rewrite interpeval; discriminate |].
        rewrite interpeval in H.
        exact (EvalIfTrue v a c1 c2 r condition_true (rec _ _ _ H)).
    (* While *)
      intros a c recc r.
      replace (do_steps (S n) (init v (while a do c)%cmd))
          with (do_steps n (
            match interp a v with
            | O => [SRunning v []]
            | _ => [SRunning v [c; While a c]]
            end ++ [])) by reflexivity.
      elim (eval_dec (interp a v)); intros interpeval H.
      (* False branch *)
        rewrite interpeval in H.
        destruct n; [ invert H; [ discriminate H0 | invert H0 ] |].
        replace (do_steps (S n) ([SRunning v []] ++ []))
            with (do_steps n [SDone (Terminated v)]) in H by reflexivity.
        rewrite (termination_const n v) in H; invert H; invert H0.
        exact (EvalWhileFalse v a c interpeval).
      (* True branch *)
        elim interpeval; clear interpeval; intros p interpeval.
        assert (interp a v <> O) as condition_true; [ rewrite interpeval; discriminate |].
        rewrite interpeval in H.
        replace ([SRunning v [c; (while a do c)%cmd]] ++ [])
            with ([SRunning v ([c] ++ [(while a do c)%cmd])]) in H by reflexivity.
        elim (code_split _ _ _ _ _ H); clear H; intro H; elim H; clear H.
        (* c terminates *)
          intros v2 H; elim H; clear H; intros m [m_le_n [nstep mstep]].
          refine (EvalWhileTrueSuccess v a c v2 r condition_true (rec _ _ _ nstep) (rec _ _ _ _)).
          rewrite (le_plus_minus _ _ m_le_n), (plus_comm _ _).
          refine (split_computation1 m (n - m) _ _ _ mstep _).
          destruct r; [ rewrite (termination_const _ _) | rewrite (abort_const _) ];
              exact (or_introl (eq_refl _)).
        (* c aborts *)
          intros st0 [H nstep]; elim H; clear H; intro H;
              [| invert H; invert H0; discriminate (proj1 H) ].
          invert H; invert H0.
          exact (EvalWhileTrueAborted v a c condition_true (rec _ _ _ nstep)).
    (* Abort *)
      replace (do_steps (S n) (init v Abort)) with (do_steps n [SDone Aborted]) by reflexivity.
      rewrite (abort_const _); intros r H; invert H; invert H0.
      exact (EvalAbort v).
Qed.

Theorem small_abort_big_may_abort : forall v c s,
         step^* (init v c) s
      -> small_aborted s
      -> exists res, eval v c res /\ big_aborted res.
Proof.
  intros v c s evol; elim (do_steps_find _ _ evol); clear evol; intros n s_eq; invert s_eq.
  Check small_abort_big_may_abort_n.
  exact (fun H => ex_intro _ Aborted (conj (small_abort_big_may_abort_n n v c Aborted H) (eq_refl _))).
Qed.

(* As an additional challenge, you  you may want to prove the following
 * theorem. Note that this is *NOT* required for this assignment and
 * will not affect your grade.
 *
 * If the small-step semantics terminates without aborting, then the
 * big-step semantics may *not* abort.
 *)
Lemma le_exists (n m:nat) : n <= m \/ m <= n.
Proof.
  cases (n ?= m).
    rewrite (proj1 (Nat.compare_eq_iff _ _) Heq); exact (or_introl (le_n _)).
    exact (or_introl (le_S_n _ _ (le_S _ _ (proj1 (Nat.compare_lt_iff _ _) Heq)))).
    refine (or_intror (le_S_n _ _ (le_S _ _ (proj1 (Nat.compare_lt_iff _ _) _))));
        rewrite (Nat.compare_antisym _ _), Heq; reflexivity.
Qed.
Theorem small_terminates_big_may_not_abort :
       forall v c s,
         step^* (init v c) s
      -> small_terminated s
      -> forall res, 
             eval v c res 
          -> big_aborted res
          -> False.
Proof.
  intros v c s small_evol term_s r big_evol r_abort; invert r_abort.
  elim (big_to_small v c _ big_evol); intros n small_abort.
  elim (do_steps_find _ _ small_evol); clear small_evol; intros m small_term; invert small_term.
  elim (le_exists n m).
  (* n <= m *)
    intro n_le_m.
    assert (In (SDone Aborted) (do_steps m (init v c))) as combined_aborted.
      rewrite (le_plus_minus _ _ n_le_m), (plus_comm _ _).
      refine (split_computation1 _ (m - n) _ _ (SDone Aborted) small_abort _).
      rewrite (abort_const _); exact (or_introl (eq_refl _)).
    exact (terminated_not_aborted _ term_s combined_aborted).
  (* m <= n *)
    intro m_le_n.
    assert (small_terminated (do_steps n (init v c))) as combined_term.
      rewrite (le_plus_minus _ _ m_le_n), (plus_comm _ _).
      rewrite <- (do_steps_split _ _ _).
      exact (terminated_future _ _ term_s (do_steps_ex (n - m) _)).
    exact (terminated_not_aborted _ combined_term small_abort).
Qed.
