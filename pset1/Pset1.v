(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 1 *)

Require Import Frap Pset1Sig.

(* The first part of this assignment involves the [bool] datatype,
 * which has the following definition.
 * <<
     Inductive bool :=
     | true
     | false.
   >>
 * We will define logical negation and conjunction of Boolean values,
 * and prove some properties of these definitions.
 *)

(* Define [Neg] so that it implements Boolean negation, which flips
 * the truth value of a Boolean value.
 *)
Definition Neg (b : bool) : bool :=
  match b with
    | false => true
    | true => false
  end.

(* For instance, the negation of [true] should be [false].
 * This proof should follow from reducing both sides of the equation
 * and observing that they are identical.
 *)
Theorem Neg_true : Neg true = false.
Proof.
  simpl.
  exact (eq_refl false).
Qed.

(* Negation should be involutive, meaning that if we negate
 * any Boolean value twice, we should get the original value back. 

 * To prove a fact like this that holds for all Booleans, it suffices
 * to prove the fact for both [true] and [false] by using the
 * [cases] tactic.
 *)
Theorem Neg_involutive : forall b : bool, Neg (Neg b) = b.
Proof.
  intros b.
  case b.
  simpl.
  exact (eq_refl _).
  simpl.
  exact (eq_refl _).
Qed.

(* Define [And] so that it implements Boolean conjunction. That is,
 * the result value should be [true] exactly when both inputs
 * are [true].
 *)
Definition And (x y : bool) : bool :=
  match x with
    | false => false
    | true => y
  end.

(* Here are a couple of examples of how [And] should act on
 * concrete inputs. 
 *)
Theorem And_true_true : And true true = true.
Proof.
  simpl.
  exact (eq_refl _).
Qed.

Theorem And_false_true : And false true = false.
Proof.
  simpl.
  exact (eq_refl _).
Qed.

(* Prove that [And] is commutative, meaning that switching the order
 * of its arguments doesn't affect the result.
 *)
Theorem And_comm : forall x y : bool, And x y = And y x.
Proof.
  intros x y.
  case x, y.
    simpl.
    exact (eq_refl _).
    simpl.
    exact (eq_refl _).
    simpl.
    exact (eq_refl _).
    simpl.
    exact (eq_refl _).
Qed.

(* Prove that the conjunction of a Boolean value with [true]
 * doesn't change that value.
 *)
Theorem And_true_r : forall x : bool, And x true = x.
Proof.
  intros x.
  case x.
    simpl.
    exact (eq_refl _).
    simpl.
    exact (eq_refl _).
Qed.

(* In the second part of this assignment, we will work with a simple language
 * of imperative arithmetic programs that sequentially apply operations
 * to a natural-number-valued state.

 * The [Prog] datatype defines abstract syntax trees for this language.
 *)

Print Prog.

(* Define [run] such that [run p n] gives the final state
 * that running the program [p] should result in, when the
 * initial state is [n].
 *)
Fixpoint run (p : Prog) (n : nat) : nat :=
  match p with
    | Done => n
    | AddThen m p2 => (run p2 (n + m))
    | MulThen m p2 => (run p2 (n * m))
    | SetToThen m p2 => (run p2 m)
  end.

Theorem run_Example1 : run Done 0 = 0.
Proof.
  simpl.
  exact (eq_refl O).
Qed.

Theorem run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
Proof.
  simpl.
  exact (eq_refl _).
Qed.

Theorem run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
Proof.
  simpl.
  exact (eq_refl _).
Qed.

(* Define [numInstructions] to compute the number of instructions
 * in a program, not counting [Done] as an instruction.
 *)
Fixpoint numInstructions (p : Prog) : nat :=
  match p with
    | Done => O
    | AddThen _ p2 => (S (numInstructions p2))
    | MulThen _ p2 => (S (numInstructions p2))
    | SetToThen _ p2 => (S (numInstructions p2))
  end.

Theorem numInstructions_Example :
  numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
Proof.
  simpl.
  exact (eq_refl _).
Qed.

(* Define [concatProg] such that [concatProg p1 p2] is the program
 * that first runs [p1] and then runs [p2].
 *)
Fixpoint concatProg (p1 p2 : Prog) : Prog :=
  match p1 with
    | Done => p2
    | AddThen m p12 => AddThen m (concatProg p12 p2)
    | MulThen m p12 => MulThen m (concatProg p12 p2)
    | SetToThen m p12 => SetToThen m (concatProg p12 p2)
  end.

Theorem concatProg_Example :
     concatProg (AddThen 1 Done) (MulThen 2 Done)
     = AddThen 1 (MulThen 2 Done).
Proof.
  simpl.
  exact (eq_refl _).
Qed.

(* Prove that the number of instructions in the concatenation of
 * two programs is the sum of the number of instructions in each
 * program.
 *)
Theorem concatProg_numInstructions
  : forall (p1 p2 : Prog), numInstructions (concatProg p1 p2)
                      = numInstructions p1 + numInstructions p2.
Proof.
  intros p1.
  elim p1.
    (* Done *)
    simpl.
    intro.
    exact (eq_refl _).
    (* AddThen *)
    intros n p hyp p2.
    simpl.
    rewrite (hyp p2).
    exact (eq_refl _).
    (* MulThen *)
    intros n p hyp p2.
    simpl.
    rewrite (hyp p2).
    exact (eq_refl _).
    (* SetToThen *)
    intros n p hyp p2.
    simpl.
    rewrite (hyp p2).
    exact (eq_refl _).
Qed.

(* Prove that running the concatenation of [p1] with [p2] is
   equivalent to running [p1] and then running [p2] on the
   result. *)
Theorem concatProg_run
  : forall (p1 p2 : Prog) (initState : nat),
    run (concatProg p1 p2) initState =
    run p2 (run p1 initState).
Proof.
  intros p1.
  elim p1.
    (* Done *)
    intros p2 n.
    simpl.
    exact (eq_refl _).
    (* AddThen *)
    intros n p hyp p2 m.
    simpl.
    exact (hyp p2 (m + n)).
    (* MulThen *)
    intros n p hyp p2 m.
    simpl.
    exact (hyp p2 (m * n)).
    (* SetToThen *)
    intros n p hyp p2 m.
    simpl.
    exact (hyp p2 n).
Qed.
