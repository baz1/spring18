Require Import Frap Pset4Sig.

Require Import OrdersFacts.

(* Before beginning this problem set, please see Pset4Sig.v,
 * which contains the instructions.
 *)

Lemma rightmost_node: forall d l r, exists a, rightmost (Node d l r) = Some a.
Proof.
  intros d l r.
  elim r.
    (* Leaf *)
    simpl.
    exact (ex_intro (fun a => Some d = Some a) d (eq_refl (Some d))).
    (* Node *)
    intros d' l' hypl r' hypr.
    simpl.
    cases r'.
      (* Leaf *)
      exact (ex_intro (fun a => Some d' = Some a) d' (eq_refl (Some d'))).
      (* Node *)
      exact hypr.
Qed.

Lemma rightmost_forall: forall P t a, rightmost t = Some a -> tree_forall P t -> P a.
Proof.
  intros P t.
  elim t.
    (* Leaf *)
    simpl.
    discriminate.
    (* Node d l r *)
    intros d l hypl r hypr a rma hypall.
    simpl in hypall, rma.
    cases r.
      (* Leaf *)
      invert rma.
      exact (proj1 hypall).
      (* Node *)
      exact (hypr a rma (proj2 (proj2 hypall))).
Qed.

Lemma tree_forall_fortiori:
  forall (P Q:t->Prop) t, (forall a, P a -> Q a) -> tree_forall P t -> tree_forall Q t.
Proof.
  intros P Q t hyp.
  elim t.
    (* Leaf *)
    intros _.
    exact I.
    (* Node d l r *)
    simpl.
    intros d l hypl r hypr allP.
    exact (conj (hyp d (proj1 allP)) (conj (hypl (proj1 (proj2 allP))) (hypr (proj2 (proj2 allP))))).
Qed.


(* For your convenience, we beforehand provide some useful facts about orders.
 * You can skim through the list of theorems by using "Print," or visiting 
 * this page:
 * https://coq.inria.fr/library/Coq.Structures.OrdersFacts.html
 *)
Include (OrderedTypeFacts Pset4Sig).
Include (OrderedTypeTest Pset4Sig).

(* Our solution only needs (at most) the following facts from the above libraries.
 * But it is certainly okay if you use facts beyond these! 
 *)
Check eq_lt.
Check eq_sym.
Check lt_eq.
Check lt_not_eq.
Check lt_trans.
Check compare_refl.
Check compare_lt_iff. (* Note that this one can be used with [apply], despite the fact that it
                       * includes an "if and only if" ([<->]) where other theorems use simple
                       * implication ([->]). *)
Check compare_gt_iff.
Check compare_eq_iff.

Lemma bst_lt : forall d lt rt, BST (Node d lt rt) -> BST lt.
Proof.
  intros lt rt d bst.
  apply bst.
Qed.

Lemma bst_rt : forall d lt rt, BST (Node d lt rt) -> BST rt.
Proof.
  intros lt rt d bst.
  apply bst.
Qed.

Theorem insert_member: forall t n, BST t -> member n (insert n t) = true.
Proof.
  intros t.
  elim t.
    (* Leaf *)
    simpl.
    intros n.
    rewrite (compare_refl n).
    reflexivity.
    (* Node d l r *)
    intros d l hypl r hypr n bst.
    simpl.
    cases compare.
      (* Eq *)
      simpl.
      rewrite Heq.
      reflexivity.
      (* Lt *)
      simpl.
      rewrite Heq.
      exact (hypl n (bst_lt d l r bst)).
      (* Rt *)
      simpl.
      rewrite Heq.
      exact (hypr n (bst_rt d l r bst)).
Qed.

Lemma tree_forall_insert: forall t P n, tree_forall P t -> P n -> tree_forall P (insert n t).
Proof.
  intros t P n.
  elim t.
    (* Leaf *)
    simpl.
    intros _ Pn.
    exact (conj Pn (conj I I)).
    (* Node d l r *)
    intros d l hypl r hypr hypall Pn.
    assert (P d) as Pd.
      apply hypall.
    assert (tree_forall P l) as tfl.
      apply hypall.
    assert (tree_forall P r) as tfr.
      apply hypall.
    simpl.
    case compare.
      (* Eq *)
      exact hypall.
      (* Lt *)
      simpl.
      exact (conj Pd (conj (hypl tfl Pn) tfr)).
      (* Gt *)
      simpl.
      exact (conj Pd (conj tfl (hypr tfr Pn))).
Qed.

Theorem insert_ok: forall t n, BST t -> BST (insert n t).
Proof.
  intros t n.
  elim t.
    (* Leaf *)
    simpl.
    unfold tree_lt, tree_gt.
    simpl.
    auto.
    (* Node d l r *)
    intros d l hypl r hypr bst.
    assert (tree_lt d l) as ltl.
      apply bst.
    assert (tree_gt d r) as gtr.
      apply bst.
    simpl.
    cases compare.
      (* Eq *)
      exact bst.
      (* Lt *)
      simpl.
      refine (conj (hypl (bst_lt d l r bst)) _).
      refine (conj (tree_forall_insert l (fun v => lt v d) n ltl (proj1 (compare_lt_iff n d) Heq)) _).
      exact (conj (bst_rt d l r bst) gtr).
      (* Gt *)
      simpl.
      refine (conj (bst_lt d l r bst) (conj ltl _)).
      refine (conj (hypr (bst_rt d l r bst)) _).
      exact (tree_forall_insert r (fun v => lt d v) n gtr (proj1 (compare_gt_iff n d) Heq)).
Qed.



Lemma rightmost_biggest: forall t a,
  BST t -> rightmost t = Some a -> tree_forall (fun v => lt v a \/ eq v a) t.
Proof.
  intros t.
  elim t.
    (* Leaf *)
    intros a _ _.
    exact I.
    (* Node d l r *)
    intros d l hypl r hypr a bst rm.
    simpl in rm.
    unfold tree_lt.
    simpl.
    cases r.
      (* Leaf *)
      invert rm.
      refine (conj (or_intror (eq_refl a)) (conj _ _)).
        cases l.
          (* Leaf *)
          exact I.
          (* Node d l1 l2 *)
          pose (extract_rm := rightmost_node d l1 l2).
          cases extract_rm.
          pose (hypl' := hypl x (proj1 bst) H).
          refine (tree_forall_fortiori
              (fun v : Pset4Sig.t => lt v x \/ eq v x)
              (fun v : Pset4Sig.t => lt v a \/ eq v a)
              (Node d l1 l2) _ hypl').
          assert (lt x a) as subgoal.
            assert (tree_forall (fun v => lt v a) (Node d l1 l2)) as lla.
              apply bst.
            exact (rightmost_forall (fun v => lt v a) (Node d l1 l2) x H lla).
          intros a0 lthyp.
          refine (or_introl _).
          cases lthyp.
            (* lt *)
            exact (lt_trans H0 subgoal).
            (* eq *)
            exact (eq_lt H0 subgoal).
        exact I.
      (* Node d0 r1 r2 *)
      assert (tree_forall (fun v => lt d v) (Node d0 r1 r2)) as rgtd.
        apply bst.
      pose (dlta := rightmost_forall (fun v => lt d v) (Node d0 r1 r2) a rm rgtd).
      refine (conj (or_introl dlta) (conj _ (hypr a (proj1 (proj2 (proj2 bst))) rm))).
      cases l.
        (* Leaf *)
        exact I.
        (* Node d1 l1 l2 *)
        pose (extract_rml := rightmost_node d1 l1 l2).
        cases extract_rml.
        pose (hypl' := hypl x (proj1 bst) H).
        refine (tree_forall_fortiori
            (fun v : Pset4Sig.t => lt v x \/ eq v x)
            (fun v : Pset4Sig.t => lt v a \/ eq v a)
            (Node d1 l1 l2) _ hypl').
        assert (lt x d) as xltd.
          assert (tree_forall (fun v => lt v d) (Node d1 l1 l2)) as lld.
            apply bst.
          exact (rightmost_forall (fun v => lt v d) (Node d1 l1 l2) x H lld).
        pose (xlta := lt_trans xltd dlta).
        intros a0 lthyp.
        refine (or_introl _).
        cases lthyp.
          (* lt *)
          exact (lt_trans H0 xlta).
          (* eq *)
          exact (eq_lt H0 xlta).
Qed.

Lemma delrm_forall: forall t P, tree_forall P t -> tree_forall P (delete_rightmost t).
Proof.
  intros t P.
  elim t.
    (* Leaf *)
    intros _.
    exact I.
    (* Node d l r *)
    intros d l hypl r hypr hypall.
    simpl.
    cases r.
      (* Leaf *)
      apply hypall.
      (* Node d0 r1 r2 *)
      refine (_ (hypr _)).
      intros mhyp.
      refine (conj _ (conj _ _)).
      apply hypall.
      apply hypall.
      apply mhyp.
      apply hypall.
Qed.


Lemma del_forall: forall t a P, tree_forall P t -> tree_forall P (delete a t).
Proof.
  intros t a P.
  elim t.
    (* Leaf *)
    intros _.
    exact I.
    (* Node d l r *)
    intros d l hypl r hypr hypall.
    simpl.
    cases (compare a d).
      (* Eq *)
      cases (rightmost l).
        (* Some t0 *)
        simpl.
        refine (conj _ (conj (delrm_forall l P _) _)).
        exact (rightmost_forall P l t0 Heq0 (proj1 (proj2 hypall))).
        apply hypall.
        apply hypall.
        (* None *)
        apply hypall.
      (* Lt *)
      simpl.
      refine (conj _ (conj (hypl _) _)).
      apply hypall.
      apply hypall.
      apply hypall.
      (* Gt *)
      simpl.
      refine (conj _ (conj _ (hypr _))).
      apply hypall.
      apply hypall.
      apply hypall.
Qed.

Theorem delete_rightmost_ok: forall t, BST t -> BST (delete_rightmost t).
Proof.
  intros t.
  elim t.
    (* Leaf *)
    intros _.
    exact I.
    (* Node d l r *)
    intros d l hypl r hypr bst.
    simpl.
    cases r.
      (* Leaf *)
      apply bst.
      (* Node d0 r1 r2 *)
      simpl.
      refine (conj (proj1 bst) (conj (proj1 (proj2 bst)) (conj (hypr _) _))).
      apply bst.
      refine (delrm_forall (Node d0 r1 r2) (fun v => lt d v) _).
      apply bst.
Qed.

Lemma rightmost_biggest2: forall t a,
  BST t -> rightmost t = Some a -> tree_lt a (delete_rightmost t).
Proof.
  intros t.
  elim t.
    (* Leaf *)
    intros a _ _.
    exact I.
    (* Node d l r *)
    intros d l hypl r hypr a bst rma.
    simpl.
    cases r.
      (* Leaf *)
      simpl in rma.
      invert rma.
      apply bst.
      (* Node d0 r1 r2 *)
      unfold tree_lt.
      simpl.
      assert (rightmost (Node d0 r1 r2) = Some a) as rma2.
        exact rma.
      assert (lt d a) as dlta.
      refine (rightmost_forall (fun v => lt d v) (Node d0 r1 r2) a rma2 _).
      apply bst.
      refine (conj dlta (conj _ (hypr a _ rma2))).
      refine (tree_forall_fortiori (fun v => lt v d) (fun v => lt v a) l _ (proj1 (proj2 bst))).
      intros a0 a0ltd.
      exact (lt_trans a0ltd dlta).
      apply bst.
Qed.

Theorem delete_ok: forall t n, BST t -> BST (delete n t).
Proof.
  intros t n.
  elim t.
    (* Leaf *)
    intros _.
    exact I.
    (* Node d l r *)
    intros d l hypl r hypr bst.
    simpl.
    cases (compare n d).
      (* Eq *)
      cases (rightmost l).
        (* Some t0 *)
        simpl.
        refine (conj (delete_rightmost_ok l (proj1 bst))
            (conj (rightmost_biggest2 l t0 (proj1 bst) Heq0) (conj _ _))).
        apply bst.
        refine (tree_forall_fortiori (fun v => lt d v) (fun v => lt t0 v) r _ _).
        (* use the fact that lt t0 d from bst and t0 in l *)
        assert (lt t0 d) as t0ltd.
          refine (rightmost_forall (fun v => lt v d) l t0 Heq0 _).
          apply bst.
        intros a dlta.
        exact (lt_trans t0ltd dlta).
        apply bst.
        (* None *)
        apply bst.
      (* Lt *)
      simpl.
      refine (conj (hypl (proj1 bst)) (conj _ (conj _ _))).
      refine (del_forall l n (fun v => lt v d) _).
      apply bst.
      apply bst.
      apply bst.
      (* Gt *)
      simpl.
      refine (conj (proj1 bst) (conj (proj1 (proj2 bst)) (conj (hypr _) _))).
      apply bst.
      refine (del_forall r n (fun v => lt d v) _).
      apply bst.
Qed.

(* OPTIONAL PART! *)

Lemma no_member: forall t a, BST t -> tree_forall (fun v => ~ eq v a) t -> member a t = false.
Proof.
  intros t a.
  elim t.
    (* Leaf *)
    intros _ _.
    reflexivity.
    (* Node d l r *)
    intros d l hypl r hypr bst hypall.
    simpl.
    destruct hypall as [notind tmp].
    destruct tmp as [notinl notinr].
    cases (compare a d).
      (* Eq *)
      cases (notind (eq_sym (proj1 (compare_eq_iff a d) Heq))).
      (* Lt *)
      refine (hypl (proj1 bst) notinl).
      (* Gt *)
      refine (hypr _ notinr).
      apply bst.
Qed.

Theorem delete_member: forall t n, BST t -> member n (delete n t) = false.
Proof.
  intros t n.
  elim t.
    (* Leaf *)
    intros _.
    reflexivity.
    (* Node d l r *)
    intros d l hypl r hypr bst.
    simpl.
    cases (compare n d).
      (* Eq *)
      pose (n_eq_d := (proj1 (compare_eq_iff n d)) Heq).
      assert (member n r = false) as subgoal.
        refine (no_member r n _ _).
        apply bst.
        refine (tree_forall_fortiori (fun v => lt d v) (fun v => ~ eq v n) r _ _).
        intros a d_lt_a a_eq_n.
        cases (lt_not_eq (eq_lt n_eq_d d_lt_a) (eq_sym a_eq_n)).
        apply bst.
      cases (rightmost l).
        (* Some t0 *)
        assert (lt t0 d) as t0_lt_d.
          exact (rightmost_forall (fun v => lt v d) l t0 Heq0 (proj1 (proj2 bst))).
        assert (compare n t0 = Gt) as right_branch.
          refine (proj2 (compare_gt_iff n t0) _).
          exact (lt_eq t0_lt_d (eq_sym n_eq_d)).
        simpl.
        rewrite right_branch.
        exact subgoal.
        (* None *)
        exact subgoal.
      (* Lt *)
      simpl.
      rewrite Heq.
      exact (hypl (proj1 bst)).
      (* Gt *)
      simpl.
      rewrite Heq.
      refine (hypr _).
      apply bst.
Qed.
