Require Import Frap Pset5Sig.

(* Before beginning this problem set, please see Pset5Sig.v,
 * which contains the instructions.
 *)

Fixpoint genbuf (n:nat) : list nat :=
  match n with
    | O => nil
    | S q => 1 :: (genbuf q)
  end.

Definition non_null (n:nat) := exists (n_1:nat), n = S n_1.

Definition pdcs2_inv
           (s : threaded_state (sharedWithLock pdcs_global_state)
                               (stateWithLock pd_thread * stateWithLock cs_thread)) :=
  exists (a b c: nat),
  s.(Shared).(SharedOrig).(cnt) = a /\
  s.(Shared).(SharedOrig).(buf) = genbuf b /\
  s.(Shared).(SharedOrig).(acc) = c /\
  ((
    (
      (s.(Shared).(Lock) = false /\ s.(Private) = (Alock, Alock) /\ non_null a) \/
      (s.(Shared).(Lock) = true /\ s.(Private) = (Aprivate DecCount, Alock) /\ non_null a) \/
      (s.(Shared).(Lock) = true /\ s.(Private) = (Aunlock, Alock)) \/
      (s.(Shared).(Lock) = false /\ s.(Private) = (Aprivate CheckCount, Alock)) \/
      (s.(Shared).(Lock) = true /\ s.(Private) = (Alock, Aprivate Pop) /\ non_null a) \/
      (s.(Shared).(Lock) = true /\ s.(Private) = (Alock, Aunlock) /\ non_null a) \/
      (s.(Shared).(Lock) = true /\ s.(Private) = (Aprivate CheckCount, Aprivate Pop)) \/
      (s.(Shared).(Lock) = true /\ s.(Private) = (Aprivate CheckCount, Aunlock))
    ) /\ (
      a + b + c = PRD_COUNT
    )
  ) \/ (
    (
      (s.(Shared).(Lock) = true /\ s.(Private) = (Aprivate Push, Alock)) \/
      (s.(Shared).(Lock) = true /\ s.(Private) = (Alock, Aprivate (Acc 1)) /\ non_null a) \/
      (s.(Shared).(Lock) = true /\ s.(Private) = (Aprivate CheckCount, Aprivate (Acc 1)))
    ) /\ (
      S (a + b + c) = PRD_COUNT
    )
  )).

Theorem pdcs2_ok_complete: invariantFor pdcs2_sys pdcs2_inv.
Proof.
  refine (invariant_induction pdcs2_sys pdcs2_inv _ _).
  (* Initial state *)
    intros s_init s_init_value.
    cases s_init_value.
    invert H.
    invert H0.
    refine (ex_intro _ PRD_COUNT (ex_intro _ O (ex_intro _ O _))).
    refine (conj _ (conj _ (conj _ _))).
    equality.
    equality.
    equality.
    refine (or_introl (conj (or_intror (or_intror (or_intror (or_introl (conj _ _))))) _)).
    equality.
    equality.
    equality.
  (* Induction *)
    intros s1 s1_inv s2 s2_transition.
    destruct s1_inv as [ a s1_inv ].
    destruct s1_inv as [ b s1_inv ].
    destruct s1_inv as [ c s1_inv ].
    destruct s1_inv as [ cnt_a s1_inv ].
    destruct s1_inv as [ cnt_b s1_inv ].
    destruct s1_inv as [ cnt_c s1_inv ].
    cases s1_inv.
      destruct H as [ H sum_abc ].
      cases H.
    (* Alock, Alock *)
        destruct H as [ main_lock rest ].
        destruct rest as [ state a_neq_0 ].
        cases s2_transition.
        (* AstepN1 *)
          discriminate state.
        (* AstepN2 *)
          discriminate state.
        (* AstepLock1 *)
          refine (ex_intro _ a (ex_intro _ b (ex_intro _ c (conj cnt_a (conj cnt_b (conj cnt_c _)))))).
          refine (or_introl (conj (or_intror (or_introl _)) sum_abc)).
          invert H.
          invert state.
          refine (conj _ (conj _ _)).
          equality.
          equality.
          exact a_neq_0.
        (* AstepLock2 *)
          refine (ex_intro _ a (ex_intro _ b (ex_intro _ c (conj cnt_a (conj cnt_b (conj cnt_c _)))))).
          refine (or_introl (conj (or_intror (or_intror (or_intror (or_intror (or_introl _))))) sum_abc)).
          invert H.
          invert state.
          refine (conj _ (conj _ _)).
          equality.
          equality.
          exact a_neq_0.
        (* AstepUnlock1 *)
          discriminate state.
        (* AstepUnlock2 *)
          discriminate state.
      cases H.
    (* Aprivate DecCount, Alock *)
        destruct H as [ main_lock rest ].
        destruct rest as [ state a_neq_0 ].
        cases s2_transition.
        (* AstepN1 *)
          refine (ex_intro _ (pred a) (ex_intro _ b (ex_intro _ c _))).
          invert H.
          invert state.
          refine (conj _ (conj _ (conj _ _))).
          equality.
          exact cnt_b.
          equality.
          refine (or_intror (conj (or_introl (conj main_lock _)) sum_abc)).
          invert state.
          equality.
          discriminate state.
        (* AstepN2 *)
          discriminate state.
        (* AstepLock1 *)
          discriminate state.
        (* AstepLock2 *)
          discriminate main_lock.
        (* AstepUnlock1 *)
          discriminate state.
        (* AstepUnlock2 *)
          discriminate state.
      cases H.
    (* Aunlock, Alock *)
        destruct H as [ main_lock state ].
        cases s2_transition.
        (* AstepN1 *)
          discriminate state.
        (* AstepN2 *)
          discriminate state.
        (* AstepLock1 *)
          discriminate state.
        (* AstepLock2 *)
          discriminate main_lock.
        (* AstepUnlock1 *)
          refine (ex_intro _ a (ex_intro _ b (ex_intro _ c (conj cnt_a (conj cnt_b (conj cnt_c _)))))).
          refine (or_introl (conj (or_intror (or_intror (or_intror (or_introl (conj _ _))))) sum_abc)).
          equality.
          invert H.
          invert state.
          equality.
        (* AstepUnlock2 *)
          discriminate state.
      cases H.
    (* Aprivate CheckCount, Alock *)
        destruct H as [ main_lock state ].
        cases s2_transition.
        (* AstepN1 *)
          invert state.
          invert H.
          refine (ex_intro _ (S c) (ex_intro _ b (ex_intro _ a (conj _ (conj cnt_b (conj _ _)))))).
          equality.
          equality.
          refine (or_introl (conj (or_introl (conj main_lock (conj (eq_refl _) _))) sum_abc)).
          exact (ex_intro _ c (eq_refl (S c))).
        (* AstepN2 *)
          discriminate state.
        (* AstepLock1 *)
          discriminate state.
        (* AstepLock2 *)
          invert state.
          invert H.
          refine (ex_intro _ (cnt sh) (ex_intro _ b (ex_intro _ (acc sh) (conj _ (conj cnt_b (conj _ _)))))).
          equality.
          equality.
          refine (or_introl (conj (or_intror (or_intror (or_intror (or_intror (or_intror
              (or_intror (or_introl (conj _ _)))))))) sum_abc)).
          equality.
          equality.
        (* AstepUnlock1 *)
          discriminate state.
        (* AstepUnlock2 *)
          discriminate state.
      cases H.
    (* Alock, Aprivate Pop *)
        destruct H as [ main_lock rest ].
        destruct rest as [ state a_neq_0 ].
        cases s2_transition.
        (* AstepN1 *)
          discriminate state.
        (* AstepN2 *)
          invert state.
          invert H.
          cases b.
          discriminate cnt_b.
          refine (ex_intro _ c (ex_intro _ b (ex_intro _ a (conj _ (conj _ (conj _ _)))))).
          equality.
          simpl.
          simpl in cnt_b.
          exact (f_equal (fun (l:list nat) => tl l) cnt_b).
          equality.
          refine (or_intror (conj (or_intror (or_introl (conj main_lock (conj _ a_neq_0)))) _)).
          simpl in cnt_b.
          simpl.
          exact (f_equal (fun (l:list nat) => (Alock, Aprivate (Acc (hd 1 l)))) cnt_b).
          simpl in sum_abc.
          rewrite <- (plus_Sn_m (c + b) a).
          rewrite (plus_n_Sm c b).
          exact sum_abc.
        (* AstepLock1 *)
          discriminate main_lock.
        (* AstepLock2 *)
          discriminate state.
        (* AstepUnlock1 *)
          discriminate state.
        (* AstepUnlock2 *)
          discriminate state.
      cases H.
    (* Alock, Aunlock *)
        destruct H as [ main_lock rest ].
        destruct rest as [ state a_neq_0 ].
        cases s2_transition.
        (* AstepN1 *)
          discriminate state.
        (* AstepN2 *)
          discriminate state.
        (* AstepLock1 *)
          discriminate main_lock.
        (* AstepLock2 *)
          discriminate state.
        (* AstepUnlock1 *)
          discriminate state.
        (* AstepUnlock2 *)
          invert state.
          invert H.
          refine (ex_intro _ (cnt sh) (ex_intro _ b (ex_intro _ (acc sh) (conj _ (conj cnt_b (conj _ _)))))).
          equality.
          equality.
          refine (or_introl (conj (or_introl (conj _ (conj _ a_neq_0))) sum_abc)).
          equality.
          equality.
      cases H.
    (* Aprivate CheckCount, Aprivate Pop *)
        destruct H as [ main_lock state ].
        cases s2_transition.
        (* AstepN1 *)
          invert state.
          invert H.
          refine (ex_intro _ (S c) (ex_intro _ b (ex_intro _ a (conj _ (conj cnt_b (conj _ _)))))).
          equality.
          equality.
          refine (or_introl (conj (or_intror (or_intror (or_intror (or_intror (or_introl
              (conj main_lock (conj (eq_refl _) _))))))) sum_abc)).
          exact (ex_intro _ c (eq_refl (S c))).
        (* AstepN2 *)
          invert state.
          invert H.
          cases b.
          discriminate cnt_b.
          refine (ex_intro _ c (ex_intro _ b (ex_intro _ a (conj _ (conj _ (conj _ _)))))).
          equality.
          simpl.
          simpl in cnt_b.
          exact (f_equal (fun (l:list nat) => tl l) cnt_b).
          equality.
          refine (or_intror (conj (or_intror (or_intror (conj main_lock _))) _)).
          simpl in cnt_b.
          simpl.
          exact (f_equal (fun (l:list nat) => (Aprivate CheckCount, Aprivate (Acc (hd 1 l)))) cnt_b).
          simpl in sum_abc.
          rewrite <- (plus_Sn_m (c + b) a).
          rewrite (plus_n_Sm c b).
          exact sum_abc.
        (* AstepLock1 *)
          discriminate state.
        (* AstepLock2 *)
          discriminate state.
        (* AstepUnlock1 *)
          discriminate state.
        (* AstepUnlock2 *)
          discriminate state.
    (* Aprivate CheckCount, Aunlock *)
        destruct H as [ main_lock state ].
        cases s2_transition.
        (* AstepN1 *)
          invert state.
          invert H.
          refine (ex_intro _ (S c) (ex_intro _ b (ex_intro _ a (conj _ (conj cnt_b (conj _ _)))))).
          equality.
          equality.
          refine (or_introl (conj (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl
              (conj main_lock (conj (eq_refl _) _)))))))) sum_abc)).
          exact (ex_intro _ c (eq_refl (S c))).
        (* AstepN2 *)
          discriminate state.
        (* AstepLock1 *)
          discriminate state.
        (* AstepLock2 *)
          discriminate state.
        (* AstepUnlock1 *)
          discriminate state.
        (* AstepUnlock2 *)
          invert state.
          invert H.
          refine (ex_intro _ (cnt sh) (ex_intro _ b (ex_intro _ (acc sh) (conj _ (conj cnt_b (conj _ _)))))).
          equality.
          equality.
          refine (or_introl (conj (or_intror (or_intror (or_intror (or_introl (conj _ _))))) sum_abc)).
          equality.
          equality.
      destruct H as [ H sum_abc ].
      cases H.
    (* Aprivate Push, Alock *)
        destruct H as [ main_lock state ].
        cases s2_transition.
        (* AstepN1 *)
          invert state.
          invert H.
          refine (ex_intro _ c (ex_intro _ (S b) (ex_intro _ a (conj _ (conj _ (conj _ _)))))).
          equality.
          simpl.
          rewrite <- cnt_b.
          equality.
          equality.
          refine (or_introl (conj (or_intror (or_intror (or_introl (conj main_lock (eq_refl _))))) _)).
          simpl in sum_abc.
          rewrite <- (plus_Sn_m (c + b) a) in sum_abc.
          rewrite (plus_n_Sm c b) in sum_abc.
          exact sum_abc.
        (* AstepN2 *)
          discriminate state.
        (* AstepLock1 *)
          discriminate state.
        (* AstepLock2 *)
          discriminate main_lock.
        (* AstepUnlock1 *)
          discriminate state.
        (* AstepUnlock2 *)
          discriminate state.
      cases H.
    (* Alock, Aprivate (Acc 1) *)
        destruct H as [ main_lock rest ].
        destruct rest as [ state a_neq_0 ].
        cases s2_transition.
        (* AstepN1 *)
          discriminate state.
        (* AstepN2 *)
          invert state.
          invert H.
          refine (ex_intro _ c (ex_intro _ b (ex_intro _ (S a) (conj _ (conj cnt_b (conj _ _)))))).
          equality.
          rewrite (plus_comm a 1).
          equality.
          refine (or_introl (conj (or_intror (or_intror (or_intror (or_intror (or_intror
              (or_introl (conj main_lock (conj (eq_refl _) a_neq_0)))))))) _)).
          simpl in sum_abc.
          rewrite (plus_n_Sm (c + b) a) in sum_abc.
          exact sum_abc.
        (* AstepLock1 *)
          discriminate main_lock.
        (* AstepLock2 *)
          discriminate state.
        (* AstepUnlock1 *)
          discriminate state.
        (* AstepUnlock2 *)
          discriminate state.
    (* Aprivate CheckCount, Aprivate (Acc 1) *)
        destruct H as [ main_lock state ].
        cases s2_transition.
        (* AstepN1 *)
          invert state.
          invert H.
          refine (ex_intro _ (S c) (ex_intro _ b (ex_intro _ a (conj _ (conj cnt_b (conj _ _)))))).
          equality.
          equality.
          refine (or_intror (conj (or_intror (or_introl (conj main_lock (conj (eq_refl _) _)))) sum_abc)).
          exact (ex_intro _ c (eq_refl _)).
        (* AstepN2 *)
          invert state.
          invert H.
          refine (ex_intro _ c (ex_intro _ b (ex_intro _ (S a) (conj _ (conj cnt_b (conj _ _)))))).
          equality.
          rewrite (plus_comm a 1).
          equality.
          refine (or_introl (conj (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror
              (or_intror (conj main_lock (eq_refl _))))))))) _)).
          simpl in sum_abc.
          rewrite (plus_n_Sm (c + b) a) in sum_abc.
          exact sum_abc.
        (* AstepLock1 *)
          discriminate state.
        (* AstepLock2 *)
          discriminate state.
        (* AstepUnlock1 *)
          discriminate state.
        (* AstepUnlock2 *)
          discriminate state.
Qed.

Theorem pdcs2_ok : invariantFor pdcs2_sys pdcs2_correct.
Proof.
  refine (invariant_weaken pdcs2_correct pdcs2_ok_complete _).
  intros s H cnt_eq_0 buf_nil no_lock.
  destruct H as [a H].
  destruct H as [b H].
  destruct H as [c H].
  destruct H as [cnt_a H].
  destruct H as [cnt_b H].
  destruct H as [cnt_c H].
  cases H.
  (* We have the equality *)
    destruct H as [H sum_abc].
    rewrite cnt_c.
    rewrite cnt_a in cnt_eq_0.
    rewrite cnt_eq_0 in sum_abc.
    rewrite cnt_b in buf_nil.
    cases b.
    exact sum_abc.
    discriminate buf_nil.
  (* We do not have the equality, but the lock is taken *)
    destruct H as [H sum_abc].
    cases H.
    rewrite (proj1 H) in no_lock.
    discriminate no_lock.
    cases H.
    rewrite (proj1 H) in no_lock.
    discriminate no_lock.
    rewrite (proj1 H) in no_lock.
    discriminate no_lock.
Qed.
