Require Import Frap Pset11Sig.


(* Takeaway: see the rule HtLoop of hoare_triple:
 * idea is to separate the heap in a section that no longer matters
 * (doesn't change / isn't used, and won't prevent the conclusion from staying
 *  true at the end when broadening back the scope)
 * and a section that matters to recurse on.
 *
 * Skipping this problem that looks quite time-consuming
 * (there seems to be a lot of home-made definitions)
 *)

(* Opaque mtree. *)
(* ^-- Don't forget to mark predicates opaque after you've finished proving 
 * all the key algebraic properties about them, in order for them to work
 * well with the [cancel] tactic. *)

Theorem lookup_ok : forall x p,
  {{mtreep p}}
    lookup x p
  {{_ ~> mtreep p}}.
Proof.
Admitted.

Theorem insert_ok : forall x p,
  {{mtreep p}}
    insert x p
  {{_ ~> mtreep p}}.
Proof.
Admitted.
