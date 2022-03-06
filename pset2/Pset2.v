(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 2 *)

Require Import Frap Pset2Sig.

(* If we [either] an [option] value with [None]
 * on the right, it leaves that value unchanged,
 * (just as if we put the [None] on the left).
 * This is analogous to how appending [nil]
 * on either side of a list leaves it unchanged.
 *)
Theorem either_None_right : forall {A} (xo : option A),
    either xo None = xo.
Proof.
  intros A xo; destruct xo; reflexivity.
Qed.

(* [either] is associative, just like [++].
 *)
Theorem either_assoc : forall {A} (xo yo zo : option A),
    either (either xo yo) zo = either xo (either yo zo).
Proof.
  intros A xo yo zo; destruct xo, yo, zo; reflexivity.
Qed.

(* [head] should compute the head of a list, that is,
 * it should return [Some] with the first element of
 * the list if the list is nonempty, and [None]
 * if the list is empty.
 *)
Fixpoint head {A} (xs : list A) : option A := match xs with
  | nil => None
  | a::_ => Some a
  end.

Example head_example : head [1; 2; 3] = Some 1.
Proof.
  reflexivity.
Qed.

(* The following theorem makes a formal connection
 * between [either] and [++].
 *)
Theorem either_app_head : forall {A} (xs ys : list A),
    head (xs ++ ys) = either (head xs) (head ys).
Proof.
  destruct xs; reflexivity.
Qed.

(* [leftmost_Node] should compute the leftmost node of
 * a tree. 
 *
 * Please implement [leftmost_Node] directly using
 * recursion (i.e., pattern matching) on the [tree] argument,
 * without using the [flatten] operation.
 *)
Fixpoint leftmost_Node {A} (t : tree A) : option A := match t with
  | Leaf => None
  | Node Leaf d _ => Some d
  | Node l _ _ => leftmost_Node l
  end.

Example leftmost_Node_example :
    leftmost_Node (Node (Node Leaf 2 (Node Leaf 3 Leaf)) 1 Leaf)
    = Some 2.
Proof.
  reflexivity.
Qed.

(* Prove that the leftmost node of the tree is the same
 * as the head of the list produced by flattening the tree
 * with an in-order traversal.
 *)
Lemma flattened_node_has_element {A} : forall (l r: tree A) (d:A),
    exists (v:A) (q:list A), flatten (Node l d r) = v::q.
Proof.
  intro l; elim l.
  (* l=Leaf *)
    intros r d; exists d, (flatten r); reflexivity.
  (* l=Node ll lr ld *)
    intros ll recl ld lr recr r d; elim (recl lr ld); clear recl.
    intros v recl; elim recl; clear recl; intros q recl.
    replace (flatten (Node (Node ll ld lr) d r)) with (flatten (Node ll ld lr)++d::flatten r) by reflexivity.
    rewrite recl; exists v, (q ++ (d::(flatten r))); reflexivity.
Qed.
Theorem leftmost_Node_head : forall {A} (t : tree A),
      leftmost_Node t = head (flatten t).
Proof.
  intros A t; elim t; clear t; [ reflexivity |].
  intros l rec d r H; destruct l; [ reflexivity |].
  replace (leftmost_Node (Node (Node l1 d0 l2) d r)) with (leftmost_Node (Node l1 d0 l2)) by reflexivity.
  rewrite rec; clear rec.
  replace (flatten (Node (Node l1 d0 l2) d r)) with (flatten (Node l1 d0 l2)++d::flatten r) by reflexivity.
  elim (flattened_node_has_element l1 l2 d0); intros v tmp; elim tmp; clear tmp; intros q rep.
  rewrite rep; reflexivity.
Qed.

(* Now let's work with the binary tries we defined earlier!
 *
 * Define [lookup] such that [lookup k t] looks up the
 * map entry corresponding to the key [k : list bool] in the
 * binary trie [t : binary_trie A], interpreting [t] such that
 * the value at the root of [t] corresponds to the 
 * entry for the key [nil], the left subtree contains entries 
 * for those keys that begin with [true], and the right subtree
 * contains entries for those keys that begin with [false].
 *)
Fixpoint lookup {A} (k : list bool) (t : binary_trie A) : option A := match k, t with
  | nil, Node _ d _ => d
  | _, Leaf => None
  | true::q, Node l _ _ => lookup q l
  | false::q, Node _ _ r => lookup q r
  end.

Example lookup_example1 : lookup [] (Node Leaf (None : option nat) Leaf) = None.
Proof.
  reflexivity.
Qed.

Example lookup_example2 : lookup [false; true]
    (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf))
                          = Some 1.
Proof.
  reflexivity.
Qed.

(* [Leaf] represents an empty binary trie, so a lookup for
 * any key should return [None].
 *)
Theorem lookup_empty {A} (k : list bool)
  : lookup k (Leaf : binary_trie A) = None.
Proof.
  destruct k; [| destruct b ]; reflexivity.
Qed.

(* Define an operation to "insert" a key and optional value
 * into a binary trie. The [insert] definition should satisfy two
 * properties: one is [lookup_insert] below, which says that if we
 * look up a key [k] in a trie where [(k, v)] has just been inserted,
 * the result should be [v]. The other is that lookups on keys different
 * from the one just inserted should be the same as on the original map.
 *
 * If an entry for that key already exists, [insert] should replace
 * that entry with the new one being inserted. Note that [insert] can
 * be used to remove an entry from the trie, too, by inserting [None] 
 * as the value.
 *
 * Hint: it may be helpful to define an auxiliary function that inserts
 * a key and optional value into the empty trie.
 *)
Fixpoint insert {A} (k : list bool) (v : option A) (t : binary_trie A) : binary_trie A :=
    match k, t with
    | nil,Leaf => Node Leaf v Leaf
    | nil, Node l _ r => Node l v r
    | true::q, Leaf => Node (insert q v Leaf) None Leaf
    | true::q, Node l d r => Node (insert q v l) d r
    | false::q, Leaf => Node Leaf None (insert q v Leaf)
    | false::q, Node l d r => Node l d (insert q v r)
    end.

Example insert_example1 : lookup [] (insert [] None (Node Leaf (Some 0) Leaf)) = None.
Proof eq_refl _.

Example insert_example2 : lookup [] (insert [true] (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.
Proof eq_refl _.

Theorem lookup_insert {A} : forall (k : list bool) (v : option A) (t : binary_trie A),
    lookup k (insert k v t) = v.
Proof.
  intro k; elim k; clear k; [ destruct t; reflexivity |]; intros a q rec v t.
  destruct t.
  (* Leaf *)
    destruct a; exact (rec v Leaf).
  (* Node t1 d t2 *)
    destruct a; [ exact (rec v t1) | exact (rec v t2) ].
Qed.


(* You've reached the end of the problem set. Congrats!
 *
 * If you're up for a completely optional additional challenge,
 * try defining a left-biased merge function below that merges two
 * binary tries, preferring map entries from the first binary trie
 * when an entry exists for both binary tries. Then prove
 * [lookup_left_biased_merge], which formally states that lookups
 * on the merged binary trie operate in exactly this manner.
 *
 * If you don't want to complete this additional challenge, you
 * can just leave everything below unmodified.
 *)

Fixpoint left_biased_merge {A} (t t' : binary_trie A) : binary_trie A :=
  match (t, t') with
    | (Leaf, Leaf) => Leaf
    | (Node l d r, Leaf) => Node l d r
    | (Leaf, Node l d r) => Node l d r
    | (Node l d r, Node l' d' r') =>
        Node (left_biased_merge l l') (either d d') (left_biased_merge r r')
  end.

Theorem lookup_left_biased_merge {A} (k : list bool)
  : forall (t t' : binary_trie A),
    lookup k (left_biased_merge t t') = either (lookup k t) (lookup k t').
Proof.
  elim k.
    (* nil *)
    intros t t'.
    case t.
      (* Leaf *)
      case t'.
        reflexivity.
        reflexivity.
      (* Node l d r *)
      intros l d r.
      case t'.
        (* Leaf *)
        case d.
          reflexivity.
          reflexivity.
        (* Node l' d' r' *)
        intros l' d' r'.
        case d, d'.
          reflexivity.
          reflexivity.
          reflexivity.
          reflexivity.
    (* a::q *)
    intros a q hyp1 t t'.
    case t, t'.
      (* Leaf, Leaf *)
      case a.
        reflexivity.
        reflexivity.
      (* Leaf, Node ... *)
      case a, d.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
      (* Node ..., Leaf *)
      assert (forall (x: option A), x = either x None) as subgoal.
        intros x.
        case x.
          reflexivity.
          reflexivity.
      case a, d.
        (* true, Some a *)
        simpl.
        exact (subgoal (lookup q t1)).
        (* true, None *)
        simpl.
        exact (subgoal (lookup q t1)).
        (* false, Some a *)
        simpl.
        exact (subgoal (lookup q t2)).
        (* false, None *)
        simpl.
        exact (subgoal (lookup q t2)).
      (* Node ..., Node ... *)
      case a.
        (* true *)
        simpl.
        exact (hyp1 t1 t'1).
        (* false *)
        simpl.
        exact (hyp1 t2 t'2).
Qed.

