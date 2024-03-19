(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Lia Utf8.

From KruskalTrees
  Require Import idx vec vtree.

From KruskalFinite
  Require Import finite choice.

Require Import base notations vtree_embed.

Import vec_notations vtree_notations af_notations.

Set Implicit Arguments.

Section veldman_afs_leave_full.

  Variables (A : Type) (k : nat)
            (X : nat → rel₁ A)
            (R : nat → rel₂ A)
            (HR : ∀ x y, X 0 x → X 0 y → R 0 x y)
            (α : A) (Hα : X 0 α).

  Lemma veldman_afs_leave_full : afs (wft X) (vtree_upto_embed k R)↑⟨α|∅⟩.
  Proof.
    constructor 1; intros t y Ht Hy.
    right; clear y Hy.
    induction Ht as [ [ | n ] x v H1 H2 IH2 ] using wft_rect.
    + clear H2 IH2; vec invert v.
      (* k = 0 ~> product embedding vec_fall2
         0 < k ~> homeo embedding vec_embed *)
      destruct k as [ | k' ]. 
      * auto with vec_db vtree_db.
      * constructor 2; auto with vec_db; lia.
    + (* pick up any sub-tree, eg the first one *)
      constructor 1 with idx_fst; auto.
  Qed.

End veldman_afs_leave_full.

Section veldman_afs_leaves_lift.

  Variables (A : Type) (k : nat)
            (X : nat → rel₁ A)
            (R : nat → rel₂ A)
            (α : A) (Ha : X 0 α).

  (* If either k or n is zero then (R 0)↑α else R n *)
  Let R' n :=
    match n with
    | 0 => (R 0)↑α
    | _ =>
      match k with
      | 0 => (R 0)↑α
      | _ => R n
      end
    end.

  Hypotheses (HR' : afs (wft X) (vtree_upto_embed k R')).

  Lemma veldman_afs_leaves_lift : afs (wft X) (vtree_upto_embed k R)↑⟨α|∅⟩.
  Proof.
    revert HR'; apply afs_mono; auto.
    intros x y _ _.
    induction 1 as [ i b v t p _ IH1
                   | i b v c w H0 H1 _ IH2
                   | i b v j c w H0 H1 _ IH2 ].
    + destruct IH1.
      * left; constructor 1 with p; auto.
      * right; auto.
    + destruct i as [ | i ].
      * destruct H1; [ left | right ]; constructor; auto with vec_db.
      * apply finite_choice in IH2 as [ IH2 | (p & Hp) ]; fin auto.
        - left; constructor 2; auto.
          simpl in H1; destruct k; auto; lia.
        - right; eauto with vtree_db.
    + destruct i as [ | i ].
      * vec invert v.
        replace k with 0 in * by lia.
        destruct H1; [ left | right ]; auto with vec_db vtree_db.
      * destruct k as [ | k' ]; simpl in H1.
        - apply vec_embed_rel_lift_inv in IH2.
          destruct H1; destruct IH2 as [ | [] ];
            ( (left; eauto with vec_db vtree_db; fail) || (right; eauto with vec_db vtree_db)).
        - apply vec_embed_rel_lift_inv in IH2 as [ | [] ];
            ( (left; eauto with vtree_db; fail) || (right; eauto with vtree_db)).
  Qed.

End veldman_afs_leaves_lift.
