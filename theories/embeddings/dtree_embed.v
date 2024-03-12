(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Utf8.

From KruskalTrees
  Require Import idx vec dtree.

Require Import base notations tactics.

Import idx_notations vec_notations dtree_notations.

Set Implicit Arguments.

#[local] Reserved Notation "s '≤st' t" (at level 70, no associativity, format "s  ≤st  t").

Section sub_dtree.

  Variable (X : nat → Type).

  Inductive sub_dtree : dtree X → dtree X → Prop :=
    | sub_dtree_refl t : t ≤st t
    | sub_dtree_sub s n i x (v : vec _ n) : s ≤st v⦃i⦄ → s ≤st ⟨x|v⟩
  where "s ≤st t" := (sub_dtree s t).

  Hint Constructors sub_dtree : core.

  Fact sub_dtree_fall P s t : s ≤st t → dtree_fall P t → dtree_fall P s.
  Proof.
    induction 1; auto.
    rewrite dtree_fall_fix; intros []; eauto.
  Qed.

  Fact sub_dtree_inv s t :
         s ≤st t → s = t ∨ match t with ⟨_|v⟩ => ∃i, s ≤st v⦃i⦄ end.
  Proof. intros []; eauto. Qed.

  Fact sub_dtree_inv_rt s n x (v : vec _ n) : s ≤st ⟨x|v⟩ → s = ⟨x|v⟩ ∨ ∃i, s ≤st v⦃i⦄.
  Proof. apply sub_dtree_inv. Qed.

  Fact sub_dtree_trans r s t : r ≤st s → s ≤st t → r ≤st t.
  Proof. induction 2; eauto. Qed.

End sub_dtree.

Module dtree_embbedings_notations.

  Notation "s ≤st t" := (sub_dtree s t).

End dtree_embbedings_notations.

Create HintDb dtree_db.

#[global] Hint Constructors sub_dtree : dtree_db.
#[global] Hint Resolve sub_dtree_trans : dtree_db.

