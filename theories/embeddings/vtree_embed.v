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
  Require Import idx vec vtree.

Require Import base notations tactics.
Require Export dtree_embed.

Import idx_notations vec_notations vtree_notations.

Set Implicit Arguments.

#[local] Reserved Notation "s '≤st' t" (at level 70, no associativity, format "s  ≤st  t").
#[local] Reserved Notation "l '≤ₖ' m" (at level 70, no associativity, format "l  ≤ₖ  m").

Module vtree_embeddings_notations.

  Notation "s ≤st t" := (sub_dtree s t).

End vtree_embeddings_notations.

Import vtree_embeddings_notations.

Section vtree_upto_embedding.

  Variables (A : Type) (k : nat) (X : nat → rel₁ A) (R : nat → rel₂ A).

  Unset Elimination Schemes.

  Inductive vtree_upto_embed : vtree A → vtree A → Prop :=
    | vtree_upto_embed_subt t n x (v : vec _ n) i : t ≤ₖ v⦃i⦄ → t ≤ₖ ⟨x|v⟩
    | vtree_upto_embed_lt n x (v : vec _ n) y w : n < k → R n x y → vec_fall2 vtree_upto_embed v w → ⟨x|v⟩ ≤ₖ ⟨y|w⟩
    | vtree_upto_embed_ge n x (v : vec _ n) m y (w : vec _ m) : k ≤ n → R k x y → vec_embed vtree_upto_embed v w → ⟨x|v⟩ ≤ₖ ⟨y|w⟩
  where "s ≤ₖ t" := (vtree_upto_embed s t).

  Set Elimination Schemes.

  Hint Constructors vtree_upto_embed : core.

  Section vtree_upto_embed_ind.

    Variable (P : vtree A → vtree A → Prop)
             (HT1 : ∀ t n x (v : vec _ n) i, t ≤ₖ v⦃i⦄ → P t v⦃i⦄ → P t ⟨x|v⟩)
             (HT2 : ∀ n x (v : vec _ n) y (w : vec _ n), n < k → R n x y → vec_fall2 vtree_upto_embed v w → vec_fall2 P v w → P ⟨x|v⟩ ⟨y|w⟩)
             (HT3 : ∀ n x (v : vec _ n) m y (w : vec _ m), k ≤ n → R k x y → vec_embed vtree_upto_embed v w → vec_embed P v w → P ⟨x|v⟩ ⟨y|w⟩).

    Theorem vtree_upto_embed_ind : ∀ s t, s ≤ₖ t → P s t.
    Proof.
      refine (fix loop s t D { struct D } := _).
      destruct D as [ t n x v p H1 | n x v y w H1 H2 H3 | n x v m y w H1 H2 H3 ].
      + apply HT1 with (1 := H1); trivial.
        apply loop, H1.
      + apply HT2; trivial.
        intros p; apply loop, H3.
      + apply HT3; trivial.
        clear x y H1 H2; revert H3.
        induction 1; eauto with vec_db.
    Qed.

  End vtree_upto_embed_ind.

  Fact vtree_upto_embed_inv_right s t :
         s ≤ₖ t
       → match t with @dtree_cons _ m y w 
           => (∃i, s ≤ₖ w⦃i⦄)
            ∨ match s with @dtree_cons _ n x v
                => (∃e : n = m, n < k ∧ R n x y ∧ vec_fall2 vtree_upto_embed v↺e w)
                 ∨ (k ≤ n ∧ R k x y ∧ vec_embed vtree_upto_embed v w)
              end  
         end.
  Proof.
    destruct 1; eauto.
    right; left; exists eq_refl; auto.
  Qed.

  Fact vtree_sub_upto_embed r s t : r ≤st s → s ≤ₖ t → r ≤ₖ t.
  Proof.
    induction 1 as [ | s n i x v Hv IHv ] in t |- *; auto.
    induction t as [ m y w IHw ].
    intros [ (? & ?%IHw) | [ (<- & ? & ? & ?) | (? & ? & H)] ]%vtree_upto_embed_inv_right; eauto.
    destruct (vec_embed_prj H i); eauto.
  Qed.

  Fact vtree_upto_embed_sub r s t : r ≤ₖ s → s ≤st t → r ≤ₖ t.
  Proof. induction 2; eauto. Qed.

End vtree_upto_embedding.

Create HintDb vtree_db.

#[global] Hint Constructors vtree_upto_embed : vtree_db.

Fact vtree_upto_embed_mono A k (R T : nat → rel₂ A) :
         (∀n, n ≤ k → R n ⊆₂ T n)
        → vtree_upto_embed k R ⊆₂ vtree_upto_embed k T.
Proof.
  intros H.
  induction 1; eauto with vtree_db.
  constructor 2; auto.
  apply H; auto; tlia.
Qed.

#[global] Hint Resolve vtree_sub_upto_embed vtree_upto_embed_sub vtree_upto_embed_mono : vtree_db.
