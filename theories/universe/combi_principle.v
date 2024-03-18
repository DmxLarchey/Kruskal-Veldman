(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Utf8.

From KruskalTrees
  Require Import notations idx vec vtree.

From KruskalFinite
  Require Import finite choice.

Require Import base notations vtree_embed.

Import idx_notations vec_notations
       vtree_notations vtree_embeddings_notations.

Set Implicit Arguments.

#[local] Notation FAN w := (λ c, vec_fall2 (λ x l, x ∈ l) c w).

Local Fact fin_FAN X n (w : vec (list X) n) : fin (FAN w).
Proof. apply fin_vec_fall2 with (R := λ l x, x ∈ l); fin auto. Qed.

(** Similar to list_combi_principle in Kruskal-Higman but for vectors 
    in place of lists. *)
Theorem vec_combi_principle X n w (P : rel₁ (vec X n)) (B : rel₁ X) :
         (∀c, FAN w c → P c ∨ ∃i, B c⦃i⦄)
       → (∃c, FAN w c ∧ P c) ∨ (∃i, ∀x, x ∈ w⦃i⦄ → B x).
Proof.
  induction w as [ | l n w IHw ] in P |- *; intros HPB.
  + destruct (HPB ∅) as [ | (i & _) ]; auto with vec_db.
    * left; exists ∅; auto with vec_db.
    * idx invert all.
  + assert (H: ∀x, x ∈ l → B x ∨ ∀c, FAN w c → P (x##c) ∨ ∃i, B c⦃i⦄).
    1:{ intros x Hx.
        apply fin_choice_cst_left.
        + apply fin_vec_fall2 with (R := λ l x, x ∈ l); fin auto.
        + intros c Hc.
          destruct (HPB (x##c)) as [ | [] ]; eauto with vec_db.
          idx invert all; simpl in *; eauto. }
    apply fin_choice in H as [ | (x & Hx & [ (c & []) | (i & ?) ]%IHw)]; fin auto.
    * right; exists 𝕆; eauto.
    * left; exists (x##c); eauto with vec_db.
    * right; exists (𝕊 i); eauto.
Qed.

Arguments vec_combi_principle {X n}.

Corollary fin_vec_fall2_find X Y (R : X → Y → Prop) P n (v : vec X n) :
      (∀i, fin (R v⦃i⦄))
    → (∀w, vec_fall2 R v w → ∃i, P w⦃i⦄)
    → (∃i, R v⦃i⦄ ⊆₁ P).
Proof.
  intros (w & Hw)%vec_reif_t Hv.
  destruct (vec_combi_principle w ⊥₁ P)
    as [ (_ & _ & []) | (i & ?) ].
  + intros c Hc.
    destruct (Hv c); eauto.
    intro; apply Hw, Hc.
  + exists i; intros ? ?%Hw; auto.
Qed.

Section combi_trees.

  Variables (A A' : Type) (X : nat → rel₁ A)
            (ana : vtree A → vtree A' → Prop)
            (fin_ana : ∀t, wft X t → fin (ana t))  (* finite analysis on well formed trees *)
            (D' : rel₁ (vtree A')).

  Notation vana := (vec_fall2 ana).
  Notation E' := (λ t, ∃s, s ≤st t ∧ D' s).


  (* This abstract nicely E_hereditary as a combinatorial
     principle on trees, for properties E'/exceptional
     defined as "contains a disapointing sub-tree". 

     It x' is an analysis label and v vector of
     wf evaluations and t an evaluation st. 
     - t is exceptional (the analyses of t are exceptional)
     - for any analysis v' of v, ⟨x'|v'⟩ analyses t
     Then 
     - either v contains an exceptional component
     - or there is analysis v' of v st  ⟨x'|v'⟩ is disapointing. *)
  Lemma vtree_combi_analysis n x' (v : vec _ n) t :
            vec_fall (wft X) v
          → ana t ⊆₁ E'
          → (∀v', vana v v' → ana t ⟨x'|v'⟩)
          → (∃p,   ana v⦃p⦄ ⊆₁ E')
          ∨ (∃v', vana v v' ∧ D' ⟨x'|v'⟩).
  Proof.
    intros Hv Ht1 Ht2.
    assert ((∀v', vana v v' → ∃p, E' v'⦃p⦄)
          ∨ (∃v', vana v v' ∧ D' ⟨x'|v'⟩)) 
      as [H|]; eauto.
    + apply fin_choice; auto.
      * apply fin_vec_fall2; auto.
      * intros v' Hv'.
        destruct (Ht1 ⟨x'|v'⟩) as (t' & H' & ?); auto.
        apply sub_dtree_inv_rt in H' as [ -> | [] ]; eauto.
    + apply fin_vec_fall2_find with (P := E') in H; auto.
  Qed.

End combi_trees.


