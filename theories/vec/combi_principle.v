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
  Require Import notations idx vec.

From KruskalFinite
  Require Import finite choice.

Require Import base notations.

Import idx_notations vec_notations.

Set Implicit Arguments.

#[local] Notation FAN w := (λ c, vec_fall2 (λ x l, x ∈ l) c w).

Fact fin_FAN X n (w : vec (list X) n) : fin (FAN w).
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
        + apply fin_FAN.
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

