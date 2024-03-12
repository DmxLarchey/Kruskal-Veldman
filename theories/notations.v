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
  Require Export notations.

(** For unary predicates (rel₁) or binary relations rel₂

    *   ⊥₁ and ⊥₂ : empty pred and rel
    *   ⊤₁ and ⊤₂ : full pred and rel
    *   ⊆₁ and ⊆₂ : inclusion         (in KruskalTrees)
    *   ∪₁ and ∪₂ : union             (in KruskalTrees)
    *   ∩₁ and ∩₂ : intersection      (in KruskalTrees)
*)

#[global] Notation "'rel₁' X" := (X -> Prop) (at level 1).
#[global] Notation "'rel₂' X" := (X -> X -> Prop) (at level 1).

#[global] Notation "⊥₁" := (fun _ => False).
#[global] Notation "⊥₂" := (fun _ _ => False).

(* Compatibility Layer accross different versions of Coq *)

Definition lt_le_weak n m : n < m → n ≤ m. 
Proof. lia. Qed.