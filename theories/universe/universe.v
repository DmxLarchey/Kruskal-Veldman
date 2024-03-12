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

Require Import notations tactics.

Set Implicit Arguments.

Section universe.

  Variable (A : Type).

  (** For U := universe we get the inclusion

          A
        + U
        + Σn, U*idxₙ*vtree U
        + Σn, U*(Σi, (vtree U)ⁱ)ⁿ
        ⊆ U

      where idxₙ ≌ {1,...,n}
       and  Xⁿ ≌ X*...*X (n times)
       and  Σn,T(n) is the dependent sum

      together with the embeddings

       - univ_init : A → U
       - univ_refl : U → U
       - univ_nest_1 : Σn, U*idxₙ*vtree U → U
       - univ_nest_2 : Σn, U*(Σi, (vtree U)ⁱ)ⁿ → U

     We do *not* need the recursor, just the embeddings
     (which are injective with disjoint 2-by-2 images).

     This type U is a universe for the proof of Higman's and
     Kruskal's tree theorems in the sense that it is stable under
     all the type constructions that occur inside those proofs.

     So instead of lifting the parameters X i & R i for each
     arity of dtrees i when invoquing a recursive call,
     we embed deeper in the universe.

     We can then work with U as uniform type, as is the type
     of natural numbers (which a universe for finitary structures)
     in "Wim Veldman's proof", so we abstract this aspect of
     his proof here.

     Notice that the above embeddings (which are constructors)
     are much easier to grasp in pratice than complex encodings
     of trees into natural numbers. *)

  Unset Elimination Schemes.

  Inductive universe :=

    | univ_init      : A
                     → universe

    | univ_refl      : universe
                     → universe

    | univ_nest_1 n  : universe
                     → idx n
                     → vtree universe
                     → universe

    | univ_nest_2 n  : universe
                     → hvec (vtree universe) n
                     → universe
    .

  Set Elimination Schemes.

  (* We use the following notations:
       "⦉a⦊₀" := (@univ_init _ a) in veldman_theorem.v
       "⦉u⦊₁" := (@univ_refl _ u) in veldman_{higman,kruskal}.v
       "⦉u,p,t⦊₂" := (@univ_nest_1 _ _ u p t) in veldman_higman.v
       "⦉u,v⦊₂" := (@univ_nest_2 _ _ u v) in veldman_kruskal.v *)

  (* We need injectivity and pattern matching, but *not* induction,
     ie we only need a post-fixpoint, not a fixpoint *)

  Fact univ_init_inj a₁ a₂ : univ_init a₁ = univ_init a₂ → a₁ = a₂.
  Proof. inversion 1; auto. Qed.

  Fact univ_refl_inj u₁ u₂ : univ_refl u₁ = univ_refl u₂ → u₁ = u₂.
  Proof. inversion 1; subst; auto. Qed.

  Fact univ_nest_1_inj n₁ u₁ p₁ t₁ n₂ u₂ p₂ t₂ :
        @univ_nest_1 n₁ u₁ p₁ t₁ = @univ_nest_1 n₂ u₂ p₂ t₂
      → (u₁ = u₂) * ({ e : n₁ = n₂ | p₁↺e = p₂ } * (t₁ = t₂)).
  Proof. inversion 1; subst; rsplit 2; auto; exists eq_refl; split; auto. Qed.

  Fact univ_nest_2_inj n₁ u₁ w₁ n₂ u₂ w₂ :
        @univ_nest_2 n₁ u₁ w₁ = @univ_nest_2 n₂ u₂ w₂
      → (u₁ = u₂) * { e : n₁ = n₂ | w₁↺e = w₂ }.
  Proof. inversion 1; subst; split; auto; exists eq_refl; split; auto. Qed.

End universe.

(** A small tactic for the injectivity of embeddings *)

Tactic Notation "univ" "inj" hyp(H) :=
  match type of H with
  | @univ_init _ _ = @univ_init _ _ => apply univ_init_inj in H
  | @univ_refl _ _ = @univ_refl _ _ => apply univ_refl_inj in H
  | @univ_nest_1 _ _ _ _ _ = @univ_nest_1 _ _ _ _ _ => apply univ_nest_1_inj in H as (? & (? & ?) & ?); eq refl
  | @univ_nest_2 _ _ _ _ = @univ_nest_2 _ _ _ _ => apply univ_nest_2_inj in H as (? & ? & ?); eq refl
  end.
