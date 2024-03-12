(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Utf8.

From KruskalTrees
  Require Import idx vec vtree.

Require Import base notations tactics
               vtree_embed
               veldman_universe.

Import vec_notations vtree_notations af_notations.

Set Implicit Arguments.

Section afs_vtree_upto_embed.

  Variables (k : nat) (A : Type)
            (X : nat → rel₁ A)
            (R : nat → rel₂ A)
            (HXk : ∀n, k ≤ n → X n = X k)
            (HRk : ∀n, k ≤ n → R n = R k)
            (HXR : ∀n, n ≤ k → afs (X n) (R n)).

  (** This is how we proceed:
       1) we embed the type A into the universe U
       2) we embed the relation (X,R) in U
       3) we show that the embedded relation gives
          an afs relation on vtree's using kruskal_afs_universe
       4) we project back on A using a rel. morphism
    *)

  Notation U := (universe A).

  Notation "⦉ x ⦊₀" := (@univ_init _ x) (at level 1, format "⦉ x ⦊₀").

  (* embedding (X,R) into U *)

  Let X' n (u : U) :=
    match u with
    | ⦉u⦊₀ => X n u
    | _   => False
    end.

  Let R' n (u v : U) :=
    match u, v with
    | ⦉u⦊₀, ⦉v⦊₀ => R n u v
    | _, _     => False
    end.

  (* the relational morphism *)

  Inductive vtree_equiv : vtree U → vtree A → Prop :=
    | in_vtree n (v : vec _ n) a w :
          vec_fall2 vtree_equiv v w
        → vtree_equiv ⟨⦉a⦊₀|v⟩ ⟨a|w⟩.

  Local Fact vtree_equiv_inv t r :
         vtree_equiv t r
       → match t, r with
         | ⟨u|v⟩, ⟨a|w⟩ => u = ⦉a⦊₀
                         ∧ ∃e, vec_fall2 vtree_equiv v↺e w
         end.
  Proof. induction 1; split; auto; exists eq_refl; auto. Qed.

  Tactic Notation "vtree" "equiv" "inv" hyp(H) :=
    apply vtree_equiv_inv in H as (-> & <- & H); simpl in H.

  Local Fact vtree_equiv_inj t r₁ r₂ : vtree_equiv t r₁ → vtree_equiv t r₂ → r₁ = r₂.
  Proof.
    intros H; revert H r₂.
    induction 1; intros [] (<-%univ_init_inj & ? & ?)%vtree_equiv_inv; eq refl.
    f_equal; vec ext; auto.
  Qed.

  Local Fact vtree_equiv_surj r : wft X r → ∃ₜ t, wft X' t ∧ vtree_equiv t r.
  Proof.
    induction 1 as [ n a w H1 H2 IH2 ] using wft_rect.
    vec reif IH2 as (v & Hv).
    exists ⟨⦉a⦊₀|v⟩; rewrite wft_fix; repeat split; auto; intro; apply Hv.
  Qed.

  Hint Resolve vtree_equiv_inj : core.

  Local Fact vec_embed_vtree_equiv_compose n (u : vec _ n) m (v : vec _ m) p (w : vec _ p) :
         vec_embed (fun r t => vtree_equiv t r) u v
       → vec_embed vtree_equiv v w
       → vec_embed eq u w.
  Proof.
    intros H1 H2.
    apply vec_embed_mono with (2 := vec_embed_compose H1 H2).
    intros ? ? (? & []); eauto.
  Qed.

  Hint Resolve vec_fall2_embed vec_embed_vtree_equiv_compose : core.

  Local Fact vtree_equiv_morph t₁ t₂ r₁ r₂ :
          vtree_equiv t₁ r₁
        → vtree_equiv t₂ r₂
        → vtree_upto_embed k R' t₁ t₂
        → vtree_upto_embed k R r₁ r₂.
  Proof.
    intros E1 E2 H; revert H r₁ r₂ E1 E2.
    induction 1 as [ i b v t p H1 IH1
                   | i u1 v1 u2 v2 H0 H1 H2 IH2
                   | i u1 v1 j u2 v2 H0 H1 H2 IH2 ]; intros y1 y2 E1 E2.
    + destruct y2 as [ q c z ]; vtree equiv inv E2.
      constructor 1 with p; eauto.
    + destruct y1 as [ j1 a1 w1 ]; vtree equiv inv E1.
      destruct y2 as [ j2 a2 w2 ]; vtree equiv inv E2.
      constructor 2; eauto; intro; eauto.
    + destruct y1 as [ j1 a1 w1 ]; vtree equiv inv E1.
      destruct y2 as [ j2 a2 w2 ]; vtree equiv inv E2.
      constructor 3; auto.
      (* Here we avoid vintercalate and stick with vec_embed/vec_fall2
         thanks to the injectivity of vtree_equiv *)
      apply vec_embed_sub_vec_fall2 in IH2 as (w & H3 & H4).
      destruct (vec_embed_fall2_inv H4 E2) as (? & <-%vec_prj_ext & G2).
      destruct (vec_embed_fall2_inv G2 (vec_fall2_swap E2)) as (w2'& E3 & G4).
      specialize (fun p => H3 p _ _ (E1 _) (E3 _)).
      apply vec_embed_sub_vec_fall2; eauto.
  Qed.

  Hint Resolve vtree_equiv_surj vtree_equiv_morph : core.

  Theorem afs_vtree_upto_embed : afs (wft X) (vtree_upto_embed k R).
  Proof.
    cut (afs (wft X') (vtree_upto_embed k R')).
    + af rel morph vtree_equiv; eauto.
    + assert (forall n, k <= n -> X' n = X' k) as HXk'.
      1: unfold X'; intros ? ?; rewrite HXk; auto.
      assert (forall n, k <= n -> R' n = R' k) as HRk'.
      1: unfold R'; intros ? ?; rewrite HRk; auto.
      assert (forall n, n <= k -> afs (X' n) (R' n)) as HXR'.
      1:{ intros n Hn.
          generalize (HXR Hn).
          af rel morph (fun a u => ⦉a⦊₀ = u).
          * intros []; simpl; eauto; tauto.
          * intros ? ? [] []; simpl; try tauto.
            intros _ _ _ _ H1 H2.
            univ inj H1; univ inj H2; subst; auto. }
      apply kruskal_afs_universe; auto.
      intros n; destruct (le_lt_dec n k) as [ Hn | Hn ]; auto.
      rewrite HXk', HRk'; eauto; tlia.
  Qed.

End afs_vtree_upto_embed.

Check afs_vtree_upto_embed.