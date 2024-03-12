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
  Require Import vec vtree.

Require Import base notations tactics
               vtree_embed
               afs_lex
               veldman_leaves
               veldman_higman
               veldman_kruskal.

Require Export universe.

Import idx notations vec_notations dtree_notations
       af_notations afs_lex_notations af_choice_notations.

Set Implicit Arguments.

Section afs_induction.

  (** We implement a tailored induction principle for
      the proof of Kruskal's tree theorem (the one below
      using a universe). This allows to circumvent
      the need for stumps (and hence Brouwer's thesis)
      when considering Prop-bounded af predicates.

      Compared to afs_seq_facile_ind, we integrate the 
      conditions

              ∀n, k ≤ n → X n = X k
        and   ∀n, k ≤ n → R n = R k

      in the induction principle.

      Notice that this "induction upto" technique is original
      to the current development, and in fact nowhere to be
      founded, as far as I (DLW) am aware of. *)

  Variables (U : Type).

  Implicit Types (s : nat → af_status)
                 (X : nat → rel₁ U)
                 (R : nat → rel₂ U).

  Variables (Q : _ → _ → _ → Base)
            (Qext : ∀ k X R X' R', (∀n, X n = X' n)
                                 → (∀n, R n = R' n)
                                 → Q k X R → Q k X' R')
            (IHQ : ∀ k s X R,
                       ⟪s,X,R⟫ₛ
                     → (∀n, k ≤ n → X n = X k)
                     → (∀n, k ≤ n → R n = R k)
                     → (∀ k' s' X' R',
                           ⟪s',X',R'⟫ₛ
                         → (∀n, k' ≤ n → X' n = X' k')
                         → (∀n, k' ≤ n → R' n = R' k')
                         → ⟪k',s',X',R'⟫ ≺ₘ ⟪k,s,X,R⟫
                         → Q k' X' R')
                     → Q k X R).

  Theorem afs_upto_induction k X R :
              (∀n, afs (X n) (R n))
            → (∀n, k ≤ n → X n = X k)
            → (∀n, k ≤ n → R n = R k)
            → Q k X R.
  Proof.
    intros H.
    set (P k X R := (∀n, k ≤ n → X n = X k)
                  → (∀n, k ≤ n → R n = R k)
                  → Q k X R).
    change (P k X R); revert k X R H.
    apply afs_seq_facile_ind; unfold P; clear P.
    + intros k X R Y T H1 H2 H3 H4 H5.
      cut (Q k X R).
      * apply Qext; auto.
      * apply H3; intros.
        - rewrite !H1; auto.
        - rewrite !H2; auto.
    + intros k s X R H IH HX HR.
      apply IHQ with s; auto.
      intros k' s' X' R' H1 H2 H3 H4.
      apply IH with s'; auto.
  Qed.

End afs_induction.

Section veldman_afs_universe.

  Variables (A : Type).

  Notation U := (universe A).

  Variables (k : nat)
            (X : nat → rel₁ U)
            (R : nat → rel₂ U)
            (HX : ∀n, k ≤ n → X n = X k)
            (HR : ∀n, k ≤ n → R n = R k)
            (HXR : ∀n, afs (X n) (R n)).

  Theorem veldman_afs_universe : afs (wft X) (vtree_upto_embed k R).
  Proof.
    revert k X R HXR HX HR.
    apply afs_upto_induction.

    (** We routine check for the extensionality of the property we are proving, *)
    1:{ intros k X R Y T H1 H2.
        apply afs_mono.
        * apply wft_mono; intro; rewrite H1; auto.
        * intros ? ? ? ?; apply vtree_upto_embed_mono; intro; rewrite H2; auto. }

    intros k s X R HXR HXk HRk IHXR.

    (** We now have the induction hypothesis available
        which includes a *status sequence* telling whether
         - (X n,R n) is empty (s n = ▢)
         - (X n,R n) is full  (s n = ▣)
         - (X n,R n) is almost full (s n = ◩, lifted case)

        * s n = ▢ is an absurd case because no node exists at arity n

        * s 0 = ▣ is dealt directly with kruskal_afs_leave_full (arity 0 is for leaves)
        * s 0 = ◩ is dealt by lifting the leave, see kruskal_afs_leaves_lift

        * s (1+i) = ▣ or ◩ is dealt with kruskal_afs_nodes
      *)

    (* First we lift by a tree t and proceed by induction on t *)
    constructor 2; induction 1 as [ i a w Ha Hw IHw ] using wft_rect.

    (* We exclude the case where X i is empty because the root belongs to X i,
       ie s i = ▢ contradicts X i a *)
    case_eq (s i); [ | specialize (@HXR i); intros E; rewrite E in HXR; destruct (HXR _ Ha) ].

   (* We distinguish leaves from internal nodes, ie arity i is 0 or S _ *)
    destruct i as [ | i ].

    + (* arity i = 0, case of leaves *)
      clear Hw IHw; vec invert w.
      intros [] Hs0.

      * (* arity i is 0 ans s 0 = ◩, lifted case, dealt with kruskal_afs_leaves_lift *)
        apply kruskal_afs_leaves_lift.
        apply IHXR with (s' := fun n =>
           match n, k with
             | 0, _ => ◩
             | _, 0 => ◩
             | _, _ => s n
           end); auto.
        - intros []; simpl; auto.
          ++ generalize (@HXR 0); rewrite Hs0.
             intro H; apply afs_inv with (1 := H); auto.
          ++ destruct k; auto; simpl.
             rewrite HXk; tlia.
             generalize (HXR 0); rewrite Hs0; simpl.
             intros H; apply afs_inv with (1 := H); auto.
        - destruct k; intros []; auto; lia.
        - destruct k.
          ++ constructor 1; rewrite Hs0; constructor; auto.
          ++ constructor 2 with 0; auto; tlia.
             ** rewrite Hs0; constructor; auto.
             ** intros [] ?; auto; lia.
      * (* arity i is 0 ans s 0 = ▣, full case, dealt with kruskal_afs_leave_full *)
        specialize (@HXR 0); rewrite Hs0 in HXR; red in HXR.
        apply kruskal_afs_leave_full; auto.

    + (* We distinguish S i < k and k ≤ S i *)
      destruct (le_lt_dec k (S i)) as [ Hik | Hik ].

      * (* case k ≤ S i. The value of s (S i) is irrelevant here, only that of s k is *)
        intros _ _.
        case_eq (s k).
        - intros c Hc.
          apply veldman_afs_nodes_ge with s; eauto; try (intros E; rewrite E in Hc; easy).
          apply wft_fix; auto.
        - intros Hsk; exfalso.
          rewrite HXk in Ha; auto.
          generalize (HXR k).
          rewrite Hsk; simpl; eauto.
      * (* case S i < k *)
        intros c Hc.
        apply veldman_afs_nodes_lt with s; eauto; try (intros E; rewrite E in Hc; easy).
        - intros s' X' R' H1 H2 H3.
          apply IHXR with (1 := H1); auto.
          ++ destruct H3 as [ j Hj _ E _ ]; intros; rewrite !E; auto; lia.
          ++ destruct H3 as [ j Hj _ _ E ]; intros; rewrite !E; auto; lia.
          ++ revert H2 H3; apply easier_more_facile.
        - apply wft_fix; auto.
  Qed.

End veldman_afs_universe.


