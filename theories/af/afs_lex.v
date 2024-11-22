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

Require Import base notations tactics wf_upto.

Import lift_notations.

Set Implicit Arguments.

Reserved Notation "⟪ a , b , c ⟫ₐ"
    (at level 0, no associativity, format "⟪ a , b , c ⟫ₐ").

Reserved Notation "'⟪' a , b , c '⟫ₛ'"
    (at level 0, no associativity, format "⟪ a , b , c ⟫ₛ").

(* this is for the "simpler" relation between witnessed afs relations *)

Reserved Notation "'⟪' a , b , c '⟫' '≺' '⟪' x , y , z '⟫'"
    (at level 0, no associativity, format "⟪ a , b , c ⟫  ≺  ⟪ x , y , z ⟫").

(* this is for the "easier" relation between sequences of witnessed afs relations *)

Reserved Notation "'⟪' a , b , c '⟫' '≺' k ']ₑ' '⟪' x , y , z '⟫'"
    (at level 0, no associativity, format "⟪ a , b , c ⟫  ≺ k ]ₑ  ⟪ x , y , z ⟫").

(* this is for the "more facile" relation between sequences of witnessed afs relations *)

Reserved Notation "'⟪' a , b , c , d '⟫' '≺ₘ' '⟪' v , x , y , z '⟫'"
    (at level 0, no associativity, format "⟪ a , b , c , d ⟫  ≺ₘ  ⟪ v , x , y , z ⟫").

(* this is for the "easier" relation between pairs of witnessed af relations *)

Reserved Notation "'⟪' a , b , c | a' , b' , c' '⟫' '≺₂' '⟪' x , y , z | x' , y' , z' '⟫'"
    (at level 0, no associativity, format "⟪ a , b , c | a' , b' , c' ⟫  ≺₂  ⟪ x , y , z | x' , y' , z' ⟫").

(** The order is roughtly ▢ < ▣ < ◩ but see af[s]_lex.v
    for the precise meaning, ie we have

      a)   ▢ < ▣
      b)   ▣ < ◩
      c) ◩↑x < ◩

    the relation ▢ < ◩ may be added but would be unused *)

Inductive af_choice := af_choice_af | af_choice_full.

Definition af_status := option af_choice.

Module af_choice_notations.

  Notation "▢" := (@None _) (at level 0).
  Notation "▣" := (Some af_choice_full) (at level 0).
  Notation "◩" := (Some af_choice_af) (at level 0).

End af_choice_notations.

Import af_choice_notations.

Section afsw.

  (** The order below (combined lexicographically below in afs_seq_easier)
      cover all the recursive calls in the proof of Higman's theorem

      1&2) the first two clauses allows to replace any full or af relation
           with an empty predicate;
        3) the third clause allows to replace an af relation with a full relation
        4) the last clause allows to shift an af relation R upwards

      Notation remark: the ad-hoc parentheses ⟪ ... ⟫ allow parsing
           it would be better w/o them but I do not know how to define
           such a syntax so that Coq accepts it.

      "Important Remark:"

      When R is full over P then we have both

          R↑x ~ R   and    ⟪◩,P,R↑x⟫ ≺ ⟪◩,P,R⟫

      ie they are extensionally equivalent over P and
      the two identical witnesses are comparable so this is
      not well-founded in the standard understanding of
      well-founded relations, ie

      the sequence n => ⟪◩,P,R↑x..{n}..↑x⟫ is ≺-decreasing forever

    *)

  Variable U : Type.

  Implicit Types (X : rel₁ U) (R : rel₂ U).

  (** The correctness predicate for witnessed afs relations *)

  Definition afs_status_correct s X R :=
    match s with
    | ▢ => ∀x, X x → False            (* s = ▢ witnesses that P is not inhabited    *)
    | ▣ => ∀ x y, X x → X y → R x y   (* s = ▣ witnesses that R is full on P        *)
    | ◩ => afs X R                    (* s = ◩ witnesses that R is almost full on P *)
    end.

  Notation "⟪ a , b , c ⟫ₐ" := (afs_status_correct a b c).

  Fact afs_status_correct_afs s X R : ⟪s,X,R⟫ₐ → afs X R.
  Proof.
    destruct s as [ [] | ]; simpl; auto.
    constructor 1; intros x ? Hx.
    apply H in Hx as [].
  Qed.

  (** The "simpler" relation between witnessed afs relations *)

  Unset Elimination Schemes.

  Inductive lt_afs_status : _ → _ → _ → _ → _ → _ → Base :=
    | lt_afs_status_1 X R Y T :           ⟪▢,X,R⟫ ≺ ⟪▣,Y,T⟫
    | lt_afs_status_2 X R x :    X x -> ⟪◩,X,R↑x⟫ ≺ ⟪◩,X,R⟫
  where "⟪ a , b , c ⟫ ≺ ⟪ x , y , z ⟫" := (lt_afs_status a b c x y z).

  Set Elimination Schemes.

  Local Fact lt_afs_status_inv_empty s1 X1 R1 X2 R2 : ⟪s1,X1,R1⟫ ≺ ⟪▢,X2,R2⟫ → False.
  Proof. inversion 1. Qed.

  Local Fact lt_afs_status_inv_full s1 X1 R1 X2 R2 : ⟪s1,X1,R1⟫ ≺ ⟪▣,X2,R2⟫ → s1 = ▢.
  Proof. inversion 1; auto. Qed.

  Local Fact lt_afs_status_inv_af X1 R1 s2 X2 R2 :
           ⟪◩,X1,R1⟫ ≺ ⟪s2,X2,R2⟫ → s2 = ◩ ∧ₜ X1 = X2 ∧ₜ ∃ₜ x, X1 x ∧ₜ R1 = R2↑x.
  Proof. inversion 1; eauto. Qed.

  (** The Σ-type of correct witnessed afs relations *)

  Local Definition afs_witnessed := (af_status * (rel₁ U * rel₂ U))%type.

  Local Definition afsw_correct : afs_witnessed -> Base := 
    λ '(s,(X,R)), afs_status_correct s X R.

  Local Definition afsw := sigT afsw_correct.

  (* Notation better than Definition because unification does not work well
     below otherwise and we would need to unfold many times *)

  Notation afsw_forget := (fun w => snd (projT1 w)).

  Local Definition lt_afsw (x y : afsw) :=
    match x, y with
    | existT _ (s,(X,R)) _, existT _ (s',(X',R')) _
        => @lt_afs_status s X R s' X' R'
    end.

  Infix "<w" := lt_afsw (at level 70).

  (** We show that lt_afw is wf_upto forgetting the witness & correctness proof *)

  Section lt_afsw_wf_upto.

    (* Here we show that <w is well-founded up to hidding the status *)

    Local Fact lt_afsw_empty : ∀ w r C, w <w existT _ (▢,r) C → False.
    Proof. intros ((?,(?,?)) & ?) (?,?) ?; simpl; apply lt_afs_status_inv_empty. Qed.

    Local Fact lt_afsw_full : ∀ s r C r' C', existT _ (s,r) C <w existT _ (▣,r') C' → s = ▢.
    Proof. intros ? (?,?) ? (?,?) ?; simpl; apply lt_afs_status_inv_full. Qed.

    Local Fact lt_afsw_lift X1 R1 C1 X2 R2 C2 :
        existT _ (◩,(X1,R1)) C1 <w existT _ (◩,(X2,R2)) C2
     ⇄ₜ ∃ₜ x, X1 x ∧ ∃ₜ e : X1 = X2, R1↺e = R2↑x.
    Proof.
      split.
      + simpl; intros H.
        apply lt_afs_status_inv_af in H; auto.
        destruct H as (_ & -> & x & ? & ->).
        exists x; split; auto; exists eq_refl; auto.
      + intros (x & ? & -> & ?); simpl in *; subst; simpl in H.
        constructor; auto.
    Qed.

    Variables (Q : rel₁ U * rel₂ U → Base)
              (IHQ : ∀w, (∀w', w' <w w → Q (afsw_forget w')) → Q (afsw_forget w)).

    (* We prove the property for empty X *)

    Local Fact HQ_empty XR : afsw_correct (▢,XR) → Q XR.
    Proof.
      intros C.
      apply IHQ with (w := existT _ (▢,_) C); auto.
      intros ((w,XR') & H1) H2.
      exfalso; revert H2; apply lt_afsw_empty.
    Qed.

    Hint Resolve HQ_empty : core.

    (* We prove the property for full R over X *)

    Local Fact HQ_full XR : afsw_correct (▣,XR) → Q XR.
    Proof.
      simpl; intros C.
      apply IHQ with (w := existT _ (▣,_) C); auto.
      intros ((w,XR') & H1) H2.
      apply lt_afsw_full in H2 as ->; auto.
    Qed.

    Hint Resolve HQ_full : core.

    (* We prove the property for afs X R,
       and stop the induction by switching to
       witness ▣.

       This is how the termination information of
       afs X R is embedded into the witnessed pair.

       If we could not forget the witness, then
       one could not apply HQ_full below hence
       once could not stop the recursive process

     *)

    Local Fact HQ_lift : ∀XR, afsw_correct (◩,XR) → Q XR.
    Proof.
      intros (X,R); simpl.
      induction 1 as [ R HR | R HR IHR ].
      + apply HQ_full; simpl; auto.
      + apply (@IHQ (existT _ (◩,(X,R)) (afs_lift HR))); simpl; auto.
        intros (([[]|],(X',R')) & H1) H2; auto; simpl.
        apply lt_afsw_lift in H2 as (x & ? & -> & ?).
        simpl in *; subst; auto.
    Qed.

    Hint Resolve HQ_lift : core.

    Local Lemma lt_afsw_wf_upto_rec : ∀w : afsw, Q (afsw_forget w).
    Proof. intros (([[]|],(X,R)) & C); simpl; auto. Qed.

  End lt_afsw_wf_upto.

  Local Theorem wf_upto_lt_afsw : wf_upto afsw_forget lt_afsw.
  Proof. intros ? ? []; apply lt_afsw_wf_upto_rec; auto. Qed.

End afsw.

Local Notation "⟪ a , b , c ⟫ₐ" := (@afs_status_correct _ a b c).
Local Notation "⟪ a , b , c ⟫ ≺ ⟪ x , y , z ⟫" := (@lt_afs_status _ a b c x y z).
Local Notation afsw_witness := (fun w => fst (projT1 w)).
Local Notation afsw_forget := (fun w => snd (projT1 w)).

Section afs_status_ind.

  (** This is the simplest example of how to transform wf_upto
      theorems into a more usable afs induction principle *)

  Variables (U : Type).

  Implicit Types (s : af_status) (X : rel₁ U) (R : rel₂ U).

  Variables (Q : _ → _ → Base)
            (IHQ : ∀ s X R,
                      ⟪s,X,R⟫ₐ
                    → (∀ s' X' R', ⟪s',X',R'⟫ₐ
                                 → ⟪s',X',R'⟫ ≺ ⟪s,X,R⟫
                                 → Q X' R')
                    → Q X R).

  Theorem afs_status_ind X R : afs X R → Q X R.
  Proof.
    intros H.
    set (Q' (σ : rel₁ U * rel₂ U) := Q (fst σ) (snd σ)).
    set (s' := (existT _ (◩,(X,R)) H : afsw _)).
    change (Q' (afsw_forget s')).
    apply wf_upto_lt_afsw.
    intros ((s1,(x1,r1)) & H1) E1.
    unfold Q'; simpl in H1.
    apply IHQ with (1 := H1).
    intros s2 x2 r2 H2 H3.
    specialize (E1 (existT _ (s2,(x2,r2)) H2)).
    apply E1, H3.
  Qed.

End afs_status_ind.

Section afs_seq_easier_ind.

  Variables (U : Type).

  Implicit Types (s : nat → af_status) (X : nat → rel₁ U) (R : nat → rel₂ U).

  Unset Elimination Schemes.

  (* We represent the order with a rule for better readability *)

  Inductive afs_seq_easier k s X R s' X' R' : Base :=
    | afs_seq_easier_intro i : i < k
                             → ⟪s i,X i,R i⟫ ≺ ⟪s' i,X' i,R' i⟫
                             → (∀n, i < n → X n = X' n)
                             → (∀n, i < n → R n = R' n)
                             → ⟪s,X,R⟫ ≺k]ₑ ⟪s',X',R'⟫
  where "⟪ a , b , c ⟫ ≺ k ]ₑ ⟪ x , y , z ⟫" := (afs_seq_easier k a b c x y z).

  Set Elimination Schemes.

  Variable (k : nat).

  Definition afs_seq_correct s X R := ∀n, ⟪s n,X n,R n⟫ₐ.
  Notation "⟪ a , b , c ⟫ₛ" := (afs_seq_correct a b c).

  Variables (Q : _ → _ → Base)
            (HQ : ∀ X Y R T, (∀n, X n = Y n)
                           → (∀n, R n = T n)
                           →  Q X R -> Q Y T)
            (IHQ : ∀ s X R,
                       ⟪s,X,R⟫ₛ
                     → (∀ s' X' R', ⟪s',X',R'⟫ₛ
                                  → ⟪s',X',R'⟫ ≺k]ₑ ⟪s,X,R⟫
                                  →  Q X' R')
                     → Q X R).

  Theorem afs_seq_easier_ind : ∀ X R, (∀n, afs (X n) (R n)) → Q X R.
  Proof.
    generalize (wf_upto_lex_r_seq (k := k) (@wf_upto_lt_afsw U)).
    unfold prj_seq; intros E x r H.
    set (Q' (σ : nat -> rel₁ U * rel₂ U) := Q (fun n => fst (σ n)) (fun n => snd (σ n))).
    set (s' (n : nat) := (existT _ (◩,(x n,r n)) (H n) : afsw _)).
    change (Q' (fun n => afsw_forget (s' n))).
    apply E; clear E.
    + intros w1 w2 Hw; apply HQ.
      all: intros n; specialize (Hw n); rewrite Hw; constructor.
    + intros w1 Hw1.
      unfold Q'; apply IHQ with (fun n => afsw_witness (w1 n)).
      * intros n; destruct (w1 n) as ((?,(?,?)) & ?); auto.
      * intros s2 x2 r2 c2 H1.
        specialize (Hw1 (fun n => existT _ (s2 n,(x2 n,r2 n)) (c2 n))).
        apply Hw1.
        revert H1.
        intros [ i G1 G2 G3 G4 ].
        exists i; repeat split; auto.
        - revert G2; simpl.
          destruct (w1 i) as ((?,(?,?)) & ?); simpl; auto.
        - intros j (Hj & _); simpl.
          generalize (G3 _ Hj) (G4 _ Hj).
          destruct (w1 j) as ((?,(?,?)) & ?); simpl.
          generalize (x2 j) (r2 j).
          intros; subst; auto.
  Qed.

End afs_seq_easier_ind.

Local Notation "⟪ a , b , c ⟫ₛ" := (@afs_seq_correct _ a b c).

Section afs_seq_facile_ind.

  Variables (U : Type).

  Implicit Types (s : nat → af_status) (X : nat → rel₁ U) (R : nat → rel₂ U).

  Unset Elimination Schemes.

  (* We represent the order with two rules for better readability *)

  Inductive afs_seq_more_facile k s X R k' s' X' R' : Base :=
    | afs_seq_more_facile_1 :   ⟪s k,X k,R k⟫ ≺ ⟪s' k',X' k',R' k'⟫
                              → ⟪k,s,X,R⟫ ≺ₘ ⟪k',s',X',R'⟫
    | afs_seq_more_facile_2 i : k = k'
                              → s k = s' k
                              → X k = X' k
                              → R k = R' k
                              → i < k
                              → ⟪s i,X i,R i⟫ ≺ ⟪s' i,X' i,R' i⟫
                              → (∀j, i < j <= k → X j = X' j)
                              → (∀j, i < j <= k → R j = R' j)
                              → ⟪k,s,X,R⟫ ≺ₘ ⟪k',s',X',R'⟫
  where "⟪ a , b , c , d ⟫ ≺ₘ ⟪ v , x , y , z ⟫" := (afs_seq_more_facile a b c d v x y z).

  Set Elimination Schemes.

  Variables (Q : _ → _ → _ -> Base)
            (HQ : ∀ k X R X' R', (∀n, X n = X' n)
                               → (∀n, R n = R' n)
                               →  Q k X R -> Q k X' R')
            (IHQ : ∀ k s X R,
                       ⟪s,X,R⟫ₛ
                    → (∀ k' s' X' R',
                           ⟪s',X',R'⟫ₛ
                         → ⟪k',s',X',R'⟫ ≺ₘ ⟪k,s,X,R⟫
                         → Q k' X' R')
                    → Q k X R)
             .

  Let Q' : (nat → rel₁ U * rel₂ U) * nat → Base :=
      λ '(σ,k), Q k (λ n, fst (σ n)) (λ n, snd (σ n)).

  Theorem afs_seq_facile_ind k X R : (∀n, afs (X n) (R n)) → Q k X R.
  Proof.
    generalize (wf_upto_lex_seq_and_nat (@wf_upto_lt_afsw U)).
    unfold prj_seq; intros E H.
    set (s' (n : nat) := (existT _ (◩,(X n,R n)) (H n) : afsw _)).
    change (Q' (fun n => afsw_forget (s' n),k)).
    apply (E Q') with (a := (s',k)); clear E.
    + intros ? ? ? ?; apply HQ; intro; f_equal; auto.
    + intros (w1,k1) Hw1.
      apply IHQ with (fun n => afsw_witness (w1 n)).
      * intros n; destruct (w1 n) as ((?,(?,?)) & ?); auto.
      * intros k2 s2 x2 r2 c2 H1.
        specialize (Hw1 (fun n => existT _ (s2 n,(x2 n,r2 n)) (c2 n),k2)).
        apply Hw1.
        revert H1.
        intros [ G1 | i <- G1 G2 G3 G5 G6 G7 G8 ]; [ left | right ].
        - destruct (w1 k1) as ((?,(?,?)),?); simpl in *; auto.
        - split; auto; exists i; rsplit 2; auto.
          ++ destruct (w1 i) as ((?,(?,?)),?); simpl in *; auto.
          ++ intros j Hj; simpl.
             rewrite G7, G8; auto.
             destruct (w1 j) as ((?,(?,?)),?); simpl; auto.
  Qed.

End afs_seq_facile_ind.

Module afs_lex_notations.

  Notation "⟪ a , b , c ⟫ₐ" := (@afs_status_correct _ a b c).
  Notation "⟪ a , b , c ⟫ₛ" := (@afs_seq_correct _ a b c).

  Notation "⟪ a , b , c ⟫ ≺ ⟪ x , y , z ⟫" := (@lt_afs_status _ a b c x y z).
  Notation "⟪ a , b , c ⟫ ≺ k ]ₑ ⟪ x , y , z ⟫" := (@afs_seq_easier _ k a b c x y z).
  Notation "⟪ a , b , c , d ⟫ ≺ₘ ⟪ v , x , y , z ⟫" := (afs_seq_more_facile a b c d v x y z).

End afs_lex_notations.

Import afs_lex_notations.

Section easier_more_facile.

  Variables (U : Type)
            (k : nat)
            (s s' : nat → af_status)
            (X X' : nat → rel₁ U)
            (R R' : nat → rel₂ U).

  Fact easier_more_facile : s k = s' k → ⟪s,X,R⟫ ≺k]ₑ ⟪s',X',R'⟫ → ⟪k,s,X,R⟫ ≺ₘ ⟪k,s',X',R'⟫.
  Proof.
    intros E [ i H1 H2 H3 H4 ].
    constructor 2 with i; auto.
    + intros; apply H3; tlia.
    + intros; apply H4; tlia.
  Qed.

End easier_more_facile.

(*
Print lt_afs_status.

Print afs_seq_easier.
Check afs_higman_induction.

Print afs_seq_more_facile.
Check afs_kruskal_induction.
*)


