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
  Require Import idx vec dtree vtree.

From KruskalFinite
  Require Import finite choice.

Require Import base notations tactics
               insert combi_principle
               vtree_embed
               afs_lex afs_quasi_morphism
               universe.

Import idx_notations vec_notations
       vtree_notations vtree_embeddings_notations
       af_notations afs_lex_notations.

#[local] Reserved Notation "v '⊲' p ']' x '⇝' w" (at level 70, x at level 200, no associativity, format "v ⊲ p ] x  ⇝  w").
#[local] Notation "v ⊲ p ] x ⇝ w" := (@vinsert_graph _ x _ v p _ w).

Set Implicit Arguments.

Section combi_trees.

  Variables (A' A : Type) (X' : nat → rel₁ A') (X : nat → rel₁ A)
            (gev : vtree A' → vtree A → Prop)
            (D' : rel₁ (vtree A')).

  Notation ana := (λ t t', gev t' t).
  Notation vana := (vec_fall2 ana).
  Notation E' := (λ t, ∃s, s ≤st t ∧ D' s).

  (* We assume the analysis of well formed trees
     are finitely many *)
  Hypothesis fin_ana : ∀t, wft X t → fin (ana t).

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
  Local Lemma combi_trees n x' (v : vec _ n) t :
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

Section veldman_afs_nodes_lt.

  Variables (A : Type).

  Notation U := (universe A).
  Notation Utree := (vtree U).

  Notation "⦉ x ⦊₁" := (@univ_refl _ x) (at level 1, format "⦉ x ⦊₁").
  Notation "⦉ x , p , t ⦊₂" := (@univ_nest_1 _ _ x p t) (at level 1, format "⦉ x , p , t ⦊₂").

  Variables  (k : nat)
             (s : nat → af_status)
             (X : nat → rel₁ U)
             (R : nat → rel₂ U)
             (HXk : ∀n, k ≤ n → X n = X k)
             (HRk : ∀n, k ≤ n → R n = R k)
             (HXR : ⟪s,X,R⟫ₛ)
             (IHXR : ∀ s' X' R', ⟪s',X',R'⟫ₛ
                               → s' k = s k
                               → ⟪s',X',R'⟫ ≺k]ₑ ⟪s,X,R⟫
                               → afs (wft X') (vtree_upto_embed k R'))

             (i : nat) (Hik : S i < k) (HsT : s (S i) ≠ None)
             (α : U) (γ : vec Utree (S i)) (Hαγ : wft X ⟨α|γ⟩)
             (IHRγ : ∀p, afs (wft X) (vtree_upto_embed k R)↑(γ⦃p⦄)).

  Notation "x '≤[' k , R ']' y" := (vtree_upto_embed k R x y) (at level 70, format "x  ≤[ k , R ]  y").

  Local Fact X_α : X (S i) α.
  Proof. apply wft_fix in Hαγ as []; auto. Qed.

  Local Fact wft_γ p : wft X γ⦃p⦄.
  Proof. apply wft_fix in Hαγ as []; auto. Qed.

  Local Fact Rn_afs n : afs (X n) (R n).
  Proof. eapply afs_status_correct_afs; eauto. Qed.

  Hint Resolve X_α wft_γ Rn_afs : core.

  Unset Elimination Schemes.

  Inductive higman_lift_pred_i : U → Prop :=

    | higman_lift_pred_i_refl x :
                   X i x
                 → higman_lift_pred_i ⦉x⦊₁

    | higman_lift_pred_i_nest_1 (p : idx (S i)) x t :
                   X (S i) x
                 → wft X t
                 → higman_lift_pred_i ⦉x,p,t⦊₂
    .

  Inductive higman_lift_rel_i : U → U → Prop :=

    | higman_lift_rel_i_refl x y :
                   R i x y
                 → higman_lift_rel_i ⦉x⦊₁ ⦉y⦊₁

    | higman_lift_rel_i_nest_1 (p : idx (S i)) x s y t :
                   R (S i) x y
                 → (vtree_upto_embed k R)↑(γ⦃p⦄) s t
                 → higman_lift_rel_i ⦉x,p,s⦊₂ ⦉y,p,t⦊₂
    .

  Set Elimination Schemes.

  Notation X'i := higman_lift_pred_i.
  Notation R'i := higman_lift_rel_i.

  Hint Constructors higman_lift_pred_i higman_lift_rel_i : core.

  Local Fact higman_lift_pred_i_invert x' :
         X'i x'
       ↔ match x' with
         | ⦉x⦊₁ => X i x
         | @univ_nest_1 _ n x _ t => n = S i ∧ X (S i) x ∧ wft X t
         | _ => False
         end.
  Proof.
    split.
    + destruct 1; auto.
    + destruct x'; try easy; eauto.
      intros (-> & ? & ?); eauto.
  Qed.

  Local Fact higman_lift_pred_i_inv x' :
         X'i x' → { x | x' = ⦉x⦊₁ ∧ X i x }
                + { x : _ & { p : idx (S i) &  { t | x' = ⦉x,p,t⦊₂ ∧ X (S i) x ∧ wft X t } } }.
  Proof.
    intros H%higman_lift_pred_i_invert; revert H.
    destruct x' as [ | x | j x p t | ]; try easy.
    + left; eauto.
    + intros (-> & ? & ?); right.
      exists x, p, t; auto.
  Qed.

  (** by several applications of Ramsey's theorem (af_sum, af_product, af_dep_sum) 
      then transported via the magic of af rel morph  *)

  Local Lemma higman_lift_i_afs : afs X'i R'i.
  Proof.
    apply afs_iff_af_sub_rel.
    assert (forall p, af ((vtree_upto_embed k R)↑(γ⦃p⦄))⇓(wft X)) as H.
    1: intro; apply afs_iff_af_sub_rel; auto.
    generalize (Rn_afs i) (Rn_afs (S i)); intros H1 H2.
    apply afs_iff_af_sub_rel in H1, H2.
    generalize (af_sum H1 (af_dep_sum _ _ (fun p => af_product H2 (H p)))); clear H H1 H2.
    af rel morph (fun x y =>
         match x, proj1_sig y with
         | inl (exist _ x _), ⦉y⦊₁ => x = y
         | inr (existT _ p (exist _ x _,exist _ r _)), ⦉y,q,t⦊₂
                                  => x = y
                                  /\ r = t
                                  /\ exists e, p↺e = q
         | _, _ => False
         end).
    + intros (x & Hx).
      destruct (higman_lift_pred_i_inv Hx)
        as [ (x' & -> & Hx') | (x' & p & t & -> & H1 & H2) ].
      * exists (inl (exist _ _ Hx')); simpl; auto.
      * exists (inr (existT _ p (exist _ _ H1,exist _ _ H2))); simpl.
        repeat split; auto; exists eq_refl; auto.
    + intros [ (x1 & ?) | (p1,((x1&?),(t1&?))) ]
             [ (x2 & ?) | (p2,((x2&?),(t2&?))) ]
             ([ | y1 | j1 q1 y1 r1 | ] & ?) ([ | y2 | j2 q2 y2 r2 | ] & ?);
             simpl proj1_sig; cbn iota; try tauto.
      * intros; subst; auto; constructor; auto.
      * intros (-> & -> & <- & ?) (-> & -> & <- & ?); subst; simpl eq_rect in *.
        intros (<- & ? & ?).
        constructor 2; auto.
  Qed.

  Hint Resolve higman_lift_i_afs : core.

  Implicit Type c : af_choice.

  Notation "▣" := af_choice_full.
  Notation "◩" := af_choice_af.

  Section higman_lift_cases.

    (* case 1 : j ≠ i and j ≠ S i
       case 2 : j = i
       case 3 : j = S i and c = ◩
       case 4 : j = S i and c = ▣ *)

    Inductive higman_lift_case : af_choice → nat → Type :=
      | higman_lift_case_1 c j : j ≠ i
                               → j ≠ S i
                               → higman_lift_case c j
      | higman_lift_case_2 c   : higman_lift_case c i
      | higman_lift_case_3     : higman_lift_case ◩ (S i)
      | higman_lift_case_4     : higman_lift_case ▣ (S i)
      .

    Hint Constructors higman_lift_case : core.

    Local Fact higman_lift_cases c j : higman_lift_case c j.
    Proof.
      destruct (eq_nat_dec j i);
      destruct (eq_nat_dec j (S i));
      destruct c; subst; auto.
    Qed.

  End higman_lift_cases.

  Local Definition higman_lift_status c (j : nat) : af_status :=
    match higman_lift_cases c j with
    | higman_lift_case_1 _ _ _ => s j
    | higman_lift_case_2 _     => Some ◩
    | higman_lift_case_3       => Some ◩
    | higman_lift_case_4       => None
    end.

  Local Definition higman_lift_pred c j :=
    match higman_lift_cases c j with
    | higman_lift_case_1 _ _ _ => X j
    | higman_lift_case_2 _     => X'i
    | higman_lift_case_3       => X (S i)
    | higman_lift_case_4       => ⊥₁
    end.

  Local Definition higman_lift_rel c j :=
    match higman_lift_cases c j with
    | higman_lift_case_1 _ _ _ => R j
    | higman_lift_case_2 _     => R'i
    | higman_lift_case_3       => (R (S i))↑α
    | higman_lift_case_4       => ⊥₂
    end.

  Notation s' := higman_lift_status.
  Notation X' := higman_lift_pred.
  Notation R' := higman_lift_rel.

  Section higman_lift_eqs.

    Ltac solve :=
      intros; match goal with
        |- ?h ?c ?j = _ => unfold h; destruct (higman_lift_cases c j); auto; tlia; easy
      end.

    Local Fact higman_lift_status_neq c j :     j ≠ i → j ≠ S i → s' c j = s j.          Proof. solve. Qed.
    Local Fact higman_lift_status_eq_i c j :            j = i   → s' c j = Some ◩.       Proof. solve. Qed.
    Local Fact higman_lift_status_eq_Si_l c j : c = ◩ → j = S i → s' c j = Some ◩.       Proof. solve. Qed.
    Local Fact higman_lift_status_eq_Si_f c j : c = ▣ → j = S i → s' c j = None.         Proof. solve. Qed.

    Local Fact higman_lift_pred_neq c j :       j ≠ i → j ≠ S i → X' c j = X j.          Proof. solve. Qed.
    Local Fact higman_lift_pred_eq_i c j :              j = i   → X' c j = X'i.          Proof. solve. Qed.
    Local Fact higman_lift_pred_eq_Si_l c j :   c = ◩ → j = S i → X' c j = X (S i).      Proof. solve. Qed.
    Local Fact higman_lift_pred_eq_Si_f c j :   c = ▣ → j = S i → X' c j = ⊥₁.           Proof. solve. Qed.

    Local Fact higman_lift_rel_neq c j :        j ≠ i → j ≠ S i → R' c j = R j.          Proof. solve. Qed.
    Local Fact higman_lift_rel_eq_i c j :               j = i   → R' c j = R'i.          Proof. solve. Qed.
    Local Fact higman_lift_rel_eq_Si_l c j :    c = ◩ → j = S i → R' c j = (R (S i))↑α.  Proof. solve. Qed.
    Local Fact higman_lift_rel_eq_Si_f c j :    c = ▣ → j = S i → R' c j = ⊥₂.           Proof. solve. Qed.

  End higman_lift_eqs.

  (** ⟪S i,s' c,X' c,R' c⟫ is correct and smaller that k,s,X,R⟫ *)

  Local Fact higman_lift_correct c : ⟪s' c,X' c,R' c⟫ₛ.
  Proof.
    unfold s', X', R'; intros j.
    destruct (higman_lift_cases c j); simpl; auto.
    apply afs_inv; auto.
  Qed.

  Local Fact higman_lift_lt c : s (S i) = Some c → ⟪s' c,X' c,R' c⟫ ≺k]ₑ ⟪s,X,R⟫.
  Proof.
    intros H; constructor 1 with (S i); auto.
    + rewrite H; destruct c.
      * rewrite higman_lift_status_eq_Si_l, higman_lift_pred_eq_Si_l, higman_lift_rel_eq_Si_l; constructor; auto.
      * rewrite higman_lift_status_eq_Si_f, higman_lift_pred_eq_Si_f, higman_lift_rel_eq_Si_f; constructor; auto.
    + intros; rewrite higman_lift_pred_neq; auto; lia.
    + intros; rewrite higman_lift_rel_neq; auto; lia.
  Qed.

  (** The evaluation map that reconstructs a tree from the information
      hidden inside nodes: the process of extracting sub-trees and hidding
      then in nodes of X' i is the reverse map 

      Here we consider analysis/evaluation adapted to the case of the product
      embedding because the arity (1+i) of ⟨α|γ⟩ is smaller than k, so the
      analysis proceeds using insertion of a single sub-tree. 

      We call this analysis/evaluation relation hev_graph where the initial "h" 
      reminds the reference to the proof of Higman's theorem in Wim Veldman's paper. *)

  Reserved Notation "x '-[' c ']->' y" (at level 70, no associativity, format "x  -[ c ]->  y").
  Reserved Notation "x '=[' c ']=>' y" (at level 70, no associativity, format "x  =[ c ]=>  y").

   (* As rules

                v' =[c]=> v
        ------------------------  X i x
          ⟨⦉x⦊₁|v'⟩ -[c]-> ⟨x|v⟩


         v' =[c]=> u     u ⊲p] t ⇝ v
        ----------------------------- X (1+i) x and wft X t
          ⟨⦉x,p,t⦊₂|v'⟩ -[c]-> ⟨x|v⟩


             v' =[c]=> v
        --------------------- j <> {i,1+i} and X j x
         ⟨x|v'⟩ -[c]-> ⟨x|v⟩


             v' =[◩]=> v
        ---------------------  X (1+i) x
         ⟨x|v'⟩ -[◩]-> ⟨x|v⟩

      *)

  Inductive hev_graph : af_choice → Utree → Utree → Prop :=

    | hev_graph_eq_i1 c x (v' : vec _ i) v :
                 X i x
               → v' =[c]=> v
               → ⟨⦉x⦊₁|v'⟩ -[c]-> ⟨x|v⟩

    | hev_graph_eq_i2 c p x t (v' : vec _ i) u (v : vec _ (S i)) :
                 X (S i) x
               → wft X t
               → v' =[c]=> u
               → u ⊲p] t ⇝ v
               → ⟨⦉x,p,t⦊₂|v'⟩ -[c]-> ⟨x|v⟩

    | hev_graph_neq_i_Si c j x (v' : vec _ j) v :
                 i ≠ j
               → S i ≠ j
               → X j x
               → v' =[c]=> v
               → ⟨x|v'⟩ -[c]-> ⟨x|v⟩

    | hev_graph_eq_Si x (v' : vec _ (S i)) v :
                 X (S i) x
               → v' =[◩]=> v
               → ⟨x|v'⟩ -[◩]-> ⟨x|v⟩

  where "x -[ b ]-> y" := (hev_graph b x y)
   and  "u =[ c ]=> v" := (vec_fall2 (hev_graph c) u v).

  Hint Constructors hev_graph : core.

  (* The domain of hev_graph is adequate, ie it is defined exactly on
     well formed trees *)

  Local Fact hev_graph_wft c t' t : t' -[c]-> t → wft (X' c) t'.
  Proof.
    induction 1; apply wft_fix; split; auto.
    + rewrite higman_lift_pred_eq_i; auto.
    + rewrite higman_lift_pred_eq_i; auto.
    + rewrite higman_lift_pred_neq; auto.
    + rewrite higman_lift_pred_eq_Si_l; auto.
  Qed.

  Local Fact hev_graph_inv_wft c t' t : t' -[c]-> t → wft X t.
  Proof.
    induction 1; apply wft_fix; split; auto.
    apply (vinsert_fall (wft X)) in H3; tauto.
  Qed.

  Local Lemma hev_graph_total c t' : wft (X' c) t' → { t | t' -[c]-> t }.
  Proof.
    induction 1 as [ j x' v' H1 H2 IH2 ] using wft_rect.
    vec reif IH2 as (v & Hv).
    destruct (higman_lift_cases c j) as [ c j H3 H4 | c | | ].
    + rewrite higman_lift_pred_neq in H1; eauto.
    + rewrite higman_lift_pred_eq_i in H1; auto.
      apply higman_lift_pred_i_inv in H1 as [ (x & -> & ?) | (x & q & t & -> & ? & ?) ].
      * exists ⟨x|v⟩; eauto.
      * destruct (vinsert_total t v q) as ([j u] & Hu); simpl in Hu.
        generalize (vinsert_length Hu); intros ->.
        exists ⟨x|u⟩; eauto.
    + rewrite higman_lift_pred_eq_Si_l in H1; eauto.
    + rewrite higman_lift_pred_eq_Si_f in H1; tauto.
  Qed.

  Local Corollary hev_graph_vec_total c n (v' : vec _ n) : vec_fall (wft (X' c)) v' → { v | v' =[c]=> v }.
  Proof.
    intros H.
    generalize (fun p => hev_graph_total c _ (H p)); intros H'.
    vec reif H' as ?; auto.
  Qed.

  Local Theorem hev_graph_domain c t' : (∃t, t' -[c]-> t) ↔ wft (X' c) t'.
  Proof.
    split.
    + intros (t & Ht); revert Ht; apply hev_graph_wft.
    + intros H; destruct hev_graph_total with (1 := H); eauto.
  Qed.

  Section hev_graph_inv_left.

    (** we study the output t depending on the shape of input t' in t' -[c]-> t *)

    Let shape c t j x' (v' : vec _ j) :=
        i = j ∧ match x' with
        | ⦉x⦊₁ => X i x ∧ ∃v, v' =[c]=> v ∧ ⟨x|v⟩ = t
        | ⦉x,p,a⦊₂ => ∃u, v' =[c]=> u ∧ X (S i) x ∧ ∃e (v : vec _ (S i)), u ⊲p↺e] a ⇝ v ∧ ⟨x|v⟩ = t
        | _ => False
        end
      ∨ (j ≠ i  ∧ j ≠ S i ∧ X j x' ∧ ∃v, v' =[c]=> v ∧ ⟨x'|v⟩ = t)
      ∨ (j = S i ∧ X j x' ∧ c = ◩  ∧ ∃v, v' =[◩]=> v ∧ ⟨x'|v⟩ = t).

    Local Fact hev_graph_inv_left c t' t : t' -[c]-> t → match t' with ⟨x'|v'⟩ => shape c t x' v' end.
    Proof.
      induction 1 as [ ? ? ? v | ? ? ? ? ? u | | ].
      + left; rsplit 2; auto; exists v; auto.
      + left; split; auto.
        exists u; rsplit 2; auto.
        exists eq_refl; simpl; eauto.
      + right; left; rsplit 3; eauto.
      + right; right; rsplit 3; eauto.
    Qed.

    (** Specialized inversions, used in hev_fun and hev_quasi_morphism below *) 

    Local Fact hev_graph_eq_1_inv c x (v' : vec _ i) t :
       ⟨⦉x⦊₁|v'⟩ -[c]-> t → X i x ∧ ∃v, v' =[c]=> v ∧ ⟨x|v⟩ = t.
    Proof. intros [ | [ [] | [] ] ]%hev_graph_inv_left; tlia; tauto. Qed.

    Local Fact hev_graph_eq_2_inv c p x a (v' : vec _ i) t :
       ⟨⦉x,p,a⦊₂|v'⟩ -[c]-> t → ∃u, v' =[c]=> u ∧ X (S i) x ∧ ∃v : vec _ (S i), u ⊲p] a ⇝ v ∧ ⟨x|v⟩ = t.
    Proof.
      intros [ (_ & v & ? & ? & ? & ? & ? & ?) | [ [] | [] ] ]%hev_graph_inv_left; tlia.
      eq refl; exists v; eauto.
    Qed.

    Local Fact hev_graph_neq_inv c j x (v' : vec _ j) t :
       j ≠ i → j ≠ S i → ⟨x|v'⟩ -[c]-> t → X j x ∧ ∃v, v' =[c]=> v ∧ ⟨x|v⟩ = t.
    Proof. intros ? ? [ [] | [ (? & ? & ? & ? & ? & <-) | [] ] ]%hev_graph_inv_left; tlia || eauto. Qed.

    Local Fact hev_graph_eq_Si_inv x (v' : vec _ (S i)) t :
       ⟨x|v'⟩ -[◩]-> t → X (S i) x ∧ ∃v, v' =[◩]=> v ∧ ⟨x|v⟩ = t.
    Proof. intros [ [] | [ (? & ? & _) | (_ & ? & ? & v & ? & <-)  ] ]%hev_graph_inv_left; tlia || eauto. Qed.

  End hev_graph_inv_left.

  Local Theorem hev_graph_fun c t' t₁ t₂ : t' -[c]-> t₁ → t' -[c]-> t₂ → t₁ = t₂.
  Proof.
    intros H1; revert H1 t₂.
    induction 1 as [ c x v' v H1 H2 IH2
                   | c p x a v' u v H1 H2 H3 IH3 H4
                   | c j x v' v H1 H2 H3 H4 IH4
                   | x v' v H1 H2 IH2 ]; intros t2 Ht2.
    + apply hev_graph_eq_1_inv in Ht2 as (_ & ? & ? & <-); f_equal; vec ext; auto.
    + apply hev_graph_eq_2_inv in Ht2 as (u' & ? & ? & m' & H6 & <-).
      assert (u = u') as <- by (vec ext; auto).
      destruct (vinsert_fun H4 H6) as (? & ?); eq refl; subst m'; auto.
    + apply hev_graph_neq_inv in Ht2 as (_ & ? & ? & <-); auto; f_equal; vec ext; auto.
    + apply hev_graph_eq_Si_inv in Ht2 as (_ & ? & ? & <-); auto; f_equal; vec ext; auto.
  Qed.

  Local Corollary hev_graph_vec_fun c n (v' v₁ v₂ : vec _ n) : v' =[c]=> v₁ → v' =[c]=> v₂ → v₁ = v₂.
  Proof. intros ? ?; vec ext; eapply hev_graph_fun; eauto. Qed.

  Section hev_graph_inv_right.

    (** We study the input t' depending on the shape of the output t *)

    Let shape c t' j x (v : vec _ j) :=
               (j = i ∧ X i x ∧ ∃v', ⟨⦉x⦊₁|v'⟩ = t' ∧ v' =[c]=> v)
             ∨ (j = S i ∧ X (S i) x ∧ ∃vin : vinsert_in _ i,
                    match vin with c_vinsert_in a u p
                      => wft X a ∧ ∃v', ⟨⦉x,p,a⦊₂|v'⟩ = t' ∧ v' =[c]=> u
                    end ∧ is_vinsert_in v vin)
             ∨ (j ≠ i ∧ j ≠ S i ∧ X j x ∧ ∃v', ⟨x|v'⟩ = t' ∧ v' =[c]=> v)
             ∨ (c = ◩ ∧ j = S i ∧ X (S i) x ∧ ∃v', ⟨x|v'⟩ = t' ∧ v' =[◩]=> v).

    Local Fact hev_graph_inv_right c t' t :
            t' -[c]-> t → match t with ⟨x|v⟩ => shape c t' x v end.
    Proof.
      induction 1 as [ c x v' v H1 H2 _
                     | c p x a v' u v H1 H2 H3 _ H4
                     | c j x v' v H1 H2 H3 H4 _
                     | x v' v H1 H2 _ ]; simpl.
      + left; rsplit 2; auto; eauto.
      + right; left; rsplit 2; auto.
        exists (c_vinsert_in a u p); simpl; split; eauto.
      + do 2 right; left; split; eauto.
      + do 3 right; split; eauto.
    Qed.

    Local Fact hev_analysis c j x (v : vec _ j) t' :
            t' -[c]-> ⟨x|v⟩ ↔ shape c t' x v.
    Proof.
      split.
      + apply hev_graph_inv_right.
      + intros [ (-> & ? & ? & <- & ?)
             | [ (-> & ? & [] & (? & ? & <- & ?) & ?)
             | [ (? & ? & ? & ? & <- & ?)
               | (-> & -> & ? & ? & <- & ?)  ] ] ]; simpl in *; eauto.
    Qed.

  End hev_graph_inv_right.

  (** A nice high-level argument based on combinations of
     finitary relations, application of fin_* closure theorems *)

  Local Fact neq_nat_dec (a b : nat) : { a ≠ b } + { ¬ a ≠ b }.
  Proof. destruct (eq_nat_dec a b) as [ -> | ? ]; auto. Qed.

  Hint Resolve vinsert_fin eq_nat_dec lt_dec le_dec neq_nat_dec : core.

  (* Ana(lysis) is the converse of evaluation *)
  Notation ana c := (λ t t', t' -[c]-> t).

  (* Vector/product analysis *)
  Notation vana c := (λ v v', v' =[c]=> v).

  (* hev has finite inverse image, ie ana(lisys) is finitary *)
  Local Theorem fin_ana c t : wft X t → fin (ana c t).
  Proof.
    induction 1 as [ j x v Hx Hv IHv ] using wft_rect.
    finite eq (hev_analysis c x v).
    finite union.
    + destruct (eq_nat_dec j i) as [ -> | ].
      2: now finite as ⊥₁.
      repeat finite cst left.
      finite compose.
      finite as (vec_fall2 (ana c) v).
      split; apply vec_fall2_swap.
    + destruct (eq_nat_dec j (S i)) as [ -> | ].
      2: now finite as ⊥₁.
      repeat finite dec left.
      finite compose.
      intros [ a u p ] H; simpl in *.
      apply (vinsert_fall _ H) in Hv as [H2 H3].
      repeat finite dec left.
      finite compose.
      finite as (vec_fall2 (ana c) u).
      1: split; apply vec_fall2_swap.
      apply fin_vec_fall2.
      apply vinsert_idx_eq in H as (? & H).
      intro; rewrite H; auto.
    + repeat finite dec left.
      finite compose.
      finite as (vec_fall2 (ana c) v).
      split; apply vec_fall2_swap.
    + destruct c.
      2: now finite as ⊥₁.
      destruct (eq_nat_dec j (S i)) as [ -> | ].
      2: now finite as ⊥₁.
      repeat finite dec left.
      finite compose.
      finite as (vec_fall2 (ana ◩) v).
      split; apply vec_fall2_swap.
  Qed.

  Hint Resolve fin_ana : core.

(*
  Local Corollary fin_vana n c (v : vec _ n) : vec_fall (wft X) v → fin (vana c v).
  Proof. intro; apply fin_vec_fall2 with (R := ana c); eauto. Qed.


  Hint Resolve fin_vana : core.
*)
  (** An analysis on (X',R') is disapointing if either
        - its root node is above "α" wrt to R at arity 1+i
        - its root node has arity i and is of shape ⦉p,x,t⦊₂ and t embeds γ⦃p⦄
   *)

  Unset Elimination Schemes.

  Inductive disapointing : Utree → Prop :=
    | disapointing_gt x (v : vec _ (S i)) :  R (S i) α x → disapointing ⟨x|v⟩
    | disapointing_eq p x t (v : vec _ i) : γ⦃p⦄ ≤[k,R] t → disapointing ⟨⦉x,p,t⦊₂|v⟩.

  Set Elimination Schemes.

  Notation D' := disapointing.

  Hint Constructors sub_dtree disapointing : core.

  Local Fact disapointing_inv t' :
        D' t'
      → (∃x (v : vec _ (S i)), R (S i) α x ∧ t' = ⟨x|v⟩)
      ∨ (∃ p x t (v : vec _ i), γ⦃p⦄ ≤[k,R] t ∧ t' = ⟨⦉x,p,t⦊₂|v⟩).
  Proof.
    destruct 1 as [ | p ]; [ left | right ]; eauto.
    exists p; eauto.
  Qed.

  Local Fact disapointing_length n x' (v' : vec Utree n) : D' ⟨x'|v'⟩ → n = i ∨ n = S i.
  Proof. intros [ (? & ? & ? & ?) | (? & ? & ? & ? & ? & ?) ]%disapointing_inv; dtree discr. Qed.

  Local Fact disapointing_inv_lt x' (v : vec _ (S i)) : D' ⟨x'|v⟩ → R (S i) α x'.
  Proof.
    intros [ (? & ? & ? & H) | (? & ? & ? & ? & ? & ?) ]%disapointing_inv; dtree discr.
    dtree inj H; subst; auto.
  Qed.

  Local Fact disapointing_inv_1 x (v : vec _ i) : ¬ D' ⟨⦉x⦊₁|v⟩.
  Proof. intros [ (? & ? & ? & ?) | (? & ? & ? & ? & ? & ?) ]%disapointing_inv; dtree discr. Qed.

  Local Fact disapointing_inv_2 p x t (v : vec _ i) :
         D' ⟨⦉x,p,t⦊₂|v⟩ → γ⦃p⦄ ≤[k,R] t.
  Proof.
    intros [ (? & ? & ? & ?) | (? & ? & ? & ? & ? & H) ]%disapointing_inv; dtree discr.
    dtree inj H; univ inj H; subst; eauto.
  Qed.

  (* An analysis is exceptional is one of its sub-trees in disapointing *)
  Local Definition has_disapointing t := ∃s, s ≤st t ∧ D' s.
  Notation E' := has_disapointing.

  Local Fact disap_has_disap : D' ⊆₁ E'.
  Proof. intros t; exists t; auto. Qed.

  Hint Resolve sub_dtree_trans : core.

  Local Fact sub_vtree_has_disap r t : r ≤st t → E' r → E' t.
  Proof. intros ? (w & ? & ?); exists w; eauto. Qed.

  Hint Resolve disap_has_disap sub_vtree_has_disap : core.

  (* Here we use left inversion lemma for hev_graph *)

  Lemma hev_quasi_morph c t1' t2' t1 t2 :
           t1' ≤[k,R' c] t2'
         → t1' -[c]-> t1
         → t2' -[c]-> t2
         → t1  ≤[k,R] t2 ∨ E' t1'.
  Proof.
    intros H3 H1 H2; revert H3 t1 t2 H1 H2.
    induction 1 as [ t j x' v' p _ IH
                   | j x1' v1' x2' v2' H0 H1 _ IH
                   | j x1' v1' m x2' v2' H0 H1 _ IH ]; intros t1 t2 E1 E3.
    + specialize (fun t => IH _ t E1); clear E1.
      apply hev_graph_inv_left in E3
        as [ (<- & E3) | [ (H1 & H2 & H3 & v & E3 & <-) | (H1 & H2 & -> & v & E3 & <-) ] ].
      (* cases i ≠ j *)
      2,3: destruct (IH _ (E3 _)); eauto with vtree_db.
      (* case j = i *)
      destruct x' as [ | x | n x q a | ]; try easy.
      * destruct E3 as (E4 & v & E3 & <-).
        destruct (IH _ (E3 _)); eauto with vtree_db.
      * destruct E3 as (u & E3 & E4 & e & v & E6 & <-); eq refl.
        destruct (IH _ (E3 _)); auto.
        apply vinsert_idx_eq in E6 as (? & E6).
        left; constructor 1 with (vinsert_idx q p); rewrite <- E6; auto.
    + (* j < S i, so either j < i or j = i *)
      destruct (higman_lift_cases c j) as [ c j Hj1 Hj2 | c | | ].
      * (* j ≠ i and j ≠ S i *)
         rewrite higman_lift_rel_neq in H1; auto.
        apply hev_graph_neq_inv in E3 as (E3 & v2 & E4 & <-); auto.
        apply hev_graph_neq_inv in E1 as (E1 & v1 & E2 & <-); auto.
        specialize (fun p => IH p _ _ (E2 _) (E4 _)).
        apply finite_choice in IH as [ IH | [] ]; fin auto; eauto with vtree_db.
      * (* j = i *)
        rewrite higman_lift_rel_eq_i in H1; auto.
        destruct H1 as [ x1 x2 G1 | p x1 r1 x2 r2 G1 G2 ].
        - apply hev_graph_eq_1_inv in E3 as (E3 & v2 & E4 & <-).
          apply hev_graph_eq_1_inv in E1 as (E1 & v1 & E2 & <-).
          specialize (fun p => IH p _ _ (E2 _) (E4 _)).
          apply finite_choice in IH as [ IH | [] ]; fin auto; eauto with vtree_db.
        - apply hev_graph_eq_2_inv in E3 as (u2 & E4 & G5 & v2 & G4 & <-).
          apply hev_graph_eq_2_inv in E1 as (u1 & E2 & G6 & v1 & G3 & <-).
          destruct G2 as [ G2 | ]; auto.
          specialize (fun p => IH p _ _ (E2 _) (E4 _)).
          apply finite_choice in IH as [ IH | [] ]; fin eauto.
          left; constructor 2; auto; tlia.
          apply (vinsert_fall2 _ G3 G4); split; auto.
      * (* j = S i and c = ◩ *)
        rewrite higman_lift_rel_eq_Si_l in H1; auto.
        apply hev_graph_eq_Si_inv in E1 as (E1 & v1 & E2 & <-).
        apply hev_graph_eq_Si_inv in E3 as (E3 & v2 & E4 & <-).
        specialize (fun p => IH p _ _ (E2 _) (E4 _)).
        apply finite_choice in IH as [ IH | [] ]; fin eauto.
        destruct H1; eauto with vtree_db.
      * (* j = S i and c = ▣ *)
        rewrite higman_lift_rel_eq_Si_f in H1; tauto.
    + (* k <= j *)
      rewrite higman_lift_rel_neq in H1; tlia.
      generalize (vec_embed_length IH); intros Hm.
      apply hev_graph_neq_inv in E3 as (E3 & v2 & E4 & <-); tlia.
      apply hev_graph_neq_inv in E1 as (E1 & v1 & E2 & <-); tlia.
      apply vec_embed_sub_vec_fall2 in IH as (v3' & IH & H3).
      destruct (vec_embed_fall2_inv H3 E4) as (? & <-%vec_prj_ext & G2).
      apply vec_embed_sub_vec_fall2 in G2 as (v3 & E5 & G3).
      specialize (fun p => IH p _ _ (E2 _) (E5 _)).
      apply finite_choice in IH as [ IH | [] ]; fin eauto.
      left; constructor 3; auto; tlia.
      apply vec_embed_sub_vec_fall2; eauto.
  Qed.

  (** An evaluation is exceptional if each of its analysis is exceptional *)
  Notation E c t := (ana c t ⊆₁ E').

  Section exceptional_vs_embedding.

    (** This proof may be a bit long and is only of informative nature.
        We do not need this result to establish the thm kruskal_afs_nodes_lt
        below but we point out the nice characterization of exceptional
        evaluations. *)
    Local Remark embed_exceptional c t : wft X t → ⟨α|γ⟩ ≤[k,R] t → E c t.
    Proof.
      induction 1 as [ m y w Hy Hw IHw ] using wft_rect.
      intros Hyw [ n' x' v' ] [ (<- & Hx') | [ (? & ? & ? & v & E1 & E2) | (-> & ? & -> & v & E1 & E2)] ]%hev_graph_inv_left.
      + destruct x' as [ | x | n p x t | ]; try easy.
        * destruct Hx' as (? & v & E1 & E2).
          dtree inj E2; subst y.
          apply vtree_upto_embed_inv_right in Hyw
            as [ (p & Hp) | [ (? & ? & ? & ?) | (? & ? & ?) ] ]; tlia.
          specialize (IHw _ Hp _ (E1 _)); eauto with vtree_db.
        * destruct Hx' as (u & H1 & H2 & -> & v & E1 & E2).
          dtree inj E2; subst y; simpl in *.
          apply vtree_upto_embed_inv_right in Hyw
            as [ (q & Hq) | [ (e & H3 & H4 & H5) | (? & ? & ?) ] ]; tlia; eq refl.
          - (* ⟨α|γ⟩ embeds into a component v⦃q⦄ *)
            specialize (IHw _ Hq).
            (* where is v⦃q⦄ in v = u⊲p]t ? *)
            destruct (vinsert_prj E1 q) as [ (<- & <-) | (j & E2) ].
            ++ (* v⦃q⦄ = t *)
               apply disap_has_disap.
               constructor.
               revert Hq; apply vtree_sub_upto_embed; eauto.
            ++ (* v⦃q⦄ = u⦃j⦄ *)
               rewrite E2 in IHw.
               specialize (IHw _ (H1 _)); eauto with vtree_db.
          - (* γ⦃z⦄ ≤[k,R] v⦃z⦄ for any z 
               but v⦃p⦄ = t hence γ⦃p⦄ ≤[k,R] t *)
            apply vinsert_eq in E1 as <-; eauto.
      + dtree inj E2; subst x'.
        apply vtree_upto_embed_inv_right in Hyw
          as [ [] | [ (? & ? & ? & ?) | (? & ? & ?) ] ]; tlia; eauto.
      + dtree inj E2; subst x'.
        apply vtree_upto_embed_inv_right in Hyw
          as [ [] | [ (? & ? & ? & ?) | (? & ? & ?) ] ]; tlia; eauto.
    Qed.

    (* Either 
       - v (of arity n) has an exceptional sub-tree
       - or there is disapointing tree of arity n rooted at x' *)
    Let Esub_or_D' c n (v : vec _ n) x' :=
      (∃p, E c v⦃p⦄) ∨ (∃v' : vec _ n, D' ⟨x'|v'⟩).

    Local Lemma E_hereditary c n x' (v : vec _ n) t :
            vec_fall (wft X) v
          → E c t
          → (∀v', vana c v v' → ana c t ⟨x'|v'⟩)
          → Esub_or_D' c v x'.
    Proof.
      intros Hv Ht1 Ht2; red.
      destruct combi_trees
        with (1 := fin_ana c)
             (2 := Hv)
             (3 := Ht1)
             (4 := Ht2) as [ | (? & _ & ?)]; eauto.
    Qed.

    Local Fact Rαx_choice_embed x (v : vec _ (S i)) :
             R (S i) α x
           → (∀ u q y, 
                 u ⊲q] y ⇝ v 
               →   γ⦃q⦄ ≤[k,R] y
               ∨ ⟨α|γ⟩ ≤[k,R] ⟨x|v⟩)
           → ⟨α|γ⟩ ≤[k,R] ⟨x|v⟩.
    Proof. 
      intros ? [ ? | (_ & _ & _ & _ & ?) ]%vinsert_choice; auto.
      constructor 2; auto.
      apply vinsert_any_vec_fall2; auto.
    Qed.

    Local Lemma vinsert_choice_embed c x (v : vec _ (S i)) u q y :
             u ⊲q] y ⇝ v
           → (∀p, E c v⦃p⦄ → ⟨α|γ⟩ ≤[k,R] v⦃p⦄)
           → Esub_or_D' c u ⦉x,q,y⦊₂
           →  γ⦃q⦄ ≤[k,R] y
           ∨ ⟨α|γ⟩ ≤[k,R] ⟨x|v⟩.
    Proof.
      intros [_ Hv]%vinsert_idx_eq IHv [ (p & Hp) | (v' & Hv')].
      + right.
        constructor 1 with (vinsert_idx q p).
        apply IHv; rewrite <- Hv; auto.
      + left.
        now apply disapointing_inv_2 in Hv'.
    Qed.

    Local Lemma E_embed c (Hc : s (S i) = Some c) t :
          wft X t → E c t → ⟨α|γ⟩ ≤[k,R] t.
    Proof.
      induction 1 as [ j x v Hx Hv0 IHv ] using wft_rect; intros Hv.
      (* We specialize E_hereditary on c so the next destruct with instanciate c *)
      generalize (λ j x' u' H, @E_hereditary c j x' u' _ H Hv); intros hereditary.
      destruct (higman_lift_cases c j) as [ c j H1 H2 | c | | ].
      + (* case j ≠ i and j ≠ S i *)
        destruct (hereditary _ x v) as [ [] | (v' & H4) ]; eauto with vtree_db.
        apply disapointing_length in H4; lia.
      + (* case j = i *)
        destruct (hereditary _ ⦉x⦊₁ v) as [ [] | (v' & H4) ]; eauto with vtree_db.
        now apply disapointing_inv_1 in H4.
      + (* case j = S i and c = ◩ *)
        destruct (hereditary _ x v) as [ [] | (v' & H4) ]; eauto with vtree_db.
        apply Rαx_choice_embed.
        * now apply disapointing_inv_lt in H4.
        * (* hereditary is called (again) by eauto *)
          intros u q y Hu.
          apply vinsert_choice_embed with (c := ◩) (1 := Hu); auto.
          destruct (proj2 (vinsert_fall _ Hu) Hv0); eauto.
      + (* case j = S i and c = ▣ *)
        apply Rαx_choice_embed; trivial.
        * (* R (S i) is total on X (S i) so ... *)
          specialize (HXR (S i)).
          rewrite Hc in HXR; simpl in HXR.
          apply HXR; auto.
        * (* hereditary is called by eauto *)
          intros u q y Hu.
          apply vinsert_choice_embed with (c := ▣) (1 := Hu); auto.
          destruct (proj2 (vinsert_fall _ Hu) Hv0); eauto.
    Qed.

  End exceptional_vs_embedding.

  Section af_choice.

   (* We freeze c such that Some c = sT *)

    Local Definition af_choice_sT_pwc : { c | s (S i) = Some c }.
    Proof. destruct (s (S i)); try easy; eauto. Qed.

    Local Definition af_choice_sT := proj1_sig af_choice_sT_pwc.

    Local Fact af_choice_sT_spec : s (S i) = Some af_choice_sT.
    Proof. apply (proj2_sig af_choice_sT_pwc). Qed.

  End af_choice.

  Notation c₀ := af_choice_sT.
  Notation Hc₀ := af_choice_sT_spec.

  Hint Resolve higman_lift_correct higman_lift_lt Hc₀ : core.

  Local Theorem exceptional_embed t : wft X t → E c₀ t → ⟨α|γ⟩ ≤[k,R] t.
  Proof. apply E_embed; auto. Qed.

  (** Exceptional evaluations are "exactly" those which embed ⟨α|γ⟩ *)

  Local Remark exceptional_iff_embed t : wft X t → E c₀ t ↔ ⟨α|γ⟩ ≤[k,R] t.
  Proof. split; [ apply exceptional_embed | apply embed_exceptional ]; auto. Qed.

  Local Fact upto'_afs : afs (wft (X' c₀)) (vtree_upto_embed k (R' c₀)).
  Proof.
    apply IHXR with (s' c₀); auto.
    rewrite higman_lift_status_neq; auto; lia.
  Qed.

  Hint Resolve hev_graph_wft
               hev_graph_inv_wft
               hev_graph_fun
               hev_graph_total
               hev_quasi_morph
               exceptional_embed : core.

  Theorem veldman_afs_nodes_lt : afs (wft X) (vtree_upto_embed k R)↑⟨α|γ⟩.
  Proof.
    generalize upto'_afs.
    afs quasi morph (hev_graph c₀) E'; eauto.
  Qed.

End veldman_afs_nodes_lt.
