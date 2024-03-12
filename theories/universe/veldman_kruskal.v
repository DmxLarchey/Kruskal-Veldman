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
  Require Import idx vec vtree.

From KruskalFinite
  Require Import finite choice.

Require Import base notations tactics
               intercal vtree_embed
               afs_lex afs_quasi_morphism
               combi_principle
               universe.

Import 
       idx_notations vec_notations vtree_notations vtree_embeddings_notations
       af_notations afs_lex_notations.

Set Implicit Arguments.

Section kruskal_afs_nodes_ge.

  Variables (A : Type).

  Notation U := (universe A).
  Notation Utree := (vtree U).

  Notation "⦉ x ⦊₁" := (@univ_refl _ x) (at level 1, format "⦉ x ⦊₁").
  Notation "⦉ x , v ⦊₂" := (@univ_nest_2 _ _ x v) (at level 1, format "⦉ x , v ⦊₂").

  Variables  (k : nat)
             (s : nat → af_status)
             (X : nat → rel₁ U)
             (R : nat → rel₂ U)
             (HXk : ∀n, k ≤ n → X n = X k)
             (HRk : ∀n, k ≤ n → R n = R k)
             (HXR : ⟪s,X,R⟫ₛ)
             (IHXR : ∀ k' s' X' R', (∀n, k' ≤ n → X' n = X' k')
                                  → (∀n, k' ≤ n → R' n = R' k')
                                  → ⟪s',X',R'⟫ₛ
                                  → ⟪k',s',X',R'⟫ ≺ₘ ⟪k,s,X,R⟫
                                  → afs (wft X') (vtree_upto_embed k' R'))

             (i : nat) (Hik : k ≤ S i) (Hsk : s k ≠ None)
             (α : U) (γ : vec Utree (S i)) (Hαγ : wft X ⟨α|γ⟩)
             (IHRγ : forall p, afs (wft X) (vtree_upto_embed k R)↑(γ⦃p⦄)).

  Notation "x '≤[' k , R ']' y" := (vtree_upto_embed k R x y) (at level 70, format "x  ≤[ k , R ]  y").

  Local Fact X_α j : k ≤ j → X j α.
  Proof.
    intro; rewrite HXk, <- (@HXk (S i)); auto.
    apply wft_fix in Hαγ as []; auto.
  Qed.

  Local Fact wft_γ p : wft X γ⦃p⦄.
  Proof. apply wft_fix in Hαγ as []; auto. Qed.

  Local Fact Rn_afs n : afs (X n) (R n).
  Proof. eapply afs_status_correct_afs; eauto. Qed.

  Hint Resolve X_α wft_γ Rn_afs : core.

  Unset Elimination Schemes.

  Inductive kruskal_lift_pred_i : U → Prop :=

    | kruskal_lift_pred_i_refl x :
                   X i x
                 → kruskal_lift_pred_i ⦉x⦊₁

    | kruskal_lift_pred_i_nest x (m : hvec (vtree U) (S i)) :
                   i < vintercal_size m
                 → X (vintercal_size m) x
                 → (∀ p q, wft X (lvec_vec m⦃p⦄)⦃q⦄)
                 → kruskal_lift_pred_i ⦉x,m⦊₂
    .

  (* If i < k then R (min i k) = R i
     If k <= i then R (min i k) = R k = R i because i >= k *)

  Inductive kruskal_lift_rel_i : U → U → Prop :=

    | kruskal_lift_rel_i_refl x y :
                    R i x y
                  → kruskal_lift_rel_i ⦉x⦊₁ ⦉y⦊₁

    | kruskal_lift_rel_i_nest x₁ x₂ (w₁ w₂ : vec _ (S i)) :
                    R k x₁ x₂
                  → (∀p, vec_embed (vtree_upto_embed k R)↑(γ⦃p⦄) (lvec_vec w₁⦃p⦄) (lvec_vec w₂⦃p⦄))
                  → kruskal_lift_rel_i ⦉x₁,w₁⦊₂ ⦉x₂,w₂⦊₂
    .

  Set Elimination Schemes.

  Notation X'i := kruskal_lift_pred_i.
  Notation R'i := kruskal_lift_rel_i.

  Hint Constructors kruskal_lift_pred_i kruskal_lift_rel_i : core.

  Local Fact kruskal_lift_pred_i_invert x' :
         X'i x'
       ↔ match x' with
         | ⦉x⦊₁ => X i x
         | @univ_nest_2 _ n x m => { e : n = S i |
                                     i < vintercal_size m↺e
                                   ∧ X (vintercal_size m↺e) x
                                   ∧ ∀ p q, wft X (lvec_vec m⦃p⦄)⦃q⦄ }
         | _ => False
         end.
  Proof.
    split.
    + destruct 1; eauto; exists eq_refl; auto.
    + destruct x'; try easy; eauto.
      intros (-> & ? & ? & ?); eauto.
  Qed.

  Local Fact kruskal_lift_pred_i_inv x' :
         X'i x'
       → { x | x' = ⦉x⦊₁ ∧ X i x }
       + { x : _ & { m : vec _ (S i) |
               x' = ⦉x,m⦊₂
             ∧ i < vintercal_size m
             ∧ X (vintercal_size m) x
             ∧ ∀ p q, wft X (lvec_vec m⦃p⦄)⦃q⦄
         } }.
  Proof.
    intros H%kruskal_lift_pred_i_invert; revert H.
    destruct x' as [ | x | | i' x m ]; try easy.
    + left; eauto.
    + right.
      destruct H as (-> & ? & ? & ?).
      exists x, m; auto.
  Qed.

  (** by several applications of Ramsey's theorem,
        af_sum, af_product, af_dep_product and Higman's lemma

      then transported via the magic of af_relmap  *)

  Local Lemma kruskal_lift_i_afs : afs X'i R'i.
  Proof.
    apply afs_iff_af_sub_rel.
    (* We build the combination *)
    assert (forall p, af (lvec_embed (vtree_upto_embed k R)↑(γ⦃p⦄)⇓(wft X))) as H.
    1: intros; apply af_lvec_embed, afs_iff_af_sub_rel; auto.
    generalize (Rn_afs i) (Rn_afs k); intros H1 H2.
    apply afs_iff_af_sub_rel in H1, H2.
    generalize (af_sum H1 (af_product H2 (af_dep_product _ _ H))); clear H H1 H2.
    (* We project the combination *)
    af rel morph (fun x y =>
      match x, proj1_sig y with
        | inl (exist _ x _), ⦉y⦊₁ => x = y
        | inr (exist _ x _,f), @univ_nest_2 _ j y w => x = y /\ exists e : S i = j,
           forall p, lvec_map (@proj1_sig _ _) (f p) = w⦃p↺e⦄
        | _, _ => False
      end).
    + intros (x' & Hx').
      destruct (kruskal_lift_pred_i_inv Hx')
        as [ (x & -> & Hx) | (x & w & -> & H1 & H2 & H3) ].
      * exists (inl (exist _ _ Hx)); simpl; auto.
      * simpl.
        rewrite HXk in H2; tlia.
        exists (inr (exist _ x H2,
                      fun p => ⦑_,vec_set (fun q => exist _ _ (H3 p q))⦒)).
        split; auto; exists eq_refl; intros p; simpl.
        rewrite (lvec_pair_eq w⦃p⦄) at 4; f_equal.
        now vec ext; vec rew; simpl.
    + intros [ (x1 & ?) | ((x1 & ?) & g1) ] [ (x2 & ?) | ((x2 & ?) & g2) ]
             ([ | y1 | | j1 y1 w1 ] & ?) ([ | y2 | | j2 y2 w2 ] & ?); simpl proj1_sig; cbn iota; try easy.
      * intros <- <- H; constructor; auto.
      * intros (<- & ? & H1) (<- & ? & H2) (H3 & H4); eq refl.
        constructor; auto.
        intros p; specialize (H4 p).
        change (lvec_embed (vtree_upto_embed k R)↑(γ⦃p⦄) w1⦃p⦄ w2⦃p⦄).
        rewrite <- H1, <- H2.
        apply lvec_embed_lvec_map, H4.
  Qed.

  Hint Resolve kruskal_lift_i_afs : core.

  (* ▢ ▣ ◩ *)

  Implicit Type c : af_choice.

  Notation "▣" := af_choice_full.
  Notation "◩" := af_choice_af.

  Section kruskal_lift_cases.

    (* case1: j < i     case2: j = i
       case3: j > i (◩) case4: j > i (▣) *)

    Inductive kruskal_lift_case : af_choice → nat → Type :=
      | kruskal_lift_case_1 c j : j < i → kruskal_lift_case c j
      | kruskal_lift_case_2 c   :         kruskal_lift_case c i
      | kruskal_lift_case_3   j : i < j → kruskal_lift_case ◩ j
      | kruskal_lift_case_4   j : i < j → kruskal_lift_case ▣ j
      .

    Hint Constructors kruskal_lift_case : core.

    Local Fact kruskal_lift_cases c j : kruskal_lift_case c j.
    Proof. destruct (lt_eq_lt_dec i j) as [ [ | <- ] | ]; destruct c; auto. Qed.

  End kruskal_lift_cases.

  Local Definition kruskal_lift_status c (j : nat) : af_status :=
    match kruskal_lift_cases c j with
    | kruskal_lift_case_1 _ _ => s j
    | kruskal_lift_case_2 _   => Some ◩
    | kruskal_lift_case_3 _   => Some ◩
    | kruskal_lift_case_4 _   => None
    end.

  Local Definition kruskal_lift_pred c j :=
    match kruskal_lift_cases c j with
    | kruskal_lift_case_1 _ _ => X j
    | kruskal_lift_case_2 _   => X'i
    | kruskal_lift_case_3 _   => X (S i)
    | kruskal_lift_case_4 _   => ⊥₁
    end.

  Local Definition kruskal_lift_rel c j :=
    match kruskal_lift_cases c j with
    | kruskal_lift_case_1 _ _ => R j
    | kruskal_lift_case_2 _   => R'i
    | kruskal_lift_case_3 _   => (R k)↑α
    | kruskal_lift_case_4 _   => ⊥₂
    end.

  Notation s' := kruskal_lift_status.
  Notation X' := kruskal_lift_pred.
  Notation R' := kruskal_lift_rel.

  Section kruskal_lift_eqs.

    Ltac solve :=
      intros; match goal with
        |- ?h ?c ?j = _ => unfold h; destruct (kruskal_lift_cases c j); auto; tlia; easy
        end.

    Local Fact kruskal_lift_status_lt c j :           j < i → s' c j = s j.      Proof. solve. Qed.
    Local Fact kruskal_lift_status_eq c j :           i = j → s' c j = Some ◩.   Proof. solve. Qed.
    Local Fact kruskal_lift_status_gt_l c j : c = ◩ → i < j → s' c j = Some ◩.   Proof. solve. Qed.
    Local Fact kruskal_lift_status_gt_f c j : c = ▣ → i < j → s' c j = None.     Proof. solve. Qed.

    Local Fact kruskal_lift_pred_lt c j :             j < i → X' c j = X j.      Proof. solve. Qed.
    Local Fact kruskal_lift_pred_eq c j :             i = j → X' c j = X'i.      Proof. solve. Qed.
    Local Fact kruskal_lift_pred_gt_l c j :   c = ◩ → i < j → X' c j = X (S i).  Proof. solve. Qed.
    Local Fact kruskal_lift_pred_gt_f c j :   c = ▣ → i < j → X' c j = ⊥₁.       Proof. solve. Qed.

    Local Fact kruskal_lift_rel_lt c j :              j < i → R' c j = R j.      Proof. solve. Qed.
    Local Fact kruskal_lift_rel_eq c j :              i = j → R' c j = R'i.      Proof. solve. Qed.
    Local Fact kruskal_lift_rel_gt_l c j :    c = ◩ → i < j → R' c j = (R k)↑α.  Proof. solve. Qed.
    Local Fact kruskal_lift_rel_gt_f c j :    c = ▣ → i < j → R' c j = ⊥₂.       Proof. solve. Qed.

  End kruskal_lift_eqs.

  (** ⟪S i,s' c,X' c,R' c⟫ is correct and smaller that k,s,X,R⟫ *)

  Local Fact kruskal_lift_correct c : ⟪s' c,X' c,R' c⟫ₛ.
  Proof.
    unfold s', X', R'; intros j.
    destruct (kruskal_lift_cases c j); simpl; auto.
    all: apply afs_inv; auto; rewrite HXk; auto.
  Qed.

  Local Fact kruskal_lift_lt c : s k = Some c → ⟪S i,s' c,X' c,R' c⟫ ≺ₘ ⟪k,s,X,R⟫.
  Proof.
    intros H; constructor 1; rewrite H; destruct c.
    + rewrite kruskal_lift_status_gt_l, kruskal_lift_pred_gt_l, kruskal_lift_rel_gt_l; auto.
      rewrite HXk; auto; constructor; auto.
    + rewrite kruskal_lift_status_gt_f; auto; constructor.
  Qed.

  (** The evaluation map that reconstructs a tree from the information
      hidden inside nodes: the process of extracting substrees and hidding
      then in nodes of X' i is the reverse map *)

  Reserved Notation "x '-[' c ']->' y" (at level 70, no associativity, format "x  -[ c ]->  y").
  Reserved Notation "x '=[' c ']=>' y" (at level 70, no associativity, format "x  =[ c ]=>  y").

  Notation "v '⧓' m '⇝' w" := (@vintercal_graph _ _ v m _ w) (at level 70, no associativity, format "v ⧓ m  ⇝  w").

    (* As rules

                v' =[c]=> v
        ------------------------ X i x
          ⟨⦉x⦊₁|v'⟩ -[c]-> ⟨x|v⟩

         v' =[c]=> u     u⧓w ⇝ v
        ------------------------- X j x and wft X (projT2 w⦃_⦄)⦃_⦄
         ⟨⦉x,w⦊₂|v'⟩ -[c]-> ⟨x|v⟩

             v' =[c]=> v
        --------------------- j < i and X j x
         ⟨x|v'⟩ -[c]-> ⟨x|v⟩

             v' =[◩]=> v
        --------------------- i < j and X j x
         ⟨x|v'⟩ -[◩]-> ⟨x|v⟩

      *)

  Inductive kev_graph : af_choice → Utree → Utree → Prop :=

    | kev_graph_eq_i1 c x (v' : vec _ i) v :      (** This case could be covered by kev_graph_eq_i2 for j = i and m = [∅;∅;...;∅] *)

            X i x → v' =[c]=> v → ⟨⦉x⦊₁|v'⟩ -[c]-> ⟨x|v⟩

    | kev_graph_eq_i2 c x (v' : vec _ i) u w m (v : vec _ m) :

            i < m → X m x → (∀ p q, wft X (lvec_vec w⦃p⦄)⦃q⦄)
          → v' =[c]=> u → u⧓w ⇝ v → ⟨⦉x,w⦊₂|v'⟩ -[c]-> ⟨x|v⟩

    | kev_graph_lt_i c j x (v' : vec _ j) v :

            j < i → X j x → v' =[c]=> v → ⟨x|v'⟩ -[c]-> ⟨x|v⟩

    | kev_graph_gt_i j x (v' : vec _ j) v :

            i < j → X j x → v' =[◩]=> v → ⟨x|v'⟩ -[◩]-> ⟨x|v⟩

  where "x -[ c ]-> y" := (kev_graph c x y)
   and  "u =[ c ]=> v" := (vec_fall2 (kev_graph c) u v).

  Hint Constructors kev_graph : core.

  (* The domain of ev_graph is adequate, ie it is defined exactly on
     well formed trees *)

  Local Fact kev_dom c t' t : t' -[c]-> t → wft (X' c) t'.
  Proof.
    induction 1 as [ | | | j x v' v H1 H2 H3 IH3 ]; apply wft_fix; split; auto.
    + rewrite kruskal_lift_pred_eq; auto.
    + rewrite kruskal_lift_pred_eq; auto.
      constructor 2; auto.
      all: apply vintercal_length in H4; subst; auto.
    + rewrite kruskal_lift_pred_lt; auto.
    + rewrite HXk in H2; tlia.
      rewrite kruskal_lift_pred_gt_l; auto.
      rewrite HXk; auto; tlia.
  Qed.

  Local Fact kev_codom c t' t : t' -[c]-> t → wft X t.
  Proof.
    induction 1; apply wft_fix; split; auto.
    apply (vintercal_fall (wft X)) in H4; tauto.
  Qed.

  Local Lemma kev_total c t' : wft (X' c) t' → { t | t' -[c]-> t }.
  Proof.
    induction 1 as [ j x' v' H1 H2 IH2 ] using wft_rect.
    destruct vec_reif_t with (1 := IH2) as (v & Hv).
    destruct (kruskal_lift_cases c j)
      as [ c j H3 | c | j H3 | j H3 ].
    + rewrite kruskal_lift_pred_lt in H1; auto.
      exists ⟨x'|v⟩; constructor; auto.
    + rewrite kruskal_lift_pred_eq in H1; auto.
      apply kruskal_lift_pred_i_inv in H1
        as [ (x & -> & H1) | (x & m & -> & H3 & H4 & H5) ].
      * exists ⟨x|v⟩; constructor; auto.
      * destruct (vintercal_total v m) as ([q r] & Hr); simpl in Hr.
        exists ⟨x|r⟩; constructor 2 with (4 := Hv); auto.
        all: apply vintercal_length in Hr; subst; auto.
    + rewrite kruskal_lift_pred_gt_l in H1; auto; tlia.
      exists ⟨x'|v⟩; constructor 4; auto.
      rewrite HXk, <- (@HXk (S i)); auto; lia.
    + rewrite kruskal_lift_pred_gt_f in H1; auto; tauto.
  Qed.

  Local Corollary kev_vec_total c n (v' : vec _ n) :
       vec_fall (wft (X' c)) v' → { v | v' =[c]=> v }.
  Proof.
    intros H.
    apply vec_reif_t with (1 := fun i => kev_total c _ (H i)).
  Qed.

  Section kev_graph_left_inv.

    (** we study the output t depending on the shape of input t' in t' -[c]-> t *)

    Let shape c t j x' (v' : vec _ j) :=
        i = j ∧ match x' with
        | ⦉x⦊₁   => X i x ∧ ∃v, v' =[c]=> v ∧ ⟨x|v⟩ = t
        | ⦉x,w⦊₂ => ∃u, v' =[c]=> u ∧ ∃ e k (v : vec _ k), i < k ∧ X k x ∧ u⧓w↺e ⇝ v ∧ ⟨x|v⟩ = t
        | _     => False
        end
      ∨ (j < i ∧ X j x' ∧ ∃v, v' =[c]=> v ∧ ⟨x'|v⟩ = t)
      ∨ (i < j ∧ X j x' ∧ c = ◩ ∧ ∃v, v' =[◩]=> v ∧ ⟨x'|v⟩ = t).

    Local Fact kev_graph_inv_left c t' t : t' -[c]-> t → match t' with ⟨x'|v'⟩ => shape c t x' v' end.
    Proof.
      induction 1 as [ ? ? ? v | ? ? ? v'' ? j v | | ].
      + left; rsplit 2; auto; exists v; auto.
      + left; split; auto; exists v''; split; auto; exists eq_refl, j, v; eauto.
      + right; left; eauto.
      + right; right; rsplit 3; eauto.
    Qed.

    (** Specialized inversions, used in kev_fun and kev_quasi_morphism below *) 

    Local Fact kev_graph_eq_1_inv c x (v' : vec _ i) t :
       ⟨⦉x⦊₁|v'⟩ -[c]-> t → X i x ∧ ∃v, v' =[c]=> v ∧ ⟨x|v⟩ = t.
    Proof. intros [ | [ [] | [] ] ]%kev_graph_inv_left; tlia; tauto. Qed.

    Local Fact kev_graph_eq_2_inv c x w (v' : vec _ i) t :
       ⟨⦉x,w⦊₂|v'⟩ -[c]-> t → ∃u, v' =[c]=> u ∧ ∃j (v : vec _ j), i < j ∧ X j x ∧ u⧓w ⇝ v ∧ ⟨x|v⟩ = t.
    Proof.
      intros [ (_ & v & ? & ? & ? & ? & ? & ? & ?) | [ [] | [] ] ]%kev_graph_inv_left; tlia.
      eq refl; exists v; split; eauto.
    Qed.

    Local Fact kev_graph_lt_inv c j x (v' : vec _ j) t :
       j < i → ⟨x|v'⟩ -[c]-> t → X j x ∧ ∃v, v' =[c]=> v ∧ ⟨x|v⟩ = t.
    Proof. intros ? [ [] | [ (? & ? & ? & ? & <-) | [] ] ]%kev_graph_inv_left; tlia || eauto. Qed.

    Local Fact kev_graph_gt_l_inv j x (v' : vec _ j) t :
       i < j → ⟨x|v'⟩ -[◩]-> t → X j x ∧ ∃v, v' =[◩]=> v ∧ ⟨x|v⟩ = t.
    Proof. intros ? [ [] | [ [] | (_ & ? & ? & v & ? & <-)  ] ]%kev_graph_inv_left; tlia || eauto. Qed.

  End kev_graph_left_inv.

  Local Theorem kev_fun c t' t₁ t₂ : t' -[c]-> t₁ → t' -[c]-> t₂ → t₁ = t₂.
  Proof.
    intros H; revert H t₂.
    induction 1 as [ c x v' v H1 H2 IH2
                   | c x v' v'' m j v H0 H1 H2 H3 IH3 H4
                   | c j x v' v H1 H2 H3 IH3
                   | j x v' v H1 H2 H3 IH3 ]; intros t2 Ht2.
    + apply kev_graph_eq_1_inv in Ht2 as (_ & u & H4 & <-); f_equal; vec ext; auto.
    + apply kev_graph_eq_2_inv in Ht2 as (u & H5 & j' & m' & H8 & H6 & H7 & <-).
      assert (v'' = u) as <- by (vec ext; auto).
      destruct (vintercal_fun H4 H7) as (? & ?); eq refl; subst m'; auto.
    + apply kev_graph_lt_inv in Ht2 as (_ & u & H4 & <-); auto; f_equal; vec ext; auto.
    + apply kev_graph_gt_l_inv in Ht2 as (_ & u & H4 & <-); auto; f_equal; vec ext; auto.
  Qed.

  Local Corollary kev_vec_fun c n (v' v₁ v₂ : vec _ n) : v' =[c]=> v₁ → v' =[c]=> v₂ → v₁ = v₂.
  Proof. intros ? ?; vec ext; eapply kev_fun; eauto. Qed.

  Section kev_graph_inv_right.

    (** We study the input t' depending on the shape of the output t *)

    Let shape c t' j x (v : vec _ j) :=
               (j = i ∧ X i x ∧ ∃v', ⟨⦉x⦊₁|v'⟩ = t' ∧ v' =[c]=> v)
             ∨ (i < j ∧ X j x
                      ∧ ∃vw' : vintercal_in _ i,
                         match vw' with
                         | @c_vinter_in _ _ u w =>
                                   (∀ p q, wft X (lvec_vec w⦃p⦄)⦃q⦄)
                                  ∧ ∃v', ⟨⦉x,w⦊₂|v'⟩ = t'
                                       ∧ v' =[c]=> u
                         end
                       ∧ is_vintercal_in v vw')
             ∨ (j < i ∧ X j x ∧ exists v', ⟨x|v'⟩ = t' ∧ v' =[c]=> v)
             ∨ (c = ◩ ∧ i < j ∧ X j x ∧ exists v', ⟨x|v'⟩ = t' ∧ v' =[◩]=> v).

    (* This one is used to show that analysis is finite kev_inv_image_fin below *)

    Local Fact kev_graph_inv_right c t' t : t' -[c]-> t → match t with ⟨x|v⟩ => shape c t' x v end.
    Proof.
      induction 1 as [ c x v' v H1 H2 _ | c x v' v'' m j v H0 H1 H2 H3 _ H4 | c j x v' v H1 H2 H3 _ | j x v' v H1 H2 H3 _ ].
      + left; rsplit 2; auto; eauto.
      + right; left; rsplit 2; auto.
        exists (c_vinter_in v'' m); simpl; split; eauto.
      + do 2 right; left; split; eauto.
      + do 3 right; split; eauto.
    Qed.

    Local Fact kev_analysis c j x (v : vec _ j) t' : t' -[c]-> ⟨x|v⟩ ↔ shape c t' x v.
    Proof.
      split.
      + apply kev_graph_inv_right.
      + intros [ (-> & ? & ? & <- & ?)
             | [ (? & ? & [] & (? & ? & <- & ?) & ?)
             | [ (? & ? & ? & <- & ?)
               | (-> & ? & ? & ? & <- & ?)  ] ] ]; eauto.
    Qed.

  End kev_graph_inv_right.

  (** A nice high-level argument based on combinations of
     finitary relations, application of fin_* closure theorems *)

  Hint Resolve vintercal_fin eq_nat_dec lt_dec le_dec : core.

  (* Ana(lysis) is the converse of evaluation *)
  Notation ana c := (λ t t', t' -[c]-> t).

  Local Theorem kev_inv_image_fin c t : wft X t → fin (ana c t).
  Proof.
    induction 1 as [ j x v H1 H2 IH2 ] using wft_rect.
    finite eq (kev_analysis c x v).
    finite union.
    + destruct (eq_nat_dec j i) as [ -> | C ].
      2: now finite as (fun _ => False).
      repeat finite cst left.
      finite compose.
      finite as (vec_fall2 (ana c) v).
      split; apply vec_fall2_swap.
    + repeat finite dec left.
      finite compose.
      intros [ v'' m ] H; simpl in *.
      apply (vintercal_fall _ H) in H2 as [H2 H3].
      repeat finite dec left.
      finite compose.
      finite as (vec_fall2 (ana c) v'' ).
      1: split; apply vec_fall2_swap.
      apply fin_vec_fall2.
      apply vintercal_idx_left in H as (f & Hf).
      intros p; specialize (IH2 (f p)).
      rewrite Hf; auto.
    + repeat finite dec left.
      finite compose.
      finite as (vec_fall2 (ana c) v).
      1: split; apply vec_fall2_swap.
    + destruct c.
      * repeat finite dec left.
        finite compose.
        finite as (vec_fall2 (ana ◩) v).
        1: split; apply vec_fall2_swap.
      * now finite as (fun _ => False).
  Qed.

  (** An analysis is disapointing if either
        - its root node is above "α" wrt to R j (= R k) at arity j > i
        - its root node has arity i and is of shape ⦉x,w⦊₂
          and for some p, one of the components of w⦃p⦄ embeds γ⦃p⦄
   *)

  Unset Elimination Schemes.

  Inductive disapointing : Utree → Prop :=
    | disapointing_gt x j (v : vec _ j) :                                   i < j → R k α x → disapointing ⟨x|v⟩
    | disapointing_eq x (v : vec _ i) (w : vec _ (S i)) p q : γ⦃p⦄ ≤[k,R] (lvec_vec w⦃p⦄)⦃q⦄ → disapointing ⟨⦉x,w⦊₂|v⟩
    .

  Notation D' := disapointing.

  Set Elimination Schemes.

  Hint Constructors sub_dtree disapointing : core.

  Local Fact disapointing_inv t' :
         D' t'
      ↔ (∃ x j (v : vec _ j), S i <= j ∧ R k α x ∧ t' = ⟨x|v⟩)
       ∨ ∃ x (v : vec _ i) (w : vec _ (S i)) p q, γ⦃p⦄ ≤[k,R] (lvec_vec w⦃p⦄)⦃q⦄ ∧ t' = ⟨⦉x,w⦊₂|v⟩.
  Proof.
    split.
    + destruct 1 as [ x j v | x v w p q ].
      * left; exists x, j, v; auto.
      * right; exists x, v, w, p, q; auto.
    + intros [ (? & ? & ? & ? & ? & ->) | (? & ? & ? & ? & ? & ? & ->) ]; eauto.
  Qed.

  Local Fact disapointing_length n x' (v' : vec Utree n) : D' ⟨x'|v'⟩ → i <= n.
  Proof. intros [ (? & ? & ? & ? & ? & ?) | (? & ? & ? & ? & ? & ? & ?) ]%disapointing_inv; dtree discr. Qed.

  Local Fact disapointing_inv_lt n x' (v : vec _ n) : i < n → D' ⟨x'|v⟩ → R k α x'.
  Proof.
    intros H0 [ (? & ? & ? & ? & ? & H) | (? & ? & ? & ? & ? & ? & ?) ]%disapointing_inv; dtree discr.
    dtree inj H; subst; auto.
  Qed.

  Local Fact disapointing_inv_1 x (v : vec _ i) : ¬ D' ⟨⦉x⦊₁|v⟩.
  Proof. intros [ (? & ? & ? & ? & ? & ?) | (? & ? & ? & p & q & ? & H) ]%disapointing_inv; dtree discr. Qed.

  Local Fact disapointing_inv_2 x (w : vec _ (S i)) (v : vec _ i) :
         D' ⟨⦉x,w⦊₂|v⟩ → ∃ p q, γ⦃p⦄ ≤[k,R] (lvec_vec w⦃p⦄)⦃q⦄.
  Proof.
    intros [ (? & ? & ? & ? & ? & ?) | (? & ? & ? & ? & ? & ? & H) ]%disapointing_inv; dtree discr.
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

  Hint Resolve disap_has_disap
               sub_vtree_has_disap
               kev_inv_image_fin
               vec_fall2_embed : core.

  Local Lemma kev_quasi_morphism c t1' t2' t1 t2 :
                 t1' ≤[S i,R' c] t2'
               → t1' -[c]-> t1
               → t2' -[c]-> t2
               → t1 ≤[k,R] t2 ∨ E' t1'.
  Proof.
    intros H3 H1 H2; revert H3 t1 t2 H1 H2.
    induction 1 as [ t j x' v' p _ IH
                   | j x1' v1' x2' v2' H0 H1 _ IH
                   | j x1' v1' m x2' v2' H0 H1 _ IH ]; intros t1 t2 E1 E3.
    + specialize (fun t => IH _ t E1); clear E1.
      apply kev_graph_inv_left in E3
        as [ (<- & E3) | [ (H1 & H2 & v & E3 & <-) | (H1 & H2 & -> & v & E3 & <-) ] ].
      (* cases i <> j *)
      2,3: destruct (IH _ (E3 _)); eauto with vtree_db.
      (* case j = i *)
      destruct x' as [ | x | | n x w ]; try easy.
      * destruct E3 as (E4 & v & E3 & <-).
        destruct (IH _ (E3 _)); eauto with vtree_db.
      * destruct E3 as (u & E3 & e & m & v & E4 & E5 & E6 & <-); eq refl.
        destruct (IH _ (E3 _)); auto.
        apply vintercal_idx_left in E6 as (f & Hf).
        left; constructor 1 with (f p); rewrite <- Hf; auto.
    + (* j < S i, so either j < i or j = i *)
      destruct (kruskal_lift_cases c j) as [ c j Hj | c | j Hj | j Hj ]; tlia.
      * (* j < i *)
        rewrite kruskal_lift_rel_lt in H1; auto.
        apply kev_graph_lt_inv in E3 as (E3 & v2 & E4 & <-); auto.
        apply kev_graph_lt_inv in E1 as (E1 & v1 & E2 & <-); auto.
        specialize (fun i => IH i _ _ (E2 _) (E4 _)).
        apply finite_choice in IH as [ IH | [] ]; fin eauto.
        left; destruct (le_lt_dec k j); auto with vtree_db.
        rewrite HRk in H1; auto with vtree_db.
      * (* j = i *)
        rewrite kruskal_lift_rel_eq in H1; auto.
        destruct H1 as [ x1 x2 G1 | x1 x2 w1 w2 G1 G2 ].
        - apply kev_graph_eq_1_inv in E3 as (E3 & v2 & E4 & <-).
          apply kev_graph_eq_1_inv in E1 as (E1 & v1 & E2 & <-).
          specialize (fun i => IH i _ _ (E2 _) (E4 _)).
          apply finite_choice in IH as [ IH | [] ]; fin eauto.
          left.
          assert (k = S i \/ k <= i) as [ | Hi ] by lia.
          ++ constructor 2; auto; lia.
          ++ rewrite HRk with (1 := Hi) in G1.  (* i <= k -> R i = R k *)
             constructor 3; auto; lia.
        - apply kev_graph_eq_2_inv in E3 as (u2 & E4 & j2 & v2 & G5 & E3 & G4 & <-).
          apply kev_graph_eq_2_inv in E1 as (u1 & E2 & j1 & v1 & G6 & E1 & G3 & <-).
          unfold rel_lift in G2.
          assert (  (forall p, lvec_embed (vtree_upto_embed k R) w1⦃p⦄ w2⦃p⦄)
                 \/ (exists p q, vtree_upto_embed k R γ⦃p⦄ (lvec_vec w1⦃p⦄)⦃q⦄))
            as [ H | (p & q & Hpq) ].
          1:{ apply finite_choice; fin auto.
              intro p; apply vec_embed_rel_lift_inv; eauto. }
          ++ specialize (fun i => IH i _ _ (E2 _) (E4 _)).
             apply finite_choice in IH as [ IH | [] ]; fin eauto.
             left; constructor 3; auto; tlia.
             revert IH H; apply vintercal_embed; auto.
          ++ right.
             exists ⟨⦉x1,w1⦊₂|v1'⟩; split; auto.
             constructor 2 with (1 := Hpq).
    + (* k <= S i and S i <= j *)
      generalize (vec_embed_length IH); intros Hm.
      apply kev_graph_inv_left in E1 as [ (? & _) | [ (? & _) | (_ & E1 & -> & v1 & E2 & <-) ] ]; tlia.
      apply kev_graph_inv_left in E3 as [ (? & _) | [ (? & _) | (_ & E3 & _ & v2 & E4 & <-) ] ]; tlia.
      rewrite kruskal_lift_rel_gt_l in H1; auto.
      destruct H1 as [ H1 | ]; auto.
      apply vec_embed_sub_vec_fall2 in IH as (v3' & IH & H3).
      destruct (vec_embed_fall2_inv H3 E4) as (? & <-%vec_prj_ext & G2).
      apply vec_embed_sub_vec_fall2 in G2 as (v3 & E5 & G3).
      specialize (fun i => IH i _ _ (E2 _) (E5 _)).
      apply finite_choice in IH as [ IH | [] ]; fin eauto.
      left; constructor 3; auto; tlia.
      apply vec_embed_sub_vec_fall2; eauto.
  Qed.

  (** An evaluation is exceptional if each of its analysis is exceptional *)
  Notation E c t := (ana c t ⊆₁ E').

  Section exceptional_vs_embedding.

    (** This proof may be a bit long and is only of informative nature.
        We do not need this result to establish the thm kruskal_afs_nodes_ge
        below, but we point out the nice characterization of exceptional
        evaluations. *)
    Local Remark embed_exceptional c t : wft X t → ⟨α|γ⟩ ≤[k,R] t → E c t.
    Proof.
      induction 1 as [ m y w Hy Hw IHw ] using wft_rect.
      intros Hyw [ n' x' v' ] [ (<- & Hx') | [ (? & ? & v & E1 & E2) | (? & ? & -> & v & E1 & E2)] ]%kev_graph_inv_left.
      + destruct x'; try easy.
        * destruct Hx' as (? & v & E1 & E2).
          dtree inj E2; subst x'.
          apply vtree_upto_embed_inv_right in Hyw
            as [ (p & Hp) | [ (? & ? & ? & ?) | (_ & _ & ?%vec_embed_length) ] ]; tlia.
          specialize (IHw _ Hp _ (E1 _)); eauto with vtree_db.
        * destruct Hx' as (u & H1 & ? & j & v & E1 & E2 & E3 & E4); eq refl.
          dtree inj E4; subst x'; simpl in *.
          apply vtree_upto_embed_inv_right in Hyw
            as [ (p & Hp) | [ (e & ? & _ & _) | (H3 & H4 & H5) ] ]; tlia.
          - (* ⟨α|γ⟩ embeds into a component v⦃p⦄ *)
            specialize (IHw _ Hp).
            (* where is v⦃p⦄ in v = u⧓h ? *)
            destruct (vintercal_prj E3 p) as [ (j & Hj) | (q & j & Hj) ].
            ++ (* v⦃p⦄ = u⦃_⦄ *)
               rewrite Hj in IHw.
               specialize (IHw _ (H1 _)); eauto with vtree_db.
            ++ (* v⦃p⦄ = h⦃_⦄⦃_⦄ *)
               rewrite Hj in Hp.
               apply disap_has_disap.
               constructor 2 with q j.
               revert Hp; apply vtree_sub_upto_embed; eauto.
          - (* R k α y and γ embeds into v = u⧓h 
               but u is "shorter" than γ, hence
               one element of γ must embed into 
               one element of an element of h.
               This is a PHP like argument. *)
            destruct (vec_embed_any_vintercal H5 E3) as (p & q & ?).
            apply disap_has_disap.
            now constructor 2 with p q.
      + dtree inj E2; subst x'.
        apply vtree_upto_embed_inv_right in Hyw
          as [ [] | [ (? & ? & ? & ?) | (_ & _ & ?%vec_embed_length) ] ]; tlia; eauto.
      + dtree inj E2; subst x'.
        apply vtree_upto_embed_inv_right in Hyw
          as [ [] | [ (? & ? & ? & ?) | (? & ? & ?) ] ]; tlia; eauto.
    Qed.

    Local Fact E_hereditary c n x (v : vec _ n) t :
           vec_fall (wft X) v
         → E c t
         → (∀v', v' =[c]=> v → ⟨x|v'⟩ -[c]-> t)
         → (∃p, E c v⦃p⦄)
         ∨ (∃v', v' =[c]=> v ∧ D' ⟨x|v'⟩).
    Proof.
      intros H1 H2 H3.
      assert ((forall v', v' =[c]=> v -> exists p, E' v'⦃p⦄)
           \/ (exists v', v' =[c]=> v /\ D' ⟨x|v'⟩)) as [ H4 | ]; eauto.
      + apply fin_choice; auto.
        * apply fin_idx_rel with (R := fun p v' => v' -[_]-> _); auto.
        * intros v' Hv'.
          destruct (H2 ⟨x|v'⟩) as (t' & H4 & ?); auto.
          apply sub_dtree_inv_rt in H4 as [ -> | (p & ?) ]; auto.
          left; exists p, t'; auto.
      + left.
        apply fin_vec_fall2_find with (R := ana _)
          in H4; eauto.
    Qed.

    (* Below looks very much like the characterization of vec_embed
             vintercal_any_vec_embed *)

    Local Lemma E_embed c (Hc : s k = Some c) t :
          wft X t → E c t → ⟨α|γ⟩ ≤[k,R] t.
    Proof.
      induction 1 as [ j x v Hx Hv0 IHv ] using wft_rect; intros Hv.
      generalize (fun j x' u' H => @E_hereditary c j x' u' _ H Hv); intros hereditary.
      destruct (kruskal_lift_cases c j) as [ c j Hij | | j Hij | j Hij ].
      + (* case j < i *)
        destruct (hereditary _ x v) as [ [] | (v' & H3 & H4) ]; eauto with vtree_db.
        apply disapointing_length in H4; lia.
      + (* case j = i *)
      destruct (hereditary _ ⦉x⦊₁ v) as [ [] | (v' & H3 & H4) ]; eauto with vtree_db.
      apply disapointing_inv_1 in H4 as [].
      + (* case i < j and c = ◩ *)
        destruct (hereditary _ x v) as [ [] | (v' & H3 & H4) ]; eauto with vtree_db.
        apply disapointing_inv_lt in H4; auto.
        (* Same proof as below *** FACTORIZE ?? *)
        assert (forall d : vintercal_in _ i, is_vintercal_in v d
            -> (exists p, match d with c_vinter_in _ w => exists q, γ⦃p⦄ ≤[k,R] (lvec_vec w⦃p⦄)⦃q⦄ end)
            \/ ⟨α|γ⟩ ≤[k,R] ⟨x|v⟩) as G.
        1:{ intros [u w]; simpl; intros H.
            generalize Hv0; intros H1; apply vintercal_fall with (1 := H) in H1 as [ H1 H2 ].
            destruct (hereditary _ ⦉x,w⦊₂ u) as [ (p & Hp) | (v1 & G1 & G2) ]; eauto.
            + destruct (vintercal_idx_left H) as (f & Hf).
              right; constructor 1 with (f p).
              apply IHv; rewrite <- Hf; auto.
            + apply disapointing_inv_2 in G2 as (p & q & Hpq); eauto. }
        apply fin_choice in G as [ G | (_ & _ & G) ]; auto.
        constructor 3; auto.
        apply vintercal_any_vec_embed; auto.
        intros u w H0; apply (G (c_vinter_in u w) H0).
      + (* case i < j and c = ▣ *)
        assert (R k α x) as Hαx.
        1:{ specialize (HXR k); rewrite Hc in HXR; simpl in HXR.
            apply HXR; auto.
            rewrite HXk in Hx; auto; tlia. }
        (* Same proof here as above *** FACTORIZE ?? *)
        assert (forall d : vintercal_in _ i, is_vintercal_in v d
            -> (exists p, match d with c_vinter_in _ w => exists q, γ⦃p⦄ ≤[k,R] (lvec_vec w⦃p⦄)⦃q⦄ end)
            \/ ⟨α|γ⟩ ≤[k,R] ⟨x|v⟩) as G.
        1:{ intros [u w]; simpl; intros H.
            generalize Hv0; intros H1; apply vintercal_fall with (1 := H) in H1 as [ H1 H2 ].
            destruct (hereditary _ ⦉x,w⦊₂ u) as [ (p & Hp) | (v1 & G1 & G2) ]; eauto.
            + destruct (vintercal_idx_left H) as (f & Hf).
              right; constructor 1 with (f p).
              apply IHv; rewrite <- Hf; auto.
            + apply disapointing_inv_2 in G2 as (p & q & Hpq); eauto. }
        apply fin_choice in G as [ G | (_ & _ & G) ]; auto.
        constructor 3; auto.
        apply vintercal_any_vec_embed; auto.
        intros u w H; apply (G (c_vinter_in u w) H).
      Qed.

  End exceptional_vs_embedding.

  Section af_choice.

    Local Definition af_choice_sk_pwc : { c | Some c = s k }.
    Proof. destruct (s k) as [ c | ]; try easy; eauto. Qed.

    Local Definition af_choice_sk := proj1_sig af_choice_sk_pwc.

    Local Fact af_choice_sk_spec : Some af_choice_sk = s k.
    Proof. apply (proj2_sig af_choice_sk_pwc). Qed.

  End af_choice.

  Notation c₀ := af_choice_sk.
  Notation Hc₀ := af_choice_sk_spec.

  Hint Resolve kruskal_lift_correct
               kruskal_lift_lt Hc₀: core.

  Local Theorem exceptional_embed t : wft X t → E c₀ t → ⟨α|γ⟩ ≤[k,R] t.
  Proof. apply E_embed; auto. Qed.

  (** Exceptional evaluations are "exactly" those which embed ⟨α|γ⟩ *)

  Local Remark exceptional_iff_embed t : wft X t → E c₀ t ↔ ⟨α|γ⟩ ≤[k,R] t.
  Proof. split; [ apply exceptional_embed | apply embed_exceptional ]; auto. Qed.

  Local Fact upto'_afs : afs (wft (X' c₀)) (vtree_upto_embed (S i) (R' c₀)).
  Proof.
    apply IHXR with (s' c₀); auto.
    + intros n Hn; destruct c₀.
      * rewrite !kruskal_lift_pred_gt_l; auto.
      * rewrite !kruskal_lift_pred_gt_f; auto.
    + intros n Hn; destruct c₀.
      * rewrite !kruskal_lift_rel_gt_l; auto.
      * rewrite !kruskal_lift_rel_gt_f; auto.
  Qed.

  Hint Resolve kev_fun
               kev_total
               kev_dom
               kev_codom
               kev_quasi_morphism
               exceptional_embed : core.

  Theorem kruskal_afs_nodes_ge : afs (wft X) (vtree_upto_embed k R)↑⟨α|γ⟩.
  Proof.
    generalize upto'_afs.
    afs quasi morph (kev_graph c₀) E'; eauto.
  Qed.

End kruskal_afs_nodes_ge.
