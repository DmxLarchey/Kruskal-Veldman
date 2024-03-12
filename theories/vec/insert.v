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
  Require Import idx vec.

From KruskalFinite
  Require Import finite.

Require Import base notations tactics app.

Import idx_notations vec_notations.

Set Implicit Arguments.

(* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

#[global] Reserved Notation "v '⊲' p ']' x '⇝' w" (at level 70, x at level 200, no associativity, format "v ⊲ p ] x  ⇝  w").

Inductive vinsert_graph X x : forall n, vec X n → idx (S n) → forall m, vec X m → Prop :=
  | in_vec_insert_gr_0 n (v : vec _ n) : v ⊲𝕆] x ⇝ x##v
  | in_vec_insert_gr_1 n y (v : vec _ n) p m (w : vec _ m) : v ⊲p] x ⇝ w -> y##v ⊲𝕊 p] x ⇝ y##w
where "v ⊲ p ] x ⇝ w" := (@vinsert_graph _ x _ v p _ w).

#[global] Hint Constructors vinsert_graph : core.

Section vinsert.

  Variable (X : Type).

  Implicit Types (x : X).

  Fact vinsert_length x n (v : vec _ n) p m (w : vec _ m) : v ⊲p] x ⇝ w → m = S n.
  Proof. induction 1; auto. Qed.

  Fact vinsert_inv x n (v : vec _ n) p m (w : vec _ m) :
          v ⊲p] x ⇝ w
        → match idx_S_inv p with
          | None   => ∃e, w↺e = x##v
          | Some q =>
            match n return vec _ n → idx n → _ with
            | 0   => ⊥₂
            | S n => λ v q,
              match w with
              | ∅    => False
              | y##w => vec_tail v ⊲q] x ⇝ w ∧ vec_head v = y
              end
            end v q
          end.
  Proof. induction 1; simpl; eauto; exists eq_refl; auto. Qed.

  Fact vinsert_left_inv_0 x n (v : vec _ n) (w : vec _ (S n)) : v ⊲𝕆] x ⇝ w -> w = x##v.
  Proof.
    intros H.
    apply vinsert_inv in H as (e & H); eq refl; auto.
  Qed.

  Fact vinsert_left_inv_1 x n y (v : vec _ n) p m (w : vec _ m) :
         y##v ⊲𝕊 p] x ⇝ w
       → match w with
         | ∅    => False
         | z##w => v ⊲p] x ⇝ w ∧ y = z
         end.
  Proof. intros H; now apply vinsert_inv in H; simpl in H. Qed.

  Fact vinsert_fun x n (v : vec _ n) p m1 (w1 : vec _ m1) m2 (w2 : vec _ m2) :
          v ⊲p] x ⇝ w1 → v ⊲p] x ⇝ w2 → exists e, w1↺e = w2.
  Proof.
    intros H; revert H m2 w2.
    induction 1 as [ n v | n y v p m1 w1 H1 IH1 ]; intros m2 w2 H2; apply vinsert_inv in H2; simpl in H2.
    + destruct H2 as (e & H2); eq refl; exists eq_refl; auto.
    + destruct w2 as [ | m2 z w2 ]; try easy; destruct H2 as [ H2 <- ].
      apply IH1 in H2 as (e & H3); eq refl; subst; exists eq_refl; auto.
  Qed.

  Inductive vinsert_out : Type :=
    | c_vinsert_out m : vec X m -> vinsert_out.

  Definition is_vinsert_out x n (v : vec _ n) p o :=
    match o with c_vinsert_out w => v ⊲p] x ⇝ w end.

  Fact vinsert_total x n v p : sig (@is_vinsert_out x n v p).
  Proof.
    revert p.
    induction v as [ | y n v IHv ]; intros p; idx invert p.
    + exists (c_vinsert_out (x##∅)); simpl; auto.
    + idx invert p.
    + exists (c_vinsert_out (x##y##v)); simpl; auto.
    + destruct (IHv p) as ([m w] & Hw); simpl in Hw.
      exists (c_vinsert_out (y##w)); simpl; auto.
  Qed.

  Inductive vinsert_in : Type :=
    | c_vinsert_in (_ : X) n : vec X n → idx (S n) → vinsert_in.

  Definition is_vinsert_in m (w : vec _ m) i :=
    match i with @c_vinsert_in x n v p => v ⊲p] x ⇝ w end.

  Fact vinsert_surj m (w : vec X m) : ∀p, { n : _ & { v : _ & { e : m = S n | v ⊲p↺e] w⦃p⦄ ⇝ w } } }.
  Proof.
    induction w as [ | x m v IHv ]; intros p; idx invert p.
    + exists m, v, eq_refl; simpl; auto.
    + destruct (IHv p) as (n & w & -> & H); simpl in *.
      exists (S n), (x##w), eq_refl; simpl; auto.
  Qed.

  Fact is_vinsert_in_nil_iff i : is_vinsert_in ∅ i ↔ False.
  Proof.
    split; try easy.
    destruct i as [ x n v p ]; simpl; intros H.
    apply vinsert_inv in H; idx invert p; simpl in H.
    + destruct H as (e & _); lia.
    + destruct n; simpl in H; auto.
  Qed.

  Fact is_vinsert_in_cons_iff m y w i :
          @is_vinsert_in (S m) (y##w) i
        ↔ c_vinsert_in y w 𝕆 = i
        ∨ ∃i', match i' with
               | @c_vinsert_in x n v p => c_vinsert_in x (y##v) (𝕊 p)
               end = i
             ∧ is_vinsert_in w i'.
  Proof.
    split.
    + destruct i as [ x n v p ]; simpl; intros H.
      apply vinsert_inv in H; idx invert p; simpl in H.
      * destruct H as (e & H); inversion e; subst; eq refl.
        apply vec_cons_inj in H as (-> & ->); auto.
      * destruct v as [ | z n v ]; try easy; simpl in H.
        destruct H as [ H -> ]; right.
        exists (c_vinsert_in x v p); split; auto.
    + intros [ <- | ([x n v p] & H1 & H2) ]; subst; simpl in *; auto.
  Qed.

  Fact vinsert_fin m w : fin (@is_vinsert_in m w).
  Proof.
    induction w as [ | y m w IHw ].
    + finite eq is_vinsert_in_nil_iff.
    + finite eq (is_vinsert_in_cons_iff _ _).
  Qed.

  Fact vinsert_fall (P : X → Prop) x n (v : vec _ n) p m (w : vec _ m) :
         v ⊲p] x ⇝ w → P x ∧ vec_fall P v ↔ vec_fall P w.
  Proof. induction 1; rewrite !vec_fall_cons_iff; tauto. Qed.

End vinsert.

Section vinsert_idx.

  (* This computes the index of an insertion *)

  Let Fixpoint vins_idx n (p : idx n) : idx (S n) → idx (S n) :=
    match p with
    | 𝕆 => λ q,
      match idx_S_inv q with
      | Some _ => idx₀
      | None   => idx₁
      end
    | 𝕊 p' as p => λ q,
      match idx_S_inv q with
      | Some q => 𝕊 (vins_idx p' q)
      | None   => 𝕊 p
      end
    end.

  Local Fact vins_surj n q k : { p : idx n | k = @vins_idx _ p q } + { k = q }.
  Proof.
    revert q k.
    induction n as [ | n IHn ]; intros q k;
      idx invert q; idx invert k; simpl; auto; try (idx invert all; fail).
    + left; exists k; simpl; idx invert k; auto.
    + left; exists idx₀; auto.
    + destruct (IHn q k) as [ (p & Hp) | -> ]; auto.
      left; exists (idx_nxt p); simpl; f_equal; auto.
  Qed.

  Definition vinsert_idx n p q := @vins_idx n q p.

  Fact vinsert_idx_surj n p q : { q' | q = @vinsert_idx n p q' } + { q = p }.
  Proof. apply vins_surj. Qed.

  Variables (X : Type) (x : X).

  Local Fact vins_idx_spec n (v : vec _ n) p m (w : vec _ m) :
      v ⊲p] x ⇝ w → ∀ (e : m = S n) q, v⦃q⦄ = (w↺e)⦃vins_idx q p⦄.
  Proof.
    induction 1 as [ n v | n y v p m w H1 IH1 ]; intros e q.
    + destruct q; eq refl; simpl; auto.
    + inversion e; subst; eq refl; idx invert q; auto.
      apply (IH1 eq_refl).
  Qed.

  Local Fact vinsert_eq_rec n (v : vec _ n) p m (w : vec _ m) :
        v ⊲p] x ⇝ w → ∀ (e : m = S n), (w↺e)⦃p⦄ = x.
  Proof.
    induction 1 as [ n v | n y v p m w H1 IH1 ]; intro e; eq refl; auto.
    inversion e; subst; eq refl.
    apply (IH1 eq_refl).
  Qed.

  Fact vinsert_eq n (v : vec _ n) p w : v ⊲p] x ⇝ w → w⦃p⦄ = x.
  Proof. intros H; apply vinsert_eq_rec with (1 := H) (e := eq_refl). Qed.

  Theorem vinsert_idx_eq n (v : vec _ n) p w :
         v ⊲p] x ⇝ w ↔ w⦃p⦄ = x ∧ ∀q, v⦃q⦄ = w⦃vinsert_idx p q⦄.
  Proof.
    split.
    + intros H; split.
      * eapply vinsert_eq; eauto.
      * apply vins_idx_spec with (1 := H) (e := eq_refl).
    + intros (<- & H).
       assert (v = vec_set (fun q => vec_prj w (vinsert_idx p q))) as ->.
       1: now vec ext; vec rew.
       clear H.
       revert p w; induction n as [ | n IHn ]; intros p w;
         vec invert w as x w; idx invert p; auto.
       * vec invert w; auto.
       * idx invert p.
       * vec invert w as y w; simpl; rewrite vec_set_prj; auto.
  Qed.

  Fact vinsert_prj n (v : vec _ n) p w :
         v ⊲p] x ⇝ w → ∀i, (i = p ∧ w⦃i⦄ = x) ∨ (∃j, w⦃i⦄ = v⦃j⦄).
  Proof.
    intros (H1 & H2)%vinsert_idx_eq i.
    destruct (vinsert_idx_surj p i) as [ (q & ->) | -> ].
    + right; eauto.
    + left; eauto.
  Qed.

End vinsert_idx.

Fact vinsert_surjective X n (v : vec X (S n)) (p : idx (S n)) :
     { u : vec _ n | u ⊲p] v⦃p⦄ ⇝ v ∧ ∀q, u⦃q⦄ = v⦃vinsert_idx p q⦄ }.
Proof.
  destruct (vinsert_surj v p) as (i & w & e & H).
  inversion e; subst; eq refl.
  exists w; split; auto.
  rewrite vinsert_idx_eq in H; tauto.
Qed.

#[local] Notation "u '=[' R ']=' v" := (vec_fall2 R u v) (at level 70, format "u  =[ R ]=  v").

Section vinsert_fall2.

  Variables (X Y : Type) (R : X → Y → Prop).

  Fact vinsert_fall2 x y n (v v' : vec _ n) p m (w w' : vec _ m) :
         v⊲p]x ⇝ w
      → v'⊲p]y ⇝ w'
      → w =[R]= w' ↔ R x y ∧ v =[R]= v'.
  Proof.
    intros H1 H2.
    generalize (vinsert_length H1); intros ->.
    apply vinsert_idx_eq in H1 as (<- & H1).
    apply vinsert_idx_eq in H2 as (<- & H2).
    split.
    + intros H; split; auto.
      intro; rewrite H1, H2; auto.
    + intros (H3 & H4) q.
      destruct (vinsert_idx_surj p q) as [ (q' & ->) | -> ]; auto.
      rewrite <- H1, <- H2; auto.
  Qed.

  Fact vinsert_fall2_inv x n (v : vec _ n) p m (w w' : vec _ m) :
         v⊲p]x ⇝ w
       → w =[R]= w'
       → { y : _ &
         { v' : _ | v'⊲p]y ⇝ w'
                  ∧ R x y
                  ∧ v =[R]= v' } }.
  Proof.
    intros H1 H2.
    generalize (vinsert_length H1); intros ->.
    apply vinsert_idx_eq in H1 as (<- & H1).
    exists (vec_prj w' p), (vec_set (fun q => vec_prj w' (vinsert_idx p q))); rsplit 2; auto.
    + apply vinsert_idx_eq; split; auto.
      intros q; rewrite vec_prj_set; auto.
    + intro; rewrite vec_prj_set, H1; auto.
  Qed.

End vinsert_fall2.

Section vec_insert_fall2.

  Variables (X Y : Type) (R : X → Y → Prop) (n : nat)
            (u : vec X (S n)) (v : vec Y (S n)).

  Theorem vinsert_any_vec_fall2 :
        (∀ w q x, w ⊲q] x ⇝ v → R u⦃q⦄ x) → u =[R]= v.
  Proof.
    intros H p.
    destruct (vinsert_surj v p) as (i & v' & e & Hv').
    inversion e; subst i; eq refl.
    apply H with (1 := Hv').
  Qed.

  Theorem vec_fall2_any_vinsert :
       u =[R]= v → ∀ w q x, w ⊲q] x ⇝ v → R u⦃q⦄ x.
  Proof. intros ? ? ? ? (<- & _)%vinsert_idx_eq; auto. Qed.

  (** This is a charaterization of vec_fall2 in terms of
      analysis using insertion/extraction of a value in v.

      This can be compared to exceptional_iff_embed in
      KruskalHigman af/af_utree_embed_[fun,rel].v 

      See also vec_embed_iff_vintercal in vec_rel/rel/intercal.v *)

  Theorem vec_fall2_iff_vinsert : 
       u =[R]= v ↔ ∀ w q x, w ⊲q] x ⇝ v → R u⦃q⦄ x.
  Proof.
    split.
    + apply vec_fall2_any_vinsert.
    + apply vinsert_any_vec_fall2.
  Qed.

End vec_insert_fall2.

