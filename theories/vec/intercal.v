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
  Require Import finite choice.

Require Import base notations tactics app mix.

Import idx_notations vec_notations.

Set Implicit Arguments.

(* Relation & inductive charaterization of vec_intercalate

      [x1,...,xn] intercalate [v0,v1,...,vn] -> v0++[x1]++v1++[x2]++v2++...++[xn]++vn *)

#[global] Reserved Notation "v '⧓' m '⇝' w" (at level 70, no associativity, format "v ⧓ m  ⇝  w").

Inductive vintercal_graph X : ∀n, vec X n → hvec X (S n) → ∀m, vec X m → Prop :=
  | vintercal_0 n (v : vec _ n) i (u : vec _ i) (w : hvec _ n) m (a : vec _ m) k (b : vec _ k) :

                v⧒w ⇝ a
              → u⊞a ⇝ b
              → v ⧓ ⦑i,u⦒##w ⇝ b

where "v ⧓ m ⇝ w" := (vintercal_graph v m w).

Section vintercal_graph.

  Variable X : Type.

  Definition vintercal_size n (w : hvec X (S n)) := pred (hvec_size w).

  Fact vintercal_length n v w m r : @vintercal_graph X n v w m r → m = vintercal_size w.
  Proof.
    induction 1 as [ ? ? ? ? ? ? ? ? ? H1 H2 ].
    apply vmix_length in H1.
    apply vapp_length in H2.
    simpl; subst; auto.
  Qed.

  Fact vintercal_length_le n v w m r : @vintercal_graph X n v w m r → n ≤ m.
  Proof.
    intros H.
    apply vintercal_length in H as ->; clear r.
    vec invert w as [] w; unfold vintercal_size; simpl.
    generalize (hvec_size_ge w); tlia.
  Qed.

  Section vintercal_inv.

    Local Fact vintercal_inv_rec n v w m r :
         @vintercal_graph X n v w m r
       → let (i,u) := vec_head w in
         ∃ j a, vmix_graph v (vec_tail w) a
              ∧ @vapp_graph _ i u j a m r.
    Proof.
      induction 1 as [ n v i u w m a k b H1 H2 ]; simpl.
      exists m, a; simpl; auto.
    Qed.

    Fact vintercal_inv n v w k r :
          @vintercal_graph X n v w k r
        → let (i,u) := vec_head w in
          { j : _ & { a | vmix_graph v (vec_tail w) a
                        ∧ @vapp_graph _ i u j a _ r } }.
    Proof.
      vec invert w as [i u] w; simpl.
      intros H.
      destruct (vmix_total v w) as ([j m] & Hm); simpl in Hm.
      exists j, m; split; auto.
      apply vintercal_inv_rec in H; simpl in H.
      destruct H as (j' & m' & H1 & H2).
      destruct (vmix_fun H1 Hm) as []; eq refl; subst; auto.
    Qed.

  End vintercal_inv.

  Fact vintercal_cons_nil_l n v w m r :
           @vintercal_graph X n v w m r → ∀x, x##v ⧓ ⦑_,∅⦒##w ⇝ x##r.
  Proof.
    induction 1 as [ n v i u w k a m r H1 H2 ]; intros x.
    constructor 1 with (a := x##r); auto with vec_db.
    constructor 2 with (1 := H1); auto with vec_db.
  Qed.

  Fact vintercal_fun n v w m1 r1 m2 r2 :
         @vintercal_graph X n v w m1 r1 → @vintercal_graph X n v w m2 r2 → ∃e, r1↺e = r2.
  Proof.
    intros H; revert H m2 r2; induction 1 as [ n v i u w m a k b H1 H2 ]; intros m2 r2 H3.
    apply vintercal_inv in H3 as (j' & a' & H3 & H4); simpl in H3.
    generalize (vmix_fun H1 H3); intros (<- & H); simpl in H; subst.
    generalize (vapp_fun H2 H4); intros (<- & H); simpl in H; subst.
    exists eq_refl; auto.
  Qed.

  Inductive vintercal_out : Type :=
    | c_vinter_out n (_ : vec X n) : vintercal_out.

  Definition is_vintercal_out n v w o :=
    match o with @c_vinter_out k r => @vintercal_graph X n v w k r end.

  Fact vintercal_total n v w : sig (@is_vintercal_out n v w).
  Proof.
    vec invert w as x w; destruct x as [i x].
    destruct (vmix_total v w) as ([j r] & Hr); simpl in Hr.
    destruct (vapp_total x r) as ([p t] & Ht); simpl in Ht.
    exists (c_vinter_out t); simpl; constructor 1 with (1 := Hr); auto.
  Qed.

  Inductive vintercal_in n : Type :=
    | c_vinter_in (_ : vec X n) (_ : hvec X (S n)) : vintercal_in n.

  Definition is_vintercal_in j r n (m : vintercal_in n) :=
    match m with c_vinter_in v w => @vintercal_graph X n v w j r end.

  Fact is_vintercal_in_iff j r n m :
       @is_vintercal_in j r n m
     ↔ ∃ c : vapp_in _,
         match c with
         | @c_vapp_in _ i a j b => ∃ d : vmix_in _ n,
           match d with
           | @c_vmix_in _ _ v w => c_vinter_in v (⦑i,a⦒##w)
           end = m
         ∧ is_vmix_in b d
         end
       ∧ is_vapp_in r c.
  Proof.
    split.
    + destruct m as [ v w ]; simpl.
      vec invert w as [i a] w.
      intros H; apply vintercal_inv in H as (k & b & H1 & H2); simpl in *.
      exists (c_vapp_in a b); split; simpl; auto.
      exists (c_vmix_in v w); split; simpl; auto.
    + intros ([i a k b] & ([v w] & <- & H2) & H3); simpl in *.
      constructor 1 with (1 := H2); auto.
  Qed.

  Fact vintercal_fin j r n : fin (@is_vintercal_in j r n).
  Proof.
    finite eq (@is_vintercal_in_iff _ _ _).
    finite compose.
    intros [] ?; finite compose; auto with vec_db.
  Qed.

  Fact vintercal_fall (P : rel₁ X) n u w m r :
       @vintercal_graph X n u w m r
     → (vec_fall P u ∧ ∀p, vec_fall P (lvec_vec w⦃p⦄))
     ↔ vec_fall P r.
  Proof.
    induction 1 as [ n v i u w m a k b H1 H2 ].
    apply (vmix_fall P) in H1.
    apply (vapp_fall P) in H2.
    rewrite H2, <- H1, forall_idx_Sn; simpl; tauto.
  Qed.

  Fact vintercal_idx_left n u w m r :
       @vintercal_graph X n u w m r → { f | ∀i, u⦃i⦄ = r⦃f i⦄ }.
  Proof.
    intros H.
    vec invert w as [i a] w.
    destruct (vintercal_inv H) as (j & v & H1 & H2); simpl in *.
    destruct (vapp_idx_right H2) as (f1 & Hf1).
    destruct (vmix_idx_left H1) as (f2 & Hf2).
    exists (fun p => f1 (f2 p)).
    intros; rewrite Hf2, Hf1; auto.
  Qed.

  Fact vintercal_invert n x (v : vec _ n) i (l : vec X i) w m (r : vec _ m) :
        (x##v) ⧓ ⦑i,l⦒##w ⇝ r 
      → ∃ nu (u : vec _ nu), v ⧓ w ⇝ u ∧ l ⊞ (x ## u) ⇝ r. 
  Proof.
    intros (na & a & H1 & H2)%vintercal_inv; simpl in H1, H2.
    vec invert w as q w.
    apply vmix_inv in H1.
    destruct a as [ | y na a ]; [ easy | ].
    destruct H1 as (<- & m' & r' & H1 & H3); simpl in H1, H3.
    exists na, a; split; auto.
    destruct q; constructor 1 with m' r'; auto.
  Qed.

  Fact vintercal_prj n u w m r :
       @vintercal_graph X n u w m r → ∀i, (∃j, r⦃i⦄ = u⦃j⦄) ∨ (∃ p q, r⦃i⦄ = (lvec_vec w⦃p⦄)⦃q⦄).
  Proof.
    induction 1 as [ n v i u w m a k b H1 H2 ]; intros j.
    destruct (vapp_prj H2 j) as [ (p & Hp) | (p & Hp) ].
    + right; exists 𝕆, p; now rewrite Hp.
    + destruct (vmix_prj H1 p) as [ (q & Hq) | (q & z & Hz) ].
      * left; exists q; now rewrite Hp.
      * right; exists (𝕊 q), z; now rewrite Hp.
  Qed.

End vintercal_graph.

#[global] Hint Constructors vintercal_graph : core.

#[local] Notation "u '=[' R ']=' v" := (vec_fall2 R u v) (at level 70, format "u  =[ R ]=  v").

Fact vintercal_fall2_inv X Y R n (u : vec X n) w m (r r' : vec _ m) :
         u⧓w ⇝ r
       → r =[R]= r'
       → { u' : vec Y _ & 
         { w' | u'⧓w' ⇝ r'
              ∧ u =[R]= u'
              ∧ w =[λ s s', vec_forall2 R (lvec_vec s) (lvec_vec s')]= w' } }.
Proof.
  vec invert w as [i a] w; intros H1 H2.
  apply vintercal_inv in H1 as (j & l & H1 & H3); simpl in H1.
  destruct (vapp_fall2_inv_left H3 H2) as (a' & l' & H4 & H5 & H6).
  destruct (vmix_fall2_inv H1 H6) as (u' & w' & H7 & H8 & H9).
  exists u', (⦑_,a'⦒##w'); rsplit 2; auto with vec_db.
  constructor 1 with (1 := H7); auto.
Qed.

#[local] Hint Resolve vapp_vec_embed_skip : core.

#[local] Infix "≤sv" := (vec_embed (@eq _)) (at level 70).

Theorem subvec_iff_intercalate X n (u : vec X n) m (v : vec _ m) : u ≤sv v ↔ ∃w, u ⧓ w ⇝ v.
Proof.
  split.
  + induction 1 as [ | n x u m ? v <- _ (w & Hw) | n u m x v _ (w & Hw) ].
    * exists (⦑_,∅⦒##∅); eauto with vec_db.
    * vec invert w as [i a] w.
      apply vintercal_inv in Hw
        as (j & b & H3 & H4); simpl in H3.
      exists (⦑_,∅⦒##⦑_,a⦒##w); eauto with vec_db.
    * vec invert w as [i a] w.
      apply vintercal_inv in Hw
        as (j & b & H3 & H4); simpl in H3.
      exists (⦑_,x##a⦒##w); eauto with vec_db.
  + intros (w & Hw); revert Hw.
    induction 1 as [ n v i u w m r k b H1 H2 ].
    apply vapp_vec_embed_skip with (1 := H2).
    clear k b H2 i u; revert H1.
    induction 1; eauto with vec_db.
Qed.

#[local] Reserved Notation "l ≤ₑ m" (at level 70, no associativity, format "l  ≤ₑ  m").

Section vec_embed_intercalate.

  Variables (X Y : Type) (R : X → Y → Prop).

  Infix "≤ₑ" := (vec_embed R).

  Fact vintercal_embed n (v1 v2 : vec _ n) w1 w2 k1 (r1 : vec _ k1) k2 (r2 : vec _ k2) :
           v1⧓w1 ⇝ r1
         → v2⧓w2 ⇝ r2
         → v1 =[R]= v2
         → w1 =[lvec_embed R]= w2
         → r1 ≤ₑ r2.
  Proof.
    induction 1 as [ n v1 i1 a1 w1 m1 u1 k1 r1 H1 H2 ].
    induction 1 as [ n v2 i2 a2 w2 m2 u2 k2 r2 H3 H4 ].
    intros H5 H6.
    apply vec_fall2_cons_inv in H6 as [ H6 H7 ]; simpl in *.
    apply vec_embed_vapp with (1 := H2) (2 := H4); auto.
    revert H1 H3 H5 H7; apply vmix_embed.
  Qed.

  Theorem vec_embed_iff_fall2_intercalate n (u : vec _ n) m (v : vec _ m) :
           u ≤ₑ v ↔ ∃ r w, u =[R]= r ∧ r ⧓ w ⇝ v.
  Proof.
    rewrite vec_embed_sub_vec_fall2.
    split; intros (r & Hr); exists r; revert Hr.
    + rewrite subvec_iff_intercalate.
      intros (H1 & w & H2); exists w; auto.
    + rewrite subvec_iff_intercalate; firstorder.
  Qed.

  (* For u v of the same length, if it is not possible to
     split v as _ ⧓ w without having some component of u
     R-related to some component of w, then u is R related to v *)

  Theorem vintercal_any_vec_fall2 n (u v : vec _ (S n)) :
        (∀ v' w, v' ⧓ w ⇝ v → ∃ i j, R u⦃i⦄ (lvec_vec w⦃i⦄)⦃j⦄)
      → u =[R]= v.
  Proof.
    revert u v; induction n as [ | n IHn ]; intros u v H; vec invert u as x u; vec invert v as y v.
    + vec invert u; vec invert v; apply vec_fall2_cons; auto with vec_db.
      destruct (H ∅ (⦑_,y##∅⦒##∅)) as (p & q & Hpq); eauto with vec_db.
       repeat idx invert p; simpl in q; repeat idx invert q; auto.
    + destruct (H v (⦑_,y##∅⦒##vec_set (fun _ => ⦑_,∅⦒)))
        as (p & q & Hpq); simpl.
      * constructor 1 with (a := v); auto with vec_db.
        apply vmix_nil_r.
        intros p; idx invert p; simpl; auto with vec_db.
        now vec rew.
      * idx invert p.
        - simpl in q; repeat idx invert q; simpl in Hpq.
          apply vec_fall2_cons; auto.
          apply IHn.
          intros v' w Hi; simpl in Hi.
          destruct (H (y##v') (⦑_,∅⦒##w)) as (p & q & Hpq').
          1: now apply vintercal_cons_nil_l.
          idx invert p; simpl in *; eauto; idx invert q.
        - idx invert p; simpl in *; repeat idx invert q.
          revert q Hpq; vec rew; simpl; intro; idx invert all.
  Qed.

  Hint Resolve vintercal_fin vec_fall2_embed vintercal_any_vec_fall2 : core.

  (** This is a critical characterization of vec_embed (the converse is also
      provable but not used in these proofs

      Notice that the hypothesis is a "forall" condition that is transformed
      into an "existential" property, a bit like the PHP *)

  Theorem vintercal_any_vec_embed n (f : vec _ (S n)) m (g : vec _ m) :
        S n ≤ m
      → (∀ v w, v ⧓ w ⇝ g → ∃ i j, R f⦃i⦄ (lvec_vec w⦃i⦄)⦃j⦄)
      → f ≤ₑ g.
  Proof.
    revert n f.
    induction g as [ | y m v IHv ]; intros n u Hn H; tlia.
    vec invert u as x u.
    destruct n as [ | n ].
    + vec invert u.
      destruct (H ∅ (⦑_,y##v⦒##∅)) as (p & q & Hpq).
      * simpl; constructor 1 with (a := ∅).
        - constructor.
        - apply vapp_nil_r.
      * repeat idx invert p; simpl in q, Hpq.
        idx invert q; eauto with vec_db.
        constructor 3.
        apply vec_sg_embed_prj; eauto.
    + assert (H1: forall i : vintercal_in Y (S n), is_vintercal_in v i
            -> match i with
               | c_vinter_in _ w => exists p q, R (x##u)⦃p⦄ (lvec_vec w⦃p⦄)⦃q⦄
               end \/ R x y).
       1:{ intros [ v' w ]; simpl; intros H1.
           vec invert w as [i a] w.
           destruct (H v' (⦑_,y##a⦒##w)) as (p & q & Hpq).
           + apply vintercal_inv in H1 as (j & w1 & H1 & H2); simpl in H1.
             constructor 1 with (1 := H1); auto with vec_db.
           + idx invert p; simpl in *.
             * idx invert q; auto.
               left; exists idx_fst, q; auto.
             * left; exists (idx_nxt p), q; auto. }
       apply fin_choice in H1 as [ H1 | (_ & _ & H1) ]; auto.
       * destruct (eq_nat_dec (S n) m) as [ <- | Hnm ]; auto.
         constructor 3; apply IHv; auto; tlia.
         intros v' w Hw.
         apply (H1 (c_vinter_in v' w)); simpl; auto.
       * constructor 2; auto.
         apply IHv; tlia.
         intros v' w Hi; simpl in Hi.
         destruct (H (y##v') (⦑_,∅⦒##w)) as (p & q & Hpq).
         - destruct Hi as [ n v' j u' w k a m v G1 G2 ]; simpl.
           constructor 1 with (a := y##v); auto with vec_db.
           constructor 2 with (1 := G1); auto.
         - idx invert p; simpl in *.
           ++ idx invert q.
           ++ exists p, q; auto.
  Qed.

  (* Much like the PHP, we need to generalize here and idx2nat *)
  Local Lemma vec_embed_any_vintercal_rec nf (f : vec _ nf) nv (v : vec _ nv) w ng (g : vec _ ng) :
        v ⧓ w ⇝ g → f ≤ₑ g → nv < nf → ∃ i j k, R f⦃i⦄ (lvec_vec w⦃j⦄)⦃k⦄ ∧ idx2nat i = idx2nat j.
  Proof.
    induction v as [ | x nv v IH ] in nf, f, w, ng, g |- *.
    + vec invert w as (i,l) w; vec invert w.
      intros (j & a' & (_ & ?)%vmix_inv & Ha')%vintercal_inv.
      destruct a'; [ | easy ].
      destruct (vapp_fun (vapp_nil_r l) Ha') as []; subst; simpl eq_rect in *.
      clear H Ha'.
      destruct f as [ | x nf f ]; tlia; intros H1 _.
      destruct (vec_embed_prj H1 idx_fst) as (p & Hp).
      exists idx_fst, idx_fst, p; auto.
    + vec invert w as (i,l) w.
      intros (nb & b & H1 & H2)%vintercal_invert H3 H4.
      destruct f as [ | y n f ]; [ tlia | ].
      destruct (vapp_embed_middle_choice H2 H3) as [ H5 | (p  & H5) ].
      * destruct IH with (1 := H1) (2 := H5) as (p & q & r & E1 & E2); tlia.
        exists (idx_nxt p), (idx_nxt q), r; simpl; split; eauto.
      * exists idx_fst, idx_fst, p; simpl; eauto.
  Qed.

  Theorem vec_embed_any_vintercal n (u : vec _ (S n)) m (a : vec _ m) v w :
        u ≤ₑ a → v ⧓ w ⇝ a → ∃ i j, R u⦃i⦄ (lvec_vec w⦃i⦄)⦃j⦄.
  Proof.
    intros H2 H1.
    destruct (vec_embed_any_vintercal_rec H1 H2) as (p & q & r & E1 & E2); tlia.
    apply idx2nat_inj in E2 as <-.
    now exists p, r.
  Qed.

  (** This is a characterization of vec_embed wrt to intercalation:

      If f is the nil vector then f R-embeds into any g

      If f is a vector of strictly positive length 1+n:

      f R-embeds into g if and only if 
       - length of f = 1+n <= length of g
       - for any intercalation of g = w0++[v1]++w1++...++[vn]++wn,
         there is i such that f⦃i⦄ belongs to w⦃i⦄
  
      Observation (DLW):
       - it is reminds me of the PHP
       - it is a critical tool in the proof of Kruskal's tree thm,
         ie the soundness of the construction of the quasi morphism

      See also vec_fall2_iff_vinsert in vec_rel/rel/insert.v *)

  Theorem vec_embed_iff_vintercal n (f : vec _ (S n)) m (g : vec _ m) :
         f ≤ₑ g ↔ S n ≤ m ∧ ∀ v w, v ⧓ w ⇝ g → ∃ i j, R f⦃i⦄ (lvec_vec w⦃i⦄)⦃j⦄.
  Proof.
    split.
    + intros H; split.
      * revert H; apply vec_embed_length.
      * intros ? ?; revert H; apply vec_embed_any_vintercal.
    + intros (H1 & H2); revert H1 H2; apply vintercal_any_vec_embed.
  Qed.

End vec_embed_intercalate.
