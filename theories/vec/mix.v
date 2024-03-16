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

(* Relation & inductive charaterization of vec_mix

      [x1,...,xn] mix [v1,...,vn] -> [x1]++v1++[x2]++v2++...++[xn]++vn *)

#[global] Reserved Notation "v '⧒' m '⇝' w" (at level 70, no associativity, format "v ⧒ m  ⇝  w").

Inductive vmix_graph X : ∀n, vec X n → hvec X n → ∀m, vec X m → Prop :=
    | vmix_0 :
                ∅ ⧒ ∅ ⇝ ∅
    | vmix_1 n x (v : vec _ n) i a (w : vec _ n) m (r : vec _ m) m' (r' : vec _ m') :
                v ⧒ w ⇝ r
           →    a ⊞ r ⇝ r' 
           → x##v ⧒ ⦑i,a⦒##w ⇝ x##r'
where "v ⧒ m ⇝ w" := (vmix_graph v m w).

#[global] Hint Constructors vmix_graph : vec_db.

Section vmix_graph.

  Variable X : Type.

  Fact vmix_length n (v : vec X n) w m (r : vec _ m) :
         v ⧒ w ⇝ r → m = hvec_size w.
  Proof.
    induction 1 as [ | ? ? ? ? ? ? ? ? ? ? ? ? H ]; simpl; f_equal; auto.
    apply vapp_length in H; tlia.
  Qed.

  Fact vmix_nil_r n (v : vec X n) w : (∀p, lvec_len w⦃p⦄ = 0) → v ⧒ w ⇝ v.
  Proof.
    revert w; induction v as [ | n x v IHv ]; intros w.
    + vec invert w; auto with vec_db.
    + vec invert w as [i u] w; intros H.
      generalize (H idx_fst); simpl; intros ->; vec invert u.
      constructor 2 with (r := v); auto with vec_db.
      apply IHv; intro; apply (H (idx_nxt _)).
  Qed.

  Fact vmix_inv n v w m r :
       @vmix_graph X n v w m r
     → match v in vec _ n return vec _ n → _ with
       | ∅    => λ w, w = ∅ ∧ match r with ∅ => True | _ => False end
       | x##v => λ w,
         match r with
         | ∅ => False
         | y##r => x = y ∧ ∃ m' (r' : vec _ m'),
                             v ⧒ vec_tail w ⇝ r'
                           ∧ lvec_vec (vec_head w) ⊞ r' ⇝ r
         end
       end w.
  Proof. intros []; simpl; eauto. Qed.

  Fact vmix_fun n v w m1 r1 m2 r2 :
          @vmix_graph X n v w m1 r1 → @vmix_graph X n v w m2 r2 → ∃e, r1↺e = r2.
  Proof.
    intros H1; revert H1 m2 r2.
    induction 1 as [ | n x v i a w m1 r1 m1' r1' H1 IH1 H0 ]; intros ? [ | z m2 r2 ] H2;
      apply vmix_inv in H2; try easy.
    + exists eq_refl; auto.
    + destruct H2 as (<- & m' & r' & H2 & H3); simpl in *.
      apply IH1 in H2 as (? & H2); eq refl; subst.
      destruct (vapp_fun H0 H3) as (? & H4); eq refl; subst.
      exists eq_refl; auto.
  Qed.

  Inductive vmix_out : Type :=
    | c_vmix_out m : vec X m → vmix_out.

  Definition is_vmix_out n v w o :=
    match o with @c_vmix_out m r => @vmix_graph X n v w m r end.

  Definition vmix_total n v w : sig (@is_vmix_out n v w).
  Proof.
    revert w; induction v as [ | x n v IH ]; intros w.
    + vec invert w; exists (c_vmix_out ∅); constructor.
    + vec invert w as a w; destruct a as [i a].
      destruct (IH w) as ([j r] & Hr).
      destruct (vapp_total a r) as ([k r'] & Hr').
      exists (c_vmix_out (x##r')); constructor 2 with (1 := Hr); auto.
  Qed.

  Fact vmix_rinv_nil n (v : vec X n) w : v ⧒ w ⇝ ∅ → { e : n = 0 | v↺e = ∅ /\ w↺e = ∅}.
  Proof.
    revert v w; intros [] w H; apply vmix_inv in H; try easy.
    destruct H as (-> & _); exists eq_refl; auto.
  Qed.

  Fact vmix_rinv_c_n n x (u : vec X n) w : x##u ⧒ w ⇝ ∅ → False.
  Proof. now intros H; apply vmix_inv in H. Qed.

  Fact vmix_rinv_nil_cons (v : vec X 0) w m x (r : vec _ m) : v ⧒ w ⇝ x##r → False.
  Proof. now intros H; apply vmix_inv in H; vec invert v. Qed.

  Fact vmix_rinv_cons n x (u : vec X n) a w m y (r : vec _ m) :
         x##u ⧒ a##w ⇝ y##r
       →  (  (x = y)
           * { j : _
           & { r' : vec _ j
             | u ⧒ w ⇝ r'
             ∧ lvec_vec a ⊞ r' ⇝ r }}
          )%type.
  Proof.
    intros H; apply vmix_inv in H; simpl in H.
    destruct H as (<- & H); split; auto.
    destruct (vmix_total u w) as ([j r'] & H'); simpl in H'.
    exists j, r'; split; auto.
    destruct H as (j' & r'' & H & H1).
    destruct (vmix_fun H H'); eq refl; subst; auto.
  Qed.

  Inductive vmix_in n : Type :=
    | c_vmix_in : vec X n → hvec X n → vmix_in n.

  Definition is_vmix_in j (r : vec X j) n (m : vmix_in n) :=
    match m with c_vmix_in v w => v ⧒ w ⇝ r end.

  Arguments is_vmix_in {_} _ n _.

  Local Fact is_vmix_in_nil_iff j r m :
         @is_vmix_in j r 0 m
       ↔ j = 0 ∧ c_vmix_in ∅ ∅ = m.
  Proof.
    split.
    + revert j r m; intros _ [ | j x r ] [ v w ] H; apply vmix_inv in H.
      * vec invert v; vec invert w; auto.
      * now vec invert v.
    + intros (-> & <-); vec invert r; constructor.
  Qed.

  Local Fact is_vmix_in_cons_iff j (r : vec _ j) n m :
        is_vmix_in r (S n) m
      ↔ match r with
        | ∅    => False
        | x##r =>
          ∃ a, match a with
               | @c_vapp_in _ i u j v =>
                 ∃ c : vmix_in n,
                   match c with
                   | c_vmix_in v' w => @c_vmix_in (S n) (x##v') (⦑i,u⦒##w)
                   end = m ∧ is_vmix_in v n c
               end ∧ is_vapp_in r a
        end.
  Proof.
    split.
    + revert j r m; intros _ [ | j x r ] [ v w ] H; apply vmix_inv in H.
      * vec invert v as ? v; auto.
      * vec invert v as y v.
        vec invert w as [i a] w; simpl in H.
        destruct H as (<- & m' & r'& H1 & H2).
        exists (c_vapp_in a r'); split; auto.
        exists (c_vmix_in v w); auto.
   + destruct r as [ | j x r ]; try easy.
     intros ([i u k v] & ([v' w] & <- & H2) & H3); simpl.
     constructor 2 with (1 := H2); auto.
  Qed.

  Hint Resolve eq_nat_dec : core.

  Lemma vmix_fin j (r : vec _ j) n : fin (is_vmix_in r n).
  Proof.
    revert j r; induction n as [ | n IHn ]; intros j r.
    + finite eq (is_vmix_in_nil_iff _).
      finite dec left.
    + finite eq (@is_vmix_in_cons_iff _ _ _).
      destruct r as [ | j x r ]; fin auto.
      do 2 (finite compose; intros [] ?); fin auto.
  Qed.

  Fact vmix_fall (P : X -> Prop) n (u : vec _ n) w m (r : vec _ m) :
        u ⧒ w ⇝ r →  (vec_fall P u ∧ ∀p, vec_fall P (lvec_vec w⦃p⦄))
                    ↔ vec_fall P r.
  Proof.
    induction 1 as [ | n x v i a w m r m' r' H1 IH1 H2 ].
    + split; try tauto; split; auto; intro; idx invert all.
    + apply (vapp_fall P) in H2.
      rewrite !vec_fall_cons_iff, H2, <- IH1.
      rewrite forall_idx_Sn; simpl; tauto.
  Qed.

  Fact vmix_id_inv n u : { w | @vmix_graph X n u w _ u }.
  Proof.
    induction u as [ | n x u (w & Hw) ].
    + exists ∅; constructor.
    + exists (⦑_,∅⦒##w).
      constructor 2 with (r := u); auto with vec_db.
  Qed.

  (* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

  Section vmix_idx_left.

    Let Fixpoint hvec_idx n (m : hvec X n) : idx n → idx (hvec_size m) :=
      match m with
      | ∅    => λ p, p
      | v##m => λ p,
        match idx_S_inv p with
        | None   => 𝕆
        | Some p => 𝕊 (idx_right (lvec_len v) (hvec_idx _ p))
        end
      end.

    Let hvec_idx_cast n m k (e : k = @hvec_size X n m) : idx n → idx k :=
      match eq_sym e with
      | eq_refl => @hvec_idx _ _
      end.

    Local Fact vmix_idx_left_rec n u m k r :
         @vmix_graph X n u m k r → ∀ (e : k = hvec_size m) p, u⦃p⦄ = r⦃hvec_idx_cast _ e p⦄.
    Proof.
      induction 1 as [ | n x v i a w m r m' r' H1 IH1 H2 ]; intros e p; idx invert p.
      + apply vmix_length in H1.
        apply vapp_length in H2.
        subst m m'; simpl in e.
        rewrite (eq_refl_nat e); simpl; auto.
      + generalize (vmix_length H1)
                   (vapp_length H2); intros -> ->.
        simpl in e.
        rewrite (eq_refl_nat e); simpl; auto.
        rewrite (IH1 eq_refl).
        rewrite <- (vapp_idx_right_eq H2); auto.
    Qed.

    Fact vmix_idx_left n u m k r :
         @vmix_graph X n u m k r → { f : idx n → idx k | ∀p, u⦃p⦄ = r⦃f p⦄ }.
    Proof.
      intros H.
      exists (hvec_idx_cast _ (vmix_length H)).
      apply vmix_idx_left_rec, H.
    Qed.

  End vmix_idx_left.

  Fact vmix_prj n u m k r :
       @vmix_graph X n u m k r → ∀i, (∃j, r⦃i⦄ = u⦃j⦄) ∨ (∃ p q, r⦃i⦄ = (lvec_vec m⦃p⦄)⦃q⦄).
  Proof.
    induction 1 as [ | n x v i a w m r m' r' H1 IH1 H2 ]; intros j; idx invert j.
    + left; now exists 𝕆.
    + destruct (vapp_prj H2 j) as [ (p & Hp) | (p & Hp) ].
      * right; now exists 𝕆, p.
      * destruct (IH1 p) as [ (q & Hq) | (q & z & Hqz) ].
        - left; exists (𝕊 q); now rewrite Hp.
        - right; exists (𝕊 q), z; now rewrite Hp.
  Qed.

End vmix_graph.

#[global] Hint Resolve vmix_fin : vec_db.

#[local] Notation "u '=[' R ']=' v" := (vec_fall2 R u v) (at level 70, format "u  =[ R ]=  v").

Fact vmix_fall2_inv X Y (R : X → Y → Prop) n u w m r r' :
         @vmix_graph X n u w m r
       → r =[R]= r'
       → { u' : _ & 
         { w' | @vmix_graph Y n u' w' m r'
              ∧ u =[R]= u'
              ∧ w =[λ s s', vec_forall2 R (lvec_vec s) (lvec_vec s')]= w' } }.
Proof.
  revert u w m r r'.
  induction n as [ | n IHn ]; intros u w.
  + vec invert u; vec invert w; intros m r r' H1 H2.
    exists ∅, ∅; rsplit 2; auto with vec_db.
    apply vmix_inv in H1; destruct r; try easy.
    vec invert r'; constructor.
  + vec invert u as x u.
    vec invert w as a w.
    destruct a as [i a].
    intros ? [ | m y1 r ] r' H1.
    1: apply vmix_rinv_c_n in H1 as [].
    vec invert r' as y2 r'; intros H.
    apply vec_fall2_cons_inv in H as [H2 H3].
    apply vmix_rinv_cons in H1 as (<- & j & r'' & H1 & H4); simpl in *.
    destruct (vapp_fall2_inv_left H4 H3) as (a' & r3 & H5 & H6 & H7).
    destruct IHn with (1 := H1) (2 := H7) as (u' & w' & G1 & G2 & G3).
    exists (y2##u'), (⦑_,a'⦒##w'); rsplit 2; auto with vec_db.
    constructor 2 with (1 := G1); auto.
Qed.

#[local] Reserved Notation "l ≤ₑ m" (at level 70, no associativity, format "l  ≤ₑ  m").

Section vec_embed_mix.

  Variables (X Y : Type) (R : X → Y → Prop).

  Infix "≤ₑ" := (vec_embed R).

  Fact vmix_embed n (v1 v2 : vec _ n) w1 w2 k1 (r1 : vec _ k1) k2 (r2 : vec _ k2) :
           v1⧒w1 ⇝ r1
         → v2⧒w2 ⇝ r2
         → v1 =[R]= v2
         → w1 =[lvec_embed R]= w2
         → r1 ≤ₑ r2.
  Proof.
    intros H; revert H v2 w2 k2 r2.
    induction 1 as [ | n x1 v1 i1 a1 w1 m1 u1 k1 r1 H1 IH1 H2 ]; intros v2 w2 k r H3 H4 H5.
    + vec invert v2; vec invert w2; auto with vec_db.
    + vec invert v2 as x2 v2.
      vec invert w2 as [i2 a2] w2.
      apply vmix_inv in H3; simpl in H3.
      destruct r as [ | ? k r ]; try easy.
      destruct H3 as (<- & m2 & r2 & G1 & G2).
      apply vec_fall2_cons_inv in H5 as [ H6 H7 ].
      apply vec_fall2_cons_inv in H4 as [ H4 H5 ].
      simpl in *.
      constructor 2; auto.
      apply vec_embed_vapp with (1 := H2) (2 := G2); auto.
      apply IH1 with (1 := G1); auto.
  Qed.

End vec_embed_mix.
