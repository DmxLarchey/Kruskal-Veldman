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

Require Import base notations tactics.

Import idx_notations vec_notations.

Set Implicit Arguments.

#[global] Reserved Notation "v '⊞' m '⇝' w" (at level 70, no associativity, format "v ⊞ m  ⇝  w").

Inductive vapp_graph {X} : ∀ n (_ : vec X n) m (_ : vec X m) k (_ : vec X k), Prop :=
  | vapp_0 m (v : vec _ m) : ∅⊞v ⇝ v
  | vapp_1 n x (u : vec _ n) m (v : vec _ m) k (w : vec _ k) : u ⊞ v ⇝ w → x##u ⊞ v ⇝ x##w
where "u ⊞ v ⇝ w" := (@vapp_graph _ _ u _ v _ w).

#[global] Hint Constructors vapp_graph : vec_db.

Fact vapp_inv X n (u : vec X n) m (v : vec _ m) k (w : vec _ k) :
        u ⊞ v ⇝ w
      → match u with
        | ∅ => ∃e, v↺e = w
        | x##u =>
          match w with
          | ∅ => False
          | y##w => x = y ∧ u ⊞ v ⇝ w
          end
        end.
Proof. intros []; auto; now exists eq_refl. Qed.

Tactic Notation "vapp" "inv" hyp(H) :=
  let e := fresh in
  match type of H with
    | vapp_graph ∅ ?b ?w
      => apply vapp_inv in H as (e & H);
         (match type of e with
           | ?x = ?y => (subst x || subst y || rewrite (eq_refl_nat e) in H)
          end); simpl in H; subst b
    | @vapp_graph _ _ (_##_) _ _ _ (_##_)
      => apply vapp_inv in H as (-> & H)
    | @vapp_graph _ _ (_##_) _ _ (S _) ?w
      => apply vapp_inv in H; revert H;
         vec invert w as e w; intros (<- & H)
    | @vapp_graph _ _ (_##_) _ _ ?k ?w
      => apply vapp_inv in H;
         destruct w as [ | k ? w ]; [ destruct H | destruct H as (<- & H) ]
    | @vapp_graph _ _ ?u _ ?v _ ∅
      => apply vapp_inv in H;
         destruct u; [ | destruct H ];
         destruct H as (-> & H); simpl in H; subst v
    | @vapp_graph _ ?n ?u _ ?v _ (_##_)
           => apply vapp_inv in H;
              destruct u as [ | n ? u ];
              destruct H as (-> & H);
              [ simpl in H; subst v | ]
  end.

Tactic Notation "vapp" "inv" "all" :=
  repeat match goal with
    | H: ∅    ⊞ _ ⇝ _    |- _ => vapp inv H
    | H: _##_ ⊞ _ ⇝ _    |- _ => vapp inv H
    | H:    _ ⊞ _ ⇝ ∅    |- _ => vapp inv H
    | H:    _ ⊞ _ ⇝ _##_ |- _ => vapp inv H
    | v: vec _ 0         |- _ => vec invert v
  end.

#[local] Infix "≤sv" := (vec_embed (@eq _)) (at level 70).

Section props.

  (* Relational & inductive characterization of vec_app *)

  Variable X : Type.

  Fact vapp_length n (u : vec X n) m (v : vec _ m) k (w : vec _ k) :
          u ⊞ v ⇝ w → k = n+m.
  Proof. induction 1; simpl; lia. Qed.

  Fact vapp_iff_vec_app n (u : vec X n) m (v : vec _ m) k (w : vec _ k) :
          u ⊞ v ⇝ w ↔ ∃e, w↺e = vec_app u v.
  Proof.
    split.
    + induction 1 as [ m v | n x u m v k w H1 (-> & H2) ]; simpl in *.
      * exists eq_refl; auto.
      * subst w; exists eq_refl; auto.
    + intros (-> & H); simpl in *; subst.
      induction u; constructor; auto.
  Qed.

  Fact vapp_fun n (u : vec X n) m (v : vec _ m) k₁ (w₁ : vec _ k₁) k₂ (w₂ : vec _ k₂) :
      u ⊞ v ⇝ w₁ → u ⊞ v ⇝ w₂ → ∃e, w₁↺e = w₂.
  Proof.
    induction 1 as [ m v | n x u m v k w H1 IH1 ] in k₂, w₂ |- *; intros H2.
    + vapp inv all; exists eq_refl; auto.
    + vapp inv all.
      apply IH1 in H2 as []; subst.
      exists eq_refl; simpl; auto.
  Qed.

  Fact vapp_nil_r n (u : vec X n) : u ⊞ ∅ ⇝ u.
  Proof. induction u; auto with vec_db. Qed.

  Inductive vapp_out : Type :=
    | c_vapp_out n (_ : vec X n) : vapp_out.

  Definition is_vapp_out n (u : vec _ n) m (v : vec _ m) o :=
    match o with @c_vapp_out k w => u ⊞ v ⇝ w end.

  Definition vapp_total n u m v : sig (@is_vapp_out n u m v).
  Proof.
    exists (c_vapp_out (vec_app u v)); apply vapp_iff_vec_app.
    exists eq_refl; auto.
  Qed.

  Inductive vapp_in : Type :=
    | c_vapp_in n (_ : vec X n) m (_ : vec X m) : vapp_in.

  Definition is_vapp_in k (w : vec _ k) i :=
    match i with @c_vapp_in n u m v => u ⊞ v ⇝ w end.

  Fact is_vapp_in_nil_iff a : is_vapp_in ∅ a ↔ c_vapp_in ∅ ∅ = a.
  Proof.
    split.
    + destruct a; simpl; intros; vapp inv all; auto.
    + intros <-; simpl; constructor.
  Qed.

  Fact is_vapp_in_cons_iff k x (w : vec _ k) a :
           is_vapp_in (x##w) a
        ↔  c_vapp_in ∅ (x##w) = a
         ∨ ∃a', match a' with
                | c_vapp_in u v => c_vapp_in (x##u) v = a
                end ∧ is_vapp_in w a'.
  Proof.
    split.
    + destruct a as [ n u m v ]; simpl; intros; vapp inv all; auto.
      right; exists (c_vapp_in u v); auto.
    + intros [ <- | ([] & <- & H2) ]; constructor; auto.
  Qed.

  Fact vapp_fin k w : fin (@is_vapp_in k w).
  Proof.
    induction w as [ | k y w IH ].
    + finite eq is_vapp_in_nil_iff.
    + finite eq (is_vapp_in_cons_iff _ _).
      apply fin_union; fin auto.
      finite compose.
      intros []; fin auto.
  Qed.

  Fact vapp_fall (P : X -> Prop) n (u : vec _ n) m (v : vec _ m) k (w : vec _ k) :
         u ⊞ v ⇝ w → vec_fall P w ↔ vec_fall P u ∧ vec_fall P v.
  Proof.
    induction 1 as [ | n x u m v k w H IH ].
    + rewrite vec_fall_nil_iff; tauto.
    + rewrite !vec_fall_cons_iff, IH; tauto.
  Qed.

  Fact vapp_split k (w : vec X k) n m : k = n + m → { u : vec _ n & { v : vec _ m | u ⊞ v ⇝ w } }.
  Proof.
    revert n m; induction w as [ | x k w IH ].
    + intros [ | ] m; tlia; simpl; intros <-; exists ∅, ∅; constructor.
    + intros [ | n ] m Hnm.
      * simpl in Hnm; subst m.
        exists ∅, (x##w); constructor.
      * apply f_equal with (f := pred) in Hnm; simpl in Hnm.
        destruct (IH _ _ Hnm) as (u & v & Huv).
        exists (x##u), v; constructor; auto.
  Qed.

  Fact vapp_sub_left n (u : vec X n) m (v : vec _ m) k (w : vec _ k) : 
         u ⊞ v ⇝ w → u ≤sv w.
  Proof. induction 1; eauto with vec_db. Qed.

  Fact vapp_sub_right n (u : vec X n) m (v : vec _ m) k (w : vec _ k) : 
         u ⊞ v ⇝ w → v ≤sv w.
  Proof. induction 1; eauto with vec_db. Qed.

  Section vapp_idx_left_right.

    Let idx_left_cast n m k (e : k = n+m) : idx n → idx k :=
      match eq_sym e with
      | eq_refl => @idx_left _ _
      end.

    Let idx_right_cast n m k (e : k = n+m) : idx m → idx k :=
      match eq_sym e with
      | eq_refl => @idx_right _ _
      end.

    Local Fact vapp_idx_left_rec n (u : vec X n) m (v : vec _ m) k (w : vec _ k) :
          u ⊞ v ⇝ w → ∀ (e : k = n+m) i, u⦃i⦄ = w⦃idx_left_cast _ e i⦄.
    Proof.
      induction 1 as [ | n x u m v k w H IH ]; intros e p.
      + idx invert all.
      + apply vapp_length in H as ->; simpl in e.
        specialize (IH eq_refl); rewrite (eq_refl_nat e).
        idx invert p; trivial; rewrite IH; auto.
    Qed.

    Fact vapp_idx_left_eq n (u : vec X n) m (v : vec X m) (w : vec X (n+m)) :
           u ⊞ v ⇝ w → ∀i, u⦃i⦄ = w⦃idx_left m i⦄.
    Proof. intros H; apply (vapp_idx_left_rec H eq_refl). Qed.

    Fact vapp_idx_left n (u : vec X n) m (v : vec X m) k (w : vec X k) :
          u ⊞ v ⇝ w -> { f : idx n → idx k | ∀i, u⦃i⦄ = w⦃f i⦄ }.
    Proof.
      intros H.
      exists (idx_left_cast _ (vapp_length H)).
      apply vapp_idx_left_rec with (1 := H).
    Qed.

    Local Fact vapp_idx_right_rec n (u : vec X n) m (v : vec X m) k (w : vec X k) :
          u ⊞ v ⇝ w → ∀ (e : k = n+m) i, v⦃i⦄ = w⦃idx_right_cast _ e i⦄.
    Proof.
      induction 1 as [ | n x u m v k w H IH ]; intros e p.
      + simpl in e; rewrite (eq_refl_nat e); auto.
      + apply vapp_length in H as ->; simpl in e.
        specialize (IH eq_refl); rewrite (eq_refl_nat e).
        rewrite IH; auto.
    Qed.

    Fact vapp_idx_right_eq n (u : vec X n) m (v : vec X m) (w : vec X (n+m)) :
           u ⊞ v ⇝ w → ∀i, v⦃i⦄ = w⦃idx_right n i⦄.
    Proof. intros H; apply (vapp_idx_right_rec H eq_refl). Qed.

    Fact vapp_idx_right n (u : vec X n) m (v : vec _ m) k (w : vec _ k) :
           u ⊞ v ⇝ w → { f : idx m → idx k |  ∀i, v⦃i⦄ = w⦃f i⦄ }.
    Proof.
      intros H.
      exists (idx_right_cast _ (vapp_length H)).
      apply vapp_idx_right_rec with (1 := H).
    Qed.

  End vapp_idx_left_right.

  Fact vapp_prj n (u : vec X n) m (v : vec X m) k (w : vec X k) :
       u ⊞ v ⇝ w → ∀i, (∃j, w⦃i⦄ = u⦃j⦄) ∨ (∃j, w⦃i⦄ = v⦃j⦄).
  Proof.
    induction 1 as [ | n x u m v k w H IH ]; intros i; eauto.
    idx invert i.
    + left; now exists 𝕆.
    + destruct (IH i) as [ (j & Hj) | (j & Hj) ].
      * left; now exists (𝕊 j).
      * right; now exists j.
  Qed.

  Fact vapp_assoc nu (u : vec X nu) nv (v : vec _ nv) nuv (uv : vec _ nuv) 
                  nw (w : vec _ nw) nr (r : vec _ nr) :
          u ⊞ v ⇝ uv
        → uv ⊞ w ⇝ r
        → ∃ nvw (vw : vec _ nvw), u ⊞ vw ⇝ r ∧ v ⊞ w ⇝ vw.
  Proof.
    induction 1 as [ | nu x u nv v nuv uv H IH ] in nw, w, nr, r |- *.
    + exists nr, r; split; auto; constructor.
    + intros H1%vapp_inv.
      destruct r as [ | y nr r ]; [ easy | ].
      destruct H1 as (<- & (nvw & vw & ? & ?)%IH).
      exists nvw, vw; split; auto; constructor; auto.
  Qed.

  Fact vapp_assoc_rev nu (u : vec X nu) nv (v : vec _ nv) nw (w : vec _ nw) 
                      nvw (vw : vec _ nvw) nr (r : vec _ nr) :
          v ⊞ w  ⇝ vw
        → u ⊞ vw ⇝ r
        → ∃ nuv (uv : vec _ nuv), u ⊞ v ⇝ uv ∧ uv ⊞ w ⇝ r.
  Proof.
    induction u as [ | x nu u IH ] in nv, v, nw, w, nvw, vw, nr, r |- *.
    + intros ? []%vapp_inv; subst; exists nv, v; split; auto; constructor.
    + intros H1 H2%vapp_inv.
      destruct r as [ | nr y r ]; [ easy | ].
      destruct H2 as (<- & H2).
      destruct IH with (1 := H1) (2 := H2)
        as (nuv & uv & []).
      exists (S nuv), (x##uv); split; constructor; auto.
  Qed.

  Fact vapp_cons_assoc n (u : vec X n) x m (v : vec _ m) k (w : vec _ k) :
         u ⊞ (x##v) ⇝ w → ∃ nux (ux : vec _ nux), u ⊞ (x##∅) ⇝ ux ∧ ux ⊞ v ⇝ w.
  Proof. 
    intros H1.
    assert ((x##∅) ⊞ v ⇝ x##v) as H2.
    1: repeat constructor.
    apply (vapp_assoc_rev H2 H1).
  Qed.

End props.

#[global] Hint Resolve vapp_fin : core.

#[local] Notation "u '=[' R ']=' v" := (vec_fall2 R u v) (at level 70, format "u  =[ R ]=  v").

Section fall2.

  Variable (X Y : Type) (R : X → Y → Prop).

  Fact vapp_fall2 n (u₁ u₂ : vec _ n) m (v₁ v₂ : vec _ m) k (w₁ w₂ : vec _ k) :
           u₁ =[R]= u₂
         → v₁ =[R]= v₂
         → u₁ ⊞ v₁ ⇝ w₁
         → u₂ ⊞ v₂ ⇝ w₂
         → w₁ =[R]= w₂.
  Proof.
    intros H; revert H m v₁ v₂ k w₁ w₂.
    induction 1 using vec_fall2_rect; intros; vapp inv all; eauto with vec_db.
  Qed.

  Fact vapp_fall2_inv n (u₁ u₂ : vec _ n) m (v₁ v₂ : vec _ m) k (w₁ w₂ : vec _ k) :
           w₁ =[R]= w₂
         → u₁ ⊞ v₁ ⇝ w₁
         → u₂ ⊞ v₂ ⇝ w₂
         → u₁ =[R]= u₂ ∧ v₁ =[R]= v₂.
  Proof.
    intros H; revert H n u₁ u₂ m v₁ v₂.
    induction 1 as [ | k x y w₁ w₂ H1 H2 IH2 ] using vec_fall2_rect; intros n u₁ u₂ m ? ? H3 H4.
    + vapp inv all; auto with vec_db.
    + vapp inv all; auto with vec_db.
      revert H3; vec invert u₁ as ? u₁; intros H3.
      vapp inv all.
      destruct IH2 with (1 := H3) (2 := H4); auto with vec_db.
  Qed.

  Fact vapp_fall2_inv_left n (u₁ : vec _ n) m (v₁ : vec _ m) k (w₁ w₂ : vec _ k) :
           u₁ ⊞ v₁ ⇝ w₁
         → w₁ =[R]= w₂
         → { u₂ : _ & { v₂ | u₂ ⊞ v₂ ⇝ w₂ ∧ u₁ =[R]= u₂ ∧ v₁ =[R]= v₂ } }.
  Proof.
    intros H1 H2.
    destruct vapp_split with (w := w₂) (1 := vapp_length H1)
      as (u₂ & v₂ & H3).
    exists u₂, v₂; split; auto.
    revert H2 H1 H3; apply vapp_fall2_inv.
  Qed.

End fall2.

#[local] Reserved Notation "l ≤ₑ m" (at level 70, no associativity, format "l  ≤ₑ  m").

Section embed.

  Variables (X Y : Type) (R : X -> Y -> Prop).

  Infix "≤ₑ" := (vec_embed R).

  Fact vec_embed_inv n (v : vec _ n) m (w : vec _ m) :
          v ≤ₑ w
        → match v with
          | ∅    => True
          | x##v => ∃ m₁ (w₁ : vec _ m₁) y m₂ (w₂ : vec _ m₂),
                      w₁ ⊞ y##w₂ ⇝ w ∧ R x y ∧ v ≤ₑ w₂
          end.
  Proof.
    induction 1 as [ | n x v m y w H1 H2 IH2
                     | n   v m y w H1 IH2 ]; auto.
    + exists 0, ∅, y, m, w; simpl; auto with vec_db.
    + destruct v as [ | n x v ]; auto.
      destruct IH2 as (m1 & w1 & z & m2 & w2 & ? & ? & ?); simpl in *.
      exists (S m1), (y##w1), z, m2, w2; simpl; auto with vec_db.
  Qed.

  Fact vec_embed_cons_inv x n (v : vec _ n) m (w : vec _ m) :
          x##v ≤ₑ w → ∃ m₁ (w₁ : vec _ m₁) y m₂ (w₂ : vec _ m₂), w₁ ⊞ y##w₂ ⇝ w ∧ R x y ∧ v ≤ₑ w₂.
  Proof. apply vec_embed_inv. Qed.

  Fact vapp_vec_embed_skip n (u : vec _ n) m (v : vec _ m) k (w : vec _ k) p (r : vec _ p) :
             u ⊞ v ⇝ w → r ≤ₑ v → r ≤ₑ w.
  Proof.
    intros H1 H2. 
    apply vec_embed_sub_trans with (1 := H2),
          vapp_sub_right with (1 := H1).
  Qed.

  Hint Resolve vapp_vec_embed_skip : core.

  (** u ≤ₑ v -> u' ≤ₑ v' -> u++u' ≤ₑ v++v' *)

  Fact vec_embed_vapp n (u : vec _ n) n' (u' : vec _ n')
                      m (v : vec _ m) m' (v' : vec _ m')
                      k (w : vec _ k) p  (r : vec _ p) :
         u ⊞ u' ⇝ w
       → v ⊞ v' ⇝ r
       → u ≤ₑ v
       → u' ≤ₑ v'
       → w ≤ₑ r.
  Proof.
    intros H1 H2 H3; revert H3 n' u' m' v' k w p r H1 H2.
    induction 1; intros; vapp inv all; eauto with vec_db.
  Qed.

 Local Lemma vapp_embed_split nc (c : vec X nc) nu (u : vec _ nu) nv (v : vec _ nv) nw (w : vec _ nw) :
        u ⊞ v ⇝ w
      → c ≤ₑ w
      → ∃ na (a : vec _ na) nb (b : vec _ nb), a ⊞ b ⇝ c ∧ a ≤ₑ u ∧ b ≤ₑ v.
  Proof.
    induction 1 as [ | nu x u nv v nw w H IH ] in nc, c |- *.
    + exists 0, ∅, nc, c; eauto with vec_db.
    + intros H1%vec_embed_inv_left; destruct c as [ | y nc c ].
      * exists 0, ∅, 0, ∅; eauto with vec_db.
      * destruct H1 as [ (H1 & (na & a & nb & b & ? & [])%IH) | (na & a & nb & b & ? & [])%IH ].
        - exists (S na), (y##a), nb, b; eauto with vec_db.
        - exists na, a, nb, b; eauto with vec_db.
  Qed.

  Lemma vapp_embed_middle_choice x nu (u : vec X nu) y nv (v : vec _ nv) nw (w : vec _ nw) nr (r : vec _ nr) :
       v ⊞ (y##w) ⇝ r → x##u ≤ₑ r → u ≤ₑ w ∨ ∃i, R x (v⦃i⦄).
  Proof.
    intros H1 H2.
    destruct (vapp_embed_split H1 H2) as (na & a & nb & b & H3 & H4 & H5).
    destruct a as [ | z na a ].
    + destruct (vapp_fun H3 (vapp_0 _)); subst; simpl eq_rect in *.
      apply vec_embed_inv_left in H5 as [ (H6 & H5) | H5 ]; auto.
      left; revert H5; apply vec_sub_embed_trans; eauto with vec_db.
    + apply vapp_inv in H3 as (-> & H3).
      right.
      exact (vec_embed_prj H4 idx_fst).
  Qed.

End embed.

Section subvec.

  (* THIS SECTION SEEMS OBSOLETE *)

  Variables (X : Type).

  Local Fact subvec_refl n (v : vec X n) : v ≤sv v.
  Proof. apply vec_sub_refl. Qed.

  Local Fact vapp_subvec_left p (w : vec X p) n (u : vec _ n) n' (u' : vec _ n')
                                        m (v : vec _ m) m' (v' : vec _ m') :
          w ⊞ u ⇝ u'
        → w ⊞ v ⇝ v'
        → u ≤sv v
        → u' ≤sv v'.
  Proof.
    intros H; revert H m v m' v'.
    induction 1; intros; vapp inv all; eauto with vec_db.
  Qed.

  Local Fact vapp_subvec_choose na (a : vec X na) nu (u : vec _ nu) nv (v : vec _ nv) nw (w : vec _ nw) : 
        u ⊞ v ⇝ w 
      → a ≤sv w 
      → a ≤sv v 
      ∨ match a with
        | ∅    => True
        | x##_ => ∃ p, u⦃p⦄ = x
        end.
  Proof.
    induction 1 as [ | nu x u nv v nw w H IH ] in na, a |- *; eauto.
    intros [ [ Ha | Ha ]%IH | Ha ]%vec_embed_inv_right; eauto; 
      destruct a as [ | y na a ]; eauto with vec_db.
    + destruct Ha as (p & <-); right; now exists (idx_nxt p).
    + destruct Ha as (-> & _); right; now exists idx_fst.
  Qed.

  Local Fact vapp_subvec_split nc (c : vec X nc) nu (u : vec _ nu) nv (v : vec _ nv) nw (w : vec _ nw) :
        u ⊞ v ⇝ w
      → c ≤sv w
      → ∃ na (a : vec _ na) nb (b : vec _ nb), a ⊞ b ⇝ c ∧ a ≤sv u ∧ b ≤sv v.
  Proof. apply vapp_embed_split. Qed.

End subvec.