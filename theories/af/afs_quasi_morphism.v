(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(** This file generalizes af_quasi_morph for Kruskal-Higman to relational quasi morphisms *)

From Coq
  Require Import Arith List Lia Utf8.

From KruskalTrees
  Require Import list_utils.

From KruskalFinite
  Require Import finite choice.

Require Import base notations tactics.

Import ListNotations lift_notations.

Set Implicit Arguments.

#[local] Notation π₁ := (@proj1_sig _ _).
#[local] Notation FAN lw := (λ c, Forall2 (λ x l, x ∈ l) c lw).

#[local] Fact sig_Forall X (P : X → Prop) (l : list (sig P)) : Forall P (map π₁ l).
Proof. apply Forall_forall; now intros x ([] & <- & ?)%in_map_iff. Qed.

Section afs_quasi_morph.

  Variables (X : Type)           (* type of analyses *)
            (Y : Type)           (* type of evaluations *)
            (ea : X → Y → Prop)  (* evaluation/analysis relation *)
            (dom : rel₁ X) (codom : rel₁ Y).

  Notation "x ⇝ y" := (ea x y) (at level 70, no associativity, format "x ⇝ y").

  Hypotheses (ea_dom   : ∀ x y, x⇝y → dom x)
             (ea_codom : ∀ x y, x⇝y → codom y)
             (ea_total : ∀ x, dom x → { y | x⇝y })
             (ea_fun   : ∀ x y₁ y₂, x⇝y₁ -> x⇝y₂ → y₁ = y₂)
             (ea_fin   : ∀ y, codom y → fin (λ x, x⇝y)).

  Variables  (R : rel₂ X)        (* AF relation on analyses *)
             (E : rel₁ X)        (* Exceptional analyses *)
             (T  : rel₂ Y)       (* Relation on evaluation *)
             (y₀ : Y)            (* We want to show af T↑y0 *)
             (H₀ : codom y₀)

             (* evaluation is a quasi-morphism wrt R/T/E *)
             (ev_qmorph : ∀ x₁ x₂ y₁ y₂, R x₁ x₂ → x₁⇝y₁ → x₂⇝y₂ → T y₁ y₂ ∨ E x₁)

             (* if all analyses of y are exceptional then y₀ embeds y *)
             (excep_ana : ∀y, codom y → (λ x, x⇝y) ⊆₁ E → T y₀ y)

             (HR : afs dom R).

  Notation X' := (sig dom).
  Notation Y' := (sig codom).
  Notation R' := R⇓dom.
  Notation T' := T⇓codom.
  Notation E' := (λ x : X', E (π₁ x)).
  Notation y'₀ := (exist codom y₀ H₀).

  Notation "x ⇝' y" := ((π₁ x)⇝(π₁ y)) (at level 70, format "x ⇝' y").

  Section ev_ana_functions.

    (** We buid the function and its "inverse" on X' → Y' *)

    Local Definition ev_pwc : ∀x : X', { y : Y' | x ⇝' y }.
    Proof.
      intros (x & Hx).
      destruct (ea_total Hx) as (y & Hy).
      exists (exist _ _ (ea_codom Hy)); auto.
    Qed.

    Local Definition ev' x := π₁ (ev_pwc x).

    Local Fact ev'_spec x : x ⇝' ev' x.
    Proof. apply (proj2_sig (ev_pwc _)). Qed.

    Local Definition ana_pwc : ∀y : Y', { l : list X' | ∀x : X', π₁ x ∈ map π₁ l ↔ x ⇝' y }.
    Proof.
      intros (y & Hy).
      destruct ea_fin with (1 := Hy) as (l & Hl).
      assert (forall x, x ∈ l -> dom x) as Hl'.
      1: { intros x Hx; apply Hl, ea_dom in Hx; auto. }
      apply Forall_forall, Forall_sig in Hl' as (m & Hm).
      exists m; intros []; simpl.
      rewrite Hl, Hm, in_map_iff; firstorder.
    Qed.

    Local Definition ana' y := π₁ (ana_pwc y).

    (* (ana y) lists the analyses of y but only up-to
       the domain-proofs and this does not matter for
       predicates that do not take those domain-proofs
       into account, such as (good R') *)

    Local Fact ana'_spec (x : X') (y : Y') : π₁ x ∈ map π₁ (ana' y) ↔ x ⇝' y.
    Proof. apply (proj2_sig (@ana_pwc _)). Qed.

  End ev_ana_functions.

  Hint Resolve ev'_spec ana'_spec in_map : core.

  (* Beware this one only holds in this direction, NOT the reverse *)
  Local Fact ana'_spec_π₁ x y : x ∈ ana' y → π₁ (ev' x) = π₁ y.
  Proof. intro; eapply ea_fun; eauto; apply ana'_spec; auto. Qed.

  (* Lifted to the FAN *)
  Local Fact FAN_map_ana'_π₁ lx ly :
        FAN (map ana' ly) lx → map (λ x, π₁ (ev' x)) lx = map π₁ ly.
  Proof.
    rewrite Forall2_map_right, <- Forall2_eq, Forall2_map_left, Forall2_map_right.
    apply Forall2_mono, ana'_spec_π₁.
  Qed.

  Local Fact In_ana'_π₁ (Q : X → Prop) y :
          (∀x, x ∈ ana' y → Q (π₁ x)) → (∀x, x⇝(π₁ y) → Q x).
  Proof.
    intros Hy x Hxy.
    generalize (ea_dom Hxy); intros Hx.
    apply (@ana'_spec (exist _ x Hx) y), in_map_iff in Hxy.
    simpl in Hxy; destruct Hxy as (? & <- & ?); auto.
  Qed.

  Hint Resolve in_map in_or_app in_cons in_eq : core.

  (* If a list is R'-good then its evaluation is T'-good unless it meets E'
     This extends the ev_qmorph property to good sequences *)
  Local Fact ev_good_or_exceptional lx :
         good R' lx → good T' (map ev' lx) ∨ ∃x, x ∈ lx ∧ E' x.
  Proof.
    induction 1 as [ ? ? ? ? H | ? ? ? [ | (? & [])] ]; simpl; eauto.
    destruct (ev_qmorph H (ev'_spec _) (ev'_spec _)); eauto.
  Qed.

  (* A(nalyses) W(ell): all possible choice sequences of analyses are good *)
  Local Definition AW ly := FAN (map ana' ly) ⊆₁ good R'.

  Hint Resolve sig_Forall Forall_app : core.

  (* The critical proof step: if ly Analyses Well then ly++[y'₀] is good for T *)
  Local Lemma AW_good_lifted ly : AW ly → good T' (ly++[y'₀]).
  Proof.
    intros Hly; red in Hly.
    destruct list_combi_principle
      with (P := λ l, good T' (map ev' l))
           (B := E') (ll := map ana' ly)
      as [ (lx & H1 & H2) | (lx & H1 & H2) ].

    + (* Hypothesis for combi principle *)
      intros lx Hl.
      apply ev_good_or_exceptional, Hly, Hl.

    + (* there is (choice) sequence of analyses lx of ly which maps
         to a good sequence, but lx maps to ly hence ly is good *)
      apply good_app_right.
      revert H2; apply good_map_proj1_sig.
      rewrite map_map.
      now apply FAN_map_ana'_π₁.

    + (* there is an evaluation of which all analyses are exceptional *)
      apply in_map_iff in H1 as (y & <- & H1%(in_map π₁)).
      apply good_sub_rel; rewrite map_app; simpl; split; eauto.
      2: apply Forall_app; auto. (* Why does the Hint fails ? *) 
      apply good_snoc with (1 := H1), excep_ana.
      * apply proj2_sig.
      * apply In_ana'_π₁, H2.
  Qed.

  Local Corollary bar_AW_good_lifted ly : bar AW ly → bar (good T') (ly++[y'₀]).
  Proof. 
    intros Hly; apply bar_app.
    revert Hly; apply bar_mono, AW_good_lifted.
  Qed.

  Local Fact bar_goodR'_nil : bar (good R') [].
  Proof. apply af_iff_bar_good_nil, afs_iff_af_sub_rel; auto. Qed.

  Hint Resolve bar_goodR'_nil : core.

  Local Fact bar_AW_nil : bar AW [].
  Proof.
    apply bar_map_inv
      with (f := ana')
           (Q := λ ll, FAN ll ⊆₁ good R'); auto.
    apply FAN_theorem; auto.
  Qed.

  Local Fact bar_goodT'_lift : bar (good (T'↑y'₀)) [].
  Proof. apply bar_rel_lift, bar_AW_good_lifted, bar_AW_nil. Qed.

  Theorem afs_quasi_morph : afs codom T↑y₀.
  Proof.
    apply afs_iff_af_sub_rel,
          af_iff_bar_good_nil,
          bar_mono with (2 := bar_goodT'_lift),
          good_mono.
    intros [] []; simpl; auto.
  Qed.

End afs_quasi_morph.

Tactic Notation "afs" "quasi" "morph" uconstr(f) uconstr(e) :=
  match goal with
  | |- afs _ _ → afs _ _ => apply afs_quasi_morph with (ea := f) (E := e)
  end.




