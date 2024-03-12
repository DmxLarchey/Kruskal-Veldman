(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Utf8.

Require Import base notations tactics.

Set Implicit Arguments.

(* For self inverse functions, eg reverse *)

#[local] Reserved Notation "⟲ f" (at level 0, right associativity, format "⟲ f").

(* nat indexed sequences implemented as maps *)

#[local] Definition cons {X} (a : X) x n :=
  match n with
  |   0 => a 
  | S n => x n
  end.

Arguments cons {_} _ _ _/.

#[local] Notation "a :: x" := (cons a x).
#[local] Notation tl x := (λ n, x (S n)).
#[local] Notation hd x := (x 0).

Section wf_upto_ext.

  Variable (X Y : Type) (ext : (Y → Base) → Base) (f : X → Y).

  Implicit Types (R : X → X → Base) (Q : Y → Base).

  (** Well founded upto is similar to well_founded except that we
      can only prove by induction predicates of the form Q∘f, ie
      Q can only express properties of the projections of the
      inhabitants of X.

      This will help at decorating member of Y with information
      helpfull for the inductive proof but not recoverable from
      the value of y : Y. *)

  Local Definition hereditary_upto R Q := ∀a, (∀b, R b a → Q (f b)) → Q (f a).

  (** Notice the reading of the statement:
        to prove Q (f a), you may assume Q (f b) already
        holds for values b which are R-lower than a

      Notice that the relation is between the non-projected
      value, ie it may use the information which is hidden
      by the projection f *)

  Definition wf_upto R :=
      ∀Q, (∀a, (∀b, R b a → Q (f b)) → Q (f a))
        → (∀a,                         Q (f a)).

  (** "well founded upto" restricted to extensional predicates Q,
     helpful when dealing with non-extensional types like nat -> X/Y *)

  Definition wf_upto_ext R :=
      ∀Q, ext Q
        → (∀a, (∀b, R b a → Q (f b)) → Q (f a))
        → (∀a,                         Q (f a)).

  Fact wf_upto_wf_upto_ext R : wf_upto R → wf_upto_ext R.
  Proof. intros H ? _; apply H. Qed.

End wf_upto_ext.

(* Q, a predicate over a function space, is extensional if it is
   invariant when a function is replaced by another which is extensionally 
   identical *)

#[local] Notation "f ≡ g" := (∀x, f x = g x) (at level 70, format "f  ≡  g").

Definition extensional {X Y} (Q : (X → Y) → Base) := ∀ f g, f ≡ g → Q f → Q g.

#[local] Notation ext := extensional.

Local Fact ext_imp X Y (P Q : (X → Y) → Base) : ext P → ext Q → ext (λ x, P x → Q x).
Proof.
  intros H1 H2 u v Huv H3 H4.
  apply (H2 u v), H3; auto.
  apply (H1 v u); auto.
Qed.

Local Fact ext_cons X (Q : (nat → X) → Base) : ext Q → ∀s, Q s ⇄ₜ Q (hd s :: tl s).
Proof. intros H ?; split; apply H; intros []; auto. Qed.

Local Fact ext_ind X (Q : (nat → X) → Base) : ext Q → (∀ x s, Q (x::s)) → ∀s, Q s.
Proof. intros ? ? ?; apply ext_cons; auto. Qed.

Local Fact ext_comp X Y (f : X → Y) (Q : (nat → Y) → Base) : ext Q → ext (λ s, Q (λ n, f (s n))).
Proof. intros H ? ? ?; apply H; intros; f_equal; auto. Qed.

Local Fact ext_comp' X Y (f : (nat → X) → (nat → Y))  (Q : (nat → Y) → Base) :
   ext Q → (∀ u v, u ≡ v → f u ≡ f v) → ext (λ s, Q (f s)).
Proof. intros H H1 ? ? ?; apply H, H1; auto. Qed.

#[local] Hint Resolve ext_comp ext_comp' : core.

Section wf_upto_lex_prod.

  (** This is the critical observation for the notion wf_upto,
      it is closed under lexicographic products *)

  Variables (Xₑ X : Type) (f : Xₑ → X) (R : Xₑ → Xₑ → Base)
            (Yₑ Y : Type) (g : Yₑ → Y) (T : Yₑ → Yₑ → Base).

  Let Zₑ := prod Xₑ Yₑ.
  Let Z  := prod X Y.

  Let lex_prj (z : Zₑ) : Z := let (x,y) := z in (f x,g y).

  Let lex_prod : Zₑ → Zₑ → Base :=
    λ '(x₁,y₁) '(x₂,y₂), R x₁ x₂ ∨ₜ f x₁ = f x₂ ∧ₜ T y₁ y₂.

  Lemma wf_upto_lex_prod :
           wf_upto f R
         → wf_upto g T
         → wf_upto lex_prj lex_prod.
  Proof.
    intros HR HT Q IHQ (x,y); simpl; revert x y.
    intros x; pattern (f x); revert x; apply HR.
    intros x IHx.
    intros y; pattern (g y); revert y; apply HT; auto.
    intros y IHy.
    apply (IHQ (_,_)).
    intros (x',y') [ H | (E & H2) ]; simpl.
    + apply IHx; auto.
    + rewrite E; apply IHy; auto.
  Qed.

End wf_upto_lex_prod.

Section wf_upto_lex_dep_prod.

  (** This is the critical observation for the notion wf_upto,
      it is closed under (dependent) lexicographic product *)

  Variables (Iₑ I : Type) (f : Iₑ → I) (R : Iₑ → Iₑ → Base)
            (Xₑ X : Type) (g : Xₑ → X) (T : I → Xₑ → Xₑ → Base).

  Let Yₑ := prod Iₑ Xₑ.
  Let Y  := prod I X.

  Let lex_dep_prj (y : Yₑ) : Y := let (i,x) := y in (f i,g x).

  (** Notice that in the second choice, the requirement
      is that the first components are equal *AFTER* projection,
      ie we require f i₁ = f i₂, *not* the stronger i₁ = i₂ *)

  Let lex_dep_prod : Yₑ → Yₑ → Base :=
    λ '(i₁,x₁) '(i₂,x₂), R i₁ i₂ ∨ₜ f i₁ = f i₂ ∧ₜ T (f i₁) x₁ x₂.

  Lemma wf_upto_lex_dep_prod ext :
            wf_upto f R
          → (∀i, wf_upto_ext ext g (T i))
          → wf_upto_ext (λ Q, ∀i, ext (λ x, Q (f i,x)))
                        lex_dep_prj
                        lex_dep_prod.
  Proof.
    intros HR HT Q HQ IHQ (i,x); simpl; revert i x.
    intros i; pattern (f i); revert i; apply HR.
    intros i IHi.
    intros x; pattern (g x); revert x; apply (HT (f i)); auto.
    intros x IHx.
    apply (IHQ (_,_)).
    intros (i',x') [ H | (E & H2) ]; simpl.
    + apply IHi; auto.
    + rewrite E in H2 |- *; apply IHx; auto.
  Qed.

End wf_upto_lex_dep_prod.

Section prj_seq.

  (** To work with sequences nat → X, viewed as streams *)

  Variables (X Y : Type) (f : X → Y).

  Definition prj_seq (α : nat → X) i := f (α i).

  Local Fact prj_seq_ext u v : u ≡ v → prj_seq u ≡ prj_seq v.
  Proof. intros Huv n; unfold prj_seq; simpl; f_equal; auto. Qed.

  Local Fact prj_seq_cons Q :
     ext Q → forall x s, Q (prj_seq (x::s)) ⇄ₜ Q (f x::prj_seq s).
  Proof. intros H x s; split; apply H; intros []; simpl; auto. Qed.

End prj_seq.

Arguments prj_seq {_ _} _ _ _ /.

Local Fact cons_ext {X} (a : X) u v : u ≡ v → a::u ≡ a::v.
Proof. intros ? []; simpl; auto. Qed.

#[local] Hint Resolve prj_seq_ext cons_ext : core.

Section rev.

  (** rev reverses [0,k[ and keeps the rest unchanged
     and ⇄f use bij to swap the argument of f *)

  Variable k : nat.

  Local Definition rev i := if le_lt_dec k i then i else k - S i.

  Local Fact rev_eq_lt i : i < k → rev i = k - S i.
  Proof. unfold rev; intro; destruct (le_lt_dec k i); lia. Qed.

  Local Fact rev_eq_ge i : k ≤ i → rev i = i.
  Proof. unfold rev; intro; destruct (le_lt_dec k i); lia. Qed.

  Local Fact rev_lt_stable i : i < k → rev i < k.
  Proof. intro; rewrite rev_eq_lt; lia. Qed.

  Local Fact rev_zero : 0 < k → rev 0 = k-1.
  Proof. intro; rewrite rev_eq_lt; auto. Qed.

  Local Fact rev_max : 0 < k → rev (pred k) = 0.
  Proof. intro; rewrite rev_eq_lt; lia. Qed.

  Hint Resolve rev_lt_stable : core.

  Local Fact rev_rev_eq i : rev (rev i) = i.
  Proof.
    destruct (le_lt_dec k i).
    + rewrite !(@rev_eq_ge i); auto.
    + rewrite (@rev_eq_lt i); auto.
      rewrite rev_eq_lt; auto; lia.
  Qed.

  Notation "⟲ f" := (λ i, f (rev i)).

  Variable (X Y : Type) (f : X → Y) (Q : (nat → Y) → Base).

  Local Fact rev_ext : ext Q → (∀α, Q (⟲α)) → ∀α, Q α.
  Proof.
    intros HQ H α.
    apply (HQ (⟲⟲α)).
    + intro; rewrite rev_rev_eq; auto.
    + apply H with (α := ⟲_).
  Qed.

  Local Fact rev_seq_prj α : ext Q → Q (prj_seq f ⟲α) ⇄ₜ Q ⟲(prj_seq f α).
  Proof. intros HQ; split; apply HQ; auto. Qed.

  Local Fact rev_rev_seq_prj α : ext Q → Q ⟲⟲α ⇄ₜ Q α.
  Proof. intros HQ; split; apply HQ; intro; rewrite rev_rev_eq; auto. Qed.

End rev.

#[local] Hint Resolve rev_lt_stable : core.

Section wf_upto_lex_seq.

  (** wf_upto is stable under lexicographic product on sequences *)

  Variables (Xₑ X : Type) (f : Xₑ → X).

  Implicit Type (α : nat → Xₑ) (R : Xₑ → Xₑ → Base).

  Definition lex_seq k R : (nat → Xₑ) -> (nat → Xₑ) → Base :=
     λ α β,
       ∃ₜ i,   (i < k)
             ∧ₜ R (α i) (β i)
             ∧ₜ ∀j, j < i → f (α j) = f (β j).

  Theorem wf_upto_lex_seq k R :
           wf_upto f R
         → wf_upto_ext ext (prj_seq f) (lex_seq k R).
  Proof.
    intros HR.
    induction k as [ | k IHk ].
    + intros Q HQ IHQ s; apply IHQ; auto; intros ? (? & ? & _); lia.
    + intros Q HQ IHQ s.
      pattern s; revert s; apply ext_ind; auto.
      intros x s; apply prj_seq_cons; auto; revert x s.
      intros x; pattern (f x); revert x; apply HR; intros x IHx.
      intros s; pattern (prj_seq f s); revert s; apply IHk; [ | intros s IHs ]; auto.
      apply prj_seq_cons; auto.
      apply IHQ.
      intros s' (i & H1 & H2 & H3).
      apply (HQ (cons (f (s' 0)) (prj_seq f (tl s')))).
      1: intros []; auto.
      destruct i as [ | i ]; auto.
      rewrite (H3 0); try lia.
      apply IHs.
      exists i; repeat split; auto; try lia.
      intros; apply H3; lia.
  Qed.

End wf_upto_lex_seq.

Section wf_upto_lex_r_seq.

  (* We get the reversed lexicographic product using the bijection rev k := fun i => k - S i *)

  Variables (Xₑ X : Type) (f : Xₑ → X) (k : nat) (R : Xₑ → Xₑ → Base).

  Definition lex_r_seq α β :=
          ∃ₜ i, i < k
             ∧ₜ R (α i) (β i)
             ∧ₜ forall j, i < j < k
                       -> f (α j) = f (β j).

  Notation bij := (rev k).
  Notation "⟲ f" := (λ i, f (bij i)).

  Local Fact bij_lex_seq α β : lex_r_seq ⟲α ⟲β ⇄ₜ lex_seq f k R α β.
  Proof.
    split.
    + intros (i & H1 & H2 & H3).
      exists (bij i); repeat split; auto.
      * intros j Hj.
        rewrite <- (rev_rev_eq k j); apply H3.
        generalize (rev_lt_stable H1).
        intros; rewrite rev_eq_lt in *; try lia.
   + intros (i & H1 & H2 & H3).
     exists (bij i); repeat split; auto.
     * rewrite rev_rev_eq; auto.
     * intros j (H4 & H5); apply H3.
       rewrite rev_eq_lt in *; try lia.
  Qed.

  Local Fact lex_r_seq_ext β : ext (λ α, lex_r_seq α β).
  Proof.
    intros u v Huv (i & H1 & H2 & H3).
    exists i; repeat split; auto;
      intros; rewrite <- Huv; auto.
  Qed.

  Hint Resolve lex_r_seq_ext : core.

  Theorem wf_upto_lex_r_seq : wf_upto f R → wf_upto_ext ext (prj_seq f) lex_r_seq.
  Proof.
    intros H.
    apply wf_upto_lex_seq with (k := k) in H.

    intros Q HQ IHQ.
    intros α; pattern α; revert α; apply (rev_ext k); auto.
    intros α.
    apply rev_seq_prj; auto.
    apply (H (fun α => Q (⟲α))); auto.
    clear α; intros α IHα.
    apply rev_seq_prj; auto.
    apply IHQ.
    intros β; pattern β; revert β; apply (rev_ext k).
    1: { intros u v Huv H1 H2.
         apply (HQ (prj_seq f u)).
         + intros; simpl; f_equal; auto.
         + apply H1; eauto.
           revert H2; apply lex_r_seq_ext; auto. }
    intros β IHβ.
    apply rev_seq_prj; auto.
    apply IHα.
    apply bij_lex_seq; auto.
  Qed.

End wf_upto_lex_r_seq.

Section wf_upto_lex_nat_and_seq.

  (** Here we build the (reversed) more facile wf upto induction principle *)

  Variables (Xₑ X : Type) (f : Xₑ → X) (Rₑ : Xₑ → Xₑ → Base) (HRₑ : wf_upto f Rₑ).

  Let Aₑ := prod Xₑ nat.
  Let A  := prod X  nat.
  Let fa  : Aₑ → A := λ '(x,n), (f x,n).
  Let RAₑ : Aₑ → Aₑ → Base := λ '(x,_) '(y,_), Rₑ x y.

  Local Fact HRAₑ : wf_upto fa RAₑ.
  Proof.
    intros Q HQ (x,n); revert x n; simpl.
    intros x; pattern (f x); revert x; apply HRₑ.
    intros x IHx n.
    apply (HQ (_,_)).
    intros []; simpl; auto.
  Qed.

  Let Bₑ := nat → Xₑ.
  Let B  := nat → X.
  Let fb : Bₑ → B := prj_seq f.
  Let RBₑ (a : A) := lex_seq f (snd a) Rₑ.

  Local Fact HRBₑ a : wf_upto_ext ext fb (RBₑ a).
  Proof. apply wf_upto_lex_seq, HRₑ. Qed.

  Let Cₑ := (nat * Xₑ * (nat → Xₑ))%type.
  Let C  := (nat * X * (nat → X))%type.
  Let fc : Cₑ → C := λ '(n,x,s), (n,f x,fb s).

  Let RCₑ : Cₑ → Cₑ → Base := λ '(n₁,x₁,s₁) '(n₂,x₂,s₂),
          Rₑ x₁ x₂
       ∨ₜ n₁ = n₂
       ∧ₜ f x₁ = f x₂
       ∧ₜ ∃ₜ i, i < n₁
             ∧ₜ Rₑ (s₁ i) (s₂ i)
             ∧ₜ ∀j, j < i → f (s₁ j) = f (s₂ j).

  Local Fact HRCₑ : wf_upto_ext (λ Q, ∀ k x s s', s ≡ s' → Q (k,x,s) → Q (k,x,s')) fc RCₑ.
  Proof.
    generalize (wf_upto_lex_dep_prod _ HRAₑ HRBₑ); intros H.
    intros Q HQ IHQ ((k,x),s); simpl.
    set (Q' (p : A * (nat -> X)) := let (a,s) := p in Q (snd a, fst a, s)).
    specialize (H Q').
    change (Q' (fa (x,k),fb s)).
    generalize (x,k); clear x k.
    intro p; apply H with (a := (_,_)); clear s p H; unfold Q'; clear Q'.
    + intros []; simpl; intros ? ? ?; apply HQ; auto.
    + intros ((x,k),s) IH; simpl.
      apply (IHQ (_,_,_)).
      intros ((n,y),t) H; simpl.
      apply (IH ((_,_),_)); simpl.
      destruct H as [ H | (-> & -> & i & H1 & H2 & H3) ]; auto.
      right; split; auto.
      exists i; simpl; auto.
  Qed.

  Let Dₑ := (nat * Bₑ)%type.
  Let D  := (nat * B)%type.
  Let fd : Dₑ → D := λ '(n,s), (n, fb s).

  Definition lex_nat_seq : Dₑ → Dₑ → Base := λ '(n₁,s₁) '(n₂,s₂),
          Rₑ (s₁ 0) (s₂ 0)
       ∨ₜ n₁ = n₂
       ∧ₜ ∃ₜ i, 0 < i <= n₁
             ∧ₜ Rₑ (s₁ i) (s₂ i)
             ∧ₜ ∀j, j < i → f (s₁ j) = f (s₂ j).

  Notation RDₑ := lex_nat_seq.

  Theorem wf_upto_lex_nat_and_seq : wf_upto_ext (λ Q, ∀k, ext (λ s, Q (k,s))) fd lex_nat_seq.
  Proof.
    intros Q HQ IHQ (n,s); simpl.
    set (Q' := fun '(n,x,s) => Q (n,x::s)).
    apply (HQ n (cons (f (s 0)) (fb (tl s)))).
    1: intros []; simpl; auto.
    change (Q' (n, f(hd s),fb (tl s))).
    generalize (hd s) (tl s); clear s; intros x s.
    change (Q' (fc (n,x,s))).
    generalize (n,x,s); clear n x s.
    apply HRCₑ.
    + intros k x s s' Hss'; apply HQ; intros []; auto.
    + intros ((n,x),s) IH.
      apply (HQ n (fb (x::s))).
      1: intros []; simpl; auto.
      apply (IHQ (_,_)).
      intros (n',s') H.
      simpl.
      apply (HQ n' (cons (f (hd s')) (fb (tl s')))).
      1: intros []; auto.
      apply (IH (_,_,_)); simpl.
      destruct H as [ | (<- & i & H1 & H2 & H3) ]; auto; right; rsplit 2; auto.
      * apply H3; lia.
      * destruct i as [ | i ]; tlia.
        exists i; rsplit 2; auto; tlia.
        intros; apply H3; lia.
  Qed.

End wf_upto_lex_nat_and_seq.

Section wf_upto_lex_seq_and_nat.

  (** We get a reverse principle using the family of bijections λ k, rev (S k) *)

  Variables (Xₑ X : Type) (f : Xₑ -> X) (Rₑ : _ → _ → Base) (HRₑ : wf_upto f Rₑ).

  Let Aₑ := ((nat → Xₑ) * nat)%type.
  Let A  := ((nat → X) * nat)%type.
  Let fa : Aₑ → A := λ '(s,n), (prj_seq f s,n).

  Definition lex_seq_nat : Aₑ → Aₑ → Base := λ '(s₁,n₁) '(s₂,n₂),
          Rₑ (s₁ n₁) (s₂ n₂)
       ∨ₜ n₁ = n₂
       ∧ₜ ∃ₜ i, i < n₁
             ∧ₜ Rₑ (s₁ i) (s₂ i)
             ∧ₜ ∀j, i < j <= n₁ → f (s₁ j) = f (s₂ j).

  Notation RAₑ := lex_seq_nat.

  Local Fact RAₑ_ext n : ∀p, ext (λ s, RAₑ (s,n) p).
  Proof.
    intros (s',n') u v Huv [ H | (<- & i & ? & ? & ?) ]; [ left | right ].
    + rewrite <- Huv; auto.
    + split; auto; exists i; rewrite <- !Huv; rsplit 2; auto.
      intro; rewrite <- Huv; auto.
  Qed.

  Let τₑ : _ → Aₑ := λ '(n,s), (λ i, s (rev (S n) i) , n).
  Let τ : _ → A :=   λ '(n,s), (λ i, s (rev (S n) i) , n).

  Local Fact bij_RAₑ : ∀ α β, lex_seq_nat (τₑ α) (τₑ β) ⇄ₜ lex_nat_seq f Rₑ α β.
  Proof.
    intros (k,s) (k',s'); equiv sum.
    + f_equal; rewrite !rev_max; tlia; tauto.
    + split; intros (<- & i & H); split; auto; exists (rev (S k) i); revert H; intros (H1 & H2 & H3); rsplit 2; auto.
      * rewrite rev_eq_lt; lia.
      * intros j Hj.
        rewrite <- (rev_rev_eq (S k) j); apply H3.
        rewrite rev_eq_lt in Hj; tlia.
        rewrite rev_eq_lt; tlia.
      * rewrite rev_eq_lt; lia.
      * rewrite rev_rev_eq; auto.
      * intros j Hj; apply H3.
        rewrite rev_eq_lt in Hj |- *; lia.
  Qed.

  Hint Resolve RAₑ_ext bij_RAₑ : core.

  Theorem wf_upto_lex_seq_and_nat :
         wf_upto_ext (λ Q, ∀k, ext (λ s, Q (s,k))) fa RAₑ.
  Proof.
    intros Q HQ IHQ.
    set (Q' := fun x => Q (τ x)).
    set (fb := fun '(n,s) => (n,prj_seq f s) : nat * (nat -> X)).
    assert (forall n, ext (fun s => Q' (n,s))) as HQ'.
    1: intros ? ? ? ?; apply HQ; intro; auto.
    intros (s,n); simpl; revert s.
    apply rev_ext with (S n).
    1: intros ? ? ?; apply HQ; intro; auto.
    intros s; change (Q' (fb (n,s))).
    generalize (n,s); clear n s.
    apply (wf_upto_lex_nat_and_seq HRₑ); auto.
    intros (n,s) IHs.
    apply (IHQ (_,_)).
    intros (s',n'); simpl fa.
    pattern s'; revert s'.
    apply rev_ext with (S n').
    + apply ext_imp; auto.
      apply ext_comp' with (Q := fun s => Q (s,_)); auto.
    + intros s' Hs'; apply (IHs (_,_)), bij_RAₑ, Hs'.
  Qed.

End wf_upto_lex_seq_and_nat.

